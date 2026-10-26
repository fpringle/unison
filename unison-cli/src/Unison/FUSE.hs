module Unison.FUSE where

import Data.ByteString qualified as BS
import Data.ByteString.Short (fromShort)
import Data.Digest.Murmur64 (asWord64, hash64)
import Data.Set qualified as Set
import Data.Text qualified as T
import Foreign.C.Error (Errno, eNOENT, eOK, ePERM)
import System.Clock (Clock (Realtime), getTime)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, makeAbsolute)
import System.FilePath (addExtension, pathSeparators, splitExtension, splitPath)
import System.LibFuse3
import System.LibFuse3.FuseConfig (FuseConfig (..))
import System.LibFuse3.Internal (fuseRun)
import System.Posix
import U.Codebase.Branch (CausalBranch)
import U.Codebase.Causal qualified as V2Causal
import U.Codebase.HashTags (CausalHash (..))
import U.Codebase.Reference (Id' (..), Reference' (..))
import Unison.Cli.Pretty (prettyProjectAndBranchName)
import Unison.Codebase
  ( Codebase,
    getShallowCausalAtPath,
    runTransaction,
  )
import Unison.Codebase.Branch (Branch0)
import Unison.Codebase.Branch.Names qualified as Branch
import Unison.Codebase.Editor.HandleInput.ShowDefinition (renderCodePretty)
import Unison.Codebase.Path (Path, fromList)
import Unison.Codebase.SqliteCodebase.Branch.Cache (newBranchCache)
import Unison.Codebase.SqliteCodebase.Conversions (branch2to1)
import Unison.Codebase.SqliteCodebase.Operations qualified as CodebaseOps
import Unison.CommandLine.OutputMessages (renderFileName)
import Unison.ConstructorReference (GConstructorReference (..))
import Unison.Core.Project
import Unison.Debug (DebugFlag (..), debugM)
import Unison.Hash (Hash (toShort))
import Unison.HashQualified (HashQualified)
import Unison.HashQualified qualified as HQ
import Unison.Name (Name)
import Unison.NameSegment (NameSegment)
import Unison.Names qualified as Names
import Unison.NamesWithHistory (SearchType (..))
import Unison.Parser.Ann (Ann)
import Unison.Prelude
import Unison.PrettyPrintEnv.Names qualified as PPE
import Unison.PrettyPrintEnvDecl qualified as PPED
import Unison.PrettyTerminal qualified as PT
import Unison.ReferentPrime (Referent' (..))
import Unison.Server.Backend (IncludeCycles (..), ShallowListEntry (..), TermEntry (..), TypeEntry (..), hqNameQuery, lsBranch)
import Unison.Server.Backend qualified as Backend
import Unison.Server.NameSearch.FromNames qualified as NameSearch
import Unison.Server.QueryResult (QueryResult (..))
import Unison.Server.SearchResult (SearchResult (..), TermResult (..), TypeResult (..))
import Unison.Server.SearchResult qualified as SearchResult
import Unison.Sqlite (Transaction)
import Unison.Symbol (Symbol)
import Unison.Syntax.HashQualified qualified as HQ
import Unison.Syntax.Name qualified as Name (toText)
import Unison.Syntax.NameSegment qualified as NameSegment
import Unison.Util.Cache qualified as Cache
import Unison.Util.Defns (Defns (..))
import Unison.Util.Pretty qualified as Pretty

-- Types

data TermOrTypeName = BuiltinName (HashQualified Name) | Hash Hash
  deriving (Show)

data FileHandle = FileHandle TermOrTypeName (HashQualified Name)
  deriving (Show)

data DirHandle = DirHandle Hash Path
  deriving (Show)

data FileOrDirName = FileName (HashQualified Name) | DirName Path
  deriving (Show)

data FileOrDirHandle
  = File FileHandle
  | Dir DirHandle
  deriving (Show)

data LookupResult a
  = Found a
  | NotFound
  | LookupError Text
  deriving (Functor)

-- Parsing

parseFileName :: Text -> Either Text (HashQualified Name)
parseFileName fileName = do
  let err =
        fileName
          <> " is not a well-formed name, hash, or hash-qualified name. "
          <> "I expected something like `foo`, `#abc123`, or `foo#abc123`."
  maybeToEither err (HQ.parseText ("." <> T.replace "/" "." (T.dropAround (`elem` pathSeparators) fileName)))

filePathToPath :: FilePath -> Either Text Path
filePathToPath ('/' : rel) =
  fmap fromList
    . traverse NameSegment.parseText
    . filter (not . T.null)
    . fmap (T.dropAround (`elem` pathSeparators))
    . fmap T.pack
    . splitPath
    $ rel
filePathToPath rel = Left . T.pack $ "Relative path: " <> rel

parseFileOrDirName :: FilePath -> Either Text FileOrDirName
parseFileOrDirName fp = case splitExtension fp of
  (fileName, ".u") -> FileName <$> parseFileName (T.pack fileName)
  _ -> DirName <$> filePathToPath fp

-- Output

-- | Used in getattr. We murmur-hash the unison hash of a term/type/namespace, or the name of a builtin.
fileOrDirID :: FileOrDirHandle -> FileID
fileOrDirID = \case
  File (FileHandle (BuiltinName builtinName) _) -> onName builtinName
  File (FileHandle (Hash hash) _) -> onHash hash
  Dir (DirHandle hash _) -> onHash hash
  where
    onHash :: Hash -> FileID
    onHash = CIno . asWord64 . hash64 . fromShort . toShort

    onName :: HashQualified Name -> FileID
    onName = CIno . asWord64 . hash64 . encodeUtf8 . HQ.toTextWith Name.toText

makeEntry :: ShallowListEntry Symbol Ann -> Maybe (String, Maybe FileStat)
makeEntry = \case
  ShallowTermEntry te ->
    Just (makeFileName (termEntryName te), Nothing)
  ShallowTypeEntry te ->
    Just (makeFileName (typeEntryName te), Nothing)
  ShallowBranchEntry name _hash _stats ->
    Just (makeDirName name, Nothing)
  ShallowPatchEntry _name -> Nothing -- no idea what this is

makeFileName :: Name -> String
makeFileName name = addExtension (T.unpack (Name.toText name)) ".u"

makeDirName :: NameSegment -> String
makeDirName name = T.unpack $ NameSegment.toEscapedText name

-- Codebase ops

getFileHandle ::
  Branch0 Transaction ->
  Codebase IO Symbol Ann ->
  HashQualified Name ->
  IO (LookupResult FileHandle)
getFileHandle root0 codebase name = do
  let names = Names.makeAbsolute (Branch.toNames root0)
      nameSearch = NameSearch.makeNameSearch 10 names

  QueryResult _ hits0 <- runTransaction codebase $ hqNameQuery codebase nameSearch ExactName (Set.singleton name)
  let hits = filter ((== name) . SearchResult.name) hits0

  case hits of
    [one] -> do
      let fromRef = \case
            ReferenceDerived (Id hsh _) -> Hash hsh
            ReferenceBuiltin _ -> BuiltinName name
      case one of
        Tp tyRes -> pure $ Found $ FileHandle (fromRef $ reference tyRes) name
        Tm tmRes -> case referent tmRes of
          Ref' ref -> pure $ Found $ FileHandle (fromRef ref) name
          Con' (ConstructorReference ref _) _ -> pure $ Found $ FileHandle (fromRef ref) name
    [] -> pure NotFound
    _many -> pure $ LookupError "Ambiguous search"

getDirHandle ::
  CausalBranch Transaction ->
  Codebase IO Symbol Ann ->
  Path ->
  IO (LookupResult DirHandle)
getDirHandle root codebase path = do
  listingCausal <-
    runTransaction codebase $ getShallowCausalAtPath path root
  let hash = unCausalHash $ V2Causal.causalHash listingCausal
  pure . Found $ DirHandle hash path

getFileOrDirHandle ::
  Branch0 Transaction ->
  CausalBranch Transaction ->
  Codebase IO Symbol Ann ->
  FilePath ->
  IO (LookupResult FileOrDirHandle)
getFileOrDirHandle root0 root codebase fp = case parseFileOrDirName fp of
  Left err -> pure $ LookupError err
  Right (FileName hqName) -> fmap File <$> getFileHandle root0 codebase hqName
  Right (DirName path) -> fmap Dir <$> getDirHandle root codebase path

handleLookupResult ::
  LookupResult a ->
  IO (Either Errno a)
handleLookupResult = \case
  Found a -> pure $ Right a
  NotFound -> pure $ Left eNOENT
  LookupError err -> do
    debug (T.unpack err)
    pure $ Left eNOENT

getRoot0 ::
  (MonadIO m) =>
  Codebase m Symbol Ann ->
  -- | Project root
  CausalBranch Transaction ->
  m (Branch0 Transaction)
getRoot0 codebase root = do
  branchCache <- newBranchCache
  declTypeCache <- Cache.semispaceCache 2048
  let getDeclType = CodebaseOps.makeCachedTransaction declTypeCache CodebaseOps.getDeclType
  runTransaction codebase $ branch2to1 branchCache getDeclType =<< V2Causal.value root

-- main

-- | Construct a FuseOperations object. This contains all the FUSE operations we support, and
-- will be passed to the libfuse3 library.
makeFuseOperations ::
  Codebase IO Symbol Ann ->
  -- | Project root
  CausalBranch Transaction ->
  IO (FuseOperations FileHandle DirHandle)
makeFuseOperations codebase root = do
  root0 <- getRoot0 codebase root

  let readdir :: FilePath -> DirHandle -> IO (Either Errno [(String, Maybe FileStat)])
      readdir fp (DirHandle _hash path) = do
        debug ("readdir " <> fp)
        listingBranch <-
          (runTransaction codebase) do
            listingCausal <- getShallowCausalAtPath path root
            listingBranch <- V2Causal.value listingCausal
            pure listingBranch
        listingEntries <- lsBranch codebase listingBranch
        pure . Right . mapMaybe makeEntry $ listingEntries

      opendir :: FilePath -> IO (Either Errno DirHandle)
      opendir fp = do
        debug ("opendir " <> fp)
        case filePathToPath fp of
          Left err -> do
            debug (T.unpack $ "Error parsing namespace: " <> err)
            pure $ Left eNOENT
          Right path -> getDirHandle root codebase path >>= handleLookupResult

      releasedir :: FilePath -> DirHandle -> IO Errno
      releasedir fp _ = do
        debug ("releasedir " <> fp)
        -- nothing to do here
        pure eOK

      getattr' :: FileOrDirHandle -> IO FileStat
      getattr' fileOrDir = do
        fileOwner <- getRealUserID
        fileGroup <- getRealGroupID
        now <- getTime Realtime
        let fileID = fileOrDirID fileOrDir
            (fileOrDirMode, fileSize) = case fileOrDir of
              File {} -> (regularFileMode, 0)
              Dir {} -> (directoryMode, 4096)
            fileMode = foldl' unionFileModes fileOrDirMode [ownerReadMode, groupReadMode, otherReadMode]
        pure
          defaultFileStat
            { fileMode,
              fileID,
              linkCount = 1,
              fileOwner,
              fileGroup,
              fileSize,
              accessTimeHiRes = now,
              modificationTimeHiRes = now,
              statusChangeTimeHiRes = now
            }

      getattr :: FilePath -> Maybe FileHandle -> IO (Either Errno FileStat)
      getattr _ (Just fileHandle) = Right <$> getattr' (File fileHandle)
      getattr fp _ = do
        debug ("getattr " <> fp)
        getFileOrDirHandle root0 root codebase fp >>= \case
          NotFound -> do
            debug "No such file or directory"
            pure $ Left eNOENT
          LookupError err -> do
            debug (T.unpack err)
            pure $ Left eNOENT
          Found fileOrDir -> Right <$> getattr' fileOrDir

      open :: FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno FileHandle)
      open fp mode flags = do
        debug ("open " <> fp <> " " <> show mode <> " " <> show flags)
        case T.stripSuffix ".u" (T.pack fp) of
          Nothing -> do
            debug $ "Invalid file name: " <> fp
            pure $ Left eNOENT
          Just fileName -> case parseFileName fileName of
            Left err -> do
              debug (T.unpack err)
              pure $ Left eNOENT
            Right name -> getFileHandle root0 codebase name >>= handleLookupResult

      read :: FilePath -> FileHandle -> ByteCount -> FileOffset -> IO (Either Errno ByteString)
      read fp (FileHandle _ name) bytes offset = do
        debug ("read " <> fp)
        let names = Branch.toNames root0
            absNames = Names.makeAbsolute names
        Backend.DefinitionResults terms types _misses0 <- do
          let nameSearch = NameSearch.makeNameSearch 10 absNames
          runTransaction codebase $
            Backend.definitionsByName
              codebase
              nameSearch
              DontIncludeCycles
              ExactName
              (Set.singleton name)
        let unbiasedPPED = PPED.makePPED (PPE.hqNamer 10 names) (PPE.suffixifyByHashName names)
            pped = PPED.biasTo (maybeToList $ HQ.toName name) unbiasedPPED
            renderedCodePretty =
              fromMaybe mempty $
                fst
                  <$> renderCodePretty
                    (const True)
                    pped
                    False
                    (const False)
                    terms
                    types
                    (Defns Set.empty Set.empty)
            renderedCodeText = Pretty.toPlain 80 renderedCodePretty
            renderedCodeByteString = encodeUtf8 renderedCodeText
        pure $ Right $ BS.take (fromIntegral bytes) $ BS.drop (fromIntegral offset) renderedCodeByteString

      release :: FilePath -> FileHandle -> IO ()
      release fp _ = do
        debug ("release " <> fp)
        -- nothing to do here
        pure ()

      access :: FilePath -> AccessMode -> IO Errno
      access fp mode = do
        debug ("access " <> fp <> " " <> show mode)
        let checkFile = do
              lookup <- getFileOrDirHandle root0 root codebase fp >>= handleLookupResult
              pure $ case lookup of
                Left err -> err
                Right _ -> eOK
        case mode of
          FileOK -> checkFile
          -- can't write
          PermOK _canRead True _canExec -> pure ePERM
          -- can't execute
          PermOK _canRead _canWrite True -> pure ePERM
          -- can only read if the file exists
          PermOK _canRead _canWrite _canExec -> checkFile

      init :: FuseConfig -> IO FuseConfig
      init cfg = do
        debugM Temp "FuseConfig" cfg
        -- since we can't know the size of a "file" before we read it, in getattr (above) we
        -- return a file size of 0 for terms/types. Without the direct_io option, any program that
        -- tries to read a file with size 0 will just not call read. By setting direct_io we ensure
        -- that the whole file will be read.
        -- see https://www.kernel.org/doc/html/v6.16/filesystems/fuse-io.html
        pure cfg {directIo = True}

  {-
  Could be interesting:
    - fuseStatfs
    - fuseGetxattr / fuseListxattr
  -}

  pure
    defaultFuseOperations
      { fuseReaddir = Just readdir,
        fuseOpendir = Just opendir,
        fuseReleasedir = Just releasedir,
        fuseGetattr = Just getattr,
        fuseOpen = Just open,
        fuseRead = Just read,
        fuseRelease = Just release,
        fuseAccess = Just access,
        fuseInit = Just init
      }

-- | Main function. Initialises the FuseOperations, builds the arguments to pass to the libfuse3
-- library, and hands off to fuseRun.
fuseMain ::
  -- | Program name
  String ->
  Codebase IO Symbol Ann ->
  ProjectAndBranch ProjectName ProjectBranchName ->
  -- | Project root
  CausalBranch Transaction ->
  -- | Mount point
  FilePath ->
  IO ()
fuseMain progName codebase project root mountPoint = do
  fuseOps <- makeFuseOperations codebase root
  absMountPoint <- makeAbsolute mountPoint
  prettyMountPoint <- renderFileName absMountPoint
  unlessM (doesDirectoryExist absMountPoint) do
    PT.putPrettyLn $
      "Creating directory "
        <> prettyMountPoint
    createDirectoryIfMissing True absMountPoint

  PT.putPrettyLn $
    "Mounting "
      <> prettyProjectAndBranchName project
      <> " at "
      <> prettyMountPoint

  let fuseArgs =
        [ "-f", -- run in foreground
          "-oauto_unmount", -- unmount on exit
          absMountPoint
        ]
  fuseRun progName fuseArgs fuseOps defaultExceptionHandler

debug :: String -> IO ()
-- debug = debugLogM Temp
debug _ = pure ()
