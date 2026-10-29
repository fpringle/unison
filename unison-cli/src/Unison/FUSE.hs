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
import U.Codebase.Sqlite.DbId (ProjectBranchId, ProjectId)
import U.Codebase.Sqlite.Operations (expectCausalBranchByCausalHash)
import U.Codebase.Sqlite.Project (Project)
import U.Codebase.Sqlite.ProjectBranch (ProjectBranch)
import U.Codebase.Sqlite.Queries (expectCausalHash, expectProjectBranchHead)
import Unison.Cli.Pretty (prettyProjectAndBranchName)
import Unison.Cli.ProjectUtils (justTheIds, justTheNames)
import Unison.Codebase
  ( Codebase,
    expectProjectBranchRoot,
    getShallowBranchAtPath,
    getShallowCausalAtPath,
    runTransaction,
  )
import Unison.Codebase.Branch.Names qualified as Branch
import Unison.Codebase.Branch.Type qualified as Branch
import Unison.Codebase.Editor.HandleInput.ShowDefinition (renderCodePretty)
import Unison.Codebase.Path (Path, fromList)
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
  deriving (Show, Eq, Ord)

data FileHandle = FileHandle TermOrTypeName (HashQualified Name)
  deriving (Show)

data DirHandle = DirHandle Hash Path
  deriving (Show)

data FileOrDirName = FileName (HashQualified Name) | DirName Path
  deriving (Show)

data FileOrDirHash = BuiltinTermOrType (HashQualified Name) | FileOrDirHash Hash
  deriving (Show, Eq, Ord)

fileOrDirHash :: FileOrDirHandle -> FileOrDirHash
fileOrDirHash = \case
  File (FileHandle (BuiltinName hq) _) -> BuiltinTermOrType hq
  File (FileHandle (Hash hash) _) -> FileOrDirHash hash
  Dir (DirHandle hash _) -> FileOrDirHash hash

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
  Codebase IO Symbol Ann ->
  ProjectAndBranch ProjectId ProjectBranchId ->
  HashQualified Name ->
  IO (LookupResult FileHandle)
getFileHandle codebase project name = do
  names <- Names.makeAbsolute <$> getRootNames codebase project
  let nameSearch = NameSearch.makeNameSearch 10 names

  QueryResult _ hits0 <- runTransactionTimed "hqNameQuery" codebase $ hqNameQuery codebase nameSearch ExactName (Set.singleton name)
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

-- | Useful for debugging bottlenecks. Un-comment the lines below to print timings.
runTransactionTimed :: (MonadIO m) => Text -> Codebase m v a -> Transaction b -> m b
runTransactionTimed _label codebase transaction = do
  -- start <- liftIO getCurrentTime
  res <- runTransaction codebase transaction
  -- end <- liftIO getCurrentTime
  -- liftIO $ putStrLn $ T.unpack label <> " took " <> show (diffUTCTime end start)
  pure res

getDirHandle ::
  Codebase IO Symbol Ann ->
  ProjectAndBranch ProjectId ProjectBranchId ->
  Path ->
  IO (LookupResult DirHandle)
getDirHandle codebase project path = do
  listingCausal <-
    getRoot codebase project >>= runTransactionTimed "getShallowCausalAtPath" codebase . getShallowCausalAtPath path
  let hash = unCausalHash $ V2Causal.causalHash listingCausal
  pure . Found $ DirHandle hash path

getFileOrDirHandle ::
  Codebase IO Symbol Ann ->
  ProjectAndBranch Project ProjectBranch ->
  FilePath ->
  IO (LookupResult FileOrDirHandle)
getFileOrDirHandle codebase project fp = case parseFileOrDirName fp of
  Left err -> pure $ LookupError err
  Right (FileName hqName) -> fmap File <$> getFileHandle codebase (justTheIds project) hqName
  Right (DirName path) -> fmap Dir <$> getDirHandle codebase (justTheIds project) path

handleLookupResult ::
  LookupResult a ->
  IO (Either Errno a)
handleLookupResult = \case
  Found a -> pure $ Right a
  NotFound -> pure $ Left eNOENT
  LookupError err -> do
    debug (T.unpack err)
    pure $ Left eNOENT

getShallowProjectRootByIds :: ProjectAndBranch ProjectId ProjectBranchId -> Transaction (CausalBranch Transaction)
getShallowProjectRootByIds (ProjectAndBranch projectId branchId) = do
  causalHashId <- expectProjectBranchHead projectId branchId
  causalHash <- expectCausalHash causalHashId
  expectCausalBranchByCausalHash causalHash

getRoot ::
  (MonadIO m) =>
  Codebase m Symbol Ann ->
  ProjectAndBranch ProjectId ProjectBranchId ->
  m (CausalBranch Transaction)
getRoot codebase project =
  runTransactionTimed "getShallowProjectRootByIds" codebase (getShallowProjectRootByIds project)

getRootNames ::
  (MonadIO m) =>
  Codebase m Symbol Ann ->
  ProjectAndBranch ProjectId ProjectBranchId ->
  m Names.Names
getRootNames codebase project = do
  branch <- expectProjectBranchRoot codebase project.project project.branch
  pure . Branch.toNames . Branch.head $ branch

-- main

-- | Construct a FuseOperations object. This contains all the FUSE operations we support, and
-- will be passed to the libfuse3 library.
makeFuseOperations ::
  Codebase IO Symbol Ann ->
  ProjectAndBranch Project ProjectBranch ->
  IO (FuseOperations FileHandle DirHandle)
makeFuseOperations codebase project = do
  let projectIds = justTheIds project

  listingCache :: Cache.Cache Hash [(String, Maybe FileStat)] <- Cache.semispaceCache 1024
  let getListing :: DirHandle -> IO [(String, Maybe FileStat)]
      getListing (DirHandle hash path) =
        Cache.lookup listingCache hash >>= \case
          Just v -> pure v
          Nothing -> do
            listingBranch <- do
              root <- getRoot codebase projectIds
              runTransactionTimed "getShallowBranchAtPath" codebase $ getShallowBranchAtPath path =<< V2Causal.value root
            listingEntries <- lsBranch codebase listingBranch
            let entries = mapMaybe makeEntry $ listingEntries
            Cache.insert listingCache hash entries
            pure entries

  attrCache :: Cache.Cache FileOrDirHash FileStat <- Cache.semispaceCache 8192
  let getattr' :: FileOrDirHandle -> IO FileStat
      getattr' fileOrDir = do
        let hash = fileOrDirHash fileOrDir
        Cache.lookup attrCache hash >>= \case
          Just attr -> pure attr
          Nothing -> do
            fileOwner <- getRealUserID
            fileGroup <- getRealGroupID
            now <- getTime Realtime
            let fileID = fileOrDirID fileOrDir
                (fileOrDirMode, fileSize) = case fileOrDir of
                  File {} -> (regularFileMode, 0)
                  Dir {} -> (directoryMode, 4096)
                fileMode = foldl' unionFileModes fileOrDirMode [ownerReadMode, groupReadMode, otherReadMode]
                attr =
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
            Cache.insert attrCache hash attr
            pure attr

  readCache :: Cache.Cache TermOrTypeName ByteString <- Cache.semispaceCache 8192
  let getRendered :: FileHandle -> IO ByteString
      getRendered (FileHandle termOrTypeName name) =
        Cache.lookup readCache termOrTypeName >>= \case
          Just v -> pure v
          Nothing -> do
            names <- getRootNames codebase projectIds
            let absNames = Names.makeAbsolute names
            Backend.DefinitionResults terms types _misses0 <- do
              let nameSearch = NameSearch.makeNameSearch 10 absNames
              runTransactionTimed "definitionsByName" codebase $
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
            Cache.insert readCache termOrTypeName renderedCodeByteString
            pure renderedCodeByteString

  let readdir :: FilePath -> DirHandle -> IO (Either Errno [(String, Maybe FileStat)])
      readdir fp dirHandle = do
        debug ("readdir " <> fp)
        Right <$> getListing dirHandle

      opendir :: FilePath -> IO (Either Errno DirHandle)
      opendir fp = do
        debug ("opendir " <> fp)
        case filePathToPath fp of
          Left err -> do
            debug (T.unpack $ "Error parsing namespace: " <> err)
            pure $ Left eNOENT
          Right path -> getDirHandle codebase projectIds path >>= handleLookupResult

      releasedir :: FilePath -> DirHandle -> IO Errno
      releasedir fp _ = do
        debug ("releasedir " <> fp)
        -- nothing to do here
        pure eOK

      getattr :: FilePath -> Maybe FileHandle -> IO (Either Errno FileStat)
      getattr _ (Just fileHandle) = Right <$> getattr' (File fileHandle)
      getattr fp _ = do
        debug ("getattr " <> fp)
        getFileOrDirHandle codebase project fp >>= \case
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
            Right name -> getFileHandle codebase projectIds name >>= handleLookupResult

      read :: FilePath -> FileHandle -> ByteCount -> FileOffset -> IO (Either Errno ByteString)
      read fp fileHandle bytes offset = do
        debug ("read " <> fp)
        renderedCodeByteString <- getRendered fileHandle
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
              lookup <- getFileOrDirHandle codebase project fp >>= handleLookupResult
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
  ProjectAndBranch Project ProjectBranch ->
  -- | Mount point
  FilePath ->
  IO ()
fuseMain progName codebase project mountPoint = do
  fuseOps <- makeFuseOperations codebase project
  absMountPoint <- makeAbsolute mountPoint
  prettyMountPoint <- renderFileName absMountPoint
  unlessM (doesDirectoryExist absMountPoint) do
    PT.putPrettyLn $
      "Creating directory "
        <> prettyMountPoint
    createDirectoryIfMissing True absMountPoint

  PT.putPrettyLn $
    "Mounting "
      <> prettyProjectAndBranchName (justTheNames project)
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
