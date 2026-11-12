module Modules
    ( module PackageData
    , Discovery (..)
    , discoverEntry
    , findPackageRoot
    , loadFromEntry
    , loadFromEntryWith
    , loadFromFilesystem
    , loadFromFilesystemWith
    , loadFromFilesystemWithOptions
    , loadFromSourceWith
    , snapshotFromFilesystem
    , snapshotFromFilesystemWith
    , captureFilesystemInput
    , captureSnapshot
    , entryModuleOf
    , findPackageRootIO
    , loadRequest
    , graphResult
    , librarySources
    ) where

import Control.Monad (filterM, forM_, when)
import Control.Exception (IOException, try)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (intercalate, nub, sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import System.Directory (canonicalizePath, doesDirectoryExist, doesFileExist, getCurrentDirectory, listDirectory)
import System.FilePath (isRelative, makeRelative, takeDirectory, (</>))

import ElaborateRequest (Graph (..), GraphFile (..), GraphModule (..), LoadKind (..), LoadRequest (..), LoadResponse (..))
import ElaboratorTool (Loader, bootstrapLoader)
import PackageData
import ParsedFile (Import (..), ParsedFile (..))
import qualified ParserSeed
import PreludeSource (libModules, nativeStorageModules)

-- The host's side of loading: it captures the snapshot of what a load reads (the files and directories, as the loader
-- written in Tersus asks for them; lib/elaborate/load.tersus), and the loader answers with the module graph
-- (AST_DATA.md, "Loading").

joinPath :: FilePath -> String -> FilePath
joinPath dir name
    | null dir = name
    | dir == "/" = '/' : name
    | otherwise = dir ++ "/" ++ name

dirNameOf :: FilePath -> FilePath
dirNameOf path = case pathSegments (normalizePath path) of
    [] -> if take 1 path == "/" then "/" else ""
    segments -> case init segments of
        [] -> if take 1 path == "/" then "/" else ""
        parents -> (if take 1 path == "/" then "/" else "") ++ intercalate "/" parents

baseNameOf :: FilePath -> String
baseNameOf path = case pathSegments (normalizePath path) of
    [] -> ""
    segments -> last segments

-- | What walking up from an entry file found: the entry stands alone
-- (no @package.tersus@ in any ancestor), or it belongs to a package.
data Discovery
    = Standalone FilePath
    | InPackage FilePath String
    deriving (Eq, Show)

findPackageRoot :: Resolver -> FilePath -> Maybe FilePath
findPackageRoot resolver entry = go (dirNameOf (normalizePath entry))
  where
    go dir
        | resolverReadFile resolver (joinPath dir "package.tersus") /= Nothing = Just dir
        | parent == dir = Nothing
        | otherwise = go parent
      where
        parent = dirNameOf dir

discoverEntry :: Resolver -> FilePath -> Discovery
discoverEntry resolver entry = case findPackageRoot resolver (normalizePath entry) of
    Nothing -> Standalone (normalizePath entry)
    Just root -> InPackage root (baseNameOf root)

-- Package layout, as the resolver reports it (no file contents yet).

data FileEntry = FileEntry
    { feName :: String
    , feStem :: String
    , fePath :: FilePath
    }
    deriving (Eq, Show)

data Layout = Layout
    { layName :: String
    , layRootFiles :: [FileEntry]
    , layModules :: Map.Map String [FileEntry]
    }

tersusFiles :: FilePath -> [String] -> [FileEntry]
tersusFiles dir names =
    [ FileEntry name (takeWhile (/= '.') name) (joinPath dir name)
    | name <- sort names
    , ".tersus" `isSuffixOf` name
    ]
  where
    isSuffixOf suffix text = drop (length text - length suffix) text == suffix

buildLayout :: Resolver -> FilePath -> Either String Layout
buildLayout resolver root = case resolverListDir resolver root of
    Nothing -> Left ("package directory " ++ root ++ " not found")
    Just (subdirs, files) ->
        let moduleOf sub = case resolverListDir resolver (joinPath root sub) of
                Nothing -> Nothing
                Just (_, subFiles) ->
                    let entries = tersusFiles (joinPath root sub) subFiles
                     in if null entries then Nothing else Just (sub, entries)
         in Right
                Layout
                    { layName = baseNameOf root
                    , layRootFiles = [entry | entry <- tersusFiles root files, feName entry /= "package.tersus"]
                    , layModules = Map.fromList [entry | Just entry <- map moduleOf subdirs]
                    }

layoutModuleFiles :: Layout -> Maybe String -> [FileEntry]
layoutModuleFiles layout Nothing = layRootFiles layout
layoutModuleFiles layout (Just name) = fromMaybe [] (Map.lookup name (layModules layout))

layoutCollapsedFile :: Layout -> Maybe String -> Maybe FileEntry
layoutCollapsedFile layout moduleName =
    let entries = layoutModuleFiles layout moduleName
        dirLabel = fromMaybe (layName layout) moduleName
     in case entries of
            [entry] | feStem entry == dirLabel -> Just entry
            _ -> Nothing

-- (the root declarations the loader written in Tersus reads to disambiguate an import, rootProbe in load.tersus: the
-- snapshot has to hold every file it reads, or the load sees the file as absent)
rootProbeEntries :: Layout -> [String] -> [FileEntry]
rootProbeEntries layout path = case path of
    [name]
        | Map.member name (layModules layout) || any ((== name) . feStem) (layRootFiles layout) -> maybe [] pure (layoutCollapsedFile layout Nothing)
        | otherwise -> layRootFiles layout
    [name, _, _] | Map.member name (layModules layout) -> []
    name : _ -> filter ((== name) . feStem) (layRootFiles layout)
    [] -> layRootFiles layout

requestedRoots :: LoadOptions -> String -> [FilePath]
requestedRoots options pkg = nub (map normalizePath
    (maybe [] pure (Map.lookup pkg (packageRoots options))
        ++ [root | pkg == "std", Just root <- [installedStdRoot options]]))

eligibleRoots :: LoadOptions -> Maybe (String, FilePath) -> String -> (FilePath -> Bool) -> [FilePath]
eligibleRoots options context pkg marker = requestedRoots options pkg ++ case context of
    Nothing -> []
    Just (name, root) -> [root | pkg == name] ++ [sibling | marker sibling]
      where sibling = joinPath (dirNameOf root) pkg

loadFromEntry :: Resolver -> FilePath -> Either String LoadResult
loadFromEntry = loadFromEntryWith bootstrapLoader

loadFromEntryWith :: Loader -> Resolver -> FilePath -> Either String LoadResult
loadFromEntryWith loader resolver entry = graphResult (Snapshot resolver (normalizePath entry) False) loader

-- Snapshot reachable modules and the root declarations used to disambiguate
-- imports; directory metadata does not require unrelated source contents.

findPackageRootIO :: FilePath -> IO (Maybe FilePath)
findPackageRootIO entry = go (takeDirectory entry)
  where
    go dir = do
        present <- doesFileExist (dir </> "package.tersus")
        if present
            then return (Just dir)
            else do
                let parent = takeDirectory dir
                if parent == dir then return Nothing else go parent

loadFromFilesystem :: FilePath -> IO (Either String LoadResult)
loadFromFilesystem = loadFromFilesystemWith bootstrapLoader

loadFromFilesystemWith :: Loader -> FilePath -> IO (Either String LoadResult)
loadFromFilesystemWith loader = loadFromFilesystemWithOptions loader defaultLoadOptions

loadFromFilesystemWithOptions :: Loader -> LoadOptions -> FilePath -> IO (Either String LoadResult)
loadFromFilesystemWithOptions loader options entry = loadFilesystemInput loader options entry Nothing

loadFromSourceWith :: Loader -> LoadOptions -> String -> IO (Either String LoadResult)
loadFromSourceWith loader options source = loadFilesystemInput loader options "<stdin>.tersus" (Just source)

loadFilesystemInput :: Loader -> LoadOptions -> FilePath -> Maybe String -> IO (Either String LoadResult)
loadFilesystemInput loader options rawEntry source = do
    snapshot <- captureFilesystemInput options rawEntry source
    pure $ case snapshot of
        Left err -> Left err
        Right (resolver, entry, _) -> graphResult (Snapshot resolver entry (source /= Nothing)) loader

captureFilesystemInput :: LoadOptions -> FilePath -> Maybe String -> IO (Either String (Resolver, FilePath, String))
captureFilesystemInput options rawEntry source = do
    snapshot <- try (do
        (resolved, entry) <- resolveFilesystemInputs options rawEntry
        (resolver, _, identity) <- filesystemSnapshot resolved entry source
        pure (resolver, entry, identity)) :: IO (Either IOException (Resolver, FilePath, String))
    pure $ case snapshot of
        Left err -> Left ("source snapshot for " ++ rawEntry ++ ": " ++ show err)
        Right captured -> Right captured

resolveFilesystemInputs :: LoadOptions -> FilePath -> IO (LoadOptions, FilePath)
resolveFilesystemInputs options entry
    | Map.null (packageRoots options) && installedStdRoot options == Nothing = do
        physical <- canonicalizePath entry
        cwd <- getCurrentDirectory
        let path = if isRelative entry then makeRelative cwd physical else physical
        pure (options, normalizePath path)
    | otherwise = do
        roots <- mapM canonicalizePath (packageRoots options)
        std <- mapM canonicalizePath (installedStdRoot options)
        canonical <- canonicalizePath entry
        pure (options{packageRoots = roots, installedStdRoot = std}, normalizePath canonical)

snapshotFromFilesystem :: FilePath -> IO [(FilePath, String)]
snapshotFromFilesystem = snapshotFromFilesystemWith defaultLoadOptions

snapshotFromFilesystemWith :: LoadOptions -> FilePath -> IO [(FilePath, String)]
snapshotFromFilesystemWith options rawEntry = do
    (resolved, entry) <- resolveFilesystemInputs options rawEntry
    (_, files, _) <- filesystemSnapshot resolved entry Nothing
    pure files

filesystemSnapshot :: LoadOptions -> FilePath -> Maybe String -> IO (Resolver, [(FilePath, String)], String)
filesystemSnapshot options rawEntry source = do
    contents <- newIORef Map.empty
    directories <- newIORef Map.empty
    visited <- newIORef Set.empty
    roots <- newIORef Map.empty
    canonicalRoots <- newIORef Map.empty
    cwd <- getCurrentDirectory
    let canonicalRoot root = do
            physical <- canonicalizePath root
            let path = normalizePath (if isRelative rawEntry then makeRelative cwd physical else physical)
            modifyIORef' canonicalRoots (Map.insert (normalizePath root) path)
            pure path
        entry = normalizePath rawEntry
        readSource path = do
            saved <- readIORef contents
            case Map.lookup path saved of
                Just text -> pure text
                Nothing -> do
                    text <- readFile path
                    length text `seq` modifyIORef' contents (Map.insert path text)
                    pure text
        readMarker root = do
            let marker = joinPath root "package.tersus"
            present <- doesFileExist marker
            when present (readSource marker >> pure ())
            pure present
        readDirectory dir = do
            saved <- readIORef directories
            case Map.lookup dir saved of
                Just names -> pure names
                Nothing -> do
                    exists <- doesDirectoryExist (if null dir then "." else dir)
                    names <- if not exists then pure ([], []) else do
                        allNames <- sort <$> listDirectory (if null dir then "." else dir)
                        subdirs <- filterM (doesDirectoryExist . joinPath dir) allNames
                        files <- filterM (doesFileExist . joinPath dir) allNames
                        pure (subdirs, files)
                    modifyIORef' directories (Map.insert dir names)
                    pure names
        rootDirectories root = do
            (subdirs, _) <- readDirectory root
            forM_ subdirs (\sub -> readDirectory (joinPath root sub) >> pure ())
        readRootProbes root pkg path = do
            saved <- readIORef contents
            dirs <- readIORef directories
            let resolver = (resolverFromFiles (Map.toAscList saved)){resolverDirs = dirs}
            case buildLayout resolver root of
                Left _ -> pure ()
                Right layout -> forM_ (rootProbeEntries layout{layName = pkg} path) (\file -> readSource (fePath file) >> pure ())
        walkModule root pkg name = do
            seen <- readIORef visited
            let key = (root, name)
            when (Set.notMember key seen) $ do
                modifyIORef' visited (Set.insert key)
                rootDirectories root
                let dir = maybe root (joinPath root) name
                (_, files) <- readDirectory dir
                forM_ [file | file <- tersusFiles dir files, feName file /= "package.tersus"] $ \file -> do
                    text <- readSource (fePath file)
                    walkImports root (Just pkg) text
        walkImports root pkg text = case ParserSeed.parseImportPrefix text of
            Left err | ParserSeed.toolFailure err -> ioError (userError err)
                     | otherwise -> pure ()
            Right imports -> forM_ imports $ \imp -> do
                let targetPkg = head (importPath imp)
                    rest = tail (importPath imp)
                    requested = requestedRoots options targetPkg
                    sibling = joinPath (dirNameOf root) targetPkg
                known <- Map.lookup targetPkg <$> readIORef roots
                siblingPresent <- if pkg == Nothing then pure False else readMarker sibling
                forM_ requested (\candidate -> readMarker candidate >> pure ())
                let context = fmap (\name -> (name, root)) pkg
                candidates <- fmap nub (mapM canonicalRoot (eligibleRoots options context targetPkg (\path -> path == sibling && siblingPresent)))
                present <- mapM readMarker candidates
                when (and present && length candidates == 1 && maybe True (== head candidates) known) $ do
                    let target = head candidates
                    modifyIORef' roots (Map.insert targetPkg target)
                    rootDirectories target
                    dirs <- readIORef directories
                    let isModule m = case Map.lookup (joinPath target m) dirs of
                            Just (_, files) -> not (null (tersusFiles (joinPath target m) files))
                            Nothing -> False
                        name = case rest of
                            m : _ | isModule m -> Just m
                            _ -> Nothing
                    readRootProbes target targetPkg rest
                    walkModule target targetPkg name
    case source of
        Just text -> do
            modifyIORef' contents (Map.insert entry text)
            walkImports (dirNameOf entry) Nothing text
        Nothing -> do
            root <- findPackageRootIO entry
            case root of
                Nothing -> do
                    exists <- doesFileExist entry
                    when exists $ do
                        text <- readSource entry
                        walkImports (dirNameOf entry) Nothing text
                Just packageRoot -> do
                    let normalized = normalizePath packageRoot
                        pkg = baseNameOf normalized
                        dir = dirNameOf entry
                        name = if dir == normalized then Nothing else Just (baseNameOf dir)
                    _ <- readMarker normalized
                    modifyIORef' roots (Map.insert pkg normalized)
                    walkModule normalized pkg name
    files <- Map.toAscList <$> readIORef contents
    dirs <- readIORef directories
    canonical <- readIORef canonicalRoots
    selectedRoots <- readIORef roots
    let resolver = (resolverFromFiles files){resolverOptions = options, resolverDirs = dirs, resolverCanonical = canonical}
        identity = show (options, entry, if isRelative entry then Just cwd else Nothing,
            files, Map.toAscList dirs, Map.toAscList selectedRoots, Map.toAscList canonical)
    pure (resolver, files, identity)

-- ---------------------------------------------------------------------------
-- The load the loader written in Tersus answers

loadRequest :: LoadKind -> Snapshot -> LoadRequest
loadRequest kind (Snapshot resolver entry source) = LoadRequest kind False resolver (Just (entry, source)) librarySources []

-- A snapshot of the filesystem as loading the entry reads it (or of the given source as the entry, read from standard
-- input)
captureSnapshot :: LoadOptions -> FilePath -> Maybe String -> IO (Either String Snapshot)
captureSnapshot options rawEntry source = do
    captured <- captureFilesystemInput options (maybe rawEntry (const "<stdin>.tersus") source) source
    pure (fmap (\(resolver, entry, _) -> Snapshot resolver entry (source /= Nothing)) captured)

-- The module a load of the snapshot enters at (loadLayout in load.tersus): a program alone, or one from standard input,
-- is the module of no package
entryModuleOf :: Snapshot -> ModuleId
entryModuleOf (Snapshot resolver rawEntry source) = case findPackageRoot resolver entry of
    Just root | not source, dirNameOf entry == root -> ModuleId (baseNameOf root) Nothing
    Just root | not source -> ModuleId (baseNameOf root) (Just (baseNameOf (dirNameOf entry)))
    _ -> ModuleId "" Nothing
  where
    entry = normalizePath rawEntry

librarySources :: [(String, Bool, String)]
librarySources = [(name, name `elem` nativeStorageModules, text) | (name, _, text) <- libModules]

graphResult :: Snapshot -> Loader -> Either String LoadResult
graphResult snapshot loader = case loader (loadRequest LoadGraph snapshot) of
    NotLoaded message -> Left message
    LoadedStandalone path body -> Right (StandaloneResult path (ParsedFile [] body))
    LoadedGraph graph -> Right (PackageResult (packageOfGraph snapshot graph))
    _ -> Left "internal: the loader did not answer with a module graph"

packageOfGraph :: Snapshot -> Graph -> LoadedPackage
packageOfGraph snapshot graph = LoadedPackage (graphRoot graph) (graphName graph) (graphEntry graph) (graphEntryModule graph) (map loadedModule (graphModules graph))
    [(path, text) | path <- graphSources graph, Just text <- [resolverReadFile resolver path]] (graphPolicies graph) snapshot
  where
    resolver = snapshotResolver snapshot
    loadedModule m = LoadedModule (gmId m) (map (loadedFile (gmId m)) (gmFiles m)) (sort (nub (concatMap gfDeclNames (gmFiles m)))) (gmDependencies m) (gmNoPrelude m)
    loadedFile modu f = LoadedFile modu (gfName f) (gfStem f) (gfPath f)
        (ParsedFile [imp | (imp, _, _, _, _, _) <- gfImports f] (gfBody f)) (gfDeclNames f)
        [ResolvedImport imp level target file symbol canonical | (imp, level, target, file, symbol, canonical) <- gfImports f]
        (fromMaybe "" (resolverReadFile resolver (gfPath f)))

