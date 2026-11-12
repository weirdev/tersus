-- What a package load reads and gives (Modules): the snapshot it reads, the identities of modules and imports, and the
-- module graph with each file as it was read
module PackageData
    ( LoadOptions (..)
    , defaultLoadOptions
    , Resolver (..)
    , resolverReadFile
    , resolverListDir
    , resolverCanonicalRoot
    , resolverFromFiles
    , normalizePath
    , pathSegments
    , ModuleId (..)
    , renderModuleId
    , ImportLevel (..)
    , ResolvedImport (..)
    , LoadedFile (..)
    , LoadedModule (..)
    , LoadedPackage (..)
    , Snapshot (..)
    , LoadResult (..)
    , packageInputIdentity
    ) where

import Data.List (intercalate, nub, sort, stripPrefix)
import qualified Data.Map.Strict as Map

import ParsedFile (Import (..), ParsedFile (..))
import Types (Name)

pathSegments :: FilePath -> [String]
pathSegments path =
    [ segment
    | segment <- split '/' path >>= split '\\'
    , segment /= "" && segment /= "."
    ]
  where
    split sep text = case break (== sep) text of
        (chunk, _ : rest) -> chunk : split sep rest
        (chunk, []) -> [chunk]

data LoadOptions = LoadOptions
    { packageRoots :: Map.Map String FilePath
    , installedStdRoot :: Maybe FilePath
    , noPrelude :: Bool
    }
    deriving (Eq, Show)

defaultLoadOptions :: LoadOptions
defaultLoadOptions = LoadOptions Map.empty Nothing False

data Resolver = Resolver
    { resolverFiles :: Map.Map FilePath String
    , resolverDirs :: Map.Map FilePath ([String], [String])
    , resolverOptions :: LoadOptions
    , resolverCanonical :: Map.Map FilePath FilePath
    }
    deriving (Eq, Show)

resolverReadFile :: Resolver -> FilePath -> Maybe String
resolverReadFile resolver path = Map.lookup (normalizePath path) (resolverFiles resolver)

resolverListDir :: Resolver -> FilePath -> Maybe ([String], [String])
resolverListDir resolver dir = Map.lookup (normalizePath dir) (resolverDirs resolver)

resolverCanonicalRoot :: Resolver -> FilePath -> FilePath
resolverCanonicalRoot resolver root = Map.findWithDefault (normalizePath root) (normalizePath root) (resolverCanonical resolver)

normalizePath :: FilePath -> FilePath
normalizePath path =
    let absolute = take 1 path == "/"
        segments = foldl step [] (pathSegments path)
        step acc "." = acc
        step acc ".." = case acc of
            [] -> acc
            _ -> init acc
        step acc segment = acc ++ [segment]
        rendered = intercalate "/" segments
     in if absolute then "/" ++ rendered else rendered

-- | An in-memory resolver built from a list of (path, contents). The
-- directory tree is derived from the file paths: a directory exists
-- when some file lives at or below it.
resolverFromFiles :: [(FilePath, String)] -> Resolver
resolverFromFiles files = Resolver contents (Map.fromList [(dir, listing) | dir <- candidates, Just listing <- [listDir dir]]) defaultLoadOptions Map.empty
  where
    contents = Map.fromList [(normalizePath path, text) | (path, text) <- files]
    candidates = nub (["", "/"] ++ concatMap ancestors (Map.keys contents))
    ancestors path =
        let segments = pathSegments path
            lead = if take 1 path == "/" then "/" else ""
         in [lead ++ intercalate "/" (take k segments) | k <- [1 .. length segments - 1]]
    listDir dir =
        let normalized = normalizePath dir
            direct =
                [ (relative, text)
                | (path, text) <- Map.toList contents
                , Just relative <- [stripDir normalized path]
                ]
            fileNames = sort [relative | (relative, _) <- direct, '/' `notElem` relative, not (null relative)]
            subdirs = sort (nub [head parts | (relative, _) <- direct, let parts = splitOn '/' relative, length parts > 1])
         in if null direct && normalized /= "" && normalized /= "/"
                then Nothing
                else Just (subdirs, fileNames)
    stripDir "" path = Just path
    stripDir "/" path = stripPrefix "/" path
    stripDir dir path = stripPrefix (dir ++ "/") path
    splitOn sep text = case break (== sep) text of
        (chunk, _ : rest) -> chunk : splitOn sep rest
        (chunk, []) -> [chunk]

-- | A module of a package: the root module ('moduleName' = 'Nothing')
-- or one immediate subdirectory module.
data ModuleId = ModuleId
    { modulePackage :: String
    , moduleName :: Maybe String
    }
    deriving (Eq, Ord, Show)

renderModuleId :: ModuleId -> String
renderModuleId (ModuleId pkg Nothing) = pkg
renderModuleId (ModuleId pkg (Just name)) = pkg ++ "::" ++ name

data ImportLevel = LevelModule | LevelFile | LevelSymbol
    deriving (Eq, Ord, Show, Enum, Bounded)

-- | An import with its level determined and its target pinned down.
-- 'resolvedTargetFile' is a file stem, 'resolvedTargetSymbol' a
-- declaration name; both are 'Nothing' at module/file level as
-- appropriate. 'resolvedCanonical' is the $<joined canonical spelling
-- of the target, for later phases to rename against.
data ResolvedImport = ResolvedImport
    { resolvedImport :: Import
    , resolvedLevel :: ImportLevel
    , resolvedTargetModule :: ModuleId
    , resolvedTargetFile :: Maybe String
    , resolvedTargetSymbol :: Maybe String
    , resolvedCanonical :: String
    }
    deriving (Eq, Show)

data LoadedFile = LoadedFile
    { loadedFileModule :: ModuleId
    , loadedFileName :: String
    , loadedFileStem :: String
    , loadedFilePath :: FilePath
    , loadedParsed :: ParsedFile
    , loadedDeclNames :: [Name]
    , loadedImports :: [ResolvedImport]
    , loadedFileSource :: String
    }
    deriving (Show)

data LoadedModule = LoadedModule
    { loadedModuleId :: ModuleId
    , loadedModuleFiles :: [LoadedFile]
    , loadedModuleDeclNames :: [Name]
    , loadedDependencies :: [ModuleId]
    , loadedNoPrelude :: Bool
    }
    deriving (Show)

data LoadedPackage = LoadedPackage
    { packageRootDir :: FilePath
    , packagePackageName :: String
    , packageEntryFile :: FilePath
    , packageEntryModule :: ModuleId
    , packageModules :: [LoadedModule]
    , packageSources :: [(FilePath, String)]
    , packagePolicies :: [(String, FilePath, Bool)]
    , packageSnapshot :: Snapshot
    }
    deriving (Show)

-- What the host captured for a load (the files and directories it read), the entry, and whether the entry came on
-- standard input
data Snapshot = Snapshot
    { snapshotResolver :: Resolver
    , snapshotEntry :: FilePath
    , snapshotFromSource :: Bool
    }
    deriving (Show)

packageInputIdentity :: LoadedPackage -> String
packageInputIdentity pkg = show
    ( normalizePath (packageEntryFile pkg), packagePolicies pkg, packageSources pkg
    , [(loadedModuleId modu, [(loadedFilePath file, loadedImports file) | file <- loadedModuleFiles modu]) | modu <- packageModules pkg]
    )

-- | Loading an entry file either reports it as a standalone program
-- (no package marker above it; imports are then unsupported) or loads
-- its package's reachable module graph, dependencies first.
data LoadResult
    = StandaloneResult FilePath ParsedFile
    | PackageResult LoadedPackage
    deriving (Show)

