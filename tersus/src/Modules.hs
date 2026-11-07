module Modules
    ( ModuleIdentity (..)
    , rootModuleIdentity
    , fileModuleIdentity
    , canonicalPrefix
    , canonicalName
    , declarationNames
    , canonicalizeDeclarations
    , Resolver (..)
    , LoadOptions (..)
    , defaultLoadOptions
    , packageInputIdentity
    , resolverFromFiles
    , normalizePath
    , Discovery (..)
    , discoverEntry
    , findPackageRoot
    , ModuleId (..)
    , renderModuleId
    , ImportLevel (..)
    , ResolvedImport (..)
    , importPrefixes
    , LoadedFile (..)
    , LoadedModule (..)
    , LoadedPackage (..)
    , LoadResult (..)
    , FileParser
    , loadFromEntry
    , loadFromEntryWith
    , loadFromFilesystem
    , loadFromFilesystemWith
    , loadFromFilesystemWithOptions
    , loadFromSourceWith
    , snapshotFromFilesystem
    , snapshotFromFilesystemWith
    , findPackageRootIO
    ) where

import Control.Monad (filterM, forM_, when)
import Control.Exception (IOException, try)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (intercalate, isPrefixOf, nub, sort, stripPrefix)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import System.Directory (canonicalizePath, doesDirectoryExist, doesFileExist, getCurrentDirectory, listDirectory)
import System.FilePath (isRelative, makeRelative, takeDirectory, (</>))
import qualified Text.Parsec as Config
import qualified Text.Parsec.Token as Token
import Text.Parsec.Language (emptyDef)

import qualified ParsedFile as Parse
import qualified ParserSeed
import LibParsed (LibParsed (..), libParsed)
import ParsedFile (Decls, Import (..), ParsedFile (..), emptyDecls, locating, renderPath)
import Syntax
import Types hiding (baseNameOf)

data ModuleIdentity = ModuleIdentity
    { identityPackageDir :: FilePath
    , identityModuleDir :: FilePath
    , identityFile :: FilePath
    , identityIsRoot :: Bool
    }
    deriving (Eq, Show)

rootModuleIdentity :: FilePath -> FilePath -> ModuleIdentity
rootModuleIdentity packageDir file = ModuleIdentity packageDir packageDir file True

fileModuleIdentity :: FilePath -> FilePath -> FilePath -> ModuleIdentity
fileModuleIdentity packageDir moduleDir file = ModuleIdentity packageDir moduleDir file False

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

fileStem :: FilePath -> String
fileStem file = case pathSegments file of
    [] -> ""
    segments -> takeWhile (/= '.') (last segments)

canonicalPrefix :: ModuleIdentity -> Maybe String
canonicalPrefix identity
    | identityIsRoot identity = Nothing
    | otherwise =
        Just
            ( intercalate
                "$"
                ( pathSegments (identityPackageDir identity)
                    ++ pathSegments (identityModuleDir identity)
                    ++ [fileStem (identityFile identity)]
                )
            )

canonicalName :: ModuleIdentity -> Name -> Name
canonicalName identity local = case canonicalPrefix identity of
    Nothing -> local
    Just prefix -> prefix ++ "$" ++ local

declarationNames :: [Statement] -> [Name]
declarationNames = concatMap top
  where
    top stmt = case stmt of
        StructDef name _ _ _ -> [name]
        EnumDef name variants -> name : map fst variants
        TraitDef name _ _ -> [name]
        Assign name (Val VFunct{}) -> [name]
        BoundedDef _ inner -> top inner
        AxiomDef name _ _ _ -> [name]
        ProofDef name _ _ _ _ -> [name]
        ImplDef _ _ _ _ _ functions -> concatMap top functions
        _ -> []

canonicalizeDeclarations :: ModuleIdentity -> [Statement] -> [Statement]
canonicalizeDeclarations identity statements
    | identityIsRoot identity = statements
    | otherwise = map renameStatement statements
  where
    locals = Set.fromList [name | name <- declarationNames statements, '<' `notElem` name]
    canon name
        | Set.member name locals = canonicalName identity name
        | otherwise = name
    renameType ty = case ty of
        TNamed base args -> TNamed (canon base) (map renameArg args)
        TVariant name -> TVariant (renameVariant name)
        TList t -> TList (renameType t)
        TArrayOf t size -> TArrayOf (renameType t) size
        TBox t -> TBox (renameType t)
        TAddr t -> TAddr (renameType t)
        TBlock t -> TBlock (renameType t)
        TUninit t -> TUninit (renameType t)
        TRef t -> TRef (renameType t)
        TMutRef t -> TMutRef (renameType t)
        TFn args ret -> TFn (map renameType args) (renameType ret)
        TForall sizes types t -> TForall sizes types (renameType t)
        other -> other
    renameNamed name = case break (== '<') name of
        (base, rest@('<' : _)) -> canon base ++ rest
        _ -> canon name
    renameArg (ArgType t) = ArgType (renameType t)
    renameArg other = other
    renameVariant name =
        let segments = splitOn "::" name
         in case segments of
                owner : rest@(_ : _) | Set.member owner locals -> canonicalName identity owner ++ "::" ++ intercalate "::" rest
                _ -> name
    splitOn needle = go
      where
        go text
            | needle `isPrefixOf` text = "" : go (drop (length needle) text)
            | otherwise = case text of
                c : rest -> case go rest of
                    [] -> [[c]]
                    (chunk : chunks) -> (c : chunk) : chunks
                [] -> [[]]
    renameSignature (Signature params ret sizes types writes from) =
        Signature (map renameType params) (renameType ret) sizes types writes from
    renameFunction stmt = case stmt of
        Assign name (Val (VFunct params ins outs body exported)) ->
            Assign
                (renameAssignName name)
                (Val (VFunct params ins outs (renameBody body) exported))
        other -> other
    renameAssignName name
        | Set.member name locals = canonicalName identity name
        | '<' `elem` name = renameImplFunction name
        | otherwise = name
    renameImplFunction name =
        let (inside, rest) = break (== '>') name
            function = drop 3 rest
            ownerAndTrait = drop 1 inside
         in case stripPrefix "" ownerAndTrait of
                _ -> case breakOn " as " ownerAndTrait of
                    Just (owner, trait) -> implFunctionName (renameNamed owner) (Just (canon trait)) function
                    Nothing -> implFunctionName (renameNamed ownerAndTrait) Nothing function
    breakOn needle = go ""
      where
        go acc text
            | needle `isPrefixOf` text = Just (reverse acc, drop (length needle) text)
            | otherwise = case text of
                c : rest -> go (c : acc) rest
                [] -> Nothing
    renameBody (NativeFunct signature termination body) = NativeFunct (renameSignature signature) termination body
    renameBody other = other
    renameStatement stmt = case stmt of
        StructDef name params fields invariant ->
            StructDef (canon name) params [(field, renameType ty) | (field, ty) <- fields] invariant
        EnumDef name variants ->
            EnumDef (canon name) [(renameVariant variant, [(field, renameType ty) | (field, ty) <- fields]) | (variant, fields) <- variants]
        TraitDef name params functions ->
            TraitDef (canon name) params [fn{traitFnSignature = renameSignature (traitFnSignature fn)} | fn <- functions]
        Assign{} -> renameFunction stmt
        BoundedDef bounds inner ->
            BoundedDef [(param, canon trait, map renameType args) | (param, trait, args) <- bounds] (renameFunction inner)
        AxiomDef name args ins outs -> AxiomDef (canon name) args ins outs
        ProofDef name args ins outs body -> ProofDef (canon name) args ins outs body
        ImplDef trait traitArgs typeName selfName bounds functions ->
            ImplDef
                (fmap canon trait)
                (map renameArg traitArgs)
                (renameNamed typeName)
                (renameType selfName)
                [(param, canon boundTrait, map renameType args) | (param, boundTrait, args) <- bounds]
                (map renameFunction functions)
        ExternDef name -> ExternDef (canon name)
        LinearDef name -> LinearDef (canon name)
        CopyDef name -> CopyDef (canon name)
        DropDef name -> DropDef (canon name)
        other -> other

-- ---------------------------------------------------------------------------
-- Package discovery, module graph and loader (Phase 2)
--
-- Packages, paths and identity:
--   * A package root is a directory containing a @package.tersus@ marker.
--   * The package name is the basename of that directory.
--   * Modules are the package root itself (the root module) plus each
--     immediate subdirectory of the root that holds @.tersus@ files.
--     Anything deeper is not a module; naming it is an error.
--   * An import path is a logical @a::b::c@ name rooted at a package name:
--     segment 1 is the package (this package, or a sibling package beside
--     the package root), segment 2 is the module (absent for the root
--     module), segment 3 is the file (absent under the single-file
--     collapse), segment 4 is the symbol.
--   * Single-file collapse: a module whose directory holds exactly one
--     @.tersus@ file named after the directory contributes that file's
--     symbols at module level, so @pkg::geo::Point@ can name a symbol of
--     @geo/geo.tersus@. Once the directory grows a second file the
--     collapsed spelling stops working; the loader says so, giving both
--     spellings (see the growth diagnostic in 'resolveInPackage').

-- | The resolver abstracts every filesystem question the pure loader
-- asks, so unit tests run entirely in memory:
--
--   * 'resolverReadFile' returns a file's contents by path, if present.
--   * 'resolverListDir' returns, for a directory, its immediate
--     subdirectory names and its immediate file names, if the directory
--     exists in the resolver's world.
--
-- Paths handed to a resolver are normalized (see 'normalizePath'):
-- @/@-separated, with @.@ components dropped and @..@ resolved
-- textually. The filesystem resolver ('loadFromFilesystem') snapshots
-- the relevant directories into exactly this shape.
data LoadOptions = LoadOptions
    { packageRoots :: Map.Map String FilePath
    , installedStdRoot :: Maybe FilePath
    , noPrelude :: Bool
    }
    deriving (Eq, Show)

defaultLoadOptions :: LoadOptions
defaultLoadOptions = LoadOptions Map.empty Nothing False

data Resolver = Resolver
    { resolverReadFile :: FilePath -> Maybe String
    , resolverListDir :: FilePath -> Maybe ([String], [String])
    , resolverOptions :: LoadOptions
    , resolverCanonicalRoot :: FilePath -> FilePath
    }

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

-- | An in-memory resolver built from a list of (path, contents). The
-- directory tree is derived from the file paths: a directory exists
-- when some file lives at or below it.
resolverFromFiles :: [(FilePath, String)] -> Resolver
resolverFromFiles files = Resolver readFile listDir defaultLoadOptions normalizePath
  where
    contents = Map.fromList [(normalizePath path, text) | (path, text) <- files]
    readFile path = Map.lookup (normalizePath path) contents
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
    deriving (Eq, Ord, Show)

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

importPrefixes :: String -> Bool -> Name -> ResolvedImport -> [[String]]
importPrefixes fileSeg isCollapsed local ri =
    let imp = resolvedImport ri
        modu = resolvedTargetModule ri
        pkgName = modulePackage modu
        moduleSeg = fromMaybe pkgName (moduleName modu)
        modSegs = maybe [] pure (moduleName modu)
        alias = importAlias imp
        bareForListed = case importNames imp of
            Just names -> local `elem` names || takeWhile (/= ':') local `elem` names
            Nothing -> False
        levelPrefixes = case resolvedLevel ri of
            LevelSymbol -> [[]]
            LevelFile -> [[fileSeg]] ++ maybe [] (\name -> [[name]]) alias
            LevelModule ->
                let full = [pkgName] ++ modSegs ++ [fileSeg]
                    shortened = [moduleSeg, fileSeg]
                    collapsedFull = [pkgName] ++ modSegs
                    collapsedShort = [moduleSeg]
                    bases = [shortened, full] ++ (if isCollapsed then [collapsedShort, collapsedFull] else [])
                    aliased = maybe [] (\name -> [[name, fileSeg]] ++ (if isCollapsed then [[name]] else [])) alias
                 in bases ++ aliased
     in (if bareForListed || resolvedLevel ri == LevelSymbol then [[]] else []) ++ levelPrefixes

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

-- Package layout, as the resolver reports it (no file contents yet).

data FileEntry = FileEntry
    { feName :: String
    , feStem :: String
    , fePath :: FilePath
    }
    deriving (Eq, Show)

data Layout = Layout
    { layName :: String
    , layRoot :: FilePath
    , layRootFiles :: [FileEntry]
    , layModules :: Map.Map String [FileEntry]
    , layModuleNested :: Map.Map String [String]
    , layRootSubdirs :: [String]
    , layNoPrelude :: Bool
    , layIsPackage :: Bool
    }

tersusFiles :: FilePath -> [String] -> [FileEntry]
tersusFiles dir names =
    [ FileEntry name (takeWhile (/= '.') name) (joinPath dir name)
    | name <- sort names
    , ".tersus" `isSuffixOf` name
    ]
  where
    isSuffixOf suffix text = drop (length text - length suffix) text == suffix

packageNoPrelude :: Resolver -> FilePath -> Either String Bool
packageNoPrelude resolver root = case resolverReadFile resolver marker of
    Nothing -> Left ("package marker not found: " ++ marker)
    Just source -> case Config.parse parser marker source of
        Left err -> Left ("package configuration: " ++ show err)
        Right enabled -> Right enabled
  where
    marker = joinPath root "package.tersus"
    lexer = Token.makeTokenParser emptyDef
        { Token.commentLine = "//", Token.commentStart = "", Token.commentEnd = ""
        , Token.reservedNames = ["noPrelude", "true", "false"]
        }
    parser = do
        Token.whiteSpace lexer
        enabled <- Config.option False $ do
            Token.reserved lexer "noPrelude"
            _ <- Token.symbol lexer "="
            value <- (Token.reserved lexer "true" >> pure True) Config.<|> (Token.reserved lexer "false" >> pure False)
            _ <- Token.semi lexer
            pure value
        Config.eof
        pure enabled

buildLayout :: Resolver -> FilePath -> Either String Layout
buildLayout resolver root = case resolverListDir resolver root of
    Nothing -> Left ("package directory " ++ root ++ " not found")
    Just (subdirs, files) -> do
        enabled <- packageNoPrelude resolver root
        let moduleOf sub = case resolverListDir resolver (joinPath root sub) of
                Nothing -> Nothing
                Just (nested, subFiles) ->
                    let entries = tersusFiles (joinPath root sub) subFiles
                     in if null entries then Nothing else Just (sub, entries, nested)
            found = [entry | Just entry <- map moduleOf subdirs]
        Right
            Layout
                { layName = baseNameOf root
                , layRoot = root
                , layRootFiles = [entry | entry <- tersusFiles root files, feName entry /= "package.tersus"]
                , layModules = Map.fromList [(sub, entries) | (sub, entries, _) <- found]
                , layModuleNested = Map.fromList [(sub, nested) | (sub, _, nested) <- found]
                , layRootSubdirs = subdirs
                , layNoPrelude = enabled || noPrelude (resolverOptions resolver)
                , layIsPackage = True
                }

layoutModuleId :: Layout -> Maybe String -> ModuleId
layoutModuleId layout = ModuleId (layName layout)

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

rootProbeEntries :: Layout -> [String] -> [FileEntry]
rootProbeEntries layout path = case path of
    [name]
        | Map.member name (layModules layout) || any ((== name) . feStem) (layRootFiles layout) -> maybe [] pure (layoutCollapsedFile layout Nothing)
        | otherwise -> layRootFiles layout
    [name, _, _] | Map.member name (layModules layout) -> []
    name : _ -> filter ((== name) . feStem) (layRootFiles layout)
    [] -> layRootFiles layout

-- Loader state for the pure core.

data PFile = PFile
    { pfEntry :: FileEntry
    , pfParsed :: ParsedFile
    , pfDecls :: [Name]
    , pfSource :: String
    }

data PModule = PModule
    { pmLayout :: Layout
    , pmId :: ModuleId
    , pmMaybeName :: Maybe String
    , pmFiles :: [PFile]
    }

type FileParser = Decls -> String -> Either String (ParsedFile, Decls)

bootstrapFileParser :: FileParser
bootstrapFileParser = ParserSeed.parseFileWith

data LState = LState
    { lsFileParser :: FileParser
    , lsLayouts :: Map.Map String Layout
    , lsParsed :: Map.Map ModuleId PModule
    , lsParsing :: [ModuleId]
    , lsResolved :: Map.Map (ModuleId, String) [ResolvedImport]
    , lsOrder :: [ModuleId]
    , lsDone :: Set.Set ModuleId
    , lsProbes :: Map.Map FilePath String
    }

newtype LoadM a = LoadM {runLoadM :: LState -> Either String (LState, a)}

instance Functor LoadM where
    fmap f (LoadM action) = LoadM (\state -> case action state of
        Left err -> Left err
        Right (state', value) -> Right (state', f value))

instance Applicative LoadM where
    pure value = LoadM (\state -> Right (state, value))
    LoadM mf <*> LoadM ma = LoadM (\state -> case mf state of
        Left err -> Left err
        Right (state', f) -> case ma state' of
            Left err -> Left err
            Right (state'', value) -> Right (state'', f value))

instance Monad LoadM where
    LoadM action >>= next = LoadM (\state -> case action state of
        Left err -> Left err
        Right (state', value) -> runLoadM (next value) state')

pureM :: a -> LoadM a
pureM = pure

failM :: String -> LoadM a
failM err = LoadM (\_ -> Left err)

getM :: LoadM LState
getM = LoadM (\state -> Right (state, state))

modifyM :: (LState -> LState) -> LoadM ()
modifyM f = LoadM (\state -> Right (f state, ()))

mapM_M :: (a -> LoadM b) -> [a] -> LoadM [b]
mapM_M = mapM

-- Declarations-only enforcement.

isDeclaration :: Statement -> Bool
isDeclaration stmt = case stmt of
    Assign _ (Val VFunct{}) -> True
    StructDef{} -> True
    EnumDef{} -> True
    TraitDef{} -> True
    ImplDef{} -> True
    BoundedDef _ inner -> isDeclaration inner
    ExternDef{} -> True
    AxiomDef{} -> True
    ProofDef{} -> True
    Mark{} -> True
    CopyDef{} -> True
    LinearDef{} -> True
    DropDef{} -> True
    _ -> False

statementKind :: Statement -> String
statementKind stmt = case stmt of
    Assign{} -> "an assignment"
    Return{} -> "a return"
    If{} -> "an if statement"
    While{} -> "a while statement"
    Block{} -> "a block"
    ValidationStatement{} -> "a validation statement"
    Let{} -> "a let"
    AssignDeref{} -> "an assignment"
    Dissolve{} -> "a dissolve"
    _ -> "a statement"

checkDeclarationsOnly :: ModuleId -> FileEntry -> Bool -> [Statement] -> Either String ()
checkDeclarationsOnly _ _ True _ = Right ()
checkDeclarationsOnly moduleId entry False body = go 1 body
  where
    go _ [] = Right ()
    go line (stmt : rest) = case stmt of
        Mark line' _ -> go line' rest
        _
            | isDeclaration stmt -> go line rest
            | otherwise ->
                Left
                    ( "in module "
                        ++ renderModuleId moduleId
                        ++ " file "
                        ++ fePath entry
                        ++ ":"
                        ++ show line
                        ++ ": modules declare, programs run: "
                        ++ statementKind stmt
                        ++ " is not a declaration"
                    )

-- Imported constructors must be available before the body can parse.
-- The entry file is exempt from declarations-only.
parseModule :: Resolver -> FilePath -> Layout -> Maybe String -> LoadM PModule
parseModule resolver entryPath layout moduleName = do
    state <- getM
    let moduleId = layoutModuleId layout moduleName
    case Map.lookup moduleId (lsParsed state) of
        Just parsed -> pureM parsed
        Nothing
            | moduleId `elem` lsParsing state -> failM ("module import cycle: " ++ intercalate " -> " (map renderModuleId (dropWhile (/= moduleId) (lsParsing state) ++ [moduleId])))
            | otherwise -> do
                modifyM (\s -> s{lsParsing = lsParsing s ++ [moduleId]})
                seeds <- mapM_M importSeedFor entries
                files <- parseFiles (lsFileParser state) seeds
                let parsed = PModule layout moduleId moduleName files
                modifyM (\s -> s{lsParsed = Map.insert moduleId parsed (lsParsed s), lsParsing = lsParsing state})
                pureM parsed
  where
    moduleId = layoutModuleId layout moduleName
    entries = layoutModuleFiles layout moduleName
    parseFiles fileParser seeds = do
        texts <- mapM_M readEntry entries
        case parseModuleFiles fileParser resolver layout moduleId entries seeds texts of
            Left err -> failM err
            Right parsedFiles -> mapM_M checkOne (zip texts parsedFiles)
      where
        readEntry entry = case resolverReadFile resolver (fePath entry) of
            Nothing -> failM ("in module " ++ renderModuleId moduleId ++ ": file not found: " ++ fePath entry)
            Just text -> do
                modifyM (\state -> state{lsProbes = Map.insert (fePath entry) text (lsProbes state)})
                pureM (entry, text)
        checkOne ((entry, source), parsedFile) = case checkDeclarationsOnly moduleId entry (fePath entry == entryPath) (fileBody parsedFile) of
            Left err -> failM err
            Right () -> pureM (PFile entry parsedFile (declarationNames (fileBody parsedFile)) source)
    importSeedFor entry = do
        source <- maybe (failM ("file not found: " ++ fePath entry)) pureM (resolverReadFile resolver (fePath entry))
        imports <- case ParserSeed.parseImportPrefix source of
            Left err -> failM ("parse error in file " ++ fePath entry ++ ": " ++ show err)
            Right found -> pureM found
        declarations <- mapM_M (seedImport entry) imports
        pureM (fePath entry, foldl addImportedDecls emptyDecls declarations)
    seedImport entry imp = do
        target <- ensureLayout resolver layout (head (importPath imp))
        case target of
            Left _ -> resolveImport True resolver entryPath layout (PModule layout moduleId moduleName []) entry imp >> pureM emptyDecls
            Right targetLayout -> do
                let rest = tail (importPath imp)
                    targetName = case rest of
                        name : _ | Map.member name (layModules targetLayout) -> Just name
                        _ -> Nothing
                    targetId = layoutModuleId targetLayout targetName
                if targetId == moduleId then pureM emptyDecls else do
                    targetModule <- parseModule resolver entryPath targetLayout targetName
                    (resolved, _) <- resolveImport True resolver entryPath layout (PModule layout moduleId moduleName []) entry imp
                    let collapsed = layoutCollapsedFile targetLayout targetName
                        covers file = maybe True (== feStem (pfEntry file)) (resolvedTargetFile resolved)
                        visible name = maybe True (\n -> name == n || takeWhile (/= ':') name == n) (resolvedTargetSymbol resolved)
                        rename file name = [intercalate "::" (prefix ++ Parse.splitPath name) | prefix <- importPrefixes (feStem (pfEntry file)) (fmap feStem collapsed == Just (feStem (pfEntry file))) name resolved]
                        declared file = [stmt | stmt <- fileBody (pfParsed file), case stmt of StructDef{} -> True; EnumDef{} -> True; TraitDef{} -> True; _ -> False]
                    pureM (foldl addImportedDecls emptyDecls [seedSpelling name spelling (canonicalOf (pmId targetModule) (Just (feStem (pfEntry file))) (Just name)) stmt | file <- pmFiles targetModule, covers file, stmt <- declared file, name <- take 1 (declarationNames [stmt]), visible name, spelling <- rename file name])
    seedSpelling old new canonical stmt = case stmt of
        StructDef _ params fields invariant ->
            let seed = Parse.declsFromStatements emptyDecls [StructDef new params fields invariant]
             in seed{Parse.declTypes = Map.singleton new [canonical]}
        EnumDef _ variants ->
            let seed = Parse.declsFromStatements emptyDecls [EnumDef new [(new ++ drop (length old) variant, fields) | (variant, fields) <- variants]]
             in seed{Parse.declTypes = Map.singleton new [canonical ++ drop (length old) variant | (variant, _) <- variants]}
        TraitDef _ params functions -> Parse.declsFromStatements emptyDecls [TraitDef new params functions]
        _ -> emptyDecls

addImportedDecls :: Decls -> Decls -> Decls
addImportedDecls base imported = base
    { Parse.declCtors = Map.union (Parse.declCtors imported) (Parse.declCtors base)
    , Parse.declTypes = Map.union (Parse.declTypes imported) (Parse.declTypes base)
    , Parse.declGenerics = Map.union (Parse.declGenerics imported) (Parse.declGenerics base)
    , Parse.declFieldTypes = Map.union (Parse.declFieldTypes imported) (Parse.declFieldTypes base)
    }

withoutImportedDecls :: Decls -> Decls -> Decls -> [Statement] -> Decls
withoutImportedDecls base imported parsed body = parsed
    { Parse.declCtors = restore Parse.declCtors
    , Parse.declTypes = restore Parse.declTypes
    , Parse.declGenerics = restore Parse.declGenerics
    , Parse.declFieldTypes = restore Parse.declFieldTypes
    }
  where
    own = Parse.declsFromStatements emptyDecls body
    restore :: Eq a => (Decls -> Map.Map Name a) -> Map.Map Name a
    restore field =
        let before = field base
            incoming = field imported
            after = field parsed
            declared = field own
            unchanged key value = Map.lookup key after == Just value && Map.notMember key declared
         in Map.union
                (Map.filterWithKey (\key value -> Map.lookup key incoming /= Just value || Map.member key declared) after)
                (Map.intersection before (Map.filterWithKey unchanged incoming))

parseModuleDeclarations :: Resolver -> Layout -> [FileEntry] -> LoadM PModule
parseModuleDeclarations resolver layout entries = do
    files <- mapM_M readNames entries
    pureM (PModule layout (layoutModuleId layout Nothing) Nothing files)
  where
    readNames entry = do
        source <- maybe (failM ("file not found: " ++ fePath entry)) pureM (resolverReadFile resolver (fePath entry))
        modifyM (\state -> state{lsProbes = Map.insert (fePath entry) source (lsProbes state)})
        names <- either failM pureM (ParserSeed.parseDeclarationNames source)
        pureM (PFile entry (ParsedFile [] []) names source)

parseModuleFiles :: FileParser -> Resolver -> Layout -> ModuleId -> [FileEntry] -> [(FilePath, Decls)] -> [(FileEntry, String)] -> Either String [ParsedFile]
parseModuleFiles fileParser resolver layout moduleId ownEntries seeds ownTexts = do
    declared <- if layNoPrelude layout then Right emptyDecls else libraryDecls
    let seed = seedDecls fileParser resolver ownEntries seeds declared
        ordered = [entry | (entry, _) <- ownTexts]
    case iterateParses seed ownTexts [] of
            Right done -> Right [parsedFile | entry <- ordered, Just parsedFile <- [lookup (fePath entry) done]]
            Left (entry, text) -> case fileParser (locating emptyDecls) text of
                Left err -> Left ("parse error in module " ++ renderModuleId moduleId ++ " file " ++ fePath entry ++ ": " ++ err)
                Right _ -> Left ("parse error in module " ++ renderModuleId moduleId ++ " file " ++ fePath entry ++ ": could not be parsed with the declarations of its package")
  where
    iterateParses _ [] done = Right done
    iterateParses decls pending done = case pass decls pending of
        (decls', [], done') -> iterateParses decls' [] (done ++ done')
        (decls', remaining, done')
            | length remaining == length pending -> Left (head remaining)
            | otherwise -> iterateParses decls' remaining (done ++ done')
    pass decls pending = go decls pending [] []
      where
        go d [] remaining done = (d, reverse remaining, reverse done)
        go d ((entry, text) : rest) remaining done = case fileParser (locating (addImportedDecls d (fromMaybe emptyDecls (lookup (fePath entry) seeds)))) text of
            Right (parsedFile, d') -> go (withoutImportedDecls d (fromMaybe emptyDecls (lookup (fePath entry) seeds)) d' (fileBody parsedFile)) rest remaining ((fePath entry, parsedFile) : done)
            Left _ -> go d rest ((entry, text) : remaining) done

-- The declarations of implicit compiler libraries, used only by default
-- package preparation before the existing library-selection decision.
libraryDecls :: Either String Decls
libraryDecls = lpDecls <$> libParsed

seedDecls :: FileParser -> Resolver -> [FileEntry] -> [(FilePath, Decls)] -> Decls -> Decls
seedDecls fileParser resolver ownEntries seeds initial = loop initial texts
  where
    texts = [(entry, text) | entry <- ownEntries, Just text <- [resolverReadFile resolver (fePath entry)]]
    loop decls [] = decls
    loop decls pending = case pass decls pending of
        (decls', []) -> decls'
        (decls', remaining)
            | length remaining == length pending -> decls
            | otherwise -> loop decls' remaining
    pass decls pending = go decls pending []
      where
        go d [] remaining = (d, reverse remaining)
        go d ((entry, text) : rest) remaining = case fileParser (locating (addImportedDecls d (fromMaybe emptyDecls (lookup (fePath entry) seeds)))) text of
            Right (parsed, d') -> go (withoutImportedDecls d (fromMaybe emptyDecls (lookup (fePath entry) seeds)) d' (fileBody parsed)) rest remaining
            Left _ -> go d rest ((entry, text) : remaining)

-- Import resolution.

canonicalOf :: ModuleId -> Maybe String -> Maybe String -> String
canonicalOf (ModuleId pkg moduleName) file symbol =
    intercalate "$" ([pkg] ++ maybe [] pure moduleName ++ maybe [] pure file ++ maybe [] pure symbol)

declsOfFile :: PModule -> String -> [Name]
declsOfFile pmod stem = concat [pfDecls pf | pf <- pmFiles pmod, feStem (pfEntry pf) == stem]

declsOfModule :: PModule -> [Name]
declsOfModule pmod = concatMap pfDecls (pmFiles pmod)

fileWithDecl :: PModule -> Name -> Maybe String
fileWithDecl pmod name = case [feStem (pfEntry pf) | pf <- pmFiles pmod, name `elem` pfDecls pf] of
    stem : _ -> Just stem
    [] -> Nothing

listDecls :: [Name] -> String
listDecls names = case nub (filter (notElem '<') names) of
    [] -> "(none)"
    unique -> intercalate ", " unique

resolveImport ::
    Bool ->
    Resolver ->
    FilePath ->
    Layout ->
    PModule ->
    FileEntry ->
    Import ->
    LoadM (ResolvedImport, Maybe ModuleId)
resolveImport seeding resolver entryPath sourceLayout sourceModule sourceFile imp = do
    targetLayout <- ensureLayout resolver sourceLayout (head segments)
    case targetLayout of
        Left err -> failM (atImport err)
        Right layout -> resolveInPackage seeding resolver entryPath sourceModule sourceFile imp layout (tail segments)
  where
    segments = importPath imp
    atImport message =
        "import "
            ++ renderPath segments
            ++ " (in module "
            ++ renderModuleId (pmId sourceModule)
            ++ " file "
            ++ fePath sourceFile
            ++ ":"
            ++ show (importLine imp)
            ++ "): "
            ++ message

requestedRoots :: LoadOptions -> String -> [FilePath]
requestedRoots options pkg = nub (map normalizePath
    (maybe [] pure (Map.lookup pkg (packageRoots options))
        ++ [root | pkg == "std", Just root <- [installedStdRoot options]]))

eligibleRoots :: LoadOptions -> Maybe (String, FilePath) -> String -> (FilePath -> Bool) -> [FilePath]
eligibleRoots options context pkg marker = requestedRoots options pkg ++ case context of
    Nothing -> []
    Just (name, root) -> [root | pkg == name] ++ [sibling | marker sibling]
      where sibling = joinPath (dirNameOf root) pkg

ensureLayout :: Resolver -> Layout -> String -> LoadM (Either String Layout)
ensureLayout resolver sourceLayout pkgName = do
    state <- getM
    let options = resolverOptions resolver
        requested = requestedRoots options pkgName
        sibling = joinPath (dirNameOf (layRoot sourceLayout)) pkgName
        marker root = resolverReadFile resolver (joinPath root "package.tersus") /= Nothing
        context = if layIsPackage sourceLayout then Just (layName sourceLayout, layRoot sourceLayout) else Nothing
        candidates = nub (map (resolverCanonicalRoot resolver) (eligibleRoots options context pkgName marker))
        missing = [root | root <- requested, not (marker root)]
        aliases root = [layName layout | layout <- Map.elems (lsLayouts state), layIsPackage layout, layRoot layout == root, layName layout /= pkgName]
    case (missing, candidates) of
        (root : _, _) -> pureM (Left ("package " ++ show pkgName ++ " not found: no package.tersus in requested root " ++ root))
        ([], []) -> pureM (Left (if layIsPackage sourceLayout
            then "package " ++ show pkgName ++ " not found: no package.tersus in " ++ sibling
            else "package " ++ show pkgName ++ " is not configured for standalone source"))
        ([], _ : _ : _) -> pureM (Left ("conflicting roots for package " ++ show pkgName ++ ": " ++ intercalate ", " candidates))
        ([], [root])
            | name : _ <- aliases root -> pureM (Left ("conflicting package identities for root " ++ root ++ ": " ++ name ++ " and " ++ pkgName))
            | Just layout <- Map.lookup pkgName (lsLayouts state) -> pureM (if layRoot layout == root
                then Right layout
                else Left ("conflicting roots for package " ++ show pkgName ++ ": " ++ intercalate ", " [layRoot layout, root]))
            | pkgName == layName sourceLayout -> pureM (Right sourceLayout)
            | otherwise -> case buildLayout resolver{resolverOptions = options{noPrelude = False}} root of
                Left err -> pureM (Left err)
                Right found -> do
                    let layout = found{layName = pkgName}
                    modifyM (\s -> s{lsLayouts = Map.insert pkgName layout (lsLayouts s)})
                    pureM (Right layout)

-- The level determination itself. @rest@ is the import path with the
-- package segment removed.
resolveInPackage ::
    Bool ->
    Resolver ->
    FilePath ->
    PModule ->
    FileEntry ->
    Import ->
    Layout ->
    [String] ->
    LoadM (ResolvedImport, Maybe ModuleId)
resolveInPackage seeding resolver entryPath sourceModule sourceFile imp layout rest = do
    let finish level targetModule targetFile targetSymbol =
            let resolved =
                    ResolvedImport
                        imp
                        level
                        targetModule
                        targetFile
                        targetSymbol
                        (canonicalOf targetModule targetFile targetSymbol)
                dep = if targetModule == pmId sourceModule then Nothing else Just targetModule
             in case importNames imp of
                    Nothing -> pureM (resolved, dep)
                    Just names -> validateNames resolved targetModule targetFile names dep
        validateNames resolved targetModule targetFile names dep = do
            pmod <- parseModule resolver entryPath layout (moduleName targetModule)
            let available = case (targetFile, resolvedLevel resolved) of
                    (Just stem, _) -> declsOfFile pmod stem
                    (Nothing, LevelModule) -> declsOfModule pmod
                    (Nothing, _) -> declsOfModule pmod
                missing = [name | name <- names, name `notElem` available]
            case missing of
                [] -> pureM (resolved, dep)
                name : _ ->
                    failM
                        ( atImport
                            ( "name "
                                ++ name
                                ++ " is not declared there; it declares: "
                                ++ listDecls available
                            )
                        )
        atImport message =
            "import "
                ++ renderPath (importPath imp)
                ++ " (in module "
                ++ renderModuleId (pmId sourceModule)
                ++ " file "
                ++ fePath sourceFile
                ++ ":"
                ++ show (importLine imp)
                ++ "): "
                ++ message
        rootId = layoutModuleId layout Nothing
        moduleIdOf name = layoutModuleId layout (Just name)
        rootProbe path = do
            state <- getM
            case Map.lookup rootId (lsParsed state) of
                Just parsed -> pureM parsed
                Nothing
                    | null (rootProbeEntries layout path) -> pureM (PModule layout rootId Nothing [])
                    | otherwise -> parseModuleDeclarations resolver layout (rootProbeEntries layout path)
        parsedOf name = parseModule resolver entryPath layout name
    case rest of
        [] -> finish LevelModule rootId Nothing Nothing
        [x] | seeding, Map.member x (layModules layout) -> finish LevelModule (moduleIdOf x) Nothing Nothing
        [x] -> do
            rootParsed <- rootProbe [x]
            let isModule = Map.member x (layModules layout)
                rootFile = [feStem e | e <- layRootFiles layout, feStem e == x]
                collapsed = layoutCollapsedFile layout Nothing
                symbolInCollapsed = case collapsed of
                    Just entry -> x `elem` declsOfFile rootParsed (feStem entry)
                    Nothing -> False
                readings =
                    [(LevelModule, moduleIdOf x, Nothing, Nothing) | isModule]
                        ++ [(LevelFile, rootId, Just x, Nothing) | not (null rootFile)]
                        ++ [(LevelSymbol, rootId, fmap feStem collapsed, Just x) | symbolInCollapsed]
            case readings of
                [reading] -> finishFrom reading
                _ : _ : _ ->
                    failM (atImport ("ambiguous import: " ++ show x ++ " names more than one of a module, a file of the root module, or a symbol of the root module; spell out the intended level"))
                []
                    | Just stem <- fileWithDecl rootParsed x ->
                        failM
                            ( atImport
                                ( "symbol "
                                    ++ x
                                    ++ " is declared in file "
                                    ++ stem
                                    ++ " of the root module; write "
                                    ++ renderPath [layName layout, stem, x]
                                    ++ " (or "
                                    ++ renderPath [layName layout, x]
                                    ++ " only when the root module has the single file "
                                    ++ layName layout
                                    ++ ".tersus)"
                                )
                            )
                    | otherwise ->
                        failM
                            ( atImport
                                ( show x
                                    ++ " is not a module of package "
                                    ++ layName layout
                                    ++ ", a file of its root module, or a symbol of its root module; modules are: "
                                    ++ intercalate ", " (Map.keys (layModules layout))
                                    ++ "; the root module's files are: "
                                    ++ intercalate ", " (map feName (layRootFiles layout))
                                    ++ "; it declares: "
                                    ++ listDecls (declsOfModule rootParsed)
                                )
                            )
          where
            finishFrom (level, targetModule, targetFile, targetSymbol) = finish level targetModule targetFile targetSymbol
        [m, x] -> do
            let isModule = Map.member m (layModules layout)
                rootFileStem = [feStem e | e <- layRootFiles layout, feStem e == m]
            modParsed <- if isModule then fmap Just (parsedOf (Just m)) else pureM Nothing
            rootParsed <- if seeding && isModule then pureM (PModule layout rootId Nothing []) else rootProbe [m, x]
            let moduleReading = case modParsed of
                    Just pmod ->
                        let entries = layoutModuleFiles layout (Just m)
                            dirNamedEntries = [e | e <- entries, feStem e == m]
                            collapsedHere = layoutCollapsedFile layout (Just m)
                         in if x `elem` map feStem entries
                                then Just (LevelFile, moduleIdOf m, Just x, Nothing)
                                else case collapsedHere of
                                    Just entry
                                        | x `elem` declsOfFile pmod (feStem entry) ->
                                            Just (LevelSymbol, moduleIdOf m, Just (feStem entry), Just x)
                                    _ -> Nothing
                    Nothing -> Nothing
                rootReading = case rootFileStem of
                    stem : _
                        | x `elem` declsOfFile rootParsed stem -> Just (LevelSymbol, rootId, Just stem, Just x)
                    _ -> Nothing
                readings = [r | Just r <- [moduleReading, rootReading]]
            case readings of
                [ (level, targetModule, targetFile, targetSymbol)] -> finish level targetModule targetFile targetSymbol
                _ : _ : _ -> failM (atImport ("ambiguous import: " ++ renderPath [m, x] ++ " reads both as a file/symbol of module " ++ m ++ " and as a symbol of root-module file " ++ m ++ "; rename one of them"))
                []
                    | isModule, Just pmod <- modParsed -> do
                        let entries = layoutModuleFiles layout (Just m)
                            nested = fromMaybe [] (Map.lookup m (layModuleNested layout))
                        if x `elem` nested
                            then
                                failM
                                    ( atImport
                                        ( show x
                                            ++ " is a directory inside module "
                                            ++ m
                                            ++ "; deeper nesting is not a module (modules are only the package root and its immediate subdirectories)"
                                        )
                                    )
                            else case [e | e <- entries, feStem e == m] of
                                dirNamed : _
                                    | length entries > 1 && x `elem` declsOfFile pmod (feStem dirNamed) ->
                                        failM
                                            ( atImport
                                                ( "symbol "
                                                    ++ x
                                                    ++ " no longer resolves as "
                                                    ++ renderPath (importPath imp)
                                                    ++ ": module "
                                                    ++ m
                                                    ++ " has grown to "
                                                    ++ show (length entries)
                                                    ++ " files, so the single-file collapse no longer applies; write "
                                                    ++ renderPath [layName layout, m, feStem dirNamed, x]
                                                    ++ " instead of "
                                                    ++ renderPath (importPath imp)
                                                )
                                            )
                                _ -> case fileWithDecl pmod x of
                                    Just stem ->
                                        failM
                                            ( atImport
                                                ( "symbol "
                                                    ++ x
                                                    ++ " is declared in file "
                                                    ++ stem
                                                    ++ " of module "
                                                    ++ m
                                                    ++ "; write "
                                                    ++ renderPath [layName layout, m, stem, x]
                                                    ++ "; module "
                                                    ++ m
                                                    ++ "'s files are: "
                                                    ++ intercalate ", " (map feName entries)
                                                    ++ "; it declares: "
                                                    ++ listDecls (declsOfModule pmod)
                                                )
                                            )
                                    Nothing ->
                                        failM
                                            ( atImport
                                                ( show x
                                                    ++ " is not a file of module "
                                                    ++ m
                                                    ++ " or a symbol of its collapsed file; module "
                                                    ++ m
                                                    ++ "'s files are: "
                                                    ++ intercalate ", " (map feName entries)
                                                    ++ "; it declares: "
                                                    ++ listDecls (declsOfModule pmod)
                                                )
                                            )
                    | not (null rootFileStem) -> do
                        let stem = head rootFileStem
                        failM
                            ( atImport
                                ( "symbol "
                                    ++ x
                                    ++ " is not declared in root-module file "
                                    ++ stem
                                    ++ "; it declares: "
                                    ++ listDecls (declsOfFile rootParsed stem)
                                )
                            )
                    | otherwise ->
                        failM
                            ( atImport
                                ( "module "
                                    ++ show m
                                    ++ " not found in package "
                                    ++ layName layout
                                    ++ "; modules are: "
                                    ++ intercalate ", " (Map.keys (layModules layout))
                                    ++ " (plus the root module); the root module's files are: "
                                    ++ intercalate ", " (map feName (layRootFiles layout))
                                )
                            )
        [m, f, s] -> do
            let isModule = Map.member m (layModules layout)
            if isModule
                then do
                    pmod <- parsedOf (Just m)
                    let entries = layoutModuleFiles layout (Just m)
                        nested = fromMaybe [] (Map.lookup m (layModuleNested layout))
                    if f `elem` nested
                        then
                            failM
                                ( atImport
                                    ( show f
                                        ++ " is a directory inside module "
                                        ++ m
                                        ++ "; deeper nesting is not a module (modules are only the package root and its immediate subdirectories)"
                                    )
                                )
                        else case [e | e <- entries, feStem e == f] of
                            [] ->
                                failM
                                    ( atImport
                                        ( "file "
                                            ++ show f
                                            ++ " not found in module "
                                            ++ m
                                            ++ "; its files are: "
                                            ++ intercalate ", " (map feName entries)
                                            ++ "; it declares: "
                                            ++ listDecls (declsOfModule pmod)
                                        )
                                    )
                            _ : _
                                | s `elem` declsOfFile pmod f -> finish LevelSymbol (moduleIdOf m) (Just f) (Just s)
                                | otherwise ->
                                    failM
                                        ( atImport
                                            ( "symbol "
                                                ++ s
                                                ++ " is not declared in file "
                                                ++ f
                                                ++ " of module "
                                                ++ m
                                                ++ "; it declares: "
                                                ++ listDecls (declsOfFile pmod f)
                                            )
                                        )
                else do
                    rootParsed <- rootProbe [m, f, s]
                    let rootFileStem = [feStem e | e <- layRootFiles layout, feStem e == m]
                    if not (null rootFileStem)
                        then
                            failM
                                ( atImport
                                    ( "too many segments for the root module: "
                                        ++ renderPath (importPath imp)
                                        ++ " would name a symbol of root-module file "
                                        ++ m
                                        ++ " as "
                                        ++ renderPath [layName layout, m, f]
                                        ++ " ("
                                        ++ show s
                                        ++ " is one segment too many); root-module file "
                                        ++ m
                                        ++ " declares: "
                                        ++ listDecls (declsOfFile rootParsed m)
                                    )
                                )
                        else
                            failM
                                ( atImport
                                    ( "module "
                                        ++ show m
                                        ++ " not found in package "
                                        ++ layName layout
                                        ++ "; modules are: "
                                        ++ intercalate ", " (Map.keys (layModules layout))
                                        ++ " (plus the root module)"
                                    )
                                )
        _ ->
            failM
                ( atImport
                    ( "import path "
                        ++ renderPath (importPath imp)
                        ++ " has too many segments: a path is package[::module[::file[::symbol]]]; deeper nesting is not a module"
                    )
                )

-- The dependency graph: a DFS from the entry module, dependencies
-- first, diamonds deduped. A cycle among modules is an error.
visitModule :: Resolver -> FilePath -> [ModuleId] -> ModuleId -> Layout -> Maybe String -> LoadM ()
visitModule resolver entryPath stack moduleId layout moduleName = do
    state <- getM
    if Set.member moduleId (lsDone state)
        then pureM ()
        else
            if moduleId `elem` stack
                then failM (cycleText stack moduleId)
                else do
                    pmod <- parseModule resolver entryPath layout moduleName
                    resolvedPerFile <- mapM_M (resolveFile pmod) (pmFiles pmod)
                    let deps = nub [dep | (_, fileDeps) <- resolvedPerFile, dep <- fileDeps]
                    mapM_M (visitDep (stack ++ [moduleId])) deps
                    modifyM
                        ( \s ->
                            s
                                { lsDone = Set.insert moduleId (lsDone s)
                                , lsOrder = lsOrder s ++ [moduleId]
                                }
                        )
  where
    cycleText chain target =
        let fromTarget = dropWhile (/= target) chain ++ [target]
         in "module import cycle: " ++ intercalate " -> " (map renderModuleId fromTarget)
    resolveFile pmod pfile = do
        resolved <- mapM_M (resolveOne pmod pfile) (fileImports (pfParsed pfile))
        modifyM (\s -> s{lsResolved = Map.insert (pmId pmod, feName (pfEntry pfile)) (map fst resolved) (lsResolved s)})
        pureM (feName (pfEntry pfile), [dep | (_, Just dep) <- resolved])
    resolveOne pmod pfile imp = resolveImport False resolver entryPath (pmLayout pmod) pmod (pfEntry pfile) imp
    visitDep chain (ModuleId pkg name) = do
        depLayout <- ensureLayoutFor pkg
        case depLayout of
            Left err -> failM err
            Right layout' -> visitModule resolver entryPath chain (ModuleId pkg name) layout' name
    ensureLayoutFor pkg = do
        state <- getM
        case Map.lookup pkg (lsLayouts state) of
            Just layout' -> pureM (Right layout')
            Nothing
                | pkg == layName layout -> pureM (Right layout)
                | otherwise -> failM ("internal: package " ++ pkg ++ " was resolved but its layout is missing")

loadFromEntry :: Resolver -> FilePath -> Either String LoadResult
loadFromEntry = loadFromEntryWith bootstrapFileParser

loadFromEntryWith :: FileParser -> Resolver -> FilePath -> Either String LoadResult
loadFromEntryWith fileParser resolver rawEntry = case discoverEntry resolver entryPath of
    Standalone _ -> do
        text <- maybe (Left ("file not found: " ++ entryPath)) Right (resolverReadFile resolver entryPath)
        if not (Map.null (packageRoots options)) || installedStdRoot options /= Nothing
            then loadLayout fileParser resolver entryPath
                (Layout "" (dirNameOf entryPath) [FileEntry (baseNameOf entryPath) (fileStem entryPath) entryPath] Map.empty Map.empty [] (noPrelude options) False)
            else do
                parsedFile <- case fileParser (locating emptyDecls) text of
                    Left err -> Left ("parse error in file " ++ entryPath ++ ": " ++ err)
                    Right (parsed, _) -> Right parsed
                if null (fileImports parsedFile)
                    then Right (StandaloneResult entryPath parsedFile)
                    else Left ("standalone program " ++ entryPath ++ ": imports are not supported without a package (no package.tersus found in any ancestor directory); first import: " ++ renderPath (importPath (head (fileImports parsedFile))))
    InPackage root _ -> buildLayout resolver root >>= loadLayout fileParser resolver entryPath
  where
    entryPath = normalizePath rawEntry
    options = resolverOptions resolver

loadLayout :: FileParser -> Resolver -> FilePath -> Layout -> Either String LoadResult
loadLayout fileParser resolver entryPath layout = do
    let root = layRoot layout
        pkgName = layName layout
        entryDir = dirNameOf entryPath
        entryName = if entryDir == root then Nothing else Just (baseNameOf entryDir)
        entryId = layoutModuleId layout entryName
    if entryDir /= root && dirNameOf entryDir /= root
        then Left ("entry file " ++ entryPath ++ " is in a directory nested below module level under package " ++ pkgName ++ "; deeper nesting is not a module")
        else do
            let initial = LState fileParser (Map.singleton pkgName layout) Map.empty [] Map.empty [] Set.empty Map.empty
            (state, ()) <- runLoadM (visitModule resolver entryPath [] entryId layout entryName) initial
            let modules =
                    [ LoadedModule moduleId'
                        [ LoadedFile moduleId' (feName (pfEntry pf)) (feStem (pfEntry pf)) (fePath (pfEntry pf))
                            (pfParsed pf) (pfDecls pf)
                            (Map.findWithDefault [] (moduleId', feName (pfEntry pf)) (lsResolved state)) (pfSource pf)
                        | pf <- pmFiles pmod ]
                        (sort (nub (declsOfModule pmod)))
                        (sort (nub [target | pf <- pmFiles pmod, ri <- Map.findWithDefault [] (moduleId', feName (pfEntry pf)) (lsResolved state), let target = resolvedTargetModule ri, target /= moduleId']))
                        (layNoPrelude (pmLayout pmod))
                    | moduleId' <- lsOrder state, Just pmod <- [Map.lookup moduleId' (lsParsed state)] ]
                layouts = Map.elems (lsLayouts state)
                markers = [(path, text) | found <- layouts, layIsPackage found, let path = joinPath (layRoot found) "package.tersus", Just text <- [resolverReadFile resolver path]]
                sources = Map.toAscList (Map.unions
                    [lsProbes state, Map.fromList markers, Map.fromList [(loadedFilePath file, loadedFileSource file) | modu <- modules, file <- loadedModuleFiles modu]])
                policies = [(layName found, layRoot found, layNoPrelude found) | found <- layouts]
            Right (PackageResult (LoadedPackage root pkgName entryPath entryId modules sources policies))

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
loadFromFilesystem = loadFromFilesystemWith bootstrapFileParser

loadFromFilesystemWith :: FileParser -> FilePath -> IO (Either String LoadResult)
loadFromFilesystemWith fileParser = loadFromFilesystemWithOptions fileParser defaultLoadOptions

loadFromFilesystemWithOptions :: FileParser -> LoadOptions -> FilePath -> IO (Either String LoadResult)
loadFromFilesystemWithOptions fileParser options entry = loadFilesystemInput fileParser options entry Nothing

loadFromSourceWith :: FileParser -> LoadOptions -> String -> IO (Either String LoadResult)
loadFromSourceWith fileParser options source = loadFilesystemInput fileParser options "<stdin>.tersus" (Just source)

loadFilesystemInput :: FileParser -> LoadOptions -> FilePath -> Maybe String -> IO (Either String LoadResult)
loadFilesystemInput fileParser options rawEntry source = do
    snapshot <- try (do
        (resolved, entry) <- resolveFilesystemInputs options rawEntry
        (resolver, _) <- filesystemSnapshot resolved entry source
        pure (resolver, entry)) :: IO (Either IOException (Resolver, FilePath))
    pure $ case snapshot of
        Left err -> Left ("source snapshot for " ++ rawEntry ++ ": " ++ show err)
        Right (resolver, entry) -> case source of
            Just _ -> loadLayout fileParser resolver entry
                (Layout "" (dirNameOf entry) [FileEntry (baseNameOf entry) (fileStem entry) entry] Map.empty Map.empty [] (noPrelude options) False)
            Nothing -> loadFromEntryWith fileParser resolver (normalizePath entry)

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
    snd <$> filesystemSnapshot resolved entry Nothing

filesystemSnapshot :: LoadOptions -> FilePath -> Maybe String -> IO (Resolver, [(FilePath, String)])
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
            let resolver = (resolverFromFiles (Map.toAscList saved))
                    {resolverListDir = \dir -> Map.lookup (normalizePath dir) dirs}
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
            Left _ -> pure ()
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
    let resolver = (resolverFromFiles files)
            { resolverOptions = options
            , resolverListDir = \dir -> Map.lookup (normalizePath dir) dirs
            , resolverCanonicalRoot = \root -> Map.findWithDefault (normalizePath root) (normalizePath root) canonical
            }
    pure (resolver, files)
