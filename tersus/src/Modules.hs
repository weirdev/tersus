module Modules
    ( ModuleIdentity (..)
    , rootModuleIdentity
    , fileModuleIdentity
    , canonicalPrefix
    , canonicalName
    , declarationNames
    , canonicalizeDeclarations
    , Resolver (..)
    , resolverFromFiles
    , normalizePath
    , Discovery (..)
    , discoverEntry
    , findPackageRoot
    , ModuleId (..)
    , renderModuleId
    , ImportLevel (..)
    , ResolvedImport (..)
    , LoadedFile (..)
    , LoadedModule (..)
    , LoadedPackage (..)
    , LoadResult (..)
    , loadFromEntry
    , loadFromFilesystem
    , findPackageRootIO
    ) where

import Control.Monad (filterM)
import Data.List (intercalate, isPrefixOf, nub, sort, stripPrefix)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath (takeDirectory, (</>))

import Parse (Import (..), ParsedFile (..), emptyDecls, locating, parseFileWith, renderPath)
import TersusTypes

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
        TNamed name -> TNamed (renameNamed name)
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
    renameNamed name = case instanceOf name of
        Just (base, args) -> instanceName (canon base) (map renameArg args)
        Nothing -> canon name
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
                (renameNamed selfName)
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
data Resolver = Resolver
    { resolverReadFile :: FilePath -> Maybe String
    , resolverListDir :: FilePath -> Maybe ([String], [String])
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
resolverFromFiles files = Resolver readFile listDir
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

data LoadedFile = LoadedFile
    { loadedFileModule :: ModuleId
    , loadedFileName :: String
    , loadedFileStem :: String
    , loadedFilePath :: FilePath
    , loadedParsed :: ParsedFile
    , loadedDeclNames :: [Name]
    , loadedImports :: [ResolvedImport]
    }
    deriving (Show)

data LoadedModule = LoadedModule
    { loadedModuleId :: ModuleId
    , loadedModuleFiles :: [LoadedFile]
    , loadedModuleDeclNames :: [Name]
    , loadedDependencies :: [ModuleId]
    }
    deriving (Show)

data LoadedPackage = LoadedPackage
    { packageRootDir :: FilePath
    , packagePackageName :: String
    , packageEntryFile :: FilePath
    , packageEntryModule :: ModuleId
    , packageModules :: [LoadedModule]
    }
    deriving (Show)

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
                Just (nested, subFiles) ->
                    let entries = tersusFiles (joinPath root sub) subFiles
                     in if null entries then Nothing else Just (sub, entries, nested)
            found = [entry | Just entry <- map moduleOf subdirs]
         in Right
                Layout
                    { layName = baseNameOf root
                    , layRoot = root
                    , layRootFiles = [entry | entry <- tersusFiles root files, feName entry /= "package.tersus"]
                    , layModules = Map.fromList [(sub, entries) | (sub, entries, _) <- found]
                    , layModuleNested = Map.fromList [(sub, nested) | (sub, _, nested) <- found]
                    , layRootSubdirs = subdirs
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

-- Loader state for the pure core.

data PFile = PFile
    { pfEntry :: FileEntry
    , pfParsed :: ParsedFile
    , pfDecls :: [Name]
    }

data PModule = PModule
    { pmLayout :: Layout
    , pmId :: ModuleId
    , pmMaybeName :: Maybe String
    , pmFiles :: [PFile]
    }

data LState = LState
    { lsLayouts :: Map.Map String Layout
    , lsParsed :: Map.Map ModuleId PModule
    , lsResolved :: Map.Map (ModuleId, String) [ResolvedImport]
    , lsOrder :: [ModuleId]
    , lsDone :: Set.Set ModuleId
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

-- Parsing one module (all its files as one unit), without resolving
-- its imports. The entry file is exempt from declarations-only.
parseModule :: Resolver -> FilePath -> Layout -> Maybe String -> LoadM PModule
parseModule resolver entryPath layout moduleName = do
    state <- getM
    let moduleId = layoutModuleId layout moduleName
    case Map.lookup moduleId (lsParsed state) of
        Just parsed -> pureM parsed
        Nothing -> do
            files <- mapM_M parseOne (layoutModuleFiles layout moduleName)
            let parsed = PModule layout moduleId moduleName files
            modifyM (\s -> s{lsParsed = Map.insert moduleId parsed (lsParsed s)})
            pureM parsed
  where
    parseOne entry = case resolverReadFile resolver (fePath entry) of
        Nothing -> failM ("in module " ++ renderModuleId (layoutModuleId layout moduleName) ++ ": file not found: " ++ fePath entry)
        Just text -> case parseFileWith (locating emptyDecls) text of
            Left err ->
                failM
                    ( "parse error in module "
                        ++ renderModuleId (layoutModuleId layout moduleName)
                        ++ " file "
                        ++ fePath entry
                        ++ ": "
                        ++ show err
                    )
            Right (parsedFile, _) -> case checkDeclarationsOnly (layoutModuleId layout moduleName) entry (fePath entry == entryPath) (fileBody parsedFile) of
                Left err -> failM err
                Right () -> pureM (PFile entry parsedFile (declarationNames (fileBody parsedFile)))

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
listDecls names = case nub names of
    [] -> "(none)"
    unique -> intercalate ", " unique

resolveImport ::
    Resolver ->
    FilePath ->
    Layout ->
    PModule ->
    FileEntry ->
    Import ->
    LoadM (ResolvedImport, Maybe ModuleId)
resolveImport resolver entryPath sourceLayout sourceModule sourceFile imp = do
    targetLayout <- ensureLayout resolver sourceLayout (head segments)
    case targetLayout of
        Left err -> failM (atImport err)
        Right layout -> resolveInPackage resolver entryPath sourceModule sourceFile imp layout (tail segments)
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

ensureLayout :: Resolver -> Layout -> String -> LoadM (Either String Layout)
ensureLayout resolver sourceLayout pkgName = do
    state <- getM
    case Map.lookup pkgName (lsLayouts state) of
        Just layout -> pureM (Right layout)
        Nothing
            | pkgName == layName sourceLayout -> pureM (Right sourceLayout)
            | otherwise -> do
                let parent = dirNameOf (layRoot sourceLayout)
                    siblingRoot = joinPath parent pkgName
                case resolverReadFile resolver (joinPath siblingRoot "package.tersus") of
                    Nothing -> do
                        let available = case resolverListDir resolver parent of
                                Nothing -> []
                                Just (subdirs, _) ->
                                    [ sub
                                    | sub <- subdirs
                                    , resolverReadFile resolver (joinPath (joinPath parent sub) "package.tersus") /= Nothing
                                    ]
                        pureM
                            ( Left
                                ( "package "
                                    ++ show pkgName
                                    ++ " not found: no package.tersus in "
                                    ++ siblingRoot
                                    ++ if null available
                                        then ""
                                        else " (packages beside " ++ layName sourceLayout ++ ": " ++ intercalate ", " available ++ ")"
                                )
                            )
                    Just _ -> case buildLayout resolver siblingRoot of
                        Left err -> pureM (Left err)
                        Right layout -> do
                            modifyM (\s -> s{lsLayouts = Map.insert pkgName layout (lsLayouts s)})
                            pureM (Right layout)

-- The level determination itself. @rest@ is the import path with the
-- package segment removed.
resolveInPackage ::
    Resolver ->
    FilePath ->
    PModule ->
    FileEntry ->
    Import ->
    Layout ->
    [String] ->
    LoadM (ResolvedImport, Maybe ModuleId)
resolveInPackage resolver entryPath sourceModule sourceFile imp layout rest = do
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
        parsedOf moduleName = parseModule resolver entryPath layout moduleName
    case rest of
        [] -> finish LevelModule rootId Nothing Nothing
        [x] -> do
            rootParsed <- parsedOf Nothing
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
            rootParsed <- parsedOf Nothing
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
                    rootParsed <- parsedOf Nothing
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
    resolveOne pmod pfile imp = resolveImport resolver entryPath (pmLayout pmod) pmod (pfEntry pfile) imp
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
loadFromEntry resolver rawEntry = case discoverEntry resolver entryPath of
    Standalone _ -> do
        text <- maybe (Left ("file not found: " ++ entryPath)) Right (resolverReadFile resolver entryPath)
        parsedFile <- case parseFileWith (locating emptyDecls) text of
            Left err -> Left ("parse error in file " ++ entryPath ++ ": " ++ show err)
            Right (parsed, _) -> Right parsed
        if null (fileImports parsedFile)
            then Right (StandaloneResult entryPath parsedFile)
            else
                Left
                    ( "standalone program "
                        ++ entryPath
                        ++ ": imports are not supported without a package (no package.tersus found in any ancestor directory); first import: "
                        ++ renderPath (importPath (head (fileImports parsedFile)))
                    )
    InPackage root pkgName -> do
        layout <- buildLayout resolver root
        let entryDir = dirNameOf entryPath
            entryModuleName
                | entryDir == root = Nothing
                | otherwise = Just (baseNameOf entryDir)
        if entryDir /= root && dirNameOf entryDir /= root
            then Left ("entry file " ++ entryPath ++ " is in a directory nested below module level under package " ++ pkgName ++ "; deeper nesting is not a module")
            else do
                let entryModuleId = layoutModuleId layout entryModuleName
                    initial =
                        LState
                            (Map.singleton pkgName layout)
                            Map.empty
                            Map.empty
                            []
                            Set.empty
                (finalState, ()) <- runLoadM (visitModule resolver entryPath [] entryModuleId layout entryModuleName) initial
                let modulesInOrder =
                        [ LoadedModule
                            moduleId'
                            [ LoadedFile
                                moduleId'
                                (feName (pfEntry pf))
                                (feStem (pfEntry pf))
                                (fePath (pfEntry pf))
                                (pfParsed pf)
                                (pfDecls pf)
                                (fromMaybe [] (Map.lookup (moduleId', feName (pfEntry pf)) (lsResolved finalState)))
                            | pf <- pmFiles pmod
                            ]
                            (sort (nub (declsOfModule pmod)))
                            (sort [dep | dep <- nub (concat [maybe [] pure (Just dep) | file <- pmFiles pmod, resolved <- fromMaybe [] (Map.lookup (moduleId', feName (pfEntry file)) (lsResolved finalState)), let target = resolvedTargetModule resolved, target /= moduleId', dep <- [target]])])
                        | moduleId' <- lsOrder finalState
                        , Just pmod <- [Map.lookup moduleId' (lsParsed finalState)]
                        ]
                Right
                    ( PackageResult
                        ( LoadedPackage
                            root
                            pkgName
                            entryPath
                            entryModuleId
                            modulesInOrder
                        )
                    )
  where
    entryPath = normalizePath rawEntry

-- Filesystem resolver: walk the real filesystem from an entry file to
-- its marker, snapshot the package (and any sibling packages) into an
-- in-memory resolver, and run the pure core on it. Not yet wired into
-- the CLI (that is Phase 5).

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
loadFromFilesystem entry = do
    root <- findPackageRootIO entry
    case root of
        Nothing -> do
            exists <- doesFileExist entry
            if not exists
                then return (Left ("file not found: " ++ entry))
                else do
                    text <- readFile entry
                    return (loadFromEntry (resolverFromFiles [(normalizePath entry, text)]) entry)
        Just packageRoot -> do
            packageFiles <- snapshotPackage packageRoot
            let parent = takeDirectory packageRoot
            siblings <- listDirectory parent >>= filterM (isSiblingPackage parent)
            siblingFiles <- fmap concat (mapM (\sib -> snapshotPackage (parent </> sib)) siblings)
            return (loadFromEntry (resolverFromFiles (packageFiles ++ siblingFiles)) entry)
  where
    isSiblingPackage parent name = do
        let dir = parent </> name
        isDir <- doesDirectoryExist dir
        if not isDir
            then return False
            else doesFileExist (dir </> "package.tersus")
    snapshotPackage root = do
        top <- snapshotDir root
        names <- listDirectory root
        dirs <- filterM (\name -> doesDirectoryExist (root </> name)) names
        moduleFiles <- fmap concat (mapM (\name -> snapshotDir (root </> name)) dirs)
        nestedFiles <-
            fmap concat $
                mapM
                    ( \modName -> do
                        subnames <- listDirectory (root </> modName)
                        subdirs <- filterM (\name -> doesDirectoryExist (root </> modName </> name)) subnames
                        fmap concat (mapM (\sub -> snapshotDir (root </> modName </> sub)) subdirs)
                    )
                    dirs
        return (top ++ moduleFiles ++ nestedFiles)
    snapshotDir dir = do
        names <- listDirectory dir
        files <- filterM (\name -> doesFileExist (dir </> name)) names
        mapM (\name -> do text <- readFile (dir </> name); return (normalizePath (dir </> name), text)) files
