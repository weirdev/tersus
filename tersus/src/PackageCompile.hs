module PackageCompile
    ( CompiledModule (..)
    , CompiledPackage (..)
    , compileModules
    , compileModulesWith
    , compileModulesUsing
    , lowerCompiledPackage
    , compileModulesLinked
    , assumptionsOfPackage
    ) where

import Data.List (nubBy)
import qualified Data.Map as Map
import qualified Mir as M
import ElaborateRequest (Elaborator, Extraction (..), FileImport (..), Package (..), PackageFile (..), Request (..), Response (..))
import ElaboratorTool (sourceElaborator)
import Interface (ModuleInterface (..))
import LibPackage (LibPackage, libCatalog, libPackage, libDefinitionContexts, libSelection, stripDeclaredFromUnits, withoutReplacedEq)
import Link (linkPrograms)
import qualified Modules as Mod
import ParsedFile (Import (..), ParsedFile (..))
import MirLower (lowerModuleWith)
import Pretty (renderVarProof)
import Syntax (Elaborated (..), Expression (..), FunctBody (..), Statement (..), ValidationStatement (..), Value (..))
import Utils

data CompiledModule = CompiledModule
    { compiledModuleId :: Mod.ModuleId
    , compiledStatements :: [Statement]
    , compiledElaborated :: Elaborated
    , compiledInterface :: ModuleInterface
    , compiledLibInterfaces :: [ModuleInterface]
    , compiledLibUnits :: [(Mod.ModuleId, M.Program)]
    , compiledImportInterfaces :: [ModuleInterface]
    , compiledDefinitionContexts :: [[ModuleInterface]]
    }
    deriving (Show)

data CompiledPackage = CompiledPackage
    { compiledEntryModule :: Mod.ModuleId
    , compiledModules :: [CompiledModule]
    }
    deriving (Show)

compileModules :: Mod.LoadedPackage -> Result CompiledPackage String
compileModules = compileModulesWith sourceElaborator

compileModulesWith :: Elaborator -> Mod.LoadedPackage -> Result CompiledPackage String
compileModulesWith elaborator = compileModulesUsing elaborator libPackage

-- The libraries are a parameter so that the frontend seed's stages can give ones elaborated by the same elaborator
compileModulesUsing :: Elaborator -> Result LibPackage String -> Mod.LoadedPackage -> Result CompiledPackage String
compileModulesUsing elaborator libraries pkg = go (Mod.packageModules pkg) Map.empty []
  where
    package = packageOf pkg
    go [] _ done = Ok (CompiledPackage (Mod.packageEntryModule pkg) (reverse done))
    go (modu : rest) compiled done =
        case compileOne compiled modu of
            Error err -> Error err
            Ok unit -> go rest (Map.insert (Mod.loadedModuleId modu) unit compiled) (unit : done)
    compileOne compiled modu =
        let moduId = Mod.loadedModuleId modu
            inModule err = "in module " ++ Mod.renderModuleId moduId ++ ": " ++ err
            depModules = [compiled Map.! dep | dep <- Mod.loadedDependencies modu, Map.member dep compiled]
            depInterfaces = map compiledInterface depModules
            definingContexts = uniqueContexts (concatMap compiledDefinitionContexts depModules)
            missing = [dep | dep <- Mod.loadedDependencies modu, not (Map.member dep compiled)]
            given = if Mod.loadedNoPrelude modu then Ok Nothing else mapResult Just libraries
         in case (missing, given) of
                (dep : _, _) -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": dependency " ++ Mod.renderModuleId dep ++ " was not compiled before it (the loader gives modules dependencies first)")
                (_, Error err) -> Error (inModule err)
                (_, Ok libPkg) ->
                    let request = Request moduId True False ModuleInterfaceOf depInterfaces definingContexts (maybe [] libCatalog libPkg) (Just package) [fileBody (Mod.loadedParsed file) | file <- Mod.loadedModuleFiles modu] 0
                     in case elaborator request of
                            Accepted elaborated@(Elaborated elaboratedStmts _) (Just iface) selected ->
                                let (selectedIfaces, libUnits) = maybe ([], []) (`libSelection` selected) libPkg
                                    libIfaces = withoutReplacedEq elaboratedStmts selectedIfaces
                                    definitions = uniqueContexts (maybe [] (`libDefinitionContexts` selected) libPkg ++ definingContexts)
                                    lowering = uniqueInterfaces (libIfaces ++ depInterfaces ++ concat definitions)
                                 in Ok (CompiledModule moduId elaboratedStmts elaborated iface libIfaces (stripDeclaredFromUnits (moduleDeclaredNames elaboratedStmts) libUnits) lowering (uniqueContexts ((iface : lowering) : definitions)))
                            Accepted _ Nothing _ -> Error (inModule "the elaborator gave no interface")
                            Refused err -> Error (inModule err)
                            RefusedInterface err -> Error err
                            Unresolved err -> Error err
                            NotModelled what -> Error (inModule ("the elaborator does not handle this module yet: " ++ what))

packageOf :: Mod.LoadedPackage -> Package
packageOf pkg = Package (Mod.packageEntryModule pkg) [packageFile file | modu <- Mod.packageModules pkg, file <- Mod.loadedModuleFiles modu]
  where
    packageFile file = PackageFile (Mod.loadedFileModule file) (Mod.loadedFileStem file) (Mod.loadedFileName file) (Mod.fileDeclarations (fileBody (Mod.loadedParsed file))) (map fileImport (Mod.loadedImports file))
    fileImport ri = FileImport (Mod.resolvedLevel ri) (Mod.resolvedTargetModule ri) (Mod.resolvedTargetFile ri) (Mod.resolvedTargetSymbol ri) (importAlias (Mod.resolvedImport ri)) (importNames (Mod.resolvedImport ri))

-- The names a module itself declares, under the names it declares them (the entry module's are the bare names the
-- libraries use; another module's are canonical and so do not meet the libraries' bare names), which the library units
-- linked for it do not declare again
moduleDeclaredNames :: [Statement] -> [String]
moduleDeclaredNames prepared = concatMap declared prepared ++ concatMap defined prepared
  where
    declared stmt = case stmt of
        StructDef name _ _ _ -> [name]
        EnumDef name _ -> [name]
        TraitDef name _ _ -> [name]
        _ -> []
    defined stmt = case stmt of
        Assign name (Val VFunct{}) -> [name]
        ImplDef _ _ _ _ _ body -> concatMap defined body
        BoundedDef _ inner -> defined inner
        _ -> []

-- The modules of a package lowered and linked into one program, not yet
-- validated (Pipeline.compileModulesValidated validates it; the host's own
-- programs are built from this, see MirHousekeeping.toolProgram)
compileModulesLinked :: Mod.LoadedPackage -> Result M.Program String
compileModulesLinked pkg = compileModules pkg `bindResult` lowerCompiledPackage pkg

-- Callers must validate the linked program before erasure or execution.
lowerCompiledPackage :: Mod.LoadedPackage -> CompiledPackage -> Result M.Program String
lowerCompiledPackage pkg compiled =
    let loadedMap = Map.fromList [(Mod.loadedModuleId modu, modu) | modu <- Mod.packageModules pkg]
        lowerOne modu = case Map.lookup (compiledModuleId modu) loadedMap of
            Nothing -> Error ("internal: compiled module " ++ Mod.renderModuleId (compiledModuleId modu) ++ " is not in the loaded package")
            Just _ ->
                let allIfaces = compiledImportInterfaces modu
                 in mapResult (\program -> (compiledModuleId modu, program)) (stage "Lowering failed: " (lowerModuleWith allIfaces (compiledElaborated modu)))
        libUnits = nubBy (\(a, _) (b, _) -> a == b) (concatMap compiledLibUnits (compiledModules compiled))
     in flatResultMap lowerOne (compiledModules compiled) `bindResult` \units -> linkPrograms (libUnits ++ units)

assumptionsOfPackage :: CompiledPackage -> [String]
assumptionsOfPackage compiled = concatMap perModule (compiledModules compiled)
  where
    perModule modu =
        let prefix = "in module " ++ Mod.renderModuleId (compiledModuleId modu) ++ ": "
            iface = compiledInterface modu
            axioms = [prefix ++ "axiom " ++ localName name ++ "(" ++ commas args ++ ")" | AxiomDef name args _ _ <- ifAxioms iface]
            externs = [prefix ++ "extern fn " ++ localName name | name <- foldr (:) [] (ifExterns iface)]
            assumes = [prefix ++ "assume " ++ renderVarProof proof | proof <- concatMap assumesIn (compiledStatements modu)]
         in axioms ++ externs ++ assumes
    localName name = reverse (takeWhile (/= '$') (reverse name))
    commas = foldr (\a b -> if null b then a else a ++ ", " ++ b) ""
    assumesIn stmt = case stmt of
        ValidationStatement (Assume proof) -> [proof]
        Assign _ (Val (VFunct _ _ _ (NativeFunct _ _ body) _)) -> concatMap assumesIn body
        Block body -> concatMap assumesIn body
        If _ yes no -> concatMap assumesIn (yes ++ no)
        While _ _ _ body -> concatMap assumesIn body
        ImplDef _ _ _ _ _ body -> concatMap assumesIn body
        BoundedDef _ inner -> assumesIn inner
        _ -> []

uniqueContexts :: [[ModuleInterface]] -> [[ModuleInterface]]
uniqueContexts = nubBy (\a b -> map ifModule (take 1 a) == map ifModule (take 1 b))

uniqueInterfaces :: [ModuleInterface] -> [ModuleInterface]
uniqueInterfaces = nubBy (\a b -> ifModule a == ifModule b)

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
