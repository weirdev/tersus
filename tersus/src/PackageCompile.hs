module PackageCompile
    ( CompiledModule (..)
    , CompiledPackage (..)
    , compileModules
    , compileModulesWith
    , compileModulesUsing
    , lowerCompiledPackage
    , compileModulesLinked
    , assumptionsOfPackage
    , packageFailure
    ) where

import Data.List (nubBy)
import qualified Data.Map as Map
import qualified Mir as M
import ElaborateRequest (LoadKind (..), LoadRequest (..), LoadResponse (..), Response (..))
import ElaboratorTool (Loader, sourceLoader)
import Interface (ModuleInterface (..))
import LibPackage (LibPackage, libCatalog, libInterfaces, libModuleId, libPackage, libSelection, stripDeclaredFromUnits, withoutReplacedEq)
import Link (linkPrograms)
import qualified Modules as Mod
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
    }
    deriving (Show)

data CompiledPackage = CompiledPackage
    { compiledEntryModule :: Mod.ModuleId
    , compiledModules :: [CompiledModule]
    }
    deriving (Show)

compileModules :: Mod.Snapshot -> Result CompiledPackage String
compileModules = compileModulesWith sourceLoader

compileModulesWith :: Loader -> Mod.Snapshot -> Result CompiledPackage String
compileModulesWith loader = compileModulesUsing loader libPackage

-- The package of the snapshot's entry, loaded and every module elaborated in order by the loader written in Tersus,
-- which names the interfaces each is lowered with. The libraries are a parameter so that the frontend seed's stages
-- can give ones elaborated by the same elaborator; when they failed, the first module that is given them refuses.
compileModulesUsing :: Loader -> Result LibPackage String -> Mod.Snapshot -> Result CompiledPackage String
compileModulesUsing loader libraries snapshot = case loader ((Mod.loadRequest LoadPackage snapshot) {lrLibraries = either' [] libCatalog libraries}) of
    LoadedModules answers -> go answers Map.empty [] `bindResult` \modules ->
        if any ((== entry) . compiledModuleId) modules
            then Ok (CompiledPackage entry modules)
            else Error ("internal: the loader did not answer for the entry module " ++ Mod.renderModuleId entry)
    NotLoaded err -> Error err
    _ -> Error "internal: the loader did not answer with the package's modules"
  where
    entry = Mod.entryModuleOf snapshot
    either' d f r = case r of
        Ok a -> f a
        Error _ -> d
    -- (only when the libraries failed: which modules are given none)
    noPrelude = case Mod.graphResult snapshot loader of
        Right (Mod.PackageResult pkg) -> [Mod.loadedModuleId m | m <- Mod.packageModules pkg, Mod.loadedNoPrelude m]
        _ -> []
    go [] _ done = Ok (reverse done)
    go ((moduId, lowering, response) : rest) ifaces done = case (libraries, response) of
        (Error err, _) | moduId `notElem` noPrelude -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": " ++ err)
        (_, Accepted elaborated@(Elaborated stmts _) (Just iface) selected) ->
            let (selectedIfaces, units) = either' ([], []) (`libSelection` selected) libraries
                known = Map.insert moduId iface ifaces
                libIfaces = either' Map.empty (\p -> Map.fromList [(libModuleId n, i) | (n, i) <- Map.toList (libInterfaces p)]) libraries
             in case mapM (\i -> maybe (Map.lookup i libIfaces) Just (Map.lookup i known)) lowering of
                    Nothing -> Error ("internal: the loader named an interface it did not give for module " ++ Mod.renderModuleId moduId)
                    Just loweringIfaces ->
                        go rest known (CompiledModule moduId stmts elaborated iface (withoutReplacedEq stmts selectedIfaces) (stripDeclaredFromUnits (moduleDeclaredNames stmts) units) loweringIfaces : done)
        _ -> Error (packageFailure moduId response)

packageFailure :: Mod.ModuleId -> Response -> String
packageFailure moduId response = case response of
    Refused err -> inModule err
    NotModelled what -> inModule ("the elaborator does not handle this module yet: " ++ what)
    RefusedInterface err -> err
    Unresolved err -> err
    Accepted _ _ _ -> inModule "the elaborator gave no interface"
  where
    inModule err = "in module " ++ Mod.renderModuleId moduId ++ ": " ++ err
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
compileModulesLinked :: Mod.Snapshot -> Result M.Program String
compileModulesLinked snapshot = compileModules snapshot `bindResult` lowerCompiledPackage

-- Callers must validate the linked program before erasure or execution.
lowerCompiledPackage :: CompiledPackage -> Result M.Program String
lowerCompiledPackage compiled =
    let lowerOne modu = mapResult (\program -> (compiledModuleId modu, program)) (stage "Lowering failed: " (lowerModuleWith (compiledImportInterfaces modu) (compiledElaborated modu)))
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

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
