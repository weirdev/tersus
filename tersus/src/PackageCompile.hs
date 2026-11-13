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
import qualified Data.Set as Set
import qualified Mir as M
import ElaborateRequest (LoadKind (..), LoadRequest (..), LoadResponse (..), Response (..))
import ElaboratorTool (Loader, sourceLoader)
import Interface (ModuleInterface (..))
import LibPackage (LibPackage, libCatalog, libPackage, libSelection, stripDeclaredFromUnits)
import Link (linkPrograms)
import qualified Modules as Mod
import Lowering (lowerAccepted)
import Mir (Lowered (..))
import MirMoves (finishLowered)
import Pretty (renderVarProof)
import Syntax (Statement (..))
import Utils

data CompiledModule = CompiledModule
    { compiledModuleId :: Mod.ModuleId
    , compiledInterface :: ModuleInterface
    , compiledLibUnits :: [(Mod.ModuleId, M.Program)] -- without what the module declares itself
    , compiledLowered :: Result Lowered String -- the unit the elaborator lowered the module to, or why it did not
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
    LoadedModules answers -> go answers [] `bindResult` \modules ->
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
    go [] done = Ok (reverse done)
    go ((moduId, _, response) : rest) done = case (libraries, response) of
        (Error err, _) | moduId `notElem` noPrelude -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": " ++ err)
        (_, Accepted (Just iface) selected _) ->
            let lowered = lowerAccepted response
                declared = either' [] (Set.toList . lowDeclared) lowered
                units = either' [] (`libSelection` selected) libraries
             in go rest (CompiledModule moduId iface (stripDeclaredFromUnits declared units) lowered : done)
        _ -> Error (packageFailure moduId response)

packageFailure :: Mod.ModuleId -> Response -> String
packageFailure moduId response = case response of
    Refused err -> inModule err
    NotModelled what -> inModule ("the elaborator does not handle this module yet: " ++ what)
    RefusedInterface err -> err
    Unresolved err -> err
    Accepted{} -> inModule "the elaborator gave no interface"
  where
    inModule err = "in module " ++ Mod.renderModuleId moduId ++ ": " ++ err
-- The modules of a package lowered and linked into one program, not yet
-- validated (Pipeline.compileModulesValidated validates it; the host's own
-- programs are built from this, see MirHousekeeping.toolProgram)
compileModulesLinked :: Mod.Snapshot -> Result M.Program String
compileModulesLinked snapshot = compileModules snapshot `bindResult` lowerCompiledPackage

-- Callers must validate the linked program before erasure or execution.
lowerCompiledPackage :: CompiledPackage -> Result M.Program String
lowerCompiledPackage compiled =
    let lowerOne modu = mapResult (\program -> (compiledModuleId modu, program)) (stage "Lowering failed: " (compiledLowered modu `bindResult` finishLowered))
        libUnits = nubBy (\(a, _) (b, _) -> a == b) (concatMap compiledLibUnits (compiledModules compiled))
     in flatResultMap lowerOne (compiledModules compiled) `bindResult` \units -> linkPrograms (libUnits ++ units)

-- (a module's assumes are in the unit it was lowered to: one that did not lower has no list of them to give)
assumptionsOfPackage :: CompiledPackage -> Result [String] String
assumptionsOfPackage compiled = mapResult concat (flatResultMap perModule (compiledModules compiled))
  where
    perModule modu =
        let prefix = "in module " ++ Mod.renderModuleId (compiledModuleId modu) ++ ": "
            iface = compiledInterface modu
            axioms = [prefix ++ "axiom " ++ localName name ++ "(" ++ commas args ++ ")" | AxiomDef name args _ _ <- ifAxioms iface]
            externs = [prefix ++ "extern fn " ++ localName name | name <- foldr (:) [] (ifExterns iface)]
         in case compiledLowered modu of
                Error err -> Error (prefix ++ err)
                Ok lowered -> Ok (axioms ++ externs ++ [prefix ++ "assume " ++ renderVarProof proof | proof <- lowAssumes lowered])
    localName name = reverse (takeWhile (/= '$') (reverse name))
    commas = foldr (\a b -> if null b then a else a ++ ", " ++ b) ""

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
