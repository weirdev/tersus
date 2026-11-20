module PackageCompile
    ( CompiledModule (..)
    , CompiledPackage (..)
    , compileModules
    , compileModulesWith
    , compileModulesUsing
    , lowerCompiledPackage
    , packageLinkInputs
    , compileModulesLinked
    , assumptionsOfPackage
    , packageFailure
    ) where

import qualified Data.Set as Set
import qualified Mir as M
import ElaborateRequest (LoadKind (..), LoadRequest (..), LoadResponse (..), MirAnswer (..), Response (..), acceptedOwnership)
import qualified Data.Map.Strict as Map
import Types (OwnershipTransport (..))
import ElaboratorTool (Loader, sourceLoader)
import Interface (ModuleInterface (..))
import LibPackage (LibPackage, libCatalog, libPackage, libUnit, stripDeclaredFromUnit)
import Link (linkPrograms)
import qualified Modules as Mod
import Lowering (lowerAccepted)
import Mir (Lowered (..))
import MirMoves (finishLowered)
import Pretty (renderExpression, renderVarProof)
import Syntax (Statement (..))
import Utils

data CompiledModule = CompiledModule
    { compiledModuleId :: Mod.ModuleId
    , compiledInterface :: ModuleInterface
    , compiledLowered :: Result Lowered String -- the unit the elaborator lowered the module to, or why it did not
    , compiledOwnership :: Maybe OwnershipTransport -- the checked ownership facts of a version 2 elaboration
    }
    deriving (Show)

data CompiledPackage = CompiledPackage
    { compiledEntryModule :: Mod.ModuleId
    , compiledModules :: [CompiledModule]
    , compiledLibUnits :: Result [(Mod.ModuleId, M.Program)] String
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
compileModulesUsing loader libraries snapshot = case loader ((Mod.loadRequest (LoadPackageAssembly entry) snapshot) {lrLibraries = either' [] libCatalog libraries}) of
    AssembledPackage root rows answers -> complete answers $ \modules ->
        if root == entry
            then Ok (CompiledPackage entry modules (assemble modules rows))
            else Error "internal: the loader answered with the wrong assembly entry"
    LoadedModules answers -> complete answers $ \modules ->
        if any loweringRefused answers
            then Ok (CompiledPackage entry modules (Error missingAssembly))
            else Error missingAssembly
    NotLoaded err -> Error err
    _ -> Error "internal: the loader did not answer with the package's modules"
  where
    entry = Mod.entryModuleOf snapshot
    missingAssembly = "internal: the loader did not answer with the package's assembly"
    complete answers use = go answers [] `bindResult` \modules ->
        if any ((== entry) . compiledModuleId) modules
            then use modules
            else Error ("internal: the loader did not answer for the entry module " ++ Mod.renderModuleId entry)
    loweringRefused (_, _, Accepted _ _ MirRefused{}) = True
    loweringRefused _ = False
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
        (_, Accepted (Just iface) _ _) ->
            let lowered = lowerAccepted response
                facts = acceptedOwnership response
             in case either' [] (uncoveredTypes facts) lowered of
                    [] -> go rest (CompiledModule moduId iface lowered facts : done)
                    missing -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": the ownership facts omit the declared types " ++ unwords missing)
        _ -> Error (packageFailure moduId response)
    assemble modules rows = flatResultMap unit rows
      where
        contributors = Map.fromList [(compiledModuleId m, compiledLowered m) | m <- modules]
        unit (name, owner) = case Map.lookup owner contributors of
            Nothing -> Error ("internal: no assembly contributor " ++ Mod.renderModuleId owner)
            Just lowered -> lowered `bindResult` \l -> libraries `bindResult` \pkg ->
                mapResult (stripDeclaredFromUnit (lowDeclared l)) (libUnit pkg name)

-- The structs and enums a module declares that its checked ownership facts give no row for
uncoveredTypes :: Maybe OwnershipTransport -> Lowered -> [String]
uncoveredTypes facts lowered = case facts of
    Nothing -> []
    Just transport -> [name | name <- Set.toList (lowDeclared lowered), Map.member name (M.progTypes (lowProgram lowered)) || Map.member name (M.progGenerics (lowProgram lowered)), not (Map.member name (transportOwnership transport))]

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
lowerCompiledPackage compiled = packageLinkInputs compiled `bindResult` \(libraries, units) -> linkPrograms (libraries ++ units)

packageLinkInputs :: CompiledPackage -> Result ([(Mod.ModuleId, M.Program)], [(Mod.ModuleId, M.Program)]) String
packageLinkInputs compiled =
    flatResultMap lowerOne (compiledModules compiled) `bindResult` \units ->
        mapResult (\libraries -> (libraries, units)) (compiledLibUnits compiled)
  where
    lowerOne modu = mapResult ((,) (compiledModuleId modu)) (stage "Lowering failed: " (compiledLowered modu `bindResult` finishLowered))

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
                Ok lowered -> Ok (axioms ++ externs ++ [prefix ++ either (("assume " ++) . renderVarProof) renderExpression trusted | trusted <- lowAssumes lowered])
    localName name = reverse (takeWhile (/= '$') (reverse name))
    commas = foldr (\a b -> if null b then a else a ++ ", " ++ b) ""

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
