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

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Mir as M
import ElaborateRequest (LoadKind (..), LoadRequest (..), LoadResponse (..), Response (..), acceptedOwnership)
import ElaboratorTool (Loader, sourceLoader)
import Interface (ModuleInterface (..))
import LibPackage (LibPackage (..), libCatalog, libModuleId, libPackage)
import Link (linkPrograms)
import Lowering (lowerAccepted)
import Mir (Lowered (..))
import MirMoves (finishLowered)
import qualified Modules as Mod
import Pretty (renderExpression, renderVarProof)
import Syntax (Statement (..))
import Types (OwnershipTransport (..), Storage (..))
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
    }
    deriving (Show)

compileModules :: Mod.Snapshot -> Result CompiledPackage String
compileModules = compileModulesWith sourceLoader

compileModulesWith :: Loader -> Mod.Snapshot -> Result CompiledPackage String
compileModulesWith loader = compileModulesUsing loader libPackage

-- The package or standalone unit of the snapshot's entry, loaded and elaborated in order by the loader written in
-- Tersus. When the snapshot uses the exact installed std package, cached std modules compiled through the same
-- LoadPackage path are reused without re-elaboration; custom --std-root and sibling std packages compile freshly.
compileModulesUsing :: Loader -> Result LibPackage String -> Mod.Snapshot -> Result CompiledPackage String
compileModulesUsing loader libraries snapshot =
    let useCache = Mod.usesInstalledStd snapshot
        request = (Mod.loadRequest LoadPackage snapshot){lrLibraries = if useCache then either' [] libCatalog libraries else []}
     in case loader request of
            LoadedModules answers ->
                go answers [] `bindResult` \modules ->
                    if any ((== entry) . compiledModuleId) modules
                        then cachedModules useCache answers modules `bindResult` \cached ->
                            Ok (CompiledPackage entry (cached ++ modules))
                        else Error ("internal: the loader did not answer for the entry module " ++ Mod.renderModuleId entry)
            NotLoaded err -> Error err
            _ -> Error "internal: the loader did not answer with the package's modules"
  where
    entry = Mod.entryModuleOf snapshot
    either' d f r = case r of
        Ok a -> f a
        Error _ -> d
    go [] done = Ok (reverse done)
    go ((moduId, _, response) : rest) done = case response of
        Accepted (Just iface) _ _ ->
            let lowered = lowerAccepted response
                facts = acceptedOwnership response
             in case either' [] (uncoveredTypes facts) lowered of
                    [] -> go rest (CompiledModule moduId iface lowered facts : done)
                    missing -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": the ownership facts omit the declared types " ++ unwords missing)
        _ -> Error (packageFailure moduId response)
    cachedModules False _ _ = Ok []
    cachedModules True answers modules =
        let present = Set.fromList (map compiledModuleId modules)
            neededDirect = Set.fromList [name | (_, deps, _) <- answers, m@(Mod.ModuleId "std" (Just name)) <- deps, Set.notMember m present]
         in if Set.null neededDirect
                then Ok []
                else libraries `bindResult` \pkg ->
                    let needed = closeStd pkg neededDirect
                        ordered = [name | name <- libOrder pkg, Set.member name needed, Set.notMember (libModuleId name) present]
                     in flatResultMap (cachedOne pkg) ordered
    closeStd pkg = goClose Set.empty
      where
        goClose seen pending
            | Set.null pending = seen
            | otherwise =
                let next = Set.difference pending seen
                    deps = Set.fromList [d | n <- Set.toList next, d <- Map.findWithDefault [] n (libImports pkg)]
                 in goClose (Set.union seen next) (Set.difference deps (Set.union seen next))
    cachedOne pkg name = case (Map.lookup name (libInterfaces pkg), Map.lookup name (libLowered pkg)) of
        (Just iface, Just lowered) -> Ok (CompiledModule (libModuleId name) iface lowered (Map.findWithDefault Nothing name (libOwnership pkg)))
        _ -> Error ("internal: missing cached std module " ++ name)

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
    inModule err
        | moduId == Mod.ModuleId "" Nothing = err
        | otherwise = "in module " ++ Mod.renderModuleId moduId ++ ": " ++ err

-- The modules of a package lowered and linked into one program, not yet
-- validated (Pipeline.compileModulesValidated validates it; the host's own
-- programs are built from this, see MirHousekeeping.toolProgram)
compileModulesLinked :: Mod.Snapshot -> Result M.Program String
compileModulesLinked snapshot = compileModules snapshot `bindResult` lowerCompiledPackage

-- Callers must validate the linked program before erasure or execution.
lowerCompiledPackage :: CompiledPackage -> Result M.Program String
lowerCompiledPackage compiled = packageLinkInputs compiled `bindResult` linkPrograms

packageLinkInputs :: CompiledPackage -> Result [(Mod.ModuleId, M.Program)] String
packageLinkInputs compiled = flatResultMap lowerOne (compiledModules compiled)
  where
    lowerOne modu = mapResult (\p -> (compiledModuleId modu, withCaptureStorage p)) (stage "Lowering failed: " (compiledLowered modu `bindResult` finishLowered))
    withCaptureStorage p =
        let st = M.progStorage p
            names = Set.fromList (filter (not . null) [storageList st, storageBox st])
            captured = Map.restrictKeys (M.progGenerics p) names
         in if Map.null captured then p else p{M.progCaptureStorage = Map.union (M.progCaptureStorage p) captured}

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
