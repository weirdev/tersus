{-# LANGUAGE PatternSynonyms #-}

module PackageCompile
    ( CompiledModule (..)
    , CompiledPackage (..)
    , compileModules
    , lowerCompiledPackage
    , compileModulesLinked
    , assumptionsOfPackage
    ) where

import Data.List (nubBy, sortBy)
import Data.Ord (comparing)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Mir as M
import Compile (librariesFor, reservedHelperName, reservedError, completeSpecEnvs)
import Interface (InterfaceFunction (..), ModuleInterface (..), extractInterface, extractLibInterface, mergeInterfacesImportEnv, nameInModule, predeclareOwnEnv, withoutDeclaredNames)
import LibPackage (LibPackage (..), libModuleOfDisplay, libPackage, libSelectionFor, stripDeclaredFromUnits)
import Link (linkPrograms)
import ModuleResolve (rewriteFileReferences)
import qualified Modules as Mod
import ParsedFile (ParsedFile (..))
import MirLower (lowerModuleWith)
import Pretty (renderVarProof)
import Syntax (Expression (..), FunctBody (..), Statement (..), ValidationStatement (..), Value (..))
import TypeCheck (Elaborated (..), elaborateWith)
import Types (Signature (..), Type (..), pattern TBox, pattern TList, baseNameOf)
import Utils

data CompiledModule = CompiledModule
    { compiledModuleId :: Mod.ModuleId
    , compiledStatements :: [Statement]
    , compiledElaborated :: Elaborated
    , compiledInterface :: ModuleInterface
    , compiledLibInterfaces :: [ModuleInterface]
    , compiledLibUnits :: [(Mod.ModuleId, M.Program)]
    }
    deriving (Show)

data CompiledPackage = CompiledPackage
    { compiledEntryModule :: Mod.ModuleId
    , compiledModules :: [CompiledModule]
    }
    deriving (Show)

compileModules :: Mod.LoadedPackage -> Result CompiledPackage String
compileModules pkg = go (Mod.packageModules pkg) Map.empty []
  where
    go [] _ done = Ok (CompiledPackage (Mod.packageEntryModule pkg) (reverse done))
    go (modu : rest) interfaces done =
        case compileOne interfaces modu of
            Error err -> Error err
            Ok compiled -> go rest (Map.insert (Mod.loadedModuleId modu) (compiledInterface compiled) interfaces) (compiled : done)
    compileOne interfaces modu =
        let moduId = Mod.loadedModuleId modu
            extract = if moduId == Mod.packageEntryModule pkg then extractLibInterface else extractInterface
            depInterfaces = [interfaces Map.! dep | dep <- Mod.loadedDependencies modu, Map.member dep interfaces]
            missing = [dep | dep <- Mod.loadedDependencies modu, not (Map.member dep interfaces)]
         in if not (null missing)
                then Error ("in module " ++ Mod.renderModuleId moduId ++ ": dependency " ++ Mod.renderModuleId (head missing) ++ " was not compiled before it (the loader gives modules dependencies first)")
                else
                    case prepareModule pkg modu of
                        Left err -> Error err
                        Right prepared | Just name <- reservedHelperName prepared -> Error (reservedError name)
                        Right prepared -> case orphanCheck moduId prepared of
                            Left err -> Error err
                            Right () -> case libPackage of
                                Error err -> Error err
                                Ok libPkg -> case moduleLibSelection libPkg depInterfaces modu prepared of
                                    Left err -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": " ++ err)
                                    Right (libIfaces, libUnits, checkOnlyIfaces) ->
                                        let env = predeclareOwnEnv (mergeInterfacesImportEnv (libIfaces ++ checkOnlyIfaces ++ depInterfaces))
                                         in case elaborateWith env prepared of
                                                Error err -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": " ++ err)
                                                Ok (elaborated@(Elaborated elaboratedStmts _), state) -> case extract moduId prepared elaboratedStmts state of
                                                    Error err -> Error err
                                                    Ok iface -> Ok (CompiledModule moduId elaboratedStmts elaborated iface (libIfaces ++ checkOnlyIfaces) libUnits)

-- The compiler libraries a module is checked against: the interfaces of
-- the librariesFor-selected lib modules (synthesised implicit imports, all
-- their names usable bare), closed over their dependencies, plus the lib
-- units to link. The selection is decided from the module as it was read,
-- with the dependency interfaces probed for String/HashMap/HashSet, as
-- before. A module that impls Drop without the prelude being selected
-- (declaring one of the prelude's traits itself suppresses the prelude)
-- is checked against the prelude's Drop trait alone, check-only: that is
-- what the old Drop-trait extraction from the prelude text served, and
-- no lib unit is linked for it.
moduleLibSelection :: LibPackage -> [ModuleInterface] -> Mod.LoadedModule -> [Statement] -> Either String ([ModuleInterface], [(Mod.ModuleId, M.Program)], [ModuleInterface])
moduleLibSelection libPkg depInterfaces modu prepared =
    let selected = [name | display <- map fst (librariesFor probed), Just name <- [libModuleOfDisplay display]]
        selection = libSelectionFor libPkg selected prepared
        checkOnlyIfaces
            | needsDropTrait prepared && "prelude" `notElem` selected = case Map.lookup "prelude" (libInterfaces libPkg) of
                Just preludeIface -> [dropOnlyInterface preludeIface]
                Nothing -> []
            | otherwise = []
     in do
        (selectedIfaces, libUnits) <- selection
        let libIfaces = map (withoutDeclaredNames (moduleDeclaredNames prepared)) selectedIfaces
            libUnits' = stripDeclaredFromUnits (moduleDeclaredNames prepared) libUnits
        Right (libIfaces, libUnits', checkOnlyIfaces)
  where
    probed = concatMap (fileBody . Mod.loadedParsed) (Mod.loadedModuleFiles modu) ++ [Return (Var name) | name <- ["String", "HashMap", "HashSet"], name `elem` dependencyTypeNames]
    dependencyTypeNames = concatMap interfaceTypeNames depInterfaces
    interfaceTypeNames iface =
        Map.keys (ifTypes iface)
            ++ Map.keys (ifGenerics iface)
            ++ concatMap (concatMap (typeNames . snd) . snd) (Map.elems (ifCtors iface))
            ++ concatMap (concatMap (typeNames . snd) . snd) (Map.elems (ifGenerics iface))
            ++ concatMap signatureTypeNames (Map.elems (ifFunctions iface))
    signatureTypeNames fn = let Signature params ret _ _ _ _ = fnSignature fn in concatMap typeNames (ret : params)
    typeNames ty = case ty of
        TNamed name _ -> [name]
        TVariant name -> [name]
        TList inner -> typeNames inner
        TArrayOf inner _ -> typeNames inner
        TBox inner -> typeNames inner
        TAddr inner -> typeNames inner
        TBlock inner -> typeNames inner
        TUninit inner -> typeNames inner
        TRef inner -> typeNames inner
        TMutRef inner -> typeNames inner
        TFn args ret -> concatMap typeNames (ret : args)
        TForall _ _ inner -> typeNames inner
        _ -> []
-- The names a prepared module itself declares, under the names it declares
-- them (the entry module's are the bare names the libraries use; another
-- module's are canonical and so do not meet the libraries' bare names).
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

needsDropTrait :: [Statement] -> Bool
needsDropTrait prepared = any implsDrop prepared && not (any declaresDrop prepared)
  where
    implsDrop stmt = case stmt of
        ImplDef (Just trait) _ _ _ _ _ -> localName trait == "Drop"
        _ -> False
    declaresDrop stmt = case stmt of
        TraitDef name _ _ -> localName name == "Drop"
        _ -> False
    localName name = reverse (takeWhile (/= '$') (reverse name))

-- The prelude interface cut down to its Drop trait: the real bare Drop
-- trait of the imported prelude unit, for a module that impls Drop while
-- the prelude is not selected for it (see moduleLibSelection).
dropOnlyInterface :: ModuleInterface -> ModuleInterface
dropOnlyInterface iface =
    iface
        { ifTypes = Map.empty
        , ifCtors = Map.empty
        , ifGenerics = Map.empty
        , ifInvariants = Map.empty
        , ifTraits = Map.filterWithKey (\name _ -> name == "Drop") (ifTraits iface)
        , ifTraitParams = Map.filterWithKey (\name _ -> name == "Drop") (ifTraitParams iface)
        , ifFunctions = Map.empty
        , ifImpls = Set.empty
        , ifAssoc = Map.empty
        , ifImplArgs = Map.empty
        , ifImplBounds = Map.empty
        , ifCopies = Set.empty
        , ifLinear = Set.empty
        , ifDrops = Set.empty
        , ifAxioms = []
        , ifProofs = []
        , ifExterns = Set.empty
        , ifTemplates = Map.empty
        , ifCompanions = Map.empty
        }

prepareModule :: Mod.LoadedPackage -> Mod.LoadedModule -> Either String [Statement]
prepareModule pkg modu = do
    perFile <- mapM prepareFile (Mod.loadedModuleFiles modu)
    Right (reorderModuleStatements (concat perFile))
  where
    prepareFile file =
        let identity
                | Mod.loadedModuleId modu == Mod.packageEntryModule pkg = Mod.rootModuleIdentity (Mod.packagePackageName pkg) (Mod.loadedFileStem file ++ ".tersus")
                | otherwise = Mod.fileModuleIdentity (Mod.modulePackage (Mod.loadedFileModule file)) (maybe "" id (Mod.moduleName (Mod.loadedFileModule file))) (Mod.loadedFileStem file ++ ".tersus")
            canonical = Mod.canonicalizeDeclarations identity (fileBody (Mod.loadedParsed file))
         in case rewriteFileReferences pkg file canonical of
                Left err -> Left ("in module " ++ Mod.renderModuleId (Mod.loadedModuleId modu) ++ " file " ++ Mod.loadedFileName file ++ ": " ++ err)
                Right rewritten -> Right rewritten

reorderModuleStatements :: [Statement] -> [Statement]
reorderModuleStatements = sortBy (comparing category)
  where
    category :: Statement -> Int
    category stmt = case stmt of
        StructDef{} -> 0
        EnumDef{} -> 0
        TraitDef{} -> 0
        ImplDef{} -> 1
        _ -> 2

orphanCheck :: Mod.ModuleId -> [Statement] -> Either String ()
orphanCheck modu statements = case [message | ImplDef (Just trait) _ typeName _ _ _ <- statements, Just message <- [orphanMessage trait typeName]] of
    message : _ -> Left message
    [] -> Right ()
  where
    declared = [name | stmt <- statements, name <- declaredNamesOf stmt]
    declaredNamesOf stmt = case stmt of
        StructDef name _ _ _ -> [name]
        EnumDef name _ -> [name]
        TraitDef name _ _ -> [name]
        _ -> []
    orphanMessage trait typeName
        | trait `elem` declared || baseOf typeName `elem` declared = Nothing
        | nameInModule modu trait || nameInModule modu (baseOf typeName) = Nothing
        | otherwise = Just ("in module " ++ Mod.renderModuleId modu ++ ": orphan impl: impl " ++ trait ++ " for " ++ typeName ++ " defines neither a trait nor a type of this module; an impl must live in the module of its trait or of its type")
    baseOf name = baseNameOf name

-- The modules of a package lowered and linked into one program, not yet
-- validated (Pipeline.compileModulesValidated validates it; the host's own
-- programs are built from this, see MirHousekeeping.toolProgram)
compileModulesLinked :: Mod.LoadedPackage -> Result M.Program String
compileModulesLinked pkg = compileModules pkg `bindResult` lowerCompiledPackage pkg

-- Callers must validate the linked program before erasure or execution.
lowerCompiledPackage :: Mod.LoadedPackage -> CompiledPackage -> Result M.Program String
lowerCompiledPackage pkg compiled =
    let ifaceMap = Map.fromList [(compiledModuleId modu, compiledInterface modu) | modu <- compiledModules compiled]
        loadedMap = Map.fromList [(Mod.loadedModuleId modu, modu) | modu <- Mod.packageModules pkg]
        lowerOne modu = case Map.lookup (compiledModuleId modu) loadedMap of
            Nothing -> Error ("internal: compiled module " ++ Mod.renderModuleId (compiledModuleId modu) ++ " is not in the loaded package")
            Just loaded ->
                let depIfaces = [ifaceMap Map.! dep | dep <- Mod.loadedDependencies loaded, Map.member dep ifaceMap]
                    allIfaces = compiledLibInterfaces modu ++ depIfaces
                 in mapResult (\program -> (compiledModuleId modu, program)) (stage "Lowering failed: " (lowerModuleWith (mergeInterfacesImportEnv allIfaces) allIfaces (compiledElaborated modu)))
        libUnits = nubBy (\(a, _) (b, _) -> a == b) (concatMap compiledLibUnits (compiledModules compiled))
     in flatResultMap lowerOne (compiledModules compiled) `bindResult` \units -> mapResult completeSpecEnvs (linkPrograms (libUnits ++ units))

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
