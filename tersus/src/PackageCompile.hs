module PackageCompile
    ( CompiledModule (..)
    , CompiledPackage (..)
    , compileModules
    , compileModulesValidated
    , assumptionsOfPackage
    ) where

import Data.List (sortBy)
import Data.Ord (comparing)
import qualified Data.Map as Map
import qualified Mir as M
import Compile (librariesFor)
import Interface (InterfaceFunction (..), ModuleInterface (..), extractInterface, mergeInterfacesImportEnv, nameInModule, predeclareOwnEnv)
import Link (linkPrograms)
import ModuleResolve (rewriteFileReferences)
import qualified Modules as Mod
import Parse (ParsedFile (..), emptyDecls, parseStatementBlockWith)
import PreludeSource (preludeSource)
import MirLower (lowerModuleWith)
import MirValidate (validateProgram)
import Pretty (renderVarProof)
import Syntax (Expression (..), FunctBody (..), Statement (..), ValidationStatement (..), Value (..))
import TypeCheck (Elaborated (..), elaborateWith)
import Types (Signature (..), Type (..), baseNameOf)
import Utils

data CompiledModule = CompiledModule
    { compiledModuleId :: Mod.ModuleId
    , compiledStatements :: [Statement]
    , compiledElaborated :: Elaborated
    , compiledInterface :: ModuleInterface
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
            depInterfaces = [interfaces Map.! dep | dep <- Mod.loadedDependencies modu, Map.member dep interfaces]
            missing = [dep | dep <- Mod.loadedDependencies modu, not (Map.member dep interfaces)]
         in if not (null missing)
                then Error ("in module " ++ Mod.renderModuleId moduId ++ ": dependency " ++ Mod.renderModuleId (head missing) ++ " was not compiled before it (the loader gives modules dependencies first)")
                else
                    let env = predeclareOwnEnv (mergeInterfacesImportEnv depInterfaces)
                     in case prepareModule pkg modu of
                            Left err -> Error err
                            Right prepared -> case orphanCheck moduId prepared of
                                Left err -> Error err
                                Right () -> case moduleLibraryStatements depInterfaces modu of
                                    Left err -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": " ++ err)
                                    Right libraryStmts ->
                                        let withLibraries = libraryStmts ++ prepared
                                            augmented = if needsDropTrait withLibraries then dropTraitStatements ++ withLibraries else withLibraries
                                         in case elaborateWith env augmented of
                                                Error err -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": " ++ err)
                                                Ok (elaborated@(Elaborated elaboratedStmts _), state) -> case extractInterface moduId prepared elaboratedStmts state of
                                                    Error err -> Error err
                                                    Ok iface -> Ok (CompiledModule moduId elaboratedStmts elaborated iface)

moduleLibraryStatements :: [ModuleInterface] -> Mod.LoadedModule -> Either String [Statement]
moduleLibraryStatements depInterfaces modu = readLibraries (librariesFor probed) emptyDecls
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
    readLibraries [] _ = Right []
    readLibraries ((name, text) : more) declared = case parseStatementBlockWith declared text of
        Left err -> Left ("Parse error in " ++ name ++ ": " ++ show err)
        Right (stmts, declared') -> fmap (stmts ++) (readLibraries more declared')

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

dropTraitStatements :: [Statement]
dropTraitStatements = case parseStatementBlockWith emptyDecls preludeSource of
    Right (stmts, _) -> [stmt | stmt@(TraitDef name _ _) <- stmts, name == "Drop"]
    Left _ -> []

prepareModule :: Mod.LoadedPackage -> Mod.LoadedModule -> Either String [Statement]
prepareModule pkg modu = do
    perFile <- mapM prepareFile (Mod.loadedModuleFiles modu)
    Right (reorderModuleStatements (concat perFile))
  where
    prepareFile file =
        let identity
                | Mod.loadedModuleId modu == Mod.packageEntryModule pkg = Mod.rootModuleIdentity (Mod.packagePackageName pkg) (Mod.loadedFileStem file ++ ".tersus")
                | otherwise = Mod.fileModuleIdentity (Mod.packagePackageName pkg) (maybe "" id (Mod.moduleName (Mod.loadedFileModule file))) (Mod.loadedFileStem file ++ ".tersus")
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

compileModulesValidated :: Mod.LoadedPackage -> Result M.Program String
compileModulesValidated pkg =
    compileModules pkg `bindResult` \compiled ->
        let ifaceMap = Map.fromList [(compiledModuleId modu, compiledInterface modu) | modu <- compiledModules compiled]
            loadedMap = Map.fromList [(Mod.loadedModuleId modu, modu) | modu <- Mod.packageModules pkg]
            lowerOne modu = case Map.lookup (compiledModuleId modu) loadedMap of
                Nothing -> Error ("internal: compiled module " ++ Mod.renderModuleId (compiledModuleId modu) ++ " is not in the loaded package")
                Just loaded ->
                    let depIfaces = [ifaceMap Map.! dep | dep <- Mod.loadedDependencies loaded, Map.member dep ifaceMap]
                     in mapResult (\program -> (compiledModuleId modu, program)) (stage "Lowering failed: " (lowerModuleWith (mergeInterfacesImportEnv depIfaces) depIfaces (compiledElaborated modu)))
         in flatResultMap lowerOne (compiledModules compiled) `bindResult` \units ->
                linkPrograms units `bindResult` \linked ->
                    stage "Validation failed: " (validateProgram linked) `bindResult` \_ -> Ok linked

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
