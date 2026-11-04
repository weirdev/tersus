module Interface
    ( InterfaceFunction (..)
    , ModuleInterface (..)
    , extractInterface
    , extractLibInterface
    , interfaceImportEnv
    , mergeInterfacesImportEnv
    , predeclareOwnEnv
    , withoutDeclaredNames
    , modulePrefixOf
    , nameInModule
    ) where

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import LibParsed (nativeStorageModules)
import Modules (ModuleId (..), renderModuleId)
import Syntax
import Types
import TypeCheck (ImportEnv (..), emptyImportEnv)
import TypeCheckCore (TcState (..), Template (..), functionType, isRefType)
import Utils (Result (..))

data InterfaceFunction = InterfaceFunction
    { fnParams :: [Variable]
    , fnSignature :: Signature
    , fnRequires :: [ValidationStatement]
    , fnEnsures :: [ValidationStatement]
    , fnTermination :: Maybe Termination
    , fnExported :: [VariableProof]
    }
    deriving (Show, Eq)

data ModuleInterface = ModuleInterface
    { ifModule :: ModuleId
    , ifTypes :: Map.Map Name [Name]
    , ifCtors :: Map.Map Name (Name, [(Variable, Type)])
    , ifGenerics :: Map.Map Name ([Variable], [(Variable, Type)])
    , ifInvariants :: Map.Map Name [ValidationStatement]
    , ifTraits :: Map.Map Name [TraitFn]
    , ifTraitParams :: Map.Map Name [Variable]
    , ifFunctions :: Map.Map Name InterfaceFunction
    , ifImpls :: Set.Set (Name, Name)
    , ifAssoc :: Map.Map (Name, Name) [Maybe Name]
    , ifImplArgs :: Map.Map (Name, Name) (Type, [Arg])
    , ifImplBounds :: Map.Map (Name, Name) [Bound]
    , ifCopies :: Set.Set Name
    , ifLinear :: Set.Set Name
    , ifDrops :: Set.Set Name
    , ifAxioms :: [Statement]
    , ifProofs :: [Statement]
    , ifExterns :: Set.Set Name
    , ifTemplates :: Map.Map Name Template
    , ifCompanions :: Map.Map Name [Name]
    }
    deriving (Show, Eq)

modulePrefixOf :: ModuleId -> String
modulePrefixOf (ModuleId pkg Nothing) = pkg ++ "$"
modulePrefixOf (ModuleId pkg (Just modu)) = pkg ++ "$" ++ modu ++ "$"

nameInModule :: ModuleId -> Name -> Bool
nameInModule modu name = modulePrefixOf modu `isPrefixOf` name || modulePrefixOf modu `isPrefixOf` dropWhile (/= '$') (drop 1 name)

extractInterface :: ModuleId -> [Statement] -> [Statement] -> TcState -> Result ModuleInterface String
extractInterface modu = extractInterfaceWith (nameInModule modu) False modu

-- The interface of a compiler-library module (LibPackage): its declarations
-- keep bare names, so every impl it checked belongs to it, and its bounded
-- functions travel as templates for importers to instantiate.
extractLibInterface :: ModuleId -> [Statement] -> [Statement] -> TcState -> Result ModuleInterface String
extractLibInterface modu = extractInterfaceWith (const True) True modu

extractInterfaceWith :: (Name -> Bool) -> Bool -> ModuleId -> [Statement] -> [Statement] -> TcState -> Result ModuleInterface String
extractInterfaceWith inModule isLib modu original elaborated state
    | hasValueProjection (original ++ elaborated) || any (hasValueProjection . tmplBody) (Map.elems (tcTemplates state)) = Error "Unmodeled: checked declaration-backed value projections"
    | any unsupportedTemplateDeclaration (original ++ elaborated) || any (\template -> borrowedResult (templateOrigins template) || hasBorrowedResult (tmplBody template)) (Map.elems (tcTemplates state)) = Error "Unmodeled: checked borrowed whole-value return places in bounded templates"
    | not isLib && not (null boundedNames) =
        Error
            ( "in module "
                ++ renderModuleId modu
                ++ ": bounded function "
                ++ head boundedNames
                ++ " cannot be exported in a module interface: a function with bounds on its types (BoundedDef) is usable inside its home module only"
            )
    | otherwise =
        Ok
            ModuleInterface
                { ifModule = modu
                , ifTypes = Map.union (Map.fromList [(name, [name]) | StructDef name _ _ _ <- elaborated]) (Map.fromList [(name, map fst variants) | EnumDef name variants <- elaborated])
                , ifCtors =
                    Map.union
                        (Map.fromList ([(name, (name, fields)) | StructDef name params fields _ <- elaborated, null params] ++ [(variant, (name, fields)) | EnumDef name variants <- elaborated, (variant, fields) <- variants]))
                        ( if isLib
                            then Map.fromList [(inst, (inst, fields)) | (name, (params, fields)) <- Map.toList genericStructs, let inst = instanceName name [if isTypeName param then ArgType (TParam param) else ArgSize (SizeParam param) | param <- params]]
                            else Map.empty
                        )
                , ifGenerics = genericStructs
                , ifInvariants = Map.fromList [(name, invariant) | StructDef name _ _ spec <- elaborated, let invariant = structInvariant spec, not (null invariant)]
                , ifTraits = Map.fromList [(name, functions) | TraitDef name _ functions <- original]
                , ifTraitParams = Map.fromList [(name, params) | TraitDef name params _ <- original]
                , ifFunctions = Map.fromList [(name, interfaceFunction params ins outs signature termination exported) | Assign name (Val (VFunct params ins outs (NativeFunct signature termination _) exported)) <- elaborated, name `Set.member` declaredFunctions]
                , ifImpls = Set.filter implVisible (tcImpls state)
                , ifAssoc = Map.filterWithKey (\(owner, _) origins -> if isLib then baseNameOf owner `Set.member` ownNames || any (\trait -> implHere (trait, baseNameOf owner)) [trait | Just trait <- origins] else inModule owner) (tcAssoc state)
                , ifImplArgs = Map.filterWithKey (\(trait, ty) _ -> implVisible (trait, ty)) (tcImplArgs state)
                , ifImplBounds = Map.filterWithKey (\(trait, ty) _ -> implVisible (trait, ty)) (tcImplBounds state)
                , ifCopies = Set.union (Set.fromList [name | CopyDef name <- elaborated]) (Set.fromList [ty | ("Copy", ty) <- Set.toList (tcImpls state), if isLib then implHere ("Copy", ty) else inModule ty])
                , ifLinear = Set.filter typeVisible (tcLinear state)
                , ifDrops = Set.filter (\name -> typeVisible name || isLib && ("Drop", baseNameOf name) `Set.member` declaredImpls) (tcDrops state)
                , ifAxioms = [stmt | stmt@(AxiomDef{}) <- elaborated]
                , ifProofs = [stmt | stmt@(ProofDef{}) <- elaborated]
                , ifExterns = Set.fromList [name | ExternDef name <- elaborated]
                , ifTemplates =
                    if isLib
                        then Map.filterWithKey (\name _ -> templateHere name) (tcTemplates state)
                        else Map.filterWithKey (\name _ -> name `elem` boundedNames) (tcTemplates state)
                , ifCompanions =
                    if isLib
                        then Map.filterWithKey (\name _ -> templateHere name) (tcCompanions state)
                        else Map.filterWithKey (\name _ -> name `elem` boundedNames) (tcCompanions state)
                }
  where
    templateOrigins template = let Signature _ _ _ _ _ origins = tmplSignature template in origins
    boundedNames = [name | BoundedDef _ (Assign name _) <- original]
    genericStructs = Map.fromList [(name, (params, fields)) | StructDef name params fields _ <- elaborated, not (null params)]
    ownNames = Set.fromList (concatMap declaredTypeOrTrait original)
    declaredTypeOrTrait stmt = case stmt of
        StructDef name _ _ _ -> [name]
        EnumDef name _ -> [name]
        TraitDef name _ _ -> [name]
        _ -> []
    implHere pair@(trait, ty) = pair `Set.member` declaredImpls || trait `Set.member` ownNames || baseNameOf ty `Set.member` ownNames
    declaredImpls
        | modu `elem` [ModuleId "tersuslib" (Just name) | name <- nativeStorageModules] = Set.fromList [(trait, ty) | ImplDef (Just trait) _ ty _ _ _ <- original]
        | otherwise = Set.empty
    implVisible pair =
        if isLib
            then implHere pair
            else inModule (fst pair) || inModule (snd pair)
    typeVisible name =
        if isLib
            then baseNameOf name `Set.member` ownNames
            else inModule name
    templateHere name
        | name `elem` boundedNames = True
        | "<" `isPrefixOf` name = case breakOn " as " (takeWhile (/= '>') (drop 1 name)) of
            Just (owner, trait) -> baseNameOf owner `Set.member` ownNames || trait `Set.member` ownNames
            Nothing -> baseNameOf (takeWhile (/= '>') (drop 1 name)) `Set.member` ownNames
        | otherwise = case breakOn " for " name of
            Just (trait, rest) -> trait `Set.member` ownNames || baseNameOf (takeWhile (/= ':') rest) `Set.member` ownNames
            Nothing -> False
    breakOn needle = go ""
      where
        go acc text
            | needle `isPrefixOf` text = Just (reverse acc, drop (length needle) text)
            | otherwise = case text of
                c : rest -> go (c : acc) rest
                [] -> Nothing
    declaredFunctions =
        Set.fromList $
            concatMap
                declared
                original
    declared stmt = case stmt of
        Assign name (Val VFunct{}) -> [name]
        ImplDef _ _ _ _ _ functions -> concatMap declared functions
        BoundedDef _ inner -> declared inner
        _ -> []
    interfaceFunction params ins outs signature termination exported = InterfaceFunction params signature ins outs termination exported

interfaceImportEnv :: ModuleInterface -> ImportEnv
interfaceImportEnv iface =
    emptyImportEnv
        { ieTypes = ifTypes iface
        , ieCtors = ifCtors iface
        , ieGenerics = ifGenerics iface
        , ieTraits = ifTraits iface
        , ieTraitParams = ifTraitParams iface
        , ieFunctions = Map.map functionOf (ifFunctions iface)
        , ieImpls = ifImpls iface
        , ieAssoc = ifAssoc iface
        , ieImplArgs = ifImplArgs iface
        , ieImplBounds = ifImplBounds iface
        , ieLinear = ifLinear iface
        , ieDrops = ifDrops iface
        , ieTemplates = ifTemplates iface
        , ieCompanions = ifCompanions iface
        , ieRefResults =
            Map.union
                ( Map.fromList
                    [ (trait ++ "::" ++ traitFnName fn, (traitFnParams fn, froms))
                    | (trait, functions) <- Map.toList (ifTraits iface)
                    , fn <- functions
                    , let Signature params result _ _ _ fromNames = traitFnSignature fn
                    , let froms = if not (null fromNames) then fromNames else case [param | (param, ty) <- zip (traitFnParams fn) params, isRefType ty] of [only] -> [ReferenceOrigin only]; _ -> []
                    , not (null froms)
                    , isRefType result || borrowedResult fromNames
                    ]
                )
                ( Map.fromList
                    [ (name, (fnParams fn, froms))
                    | (name, fn) <- Map.toList (ifFunctions iface)
                    , let Signature _ _ _ _ _ froms = fnSignature fn
                    , not (null froms)
                    ]
                )
        }
  where
    functionOf fn = let Signature ptys rty sizes types _ _ = fnSignature fn in functionType sizes types ptys rty

predeclareOwnEnv :: ImportEnv -> ImportEnv
predeclareOwnEnv env = env{iePredeclareOwn = True}

-- An interface as a module that itself declares some of the same names
-- sees it: the module's own declarations win, so nothing the interface
-- declares under one of those names is imported. This is what keeps the
-- selection of Compile.librariesFor in force when a library is only in
-- the environment as a dependency of another: a program that declares
-- its own trait Eq does not have the equality library in front of it,
-- and the string library that is in front of it (which depends on the
-- equality library) must not put the library Eq back. Retained impls
-- were checked against the library trait, not the user's declaration:
-- LibPackage.libSelectionFor checks exact Eq compatibility before it
-- exposes them, and keeps suppressed implementation registries private.
withoutDeclaredNames :: [Name] -> ModuleInterface -> ModuleInterface
withoutDeclaredNames declared iface =
    iface
        { ifTypes = Map.withoutKeys (ifTypes iface) declaredSet
        , ifCtors = Map.filterWithKey (\ctor (owner, _) -> ctor `Set.notMember` declaredSet && owner `Set.notMember` declaredSet) (ifCtors iface)
        , ifGenerics = Map.withoutKeys (ifGenerics iface) declaredSet
        , ifInvariants = Map.withoutKeys (ifInvariants iface) declaredSet
        , ifTraits = Map.withoutKeys (ifTraits iface) declaredSet
        , ifTraitParams = Map.withoutKeys (ifTraitParams iface) declaredSet
        , ifFunctions = Map.withoutKeys (ifFunctions iface) declaredSet
        , ifCopies = Set.filter (\name -> baseNameOf name `Set.notMember` declaredSet) (ifCopies iface)
        , ifLinear = Set.filter (\name -> baseNameOf name `Set.notMember` declaredSet) (ifLinear iface)
        , ifDrops = Set.filter (\name -> baseNameOf name `Set.notMember` declaredSet) (ifDrops iface)
        , ifAxioms = [stmt | stmt@(AxiomDef name _ _ _) <- ifAxioms iface, name `Set.notMember` declaredSet]
        , ifProofs = [stmt | stmt@(ProofDef name _ _ _ _) <- ifProofs iface, name `Set.notMember` declaredSet]
        , ifExterns = Set.difference (ifExterns iface) declaredSet
        , ifTemplates = Map.filterWithKey (\name _ -> not (declaredName name)) (ifTemplates iface)
        , ifCompanions = Map.filterWithKey (\name _ -> not (declaredName name)) (ifCompanions iface)
        }
  where
    declaredSet = Set.fromList declared
    declaredName name = name `Set.member` declaredSet || any (\own -> (" as " ++ own ++ ">") `isInfixOf` name || (own ++ "::") `isPrefixOf` name) declared

mergeInterfacesImportEnv :: [ModuleInterface] -> ImportEnv
mergeInterfacesImportEnv ifaces = foldr merge emptyImportEnv ifaces
  where
    merge iface env =
        let addition = interfaceImportEnv iface
         in ImportEnv
                { ieTypes = Map.union (ieTypes addition) (ieTypes env)
                , ieCtors = Map.union (ieCtors addition) (ieCtors env)
                , ieGenerics = Map.union (ieGenerics addition) (ieGenerics env)
                , ieTraits = Map.union (ieTraits addition) (ieTraits env)
                , ieTraitParams = Map.union (ieTraitParams addition) (ieTraitParams env)
                , ieFunctions = Map.union (ieFunctions addition) (ieFunctions env)
                , ieImpls = Set.union (ieImpls addition) (ieImpls env)
                , ieAssoc = Map.unionWith (++) (ieAssoc addition) (ieAssoc env)
                , ieImplArgs = Map.union (ieImplArgs addition) (ieImplArgs env)
                , ieImplBounds = Map.union (ieImplBounds addition) (ieImplBounds env)
                , ieLinear = Set.union (ieLinear addition) (ieLinear env)
                , ieDrops = Set.union (ieDrops addition) (ieDrops env)
                , ieRefResults = Map.union (ieRefResults addition) (ieRefResults env)
                , ieTemplates = Map.union (ieTemplates addition) (ieTemplates env)
                , ieCompanions = Map.unionWith (++) (ieCompanions addition) (ieCompanions env)
                , iePredeclareOwn = iePredeclareOwn env
                }
