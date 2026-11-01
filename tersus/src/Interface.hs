module Interface
    ( InterfaceFunction (..)
    , ModuleInterface (..)
    , extractInterface
    , interfaceImportEnv
    , mergeInterfacesImportEnv
    , predeclareOwnEnv
    , modulePrefixOf
    , nameInModule
    ) where

import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Modules (ModuleId (..), renderModuleId)
import TersusTypes
import TypeCheck (ImportEnv (..), TcState (..), emptyImportEnv, functionType)
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
    , ifImplArgs :: Map.Map (Name, Name) (Name, [Arg])
    , ifImplBounds :: Map.Map (Name, Name) [Bound]
    , ifCopies :: Set.Set Name
    , ifLinear :: Set.Set Name
    , ifDrops :: Set.Set Name
    , ifAxioms :: [Statement]
    , ifProofs :: [Statement]
    , ifExterns :: Set.Set Name
    }
    deriving (Show, Eq)

modulePrefixOf :: ModuleId -> String
modulePrefixOf (ModuleId pkg Nothing) = pkg ++ "$"
modulePrefixOf (ModuleId pkg (Just modu)) = pkg ++ "$" ++ modu ++ "$"

nameInModule :: ModuleId -> Name -> Bool
nameInModule modu name = modulePrefixOf modu `isPrefixOf` name || modulePrefixOf modu `isPrefixOf` dropWhile (/= '$') (drop 1 name)

extractInterface :: ModuleId -> [Statement] -> [Statement] -> TcState -> Result ModuleInterface String
extractInterface modu original elaborated state
    | not (null boundedNames) =
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
                    Map.fromList ([(name, (name, fields)) | StructDef name params fields _ <- elaborated, null params] ++ [(variant, (name, fields)) | EnumDef name variants <- elaborated, (variant, fields) <- variants])
                , ifGenerics = Map.fromList [(name, (params, fields)) | StructDef name params fields _ <- elaborated, not (null params)]
                , ifInvariants = Map.fromList [(name, invariant) | StructDef name _ _ invariant <- elaborated]
                , ifTraits = Map.fromList [(name, functions) | TraitDef name _ functions <- original]
                , ifTraitParams = Map.fromList [(name, params) | TraitDef name params _ <- original]
                , ifFunctions = Map.fromList [(name, interfaceFunction params ins outs signature termination exported) | Assign name (Val (VFunct params ins outs (NativeFunct signature termination _) exported)) <- elaborated, name `Set.member` declaredFunctions]
                , ifImpls = Set.filter (\(trait, ty) -> nameInModule modu trait || nameInModule modu ty) (tcImpls state)
                , ifAssoc = Map.filterWithKey (\(owner, _) _ -> nameInModule modu owner) (tcAssoc state)
                , ifImplArgs = Map.filterWithKey (\(trait, ty) _ -> nameInModule modu trait || nameInModule modu ty) (tcImplArgs state)
                , ifImplBounds = Map.filterWithKey (\(trait, ty) _ -> nameInModule modu trait || nameInModule modu ty) (tcImplBounds state)
                , ifCopies = Set.union (Set.fromList [name | CopyDef name <- elaborated]) (Set.fromList [ty | ("Copy", ty) <- Set.toList (tcImpls state), nameInModule modu ty])
                , ifLinear = Set.filter (nameInModule modu) (tcLinear state)
                , ifDrops = Set.filter (nameInModule modu) (tcDrops state)
                , ifAxioms = [stmt | stmt@(AxiomDef{}) <- elaborated]
                , ifProofs = [stmt | stmt@(ProofDef{}) <- elaborated]
                , ifExterns = Set.fromList [name | ExternDef name <- elaborated]
                }
  where
    boundedNames = [name | BoundedDef _ (Assign name _) <- original]
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
        , ieRefResults =
            Map.fromList
                [ (name, (fnParams fn, froms))
                | (name, fn) <- Map.toList (ifFunctions iface)
                , let Signature _ _ _ _ _ froms = fnSignature fn
                , not (null froms)
                ]
        }
  where
    functionOf fn = let Signature ptys rty sizes types _ _ = fnSignature fn in functionType sizes types ptys rty

predeclareOwnEnv :: ImportEnv -> ImportEnv
predeclareOwnEnv env = env{iePredeclareOwn = True}

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
                , iePredeclareOwn = iePredeclareOwn env
                }
