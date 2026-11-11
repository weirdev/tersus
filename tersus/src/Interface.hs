module Interface
    ( InterfaceFunction (..)
    , ModuleInterface (..)
    ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Modules (ModuleId (..))
import Syntax
import Types
import Elaboration (Template)

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
