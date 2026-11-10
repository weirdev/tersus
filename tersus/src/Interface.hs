module Interface
    ( InterfaceFunction (..)
    , ModuleInterface (..)
    , withoutDeclaredNames
    , modulePrefixOf
    , nameInModule
    ) where

import Data.List (isInfixOf, isPrefixOf)
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

modulePrefixOf :: ModuleId -> String
modulePrefixOf (ModuleId pkg Nothing) = pkg ++ "$"
modulePrefixOf (ModuleId pkg (Just modu)) = pkg ++ "$" ++ modu ++ "$"

nameInModule :: ModuleId -> Name -> Bool
nameInModule modu name = modulePrefixOf modu `isPrefixOf` name || modulePrefixOf modu `isPrefixOf` dropWhile (/= '$') (drop 1 name)

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
