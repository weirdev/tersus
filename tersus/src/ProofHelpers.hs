module ProofHelpers
    ( iotaProofToVarProof
    , namedIotaMap
    , proofIotas
    , proofOnlyOfNamedIotasOrConst
    , proofVars
    , substituteProofTerm
    , valStmtDefinedVars
    ) where

import Data.Containers.ListUtils (nubOrd)
import Data.Map (Map, fromList)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isJust)

import Types
import Syntax
import Utils

-- Helpers for the terms of proofs: which iotas and variables a proof mentions, replacing a term by another, and moving a
-- proof between the iotas of the validator's values and the names a function gives them.

-- All iotas a proof mentions
proofIotas :: Proof Iota -> [Iota]
proofIotas (ATerm iota) = [iota]
proofIotas (CTerm _) = []
proofIotas (BVar _) = []
proofIotas (Forall _ guards body) = concatMap proofIotas (body : guards)
proofIotas (FApp funct args) = proofIotas funct ++ concatMap proofIotas args

-- The proof with each occurrence of the source replaced by the target, if there is one
substituteProofTerm :: IotaProof -> IotaProof -> IotaProof -> Maybe IotaProof
substituteProofTerm source target proof
    | proof == source = Just target
substituteProofTerm source target (FApp funct args) =
    let maybeFunct = substituteProofTerm source target funct
     in let maybeArgs = map (substituteProofTerm source target) args
         in if any isJust (maybeFunct : maybeArgs)
                then
                    Just
                        ( FApp
                            (fromMaybe funct maybeFunct)
                            (zipWith (flip fromMaybe) maybeArgs args)
                        )
                else Nothing
substituteProofTerm source target (Forall index guards body) =
    let maybeGuards = map (substituteProofTerm source target) guards
        maybeBody = substituteProofTerm source target body
     in if any isJust (maybeBody : maybeGuards)
            then Just (Forall index (zipWith (`maybe` id) guards maybeGuards) (fromMaybe body maybeBody))
            else Nothing
substituteProofTerm _ _ _ = Nothing

proofVars :: VariableProof -> [Variable]
proofVars (CTerm _) = []
proofVars (ATerm var) = [var]
proofVars BVar{} = []
proofVars (Forall _ guards body) = nubOrd (concatMap proofVars guards ++ proofVars body)
proofVars (FApp funct args) = nubOrd (proofVars funct ++ concatMap proofVars args)

valStmtDefinedVars :: ValidationStatement -> [Variable]
-- Only proof-variable definitions are exportable names from a validation block.
valStmtDefinedVars (AssignProofVar var _) = [var]
valStmtDefinedVars _ = []

proofOnlyOfNamedIotasOrConst :: Map Iota Variable -> IotaProof -> Bool
proofOnlyOfNamedIotasOrConst namedIotas (ATerm iota) = Map.member iota namedIotas
proofOnlyOfNamedIotasOrConst _ CTerm{} = True
proofOnlyOfNamedIotasOrConst _ BVar{} = True
proofOnlyOfNamedIotasOrConst namedIotas (Forall _ guards body) =
    all (proofOnlyOfNamedIotasOrConst namedIotas) (body : guards)
proofOnlyOfNamedIotasOrConst namedIotas (FApp funct proofs) =
    proofOnlyOfNamedIotasOrConst namedIotas funct
        && all (proofOnlyOfNamedIotasOrConst namedIotas) proofs

iotaProofToVarProof :: Map Iota Variable -> IotaProof -> Maybe VariableProof
iotaProofToVarProof _ (CTerm val) = Just (CTerm val)
iotaProofToVarProof _ (BVar index) = Just (BVar index)
iotaProofToVarProof namedIotas (Forall index guards body) =
    Forall index <$> collectMaybes (iotaProofToVarProof namedIotas) guards <*> iotaProofToVarProof namedIotas body
iotaProofToVarProof namedIotas (ATerm iota) = ATerm <$> Map.lookup iota namedIotas
iotaProofToVarProof namedIotas (FApp funct args) = do
    vfunct <- iotaProofToVarProof namedIotas funct
    vargs <- collectMaybes (iotaProofToVarProof namedIotas) args
    Just (FApp vfunct vargs)

namedIotaMap :: [(Variable, Iota)] -> Map Iota Variable
namedIotaMap = fromList . map (\(var, iota) -> (iota, var))
