module ProofEngine
    ( BuiltinEvaluator
    , ProofContext
    , EngineRewriteRule (..)
    , emptyProofContext
    , proofContextFromFacts
    , proofContextFacts
    , insertProofs
    , proofContextDelta
    , entails
    , applyRewrite
    , deriveRefl
    , reflectProofsByProofs
    ) where

import Data.List (nub)
import Data.Maybe (fromMaybe)

import StdLib
import TersusTypes
import Utils

type BuiltinEvaluator = BuiltinFunct -> [Value] -> Result Value String

newtype ProofContext = ProofContext [IotaProof] deriving (Show, Eq)

data EngineRewriteRule
    = EngineRefl
    | EngineEval Iota
    | EngineEvalAll
    | EngineCheckGtZero IotaProof
    deriving (Show, Eq)

emptyProofContext :: ProofContext
emptyProofContext = ProofContext []

proofContextFromFacts :: [IotaProof] -> ProofContext
proofContextFromFacts = ProofContext . nub

proofContextFacts :: ProofContext -> [IotaProof]
proofContextFacts (ProofContext facts) = facts

insertProofs :: [IotaProof] -> ProofContext -> ProofContext
insertProofs newFacts (ProofContext facts) = ProofContext (nub (facts ++ newFacts))

proofContextDelta :: ProofContext -> ProofContext -> [IotaProof]
proofContextDelta (ProofContext oldFacts) (ProofContext newFacts) =
    filter (`notElem` oldFacts) newFacts

entails :: IotaProof -> ProofContext -> Bool
entails goal context@(ProofContext facts) =
    any (proofEquivalent context goal) facts

applyRewrite :: BuiltinEvaluator -> EngineRewriteRule -> ProofContext -> Result ProofContext String
applyRewrite _ EngineRefl context = Ok (deriveRefl context)
applyRewrite evalBuiltin (EngineEval iota) context =
    Ok (insertProofs (evalIota evalBuiltin iota context) context)
applyRewrite evalBuiltin EngineEvalAll context =
    Ok (insertProofs (evalAll evalBuiltin context) context)
applyRewrite evalBuiltin (EngineCheckGtZero proof) context =
    checkGtZero evalBuiltin proof context

checkGtZero :: BuiltinEvaluator -> IotaProof -> ProofContext -> Result ProofContext String
checkGtZero evalBuiltin proof context =
    let gtZeroProof = FApp (CTerm (builtinFunct (Rel Gt))) [proof, CTerm (VInt 0)]
     in if entails gtZeroProof context
            then Ok (insertProofs [gtZeroProof] context)
            else case evalProofTerm evalBuiltin proof context of
                Just (VInt num) | num > 0 -> Ok (deriveRefl (insertProofs [gtZeroProof] context))
                Just (VInt _) -> Error "Proof term is not greater than 0"
                Just _ -> Error "Proof term is not an int"
                Nothing -> Error "Proof term lacks concrete definition and no equivalent proof exists"

deriveRefl :: ProofContext -> ProofContext
deriveRefl context@(ProofContext facts) =
    let eqFacts = equalityFacts facts
        reversedEqFacts = map reverseEqProof eqFacts
        derivedFacts = reflectProofsByProofs facts (eqFacts ++ reversedEqFacts)
     in insertProofs derivedFacts context

evalAll :: BuiltinEvaluator -> ProofContext -> [IotaProof]
evalAll evalBuiltin context@(ProofContext facts) =
    concatMap (evalProof evalBuiltin context) facts

evalIota :: BuiltinEvaluator -> Iota -> ProofContext -> [IotaProof]
evalIota evalBuiltin iota context@(ProofContext facts) =
    concatMap (evalProofIfForIota evalBuiltin iota context) facts

evalProofIfForIota :: BuiltinEvaluator -> Iota -> ProofContext -> IotaProof -> [IotaProof]
evalProofIfForIota evalBuiltin iota context proof =
    case proof of
        FApp funct [ATerm proofIota, FApp _ _]
            | funct == eqProof && proofIota == iota ->
                evalProof evalBuiltin context proof
        _ -> []

evalProof :: BuiltinEvaluator -> ProofContext -> IotaProof -> [IotaProof]
evalProof
    evalBuiltin
    context
    ( FApp
            eqFunct
            [ ATerm iota
                , FApp (CTerm (VFunct _ _ _ (BuiltinFunct funct) _)) args
                ]
        )
        | eqFunct == eqProof =
            case proofArgsToValues args context of
                Just values ->
                    case evalBuiltin funct values of
                        Ok val -> [FApp eqFunct [ATerm iota, CTerm val]]
                        Error _ -> []
                Nothing -> []
evalProof _ _ _ = []

proofArgsToValues :: [IotaProof] -> ProofContext -> Maybe [Value]
proofArgsToValues [] _ = Just []
proofArgsToValues (ATerm iota : proofs) context =
    case concreteValueOfIota iota context of
        Just value ->
            case proofArgsToValues proofs context of
                Just values -> Just (value : values)
                Nothing -> Nothing
        Nothing -> Nothing
proofArgsToValues (CTerm value : proofs) context =
    case proofArgsToValues proofs context of
        Just values -> Just (value : values)
        Nothing -> Nothing
proofArgsToValues _ _ = Nothing

evalProofTerm :: BuiltinEvaluator -> IotaProof -> ProofContext -> Maybe Value
evalProofTerm _ (CTerm value) _ = Just value
evalProofTerm _ (ATerm iota) context = concreteValueOfIota iota context
evalProofTerm evalBuiltin (FApp (CTerm (VFunct _ _ _ (BuiltinFunct funct) _)) args) context =
    case proofArgsToValues args context of
        Just values ->
            case evalBuiltin funct values of
                Ok value -> Just value
                Error _ -> Nothing
        Nothing -> Nothing
evalProofTerm _ _ _ = Nothing

concreteValueOfIota :: Iota -> ProofContext -> Maybe Value
concreteValueOfIota iota (ProofContext facts) =
    concreteValueOfIotaFromFacts iota facts

concreteValueOfIotaFromFacts :: Iota -> [IotaProof] -> Maybe Value
concreteValueOfIotaFromFacts _ [] = Nothing
concreteValueOfIotaFromFacts iota (proof : proofs) =
    case proof of
        FApp funct [ATerm proofIota, CTerm val]
            | funct == eqProof && proofIota == iota -> Just val
        _ -> concreteValueOfIotaFromFacts iota proofs

proofEquivalent :: ProofContext -> IotaProof -> IotaProof -> Bool
proofEquivalent context (FApp goalFunct goalArgs) (FApp factFunct factArgs) =
    length goalArgs == length factArgs
        && proofEquivalent context goalFunct factFunct
        && all (uncurry (proofEquivalent context)) (zip goalArgs factArgs)
proofEquivalent context goal fact =
    fact `elem` equivalentTermsInclusive 10 context goal

-- Terms reachable from the proof through at most `depth` equalities, including the
-- proof itself. Breadth-first with a seen list: equalities are symmetric once
-- deriveRefl adds their reversals, so an unmemoized walk revisits terms
-- exponentially often.
equivalentTermsInclusive :: Int -> ProofContext -> IotaProof -> [IotaProof]
equivalentTermsInclusive depth context proof = expandEquivalentTerms depth context [proof] [proof]

expandEquivalentTerms :: Int -> ProofContext -> [IotaProof] -> [IotaProof] -> [IotaProof]
expandEquivalentTerms 0 _ _ seen = seen
expandEquivalentTerms _ _ [] seen = seen
expandEquivalentTerms depth context frontier seen =
    let nextFrontier =
            nub
                [ next
                | current <- frontier
                , next <- firstDegreeEquivalentTerms context current
                , next `notElem` seen
                ]
     in expandEquivalentTerms (depth - 1) context nextFrontier (seen ++ nextFrontier)

firstDegreeEquivalentTerms :: ProofContext -> IotaProof -> [IotaProof]
firstDegreeEquivalentTerms (ProofContext facts) proof =
    mapMaybeProof (firstDegreeEquivalentTerm proof) facts

firstDegreeEquivalentTerm :: IotaProof -> IotaProof -> Maybe IotaProof
firstDegreeEquivalentTerm proof (FApp funct [lhs, rhs])
    | funct == eqProof && lhs == proof = Just rhs
    | funct == eqProof && rhs == proof = Just lhs
firstDegreeEquivalentTerm _ _ = Nothing

equalityFacts :: [IotaProof] -> [IotaProof]
equalityFacts facts =
    [ proof
    | proof@(FApp funct [_lhs, _rhs]) <- facts
    , funct == eqProof
    ]

reflectProofsByProofs :: [IotaProof] -> [IotaProof] -> [IotaProof]
reflectProofsByProofs proofs = nub . concatMap (reflectProofsByProof proofs)

reflectProofsByProof :: [IotaProof] -> IotaProof -> [IotaProof]
reflectProofsByProof (proof : proofs) eqProofSource@(FApp funct [_lhs, _rhs])
    | funct == eqProof =
        case reflectProofByProof proof eqProofSource of
            Just newProof -> newProof : reflectProofsByProof proofs eqProofSource
            Nothing -> reflectProofsByProof proofs eqProofSource
reflectProofsByProof _ _ = []

reflectProofByProof :: IotaProof -> IotaProof -> Maybe IotaProof
reflectProofByProof proof (FApp funct [lhs, rhs])
    | funct == eqProof =
        substituteProofTerm lhs rhs proof
reflectProofByProof _ _ = error "Only Eq relation supported"

substituteProofTerm :: IotaProof -> IotaProof -> IotaProof -> Maybe IotaProof
substituteProofTerm source target proof
    | proof == source = Just target
substituteProofTerm source target (FApp funct args) =
    let maybeFunct = substituteProofTerm source target funct
        maybeArgs = map (substituteProofTerm source target) args
     in if any isJustProof (maybeFunct : maybeArgs)
            then
                Just
                    ( FApp
                        (fromMaybe funct maybeFunct)
                        (zipWith (`maybe` id) args maybeArgs)
                    )
            else Nothing
substituteProofTerm _ _ _ = Nothing

reverseEqProof :: IotaProof -> IotaProof
reverseEqProof (FApp funct [lhs, rhs])
    | funct == eqProof = FApp eqProof [rhs, lhs]
reverseEqProof _ = error "Only Eq relation supported"

mapMaybeProof :: (a -> Maybe b) -> [a] -> [b]
mapMaybeProof _ [] = []
mapMaybeProof f (x : xs) =
    case f x of
        Just y -> y : mapMaybeProof f xs
        Nothing -> mapMaybeProof f xs

isJustProof :: Maybe a -> Bool
isJustProof Just{} = True
isJustProof Nothing = False
