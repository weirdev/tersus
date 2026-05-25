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
    | EngineEqToLtPlus1 Iota Iota Iota
    | EngineEqToGtZero Iota
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
applyRewrite evalBuiltin (EngineEqToLtPlus1 iota resultIota oneIota) context =
    Ok (deriveEqToLtPlus1 evalBuiltin iota resultIota oneIota context)
applyRewrite _ (EngineEqToGtZero iota) context =
    deriveEqToGtZero iota context

deriveRefl :: ProofContext -> ProofContext
deriveRefl context@(ProofContext facts) =
    let eqFacts = equalityFacts facts
        reversedEqFacts = map reverseEqProof eqFacts
        derivedFacts = reflectProofsByProofs facts (eqFacts ++ reversedEqFacts)
     in insertProofs derivedFacts context

deriveEqToLtPlus1 :: BuiltinEvaluator -> Iota -> Iota -> Iota -> ProofContext -> ProofContext
deriveEqToLtPlus1 evalBuiltin iota resultIota oneIota context =
    let newFacts =
            [ FApp (CTerm (builtinFunct (Rel Lt))) [ATerm iota, ATerm resultIota]
            , FApp eqProof [ATerm resultIota, FApp (CTerm (builtinFunct Plus)) [ATerm iota, ATerm oneIota]]
            , FApp eqProof [ATerm oneIota, CTerm $ VInt 1]
            ]
        withNewFacts = insertProofs newFacts context
        withEvaledFacts = insertProofs (evalIota evalBuiltin resultIota withNewFacts) withNewFacts
     in deriveRefl withEvaledFacts

deriveEqToGtZero :: Iota -> ProofContext -> Result ProofContext String
deriveEqToGtZero iota context =
    case validateGtZero iota context of
        Ok () ->
            let gtZeroProof = FApp (CTerm (builtinFunct (Rel Gt))) [ATerm iota, CTerm (VInt 0)]
                withGtZeroProof = insertProofs [gtZeroProof] context
             in Ok (deriveRefl withGtZeroProof)
        Error e -> Error e

validateGtZero :: Iota -> ProofContext -> Result () String
validateGtZero iota context =
    case concreteValueOfIota iota context of
        Nothing ->
            if entails (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm iota, CTerm (VInt 0)]) context
                then Ok ()
                else Error "Iota lacks concrete definition and no equivalent proof exists"
        Just (VInt num) ->
            if num > 0
                then Ok ()
                else Error "Iota is not greater than 0"
        Just _ -> Error "Iota is not an int"

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
            case collectIotaTerms args of
                Just iotas ->
                    case iotasToValues iotas context of
                        Just values ->
                            case evalBuiltin funct values of
                                Ok val -> [FApp eqFunct [ATerm iota, CTerm val]]
                                Error _ -> []
                        Nothing -> []
                Nothing -> []
evalProof _ _ _ = []

collectIotaTerms :: [IotaProof] -> Maybe [Iota]
collectIotaTerms [] = Just []
collectIotaTerms (ATerm iota : proofs) =
    case collectIotaTerms proofs of
        Just iotas -> Just (iota : iotas)
        Nothing -> Nothing
collectIotaTerms _ = Nothing

iotasToValues :: [Iota] -> ProofContext -> Maybe [Value]
iotasToValues [] _ = Just []
iotasToValues (iota : iotas) context =
    case concreteValueOfIota iota context of
        Just value ->
            case iotasToValues iotas context of
                Just values -> Just (value : values)
                Nothing -> Nothing
        Nothing -> Nothing

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

equivalentTermsInclusive :: Int -> ProofContext -> IotaProof -> [IotaProof]
equivalentTermsInclusive depth context proof =
    proof : equivalentTerms depth context proof

equivalentTerms :: Int -> ProofContext -> IotaProof -> [IotaProof]
equivalentTerms 0 _ _ = []
equivalentTerms depth context proof =
    let nextProofs = firstDegreeEquivalentTerms context proof
     in nub (nextProofs ++ concatMap (equivalentTerms (depth - 1) context) nextProofs)

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
