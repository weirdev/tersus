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
    , entailsAll
    , applyRewrite
    , deriveRefl
    , reflectProofsByProofs
    ) where

import qualified Data.IntMap.Strict as IntMap
import Data.List (foldl', mapAccumL, nub)
import qualified Data.Map.Strict as Map
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
    | EngineCheckRel IotaProof
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
entails goal context = and (entailsAll [goal] context)

-- Which of the goals the context entails, sharing one congruence closure between them.
entailsAll :: [IotaProof] -> ProofContext -> [Bool]
entailsAll goals (ProofContext facts) =
    let (table1, factIds) = internAll emptyTable facts
        (table2, goalIds) = internAll table1 goals
        (table3a, trueId) = internTerm table2 (CTerm (VBool True))
        (table3, zeroId) = internTerm table3a (CTerm (VInt 0))
        equalities =
            concat
                [ (factId, trueId) : [(idOf table3 lhs, idOf table3 rhs) | FApp funct [lhs, rhs] <- [fact], funct == eqProof]
                | (fact, factId) <- zip facts factIds
                ]
        classes = congruenceClosure (tableApps table3) equalities
        sameClass a b = rep classes a == rep classes b
        arithmetic = arithmeticEdges table3 classes trueId zeroId
        entailed goal goalId =
            sameClass goalId trueId
                || or [sameClass (idOf table3 lhs) (idOf table3 rhs) | FApp funct [lhs, rhs] <- [goal], funct == eqProof]
                || or
                    [ arithmeticEntails arithmetic rel (rep classes (idOf table3 lhs)) (rep classes (idOf table3 rhs))
                    | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) [lhs, rhs] <- [goal]
                    ]
     in zipWith entailed goals goalIds

-- Congruence closure
--
-- Every term and subterm gets a number, and two numbers are in one class when the facts force
-- the terms to be equal. An equality joins its two sides, and two terms built from the same
-- function on equal arguments are joined too. So size(s0) + 1 is equal to l0 + 1 once
-- s0 = k0 and size(k0) = l0, although no fact was ever rewritten to say so (which is what
-- `rewrite refl` does, at the cost of a copy of every fact). A relation that is a fact is
-- equal to true, so a goal is entailed when its term is in the class of true. An equality
-- goal also holds when both of its sides are in one class.

data TermKey = KIota Iota | KConst Int | KApp Int [Int] deriving (Eq, Ord)

data TermTable = TermTable
    { tableKeys :: Map.Map TermKey Int
    , tableConsts :: [(Value, Int)]
    , tableApps :: [(Int, (Int, [Int]))] -- applications: term, function term, argument terms
    }

emptyTable :: TermTable
emptyTable = TermTable Map.empty [] []

internAll :: TermTable -> [IotaProof] -> (TermTable, [Int])
internAll = mapAccumL internTerm

internTerm :: TermTable -> IotaProof -> (TermTable, Int)
internTerm table (ATerm iota) = internKey table (KIota iota)
internTerm table (CTerm value) =
    case lookup value (tableConsts table) of
        Just constId -> internKey table (KConst constId)
        Nothing ->
            let constId = length (tableConsts table)
             in internKey table{tableConsts = (value, constId) : tableConsts table} (KConst constId)
internTerm table (FApp funct args) =
    let (table1, functId) = internTerm table funct
        (table2, argIds) = internAll table1 args
        key = KApp functId argIds
        (table3, termId) = internKey table2 key
     in if Map.member key (tableKeys table2)
            then (table3, termId)
            else (table3{tableApps = (termId, (functId, argIds)) : tableApps table3}, termId)

internKey :: TermTable -> TermKey -> (TermTable, Int)
internKey table key =
    case Map.lookup key (tableKeys table) of
        Just termId -> (table, termId)
        Nothing ->
            let termId = Map.size (tableKeys table)
             in (table{tableKeys = Map.insert key termId (tableKeys table)}, termId)

-- The number of a term that is already in the table
idOf :: TermTable -> IotaProof -> Int
idOf table term = snd (internTerm table term)

-- Maps term numbers to their class representative (a number missing from the map is its own)
congruenceClosure :: [(Int, (Int, [Int]))] -> [(Int, Int)] -> IntMap.IntMap Int
congruenceClosure apps equalities = settle (foldl' unionClasses IntMap.empty equalities)
  where
    settle classes =
        let flat = IntMap.map (findClass classes) classes
            bySignature = Map.fromListWith (++) [((rep flat functId, map (rep flat) argIds), [termId]) | (termId, (functId, argIds)) <- apps]
            merges = [(a, b) | (a : rest) <- Map.elems bySignature, b <- rest, rep flat a /= rep flat b]
         in if null merges then flat else settle (foldl' unionClasses flat merges)

rep :: IntMap.IntMap Int -> Int -> Int
rep classes x = IntMap.findWithDefault x x classes

findClass :: IntMap.IntMap Int -> Int -> Int
findClass classes x =
    case IntMap.lookup x classes of
        Just parent | parent /= x -> findClass classes parent
        _ -> x

unionClasses :: IntMap.IntMap Int -> (Int, Int) -> IntMap.IntMap Int
unionClasses classes (a, b) =
    let ra = findClass classes a
        rb = findClass classes b
     in if ra == rb then classes else IntMap.insert ra rb classes

-- Integer arithmetic
--
-- Integer relations are decided by difference constraints x - y <= c between classes of the
-- congruence closure, the way a shortest path problem is: an edge from y to x of weight c says
-- x - y <= c, and a goal x - y <= k holds when the shortest path from y to x weighs at most k.
-- The constraints come from
--   * the relation facts (x < y is x - y <= -1, and so on),
--   * x + c and x - c where c is a class with a known integer value (t = x + c is t - x = c),
--   * a class with a known integer value n (it differs from 0 by n), and
--   * size(l) >= 0.
-- So s = 3 gives s > 0, and i = j + 1 with i < n gives j + 1 < n, without a rewrite rule.
-- A negative cycle means the facts contradict each other, and then every relation is entailed.

type Edge = (Int, Int, Integer)

newtype Arithmetic = Arithmetic [Edge]

arithmeticEdges :: TermTable -> IntMap.IntMap Int -> Int -> Int -> Arithmetic
arithmeticEdges table classes trueId zeroId =
    let node = rep classes
        constTerms = [(Map.lookup (KConst constId) (tableKeys table), value) | (value, constId) <- tableConsts table]
        builtinOfClass = Map.fromList [(node termId, funct) | (Just termId, VFunct _ _ _ (BuiltinFunct funct) _) <- constTerms]
        intOfClass = Map.fromList [(node termId, n) | (Just termId, VInt n) <- constTerms]
        diff t a n = [(node a, node t, n), (node t, node a, negate n)]
        relEdges rel l r =
            case rel of
                Lt -> [(node r, node l, -1)]
                LtEq -> [(node r, node l, 0)]
                Gt -> [(node l, node r, -1)]
                GtEq -> [(node l, node r, 0)]
                Eq -> [(node r, node l, 0), (node l, node r, 0)]
                NotEq -> []
        appEdges t functId args =
            case (Map.lookup (node functId) builtinOfClass, args) of
                (Just Plus, [a, b])
                    | Just n <- Map.lookup (node b) intOfClass -> diff t a n
                    | Just n <- Map.lookup (node a) intOfClass -> diff t b n
                (Just Minus, [a, b])
                    | Just n <- Map.lookup (node b) intOfClass -> diff t a (negate n)
                (Just Size, [_]) -> [(node t, node zeroId, 0)]
                (Just (Rel rel), [l, r]) | node t == node trueId -> relEdges rel l r
                _ -> []
        constEdges = concat [diff termId zeroId n | (termId, n) <- Map.toList intOfClass]
     in Arithmetic (constEdges ++ concat [appEdges t functId args | (t, (functId, args)) <- tableApps table])

-- Whether lhs rel rhs follows from the constraints, for the class representatives lhs and rhs
arithmeticEntails :: Arithmetic -> Rel -> Int -> Int -> Bool
arithmeticEntails (Arithmetic edges) rel lhs rhs =
    case rel of
        Lt -> bound rhs lhs (-1)
        LtEq -> bound rhs lhs 0
        Gt -> bound lhs rhs (-1)
        GtEq -> bound lhs rhs 0
        Eq -> bound rhs lhs 0 && bound lhs rhs 0
        NotEq -> bound rhs lhs (-1) || bound lhs rhs (-1)
  where
    -- Whether the shortest path from source to target weighs at most k
    bound source target k =
        case shortestPaths edges source of
            Nothing -> True
            Just dist -> maybe (source == target && 0 <= k) (<= k) (Map.lookup target dist)

-- Bellman-Ford from one node; Nothing when a negative cycle is reachable from it
shortestPaths :: [Edge] -> Int -> Maybe (Map.Map Int Integer)
shortestPaths edges source = go (length edges + 1) (Map.singleton source 0)
  where
    go :: Int -> Map.Map Int Integer -> Maybe (Map.Map Int Integer)
    go rounds dist =
        let dist' = foldl' relax dist edges
         in if dist' == dist
                then Just dist
                else if rounds <= 0 then Nothing else go (rounds - 1) dist'
    relax dist (from, to, weight) =
        case Map.lookup from dist of
            Nothing -> dist
            Just d ->
                case Map.lookup to dist of
                    Just current | current <= d + weight -> dist
                    _ -> Map.insert to (d + weight) dist

applyRewrite :: BuiltinEvaluator -> EngineRewriteRule -> ProofContext -> Result ProofContext String
applyRewrite _ EngineRefl context = Ok (deriveRefl context)
applyRewrite evalBuiltin (EngineEval iota) context =
    Ok (insertProofs (evalIota evalBuiltin iota context) context)
applyRewrite evalBuiltin EngineEvalAll context =
    Ok (insertProofs (evalAll evalBuiltin context) context)
applyRewrite evalBuiltin (EngineCheckGtZero proof) context =
    checkGtZero evalBuiltin proof context
applyRewrite evalBuiltin (EngineCheckRel proof) context =
    checkRel evalBuiltin proof context

-- Succeeds, adding the relation as a fact, when it is already entailed or when both sides
-- have concrete values and the relation holds between them. Fails otherwise.
checkRel :: BuiltinEvaluator -> IotaProof -> ProofContext -> Result ProofContext String
checkRel evalBuiltin proof@(FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) [lhs, rhs]) context =
    if entails proof context
        then Ok (insertProofs [proof] context)
        else case (evalProofTerm evalBuiltin lhs context, evalProofTerm evalBuiltin rhs context) of
            (Just l, Just r) ->
                case evalBuiltin (Rel rel) [l, r] of
                    Ok (VBool True) -> Ok (insertProofs [proof] context)
                    Ok _ -> Error "Relation does not hold"
                    Error e -> Error e
            _ -> Error "Relation lacks a proof and its terms lack concrete definitions"
checkRel _ _ _ = Error "checkRel requires a relation such as x < y"

checkGtZero :: BuiltinEvaluator -> IotaProof -> ProofContext -> Result ProofContext String
checkGtZero evalBuiltin proof context =
    let gtZeroProof = FApp (CTerm (builtinFunct (Rel Gt))) [proof, CTerm (VInt 0)]
     in if entails gtZeroProof context
            then Ok (insertProofs [gtZeroProof] context)
            else case evalProofTerm evalBuiltin proof context of
                Just (VInt num) | num > 0 -> Ok (insertProofs [gtZeroProof] context)
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

isJustProof :: Maybe a -> Bool
isJustProof Just{} = True
isJustProof Nothing = False
