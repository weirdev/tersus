module ProofEngine
    ( BuiltinEvaluator
    , ProofContext
    , EngineRewriteRule (..)
    , emptyProofContext
    , proofContextFromFacts
    , proofContextFromCache
    , emptyFactCache
    , factCacheAdd
    , proofContextFacts
    , insertProofs
    , proofContextDelta
    , entails
    , entailsAll
    , constantValues
    , entailsDirect
    , applyRewrite
    , deriveRefl
    , reflectProofsByProofs
    ) where

import qualified Data.IntMap.Strict as IntMap
import Data.Containers.ListUtils (nubOrd, nubOrdOn)
import Data.List (foldl', mapAccumL)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)

import Linear
import StdLib
import TersusTypes
import Utils

type BuiltinEvaluator = BuiltinFunct -> [Value] -> Result Value String

-- The facts, and the solver of them when it is known (see FactCache). Two contexts are equal when their facts are.
data ProofContext = ProofContext [IotaProof] (Maybe FactCache)

instance Show ProofContext where
    show (ProofContext facts _) = "ProofContext " ++ show facts

instance Eq ProofContext where
    ProofContext facts _ == ProofContext facts' _ = facts == facts'

data EngineRewriteRule
    = EngineRefl
    | EngineEval Iota
    | EngineEvalAll
    | EngineCheckGtZero IotaProof
    | EngineCheckRel IotaProof
    deriving (Show, Eq)

emptyProofContext :: ProofContext
emptyProofContext = ProofContext [] Nothing

proofContextFromFacts :: [IotaProof] -> ProofContext
proofContextFromFacts facts = ProofContext (nubOrd facts) Nothing

-- The context of some facts that has a cache's solver when everything the cache has is among the facts, and
-- the facts it lacks are added to it. A cache that holds a fact the context no longer has is not used.
proofContextFromCache :: Maybe FactCache -> [IotaProof] -> ProofContext
proofContextFromCache Nothing facts = proofContextFromFacts facts
proofContextFromCache (Just cache) facts =
    let factSet = Set.fromList facts
     in if cacheOriginals cache `Set.isSubsetOf` factSet
            then ProofContext (nubOrd facts) (Just (factCacheAdd cache (Set.toList (factSet `Set.difference` cacheOriginals cache))))
            else proofContextFromFacts facts

emptyFactCache :: FactCache
emptyFactCache = FactCache Set.empty [] Set.empty newSolver

-- The cache with more facts. The solver is built when something asks for it.
factCacheAdd :: FactCache -> [IotaProof] -> FactCache
factCacheAdd cache new =
    let fresh = filter (`Set.notMember` cacheFactSet cache) (nubOrd (map lightProof new))
     in FactCache
            (foldr Set.insert (cacheOriginals cache) new)
            (cacheFacts cache ++ fresh)
            (foldr Set.insert (cacheFactSet cache) fresh)
            (if null fresh then cacheSolver cache else solverAddFacts (cacheSolver cache) fresh)

proofContextFacts :: ProofContext -> [IotaProof]
proofContextFacts (ProofContext facts _) = facts

insertProofs :: [IotaProof] -> ProofContext -> ProofContext
insertProofs newFacts (ProofContext facts _) = ProofContext (nubOrd (facts ++ newFacts)) Nothing

proofContextDelta :: ProofContext -> ProofContext -> [IotaProof]
proofContextDelta (ProofContext oldFacts _) (ProofContext newFacts _) =
    filter (`notElem` oldFacts) newFacts

entails :: IotaProof -> ProofContext -> Bool
entails goal context = and (entailsAll [goal] context)

-- Which of the goals the context entails, sharing one congruence closure between them.
-- The value each term is known to have: the facts equate it to a constant, or to a builtin applied to
-- terms that have constants
constantValues :: [IotaProof] -> ProofContext -> [Maybe Value]
constantValues terms (ProofContext facts cache) =
    let start = case cache of
            Just c -> cacheSolver c
            Nothing -> satSolver (initialSaturation facts)
        (solver, ids) = solverGoals start (map lightProof terms)
        classes = closureFlat (solverClosure solver)
        constants = constantsByClass (solverTable solver) classes
     in [case Map.lookup (rep classes termId) constants of Just (value : _) -> Just value; _ -> Nothing | termId <- ids]

-- Whether each goal follows from the facts by congruence and arithmetic alone: no forall is instantiated and no case is
-- split, so it is cheap, and a goal that needs them is not entailed
entailsDirect :: [IotaProof] -> ProofContext -> [Bool]
entailsDirect goals (ProofContext facts cache) =
    let start = case cache of
            Just c -> cacheSolver c
            Nothing -> satSolver (initialSaturation facts)
        (_, _, flags, _) = querySolver start (map lightProof goals)
     in flags

entailsAll :: [IotaProof] -> ProofContext -> [Bool]
entailsAll goals context = fst (entailsBlocked goals context)

-- Also the guards that kept an instance of a forall from being used: each is the one condition missing
-- for an instance whose other guards hold, so a case split on it is what may let the proof go on.
entailsBlocked :: [IotaProof] -> ProofContext -> ([Bool], [IotaProof])
entailsBlocked goals (ProofContext facts cache) =
    let start = case cache of
            Just c -> Saturation (cacheFacts c) (cacheFactSet c) Map.empty (cacheSolver c) Set.empty
            Nothing -> initialSaturation facts
        (flags, blocked, _) = entailsFrom goals start
     in (flags, blocked)

-- The facts a proof has reached by instantiating foralls, and the generation of each term an instance added (see saturate). A
-- case split starts from the saturation of the case before it, since facts only grow.
data Saturation = Saturation
    { satFacts :: [IotaProof]
    , satFactSet :: Set.Set IotaProof
    , satBirths :: Map.Map IotaProof Int
    , satSolver :: Solver
    , satDone :: Set.Set (Int, IotaProof) -- the foralls (by place in the facts) already instantiated at an index term
    }

-- The list builtins carry their contracts, which are large, and every fact and goal is compared with the
-- others many times. They are replaced by plain symbols up front.
initialSaturation :: [IotaProof] -> Saturation
initialSaturation facts =
    let lightFacts = map lightProof facts
     in Saturation lightFacts (Set.fromList lightFacts) Map.empty (solverAddFacts newSolver lightFacts) Set.empty

-- Adds facts that hold in a case
extendSaturation :: Saturation -> [IotaProof] -> Saturation
extendSaturation (Saturation facts factSet births solver done) new =
    let fresh = filter (`Set.notMember` factSet) (nubOrd new)
     in Saturation
            (facts ++ fresh)
            (foldr Set.insert factSet fresh)
            births
            (if null fresh then solver else solverAddFacts solver fresh)
            done

entailsFrom :: [IotaProof] -> Saturation -> ([Bool], [IotaProof], Saturation)
entailsFrom originalGoals startSaturation =
    let (flags, blocked, saturated) = saturateWith (0 :: Int) startSaturation
     in (zipWith provedAsForall goals flags, blocked, saturated)
  where
    goals = map lightProof originalGoals
    -- A forall goal that is not already a known fact is proved for an arbitrary index
    provedAsForall goal entailed = entailed || proveForall goal
    -- Takes a fresh index that meets the guards, and asks for the body at that index. The name
    -- cannot be written in a program, so no fact is about it. A range with no index in it has
    -- guards that contradict each other, which entail everything.
    --
    -- If the body does not follow directly, the proof splits cases. First on the guards that kept a
    -- forall from being used, which is where the facts say `j != p` or `j < size(l)` and the new index is
    -- not yet known to meet them (`set` leaves p out, `push` leaves the new element out). Each guard
    -- is split into the ways it can go, and the body must follow in each; a split can leave another
    -- guard blocked, so it repeats within a budget. Failing that, the index is compared with an index
    -- the program reads: below it, equal to it, and above it.
    proveForall (Forall index guards body) =
        let fresh = ATerm (Iota ("$" ++ index))
            guardFacts = map (substituteIndex index fresh) guards
            bodyGoal = substituteIndex index fresh body
            sat0 = extendSaturation startSaturation guardFacts
            known = satFacts sat0
            holdsUnder extra = let (flags, _, _) = entailsFrom [bodyGoal] (extendSaturation sat0 extra) in and flags
            -- Each entailment costs one unit of budget
            guided budget depth sat extra
                | budget <= 0 = (False, 0 :: Int)
                | and flags = (True, budget - 1)
                | depth <= 0 = (False, budget - 1)
                | otherwise = anyGuard (budget - 1) (take maxSplitGuards (filter notSplit (nubOrd blocked)))
              where
                notSplit (FApp _ [a, b]) = not (or [sameTerms x y a b | FApp _ [x, y] <- extra])
                notSplit _ = False
                sameTerms x y p q = (x == p && y == q) || (x == q && y == p)
                (flags, blocked, saturated) = entailsFrom [bodyGoal] sat
                anyGuard remaining [] = (False, remaining)
                anyGuard remaining (guard : rest) =
                    case guardCases guard of
                        [] -> anyGuard remaining rest
                        cases ->
                            let (ok, remaining') = allBranches remaining cases
                             in if ok then (True, remaining') else if remaining' <= 0 then (False, 0) else anyGuard remaining' rest
                allBranches remaining [] = (True, remaining)
                allBranches remaining (c : cs) =
                    let (ok, remaining') = guided remaining (depth - 1) (extendSaturation saturated c) (extra ++ c)
                     in if ok then allBranches remaining' cs else (False, remaining')
            comparisons t =
                [ [FApp (CTerm (builtinFunct (Rel Lt))) [fresh, t]]
                , [FApp eqProof [fresh, t]]
                , [FApp (CTerm (builtinFunct (Rel Gt))) [fresh, t]]
                ]
            reads = take maxSplitIndexes (splitIndexes known fresh bodyGoal)
            (guidedProved, budgetLeft) = guided maxSplitAttempts maxSplitDepth sat0 []
         in guidedProved
                || any (all holdsUnder . comparisons) (take (budgetLeft `div` 3) reads)
    proveForall _ = False
    -- Facts that are foralls are instantiated, and the closure is rebuilt with the instances
    -- that hold, until no new instance appears or the rounds run out. Without a forall this is
    -- one closure.
    -- Each term has a generation: those of the facts and the goals are 0, and the terms an instance adds are one
    -- more than the index it was instantiated at. A forall is only instantiated at indexes of a low generation,
    -- so an agreement invariant such as get(l, get(l, i).next).prev = i, whose instance contains a new index
    -- to instantiate at, does not feed itself without end.
    saturateWith round saturation =
        let currentFacts = satFacts saturation
            factSet = satFactSet saturation
            births = satBirths saturation
            solver = satSolver saturation
            done = satDone saturation
            (table, classes, flags, quick) = querySolver solver goals
            generationOf t = Map.findWithDefault 0 t births
            instances = forallInstances ((<= maxIndexGeneration) . generationOf) table classes currentFacts factSet done
         in if null instances || and flags
                then (flags, [], saturation)
                else
                    let guardGoals = concatMap (\(guards, _, _, _) -> guards) instances
                        -- The guards are asked of the same classes when the table has their terms; otherwise the facts are
                        -- solved again with the guards as goals
                        quickGuards = map quick guardGoals
                        (guardTable, guardClasses, guardHolds)
                            | all (/= Nothing) quickGuards = (table, classes, zip guardGoals (map (== Just True) quickGuards))
                            | otherwise =
                                let (guardTable', guardClasses', guardFlags, _) = querySolver solver (goals ++ guardGoals)
                                 in (guardTable', guardClasses', zip guardGoals (drop (length goals) guardFlags))
                        holds g = Map.lookup g guardHoldsMap == Just True
                        guardHoldsMap = Map.fromList guardHolds
                        acceptedInstances = [(body, indexTerm, key) | (guards, body, indexTerm, key) <- instances, all holds guards]
                        accepted = [body | (body, _, _) <- acceptedInstances]
                        births' =
                            foldl
                                (\known (body, indexTerm, _) -> foldl (\m t -> if Map.member t m || isJust (lookupTerm table t) then m else Map.insert t (generationOf indexTerm + 1) m) known (subterms body))
                                births
                                acceptedInstances
                        -- (a term the table already has is of generation 0, or has the generation it was given then)
                        -- an instance with exactly one guard missing would be used if that guard held, unless the
                        -- guard compares two terms that are already equal
                        -- those at an index the goal reads with get come first: the splits that bear on the goal
                        missing = distinctGuards (relevantFirst [(g, indexTerm) | (guards, _, indexTerm, _) <- instances, [g] <- [filter (not . holds) guards], distinctSides guardTable guardClasses g])
                        -- guards about the same two classes of terms are one split, however the terms are written
                        distinctGuards = go Set.empty
                          where
                            go _ [] = []
                            go seen (g : rest) =
                                let key = guardKey g
                                 in if key `Set.member` seen then go seen rest else g : go (Set.insert key seen) rest
                        guardKey (FApp f [a, b]) = (f, min (classOfTerm a) (classOfTerm b), max (classOfTerm a) (classOfTerm b))
                        guardKey _ = (CTerm (VBool False), -1, -1)
                        classOfTerm t = rep guardClasses (idOf guardTable t)
                        goalIndexClasses = Set.fromList [rep guardClasses (idOf guardTable t) | t <- concatMap goalIndexes goals]
                        relevantFirst gs = [g | (g, t) <- gs, relevant t] ++ [g | (g, t) <- gs, not (relevant t)]
                        relevant t = rep guardClasses (idOf guardTable t) `Set.member` goalIndexClasses
                        distinctSides table' classes' (FApp _ [a, b]) = rep classes' (idOf table' a) /= rep classes' (idOf table' b)
                        distinctSides _ _ _ = True
                        next = (extendSaturation saturation accepted){satBirths = births', satDone = foldr (\(_, _, key) -> Set.insert key) done acceptedInstances}
                     in if null accepted || round >= maxInstantiationRounds
                            then (flags, missing, next)
                            else saturateWith (round + 1) next

-- The index terms of the get(L, t) a proof contains
goalIndexes :: IotaProof -> [IotaProof]
goalIndexes proof = [index | FApp (CTerm (VFunct _ _ _ (BuiltinFunct Get) _)) [_, index] <- subterms proof]

-- The indexes of the get(L, t) in the facts and the goal, one for each class of equal indexes, other
-- than the index itself. Only the first few are tried, to bound the work of a proof.
splitIndexes :: [IotaProof] -> IotaProof -> IotaProof -> [IotaProof]
splitIndexes facts fresh goal =
    let (table, classes, _) = solve facts [goal, fresh]
        getClasses = Map.keys (builtinsByClass table classes (== Get))
        indexIds =
            [ indexId
            | (_, (functId, [_, indexId])) <- tableApps table
            , rep classes functId `elem` getClasses
            , rep classes indexId /= rep classes (idOf table fresh)
            ]
        firstOfEachClass = Map.elems (Map.fromListWith (\_ old -> old) [(rep classes indexId, indexId) | indexId <- reverse indexIds])
     in take maxSplitIndexes (map (termOf table) firstOfEachClass)

maxSplitIndexes :: Int
maxSplitIndexes = 60

-- How deep the case splits on blocked guards go, how many guards one level tries, and how many
-- entailments one forall proof may spend on them
maxSplitDepth :: Int
maxSplitDepth = 10

maxSplitGuards :: Int
maxSplitGuards = 1

maxSplitAttempts :: Int
maxSplitAttempts = 600

-- The ways a guard can go. A guard that is a left-out index splits into holding or not, a range bound into
-- the three orders, which lets the case where they are equal join the two terms.
guardCases :: IotaProof -> [[IotaProof]]
guardCases (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) [a, b]) =
    case rel of
        NotEq -> [[FApp eqProof [a, b]], [FApp (CTerm (builtinFunct (Rel NotEq))) [a, b], FApp (CTerm (builtinFunct (Rel NotEq))) [b, a]]]
        _ ->
            [ [FApp (CTerm (builtinFunct (Rel Lt))) [a, b]]
            , [FApp eqProof [a, b]]
            , [FApp (CTerm (builtinFunct (Rel Gt))) [a, b]]
            ]
guardCases _ = []

-- The highest generation of an index a forall is instantiated at (see saturate)
maxIndexGeneration :: Int
maxIndexGeneration = 1

maxInstantiationRounds :: Int
maxInstantiationRounds = 5

-- Interns the facts and goals, builds the classes, and says which goals hold
solve :: [IotaProof] -> [IotaProof] -> (TermTable, IntMap.IntMap Int, [Bool])
solve givenFacts goals =
    let (table, classes, flags, _) = solveQuery givenFacts goals
     in (table, classes, flags)

-- As solve, and a way to ask about more relations without solving again: it answers for a relation whose sides are
-- terms the table already has, and says Nothing for any other goal
solveQuery :: [IotaProof] -> [IotaProof] -> (TermTable, IntMap.IntMap Int, [Bool], IotaProof -> Maybe Bool)
solveQuery givenFacts goals = querySolver (solverAddFacts newSolver givenFacts) goals

-- The classes of a solver's facts and the goals interned with them, which of the goals hold, and a quick query
querySolver :: Solver -> [IotaProof] -> (TermTable, IntMap.IntMap Int, [Bool], IotaProof -> Maybe Bool)
querySolver facts goals =
    let (solver, goalIds) = solverGoals facts goals
        table4 = solverTable solver
        classes = closureFlat (solverClosure solver)
        trueId = solverTrueId solver
        zeroId = solverZeroId solver
        sameClass a b = rep classes a == rep classes b
        arithmetic = arithmeticEdges table4 classes trueId zeroId
        -- shared by the questions asked
        valuesByClass = constantsByClass table4 classes
        namesByClass = constructorNames table4 classes
        distinct = provablyDistinct classes valuesByClass namesByClass
        clash = constructorClash table4 classes valuesByClass namesByClass trueId
        entailed goal goalId =
            clash
                || sameClass goalId trueId
                || or [sameClass (idOf table4 lhs) (idOf table4 rhs) | FApp funct [lhs, rhs] <- [goal], funct == eqProof]
                || or
                    [ distinct (idOf table4 lhs) (idOf table4 rhs)
                    | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _)) [lhs, rhs] <- [goal]
                    ]
                || or
                    [ arithmeticEntails arithmetic rel (rep classes (idOf table4 lhs)) (rep classes (idOf table4 rhs))
                    | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) [lhs, rhs] <- [goal]
                    ]
                || or
                    [ differenceEntails differences arithmetic zeroClass rel (rep classes (idOf table4 lhs)) (rep classes (idOf table4 rhs))
                    | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) [lhs, rhs] <- [goal]
                    ]
                || or
                    [ linearGoal rel (idOf table4 lhs) (idOf table4 rhs)
                    | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) [lhs, rhs] <- [goal]
                    ]
                || or
                    [ partOf table4 classes (idOf table4 lhs) (idOf table4 rhs)
                    | FApp (CTerm (VFunct _ _ _ (BuiltinFunct Within) _)) [lhs, rhs] <- [goal]
                    ]
        differences = differencesByClass table4 classes
        linear = linearSystem table4 classes trueId (\x -> arithmeticEntails arithmetic Gt (rep classes x) zeroClass) (\x -> arithmeticEntails arithmetic Lt (rep classes x) zeroClass)
        -- (the system is looked at as a whole once, in case the facts contradict each other somewhere the goal does not reach)
        linearContradiction = infeasible linear
        linearGoal rel l r = not (null linear) && (linearEntails linear rel (rep classes l) (rep classes r) || linearContradiction)
        zeroClass = rep classes zeroId
        -- The applications by the classes of their function and arguments, to find a relation that is a fact
        -- under congruence
        appsBySignature = Map.fromListWith (++) [((rep classes functId, map (rep classes) argIds), [termId]) | (termId, (functId, argIds)) <- tableApps table4]
        quick (FApp funct [lhs, rhs]) =
            case (lookupTerm table4 funct, lookupTerm table4 lhs, lookupTerm table4 rhs) of
                (functId, Just l, Just r) ->
                    Just
                        ( clash
                            || or [sameClass t trueId | Just f <- [functId], t <- Map.findWithDefault [] (rep classes f, [rep classes l, rep classes r]) appsBySignature]
                            || or [sameClass l r | funct == eqProof]
                            || or [distinct l r | CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _) <- [funct]]
                            || or [arithmeticEntails arithmetic rel (rep classes l) (rep classes r) | CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _) <- [funct]]
                            || or [differenceEntails differences arithmetic zeroClass rel (rep classes l) (rep classes r) | CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _) <- [funct]]
                            || or [linearGoal rel l r | CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _) <- [funct]]
                        )
                _ -> Nothing
        quick _ = Nothing
     in (table4, classes, zipWith entailed goals goalIds, quick)

newSolver :: Solver
newSolver =
    let (table1, trueId) = internTerm emptyTable (CTerm (VBool True))
        (table2, zeroId) = internTerm table1 (CTerm (VInt 0))
     in Solver table2 emptyClosure trueId zeroId 0 0

-- Gives the closure the terms interned since it last had them
syncClosure :: Solver -> Solver
syncClosure solver =
    let table = solverTable solver
        newApps = take (tableAppCount table - solverApps solver) (tableApps table)
        newForalls = take (tableForallCount table - solverForalls solver) (tableForalls table)
        shapes =
            reverse [(termId, AppShape functId argIds) | (termId, (functId, argIds)) <- newApps]
                ++ reverse [(termId, ForallShape index guardIds bodyId) | (termId, (index, guardIds, bodyId)) <- newForalls]
     in solver{solverClosure = closureAdd (solverClosure solver) shapes, solverApps = tableAppCount table, solverForalls = tableForallCount table}

solverIntern :: Solver -> [IotaProof] -> (Solver, [Int])
solverIntern solver terms =
    let (table, ids) = internAll (solverTable solver) terms
     in (syncClosure solver{solverTable = table}, ids)

-- Facts are equal to true, and the two sides of an equality are equal. a != b is also b != a.
solverAddFacts :: Solver -> [IotaProof] -> Solver
solverAddFacts solver givenFacts =
    let facts = givenFacts ++ [FApp funct [b, a] | FApp funct@(CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _)) [a, b] <- givenFacts]
        (solver1, factIds) = solverIntern solver facts
        table = solverTable solver1
        equalities =
            concat
                [ (factId, solverTrueId solver1) : [(idOf table lhs, idOf table rhs) | FApp funct [lhs, rhs] <- [fact], funct == eqProof]
                | (fact, factId) <- zip facts factIds
                ]
     in settleSolver 0 solver1{solverClosure = closureJoin (solverClosure solver1) equalities}

-- Interns goals into a solver, so that they take part in the closure
solverGoals :: Solver -> [IotaProof] -> (Solver, [Int])
solverGoals solver goals =
    let (solver1, goalIds) = solverIntern solver goals
     in (settleSolver 0 solver1, goalIds)

-- The number of a term, when the table already has it
lookupTerm :: TermTable -> IotaProof -> Maybe Int
lookupTerm table (ATerm iota) = Map.lookup (KIota iota) (tableKeys table)
lookupTerm table (BVar index) = Map.lookup (KBound index) (tableKeys table)
lookupTerm table (CTerm value) =
    let found =
            case constKey value of
                Just key -> Map.lookup key (tableConstIds table)
                Nothing -> lookup value (tableOtherConsts table)
     in found >>= \constId -> Map.lookup (KConst constId) (tableKeys table)
lookupTerm table (FApp funct args) = do
    functId <- lookupTerm table funct
    argIds <- mapM (lookupTerm table) args
    Map.lookup (KApp functId argIds) (tableKeys table)
lookupTerm _ (Forall _ _ _) = Nothing

-- Makes every builtin applied to concrete values equal to its value. Evaluating gives new constants, which can make
-- more applications concrete, so it repeats.
settleSolver :: Int -> Solver -> Solver
settleSolver round solver =
    let table = solverTable solver
        classes = closureFlat (solverClosure solver)
        values = evaluatedTerms table classes
        links = [link | link@(term, field) <- selections table classes, rep classes term /= rep classes field]
     in if (null values && null links) || round >= maxEvaluationRounds
            then solver
            else
                let (solver1, valueIds) = solverIntern solver [CTerm value | (_, value) <- values]
                 in settleSolver (round + 1) solver1{solverClosure = closureJoin (solverClosure solver1) (zip (map fst values) valueIds ++ links)}

maxEvaluationRounds :: Int
maxEvaluationRounds = 8

-- Struct fields
--
-- Reading a field of a struct built by a constructor is the field's value, however the struct got
-- its name: field(Name(a, b), f) = a. Together with congruence this makes two constructor applications
-- in one class agree field by field, and it needs no rule for an update, which is a constructor
-- applied to the old struct's fields. A struct that is a known value is handled by evaluation.

-- The field a builtin reads from a struct, however the program wrote it
fieldRead :: BuiltinFunct -> Maybe Variable
fieldRead (Field _ field) = Just field
fieldRead (Project _ field) = Just field
fieldRead _ = Nothing

selections :: TermTable -> IntMap.IntMap Int -> [(Int, Int)]
selections table classes = reads ++ injectivity ++ casts
  where
    -- a cast changes how a value is read, not the value
    casts =
        [ (termId, argId)
        | (termId, (functId, [argId])) <- tableApps table
        , Just (Cast _) <- [Map.lookup (rep classes functId) builtinOfClass]
        ]
    reads =
        [ (termId, arg)
        | (termId, (functId, [structId])) <- tableApps table
        , Just funct <- [Map.lookup (rep classes functId) builtinOfClass]
        , Just field <- [fieldRead funct]
        , (_, fields, args) <- Map.findWithDefault [] (rep classes structId) constructions
        , (name, arg) <- zip fields args
        , name == field
        ]
    -- Two constructions in one class are of equal structs, so their fields are equal
    injectivity =
        [ link
        | group <- Map.elems constructions
        , (name, fields, args) : others <- [group]
        , (name', fields', args') <- others
        , name == name'
        , link <- zip args args'
        ]
    builtinOfClass = builtinsByClass table classes (const True)
    constructions =
        Map.fromListWith
            (++)
            [ (rep classes termId, [(name, fields, args)])
            | (termId, (functId, args)) <- tableApps table
            , Just (Ctor name fields) <- [Map.lookup (rep classes functId) builtinOfClass]
            , length fields == length args
            ]

-- Whether the first term is a part of the second: a field of it, or a field of a field. It goes by the field reads
-- among the terms, so a value read from the second term and then bound to a name is found.
partOf :: TermTable -> IntMap.IntMap Int -> Int -> Int -> Bool
partOf table classes inner outer =
    rep classes inner /= rep classes outer && Set.member (rep classes inner) (reached Set.empty [rep classes outer])
  where
    builtinOfClass = builtinsByClass table classes (const True)
    children =
        Map.fromListWith
            (++)
            [ (rep classes structId, [rep classes termId])
            | (termId, (functId, [structId])) <- tableApps table
            , Just funct <- [Map.lookup (rep classes functId) builtinOfClass]
            , Just _ <- [fieldRead funct]
            ]
    reached seen [] = seen
    reached seen (next : rest) =
        let new = [child | child <- Map.findWithDefault [] next children, Set.notMember child seen]
         in reached (foldr Set.insert seen new) (new ++ rest)

-- Evaluation
--
-- A builtin applied to arguments that are known to be concrete values has that value, so
-- size([1, 2]) = 2 needs no `define` and `rewrite eval`. The term is joined to its value when
-- the closure is built.

evaluatedTerms :: TermTable -> IntMap.IntMap Int -> [(Int, Value)]
evaluatedTerms table classes = variantTests ++ evaluated
  where
    evaluated =
        [ (termId, value)
        | (termId, (functId, argIds)) <- tableApps table
        , Map.notMember (rep classes termId) concreteOfClass
        , Just funct <- [Map.lookup (rep classes functId) builtinOfClass]
        , Just args <- [mapM ((`Map.lookup` concreteOfClass) . rep classes) argIds]
        , Ok value <- [evalBuiltinFunct funct args]
        , concrete value
        ]
    -- Which variant a value is, when it is built by a constructor whose fields are not all known
    variantTests =
        [ (termId, VBool (variant `elem` built))
        | (termId, (functId, [argId])) <- tableApps table
        , Map.notMember (rep classes termId) concreteOfClass
        , Just (Is variant) <- [Map.lookup (rep classes functId) builtinOfClass]
        , built@(_ : _) <- [Map.findWithDefault [] (rep classes argId) constructed]
        ]
    constructed =
        Map.fromListWith
            (++)
            [ (rep classes termId, [name])
            | (termId, (functId, _)) <- tableApps table
            , Just (Ctor name _) <- [Map.lookup (rep classes functId) builtinOfClass]
            ]
    builtinOfClass = builtinsByClass table classes (const True)
    concreteOfClass = Map.map head (constantsByClass table classes)

concrete :: Value -> Bool
concrete (VInt _) = True
concrete (VList _) = True
concrete (VData _ _) = True
concrete (VBool _) = True
concrete _ = False

-- The concrete values equal to each class, once each
constantsByClass :: TermTable -> IntMap.IntMap Int -> Map.Map Int [Value]
constantsByClass table classes =
    Map.map nubOrd $
        Map.fromListWith
            (++)
            [ (rep classes termId, [value])
            | (value, constId) <- tableConsts table
            , concrete value
            , Just termId <- [Map.lookup (KConst constId) (tableKeys table)]
            ]

-- The constructors a class is built by: those applied in it and those of its known values
constructorNames :: TermTable -> IntMap.IntMap Int -> Map.Map Int [Name]
constructorNames table classes =
    Map.map nubOrd $
        Map.fromListWith
            (++)
            ( [ (rep classes termId, [name])
              | (termId, (functId, _)) <- tableApps table
              , Just (Ctor name _) <- [Map.lookup (rep classes functId) builtinOfClass]
              ]
                ++ [ (cls, [name])
                   | (cls, values) <- Map.toList (constantsByClass table classes)
                   , VData name _ <- values
                   ]
            )
  where
    builtinOfClass = builtinsByClass table classes (const True)

-- Two different values, or two different constructors, in one class cannot both be what it is equal to
constructorClash :: TermTable -> IntMap.IntMap Int -> Map.Map Int [Value] -> Map.Map Int [Name] -> Int -> Bool
constructorClash table classes values names trueId =
    any ((> 1) . length) (Map.elems values)
        || any ((> 1) . length) (Map.elems names)
        || any ((> 1) . length . nubOrd) (Map.elems variantsKnownToHold)
  where
    -- the variants a value has been said to be, as in `x is Opt::Some` assumed true
    variantsKnownToHold =
        Map.fromListWith
            (++)
            [ (rep classes argId, [variant])
            | (termId, (functId, [argId])) <- tableApps table
            , rep classes termId == rep classes trueId
            , Just (Is variant) <- [Map.lookup (rep classes functId) (builtinsByClass table classes (const True))]
            ]

-- Two classes that are known to differ: they are equal to different values, or built by different constructors
provablyDistinct :: IntMap.IntMap Int -> Map.Map Int [Value] -> Map.Map Int [Name] -> Int -> Int -> Bool
provablyDistinct classes values names a b =
    differ values || differ' names
  where
    differ values = case (Map.lookup (rep classes a) values, Map.lookup (rep classes b) values) of
        (Just (x : _), Just (y : _)) -> x /= y
        _ -> False
    differ' names = case (Map.lookup (rep classes a) names, Map.lookup (rep classes b) names) of
        (Just xs@(_ : _), Just ys@(_ : _)) -> all (`notElem` ys) xs
        _ -> False

-- Forall instances
--
-- A forall fact `forall j where guards: body` is used at the indexes where its body is about
-- an element: for every get(L, t) in the closure with L equal to the list of a get(L, j) in the
-- body, the index j is replaced by t. An instance is the instantiated guards, which must be
-- entailed, and the instantiated body, which then becomes a fact. A forall whose body has no
-- get(L, j) is never instantiated.

forallInstances :: (IotaProof -> Bool) -> TermTable -> IntMap.IntMap Int -> [IotaProof] -> Set.Set IotaProof -> Set.Set (Int, IotaProof) -> [([IotaProof], IotaProof, IotaProof, (Int, IotaProof))]
forallInstances eligible table classes facts known done =
    nubOrdOn
        (\(guards, instantiated, indexTerm, _) -> (guards, instantiated, indexTerm))
        [ (map (substituteIndex index indexTerm) guards, instantiated, indexTerm, key)
        | (place, Forall index guards body) <- zip [0 ..] facts
        , listTerm <- indexedLists index body
        , indexTerm <- getIndexesOf listTerm
        , let key = (place, indexTerm)
        , key `Set.notMember` done
        , let instantiated = substituteIndex index indexTerm body
        , instantiated `Set.notMember` known
        ]
  where
    getClasses = Map.keys (builtinsByClass table classes (== Get))
    termFor = termOf table
    -- The index terms t of the get(L', t) in the closure, by the class of L'
    getIndexes =
        Map.fromListWith
            (flip (++))
            [ (rep classes listId, [indexTerm])
            | (_, (functId, [listId, indexId])) <- tableApps table
            , rep classes functId `elem` getClasses
            , let indexTerm = termFor indexId
            , eligible indexTerm
            ]
    getIndexesOf listTerm = Map.findWithDefault [] (rep classes (idOf table listTerm)) getIndexes

-- The lists L of the get(L, index) in a proof, where L does not mention the index
indexedLists :: Variable -> IotaProof -> [IotaProof]
indexedLists index (FApp funct args) =
    [ listTerm
    | FApp (CTerm (VFunct _ _ _ (BuiltinFunct Get) _)) [listTerm, BVar bound] <- [FApp funct args]
    , bound == index
    , not (mentionsIndex index listTerm)
    ]
        ++ concatMap (indexedLists index) (funct : args)
indexedLists _ _ = []

mentionsIndex :: Variable -> IotaProof -> Bool
mentionsIndex index (BVar bound) = bound == index
mentionsIndex index (FApp funct args) = any (mentionsIndex index) (funct : args)
mentionsIndex _ _ = False

substituteIndex :: Variable -> IotaProof -> IotaProof -> IotaProof
substituteIndex index replacement (BVar bound) | bound == index = replacement
substituteIndex index replacement (FApp funct args) =
    FApp (substituteIndex index replacement funct) (map (substituteIndex index replacement) args)
substituteIndex _ _ other = other

-- The classes of the builtin functions satisfying the predicate, with which builtin each is
builtinsByClass :: TermTable -> IntMap.IntMap Int -> (BuiltinFunct -> Bool) -> Map.Map Int BuiltinFunct
builtinsByClass table classes wanted =
    Map.fromList
        [ (rep classes termId, funct)
        | (value, constId) <- tableConsts table
        , VFunct _ _ _ (BuiltinFunct funct) _ <- [value]
        , wanted funct
        , Just termId <- [Map.lookup (KConst constId) (tableKeys table)]
        ]

-- A proof for a term number of the table
termOf :: TermTable -> Int -> IotaProof
termOf table = build
  where
    keyOf = IntMap.fromList [(termId, key) | (key, termId) <- Map.toList (tableKeys table)]
    valueOf = IntMap.fromList [(constId, value) | (value, constId) <- tableConsts table]
    build termId =
        case IntMap.lookup termId keyOf of
            Just (KIota iota) -> ATerm iota
            Just (KConst constId) -> maybe (ATerm (Iota "?")) CTerm (IntMap.lookup constId valueOf)
            Just (KApp functId argIds) -> FApp (build functId) (map build argIds)
            Just (KBound index) -> BVar index
            Just (KForall index guardIds bodyId) -> Forall index (map build guardIds) (build bodyId)
            Nothing -> ATerm (Iota "?")

-- Congruence closure
--
-- Every term and subterm gets a number, and two numbers are in one class when the facts force
-- the terms to be equal. An equality joins its two sides, and two terms built from the same
-- function on equal arguments are joined too. So size(s0) + 1 is equal to l0 + 1 once
-- s0 = k0 and size(k0) = l0, although no fact was ever rewritten to say so (which is what
-- `rewrite refl` does, at the cost of a copy of every fact). A relation that is a fact is
-- equal to true, so a goal is entailed when its term is in the class of true. An equality
-- goal also holds when both of its sides are in one class.

constKey :: Value -> Maybe ConstKey
constKey (VInt n) = Just (CInt n)
constKey (VList l) = CList <$> mapM constKey l
constKey (VData name fields) = CData name <$> mapM (\(field, value) -> (,) field <$> constKey value) fields
constKey (VBool b) = Just (CBool b)
constKey (VFunct _ _ _ (BuiltinFunct funct) _) = Just (CBuiltin (show (unowned funct)))
constKey _ = Nothing

emptyTable :: TermTable
emptyTable = TermTable Map.empty [] Map.empty [] [] [] 0 0

internAll :: TermTable -> [IotaProof] -> (TermTable, [Int])
internAll = mapAccumL internTerm

internTerm :: TermTable -> IotaProof -> (TermTable, Int)
internTerm table (ATerm iota) = internKey table (KIota iota)
internTerm table (BVar index) = internKey table (KBound index)
internTerm table (Forall index guards body) =
    let (table1, guardIds) = internAll table guards
        (table2, bodyId) = internTerm table1 body
        key = KForall index guardIds bodyId
        (table3, termId) = internKey table2 key
     in if Map.member key (tableKeys table2)
            then (table3, termId)
            else (table3{tableForalls = (termId, (index, guardIds, bodyId)) : tableForalls table3, tableForallCount = tableForallCount table3 + 1}, termId)
internTerm table (CTerm value) =
    -- A builtin function is the same term however it was written, with or without its contracts
    let found =
            case constKey value of
                Just key -> Map.lookup key (tableConstIds table)
                Nothing -> lookup value (tableOtherConsts table)
     in case found of
            Just constId -> internKey table (KConst constId)
            Nothing ->
                let constId = length (tableConsts table)
                    withConst = table{tableConsts = (canonicalValue value, constId) : tableConsts table}
                 in internKey
                        ( case constKey value of
                            Just key -> withConst{tableConstIds = Map.insert key constId (tableConstIds table)}
                            Nothing -> withConst{tableOtherConsts = (value, constId) : tableOtherConsts table}
                        )
                        (KConst constId)
internTerm table (FApp funct args) =
    let (table1, functId) = internTerm table funct
        (table2, argIds) = internAll table1 args
        key = KApp functId argIds
        (table3, termId) = internKey table2 key
     in if Map.member key (tableKeys table2)
            then (table3, termId)
            else (table3{tableApps = (termId, (functId, argIds)) : tableApps table3, tableAppCount = tableAppCount table3 + 1}, termId)

-- A proof with the large builtin function values replaced by plain symbols
lightProof :: IotaProof -> IotaProof
lightProof (CTerm value@(VFunct _ _ _ (BuiltinFunct funct) _))
    | funct `elem` [Get, Push, Pop, Set, First, Last, NewArray, NewBoxedArray, NewEmptyArray] = CTerm (canonicalValue value)
lightProof (FApp funct args) = FApp (lightProof funct) (map lightProof args)
lightProof (Forall index guards body) = Forall index (map lightProof guards) (lightProof body)
lightProof other = other

-- Which struct the base of an update must be is for the type checker: for the proof engine a field is
-- the same function however it was written
unowned :: BuiltinFunct -> BuiltinFunct
unowned (Field _ field) = Field Nothing field
unowned (Project _ field) = Field Nothing field
unowned funct = funct

canonicalValue :: Value -> Value
canonicalValue (VFunct _ _ _ (BuiltinFunct funct) _) = VFunct [] [] [] (BuiltinFunct (unowned funct)) []
canonicalValue (VData name fields) = VData name [(field, canonicalValue value) | (field, value) <- fields]
canonicalValue value = value

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

-- The congruence closure
--
-- Two terms built from the same function on equal arguments are joined, and so are foralls with
-- the same index and equal guards and body. Joining classes changes the signatures of the terms
-- that use them, so each class keeps a list of its users, and only those are looked at again. Terms
-- and equalities can be added to a closure that has been built.

emptyClosure :: Closure
emptyClosure = Closure IntMap.empty Map.empty IntMap.empty IntMap.empty

-- Maps every term number to its class representative
closureFlat :: Closure -> IntMap.IntMap Int
closureFlat closure = IntMap.map (findClass (closureParents closure)) (closureParents closure)

signatureOf :: IntMap.IntMap Int -> Shape -> ShapeKey
signatureOf classes (AppShape functId argIds) = Left (findClass classes functId, map (findClass classes) argIds)
signatureOf classes (ForallShape index guardIds bodyId) = Right (index, map (findClass classes) guardIds, findClass classes bodyId)

shapeParts :: Shape -> [Int]
shapeParts (AppShape functId argIds) = functId : argIds
shapeParts (ForallShape _ guardIds bodyId) = guardIds ++ [bodyId]

-- Adds terms with parts, joining those that agree with a term already there
closureAdd :: Closure -> [(Int, Shape)] -> Closure
closureAdd closure terms =
    let firstNode = IntMap.size (closureNodes closure)
        numbered = zip [firstNode ..] terms
        classes = closureParents closure
        withNodes =
            closure
                { closureNodes = foldl' (\nodes (node, entry) -> IntMap.insert node entry nodes) (closureNodes closure) numbered
                , closureUsers = foldl' (\users (node, (_, shape)) -> foldl' (\acc part -> IntMap.insertWith (++) (findClass classes part) [node] acc) users (shapeParts shape)) (closureUsers closure) numbered
                }
        (resolved, merges) = resolveNodes withNodes (map fst numbered)
     in closureJoin resolved merges

-- Looks the nodes up by signature, and gives the pairs of terms that agree
resolveNodes :: Closure -> [Int] -> (Closure, [(Int, Int)])
resolveNodes closure0 = foldl' step (closure0, [])
  where
    step (closure, merges) node =
        case IntMap.lookup node (closureNodes closure) of
            Nothing -> (closure, merges)
            Just (termId, shape) ->
                let classes = closureParents closure
                    key = signatureOf classes shape
                 in case Map.lookup key (closureSignatures closure) of
                        Just other
                            | findClass classes other /= findClass classes termId -> (closure, (termId, other) : merges)
                            | otherwise -> (closure, merges)
                        Nothing -> (closure{closureSignatures = Map.insert key termId (closureSignatures closure)}, merges)

-- Joins the classes of the pairs of terms, and whatever that makes agree
closureJoin :: Closure -> [(Int, Int)] -> Closure
closureJoin closure [] = closure
closureJoin closure ((a, b) : pending) =
    let classes = closureParents closure
        ra = findClass classes a
        rb = findClass classes b
     in if ra == rb
            then closureJoin closure pending
            else
                let users = closureUsers closure
                    usersOf r = IntMap.findWithDefault [] r users
                    -- the class with fewer users is the one whose users are looked at again
                    (loser, winner) = if length (usersOf ra) <= length (usersOf rb) then (ra, rb) else (rb, ra)
                    joined =
                        closure
                            { closureParents = IntMap.insert loser winner classes
                            , closureUsers = IntMap.insertWith (++) winner (usersOf loser) (IntMap.delete loser users)
                            }
                    (resolved, merges) = resolveNodes joined (usersOf loser)
                 in closureJoin resolved (merges ++ pending)

rep :: IntMap.IntMap Int -> Int -> Int
rep classes x = IntMap.findWithDefault x x classes

findClass :: IntMap.IntMap Int -> Int -> Int
findClass classes x =
    case IntMap.lookup x classes of
        Just parent | parent /= x -> findClass classes parent
        _ -> x

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

-- The constraints, and whether they contradict each other anywhere (not only near a goal)
data Arithmetic = Arithmetic Graph Bool

-- The edges out of each node, and the number of nodes
data Graph = Graph (IntMap.IntMap [(Int, Integer)]) Int

buildGraph :: [Edge] -> Graph
buildGraph edges =
    let outgoing = IntMap.fromListWith (++) [(from, [(to, weight)]) | (from, to, weight) <- edges]
        nodes = IntMap.fromList ([(from, ()) | (from, _, _) <- edges] ++ [(to, ()) | (_, to, _) <- edges])
     in Graph outgoing (IntMap.size nodes)

arithmeticEdges :: TermTable -> IntMap.IntMap Int -> Int -> Int -> Arithmetic
arithmeticEdges table classes trueId zeroId =
    let node = rep classes
        constTerms = [(Map.lookup (KConst constId) (tableKeys table), value) | (value, constId) <- tableConsts table]
        builtinOfClass = builtinsByClass table classes (const True)
        intOfClass = Map.fromList [(node termId, n) | (Just termId, VInt n) <- constTerms]
        -- t = a * n is only a difference constraint when n is 0 or 1
        scaled t a n
            | n == 0 = diff t zeroId 0
            | n == 1 = diff t a 0
            | otherwise = []
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
                (Just Times, [a, b])
                    | Just n <- Map.lookup (node b) intOfClass -> scaled t a n
                    | Just n <- Map.lookup (node a) intOfClass -> scaled t b n
                (Just Div, [a, b])
                    | Just 1 <- Map.lookup (node b) intOfClass -> diff t a 0
                (Just Size, [_]) -> [(node t, node zeroId, 0)]
                (Just (Rel rel), [l, r]) | node t == node trueId -> relEdges rel l r
                _ -> []
        constEdges = concat [diff termId zeroId n | (termId, n) <- Map.toList intOfClass]
        edges = constEdges ++ concat [appEdges t functId args | (t, (functId, args)) <- tableApps table]
        -- x != y facts, and the terms c * x for a constant c, which the difference constraints cannot express and
        -- are refined from the graph (below)
        notEquals =
            [ (node l, node r)
            | (t, (functId, [l, r])) <- tableApps table
            , node t == node trueId
            , Just (Rel NotEq) <- [Map.lookup (node functId) builtinOfClass]
            ]
        scaledBy =
            Map.fromListWith
                (++)
                [ (n, [(node t, node x)])
                | (t, (functId, [a, b])) <- tableApps table
                , Just Times <- [Map.lookup (node functId) builtinOfClass]
                , (x, n) <- take 1 ([(a, n') | Just n' <- [Map.lookup (node b) intOfClass]] ++ [(b, n') | Just n' <- [Map.lookup (node a) intOfClass]])
                , n /= 0
                , n /= 1
                ]
        zeroNode = node zeroId
        -- Adds what the graph so far implies about those terms, twice, since the second round can use the first's edges:
        -- x != y with x <= y is x < y, and c * x - c * y <= c * d when x - y <= d (when c is negative, the other way round)
        refine :: Int -> [Edge] -> Graph
        refine rounds es =
            let graph = buildGraph es
                sources = nubOrd (concat [[l, r] | (l, r) <- notEquals] ++ concat [[x, t] | group <- Map.elems scaledBy, (t, x) <- (zeroNode, zeroNode) : group])
                dists = IntMap.fromList [(source, shortestPaths graph (IntMap.singleton source 0)) | source <- sources]
                dist source target = case IntMap.lookup source dists of
                    Just (Just reached) -> IntMap.lookup target reached
                    _ -> Nothing
                tighter source target bound = maybe True (> bound) (dist source target)
                strictEdges =
                    concat
                        [ [(r, l, -1) | dist r l == Just 0] ++ [(l, r, -1) | dist l r == Just 0]
                        | (l, r) <- notEquals
                        ]
                scaledEdges =
                    concat
                        [ [ (t2, t1, bound)
                          | (p@(t1, x1), pi') <- zip points [0 :: Int ..]
                          , (q@(t2, x2), qi) <- zip points [0 ..]
                          , pi' /= qi
                          , p /= q
                          , Just d <- [if c > 0 then dist x2 x1 else dist x1 x2]
                          , let bound = abs c * d
                          , tighter t2 t1 bound
                          ]
                        | (c, group) <- Map.toList scaledBy
                        , let points = (zeroNode, zeroNode) : take 8 group
                        ]
                extra = strictEdges ++ scaledEdges
             in if rounds <= 0 || null extra then graph else refine (rounds - 1) (es ++ extra)
        graphOf = if null notEquals && Map.null scaledBy then buildGraph edges else refine 2 edges
     in let graph = graphOf in Arithmetic graph (not (consistent graph))

-- The differences x - y among the terms, as the classes of x and y, by the class of the difference
differencesByClass :: TermTable -> IntMap.IntMap Int -> Map.Map Int [(Int, Int)]
differencesByClass table classes =
    Map.fromListWith
        (++)
        [ (rep classes termId, [(rep classes x, rep classes y)])
        | (termId, (functId, [x, y])) <- tableApps table
        , Just Minus <- [Map.lookup (rep classes functId) builtinOfClass]
        ]
  where
    builtinOfClass = builtinsByClass table classes (== Minus)

-- The constraints are on the differences between terms, so a term x - y is a node of its own that they say
-- nothing about. A difference compared with zero, or with another that has a side in common, is a comparison
-- of the other sides: x - y >= 0 is x >= y, and x - y < x - z is z < y. That is what a loop variant such as
-- n - i needs.
differenceEntails :: Map.Map Int [(Int, Int)] -> Arithmetic -> Int -> Rel -> Int -> Int -> Bool
differenceEntails differences arithmetic zeroClass rel lhs rhs =
    or [arithmeticEntails arithmetic rel x y | rhs == zeroClass, (x, y) <- of' lhs]
        || or [arithmeticEntails arithmetic rel y x | lhs == zeroClass, (x, y) <- of' rhs]
        || or
            [ if x1 == x2 then arithmeticEntails arithmetic rel y2 y1 else arithmeticEntails arithmetic rel x1 x2
            | (x1, y1) <- of' lhs
            , (x2, y2) <- of' rhs
            , x1 == x2 || y1 == y2
            ]
  where
    of' side = Map.findWithDefault [] side differences

-- Linear arithmetic
--
-- The difference constraints stop at x - y <= c. A relation with a sum of two variables or a multiple of one
-- (s + i = n, 2 * x <= y, x / 2 < x) goes to Linear: the arithmetic of the facts becomes equations and inequalities
-- between the classes, and a relation is entailed when the facts with its negation have no solution. That is only
-- done when some fact needs it (otherwise the difference constraints are already complete), and Linear gives up on a
-- system that grows too large, which proves nothing.
--   t = a + b          t - a - b = 0
--   t = a - b          t - a + b = 0
--   t = c * a          t - c a = 0             (c a known integer)
--   t = a / c          c t <= a <= c t + c - 1 (c > 0, rounding down; the reverse for c < 0)
--   size(l)            size(l) >= 0
--   x < y and so on    x - y <= -1 and so on
--   a class that is a known integer n    x = n
linearSystem :: TermTable -> IntMap.IntMap Int -> Int -> (Int -> Bool) -> (Int -> Bool) -> [Constraint]
linearSystem table classes trueId positive negative
    | not (any needsLinear applications) = []
    | otherwise = [Equal (IntMap.singleton x 1) (fromInteger n) | (x, n) <- Map.toList intOfClass] ++ concatMap constraintsOf applications
  where
    node = rep classes
    builtinOfClass = builtinsByClass table classes (const True)
    constTerms = [(Map.lookup (KConst constId) (tableKeys table), value) | (value, constId) <- tableConsts table]
    intOfClass = Map.fromList [(node termId, n) | (Just termId, VInt n) <- constTerms]
    applications = [(t, node t, builtinOfClass `lookupBuiltin` functId, map node args) | (t, (functId, args)) <- tableApps table]
    lookupBuiltin m functId = Map.lookup (node functId) m
    known x = Map.lookup x intOfClass
    needsLinear (_, _, Just Plus, [a, b]) = known a == Nothing && known b == Nothing
    needsLinear (_, _, Just Minus, [_, b]) = known b == Nothing
    needsLinear (_, _, Just Times, [a, b]) = any (maybe False (\n -> n /= 0 && n /= 1)) [known a, known b]
    needsLinear (_, _, Just Div, [_, b]) = maybe False (/= 1) (known b)
    needsLinear (_, _, Just Mod, [_, b]) = maybe True (/= 0) (known b)
    needsLinear _ = False
    form terms = IntMap.filter (/= 0) (IntMap.fromListWith (+) terms)
    constraintsOf (_, t, Just Plus, [a, b]) = [Equal (form [(t, 1), (a, -1), (b, -1)]) 0]
    constraintsOf (_, t, Just Minus, [a, b]) = [Equal (form [(t, 1), (a, -1), (b, 1)]) 0]
    constraintsOf (_, t, Just Times, [a, b])
        | Just n <- known b = [Equal (form [(t, 1), (a, negate (fromInteger n))]) 0]
        | Just n <- known a = [Equal (form [(t, 1), (b, negate (fromInteger n))]) 0]
    constraintsOf (_, t, Just Div, [a, b])
        | Just n <- known b, n > 0 = [AtMost (form [(t, fromInteger n), (a, -1)]) 0, AtMost (form [(a, 1), (t, negate (fromInteger n))]) (fromInteger (n - 1))]
        | Just n <- known b, n < 0 = [AtMost (form [(a, 1), (t, negate (fromInteger n))]) 0, AtMost (form [(t, fromInteger n), (a, -1)]) (fromInteger (negate n - 1))]
    -- a = c * q + t with the remainder t from 0 to c - 1 (from c + 1 to 0 for a negative c): q is a variable of its own,
    -- numbered below zero from the application (not its class: two remainders that are equal still have quotients of their own), and it is a / c when that is a term too
    constraintsOf (raw, t, Just Mod, [a, b])
        | Just n <- known b, n /= 0 =
            let q = negate raw - 1
                bounds
                    | n > 0 = [AtMost (form [(t, -1)]) 0, AtMost (form [(t, 1)]) (fromInteger (n - 1))]
                    | otherwise = [AtMost (form [(t, 1)]) 0, AtMost (form [(t, -1)]) (fromInteger (negate n - 1))]
             in Equal (form [(a, 1), (q, negate (fromInteger n)), (t, -1)]) 0 : bounds
    -- a divisor that is not a known number but is known to be positive (or negative) still bounds the remainder
    constraintsOf (_, t, Just Mod, [_, b])
        | known b == Nothing && positive b = [AtMost (form [(t, -1)]) 0, AtMost (form [(t, 1), (b, -1)]) (-1)]
        | known b == Nothing && negative b = [AtMost (form [(t, 1)]) 0, AtMost (form [(b, 1), (t, -1)]) (-1)]
    constraintsOf (_, t, Just Size, [_]) = [AtMost (form [(t, -1)]) 0]
    constraintsOf (_, t, Just (Rel rel), [l, r])
        | t == node trueId = case rel of
            Lt -> [AtMost (form [(l, 1), (r, -1)]) (-1)]
            LtEq -> [AtMost (form [(l, 1), (r, -1)]) 0]
            Gt -> [AtMost (form [(r, 1), (l, -1)]) (-1)]
            GtEq -> [AtMost (form [(r, 1), (l, -1)]) 0]
            _ -> []
    constraintsOf _ = []

-- Whether l rel r follows from the linear system, for class representatives l and r
linearEntails :: [Constraint] -> Rel -> Int -> Int -> Bool
linearEntails system rel l r =
    case rel of
        Lt -> refuted [AtMost (form [(r, 1), (l, -1)]) 0]
        LtEq -> refuted [AtMost (form [(r, 1), (l, -1)]) (-1)]
        Gt -> refuted [AtMost (form [(l, 1), (r, -1)]) 0]
        GtEq -> refuted [AtMost (form [(l, 1), (r, -1)]) (-1)]
        Eq -> linearEntails system LtEq l r && linearEntails system GtEq l r
        NotEq -> refuted [Equal (form [(l, 1), (r, -1)]) 0]
  where
    form terms = IntMap.filter (/= 0) (IntMap.fromListWith (+) terms)
    refuted = infeasibleWith system

-- Whether lhs rel rhs follows from the constraints, for the class representatives lhs and rhs
arithmeticEntails :: Arithmetic -> Rel -> Int -> Int -> Bool
arithmeticEntails (Arithmetic graph inconsistent) rel lhs rhs =
    inconsistent || case rel of
        Lt -> bound rhs lhs (-1)
        LtEq -> bound rhs lhs 0
        Gt -> bound lhs rhs (-1)
        GtEq -> bound lhs rhs 0
        Eq -> bound rhs lhs 0 && bound lhs rhs 0
        NotEq -> bound rhs lhs (-1) || bound lhs rhs (-1)
  where
    -- Whether the shortest path from source to target weighs at most k
    bound source target k =
        case shortestPaths graph (IntMap.singleton source 0) of
            Nothing -> True
            Just dist -> maybe (source == target && 0 <= k) (<= k) (IntMap.lookup target dist)

-- Whether the constraints have a solution, which is when no cycle of edges weighs less than
-- zero. Starting every node at distance 0 finds a negative cycle anywhere in the graph, whether
-- or not a goal can reach it.
consistent :: Graph -> Bool
consistent graph@(Graph outgoing _) = shortestPaths graph (IntMap.map (const 0) outgoing) /= Nothing

-- Bellman-Ford from the given starting distances, looking again only at the edges out of the nodes that
-- got shorter in the last round; Nothing when it keeps improving, which is a negative cycle reachable
-- from them
shortestPaths :: Graph -> IntMap.IntMap Integer -> Maybe (IntMap.IntMap Integer)
shortestPaths (Graph outgoing nodeCount) start = go (nodeCount + 1) start (IntMap.keys start)
  where
    go :: Int -> IntMap.IntMap Integer -> [Int] -> Maybe (IntMap.IntMap Integer)
    go _ dist [] = Just dist
    go rounds dist frontier
        | rounds <= 0 = Nothing
        | otherwise =
            let (dist', improved) = foldl' relaxFrom (dist, IntMap.empty) frontier
             in go (rounds - 1) dist' (IntMap.keys improved)
    relaxFrom (dist, improved) from =
        case IntMap.lookup from dist of
            Nothing -> (dist, improved)
            Just d -> foldl' (relax d) (dist, improved) (IntMap.findWithDefault [] from outgoing)
    relax d (dist, improved) (to, weight) =
        case IntMap.lookup to dist of
            Just current | current <= d + weight -> (dist, improved)
            _ -> (IntMap.insert to (d + weight) dist, IntMap.insert to () improved)

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
deriveRefl context@(ProofContext facts _) =
    let eqFacts = equalityFacts facts
        reversedEqFacts = map reverseEqProof eqFacts
        derivedFacts = reflectProofsByProofs facts (eqFacts ++ reversedEqFacts)
     in insertProofs derivedFacts context

evalAll :: BuiltinEvaluator -> ProofContext -> [IotaProof]
evalAll evalBuiltin context@(ProofContext facts _) =
    concatMap (evalProof evalBuiltin context) facts

evalIota :: BuiltinEvaluator -> Iota -> ProofContext -> [IotaProof]
evalIota evalBuiltin iota context@(ProofContext facts _) =
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
concreteValueOfIota iota (ProofContext facts _) =
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

-- Each proof is rewritten with the sources whose left side occurs in it. With few sources every proof is tried
-- against each; with many, its subterms are looked up among the sources instead of trying every source.
reflectProofsByProofs :: [IotaProof] -> [IotaProof] -> [IotaProof]
reflectProofsByProofs proofs sources = nubOrd (concatMap reflected proofs)
  where
    rewrites = [(lhs, rhs) | FApp funct [lhs, rhs] <- sources, funct == eqProof]
    rewritesOf = Map.fromListWith (flip (++)) [(lhs, [rhs]) | (lhs, rhs) <- rewrites]
    reflected proof
        | length rewrites <= fewSources = [new | (lhs, rhs) <- rewrites, Just new <- [substituteProofTerm lhs rhs proof]]
        | otherwise =
            [ new
            | lhs <- nubOrd (subterms proof)
            , rhs <- Map.findWithDefault [] lhs rewritesOf
            , Just new <- [substituteProofTerm lhs rhs proof]
            ]
    fewSources = 4

-- The terms substituteProofTerm can replace in a proof: the proof itself and the parts of its applications and foralls
subterms :: IotaProof -> [IotaProof]
subterms proof@(FApp funct args) = proof : concatMap subterms (funct : args)
subterms proof@(Forall _ guards body) = proof : concatMap subterms (body : guards)
subterms proof = [proof]

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
substituteProofTerm source target (Forall index guards body) =
    let maybeGuards = map (substituteProofTerm source target) guards
        maybeBody = substituteProofTerm source target body
     in if any isJustProof (maybeBody : maybeGuards)
            then Just (Forall index (zipWith (`maybe` id) guards maybeGuards) (fromMaybe body maybeBody))
            else Nothing
substituteProofTerm _ _ _ = Nothing

reverseEqProof :: IotaProof -> IotaProof
reverseEqProof (FApp funct [lhs, rhs])
    | funct == eqProof = FApp eqProof [rhs, lhs]
reverseEqProof _ = error "Only Eq relation supported"

isJustProof :: Maybe a -> Bool
isJustProof Just{} = True
isJustProof Nothing = False
