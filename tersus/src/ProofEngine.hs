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
import Data.Containers.ListUtils (nubOrd)
import Data.List (foldl', mapAccumL)
import qualified Data.Set as Set
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
proofContextFromFacts = ProofContext . nubOrd

proofContextFacts :: ProofContext -> [IotaProof]
proofContextFacts (ProofContext facts) = facts

insertProofs :: [IotaProof] -> ProofContext -> ProofContext
insertProofs newFacts (ProofContext facts) = ProofContext (nubOrd (facts ++ newFacts))

proofContextDelta :: ProofContext -> ProofContext -> [IotaProof]
proofContextDelta (ProofContext oldFacts) (ProofContext newFacts) =
    filter (`notElem` oldFacts) newFacts

entails :: IotaProof -> ProofContext -> Bool
entails goal context = and (entailsAll [goal] context)

-- Which of the goals the context entails, sharing one congruence closure between them.
entailsAll :: [IotaProof] -> ProofContext -> [Bool]
entailsAll goals context = fst (entailsBlocked goals context)

-- Also the guards that kept an instance of a forall from being used: each is the one condition missing
-- for an instance whose other guards hold, so a case split on it is what may let the proof go on.
entailsBlocked :: [IotaProof] -> ProofContext -> ([Bool], [IotaProof])
entailsBlocked originalGoals (ProofContext originalFacts) =
    let (flags, blocked) = saturate (0 :: Int) facts
     in (zipWith provedAsForall goals flags, blocked)
  where
    -- The list builtins carry their contracts, which are large, and every fact and goal is
    -- compared with the others many times. They are replaced by plain symbols up front.
    facts = map lightProof originalFacts
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
            known = nubOrd (facts ++ guardFacts)
            context extra = ProofContext (nubOrd (known ++ extra))
            holdsUnder extra = and (entailsAll [bodyGoal] (context extra))
            -- Each entailment costs one unit of budget
            guided budget depth extra
                | budget <= 0 = (False, 0 :: Int)
                | and flags = (True, budget - 1)
                | depth <= 0 = (False, budget - 1)
                | otherwise = anyGuard (budget - 1) (take maxSplitGuards (aboutIndexFirst (filter notSplit (nubOrd blocked))))
              where
                -- Guards not already split on, those about the new index, or a term it has been found equal to, first
                aboutIndex = fresh : [other | FApp eq [x, y] <- extra, eq == eqProof, other <- if x == fresh then [y] else if y == fresh then [x] else []]
                aboutIndexFirst gs = [g | g <- gs, mentions g] ++ [g | g <- gs, not (mentions g)]
                mentions (FApp _ [a, b]) = a `elem` aboutIndex || b `elem` aboutIndex
                mentions _ = False
                notSplit (FApp _ [a, b]) = not (or [sameTerms x y a b | FApp _ [x, y] <- extra])
                notSplit _ = False
                sameTerms x y p q = (x == p && y == q) || (x == q && y == p)
                (flags, blocked) = entailsBlocked [bodyGoal] (context extra)
                anyGuard remaining [] = (False, remaining)
                anyGuard remaining (guard : rest) =
                    case guardCases guard of
                        [] -> anyGuard remaining rest
                        cases ->
                            let (ok, remaining') = allBranches remaining cases
                             in if ok then (True, remaining') else if remaining' <= 0 then (False, 0) else anyGuard remaining' rest
                allBranches remaining [] = (True, remaining)
                allBranches remaining (c : cs) =
                    let (ok, remaining') = guided remaining (depth - 1) (extra ++ c)
                     in if ok then allBranches remaining' cs else (False, remaining')
            comparisons t =
                [ [FApp (CTerm (builtinFunct (Rel Lt))) [fresh, t]]
                , [FApp eqProof [fresh, t]]
                , [FApp (CTerm (builtinFunct (Rel Gt))) [fresh, t]]
                ]
            reads = take maxSplitIndexes (splitIndexes known fresh bodyGoal)
         in holdsUnder []
                || fst (guided maxSplitAttempts maxSplitDepth [])
                || any (all holdsUnder . comparisons) reads
    proveForall _ = False
    -- Facts that are foralls are instantiated, and the closure is rebuilt with the instances
    -- that hold, until no new instance appears or the rounds run out. Without a forall this is
    -- one closure.
    saturate round currentFacts =
        let (table, classes, flags) = solve currentFacts goals
            instances = forallInstances table classes currentFacts
         in if null instances
                then (flags, [])
                else
                    let guardGoals = concatMap fst instances
                        (guardTable, guardClasses, guardFlags) = solve currentFacts (goals ++ guardGoals)
                        guardHolds = zip guardGoals (drop (length goals) guardFlags)
                        holds g = lookup g guardHolds == Just True
                        accepted = [body | (guards, body) <- instances, all holds guards]
                        -- an instance with exactly one guard missing would be used if that guard held, unless the
                        -- guard compares two terms that are already equal
                        missing = [g | (guards, _) <- instances, [g] <- [filter (not . holds) guards], distinctSides guardTable guardClasses g]
                        distinctSides table' classes' (FApp _ [a, b]) = rep classes' (idOf table' a) /= rep classes' (idOf table' b)
                        distinctSides _ _ _ = True
                     in if null accepted || round >= maxInstantiationRounds then (flags, missing) else saturate (round + 1) (nubOrd (currentFacts ++ accepted))

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
maxSplitDepth = 4

maxSplitGuards :: Int
maxSplitGuards = 6

maxSplitAttempts :: Int
maxSplitAttempts = 300

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

maxInstantiationRounds :: Int
maxInstantiationRounds = 5

-- Interns the facts and goals, builds the classes, and says which goals hold
solve :: [IotaProof] -> [IotaProof] -> (TermTable, IntMap.IntMap Int, [Bool])
solve givenFacts goals =
    let -- a != b is also b != a
        facts = givenFacts ++ [FApp funct [b, a] | FApp funct@(CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _)) [a, b] <- givenFacts]
        (table1, factIds) = internAll emptyTable facts
        (table2, goalIds) = internAll table1 goals
        (table3a, trueId) = internTerm table2 (CTerm (VBool True))
        (table3, zeroId) = internTerm table3a (CTerm (VInt 0))
        equalities =
            concat
                [ (factId, trueId) : [(idOf table3 lhs, idOf table3 rhs) | FApp funct [lhs, rhs] <- [fact], funct == eqProof]
                | (fact, factId) <- zip facts factIds
                ]
        (table4, classes) = evaluateClosure (0 :: Int) table3 equalities
        sameClass a b = rep classes a == rep classes b
        arithmetic = arithmeticEdges table4 classes trueId zeroId
        clash = constructorClash table4 classes trueId
        entailed goal goalId =
            clash
                || sameClass goalId trueId
                || or [sameClass (idOf table4 lhs) (idOf table4 rhs) | FApp funct [lhs, rhs] <- [goal], funct == eqProof]
                || or
                    [ provablyDistinct table4 classes (idOf table4 lhs) (idOf table4 rhs)
                    | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _)) [lhs, rhs] <- [goal]
                    ]
                || or
                    [ arithmeticEntails arithmetic rel (rep classes (idOf table4 lhs)) (rep classes (idOf table4 rhs))
                    | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) [lhs, rhs] <- [goal]
                    ]
     in (table4, classes, zipWith entailed goals goalIds)

-- The classes, once every builtin applied to concrete values is equal to its value. Evaluating
-- gives new constants, which can make more applications concrete, so it repeats.
evaluateClosure :: Int -> TermTable -> [(Int, Int)] -> (TermTable, IntMap.IntMap Int)
evaluateClosure round table equalities =
    let classes = congruenceClosure (tableApps table) (tableForalls table) equalities
        values = evaluatedTerms table classes
        links = [link | link@(term, field) <- selections table classes, rep classes term /= rep classes field]
     in if (null values && null links) || round >= maxEvaluationRounds
            then (table, classes)
            else
                let (table', valueIds) = internAll table [CTerm value | (_, value) <- values]
                 in evaluateClosure (round + 1) table' (equalities ++ zip (map fst values) valueIds ++ links)

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
selections table classes = reads ++ injectivity
  where
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
constructorClash :: TermTable -> IntMap.IntMap Int -> Int -> Bool
constructorClash table classes trueId =
    any ((> 1) . length) (Map.elems (constantsByClass table classes))
        || any ((> 1) . length) (Map.elems (constructorNames table classes))
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
provablyDistinct :: TermTable -> IntMap.IntMap Int -> Int -> Int -> Bool
provablyDistinct table classes a b =
    differ (constantsByClass table classes) || differ' (constructorNames table classes)
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

forallInstances :: TermTable -> IntMap.IntMap Int -> [IotaProof] -> [([IotaProof], IotaProof)]
forallInstances table classes facts =
    nubOrd
        [ (map (substituteIndex index indexTerm) guards, instantiated)
        | Forall index guards body <- facts
        , listTerm <- indexedLists index body
        , indexTerm <- getIndexesOf listTerm
        , let instantiated = substituteIndex index indexTerm body
        , instantiated `Set.notMember` known
        ]
  where
    known = Set.fromList facts
    getClasses = Map.keys (builtinsByClass table classes (== Get))
    termFor = termOf table
    -- The index terms t of the get(L', t) in the closure, by the class of L'
    getIndexes =
        Map.fromListWith
            (flip (++))
            [ (rep classes listId, [termFor indexId])
            | (_, (functId, [listId, indexId])) <- tableApps table
            , rep classes functId `elem` getClasses
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

-- A forall is one opaque term built from its guards and body, so the same forall twice is one term
data TermKey = KIota Iota | KConst Int | KApp Int [Int] | KBound Variable | KForall Variable [Int] Int deriving (Eq, Ord)

-- What tells constants apart. Builtin functions are one constant each, however they were written.
-- Any other constant (a user function) has no key and is found by comparing whole values.
data ConstKey = CInt Integer | CList [ConstKey] | CBool Bool | CData Name [(Variable, ConstKey)] | CBuiltin String deriving (Eq, Ord)

constKey :: Value -> Maybe ConstKey
constKey (VInt n) = Just (CInt n)
constKey (VList l) = CList <$> mapM constKey l
constKey (VData name fields) = CData name <$> mapM (\(field, value) -> (,) field <$> constKey value) fields
constKey (VBool b) = Just (CBool b)
constKey (VFunct _ _ _ (BuiltinFunct funct) _) = Just (CBuiltin (show (unowned funct)))
constKey _ = Nothing

data TermTable = TermTable
    { tableKeys :: Map.Map TermKey Int
    , tableConsts :: [(Value, Int)]
    , tableConstIds :: Map.Map ConstKey Int -- the number of each constant, found without comparing whole values
    , tableOtherConsts :: [(Value, Int)] -- constants with no key
    , tableApps :: [(Int, (Int, [Int]))] -- applications: term, function term, argument terms
    , tableForalls :: [(Int, (Variable, [Int], Int))] -- foralls: term, index, guard terms, body term
    }

emptyTable :: TermTable
emptyTable = TermTable Map.empty [] Map.empty [] [] []

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
            else (table3{tableForalls = (termId, (index, guardIds, bodyId)) : tableForalls table3}, termId)
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
            else (table3{tableApps = (termId, (functId, argIds)) : tableApps table3}, termId)

-- A proof with the large builtin function values replaced by plain symbols
lightProof :: IotaProof -> IotaProof
lightProof (CTerm value@(VFunct _ _ _ (BuiltinFunct funct) _))
    | funct `elem` [Get, Push, Set, First, Last] = CTerm (canonicalValue value)
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

-- Maps term numbers to their class representative (a number missing from the map is its own)
congruenceClosure :: [(Int, (Int, [Int]))] -> [(Int, (Variable, [Int], Int))] -> [(Int, Int)] -> IntMap.IntMap Int
congruenceClosure apps foralls equalities = settle (foldl' unionClasses IntMap.empty equalities)
  where
    -- Two terms are congruent when they have the same shape on equal parts. foralls with the same
    -- index and equal guards and body are equal, as for applications.
    settle classes =
        let flat = IntMap.map (findClass classes) classes
            bySignature =
                Map.fromListWith
                    (++)
                    ( [(Left (rep flat functId, map (rep flat) argIds), [termId]) | (termId, (functId, argIds)) <- apps]
                        ++ [(Right (index, map (rep flat) guardIds, rep flat bodyId), [termId]) | (termId, (index, guardIds, bodyId)) <- foralls]
                    )
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

-- The constraints, and whether they contradict each other anywhere (not only near a goal)
data Arithmetic = Arithmetic [Edge] Bool

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
     in Arithmetic edges (not (consistent edges))

-- Whether lhs rel rhs follows from the constraints, for the class representatives lhs and rhs
arithmeticEntails :: Arithmetic -> Rel -> Int -> Int -> Bool
arithmeticEntails (Arithmetic edges inconsistent) rel lhs rhs =
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
        case shortestPaths edges (Map.singleton source 0) of
            Nothing -> True
            Just dist -> maybe (source == target && 0 <= k) (<= k) (Map.lookup target dist)

-- Whether the constraints have a solution, which is when no cycle of edges weighs less than
-- zero. Starting every node at distance 0 finds a negative cycle anywhere in the graph, whether
-- or not a goal can reach it.
consistent :: [Edge] -> Bool
consistent edges = shortestPaths edges (Map.fromList [(node, 0) | (from, to, _) <- edges, node <- [from, to]]) /= Nothing

-- Bellman-Ford from the given starting distances; Nothing when it keeps improving, which is a
-- negative cycle reachable from them
shortestPaths :: [Edge] -> Map.Map Int Integer -> Maybe (Map.Map Int Integer)
shortestPaths edges start = go (length edges + 1) start
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

-- Each proof is rewritten with the sources whose left side occurs in it, found by looking its
-- subterms up among the sources instead of trying every source.
reflectProofsByProofs :: [IotaProof] -> [IotaProof] -> [IotaProof]
reflectProofsByProofs proofs sources = nubOrd (concatMap reflected proofs)
  where
    rewritesOf = Map.fromListWith (flip (++)) [(lhs, [rhs]) | FApp funct [lhs, rhs] <- sources, funct == eqProof]
    reflected proof =
        [ new
        | lhs <- nubOrd (subterms proof)
        , rhs <- Map.findWithDefault [] lhs rewritesOf
        , Just new <- [substituteProofTerm lhs rhs proof]
        ]

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
