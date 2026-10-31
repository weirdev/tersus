module TestProofs
    ( testProofEngine
    , testArithmetic
    , testForallInstantiation
    , testForallProof
    , testForallGrownList
    , testRefinedArithmetic
    , testModulo
    , testLinearArithmetic
    , testSolverCache
    , testListProofs
    , testEqualityByParts
    , testMulDivNegative
    , testPrettyProofs
    , testForallLoops
    , testForallSyntax
    ) where

import Data.List (isInfixOf)
import Parse
import Pipeline (validateStatements)
import qualified ProofEngine as Engine
import StdLib
import TersusTypes
import Utils
import TestHarness

-- Proof engine tests
testProofEngineInsertDedupes :: TestResult
testProofEngineInsertDedupes =
    let knownProof = FApp eqProof [ATerm (Iota "x"), CTerm (VInt 5)]
        context = Engine.insertProofs [knownProof, knownProof] Engine.emptyProofContext
     in testAssertEq (Engine.proofContextFacts context) [knownProof]

testProofEngineEntailsEquivalentTerms :: TestResult
testProofEngineEntailsEquivalentTerms =
    let iotaX = Iota "x"
        iotaA = Iota "a"
        context =
            Engine.proofContextFromFacts
                [ FApp eqProof [ATerm iotaX, ATerm iotaA]
                , FApp eqProof [ATerm iotaA, CTerm (VInt 5)]
                ]
        goal = FApp eqProof [ATerm iotaX, CTerm (VInt 5)]
     in testAssertTrue (Engine.entails goal context)

testProofEngineReflSubstitutesNestedTerms :: TestResult
testProofEngineReflSubstitutesNestedTerms =
    let iotaX = Iota "x"
        iotaA = Iota "a"
        context =
            Engine.proofContextFromFacts
                [ FApp eqProof [ATerm iotaA, CTerm (VInt 5)]
                , FApp (CTerm (builtinFunct (Rel Gt))) [ATerm iotaX, ATerm iotaA]
                ]
        derived = Engine.deriveRefl context
        goal = FApp (CTerm (builtinFunct (Rel Gt))) [ATerm iotaX, CTerm (VInt 5)]
     in testAssertTrue (Engine.entails goal derived)

testProofEngineEvalDerivesConcreteBuiltinResult :: TestResult
testProofEngineEvalDerivesConcreteBuiltinResult =
    let iotaList = Iota "list"
        iotaSize = Iota "size"
        context =
            Engine.proofContextFromFacts
                [ FApp eqProof [ATerm iotaList, CTerm (VList [VInt 1, VInt 2])]
                , FApp eqProof [ATerm iotaSize, FApp (CTerm (builtinFunct Size)) [ATerm iotaList]]
                ]
        result = Engine.applyRewrite evalBuiltinFunct (Engine.EngineEval iotaSize) context
        goal = FApp eqProof [ATerm iotaSize, CTerm (VInt 2)]
     in case result of
            Ok derived -> testAssertTrue (Engine.entails goal derived)
            Error e -> Just $ "Engine eval failed: " ++ e

-- Every iota in the clique equals every other, so an unmemoized equivalence walk is
-- exponential. The unrelated fact comes first so entailment must exhaust the clique's
-- equivalence class before reaching the fact that matches.
testProofEngineEntailsDenseEqualitiesTerminates :: TestResult
testProofEngineEntailsDenseEqualitiesTerminates =
    let firstIota = Iota "i1"
        secondIota = Iota "i2"
        iotas = firstIota : secondIota : map (Iota . ("i" ++) . show) [3 .. 8 :: Int]
        context =
            Engine.proofContextFromFacts
                ( FApp eqProof [ATerm (Iota "outsideA"), ATerm (Iota "outsideB")]
                    : [FApp eqProof [ATerm a, ATerm b] | a <- iotas, b <- iotas, a /= b]
                )
        related = FApp eqProof [ATerm firstIota, ATerm secondIota]
        unrelated = FApp eqProof [ATerm firstIota, ATerm (Iota "unrelated")]
     in testAssertEq (Engine.entails related context, Engine.entails unrelated context) (True, False)

-- Equal arguments give equal results without any fact having been rewritten (no refl):
-- size(q) = size(s) + 1, s = k and size(k) = l give size(q) = l + 1.
nestedCongruenceFacts :: [IotaProof]
nestedCongruenceFacts =
    let sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        plus a b = FApp (CTerm (builtinFunct Plus)) [a, b]
     in [ FApp eqProof [sizeOf (ATerm (Iota "q")), plus (sizeOf (ATerm (Iota "s"))) (CTerm (VInt 1))]
        , FApp eqProof [ATerm (Iota "s"), ATerm (Iota "k")]
        , FApp eqProof [sizeOf (ATerm (Iota "k")), ATerm (Iota "l")]
        , FApp eqProof [ATerm (Iota "d"), plus (ATerm (Iota "l")) (CTerm (VInt 1))]
        ]

testProofEngineEntailsNestedCongruence :: TestResult
testProofEngineEntailsNestedCongruence =
    let goal = FApp eqProof [FApp (CTerm (builtinFunct Size)) [ATerm (Iota "q")], ATerm (Iota "d")]
        ltGoal = FApp (CTerm (builtinFunct (Rel LtEq))) [FApp (CTerm (builtinFunct Size)) [ATerm (Iota "q")], ATerm (Iota "d")]
        context = Engine.proofContextFromFacts nestedCongruenceFacts
     in testAssertEq (Engine.entails goal context, Engine.entails ltGoal context) (True, True)

-- Dropping the link between s and k breaks the chain, so the goal is no longer entailed
testProofEngineEntailsNestedCongruenceNeedsEveryLink :: TestResult
testProofEngineEntailsNestedCongruenceNeedsEveryLink =
    let goal = FApp eqProof [FApp (CTerm (builtinFunct Size)) [ATerm (Iota "q")], ATerm (Iota "d")]
        context = Engine.proofContextFromFacts (filter (/= (nestedCongruenceFacts !! 1)) nestedCongruenceFacts)
     in testAssertEq (Engine.entails goal context) False

-- A relation that is a fact holds for terms equal to its arguments, and entailsAll answers each goal
testProofEngineEntailsRelationOfEqualTerms :: TestResult
testProofEngineEntailsRelationOfEqualTerms =
    let lt a b = FApp (CTerm (builtinFunct (Rel Lt))) [a, b]
        context =
            Engine.proofContextFromFacts
                [ lt (ATerm (Iota "x")) (ATerm (Iota "n"))
                , FApp eqProof [ATerm (Iota "x"), ATerm (Iota "y")]
                ]
        goals = [lt (ATerm (Iota "y")) (ATerm (Iota "n")), lt (ATerm (Iota "n")) (ATerm (Iota "y"))]
     in testAssertEq (Engine.entailsAll goals context) [True, False]

testProofEngine :: Test
testProofEngine =
    testCaseSeq
        "testProofEngine"
        [ testProofEngineInsertDedupes
        , testProofEngineEntailsDenseEqualitiesTerminates
        , testProofEngineEntailsEquivalentTerms
        , testProofEngineEntailsNestedCongruence
        , testProofEngineEntailsNestedCongruenceNeedsEveryLink
        , testProofEngineEntailsRelationOfEqualTerms
        , testProofEngineReflSubstitutesNestedTerms
        , testProofEngineEvalDerivesConcreteBuiltinResult
        ]

testArithmetic :: Test
testArithmetic =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        plus a b = FApp (CTerm (builtinFunct Plus)) [a, b]
        sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        iota = ATerm . Iota
        int = CTerm . VInt
        ctx = Engine.proofContextFromFacts
        engine facts goal = testAssertTrue (Engine.entails goal (ctx facts))
        engineNot facts goal = testAssertTrue (not (Engine.entails goal (ctx facts)))
     in testCaseSeq
            "testArithmetic"
            [ -- Engine: relations follow from known values and from x + c
              engine [FApp eqProof [iota "s", int 3]] (rel Gt (iota "s") (int 0))
            , engine [FApp eqProof [iota "j", plus (iota "i") (int 1)], rel Lt (iota "i") (iota "n")] (rel LtEq (iota "j") (iota "n"))
            , engine [rel Lt (iota "a") (iota "b"), rel Lt (iota "b") (iota "c")] (rel Lt (iota "a") (iota "c"))
            , engine [rel Lt (iota "a") (iota "b")] (rel NotEq (iota "a") (iota "b"))
            , engine [FApp eqProof [iota "x", iota "y"]] (rel LtEq (iota "x") (iota "y"))
            , engine [] (rel GtEq (sizeOf (iota "l")) (int 0))
            , engine [] (rel Lt (int 2) (int 3))
            , -- Engine: nothing follows from too little
              engineNot [rel LtEq (iota "a") (iota "b")] (rel Lt (iota "a") (iota "b"))
            , engineNot [rel Lt (iota "i") (iota "n")] (rel Lt (plus (iota "i") (int 2)) (iota "n"))
            , engineNot [FApp eqProof [iota "s", int 0]] (rel Gt (iota "s") (int 0))
            , engineNot [rel Lt (iota "a") (iota "b")] (rel Lt (iota "b") (iota "a"))
            , engineNot [] (rel Gt (sizeOf (iota "l")) (int 0))
            , engineNot [rel LtEq (iota "a") (iota "b")] (rel NotEq (iota "a") (iota "b"))
            , -- Engine: a contradiction anywhere proves every comparison, also between unrelated terms
              engine [rel Lt (sizeOf (iota "xs")) (int 0)] (rel Lt (iota "a") (iota "b"))
            , engine [rel Lt (iota "p") (iota "q"), rel Lt (iota "q") (iota "p")] (rel Gt (iota "a") (iota "b"))
            , -- != parses, evaluates and validates
              parseEvalProgramHelper "return 3 != 4;" (Just (VBool True))
            , parseEvalProgramHelper "return 3 != 3;" (Just (VBool False))
            , parseEvalProgramHelper "x = 2; if x != 2 { return 1; } else { return 0; };" (Just (VInt 0))
            , parseValidProgramHelper "x = 2; affirm x != 3;"
            , parseValidateFailProgramHelper "x = 2; affirm x != 2;" "Could not prove"
            , parseValidProgramHelper "fn f(n: Int) -> Int { if n != 0 { affirm n != 0; } else { affirm n = 0; }; return 1; }; return f(4);"
            , -- Programs: no manual rewrites for the arithmetic
              parseValidProgramHelper "s = 3; affirm s > 0; affirm s >= 3; affirm s != 0;"
            , parseValidProgramHelper "x = 5; y = x + 1; affirm y > x; affirm y = 6;"
            , parseValidProgramHelper "fn f(l: List<Int>) -> Int { n = size(l); affirm n >= 0; return n; }; return f([1, 2]);"
            , parseValidProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i < n; }] [{ }] { j = i + 1; affirm j <= n; return j; }; return f(1, 2);"
            , parseValidateFailProgramHelper "x = 5; y = x + 1; affirm y > 6;" "Could not prove"
            , parseValidateFailProgramHelper "x = 5; y = x - 1; affirm y > 4;" "Could not prove"
            , parseValidateFailProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i <= n; }] [{ }] { j = i + 1; affirm j <= n; return j; };" "Could not prove"
            , -- The guard of an unreachable branch proves anything inside it
              parseValidProgramHelper "fn f(xs: List<Int>, a: Int, b: Int) -> Int { if size(xs) < 0 { affirm a < b; }; return 0; };"
            , -- A counting loop needs no axioms
              parseValidProgramHelper
                "i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { i = i + 1; }; affirm i = 3;"
            , parseValidateFailProgramHelper
                "i = 0; while i < 3 [{ affirm i <= 2; }] shrinks 3 - i { i = i + 1; };"
                "Loop invariant is not preserved"
            , parseValidateFailProgramHelper
                "i = 0; while i < 3 [{ affirm i >= 1; }] shrinks 3 - i { i = i + 1; };"
                "Loop invariant does not hold on entry"
            ]

-- forall parses into a bound index (BVar) with its guards, and the validator rejects it for now
-- forall facts are instantiated at the elements the program reads
testForallInstantiation :: Test
testForallInstantiation =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        getOf l t = FApp (CTerm (builtinFunct Get)) [l, t]
        sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        iota = ATerm . Iota
        int = CTerm . VInt
        allZero l = Forall "j" [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") (sizeOf l)] (rel Eq (getOf l (BVar "j")) (int 0))
        engine facts goal = testAssertTrue (Engine.entails goal (Engine.proofContextFromFacts facts))
        engineNot facts goal = testAssertTrue (not (Engine.entails goal (Engine.proofContextFromFacts facts)))
        inRange i l = [rel GtEq (iota i) (int 0), rel Lt (iota i) (sizeOf (iota l))]
        zeroAt l i = rel Eq (getOf (iota l) (iota i)) (int 0)
        -- reads element i of l under the contract that every element of l is 0
        reader = "fn f(l: List<Int>, i: Int) -> Int [{ affirm forall j in 0..size(l): get(l, j) = 0; rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] "
     in testCaseSeq
            "testForallInstantiation"
            [ -- Engine: an instance is used at the elements in the goal, when its guards hold
              engine (allZero (iota "l") : inRange "i" "l") (zeroAt "l" "i")
            , -- It also reaches elements of an equal list
              engine (allZero (iota "l") : rel Eq (iota "m") (iota "l") : inRange "i" "m") (zeroAt "m" "i")
            , -- and an index known only by its value
              engine [allZero (iota "l"), rel Eq (sizeOf (iota "l")) (int 3), rel Eq (iota "i") (int 2)] (zeroAt "l" "i")
            , -- Two elements, each with its own instance
              engine (allZero (iota "l") : inRange "i" "l" ++ inRange "k" "l") (rel Eq (getOf (iota "l") (iota "i")) (getOf (iota "l") (iota "k")))
            , -- Engine: an index outside the guards, another list, or no get term at all gets nothing
              engineNot (allZero (iota "l") : [rel GtEq (iota "i") (int 0)]) (zeroAt "l" "i")
            , engineNot (allZero (iota "l") : rel Lt (iota "i") (int 0) : [rel Lt (iota "i") (sizeOf (iota "l"))]) (zeroAt "l" "i")
            , engineNot (allZero (iota "l") : inRange "i" "m") (zeroAt "m" "i")
            , engineNot (inRange "i" "l") (zeroAt "l" "i")
            , engineNot (allZero (iota "l") : inRange "i" "l") (rel Eq (getOf (iota "l") (iota "i")) (int 1))
            , -- Programs: the contract's forall gives the element a function reads
              parseValidProgramHelper
                (reader ++ "[{ affirm return = 0; }] { x = get(l, i); return x; };")
            , parseValidProgramHelper
                ( zeroAxiom
                    ++ reader
                    ++ "[{ affirm return = 0; }] { x = get(l, i); return x; };\
                       \a = [0, 0]; rewrite zeros a; r = f(a, 1); affirm r = 0;"
                )
            , -- Without the forall, or with a guard that does not cover the index, nothing is known
              parseValidateFailProgramHelper
                "fn f(l: List<Int>, i: Int) -> Int [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ affirm return = 0; }] { x = get(l, i); return x; };"
                "Could not prove"
            , parseValidateFailProgramHelper
                "fn f(l: List<Int>, i: Int) -> Int [{ affirm forall j in 0..1: get(l, j) = 0; rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ affirm return = 0; }] { x = get(l, i); return x; };"
                "Could not prove"
            , parseValidateFailProgramHelper
                "fn f(l: List<Int>, m: List<Int>, i: Int) -> Int [{ affirm forall j in 0..size(l): get(l, j) = 0; rewrite checkRel i >= 0; rewrite checkRel i < size(m); affirm i >= 0; affirm i < size(m); }] [{ affirm return = 0; }] { x = get(m, i); return x; };"
                "Could not prove"
            , -- get's result is the term get(list, index), also without a forall
              parseValidProgramHelper
                "fn g(l: List<Int>, i: Int) -> Int [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ }] { x = get(l, i); y = get(l, i); affirm x = y; return x; };"
            ]

-- forall goals are proved for an arbitrary index that meets the guards
testForallProof :: Test
testForallProof =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        getOf l t = FApp (CTerm (builtinFunct Get)) [l, t]
        sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        iota = ATerm . Iota
        int = CTerm . VInt
        range hi = [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") hi]
        forallJ hi body = Forall "j" (range hi) body
        elementIsZero l = rel Eq (getOf l (BVar "j")) (int 0)
        engine facts goal = testAssertTrue (Engine.entails goal (Engine.proofContextFromFacts facts))
        engineNot facts goal = testAssertTrue (not (Engine.entails goal (Engine.proofContextFromFacts facts)))
     in testCaseSeq
            "testForallProof"
            [ -- Facts about the index alone
              engine [] (forallJ (int 3) (rel Lt (BVar "j") (int 3)))
            , engineNot [] (forallJ (int 3) (rel Lt (BVar "j") (int 2)))
            , engine [rel Eq (iota "n") (int 2)] (forallJ (iota "n") (rel Lt (BVar "j") (int 2)))
            , engineNot [] (forallJ (iota "n") (rel Lt (BVar "j") (int 2)))
            , -- A narrower range than a known forall, when the bound is known to be within it
              engine [forallJ (sizeOf (iota "l")) (elementIsZero (iota "l")), rel LtEq (iota "k") (sizeOf (iota "l"))] (forallJ (iota "k") (elementIsZero (iota "l")))
            , engineNot [forallJ (sizeOf (iota "l")) (elementIsZero (iota "l"))] (forallJ (iota "k") (elementIsZero (iota "l")))
            , -- The same forall about an equal list
              engine [forallJ (sizeOf (iota "l")) (elementIsZero (iota "l")), rel Eq (iota "m") (iota "l")] (forallJ (sizeOf (iota "m")) (elementIsZero (iota "m")))
            , -- Equal elements of two equal lists, and of two lists that are not known to be equal
              engine [rel Eq (iota "m") (iota "l")] (forallJ (sizeOf (iota "l")) (rel Eq (getOf (iota "l") (BVar "j")) (getOf (iota "m") (BVar "j"))))
            , engineNot [] (forallJ (sizeOf (iota "l")) (rel Eq (getOf (iota "l") (BVar "j")) (getOf (iota "m") (BVar "j"))))
            , -- An empty range holds for any body
              engine [] (forallJ (int 0) (rel Eq (int 1) (int 2)))
            , engine [rel LtEq (iota "n") (int 0)] (forallJ (iota "n") (rel Eq (int 1) (int 2)))
            , engineNot [] (forallJ (int 1) (rel Eq (int 1) (int 2)))
            , -- A guard other than a range
              engine [] (Forall "j" [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") (int 3), rel NotEq (BVar "j") (int 1)] (rel NotEq (BVar "j") (int 1)))
            , engineNot [] (Forall "j" [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") (int 3)] (rel NotEq (BVar "j") (int 1)))
            , -- Programs
              parseValidProgramHelper "affirm forall j in 0..3: j >= 0;"
            , parseValidProgramHelper "n = 2; affirm forall j in 0..n: j < 2;"
            , parseValidateFailProgramHelper "n = 3; affirm forall j in 0..n: j < 2;" "Could not prove"
            , parseValidProgramHelper "affirm forall j in 3..3: 1 = 2;"
            , -- Facts the program knows about other variables are used
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n <= 2; }] [{ affirm forall j in 0..n: j < 2; }] { return n; };"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n <= 3; }] [{ affirm forall j in 0..n: j < 2; }] { return n; };" "Could not prove"
            , -- A function proves a forall about its result from one about its argument
              parseValidProgramHelper
                "fn id(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ affirm forall j in 0..size(return): get(return, j) = 0; }] { return l; };"
            , parseValidProgramHelper
                "fn id(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 7; }] [{ affirm forall j in 0..size(return): get(return, j) = 7; }] { return l; };"
            , parseValidateFailProgramHelper
                "fn id(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ affirm forall j in 0..size(return): get(return, j) = 1; }] { return l; };"
                "Could not prove"
            ]

-- A list that grew by one: the old elements are kept, and the new one sits at the old size
testForallGrownList :: Test
testForallGrownList =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        getOf l t = FApp (CTerm (builtinFunct Get)) [l, t]
        sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        plus a b = FApp (CTerm (builtinFunct Plus)) [a, b]
        iota = ATerm . Iota
        int = CTerm . VInt
        forallJ hi body = Forall "j" [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") hi] body
        copiesA l = rel Eq (getOf l (BVar "j")) (getOf (iota "a") (BVar "j"))
        -- out0 copies a below i0, out1 keeps out0 below its size, and has a's element i0 after it
        grown =
            [ forallJ (iota "i0") (copiesA (iota "out0"))
            , forallJ (sizeOf (iota "out0")) (rel Eq (getOf (iota "out1") (BVar "j")) (getOf (iota "out0") (BVar "j")))
            , rel Eq (sizeOf (iota "out0")) (iota "i0")
            , rel Eq (getOf (iota "out1") (sizeOf (iota "out0"))) (getOf (iota "a") (iota "i0"))
            , rel Eq (iota "i1") (plus (iota "i0") (int 1))
            , rel GtEq (iota "i0") (int 0)
            ]
        engine facts goal = testAssertTrue (Engine.entails goal (Engine.proofContextFromFacts facts))
        engineNot facts goal = testAssertTrue (not (Engine.entails goal (Engine.proofContextFromFacts facts)))
     in testCaseSeq
            "testForallGrownList"
            [ -- Old elements come from the old fact, the new one from its own, and the cases are told apart
              engine grown (forallJ (iota "i1") (copiesA (iota "out1")))
            , -- The old range alone still holds for the new list
              engine grown (forallJ (iota "i0") (copiesA (iota "out1")))
            , -- Not past the new element
              engineNot grown (forallJ (plus (iota "i1") (int 1)) (copiesA (iota "out1")))
            , -- Without the new element's fact, or without the old elements', it does not hold
              engineNot (filter (/= (grown !! 3)) grown) (forallJ (iota "i1") (copiesA (iota "out1")))
            , engineNot (filter (/= head grown) grown) (forallJ (iota "i1") (copiesA (iota "out1")))
            , engineNot (filter (/= (grown !! 1)) grown) (forallJ (iota "i1") (copiesA (iota "out1")))
            , -- Without knowing the old size is i0, the new element is not at the end of the range
              engineNot (filter (/= (grown !! 2)) grown) (forallJ (iota "i1") (copiesA (iota "out1")))
            ]

-- x != y is a fact, and c * x for a constant c is related to the terms it is made from by the difference constraints
testRefinedArithmetic :: Test
testRefinedArithmetic =
    let given facts goal = "fn f(i: Int, j: Int, n: Int, m: Int) -> Int [{ " ++ facts ++ " }] [{ }] { affirm " ++ goal ++ "; return 0; };"
        holds facts goal = parseValidProgramHelper (given facts goal)
        fails facts goal = parseValidateFailProgramHelper (given facts goal) ("Could not prove: " ++ goal)
     in testCaseSeq
            "testRefinedArithmetic"
            [ -- x != y with x <= y is x < y, also next to a constant
              holds "affirm i >= -3; affirm i != -3;" "i > -3"
            , holds "affirm i <= n; affirm i != n;" "i < n"
            , holds "affirm i <= n; affirm i != n;" "i + 1 <= n"
            , holds "affirm n >= i; affirm n != i;" "i < n"
            , holds "affirm i < n; affirm i != n;" "i < n"
            , fails "affirm i <= 5; affirm i != 3;" "i < 3"
            , fails "affirm i != n;" "i < n"
            , holds "affirm i != n; affirm i <= n; affirm n <= i;" "j = j + 1"
            , -- A loop that stops at a value other than its bound
              parseValidProgramHelper "i = 5; while i != 0 [{ affirm i >= 0; }] shrinks i { i = i - 1; }; affirm i = 0;"
            , parseValidProgramHelper "i = 5; while i != -3 [{ affirm i >= -3; }] shrinks i + 3 { i = i - 1; };"
            , -- c * x for a positive or negative constant
              holds "affirm n > 0;" "2 * n > 0"
            , holds "affirm n > 0;" "n * 2 > 0"
            , holds "affirm n >= 1;" "3 * n >= 3"
            , holds "affirm n > 2;" "n * 3 > 6"
            , fails "affirm n >= 0;" "2 * n > 0"
            , fails "affirm n >= 1;" "3 * n > 3"
            , holds "affirm n < 0;" "-2 * n > 0"
            , fails "affirm n <= 0;" "-2 * n > 0"
            , holds "affirm n < m;" "2 * n < 2 * m"
            , holds "affirm n < m;" "2 * n < 2 * m - 1"
            , fails "affirm n < m;" "2 * n < 2 * m - 2"
            , holds "affirm n <= m;" "3 * n <= 3 * m"
            , fails "affirm n <= m;" "2 * n < 2 * m"
            , holds "affirm n < m;" "-2 * m < -2 * n"
            , -- Different constants are different terms
              fails "affirm n < m;" "2 * n < 3 * m"
            , -- A variant that is twice a counter
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks 2 * n { if n < 1 { return 0; } else { return f(n - 1); }; }; x = f(3);"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks 2 * n { if n < 1 { return 0; } else { return f(n + 1); }; }; x = f(3);" "Recursive call does not shrink the variant"
            ]

-- x % c is the remainder of x / c, which rounds down: it has the sign of the divisor
testModulo :: Test
testModulo =
    let given facts goal = "fn f(i: Int, j: Int, n: Int, m: Int) -> Int [{ " ++ facts ++ " }] [{ }] { affirm " ++ goal ++ "; return 0; };"
        holds facts goal = parseValidProgramHelper (given facts goal)
        fails facts goal = parseValidateFailProgramHelper (given facts goal) ("Could not prove: " ++ goal)
     in testCaseSeq
            "testModulo"
            [ -- Evaluation: the remainder has the sign of the divisor, and x = (x / c) * c + x % c
              parseEvalProgramHelper "return 7 % 3;" (Just (VInt 1))
            , parseEvalProgramHelper "return -7 % 3;" (Just (VInt 2))
            , parseEvalProgramHelper "return 7 % -3;" (Just (VInt (-2)))
            , parseEvalProgramHelper "return -7 % -3;" (Just (VInt (-1)))
            , parseEvalProgramHelper "return 2 + 7 % 4 * 3;" (Just (VInt 11))
            , parseEvalProgramHelper "x = 17; return (x / 5) * 5 + x % 5;" (Just (VInt 17))
            , parseEvalProgramFailHelper "x = 0; return 5 % x;" "Modulo by zero"
            , -- By a known constant
              holds "affirm n = n;" "n % 4 >= 0"
            , holds "affirm n = n;" "n % 4 < 4"
            , holds "affirm n = n;" "n % -4 <= 0"
            , holds "affirm n = n;" "n % -4 > -4"
            , fails "affirm n = n;" "n % 4 < 3"
            , fails "affirm n = n;" "n % 4 > 0"
            , holds "affirm n % 2 = 1;" "n != 0"
            , holds "affirm n >= 0; affirm n < 4;" "n % 4 = n"
            , holds "affirm n >= 0; affirm n < 4;" "n % 8 = n"
            , fails "affirm n >= 0; affirm n < 9;" "n % 8 = n"
            , holds "affirm n = m + 4;" "n % 4 = m % 4"
            , fails "affirm n = m + 3;" "n % 4 = m % 4"
            , holds "affirm n % 2 = 0; affirm m % 2 = 0;" "(n + m) % 2 = 0"
            , holds "affirm n % 2 = 1; affirm m % 2 = 1;" "(n + m) % 2 = 0"
            , fails "affirm n % 2 = 1; affirm m % 2 = 0;" "(n + m) % 2 = 0"
            , holds "affirm n = n;" "n = n / 3 * 3 + n % 3"
            , -- Two remainders that are equal have a quotient each: x % 2 = 0 and y % 3 = 0 do not relate x and y
              fails "affirm n % 2 = 0; affirm m % 3 = 0;" "3 * n = 2 * m"
            , parseValidateFailProgramHelper "fn f(n: Int, m: Int) -> Int [{ affirm n % 2 = 0; affirm m % 3 = 0; affirm n = 4; affirm m = 3; }] [{ }] { affirm 0 = 1; return 0; };" "Could not prove: 0 = 1"
            , -- With the division of the same number
              holds "affirm n >= 0;" "n / 4 * 4 <= n"
            , holds "affirm n >= 0; affirm n % 4 = 0;" "n / 4 * 4 = n"
            , -- By a variable that is known to be positive (or negative)
              holds "affirm m > 0;" "n % m >= 0"
            , holds "affirm m > 0;" "n % m < m"
            , holds "affirm m < 0;" "n % m <= 0"
            , holds "affirm m < 0;" "n % m > m"
            , fails "affirm m >= 0;" "n % m < m"
            , -- The divisor must be known to be non-zero, as for /
              parseValidateFailProgramHelper "fn f(x: Int, y: Int) -> Int { return x % y; };" "Funct input validation failed"
            , -- A ring index wraps around
              parseValidProgramHelper "fn next(i: Int, n: Int) -> Int [{ affirm n > 0; affirm i >= 0; }] [{ affirm return >= 0; affirm return < n; }] { return (i + 1) % n; }; fn at(l: List<Int>, i: Int) -> Int [{ affirm size(l) > 0; affirm i >= 0; }] { return get(l, i % size(l)); }; x = at([5, 6, 7], next(2, 3));"
            , parseValidProgramHelper "fn at(l: List<Int>, i: Int) -> Int [{ affirm size(l) > 0; }] { return get(l, i % size(l)); }; x = at([5, 6], -3);"
            , parseValidateFailProgramHelper "fn at(l: List<Int>, i: Int) -> Int { return get(l, i % size(l)); }; x = 0;" "Funct input validation failed"
            ]

-- Sums of variables, multiples and division by a constant are solved together as linear arithmetic
testLinearArithmetic :: Test
testLinearArithmetic =
    let given facts goal = "fn f(i: Int, j: Int, n: Int, m: Int) -> Int [{ " ++ facts ++ " }] [{ }] { affirm " ++ goal ++ "; return 0; };"
        holds facts goal = parseValidProgramHelper (given facts goal)
        fails facts goal = parseValidateFailProgramHelper (given facts goal) ("Could not prove: " ++ goal)
     in testCaseSeq
            "testLinearArithmetic"
            [ -- A sum bounded as a whole, or by its parts
              holds "affirm i + j = n; affirm i >= 0;" "j <= n"
            , holds "affirm i + j <= n; affirm j >= 0;" "i <= n"
            , fails "affirm i + j <= n;" "i <= n"
            , holds "affirm i + j = n; affirm i = m;" "j = n - m"
            , holds "affirm i < n; affirm j < m;" "i + j < n + m"
            , holds "affirm i <= n; affirm j < m;" "i + j < n + m"
            , fails "affirm i <= n; affirm j <= m;" "i + j < n + m"
            , holds "affirm i >= 1; affirm j >= 1;" "i + j >= 2"
            , fails "affirm i >= 1; affirm j >= 0;" "i + j >= 2"
            , holds "affirm i = 2; affirm j = 3;" "i + j = 5"
            , -- Several relations at once, which no single difference between two terms shows
              holds "affirm i + j <= 10; affirm i >= 4; affirm j >= 5;" "i <= 5"
            , fails "affirm i + j <= 10; affirm i >= 4; affirm j >= 4;" "i <= 5"
            , holds "affirm i + j + n = 0; affirm i >= 0; affirm j >= 0;" "n <= 0"
            , -- A multiple of a variable, with another variable
              holds "affirm 2 * i <= j; affirm i >= 1;" "j >= 2"
            , fails "affirm 2 * i <= j; affirm i >= 0;" "j >= 2"
            , holds "affirm i = i;" "i + i = 2 * i"
            , holds "affirm i + i = j;" "j = 2 * i"
            , holds "affirm 3 * i + 2 * j = 12; affirm i >= 0; affirm j >= 0;" "i <= 4"
            , -- Whole numbers only: 2 * i = 2 * j + 1 has no solution, and 2 * i <= 1 means i <= 0
              holds "affirm 2 * i <= 1;" "i <= 0"
            , holds "affirm 2 * i = 2 * j + 1;" "n = n + 1"
            , fails "affirm 3 * i <= 4;" "i <= 0"
            , -- Division by a constant rounds down
              holds "affirm n >= 0;" "n / 2 >= 0"
            , holds "affirm n > 0;" "n / 2 < n"
            , fails "affirm n >= 0;" "n / 2 < n"
            , holds "affirm n >= 0;" "n / 2 * 2 <= n"
            , holds "affirm n >= 0;" "n <= n / 2 * 2 + 1"
            , fails "affirm n >= 0;" "n <= n / 2 * 2"
            , holds "affirm n >= 4;" "n / 2 >= 2"
            , fails "affirm n >= 3;" "n / 2 >= 2"
            , holds "affirm n >= 0;" "n / 4 <= n / 2"
            , holds "affirm n >= 0; affirm n <= 9;" "n / 4 <= 2"
            , fails "affirm n >= 0; affirm n <= 12;" "n / 4 <= 2"
            , holds "affirm i < j;" "(i + j) / 2 < j"
            , holds "affirm i < j;" "(i + j) / 2 >= i"
            , fails "affirm i <= j;" "(i + j) / 2 < j"
            , -- Division by a negative constant rounds down too
              holds "affirm n > 0;" "n / -2 < 0"
            , fails "affirm n >= 0;" "n / -2 < 0"
            , -- Division by 1 is the number, and the result of a division is not assumed to be a multiple
              holds "affirm i = i;" "n / 1 = n"
            , fails "affirm n >= 0;" "n / 2 * 2 = n"
            , parseValidateFailProgramHelper "x = -9223372036854775808 / -1; affirm x > 0;" "Could not prove: x > 0"
            , parseValidProgramHelper "x = -9223372036854775808 % -1; affirm x = 0;"
            , -- Evaluation
              parseEvalProgramHelper "x = 7; y = x / 2 + x / -2; return y;" (Just (VInt (-1)))
            , -- Programs: a loop that moves from one variable to another keeps their sum
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n; }] { s = 0; i = n; while i > 0 [{ affirm i >= 0; }] shrinks i { s = s + 1; i = i - 1; }; return s; };"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n; }] { s = 0; i = n; while i > 0 [{ affirm s + i = n; affirm i >= 0; }] shrinks i { s = s + 1; i = i - 1; }; return s; };"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n + 5; }] { s = 5; i = n; while i > 0 [{ affirm i >= 0; }] shrinks i { s = s + 1; i = i - 1; }; return s; };"
            , parseValidProgramHelper "s = 0; i = 5; while i > 0 [{ affirm i >= 0; }] shrinks i { s = s + 1; i = i - 1; }; affirm s = 5;"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n; }] { s = 0; i = n; while i > 0 [{ affirm i >= 0; }] shrinks i { s = s + 2; i = i - 1; }; return s; };" "Could not prove: return = n"
            , -- Halving shrinks a number that is at least 1, but not one that is at least 0
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { if n < 1 { return 0; } else { return 1 + f(n / 2); }; }; x = f(9);"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { return f(n / 2); }; x = f(9);" "Recursive call does not shrink the variant"
            , -- A loop that halves
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; c = 0; while i > 0 [{ affirm i >= 0; }] shrinks i { i = i / 2; c = c + 1; }; return c; };"
            , -- size(l) >= 0 is part of the linear system
              parseValidProgramHelper "fn f(i: Int, l: List<Int>) -> Int [{ }] [{ affirm return >= i; }] { return i + size(l); };"
            , parseValidateFailProgramHelper "fn f(i: Int, l: List<Int>) -> Int [{ }] [{ affirm return > i; }] { return i + size(l); };" "Could not prove: return > i"
            , -- Sums of terms never push the distances out of the candidates: the last pair keeps its distance with six terms
              parseValidProgramHelper "p = 0; q = 0; r = 0; s = 0; x = 0; y = 5; while p < 3 [{ affirm p <= 3; }] shrinks 3 - p { p = p + 1; q = q + 2; r = r + 3; s = s + 4; x = x + 1; y = y + 1; }; affirm y = x + 5;"
            , -- A variant that is a sum, or a difference whose two sides both move
              parseValidProgramHelper "fn f(n: Int, m: Int) -> Int [{ affirm n >= 0; affirm m >= 0; }] { i = n; j = m; while i + j > 0 [{ affirm i >= 0; affirm j >= 0; }] shrinks i + j { old = i + j; if i > 0 { i = i - 1; affirm i >= 0; affirm j >= 0; affirm i + j < old; } else { j = j - 1; affirm i >= 0; affirm j >= 0; affirm i + j < old; }; }; return 0; }; x = f(2, 3);"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = 0; k = n; while i + 1 < k [{ affirm i >= 0; affirm i <= k; }] shrinks k - i { i = i + 1; k = k - 1; }; return 0; }; x = f(7);"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = 0; k = n; while i + 1 < k [{ affirm i >= 0; affirm i <= k; }] shrinks k - i { i = i + 1; k = k + 1; }; return 0; };" "Loop variant does not shrink"
            , -- Binary search: the middle is between the ends, so the range narrows
              parseValidProgramHelper "fn f(secret: Int) -> Int [{ affirm secret >= 0; affirm secret <= 1000; }] [{ affirm return = secret; }] { lo = 0; hi = 1000; while lo < hi [{ affirm lo <= secret; affirm secret <= hi; }] shrinks hi - lo { width = hi - lo; mid = (lo + hi) / 2; if mid < secret { lo = mid + 1; affirm lo <= secret; affirm hi - lo < width; } else { hi = mid; affirm secret <= hi; affirm hi - lo < width; }; }; return lo; }; x = f(617);"
            , parseValidateFailProgramHelper "fn f(secret: Int) -> Int [{ affirm secret >= 0; affirm secret <= 1000; }] { lo = 0; hi = 1000; while lo < hi [{ affirm lo <= secret; affirm secret <= hi; }] shrinks hi - lo { width = hi - lo; mid = (lo + hi) / 2; if mid < secret { lo = mid; affirm hi - lo < width; } else { hi = mid; affirm hi - lo < width; }; }; return lo; };" "Could not prove: hi - lo < width"
            ]

-- The validator keeps a solver of the visible facts between questions, and uses it only while it holds nothing the
-- state has lost
testSolverCache :: Test
testSolverCache =
    testCaseSeq
        "testSolverCache"
        [ -- A fact assumed in a branch is not visible after the if, though the branch has been validated before the question
          parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ }] [{ }] { a = 0; affirm n = n; if n > 7 { affirm n > 7; a = 1; } else { a = 2; }; affirm n > 7; return a; };" "Could not prove: n > 7"
        , parseValidProgramHelper "fn f(n: Int) -> Int [{ }] [{ }] { a = 0; if n > 7 { affirm n > 7; a = 1; } else { a = 2; }; affirm n = n; return a; };"
        , -- Facts from before the if are still visible after it
          parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n > 3; }] [{ }] { a = 0; affirm n >= 3; if n > 7 { a = 1; } else { a = 2; }; affirm n > 2; return a; };"
        , -- The same for a loop: what the body assumes is gone after it
          parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { affirm i < n; i = i + 1; }; affirm i < n; return i; };" "Could not prove: i < n"
        , -- Facts about a list built by many calls
          parseValidProgramHelper "l = []; l = push(l, 1); affirm size(l) = 1; l = push(l, 2); affirm size(l) = 2; l = push(l, 3); affirm get(l, 0) = 1; affirm get(l, 2) = 3; affirm size(l) = 3;"
        , parseValidateFailProgramHelper "l = []; l = push(l, 1); affirm size(l) = 1; l = push(l, 2); affirm size(l) = 3;" "Could not prove: size(l) = 3"
        ]

testListProofs :: Test
testListProofs =
    let node = "struct Node { value: Int, prev: Int, next: Int };"
        nonNegative l = "affirm forall i in 0..size(" ++ l ++ "): get(" ++ l ++ ", i) >= 0;"
     in testCaseSeq
            "testListProofs"
            [ -- Case splits on the guards that block a forall: the index set by one update, then another
              parseValidProgramHelper ("fn f(l: List<Int>, p: Int, q: Int) -> List<Int> [{ affirm p >= 0; affirm p < size(l); affirm q >= 0; affirm q < size(l); " ++ nonNegative "l" ++ " }] [{ " ++ nonNegative "return" ++ " }] { out = set(l, p, 5); out = set(out, q, 6); return out; };")
            , parseValidateFailProgramHelper ("fn f(l: List<Int>, p: Int, q: Int) -> List<Int> [{ affirm p >= 0; affirm p < size(l); affirm q >= 0; affirm q < size(l); " ++ nonNegative "l" ++ " }] [{ " ++ nonNegative "return" ++ " }] { out = set(l, p, 5); out = set(out, q, 0 - 6); return out; };") "Could not prove: forall i in 0..size(return): get(return, i) >= 0"
            , -- The two updates may hit the same element, and the new element at the end is told apart too
              parseValidProgramHelper ("fn f(l: List<Int>, p: Int, q: Int) -> List<Int> [{ affirm p >= 0; affirm p < size(l); affirm q >= 0; affirm q < size(l); " ++ nonNegative "l" ++ " }] [{ " ++ nonNegative "return" ++ " }] { out = push(l, 1); out = set(out, p, 5); out = set(out, q, 6); return out; };")
            , parseValidateFailProgramHelper ("fn f(l: List<Int>, p: Int, q: Int) -> List<Int> [{ affirm p >= 0; affirm p < size(l); affirm q >= 0; affirm q < size(l); " ++ nonNegative "l" ++ " }] [{ " ++ nonNegative "return" ++ " }] { out = push(l, 0 - 1); out = set(out, p, 5); out = set(out, q, 6); return out; };") "Could not prove: forall i in 0..size(return): get(return, i) >= 0"
            , -- Struct fields: the links stay in range through a push and two updates
              parseValidProgramHelper (node ++ "fn f(nodes: List<Node>, p: Int, v: Int) -> List<Node> [{ affirm size(nodes) > 0; affirm p >= 0; affirm p < size(nodes); affirm forall i in 0..size(nodes): get(nodes, i).next >= 0; affirm forall i in 0..size(nodes): get(nodes, i).next < size(nodes); }] [{ affirm forall i in 0..size(return): get(return, i).next >= 0; affirm forall i in 0..size(return): get(return, i).next < size(return); }] { q = get(nodes, p).next; n = size(nodes); out = push(nodes, Node { value: v, prev: p, next: q }); out = set(out, p, Node { next: n, ..get(out, p) }); out = set(out, q, Node { prev: n, ..get(out, q) }); return out; };")
            , parseValidateFailProgramHelper (node ++ "fn f(nodes: List<Node>, p: Int, v: Int) -> List<Node> [{ affirm size(nodes) > 0; affirm p >= 0; affirm p < size(nodes); affirm forall i in 0..size(nodes): get(nodes, i).next >= 0; affirm forall i in 0..size(nodes): get(nodes, i).next < size(nodes); }] [{ affirm forall i in 0..size(return): get(return, i).next < size(return); }] { q = get(nodes, p).next; n = size(nodes); out = push(nodes, Node { value: v, prev: p, next: n + 1 }); return out; };") "Could not prove: forall i in 0..size(return): get(return, i).next < size(return)"
            , -- A disequality is the same in both directions
              parseValidProgramHelper "fn f(a: Int, b: Int) -> Int [{ affirm a != b; }] [{ }] { affirm b != a; return 0; };"
            ]

testMulDivNegative :: Test
testMulDivNegative =
    testCaseSeq
        "testMulDivNegative"
        [ -- Evaluation: `*` and `/` bind tighter than the other infix operators, and `/` rounds down
          parseEvalProgramHelper "return 2 + 3 * 4;" (Just (VInt 14))
        , parseEvalProgramHelper "return 2 * 3 + 4 * 5 - 6 / 4;" (Just (VInt 25))
        , parseEvalProgramHelper "return 7 / 2 * 2;" (Just (VInt 6))
        , parseEvalProgramHelper "return (0 - 7) / 2;" (Just (VInt (-4)))
        , parseEvalProgramHelper "return -7 / 2;" (Just (VInt (-4)))
        , parseEvalProgramHelper "return 3 - -2;" (Just (VInt 5))
        , parseEvalProgramHelper "x = 4; return x-1;" (Just (VInt 3))
        , parseEvalProgramHelper "l = [-1, 2, -3]; return get(l, 2);" (Just (VInt (-3)))
        , parseEvalProgramFailHelper "return 1 / 0;" "Division by zero"
        , -- Validation: constants fold, `* 1` and `/ 1` keep their operand, other products are opaque
          parseValidProgramHelper "x = 3; y = x * 4; affirm y = 12; z = y / 5; affirm z = 2;"
        , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n * 1; }; x = f(3);"
        , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return = 0; }] { return n * 0; }; x = f(3);"
        , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n * 2; }; x = f(3);"
        , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return > 0; }] { return n * 2; }; x = f(3);" "Could not prove: return > 0"
        , parseValidateFailProgramHelper "x = 3; y = x + -1; affirm y = 3;" "Could not prove: y = 3"
        , -- Division needs a divisor known to be non-zero
          parseValidProgramHelper "fn f(a: Int, b: Int) -> Int [{ affirm b != 0; }] [{ }] { return a / b; }; x = f(8, 2);"
        , parseValidProgramHelper "fn f(a: Int, b: Int) -> Int [{ affirm b < 0; }] [{ }] { return a / b; }; x = f(8, -2);"
        , parseValidateFailProgramHelper "fn f(a: Int, b: Int) -> Int [{ }] [{ }] { return a / b; }; x = f(8, 2);" "Relation lacks a proof"
        , parseValidateFailProgramHelper "x = 3 / 0;" "Relation does not hold"
        , -- Proofs print with the same precedence
          parseValidateFailProgramHelper "x = 2; affirm x * (x + 1) = 5;" "Could not prove: x * (x + 1) = 5"
        ]

testPrettyProofs :: Test
testPrettyProofs =
    testCaseSeq
        "testPrettyProofs"
        [ -- Failed assertions are reported in source syntax rather than as a raw AST
          parseValidateFailProgramHelper "x = 1; affirm x < 4; affirm x = 2;" "Could not prove: x = 2"
        , parseValidateFailProgramHelper "l = [1, 2]; affirm size(l) + 1 = 4;" "Could not prove: size(l) + 1 = 4"
        , parseValidateFailProgramHelper "x = 1; affirm x - (1 - 1) != 1;" "Could not prove: x - (1 - 1) != 1"
        , parseValidateFailProgramHelper "l = [1, 2]; affirm forall j in 0..size(l): get(l, j) = 0;" "Could not prove: forall j in 0..size(l): get(l, j) = 0"
        , parseValidateFailProgramHelper "l = [1, 2]; affirm forall j where j > 0: get(l, j) = 0;" "Could not prove: forall j where j > 0: get(l, j) = 0"
        , case parseStatementBlock "l = [1]; affirm 1 = 2;" of
            Right stmts -> case validateStatements stmts of
                Error e | "FApp" `isInfixOf` e || "VFunct" `isInfixOf` e -> Just $ "Raw AST in error: " ++ e
                _ -> Nothing
            Left err -> Just (show err)
        ]

testForallLoops :: Test
testForallLoops =
    let copyLoop invariant element = loopWith "get(a, j)" invariant element
        -- the output contract says every element of the result is `claim`
        loopWith claim invariant element =
            "fn copy(a: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(a); affirm forall j in 0..size(a): get(return, j) = " ++ claim ++ "; }] {\
            \  n = size(a); i = 0; out = [];\
            \  while i < n [{ affirm i >= 0; affirm i <= n; affirm size(out) = i; "
                ++ invariant
                ++ " }] shrinks n - i { out = push(out, "
                ++ element
                ++ "); i = i + 1; };\
                   \  return out; };"
        copyInvariant = "affirm forall j in 0..i: get(out, j) = get(a, j);"
     in testCaseSeq
            "testForallLoops"
            [ -- A list built element by element: the invariant covers the elements so far
              parseValidProgramHelper (copyLoop copyInvariant "get(a, i)")
            , parseValidProgramHelper (loopWith "(get(a, j) + 1)" "affirm forall j in 0..i: get(out, j) = (get(a, j) + 1);" "get(a, i) + 1")
            , -- Rejected: the element pushed is not the one the invariant claims
              parseValidateFailProgramHelper (copyLoop copyInvariant "get(a, i) + 1") "Loop invariant is not preserved"
            , parseValidateFailProgramHelper (loopWith "(get(a, j) + 1)" "affirm forall j in 0..i: get(out, j) = (get(a, j) + 1);" "get(a, i)") "Loop invariant is not preserved"
            , -- Rejected: the invariant covers one element too many on entry
              parseValidateFailProgramHelper (copyLoop "affirm forall j in 0..(i + 1): get(out, j) = get(a, j);" "get(a, i)") "Loop invariant does not hold on entry"
            , -- Without the forall in the invariant the output contract's forall cannot be proved
              parseValidateFailProgramHelper (copyLoop "" "get(a, i)") "Could not prove"
            , -- A call nested in an argument keeps its link to the caller's variables
              parseValidProgramHelper
                "fn g(l: List<Int>, i: Int) -> List<Int> [{ affirm i >= 0; affirm i < size(l); }] [{ }] { y = push(l, get(l, i)); affirm get(y, size(l)) = get(l, i); return y; };"
            , parseValidateFailProgramHelper
                "fn g(l: List<Int>, i: Int, k: Int) -> List<Int> [{ affirm i >= 0; affirm i < size(l); affirm k >= 0; affirm k < size(l); }] [{ }] { y = push(l, get(l, i)); affirm get(y, size(l)) = get(l, k); return y; };"
                "Could not prove"
            , parseValidProgramHelper
                "fn g(l: List<Int>, i: Int) -> List<Int> [{ affirm i >= 0; affirm i < size(l); }] [{ }] { y = push(l, get(l, i) + 1); affirm get(y, size(l)) = (get(l, i) + 1); return y; };"
            , -- The elementwise contract reaches the caller
              parseValidProgramHelper
                ( copyLoop copyInvariant "get(a, i)"
                    ++ "b = [4, 5, 6]; c = copy(b); affirm get(c, 1) = get(b, 1); affirm forall j in 0..size(b): get(c, j) = get(b, j);"
                )
            ]

zeroAxiom :: String
zeroAxiom = "axiom zeros(l) [{ }] [{ affirm forall j in 0..size(l): get(l, j) = 0; }];"

testForallSyntax :: Test
testForallSyntax =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        getProof l t = FApp (CTerm (builtinFunct Get)) [l, t]
        parseAffirm source expected =
            case parseStatementBlock source of
                Left err -> Just $ "Parse failed: " ++ show err
                Right stmts -> testAssertEq stmts [ValidationStatement (ProofAssert expected)]
        parseFails source =
            case parseStatementBlock source of
                Left _ -> Nothing
                Right stmts -> Just $ "Expected a parse error, got: " ++ show stmts
        body = rel Eq (getProof (ATerm "l") (BVar "j")) (CTerm (VInt 0))
     in testCaseSeq
            "testForallSyntax"
            [ -- The range form is shorthand for a lower and an upper guard
              parseAffirm
                "affirm forall j in 0..n: get(l, j) = 0;"
                (Forall "j" [rel GtEq (BVar "j") (CTerm (VInt 0)), rel Lt (BVar "j") (ATerm "n")] body)
            , parseAffirm
                "affirm forall j where j >= 0, j < n: get(l, j) = 0;"
                (Forall "j" [rel GtEq (BVar "j") (CTerm (VInt 0)), rel Lt (BVar "j") (ATerm "n")] body)
            , -- The range bounds may be expressions, and the guards may use any relation
              parseAffirm
                "affirm forall j in 0..(n + 1): get(l, j) = 0;"
                ( Forall
                    "j"
                    [ rel GtEq (BVar "j") (CTerm (VInt 0))
                    , rel Lt (BVar "j") (FApp (CTerm (builtinFunct Plus)) [ATerm "n", CTerm (VInt 1)])
                    ]
                    body
                )
            , parseAffirm
                "affirm forall j where j != 2: get(l, j) = 0;"
                (Forall "j" [rel NotEq (BVar "j") (CTerm (VInt 2))] body)
            , -- Only the index is bound: other names stay ordinary variables
              parseAffirm
                "affirm forall k where k < j: get(l, k) = j;"
                ( Forall
                    "k"
                    [rel Lt (BVar "k") (ATerm "j")]
                    (rel Eq (getProof (ATerm "l") (BVar "k")) (ATerm "j"))
                )
            , -- It is allowed in contracts and invariants too
              case parseStatementBlock "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm forall j in 0..size(return): get(return, j) = 0; }] { return l; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right _ -> Nothing
            , case parseStatementBlock "i = 0; while i < 3 [{ affirm forall j in 0..i: j < 3; }] { i = i + 1; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right _ -> Nothing
            , -- Malformed or unsupported forms
              parseFails "affirm forall j in 0..n get(l, j) = 0;"
            , parseFails "affirm forall j: get(l, j) = 0;"
            , parseFails "affirm forall in 0..n: 1 = 1;"
            , parseFails "affirm forall j in 0..n: forall k in 0..n: get(l, j) = get(l, k);"
            , -- A name that merely starts with forall is still an ordinary variable
              case parseStatementBlock "forallx = 1;" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right stmts -> testAssertEq stmts [Assign "forallx" (Val (VInt 1))]
            , -- Evaluation ignores validation statements, so a program with forall still runs
              parseEvalProgramHelper "affirm forall j in 0..2: j < 2; return 5;" (Just (VInt 5))
            , -- A forall that holds for every index in its range is accepted, and one that does not is rejected
              parseValidProgramHelper "affirm forall j in 0..3: j < 3;"
            , parseValidateFailProgramHelper "affirm forall j in 0..3: j < 2;" "Could not prove"
            , parseValidProgramHelper "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm forall j in 0..2: j < 2; }] { return l; };"
            , parseValidateFailProgramHelper "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm forall j in 0..3: j < 2; }] { return l; };" "Could not prove"
            , parseValidProgramHelper "i = 0; while i < 3 [{ affirm forall j in 0..i: j < 3; }] shrinks 3 - i { i = i + 1; };"
            , parseValidateFailProgramHelper "i = 0; while i < 3 [{ affirm forall j in 0..i: j < 2; }] shrinks 3 - i { i = i + 1; };" "Loop invariant is not preserved"
            , -- A forall assumed by an axiom is kept as a fact, and is entailed again when it is the same forall
              parseValidProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall j in 0..size(a): get(a, j) = 0;")
            , -- The rule's argument is substituted into the forall
              parseValidProgramHelper (zeroAxiom ++ "a = [0, 0]; b = [0]; rewrite zeros a; rewrite zeros b; affirm forall j in 0..size(b): get(b, j) = 0;")
            , parseValidateFailProgramHelper (zeroAxiom ++ "a = [0, 0]; b = [0]; rewrite zeros a; affirm forall j in 0..size(b): get(b, j) = 0;") "Could not prove"
            , -- A range the fact does not cover, or another body, is not proved
              parseValidProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall j in 0..1: get(a, j) = 0;")
            , parseValidateFailProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall j in 0..3: get(a, j) = 0;") "Could not prove"
            , parseValidateFailProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall j in 0..size(a): get(a, j) = 1;") "Could not prove"
            , -- The name of the index does not matter
              parseValidProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall k in 0..size(a): get(a, k) = 0;")
            , -- Through a function: the input contract is checked at the call, and the output reaches the caller
              parseValidProgramHelper
                ( zeroAxiom
                    ++ "fn same(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ affirm forall j in 0..size(return): get(return, j) = 0; }] { return l; };\
                       \a = [0, 0]; rewrite zeros a; r = same(a); affirm forall j in 0..size(r): get(r, j) = 0;"
                )
            , parseValidateFailProgramHelper
                ( zeroAxiom
                    ++ "fn same(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ }] { return l; };\
                       \a = [0, 0]; r = same(a);"
                )
                "Could not prove"
            , -- A forall is not a rule argument
              parseValidateFailProgramHelper (zeroAxiom ++ "rewrite zeros forall j in 0..2: j < 2;") "cannot take a forall"
            , parseValidProgramHelper "x = 1; affirm x = 1;"
            ]

testEqualityByParts :: Test
testEqualityByParts =
    let point = "struct P { x: Int, y: Int };"
        shape = "enum S { A { v: Int }, B, C { w: Int, z: Bool } };"
     in testCaseSeq
            "testEqualityByParts"
            [ -- A struct is equal to another whose fields are all equal to its own, and differs from one with a field that differs
              parseValidProgramHelper (point ++ "fn f(a: &P, b: &P) -> Int [{ affirm a.x = b.x; affirm a.y = b.y; }] [{ }] { affirm a = b; return 1; };")
            , parseValidateFailProgramHelper (point ++ "fn f(a: &P, b: &P) -> Int [{ affirm a.x = b.x; }] [{ }] { affirm a = b; return 1; };") "Could not prove: a = b"
            , parseValidProgramHelper (point ++ "fn f(a: &P, b: &P) -> Int [{ affirm a.x != b.x; }] [{ }] { affirm a != b; return 1; };")
            , parseValidateFailProgramHelper (point ++ "fn f(a: &P, b: &P) -> Int [{ }] [{ }] { affirm a != b; return 1; };") "Could not prove: a != b"
            , -- Lists differ by their sizes or by an element, and are equal when their sizes are and every element is
              parseValidProgramHelper "fn f(a: &List<Int>, b: &List<Int>) -> Int [{ affirm size(a) != size(b); }] [{ }] { affirm a != b; return 1; };"
            , parseValidProgramHelper "fn f(a: &List<Int>, b: &List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(a); affirm i < size(b); affirm get(a, i) != get(b, i); }] [{ }] { affirm a != b; return 1; };"
            , parseValidProgramHelper "fn f(a: &List<Int>, b: &List<Int>) -> Int [{ affirm size(a) = size(b); affirm forall j in 0..size(a): get(a, j) = get(b, j); }] [{ }] { affirm a = b; return 1; };"
            , parseValidateFailProgramHelper "fn f(a: &List<Int>, b: &List<Int>) -> Int [{ affirm size(a) = size(b); affirm forall j in 0..size(a) - 1: get(a, j) = get(b, j); }] [{ }] { affirm a = b; return 1; };" "Could not prove: a = b"
            , -- The frame of a set leaves out the element it sets, so it does not make the list equal to the one it was set in
              parseValidateFailProgramHelper "fn f(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); }] [{ }] { m = set(l, i, 5); affirm m = l; return 1; };" "Could not prove: m = l"
            , -- Values known to be different variants differ, and a value that is none of the other variants is the one left
              parseValidProgramHelper (shape ++ "fn f(a: &S, b: &S) -> Int [{ affirm a is S::A; affirm b is S::B; }] [{ }] { affirm a != b; return 1; };")
            , parseValidProgramHelper (shape ++ "fn f(a: &S) -> Int { if a is S::A { return 0; }; if a is S::B { return 1; }; return (a as S::C).w; };")
            , -- A Bool that is the result of a comparison says the comparison holds, or does not: what Eq::eq promises
              parseValidProgramHelper (point ++ "fn same(a: &P, b: &P) -> Bool [{ }] [{ affirm return = (a = b); }] { if a.x != b.x { return false; }; if a.y != b.y { return false; }; return true; };")
            , parseValidateFailProgramHelper (point ++ "fn same(a: &P, b: &P) -> Bool [{ }] [{ affirm return = (a = b); }] { if a.x != b.x { return false; }; return true; };") "Could not prove: return = (a = b)"
            , parseValidProgramHelper (shape ++ "fn same(a: &S, b: &S) -> Bool [{ }] [{ affirm return = (a = b); }] { if a is S::A { if b is S::A { if (a as S::A).v != (b as S::A).v { return false; }; return true; }; return false; }; if a is S::B { if b is S::B { return true; }; return false; }; if b is S::C { if (a as S::C).w != (b as S::C).w { return false; }; if (a as S::C).z != (b as S::C).z { return false; }; return true; }; return false; };")
            , parseValidProgramHelper "fn same(a: &List<Int>, b: &List<Int>) -> Bool [{ }] [{ affirm return = (a = b); }] { if size(a) != size(b) { return false; }; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); affirm forall j in 0..i: get(a, j) = get(b, j); }] shrinks size(a) - i { if get(a, i) != get(b, i) { return false; }; i = i + 1; }; return true; };"
            , -- Two structs are equal when a field that is a list is equal by its elements and the other fields are
              parseValidProgramHelper "struct Q { n: Int, xs: List<Int> }; fn f(a: &Q, b: &Q) -> Int [{ affirm a.n = b.n; affirm size(a.xs) = size(b.xs); affirm forall j in 0..size(a.xs): get(a.xs, j) = get(b.xs, j); }] [{ }] { affirm a = b; return 1; };"
            , -- An element of a list that a value holds is a part of the value, so a function can call itself on one
              parseValidProgramHelper "enum R { Leaf, Node { kids: List<R> } }; fn count(r: &R) -> Int [{ }] [{ affirm return >= 0; }] shrinks r { if r is R::Node { if size((r as R::Node).kids) > 0 { return 1 + count(get((r as R::Node).kids, 0)); }; }; return 0; };"
            ]
