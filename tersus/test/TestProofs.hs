module TestProofs
    ( testForallInstantiation
    , testForallProof
    , testGoalSlices
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

import Data.List (isInfixOf, isPrefixOf)
import TestParserFragments
import Pipeline (validateStatements)
import StdLib
import Types
import Syntax
import Utils
import TestHarness


-- Shared table helpers for the arithmetic proof suites (formerly copy-pasted
-- as local given/holds/fails closures in each of the three suites).
proofGiven :: String -> String -> String
proofGiven facts goal = "fn f(i: Int, j: Int, n: Int, m: Int) -> Int [{ " ++ facts ++ " }] [{ }] { affirm " ++ goal ++ "; return 0; };"

proofHolds :: String -> String -> TestResult
proofHolds facts goal = parseValidProgramHelper (proofGiven facts goal)

proofFails :: String -> String -> TestResult
proofFails facts goal = parseValidateFailProgramHelper (proofGiven facts goal) ("Could not prove: " ++ goal)

-- forall parses into a bound index (BVar) with its guards, and the validator rejects it for now
-- forall facts are instantiated at the elements the program reads
testForallInstantiation :: Test
testForallInstantiation =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        getOf l t = FApp (CTerm (builtinFunct Get)) [l, t]
        sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        iota = ATerm . Iota
        int = CTerm . VInt
        -- reads element i of l under the contract that every element of l is 0
        reader = "fn f(l: List<Int>, i: Int) -> Int [{ affirm forall j in 0..size(l): get(l, j) = 0; rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] "
     in testCaseSeq
            "testForallInstantiation"
            [ -- Programs: the contract's forall gives the element a function reads
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

-- A check sees the facts near its goal within a work budget: a hub too heavy for a cheap
-- rung is left out, a fact appended after the block's first check is seen, and a long
-- derivation needs its intermediate steps affirmed within reach.
testGoalSlices :: Test
testGoalSlices =
    let offsets n = concat ["b" ++ show k ++ " = x + " ++ show k ++ "; " | k <- [0 .. n - 1]]
        guided spacing n = "fn f(a: List<Int>, x: Int) -> Int [{ affirm x >= 0; affirm x < 1000; }] [{ }] { salt = 0; z0 = x + 1; "
            ++ concat ["z" ++ show k ++ " = z" ++ show (k - 1) ++ " + 1; " ++ stone k | k <- [1 .. n]]
            ++ "affirm z" ++ show n ++ " > x; n0 = z" ++ show n ++ "; return n0; }; return f([1, 2, 3], 5);"
          where stone k = if k < n && (k + 1) `mod` spacing == 0 then "affirm z" ++ show k ++ " = x + " ++ show (k + 1) ++ "; " else ""
        hub goal = "fn h(x: Int, g: Int) -> Int [{ affirm g > x; }] [{ }] { " ++ offsets 48 ++ "affirm " ++ goal ++ "; return g; }; return h(1, 2);"
        branchHub goal = "fn h(x: Int, g: Int, c: Int) -> Int [{ affirm g > x; }] [{ }] { y = 0; if c > 0 { " ++ offsets 48 ++ "y = 1; } else { y = 2; }; affirm " ++ goal ++ "; return g; }; return h(1, 2, 3);"
        loopHub goal = "fn h(x: Int, g: Int, n: Int) -> Int [{ affirm g > x; affirm n >= 0; }] [{ }] { i = 0; while i < n [{ affirm i >= 0; affirm g > x; }] shrinks n - i { " ++ offsets 24 ++ "i = i + 1; }; affirm " ++ goal ++ "; return g; }; return h(1, 2, 3);"
        steps n = concat ["z" ++ show k ++ " = z" ++ show (k - 1) ++ " + 1; " ++ (if k `mod` 4 == 3 then "affirm z" ++ show k ++ " = x + " ++ show (k + 1) ++ "; " else "") | k <- [1 .. n]]
        branchStones goal = "fn s(x: Int, c: Int) -> Int [{ affirm x >= 0; affirm x < 1000; }] [{ }] { r = x; if c > 0 { z0 = x + 1; " ++ steps 16 ++ "affirm " ++ goal ++ "; r = z16; }; return r; }; return s(5, 1);"
        hubArm pre test = "fn f(x: Int) -> Int [{ affirm " ++ pre ++ "; affirm x < 1000; }] [{ affirm return = 1; }] { " ++ offsets 12 ++ "if " ++ test ++ " { return 2; }; return 1; }; return f(5);"
        wideParams = concat [", a" ++ show k ++ ": Int" | k <- [1 .. 40 :: Int]]
        wideArgs = concat [", a" ++ show k | k <- [1 .. 40 :: Int]]
        wide goal = "fn big(x: Int" ++ wideParams ++ ") -> Int { return x; }; fn w(x: Int, g: Int" ++ wideParams ++ ") -> Int [{ affirm g > x; }] [{ }] { y = big(x" ++ wideArgs ++ "); affirm " ++ goal ++ "; return g; }; return w(1, 2" ++ concat (replicate 40 ", 0") ++ ");"
        loopStones goal = "fn s(x: Int, n: Int) -> Int [{ affirm x >= 0; affirm x < 1000; affirm n >= 0; }] [{ }] { i = 0; while i < n [{ affirm i >= 0; }] shrinks n - i { z0 = x + 1; " ++ steps 16 ++ "affirm " ++ goal ++ "; i = i + 1; }; return i; }; return s(5, 2);"
     in testCaseSeq
            "testGoalSlices"
            [ -- a fact appended after the block's first check
              parseValidProgramHelper "fn f(x: Int) -> Int [{ affirm x > 0; }] [{ }] { affirm x > 0; y = x + 1; affirm y > 1; return y; }; return f(1);"
            , parseValidateFailProgramHelper "fn f(x: Int) -> Int [{ affirm x > 0; }] [{ }] { affirm x > 0; y = x + 1; affirm y > 2; return y; }; return f(1);" "Could not prove: y > 2"
            , -- reads checked against the bounds after an earlier check in the block
              parseValidProgramHelper "fn g(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); }] [{ }] { affirm i >= 0; x = get(l, i); y = get(l, i); affirm x = y; return x; }; return g([4], 0);"
            , parseValidateFailProgramHelper "fn g(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i <= size(l); }] [{ }] { affirm i >= 0; x = get(l, i); return x; }; return g([4], 0);" "Could not prove"
            , -- a scoped forall after a check, and its negative
              parseValidProgramHelper "fn f(l: List<Int>, n: Int) -> Int [{ affirm n >= 0; affirm n <= size(l); affirm forall j in 0..size(l): get(l, j) = 0; }] [{ }] { affirm n >= 0; affirm forall j in 0..n: get(l, j) = 0; return n; }; return f([0], 1);"
            , parseValidateFailProgramHelper "fn f(l: List<Int>, n: Int) -> Int [{ affirm n >= 0; affirm n <= size(l); affirm forall j in 0..size(l): get(l, j) = 0; }] [{ }] { affirm n >= 0; affirm forall j in 0..n: get(l, j) = 1; return n; }; return f([0], 1);" "Could not prove"
            , -- a hub the goal mentions, straight-line, after a branch and after a loop
              parseValidProgramHelper (hub "g > x")
            , parseValidateFailProgramHelper (hub "g > x + 1") "Could not prove"
            , parseValidProgramHelper (branchHub "g > x")
            , parseValidateFailProgramHelper (branchHub "g > x + 1") "Could not prove"
            , parseValidProgramHelper (loopHub "g > x")
            , parseValidateFailProgramHelper (loopHub "g > x + 1") "Could not prove"
            , -- a constant many facts mention, and a wide call next to the goal
              parseValidProgramHelper ("fn k(x: Int, a: Int) -> Int [{ affirm x >= 1; }] [{ }] { b0 = a + 1; " ++ concat ["b" ++ show k ++ " = b" ++ show (k - 1) ++ " + 1; " | k <- [1 .. 40 :: Int]] ++ "affirm x >= 1; return x; }; return k(1, 2);")
            , parseValidProgramHelper (wide "g > x")
            , parseValidateFailProgramHelper (wide "g > x + 1") "Could not prove"
            , -- stepping stones, each within reach of the one before
              parseValidProgramHelper (guided 4 32)
            , parseValidProgramHelper (guided 2 32)
            , parseValidateFailProgramHelper (replaceEnd (guided 4 32)) "Could not prove"
            , parseValidProgramHelper (branchStones "z16 > x")
            , parseValidateFailProgramHelper (branchStones "z16 > x + 17") "Could not prove"
            , parseValidProgramHelper (loopStones "z16 > x")
            , parseValidateFailProgramHelper (loopStones "z16 > x + 17") "Could not prove"
            , -- code after an assumption its nearby facts contradict is unreachable
              parseValidProgramHelper "affirm forall j in 3..3: 1 = 2;"
            , parseValidateFailProgramHelper "affirm forall j in 3..3: 1 = 2; affirm 1 = 2;" "Could not prove: 1 = 2"
            , parseValidProgramHelper "fn f(i: Int, j: Int, n: Int) -> Int [{ affirm i != n; affirm i <= n; affirm n <= i; }] [{ }] { affirm j = j + 1; return 0; };"
            , parseValidateFailProgramHelper "fn f(i: Int, j: Int) -> Int [{ affirm i < j; affirm j <= i + 1; }] [{ }] { affirm i = 7; return 0; };" "Could not prove: i = 7"
            , parseValidProgramHelper "enum Opt { None, Some { value: Int } };fn f(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ affirm return = 7; }] { return match o { Opt::None => 1, Opt::Some { value: v } => 7 }; };"
            , parseValidateFailProgramHelper "enum Opt { None, Some { value: Int } };fn f(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ affirm return = 7; }] { return match o { Opt::None => 1, Opt::Some { value: v } => 8 }; };" "Could not prove"
            , parseValidProgramHelper "fn f() -> Int [{ }] [{ affirm return = 0; }] { n = 0; while false [{ affirm n >= 0; }] shrinks n { return 5; }; affirm n = 0; return n; }; return f();"
            , parseValidateFailProgramHelper "fn f() -> Int [{ }] [{ affirm return = 5; }] { n = 0; while false [{ affirm n >= 0; }] shrinks n { return 5; }; affirm n = 0; return n; }; return f();" "Could not prove"
            , parseValidateFailProgramHelper "fn f(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return = 0; }] { flag = false; n = x; while flag || n > 0 [{ affirm flag = false; affirm n >= 0; }] shrinks n { return 5; }; return 0; }; return f(0);" "Could not prove"
            , -- an arm whose condition touches a hub too heavy for the first rung is still checked
              parseValidProgramHelper (hubArm "x >= 5" "x < 3")
            , parseValidateFailProgramHelper (hubArm "x >= 0" "x > 3") "Could not prove"
            , -- a goal between two literals sees the fact that links them
              parseValidProgramHelper "axiom five(x) [{ }] [{ affirm x = 5; }]; x = 0; rewrite five x; affirm x = 5;"
            ]
  where
    replaceEnd source = case breakOn source of (before, after) -> before ++ "affirm z32 > x + 33;" ++ drop (length goalText) after
    goalText = "affirm z32 > x;"
    breakOn haystack
        | null haystack || goalText `isPrefixOf` haystack = ([], haystack)
        | otherwise = let (b, a) = breakOn (tail haystack) in (head haystack : b, a)

-- forall goals are proved for an arbitrary index that meets the guards
testForallProof :: Test
testForallProof =
    testCaseSeq
        "testForallProof"
                    [ -- Programs
              parseValidProgramHelper "affirm forall j in 0..3: j >= 0;"
            , parseValidProgramHelper "n = 2; affirm forall j in 0..n: j < 2;"
            , parseValidateFailProgramHelper "n = 3; affirm forall j in 0..n: j < 2;" "Could not prove"
            , parseValidProgramHelper "affirm forall j in 3..3: 1 = 2;"
            , -- Nothing proved inside a forall check is kept, so an empty range proves nothing after it
              parseValidateFailProgramHelper "affirm forall j in 3..3: 1 = 2; affirm 1 = 2;" "Could not prove: 1 = 2"
            , parseValidateFailProgramHelper "fn f(x: Int) -> Int { n = 0; affirm forall j in 0..n: x > 5; affirm x > 5; return x; }; y = f(1);" "Could not prove: x > 5"
            , parseValidateFailProgramHelper "fn f(x: Int) -> Int { affirm forall j in 0..0: 10 / x >= 0; affirm x != 0; return x; }; y = f(1);" "Could not prove: x != 0"
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

-- x != y is a fact, and c * x for a constant c is related to the terms it is made from by the difference constraints
testRefinedArithmetic :: Test
testRefinedArithmetic =
    let holds = proofHolds
        fails = proofFails
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
    let holds = proofHolds
        fails = proofFails
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
            , parseValidateFailProgramHelper (proofGiven "affirm m >= 0;" "n % m < m") "Could not prove: an obligation could not be proved by the Tersus validator (in f, block 0, step 0)"
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
    let holds = proofHolds
        fails = proofFails
     in testCaseSeq
            "testLinearArithmetic"
            [ -- Bounds both ways make terms one only at a distance of 0: on a cycle of weight 0, the
              -- terms the same potential puts at one place
              holds "affirm i <= j; affirm j <= n; affirm n <= i;" "i = n"
            , fails "affirm i <= j; affirm j <= n + 1; affirm n <= i;" "i = n"
            , holds "affirm i >= 0; affirm i < 100; affirm n = i + 1; affirm m = i + 1;" "n = m"
            , fails "affirm i >= 0; affirm i < 100; affirm n = i + 1; affirm m = i + 2;" "n = m"
            , fails "affirm i >= 0; affirm i < 100; affirm n = i + 1;" "n = i"
            , -- A sum bounded as a whole, or by its parts
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
            , -- Integers are unbounded to the validator: the quotient is 2^63, and a run stops on the overflow first
              parseValidProgramHelper "x = -9223372036854775808 / -1; affirm x > 0;"
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
        readOverPush bounds affirmed argument =
            "fn f(l: &List<Int>, j: Int) -> Int [{ "
                ++ bounds
                ++ " }] [{ }] { assume get(l, j) = 5; a = push(clone(l), 7); affirm "
                ++ affirmed
                ++ "; return 0; };\nreturn f("
                ++ argument
                ++ ");\n"
        negativeIndex = "affirm size(l) = 0; affirm j < size(l);"
        rangeOverPush bounds affirmed argument =
            "fn f(b: &List<Int>, c: &List<Int>) -> Int [{ "
                ++ bounds
                ++ " }] [{ }] { a = push(clone(b), 7); affirm "
                ++ affirmed
                ++ "; return 0; };\nreturn f("
                ++ argument
                ++ ");\n"
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
            , -- A get written in a proof is a term with no bounds of its own, so
              -- a push does not carry it: this invariant holds on entry and is
              -- assumed of a list havoced to an unknown size, where the element
              -- the push defines (index size(l), which is 0 here) would
              -- otherwise contradict it and prove everything on that path --
              -- including that the divisor below is not zero, which it is.
              pipelineRejected "fn f() -> Int { l = [5]; i = 0; x = 9; while i < 2 [{ affirm i >= 0; affirm get(l, 0) = 5; }] shrinks 2 - i { if size(l) = 0 { a = push(clone(l), 7); x = 10 / (size(a) - 1); } else { l = pop(l); }; i = i + 1; }; return x; };\nreturn f();\n" "Could not prove: an obligation could not be proved by the Tersus validator"
            , -- A read the code made is in range, and a push keeps it: at an
              -- index that is a number, and at one that is only known to be
              -- between zero and the size
              parseValidProgramHelper "l = [4, 5]; v = get(l, 1); r = push(l, 9); affirm get(r, 1) = v; affirm get(r, 1) = 5;"
            , parseValidProgramHelper "fn f(l: List<Int>, j: Int) -> Int [{ affirm j >= 0; affirm j < size(l); }] [{ }] { v = get(l, j); r = push(l, 7); affirm get(r, j) = v; return 0; };"
            , -- The goal splitter is the third way a read crosses a push: it
              -- splits a read of the pushed list at the write index and
              -- elsewhere, and the elsewhere arm equates the read with a fresh
              -- read of the old list. That equation needs the index to be in
              -- the old list, so a ghost get below the old length whose sign is
              -- unknown, or known negative, does not reach it.
              pipelineRejected (readOverPush "affirm j < size(l);" "get(a, j) = 5" "[3], 0") "Could not prove: get(a, j) = 5"
            , pipelineRejected (readOverPush negativeIndex "get(a, j) = 5" "[], 0 - 1") "Could not prove: get(a, j) = 5"
            , -- and the refusal is a refusal, not a contradictory path: the
              -- opposite element value and a false equation stay unproved there
              pipelineRejected (readOverPush negativeIndex "get(a, j) = 6" "[], 0 - 1") "Could not prove: get(a, j) = 6"
            , pipelineRejected (readOverPush negativeIndex "1 = 2" "[], 0 - 1") "Could not prove: 1 = 2"
            , -- with the index proved to be in the old list, the same program passes
              pipelineValid (readOverPush "affirm j >= 0; affirm j < size(l);" "get(a, j) = 5" "[5], 0")
            , -- A fact that two lists agree over a range is used at a read of a
              -- push onto one of them, and its own lower bound is where that
              -- read's lower bound came from. A range that starts below zero
              -- gave one for free, so the index needs a bound of its own.
              pipelineRejected (rangeOverPush "affirm size(b) = 0; affirm forall i in (0 - 1)..size(b): get(c, i) = get(b, i);" "get(a, 0 - 1) = get(c, 0 - 1)" "[], []") "Could not prove: get(a, 0 - 1) = get(c, 0 - 1)"
            , pipelineRejected (rangeOverPush "affirm size(b) = 0; affirm forall i in (0 - 1)..size(b): get(c, i) = get(b, i);" "1 = 2" "[], []") "Could not prove: 1 = 2"
            , -- and over a range that starts at zero the read still crosses
              pipelineValid (rangeOverPush "affirm size(b) = 1; affirm forall i in 0..size(b): get(c, i) = get(b, i);" "get(a, 0) = get(c, 0)" "[4], [4]")
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
            , parseValidateFailProgramHelper (zeroAxiom ++ "fn f(a: List<Int>, b: List<Int>) -> Int { rewrite zeros a; affirm forall j in 0..size(b): get(b, j) = 0; return 0; };") "Could not prove"
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
                       \fn g(a: List<Int>) -> Int { r = same(a); return 0; };"
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
