module TestProofs
    ( testForallInstantiation
    , testForallProof
    , testRefinedArithmetic
    , testModulo
    , testLinearArithmetic
    , testSolverCache
    , testListProofs
    , testMulDivNegative
    , testPrettyProofs
    , testForallLoops
    , testForallSyntax
    ) where

import Data.List (isInfixOf)
import Parse
import Pipeline (validateStatements)
import StdLib
import TersusTypes
import Utils
import TestHarness

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
