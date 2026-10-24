module TestControl
    ( testCallsAndReturnJoin
    , testIfJoin
    , testForLoops
    , testInferredInvariants
    , testTermination
    , testCfgValidation
    ) where

import Parse
import TersusTypes
import TypeCheck
import Utils
import TestHarness

-- A call nested in an expression keeps its callee's output contract, and the join of an `if` tries the function's own
testCallsAndReturnJoin :: Test
testCallsAndReturnJoin =
    let one = "fn one(x: Int) -> Int [{ }] [{ affirm return > x; }] { return x + 1; }; "
     in testCaseSeq
            "testCallsAndReturnJoin"
            [ -- Nested calls
              parseValidProgramHelper (one ++ "fn f(y: Int) -> Int [{ }] [{ affirm return > y + 1; }] { return one(y) + 1; }; z = f(1);")
            , parseValidProgramHelper (one ++ "fn f(y: Int) -> Int [{ }] [{ affirm return > y + 1; }] { return one(one(y)); }; z = f(1);")
            , parseValidProgramHelper (one ++ "fn f(y: Int) -> Int [{ }] [{ affirm return > y; }] { x = 2 * one(y); affirm x > 2 * y; return y + 1; }; z = f(1);")
            , parseValidProgramHelper "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(l) + 2; }] { return push(push(l, 1), 2); }; z = f([1]);"
            , parseValidateFailProgramHelper (one ++ "fn f(y: Int) -> Int [{ }] [{ affirm return > y + 1; }] { return one(y); }; z = f(1);") "Could not prove: return > y + 1"
            , parseValidateFailProgramHelper "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(l) + 3; }] { return push(push(l, 1), 2); }; z = f([1]);" "Could not prove: size(return) = size(l) + 3"
            , parseValidProgramHelper "fn s(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] shrinks n { r = 0; if n < 1 { r = 0; } else { r = n + s(n - 1); }; return r; }; x = s(4);"
            , -- Returning paths: the output contract holds if every path entails it
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] { if n < 1 { return 1; } else { return n + 1; }; }; x = f(3);"
            , parseValidProgramHelper "fn s(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] shrinks n { if n < 1 { return 0; } else { return n + s(n - 1); }; }; x = s(4);"
            , parseValidProgramHelper "fn b(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= 0; }] shrinks n { if n < 1 { return 0; } else { return 1 + b(n / 2); }; }; x = b(9);"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] { if n < 1 { return 0; } else { return n - 1; }; }; x = f(3);" "Could not prove: return >= n"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] { if n < 1 { return -1; } else { return n + 1; }; }; x = f(3);" "Could not prove: return >= n"
            , -- A path that is not the end of the function
              parseValidProgramHelper "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] { if n < 1 { return 1; }; if c > 0 { return n + 1; } else { return n + 2; }; }; x = f(3, 1);"
            , -- An if that falls through, then a return
              parseValidProgramHelper "fn g(n: Int, c: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { r = n; if c > 0 { r = r + 1; } else { r = r + 2; }; return r; }; x = g(1, 2);"
            , parseValidateFailProgramHelper "fn g(n: Int, c: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { r = n; if c > 0 { r = r + 1; } else { r = r - 2; }; return r; }; x = g(1, 2);" "Could not prove: return > 0"
            , parseValidProgramHelper "fn g(n: Int, c: Int) -> Int [{ affirm n > 0; }] [{ affirm return > n; }] { r = n; if c > 0 { r = r + 1; } else { r = r + 2; }; if c > 5 { r = r + 1; }; return r; }; x = g(1, 2);"
            , -- What a rewrite in the contract needs is tried too: the check of a relation, a rule's input contract
              parseValidProgramHelper "fn f(c: Int) -> Int [{ }] [{ rewrite checkRel return > 0; affirm return > -5; }] { if c > 0 { return 1; } else { return 2; }; }; x = f(1);"
            , parseValidProgramHelper "fn f(c: Int) -> Int [{ }] [{ rewrite checkGtZero return; affirm return > -5; }] { if c > 0 { return 1; } else { return 2; }; }; x = f(1);"
            , parseValidProgramHelper "axiom posIsSmall(i) [{ affirm i > 0; }] [{ affirm i > -1; }]; fn f(c: Int) -> Int [{ }] [{ rewrite posIsSmall return; affirm return > -5; }] { if c > 0 { return 1; } else { return 2; }; }; x = f(1);"
            , parseValidateFailProgramHelper "axiom posIsSmall(i) [{ affirm i > 0; }] [{ affirm i > -1; }]; fn f(c: Int) -> Int [{ }] [{ rewrite posIsSmall return; affirm return > -5; }] { if c > 0 { return 1; } else { return 0; }; }; x = f(1);" "Rewrite rule posIsSmall input validation failed: Could not prove: return > 0"
            , parseValidProgramHelper "fn f(c: Int) -> Int [{ }] { x = 0; if c > 0 { x = 1; } else { x = 2; }; rewrite checkRel x > 0; return x; }; y = f(1);"
            , -- A loop that returns from inside, with the contract on both its returns
              parseValidProgramHelper "fn f(a: List<Int>) -> Int [{ }] [{ affirm return >= -1; affirm return < size(a); }] { for i in 0..size(a) { if get(a, i) > 2 { return i; }; }; return -1; }; x = f([1, 3]);"
            ]

-- The join of an `if` also tries what the program is about to need (see mergeStates in MirValidate.hs)
testIfJoin :: Test
testIfJoin =
    let fn' body = "fn f(c: Int, y: Int) -> Int [{ affirm y > 0; }] [{ }] { " ++ body ++ " return 0; };"
     in testCaseSeq
            "testIfJoin"
            [ -- An affirm after the if asks for a fact that both branches entail
              parseValidProgramHelper (fn' "x = 0; if c > 0 { x = 1; } else { x = 2; }; affirm x > 0;")
            , parseValidProgramHelper (fn' "x = 0; if c > 0 { x = 1; } else { x = 2; }; affirm x < 3; affirm x != 0;")
            , parseValidateFailProgramHelper (fn' "x = 0; if c > 0 { x = 1; } else { x = -1; }; affirm x > 0;") "Could not prove: x > 0"
            , parseValidateFailProgramHelper (fn' "x = 0; if c > 0 { x = 1; } else { x = 2; }; affirm x = 1;") "Could not prove: x = 1"
            , -- Facts from before the if about a variable it assigns, in terms of its new value
              parseValidProgramHelper (fn' "x = y; if c > 0 { x = x + 1; } else { x = x + 2; }; affirm x > 1;")
            , parseValidProgramHelper (fn' "x = y; if c > 0 { x = x + 1; } else { }; affirm x > 0;")
            , parseValidateFailProgramHelper (fn' "x = y; if c > 0 { x = x + 1; } else { x = 0; }; affirm x > 0;") "Could not prove: x > 0"
            , -- The branches' own facts still count, and so do the else branch's
              parseValidProgramHelper (fn' "x = 0; if c > 0 { x = 5; } else { x = 5; affirm x = 5; }; affirm x = 5;")
            , parseValidProgramHelper (fn' "x = 0; z = 0; if c > 0 { x = 1; z = 2; } else { x = 3; z = 4; }; affirm x < z;")
            , -- Nested ifs
              parseValidProgramHelper (fn' "x = 0; if c > 0 { if c > 5 { x = 2; } else { x = 1; }; } else { x = 3; }; affirm x > 0;")
            , -- A loop body does not have to restate the invariant or the variant in each branch
              parseValidProgramHelper "fn f(secret: Int) -> Int [{ affirm secret >= 0; affirm secret <= 1000; }] [{ affirm return = secret; }] { lo = 0; hi = 1000; while lo < hi [{ affirm lo <= secret; affirm secret <= hi; }] shrinks hi - lo { mid = (lo + hi) / 2; if mid < secret { lo = mid + 1; } else { hi = mid; }; }; return lo; }; x = f(617);"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; c = 0; while i > 0 [{ affirm i >= 0; affirm c >= 0; }] shrinks i { if i > 5 { i = i - 2; c = c + 1; } else { i = i - 1; }; }; return c; };"
            , parseValidateFailProgramHelper "fn f(secret: Int) -> Int [{ affirm secret >= 0; affirm secret <= 1000; }] { lo = 0; hi = 1000; while lo < hi [{ affirm lo <= secret; affirm secret <= hi; }] shrinks hi - lo { mid = (lo + hi) / 2; if mid < secret { lo = mid; } else { hi = mid; }; }; return lo; };" "Loop variant does not shrink"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; while i > 0 [{ affirm i >= 0; }] shrinks i { if i > 5 { i = i - 2; } else { i = i + 1; }; }; return 0; };" "Loop variant does not shrink"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; while i > 0 [{ affirm i >= 0; }] shrinks i { if i > 5 { i = i - 7; } else { i = i - 1; }; }; return 0; };" "Loop invariant is not preserved: Could not prove: i >= 0"
            , -- The same when the loop body returns, which ends its path with the loop end check
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { lo = 0; hi = n; while lo < hi [{ affirm lo <= hi; }] shrinks hi - lo { mid = (lo + hi) / 2; if mid > 100 { return mid; }; if mid < 7 { lo = mid + 1; } else { hi = mid; }; }; return lo; }; x = f(30);"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { lo = 0; hi = n; while lo < hi [{ affirm lo <= hi; }] shrinks hi - lo { mid = (lo + hi) / 2; if mid > 100 { return mid; }; if mid < 7 { lo = mid; } else { hi = mid; }; }; return lo; };" "Loop variant does not shrink"
            , -- A fact that needs a forall is not looked for, and is not wrongly kept
              parseValidateFailProgramHelper "fn f(a: List<Int>, c: Int) -> Int [{ affirm size(a) > 1; }] { l = a; if c > 0 { l = set(l, 0, 1); } else { l = set(l, 0, 2); }; affirm get(l, 0) = 1; return 0; };" "Could not prove: get(l, 0) = 1"
            ]

-- for i in lo..hi counts a loop variable, and the validator is given its bounds, its termination and (see
-- testInferredInvariants) what grows in step with it
testForLoops :: Test
testForLoops =
    let sumList = "fn total(a: List<Int>) -> Int { s = 0; for i in 0..size(a) { s = s + get(a, i); }; return s; };"
        parseFailsWith source expected = case parseStatementBlock source of
            Left err -> testAssertErrorContains expected (Error (show err) :: Result () String)
            Right _ -> Just ("Expected a parse error for: " ++ source)
     in testCaseSeq
            "testForLoops"
            [ -- Evaluation: the range is half open, hi is read once, and the variable is hi afterwards
              parseEvalProgramHelper "n = 0; for i in 0..4 { n = n + i; }; return n;" (Just (VInt 6))
            , parseEvalProgramHelper "n = 0; for i in 3..3 { n = n + 1; }; return n * 10 + i;" (Just (VInt 3))
            , parseEvalProgramHelper "n = 0; for i in 5..2 { n = n + 1; }; return n;" (Just (VInt 0))
            , parseEvalProgramHelper "l = [1, 2]; n = 0; for i in 0..size(l) { l = push(l, 0); n = n + 1; }; return n;" (Just (VInt 2))
            , parseEvalProgramHelper "n = 0; for i in 0..3 { for j in 0..i { n = n + 1; }; }; return n;" (Just (VInt 3))
            , parseEvalProgramHelper "fn f(l: List<Int>) -> Int { for i in 0..size(l) { if get(l, i) > 2 { return i; }; }; return -1; }; return f([1, 5]) + f([1]);" (Just (VInt 0))
            , parseEvalProgramHelper (sumList ++ "return total([1, 2, 3]);") (Just (VInt 6))
            , -- Validation: i is at least lo and below hi inside, so get is in range, and i = hi afterwards
              parseValidProgramHelper sumList
            , parseValidProgramHelper "n = 0; for i in 2..5 { n = n + i; }; affirm i = 5;"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int [{ affirm size(a) > 0; }] [{ }] { for i in 1..size(a) { x = get(a, i - 1); }; return 0; };"
            , parseValidProgramHelper "fn f(l: List<Int>) -> Int { for i in 0..size(l) { if get(l, i) > 2 { return i; }; }; return -1; };"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { t = 0; for i in 0..n { for j in 0..i { t = t + 1; }; }; return t; };"
            , -- An invariant can be written as for a while loop, and uses i
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = 0; }] { z = 0; for i in 0..n [{ affirm z = 0; }] { z = z * 1; }; return z; };"
            , -- Refused: reading past the end, writing the variable, and an invariant the body breaks
              parseValidateFailProgramHelper "fn f(a: List<Int>) -> Int { s = 0; for i in 0..size(a) + 1 { s = s + get(a, i); }; return s; };" "Funct input validation failed"
            , -- The loop variable is the loop's to change, in any branch or nested loop, but a function of the same name is its own
              parseFailsWith "for i in 0..3 { i = i + 1; };" "cannot assign its loop variable i"
            , parseFailsWith "n = 0; for i in 0..3 { n = n + 1; i = 2; };" "cannot assign its loop variable i"
            , parseFailsWith "for i in 0..3 { if i > 1 { i = 5; }; };" "cannot assign its loop variable i"
            , parseFailsWith "for i in 0..3 { for i in 0..2 { x = i; }; };" "cannot assign its loop variable i"
            , parseFailsWith "for i in 0..3 { while true ~ { i = 0; }; };" "cannot assign its loop variable i"
            , parseValidProgramHelper "for i in 0..3 { for j in 0..2 { x = j; }; };"
            , parseValidProgramHelper "fn f(i: Int) -> Int { i = 5; return i; }; for i in 0..3 { y = f(i); };"
            , parseValidateFailProgramHelper "z = 0; for i in 0..3 [{ affirm z = 0; }] { z = z + 1; };" "Loop invariant is not preserved: Could not prove: z = 0"
            , parseValidateFailProgramHelper "n = 0; for i in 0..3 { n = n + 1; }; affirm i = 4;" "Could not prove: i = 4"
            , -- Through the elements of a list: x is bound in each iteration and is local to the body, i is the index
              parseEvalProgramHelper "s = 0; for x in [4, 5, 6] { s = s + x; }; return s;" (Just (VInt 15))
            , parseEvalProgramHelper "s = 0; for i, x in [4, 5, 6] { s = s + i * x; }; return s;" (Just (VInt 17))
            , parseEvalProgramHelper "s = 0; for i, x in [4, 5, 6] { s = s + 1; }; return s * 10 + i;" (Just (VInt 33))
            , parseEvalProgramHelper "l = [1, 2]; n = 0; for x in l { l = push(l, x); n = n + 1; }; return n * 10 + size(l);" (Just (VInt 24))
            , parseEvalProgramHelper "n = 0; for row in [[1, 2], [3]] { for x in row { n = n + x; }; }; return n;" (Just (VInt 6))
            , parseEvalProgramHelper "fn f(l: List<Int>) -> Int { for x in l { if x > 2 { return x; }; }; return -1; }; return f([1, 5, 7]);" (Just (VInt 5))
            , parseValidProgramHelper "fn total(a: List<Int>) -> Int { s = 0; for x in a { s = s + x; }; return s; };"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int { for i, x in a { affirm x = get(a, i); }; return 0; };"
            , parseValidProgramHelper "fn f(a: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(a); }] { out = []; for x in a { out = push(out, x + 1); }; return out; };"
            , parseValidProgramHelper "fn f(a: List<List<Int>>) -> Int { s = 0; for row in a { for x in row { s = s + x; }; }; return s; };"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int { for x in a { if x > 2 { return x; }; }; return -1; };"
            , -- Loops that nest or follow each other with the same names keep their own copies of the list
              parseEvalProgramHelper "s = 0; for i, x in [1, 2] { for j, x in [10, 20] { y = x; }; s = s + x; }; return s;" (Just (VInt 3))
            , parseEvalProgramHelper "s = 0; for x in [1, 2] { for x in [10, 20] { s = s + 1; }; s = s + x; }; return s;" (Just (VInt 7))
            , parseValidProgramHelper "for x in [1, 2] { y = x; }; for x in [true, false] { z = x; };"
            , parseValidProgramHelper "fn f(a: List<Int>, b: List<Bool>) -> Int { for x in a { for x in b { y = x; }; z = x + 1; }; return 0; };"
            , parseValidateFailProgramHelper "for x in [1, 2] { for x in [10, 20] { y = 0; }; affirm x = 10; };" "Could not prove: x = 10"
            , -- A body that changes the list it goes through does not change what it goes through
              parseValidProgramHelper "fn f(a: List<Int>) -> Int { for x in a { a = push(a, x); }; return 0; };"
            , parseValidateFailProgramHelper "fn f(a: List<Int>) -> Int { for x in a { y = x; }; return x; };" "Undefined variable: x"
            , parseFailsWith "for i, x in [1] { i = 3; };" "cannot assign its loop variable i"
            , parseFailsWith "for i, x in 0..3 { y = 1; };" "has one variable"
            , -- The range has to be known not to run backwards, which is what gives i = hi afterwards
              parseValidateFailProgramHelper "fn f(n: Int) -> Int { for i in 0..n { x = i; }; return 0; };" "the range has to be known to end at or after its start"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { for i in 0..n { x = i; }; affirm i = n; return 0; };"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 3; }] [{ }] { for i in 3..n { x = i; }; affirm i = n; return 0; };"
            ]

-- Loops get the invariants a counter and the lists built beside it satisfy, without the program writing them
testInferredInvariants :: Test
testInferredInvariants =
    let building body = "fn f(a: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(a); }] { out = []; " ++ body ++ " return out; };"
     in testCaseSeq
            "testInferredInvariants"
            [ -- A list that gets an element per iteration has the size of the counter
              parseValidProgramHelper (building "for i in 0..size(a) { out = push(out, 0); };")
            , parseValidProgramHelper (building "i = 0; n = size(a); while i < n [{ affirm i <= n; }] shrinks n - i { out = push(out, get(a, i)); i = i + 1; };")
            , parseValidProgramHelper "out = []; i = 0; while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { out = push(out, i); i = i + 1; }; affirm size(out) = 3;"
            , -- Counters keep their distance, and a lower bound they keep
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = 0; j = 5; while i < n [{ affirm i <= n; }] shrinks n - i { i = i + 1; j = j + 1; }; affirm j = i + 5; return 0; };"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 3; }] { i = 3; while i < n [{ affirm i <= n + 1; }] shrinks n - i { i = i + 2; }; affirm i >= 3; return 0; };"
            , -- set keeps the size
              parseValidProgramHelper "l = [1, 2, 3]; for i in 0..3 { l = set(l, i, 0); }; affirm size(l) = 3;"
            , -- Only what the body keeps is inferred
              parseValidateFailProgramHelper (building "for i in 0..size(a) { out = push(out, 0); out = push(out, 1); };") "Could not prove: size(return) = size(a)"
            , parseValidateFailProgramHelper "out = []; for i in 0..3 { if i > 1 { out = push(out, i); }; }; affirm size(out) = 3;" "Could not prove: size(out) = 3"
            , parseValidateFailProgramHelper "out = []; i = 0; while i < 3 shrinks 3 - i { out = push(out, i); i = i + 2; }; affirm size(out) = 2;" "Could not prove: size(out) = 2"
            , parseValidateFailProgramHelper "i = 0; while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { i = i + 1; }; affirm i = 0;" "Could not prove: i = 0"
            , -- A mistake in the invariant is reported as before
              parseValidateFailProgramHelper "out = []; i = 0; while i < 3 [{ affirm size(out) = 7; }] shrinks 3 - i { out = push(out, i); i = i + 1; };" "Loop invariant does not hold on entry"
            , -- A list whose size is known without being a literal: the size term has a value on entry
              parseValidProgramHelper "fn f(v: Int, p: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(p) + 2; }] { out = push(push([], v), v); for x in p { out = push(out, x); }; return out; };"
            , parseValidProgramHelper "fn f(v: Int, p: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(p) + 3; }] { out = push(push([], v), v); for x in p { out = push(out, x); }; return push(out, 0); };"
            , parseValidateFailProgramHelper "fn f(v: Int, p: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(p) + 2; }] { out = push(push([], v), v); for x in p { out = push(push(out, x), x); }; return out; };" "Could not prove: size(return) = size(p) + 2"
            , -- A loop that starts at a variable: the counter and the size differ by it
              parseValidProgramHelper "fn f(buf: List<Int>, lo: Int, hi: Int) -> List<Int> [{ affirm 0 <= lo; affirm lo <= hi; affirm hi <= size(buf); }] [{ affirm size(return) = hi - lo; }] { out = []; for i in lo..hi { out = push(out, get(buf, i)); }; return out; };"
            , parseValidateFailProgramHelper "fn f(buf: List<Int>, lo: Int, hi: Int) -> List<Int> [{ affirm 0 <= lo; affirm lo <= hi; affirm hi <= size(buf); }] [{ affirm size(return) = hi - lo; }] { out = []; for i in lo..hi { out = push(push(out, get(buf, i)), 0); }; return out; };" "Could not prove: size(return) = hi - lo"
            , -- The first elements of a list stay as they were when the loop only pushes
              parseValidProgramHelper "fn f(v: Int, p: List<Int>) -> List<Int> [{ }] [{ affirm get(return, 1) = size(p); }] { out = push(push([], v), size(p)); for x in p { out = push(out, x); }; return out; };"
            , parseValidProgramHelper "fn f(p: List<Int>) -> List<Int> [{ }] [{ affirm get(return, 0) = 5; affirm get(return, 1) = 6; }] { out = [5, 6]; for x in p { out = push(out, x); }; return out; };"
            , parseValidateFailProgramHelper "fn f(p: List<Int>) -> List<Int> [{ affirm size(p) > 0; }] [{ affirm get(return, 1) = 6; }] { out = [5, 6]; for i in 0..size(p) { out = set(out, 1, get(p, i)); }; return out; };" "Could not prove: get(return, 1) = 6"
            , -- The elements of literal lists do not push a counter or a comparison out of the candidates
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { a = [1, 2, 3]; b = [4, 5, 6]; i = 0; while i < n shrinks n - i { a = set(a, 0, 1); b = set(b, 0, 4); i = i + 1; }; affirm i = n; return 0; }; x = f(3);"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { a = [1, 2, 3]; b = [4, 5, 6]; i = 0; while i < n shrinks n - i { a = set(a, 0, 1); b = set(b, 0, 4); i = i + 1; }; affirm get(a, 1) = 2; return 0; }; x = f(3);"
            , -- A loop that returns infers its invariants too, one candidate at a time
              parseValidProgramHelper "fn f(a: List<Int>) -> Int { out = []; for i in 0..size(a) { if get(a, i) > 2 { return i; }; out = push(out, 0); }; return -1; };"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int { i = 0; while i < size(a) shrinks size(a) - i { if get(a, i) > 2 { return i; }; i = i + 1; }; affirm i = size(a); return -1; };"
            , parseValidateFailProgramHelper "fn f(a: List<Int>) -> Int { i = 0; while i < size(a) shrinks size(a) - i { if get(a, i) > 2 { return i; }; i = i + 1; }; affirm i = 0; return -1; };" "Could not prove: i = 0"
            , -- Starting from something that is not a number: a copy of an argument, or a counter bounded by a parameter
              parseValidProgramHelper "fn f(a: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(a); }] { out = a; for i in 0..size(a) { out = set(out, i, 0); }; return out; };"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int { c = a; i = 0; while i < size(a) shrinks size(a) - i { c = set(c, i, 1); i = i + 1; }; affirm size(c) = size(a); return 0; };"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int { i = 0; n = size(a); while i < n shrinks n - i { i = i + 1; }; affirm i = n; return i; };"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = 0; while i < n shrinks n - i { i = i + 1; }; affirm i = n; return i; };"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int { i = 0; while i < n shrinks n - i { i = i + 1; }; affirm i = n; return i; };" "Could not prove: i = n"
            , parseValidateFailProgramHelper "fn f(a: List<Int>) -> Int { c = a; i = 0; while i < size(a) shrinks size(a) - i { c = push(c, 0); i = i + 1; }; affirm size(c) = size(a); return 0; };" "Could not prove: size(c) = size(a)"
            , parseValidateFailProgramHelper "fn f(a: List<Int>, b: List<Int>) -> Int { c = b; i = 0; while i < size(a) shrinks size(a) - i { c = set(c, 0, 1); i = i + 1; }; return 0; };" "Funct input validation failed"
            ]

-- Loops and recursive functions say why they end, and code that may not end is declared
testTermination :: Test
testTermination =
    let tree = "enum Tree { Leaf, Branch { left: Box<Tree>, right: Box<Tree> } };"
        settle = "fn settle(n: Int) -> Int ~ { while n != 1 ~ { n = n - 1; }; return n; };"
     in testCaseSeq
            "testTermination"
            [ -- The clause is parsed before the body, after an invariant, and after the contracts of a function
              case parseStatementBlock "while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { i = i + 1; };" of
                Left err -> Just ("Parse error: " ++ show err)
                Right [While _ inv (Just (Shrinks _)) _] -> testAssertEq (length inv) 1
                Right other -> Just ("Unexpected parse: " ++ show other)
            , case parseStatementBlock "while i < 3 ~ { i = i + 1; };" of
                Left err -> Just ("Parse error: " ++ show err)
                Right [While _ _ (Just MayDiverge) _] -> Nothing
                Right other -> Just ("Unexpected parse: " ++ show other)
            , case parseStatementBlock (tree ++ "while t is Tree::Branch shrinks t { t = t; };") of
                Left err -> Just ("Parse error: " ++ show err)
                Right [_, While _ _ (Just (Shrinks _)) _] -> Nothing
                Right other -> Just ("Unexpected parse: " ++ show other)
            , -- A loop has to say how it ends
              parseValidateFailProgramHelper "i = 0; while i < 3 { i = i + 1; };" "Loop must say how it ends"
            , parseValidProgramHelper "i = 0; while i < 3 ~ { i = i + 1; };"
            , -- The variant is at least 0 when an iteration starts, and smaller when it ends
              parseValidProgramHelper "i = 0; while i < 3 shrinks 3 - i { i = i + 1; };"
            , parseValidateFailProgramHelper "i = 0; while i < 3 shrinks 3 - i { };" "Loop variant does not shrink: 3 - i"
            , parseValidateFailProgramHelper "i = 0; while i < 3 [{ affirm i >= 0; }] shrinks i { i = i + 1; };" "Loop variant does not shrink: i"
            , parseValidateFailProgramHelper "fn f(i: Int) -> Int { while i != 0 shrinks i { i = i - 1; }; return i; };" "Loop variant is not bounded below: i"
            , -- Counting down towards a bound that moves, and a body with an early return
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; while i > 0 shrinks i { if i = 7 { return 7; }; i = i - 1; }; return i; };"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; while i > 0 shrinks i { if i = 7 { return 7; }; i = i + 1; }; return i; };" "Loop variant does not shrink: i"
            , -- Loops inside loops each have their own variant
              parseValidProgramHelper "i = 0; while i < 3 shrinks 3 - i { j = 0; while j < 2 shrinks 2 - j { j = j + 1; }; i = i + 1; };"
            , -- A difference is compared by its sides
              parseValidProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i <= n; }] [{ }] { affirm n - i >= 0; return 0; };"
            , parseValidProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i < n; }] [{ }] { affirm n - (i + 1) < n - i; return 0; };"
            , parseValidateFailProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i < n; }] [{ }] { affirm n - i < 0; return 0; };" "Could not prove: n - i < 0"
            , -- A function that calls itself says what shrinks
              parseValidateFailProgramHelper "fn down(n: Int) -> Int [{ affirm n >= 0; }] { if n < 1 { return 0; } else { return down(n - 1); }; };" "Not guaranteed to terminate: it calls itself"
            , parseValidProgramHelper "fn down(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { if n < 1 { return 0; } else { return down(n - 1); }; };"
            , parseValidateFailProgramHelper "fn down(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { if n < 1 { return 0; } else { return down(n); }; };" "Recursive call does not shrink the variant: n"
            , parseValidateFailProgramHelper "fn down(n: Int) -> Int shrinks n { if n < 1 { return 0; } else { return down(n - 1); }; };" "Function variant is not bounded below: n"
            , parseValidProgramHelper "fn down(n: Int) -> Int ~ { return down(n); };"
            , -- Recursion over a structure: the call is given a field of the value
              parseValidProgramHelper (tree ++ "fn count(t: Box<Tree>) -> Int shrinks t { return match t { Tree::Leaf => 1, Tree::Branch { left: l, right: r } => count(l) + count(r) }; };")
            , parseValidateFailProgramHelper (tree ++ "fn count(t: Box<Tree>) -> Int shrinks t { return match t { Tree::Leaf => 1, Tree::Branch { left: l, right: r } => count(l) + count(t) }; };") "Recursive call does not shrink the variant: t"
            , parseValidProgramHelper (tree ++ "fn depth(t: Box<Tree>) -> Int { n = 0; while t is Tree::Branch shrinks t { t = (t as Tree::Branch).left; n = n + 1; }; return n; };")
            , parseValidateFailProgramHelper (tree ++ "fn depth(t: Box<Tree>) -> Int { n = 0; while t is Tree::Branch shrinks t { n = n + 1; }; return n; };") "Loop variant does not shrink: t"
            , -- Code that may not end makes a function that contains it say so
              parseValidProgramHelper settle
            , parseValidateFailProgramHelper "fn settle(n: Int) -> Int { while n != 1 ~ { n = n - 1; }; return n; };" "Not guaranteed to terminate: a loop is declared ~"
            , parseValidateFailProgramHelper (settle ++ "fn twice(n: Int) -> Int { return settle(n) + 1; };") "Not guaranteed to terminate: it calls a function that is declared ~"
            , parseValidProgramHelper (settle ++ "fn twice(n: Int) -> Int ~ { return settle(n) + 1; };")
            , -- A cycle has to be a function calling itself: a function inside another cannot call the one around it unless both say ~
              parseValidProgramHelper "fn f(n: Int) -> Int ~ { fn g(m: Int) -> Int ~ { return f(m); }; return g(n); };"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int ~ { fn g(m: Int) -> Int { return f(m); }; return g(n); };" "Not guaranteed to terminate: it calls a function that is declared ~"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int { fn g(m: Int) -> Int { return f(m); }; return g(n); };" "Not guaranteed to terminate: it calls itself"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { fn g(m: Int) -> Int [{ affirm m >= 0; }] { return f(m); }; if n < 1 { return 0; } else { return g(n - 1); }; };" "not from a function defined inside it"
            , -- Calling itself through another name is still a call to itself
              parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { h = f; return h(n); };" "Not guaranteed to terminate: it calls itself"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { h = f; if n < 1 { return 0; } else { return h(n - 1); }; };"
            , -- A function sees only the functions before it, so two cannot call each other
              parseValidateFailProgramHelper "fn a(n: Int) -> Int { return b(n); }; fn b(n: Int) -> Int { return a(n); };" "Undefined variable: b"
            , -- The program itself may call one
              parseValidProgramHelper (settle ++ "x = settle(3);")
            , -- Code that cannot be reached is not counted
              parseValidProgramHelper (settle ++ "fn f(n: Int) -> Int { if n > 0 { if n < 0 { return settle(n); }; }; return n; };")
            , parseValidateFailProgramHelper (settle ++ "fn f(n: Int) -> Int { if n > 0 { if n < 5 { return settle(n); }; }; return n; };") "Not guaranteed to terminate"
            , -- A function defined inside another says for itself
              parseValidProgramHelper (settle ++ "fn outer(n: Int) -> Int { fn inner(m: Int) -> Int ~ { return settle(m); }; return n; };")
            , parseValidateFailProgramHelper (settle ++ "fn outer(n: Int) -> Int ~ { fn inner(m: Int) -> Int { return settle(m); }; return n; };") "Not guaranteed to terminate"
            , -- The type of what shrinks decides what it means: an Int counts down, an enum or struct loses a field
              case parseStatementBlock "i = 0; while i < 3 shrinks 3 - i { i = i + 1; };" of
                Left err -> Just ("Parse error: " ++ show err)
                Right stmts -> case elaborate stmts of
                    Ok [_, While _ _ (Just (Counting _)) _] -> Nothing
                    other -> Just ("Unexpected: " ++ show other)
            , case parseStatementBlock (tree ++ "t = Box::new(Tree::Leaf); while t is Tree::Branch shrinks t { t = (t as Tree::Branch).left; };") of
                Left err -> Just ("Parse error: " ++ show err)
                Right stmts -> case elaborate stmts of
                    Ok [_, _, While _ _ (Just (Parts _)) _] -> Nothing
                    other -> Just ("Unexpected: " ++ show other)
            , case parseStatementBlock "fn f(n: Int) -> Int shrinks n { return 0; };" of
                Left err -> Just ("Parse error: " ++ show err)
                Right stmts -> case elaborate stmts of
                    Ok [Assign _ (Val (VFunct _ _ _ (NativeFunct _ (Just (Counting _)) _) _))] -> Nothing
                    other -> Just ("Unexpected: " ++ show other)
            , parseValidateFailProgramHelper "x = [1]; while x = x shrinks x { x = x; };" "shrinks needs an Int, an enum or a struct, got List<Int>"
            , parseValidateFailProgramHelper "fn f(b: Bool) -> Int shrinks b { return 0; };" "shrinks needs an Int, an enum or a struct, got Bool"
            , -- Evaluation does not use any of it
              parseEvalProgramHelper "i = 0; while i < 3 shrinks 3 - i { i = i + 1; }; return i;" (Just (VInt 3))
            ]

-- Validation walks the control-flow graph of the MIR: the paths that meet are joined, loops are regions, a return ends a path
testCfgValidation :: Test
testCfgValidation =
    testCaseSeq
        "testCfgValidation"
        [ -- Three paths meet at one block
          parseValidProgramHelper "fn f(c: Int) -> Int [{ }] [{ }] { x = 0; if c < 0 { x = 1; } else { if c = 0 { x = 2; } else { x = 3; }; }; affirm x > 0; affirm x < 4; return x; }; y = f(1);"
        , parseValidateFailProgramHelper "fn f(c: Int) -> Int [{ }] [{ }] { x = 0; if c < 0 { x = 1; } else { if c = 0 { x = 2; } else { x = -3; }; }; affirm x > 0; return x; }; y = f(1);" "Could not prove: x > 0"
        , -- A guard that returns leaves the rest of the function to the path that falls through
          parseValidProgramHelper "fn f(n: Int) -> Int [{ }] [{ affirm return > 0; }] { if n < 1 { return 1; }; affirm n >= 1; return n; }; y = f(1);"
        , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ }] [{ affirm return > 0; }] { if n < 1 { return n; }; return n; }; y = f(1);" "Could not prove: return > 0"
        , -- A constant condition has one way on
          parseValidProgramHelper "x = 0; if true { x = 1; } else { x = 2; }; affirm x = 1;"
        , -- Code after a return cannot run, so it is not validated
          parseValidProgramHelper "return 1; affirm 1 = 2;"
        , parseValidProgramHelper "fn f(n: Int) -> Int [{ }] [{ }] { return n; affirm n = n + 1; }; x = f(1);"
        , -- A loop in a loop: what the outer invariant says survives the inner loop
          parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { c = 0; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { j = 0; while j < 2 [{ affirm j >= 0; affirm j <= 2; }] shrinks 2 - j { c = c + 1; j = j + 1; }; affirm i >= 0; i = i + 1; }; return c; }; x = f(3);"
        , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { j = 0; while j < 2 [{ affirm j >= 0; affirm j <= 2; }] shrinks 2 - j { j = j + 1; i = i + 1; }; i = i + 1; }; return i; }; x = f(3);" "Loop invariant is not preserved"
        , -- A return inside a nested loop leaves the function from there
          parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= 0; }] { for i in 0..n { for j in 0..n { if i + j > 3 { return i + j; }; }; }; return 0; }; x = f(3);"
        , -- The result of a function that returns what it was given is that argument
          parseValidProgramHelper "fn id(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; }; x = 3; y = id(x); affirm y = x; affirm y = 3;"
        , -- (what a body establishes is not exported: a caller has only the contract)
          parseValidateFailProgramHelper "fn id(n: Int) -> Int [{ }] [{ }] { return n; }; fn twice(n: Int) -> Int [{ }] [{ affirm return = n; }] { return id(id(n)); };" "Could not prove: return = n"
        , parseValidProgramHelper "fn id(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; }; fn twice(n: Int) -> Int [{ }] [{ affirm return = n; }] { return id(id(n)); }; x = twice(2); affirm x = 2;"
        , -- A function defined in a branch is local to it
          parseValidProgramHelper "x = 0; if true { fn inc(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { return n + 1; }; x = inc(1); } else { x = 2; }; affirm x = 2;"
        , -- A function defined in a loop is checked, and used there
          parseValidProgramHelper "i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { fn inc(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { return n + 1; }; i = inc(i); }; affirm i >= 2;"
        , -- A path that ends without a return, however it got there
          parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ }] [{ }] { if n > 0 { return 1; } else { if n < 0 { return 2; }; }; }; x = f(1);" "Return value not found"
        , -- The variant starts at the test of the condition, which a call in the condition moves to a block of its own, or a constant
          parseValidProgramHelper "fn id(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; }; i = 3; while id(i) > 0 [{ affirm i >= 0; }] shrinks i { i = i - 1; };"
        , parseValidateFailProgramHelper "fn id(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; }; i = 3; while id(i) > 0 [{ affirm i >= 0; }] shrinks i { i = i + 1; };" "Loop variant does not shrink"
        , parseValidProgramHelper "i = 0; while true [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { if i = 3 { return i; }; i = i + 1; };"
        , -- A variable of a proof that has the name of a program variable stands for it until the program assigns it again
          parseValidProgramHelper "x = 0; define x = x; x = 1; affirm x = 1;"
        , parseValidateFailProgramHelper "x = 0; define x = x; x = 1; affirm x = 0;" "Could not prove: x = 0"
        , -- A builtin used as a value keeps its contract
          parseValidProgramHelper "h = size; x = h([1, 2]); affirm x = 2;"
        , parseValidateFailProgramHelper "h = first; x = h([]);" "Funct input validation failed"
        , -- A function that is called is the one that was defined, even when a local has its name later
          parseValidProgramHelper "fn f(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; }; fn g(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { return n + 1; }; h = f; { h = g; }; x = f(1); affirm x = 1;"
        ]
