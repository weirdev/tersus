module TestControl
    ( testCallsAndReturnJoin
    , testIfJoin
    , testForLoops
    , testInferredInvariants
    , testTermination
    , testCfgValidation
    ) where

import Compile (lowerSource)
import qualified Data.Map as Map
import qualified Mir as M
import TestParserFragments
import Types
import Syntax
import Compile (elaborateStatements)
import Utils
import TestHarness
import ValidatorNative (validateCompiled)

-- A call nested in an expression keeps its callee's output contract, and the join of an `if` tries the function's own
data ControlVerdict = ControlValid | ControlFails String

testCallsAndReturnJoin :: Test
testCallsAndReturnJoin =
    let one = "fn one(x: Int) -> Int [{ }] [{ affirm return > x; }] { return x + 1; }; "
        rows :: [(String, String, ControlVerdict)]
        rows =
            [
              -- Nested calls
              ( "valid-one-fn-f-y-int-int-affirm-return-y-1", (one ++ "fn f(y: Int) -> Int [{ }] [{ affirm return > y + 1; }] { return one(y) + 1; }; z = f(1);"), ControlValid )
            , ( "valid-one-fn-f-y-int-int-affirm-return-y-1-2", (one ++ "fn f(y: Int) -> Int [{ }] [{ affirm return > y + 1; }] { return one(one(y)); }; z = f(1);"), ControlValid )
            , ( "valid-one-fn-f-y-int-int-affirm-return-y-x", (one ++ "fn f(y: Int) -> Int [{ }] [{ affirm return > y; }] { x = 2 * one(y); affirm x > 2 * y; return y + 1; }; z = f(1);"), ControlValid )
            , ( "valid-fn-f-l-list-int-list-int-affirm-size-return", "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(l) + 2; }] { return push(push(l, 1), 2); }; z = f([1]);", ControlValid )
            , ( "fail-one-fn-f-y-int-int-affirm-return-y-1", (one ++ "fn f(y: Int) -> Int [{ }] [{ affirm return > y + 1; }] { return one(y); }; z = f(1);"), ControlFails "Could not prove: return > y + 1" )
            , ( "fail-fn-f-l-list-int-list-int-affirm-size-return", "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(l) + 3; }] { return push(push(l, 1), 2); }; z = f([1]);", ControlFails "Could not prove: size(return) = size(l) + 3" )
            , ( "valid-fn-s-n-int-int-affirm-n-0-affirm-return", "fn s(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] shrinks n { r = 0; if n < 1 { r = 0; } else { r = n + s(n - 1); }; return r; }; x = s(4);", ControlValid )
              -- Returning paths: the output contract holds if every path entails it
            , ( "valid-fn-f-n-int-int-affirm-n-0-affirm-return", "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] { if n < 1 { return 1; } else { return n + 1; }; }; x = f(3);", ControlValid )
            , ( "valid-fn-s-n-int-int-affirm-n-0-affirm-return-2", "fn s(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] shrinks n { if n < 1 { return 0; } else { return n + s(n - 1); }; }; x = s(4);", ControlValid )
            , ( "valid-fn-b-n-int-int-affirm-n-0-affirm-return", "fn b(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= 0; }] shrinks n { if n < 1 { return 0; } else { return 1 + b(n / 2); }; }; x = b(9);", ControlValid )
            , ( "fail-fn-f-n-int-int-affirm-n-0-affirm-return", "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] { if n < 1 { return 0; } else { return n - 1; }; }; x = f(3);", ControlFails "Could not prove: return >= n" )
            , ( "fail-fn-f-n-int-int-affirm-n-0-affirm-return-2", "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] { if n < 1 { return -1; } else { return n + 1; }; }; x = f(3);", ControlFails "Could not prove: return >= n" )
              -- A path that is not the end of the function
            , ( "valid-fn-f-n-int-c-int-int-affirm-n-0", "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= n; }] { if n < 1 { return 1; }; if c > 0 { return n + 1; } else { return n + 2; }; }; x = f(3, 1);", ControlValid )
              -- An if that falls through, then a return
            , ( "valid-fn-g-n-int-c-int-int-affirm-n-0", "fn g(n: Int, c: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { r = n; if c > 0 { r = r + 1; } else { r = r + 2; }; return r; }; x = g(1, 2);", ControlValid )
            , ( "fail-fn-g-n-int-c-int-int-affirm-n-0", "fn g(n: Int, c: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { r = n; if c > 0 { r = r + 1; } else { r = r - 2; }; return r; }; x = g(1, 2);", ControlFails "Could not prove: return > 0" )
            , ( "valid-fn-g-n-int-c-int-int-affirm-n-0-2", "fn g(n: Int, c: Int) -> Int [{ affirm n > 0; }] [{ affirm return > n; }] { r = n; if c > 0 { r = r + 1; } else { r = r + 2; }; if c > 5 { r = r + 1; }; return r; }; x = g(1, 2);", ControlValid )
              -- What a rewrite in the contract needs is tried too: the check of a relation, a rule's input contract
            , ( "valid-fn-f-c-int-int-rewrite-checkrel-return-0-affirm", "fn f(c: Int) -> Int [{ }] [{ rewrite checkRel return > 0; affirm return > -5; }] { if c > 0 { return 1; } else { return 2; }; }; x = f(1);", ControlValid )
            , ( "valid-fn-f-c-int-int-rewrite-checkgtzero-return-affirm-return", "fn f(c: Int) -> Int [{ }] [{ rewrite checkGtZero return; affirm return > -5; }] { if c > 0 { return 1; } else { return 2; }; }; x = f(1);", ControlValid )
            , ( "valid-axiom-posissmall-i-affirm-i-0-affirm-i-1-fn", "axiom posIsSmall(i) [{ affirm i > 0; }] [{ affirm i > -1; }]; fn f(c: Int) -> Int [{ }] [{ rewrite posIsSmall return; affirm return > -5; }] { if c > 0 { return 1; } else { return 2; }; }; x = f(1);", ControlValid )
            , ( "fail-axiom-posissmall-i-affirm-i-0-affirm-i-1-fn", "axiom posIsSmall(i) [{ affirm i > 0; }] [{ affirm i > -1; }]; fn f(c: Int) -> Int [{ }] [{ rewrite posIsSmall return; affirm return > -5; }] { if c > 0 { return 1; } else { return 0; }; }; x = f(1);", ControlFails "Rewrite rule posIsSmall input validation failed: Could not prove: return > 0" )
            , ( "valid-fn-f-c-int-int-x-0-if-c-0", "fn f(c: Int) -> Int [{ }] { x = 0; if c > 0 { x = 1; } else { x = 2; }; rewrite checkRel x > 0; return x; }; y = f(1);", ControlValid )
              -- A loop that returns from inside, with the contract on both its returns
            , ( "valid-fn-f-a-list-int-int-affirm-return-1-affirm", "fn f(a: List<Int>) -> Int [{ }] [{ affirm return >= -1; affirm return < size(a); }] { for i in 0..size(a) { if get(a, i) > 2 { return i; }; }; return -1; }; x = f([1, 3]);", ControlValid )
            ]
        runRow (name, source, verdict) =
            ( name
            , case verdict of
                ControlValid -> parseValidProgramHelper source
                ControlFails err -> parseValidateFailProgramHelper source err
            )
     in testCaseNamedSeq "testCallsAndReturnJoin" (map runRow rows)

-- The join of an `if` also tries what the program is about to need (see mergeStates in lib/validation/joins.tersus)
testIfJoin :: Test
testIfJoin =
    let fn' body = "fn f(c: Int, y: Int) -> Int [{ affirm y > 0; }] [{ }] { " ++ body ++ " return 0; };"
        rows :: [(String, String, ControlVerdict)]
        rows =
            [
              -- An affirm after the if asks for a fact that both branches entail
              ( "valid-fn-x-0-if-c-0-x-1-else-x", (fn' "x = 0; if c > 0 { x = 1; } else { x = 2; }; affirm x > 0;"), ControlValid )
            , ( "valid-fn-x-0-if-c-0-x-1-else-x-2", (fn' "x = 0; if c > 0 { x = 1; } else { x = 2; }; affirm x < 3; affirm x != 0;"), ControlValid )
            , ( "fail-fn-x-0-if-c-0-x-1-else-x", (fn' "x = 0; if c > 0 { x = 1; } else { x = -1; }; affirm x > 0;"), ControlFails "Could not prove: x > 0" )
            , ( "fail-fn-x-0-if-c-0-x-1-else-x-2", (fn' "x = 0; if c > 0 { x = 1; } else { x = 2; }; affirm x = 1;"), ControlFails "Could not prove: x = 1" )
              -- Facts from before the if about a variable it assigns, in terms of its new value
            , ( "valid-fn-x-y-if-c-0-x-x-1-else", (fn' "x = y; if c > 0 { x = x + 1; } else { x = x + 2; }; affirm x > 1;"), ControlValid )
            , ( "valid-fn-x-y-if-c-0-x-x-1-else-2", (fn' "x = y; if c > 0 { x = x + 1; } else { }; affirm x > 0;"), ControlValid )
            , ( "fail-fn-x-y-if-c-0-x-x-1-else", (fn' "x = y; if c > 0 { x = x + 1; } else { x = 0; }; affirm x > 0;"), ControlFails "Could not prove: x > 0" )
            , ( "joined-local-keeps-source-size-fact", "fn f(bytes: &List<Int>, p: Int) -> Int { limit = size(bytes); end = p; if end > limit { end = limit; }; affirm limit = size(bytes); affirm end <= size(bytes); return end; }; return 0;", ControlValid )
            , ( "joined-local-keeps-borrowed-size-bound", "fn f(bytes: &List<Int>, p: Int) -> Int { end = p; if end > size(bytes) { end = size(bytes); }; affirm end <= size(bytes); return end; }; return 0;", ControlValid )
            , ( "sequential-conditional-push-facts", "fn f(c: Int, xs: List<Int>) -> List<Int> { facts = xs; " ++ concat ["if c > " ++ show i ++ " { facts = push(facts, " ++ show i ++ "); }; " | i <- [0 .. 9 :: Int]] ++ "return facts; }; return 0;", ControlValid )
              -- The branches' own facts still count, and so do the else branch's
            , ( "valid-fn-x-0-if-c-0-x-5-else-x", (fn' "x = 0; if c > 0 { x = 5; } else { x = 5; affirm x = 5; }; affirm x = 5;"), ControlValid )
            , ( "join-overlapping-constant-ranges-checked-per-path-in-a-return-block", (fn' "x = 0; z = 0; if c > 0 { x = 1; z = 2; } else { x = 3; z = 4; }; affirm x < z;"), ControlValid )
            , ( "fail-join-keeps-no-order-between-overlapping-constant-ranges", (fn' "x = 0; z = 0; if c > 0 { x = 1; z = 2; } else { x = 3; z = 4; }; affirm x < z; if y > 5 { return 1; };"), ControlFails "Could not prove: x < z" )
            , ( "fail-join-overlapping-constant-ranges-not-restored-at-arm-ends", (fn' "x = 0; z = 0; if c > 0 { x = 1; z = 2; affirm x < z; } else { x = 3; z = 4; affirm x < z; }; affirm x < z; if y > 5 { return 1; };"), ControlFails "Could not prove: x < z" )
              -- Nested ifs
            , ( "valid-fn-x-0-if-c-0-if-c-5-x", (fn' "x = 0; if c > 0 { if c > 5 { x = 2; } else { x = 1; }; } else { x = 3; }; affirm x > 0;"), ControlValid )
              -- A loop body does not have to restate the invariant or the variant in each branch
            , ( "valid-fn-f-secret-int-int-affirm-secret-0-affirm-secret", "fn f(secret: Int) -> Int [{ affirm secret >= 0; affirm secret <= 1000; }] [{ affirm return = secret; }] { lo = 0; hi = 1000; while lo < hi [{ affirm lo <= secret; affirm secret <= hi; }] shrinks hi - lo { mid = (lo + hi) / 2; if mid < secret { lo = mid + 1; } else { hi = mid; }; }; return lo; }; x = f(617);", ControlValid )
            , ( "valid-fn-f-n-int-int-affirm-n-0-i-n", "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; c = 0; while i > 0 [{ affirm i >= 0; affirm c >= 0; }] shrinks i { if i > 5 { i = i - 2; c = c + 1; } else { i = i - 1; }; }; return c; };", ControlValid )
            , ( "fail-fn-f-secret-int-int-affirm-secret-0-affirm-secret", "fn f(secret: Int) -> Int [{ affirm secret >= 0; affirm secret <= 1000; }] { lo = 0; hi = 1000; while lo < hi [{ affirm lo <= secret; affirm secret <= hi; }] shrinks hi - lo { mid = (lo + hi) / 2; if mid < secret { lo = mid; } else { hi = mid; }; }; return lo; };", ControlFails "Loop variant does not shrink" )
            , ( "fail-fn-f-n-int-int-affirm-n-0-i-n", "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; while i > 0 [{ affirm i >= 0; }] shrinks i { if i > 5 { i = i - 2; } else { i = i + 1; }; }; return 0; };", ControlFails "Loop variant does not shrink" )
            , ( "fail-fn-f-n-int-int-affirm-n-0-i-n-2", "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; while i > 0 [{ affirm i >= 0; }] shrinks i { if i > 5 { i = i - 7; } else { i = i - 1; }; }; return 0; };", ControlFails "Loop invariant is not preserved: Could not prove: i >= 0" )
              -- The same when the loop body returns, which ends its path with the loop end check
            , ( "valid-fn-f-n-int-int-affirm-n-0-lo-0", "fn f(n: Int) -> Int [{ affirm n >= 0; }] { lo = 0; hi = n; while lo < hi [{ affirm lo <= hi; }] shrinks hi - lo { mid = (lo + hi) / 2; if mid > 100 { return mid; }; if mid < 7 { lo = mid + 1; } else { hi = mid; }; }; return lo; }; x = f(30);", ControlValid )
            , ( "fail-fn-f-n-int-int-affirm-n-0-lo-0", "fn f(n: Int) -> Int [{ affirm n >= 0; }] { lo = 0; hi = n; while lo < hi [{ affirm lo <= hi; }] shrinks hi - lo { mid = (lo + hi) / 2; if mid > 100 { return mid; }; if mid < 7 { lo = mid; } else { hi = mid; }; }; return lo; };", ControlFails "Loop variant does not shrink" )
              -- A fact that needs a forall is not looked for, and is not wrongly kept
            , ( "fail-fn-f-a-list-int-c-int-int-affirm-size", "fn f(a: List<Int>, c: Int) -> Int [{ affirm size(a) > 1; }] { l = a; if c > 0 { l = set(l, 0, 1); } else { l = set(l, 0, 2); }; affirm get(l, 0) = 1; return 0; };", ControlFails "Could not prove: get(l, 0) = 1" )
              -- A term both arms inherit but no local names keeps what both of them hold
              -- of it: the intermediate n * 2, and the size ghost a later goal reuses
            , ( "valid-intermediate-term-survives-join", "fn f(n: Int, c: Bool) -> Int { a = n * 2; a = a + 1; y = 0; if c { y = 1; } else { y = 2; }; affirm a > n * 2; return a; }; return f(3, true);", ControlValid )
            , ( "valid-ghost-size-term-survives-join", "fn f(xs: List<Int>, c: Bool) -> Int { n = size(xs) + 1; y = 0; if c { y = 1; } else { y = 2; }; affirm n > size(xs); return n; }; return 0;", ControlValid )
              -- The arms mint fresh terms from the same state, so the same id on the two
              -- sides is two values: a fact one arm holds of its own is not the other's
            , ( "fail-swapped-fresh-terms-across-arms", "fn f(c: Bool, p: Int) -> Int { x = p; y = p; if c { x = p + 1; } else { y = p + 1; }; affirm x = y + 1; return 0; }; return 0;", ControlFails "Could not prove: x = y + 1" )
            , ( "fail-swapped-locals-order-across-arms", "fn f(c: Bool, p: Int, q: Int) -> Int [{ affirm p < q; }] [{ }] { x = p; y = q; if c { } else { x = q; y = p; }; affirm x < y; return 0; }; return 0;", ControlFails "Could not prove: x < y" )
              -- One term the arms take in two directions, and an alias only one arm keeps
            , ( "fail-one-source-two-joined-locals", "fn f(c: Bool, p: Int) -> Int { s = p + 1; x = s; y = s; if c { x = s + 1; y = s + 2; }; affirm x = y; return 0; }; return 0;", ControlFails "Could not prove: x = y" )
            , ( "fail-alias-not-kept-when-one-side-reassigns", "fn f(c: Bool, p: Int) -> Int { x = p; z = p; if c { x = p + 1; }; affirm x = z; return 0; }; return 0;", ControlFails "Could not prove: x = z" )
              -- A bound has to hold on both sides: the strict one is kept, the unsound one is not
            , ( "valid-strict-local-bound-kept-through-join", "fn f(c: Bool, n: Int) -> Int [{ affirm n > 0; }] [{ }] { x = 0; if c { x = n + 1; } else { x = n + 2; }; affirm x > n; return 0; }; return 0;", ControlValid )
            , ( "fail-sign-not-kept-through-join", "fn f(c: Bool, n: Int) -> Int [{ affirm n >= 0; }] [{ }] { x = 0; if c { x = n; } else { x = 0 - n; }; affirm x >= 0; return 0; }; return 0;", ControlFails "Could not prove: x >= 0" )
              -- An arm the path condition rules out contributes nothing to the join
            , ( "valid-infeasible-arm-contributes-nothing", "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ }] { x = 0; if n < 0 { x = 1; } else { x = 2; }; affirm x = 2; return 0; }; return 0;", ControlValid )
            , ( "fail-infeasible-arm-contributes-nothing", "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ }] { x = 0; if n < 0 { x = 1; } else { x = 2; }; affirm x = 1; return 0; }; return 0;", ControlFails "Could not prove: x = 1" )
              -- The merge model's contest fixtures written as programs (their structural twins,
              -- which reach a kept self-pair only through the contest, are in the bridges family)
            , ( "join-bounds-x-through-unnamed-intermediate", "fn f(y: Int, a: Int, b: Int, c: Bool) -> Int [{ affirm a >= 0; affirm b >= 0; }] [{ }] { x = y; if c { x = y + a + 1; } else { x = y + b + 1; }; affirm x > y; return x; }; return 0;", ControlValid )
            , ( "join-bounds-x-through-two-unnamed-intermediates", "fn f(y: Int, a: Int, b: Int, c: Bool) -> Int [{ affirm a >= 0; affirm b >= 0; }] [{ }] { x = y; if c { x = y + a + 1 + 1; } else { x = y + b + 1 + 1; }; affirm x > y; return x; }; return 0;", ControlValid )
            , ( "join-bounds-call-result-through-unnamed-temporary", "fn g(p: Int) -> Int [{ }] [{ affirm return <= p; }] { return p; }; fn f(y: Int, c: Bool) -> Int [{ }] [{ }] { w = y + 3; x = 0; if c { x = g(y + 2); } else { x = g(y + 3); }; affirm x <= w; return x; }; return 0;", ControlValid )
            , ( "join-keeps-zero-bound-over-two-diamonds", "fn f(c: Bool, d: Bool) -> Int [{ }] [{ }] { x = 0; if c { x = x + 1; } else { x = x + 2; }; if d { x = x + 1; } else { x = x + 2; }; affirm x > 0; return x; }; return 0;", ControlValid )
              -- x is defined from an old value no local holds, and t = old + 3 is kept
            , ( "join-bounds-named-lockstep-definition-from-old-value", "fn f(y: Int, k: Int, c: Bool) -> Int [{ }] [{ }] { u = y + k; t = u + 3; w = u; u = y; x = 0; if c { x = w + 1; w = y; } else { x = w + 2; w = y; }; affirm x < t; return x; }; return 0;", ControlValid )
              -- An arm that resets the counter to the bound answers no to the strict question
            , ( "fail-one-arm-resets-to-the-bound", "fn f(c: Int) -> Int [{ }] [{ }] { x = 5; if c > 0 { x = x + 1; } else { x = 0; }; affirm x > 0; return x; }; return 0;", ControlFails "Could not prove: x > 0" )
              -- A literal is every fact's term, never renamed or aliased into a joined local
            , ( "fail-literal-not-aliased-into-joined-local", "fn f(c: Int) -> Int [{ }] [{ }] { m = 1; if c > 0 { m = 1; } else { m = 2; }; affirm m >= 3; return m; }; return 0;", ControlFails "Could not prove: m >= 3" )
            , ( "valid-parameter-and-literal-kept-unpaired", "fn f(c: Bool, p: Int) -> Int [{ affirm p > 3; }] [{ }] { x = p; m = 1; if c { x = p; m = 1; } else { m = 2; }; affirm x > 3; affirm m >= 1; affirm p > 1; return x; }; return 0;", ControlValid )
            , ( "valid-size-of-joined-local-survives-join", "fn f(c: Bool, l: List<Int>) -> Int [{ }] [{ }] { m = l; n = size(m); if c { m = push(m, 1); n = size(m); } else { m = push(m, 2); n = size(m); }; affirm n = size(m); return 0; }; return 0;", ControlValid )
              -- Arms of unequal length mint different ids for the same local, both ways round
            , ( "valid-unequal-arm-lengths", "fn f(c: Bool) -> Int [{ }] [{ }] { x = 0; if c { x = x + 1; x = x + 1; } else { x = x + 3; }; affirm x > 1; return x; }; return 0;", ControlValid )
            , ( "valid-unequal-arm-lengths-reversed", "fn f(c: Bool) -> Int [{ }] [{ }] { x = 0; if c { x = x + 3; } else { x = x + 1; x = x + 1; }; affirm x > 1; return x; }; return 0;", ControlValid )
            , ( "fail-unequal-arms-same-id-two-values", "fn f(c: Bool, p: Int) -> Int [{ }] [{ }] { t = 0; x = 0; if c { t = p + 1; x = t + 1; } else { x = p + 5; }; affirm x = t + 1; return x; }; return 0;", ControlFails "Could not prove: x = t + 1" )
            , ( "join-bound-two-hops-from-a-constant-checked-per-path-in-a-return-block", "fn f(y: Int, a: Int, b: Int, c: Bool) -> Int [{ affirm b >= 1; affirm a >= b; }] [{ }] { x = y; if c { x = y + a; } else { x = y + b; }; affirm x > y; return x; }; return 0;", ControlValid )
            , ( "fail-join-bound-two-hops-from-a-constant", "fn f(y: Int, a: Int, b: Int, c: Bool, d: Int) -> Int [{ affirm b >= 1; affirm a >= b; }] [{ }] { x = y; if c { x = y + a; } else { x = y + b; }; affirm x > y; if d > 0 { return x; }; return 0; }; return 0;", ControlFails "Could not prove: x > y" )
            , ( "join-bound-restated-at-each-arm-end", "fn f(y: Int, a: Int, b: Int, c: Bool, d: Int) -> Int [{ affirm b >= 1; affirm a >= b; }] [{ }] { x = y; if c { x = y + a; affirm x > y; } else { x = y + b; affirm x > y; }; affirm x > y; if d > 0 { return x; }; return 0; }; return 0;", ControlValid )
            , ( "join-call-bound-restated-at-each-arm-end", "fn g(p: Int) -> Int [{ }] [{ affirm return <= p; }] { return p; }; fn f(y: Int, c: Bool) -> Int [{ }] [{ }] { w = y + 3; x = 0; if c { x = g(y + 2); affirm x <= w; } else { x = g(y + 3); affirm x <= w; }; affirm x <= w; return x; }; return 0;", ControlValid )
            , ( "join-alias-in-one-arm-keeps-call-bound", "fn h(p: Int) -> Int [{ }] [{ affirm return > p; }] { return p + 1; }; fn f(y: Int, c: Bool) -> Int [{ }] [{ }] { a = y; b = y; if c { a = h(y); b = a; } else { a = h(y); b = h(a); }; affirm b > y; return b; }; return 0;", ControlValid )
            , ( "fail-join-alias-in-one-arm-is-no-order", "fn h(p: Int) -> Int [{ }] [{ affirm return > p; }] { return p + 1; }; fn f(y: Int, c: Bool) -> Int [{ }] [{ }] { a = y; b = y; if c { a = h(y); b = a; } else { a = h(y); b = h(a); }; affirm b > a; return b; }; return 0;", ControlFails "Could not prove: b > a" )
            ]
        runRow (name, source, verdict) =
            ( name
            , case verdict of
                ControlValid -> parseValidProgramHelper source
                ControlFails err -> parseValidateFailProgramHelper source err
            )
     in testCaseNamedSeq "testIfJoin" (map runRow rows)

-- for i in lo..hi counts a loop variable, and the validator is given its bounds, its termination and (see
-- testInferredInvariants) what grows in step with it
testForLoops :: Test
testForLoops =
    let sumList = "fn total(a: List<Int>) -> Int { s = 0; for i in 0..size(a) { s = s + get(a, i); }; return s; };"
        parseFailsWith = parseFailsWithHelper
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
            , -- Locals the loop has nothing to do with change nothing: thirty of them, each with a bound
              -- through x, neither crowd out k (tied to s at the entry) nor spend the arithmetic's budget
              let unrelated = concat ["b" ++ show k ++ " = x + " ++ show k ++ "; " | k <- [0 .. 29 :: Int]]
               in parseValidProgramHelper ("fn f(n: Int, x: Int, k: Int) -> Int [{ affirm n >= 0; affirm n < 1000; affirm x >= 0; affirm x < 1000; affirm k >= 0; affirm k < 1000; }] [{ affirm return = k + n; }] { " ++ unrelated ++ "s = k; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { s = s + 1; i = i + 1; }; return s; };")
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
            , -- Element properties are explicit invariants, with their read bounds
              parseValidProgramHelper "fn f(v: Int, p: List<Int>) -> List<Int> [{ }] [{ affirm get(return, 1) = size(p); }] { out = push(push([], v), size(p)); for x in p [{ affirm size(out) >= 2; affirm get(out, 1) = size(p); }] { out = push(out, x); }; return out; };"
            , parseValidProgramHelper "fn f(p: List<Int>) -> List<Int> [{ }] [{ affirm get(return, 0) = 5; affirm get(return, 1) = 6; }] { out = [5, 6]; for x in p [{ affirm size(out) >= 2; affirm get(out, 0) = 5; affirm get(out, 1) = 6; }] { out = push(out, x); }; return out; };"
            , parseValidateFailProgramHelper "fn f(p: List<Int>) -> List<Int> [{ affirm size(p) > 0; }] [{ affirm get(return, 1) = 6; }] { out = [5, 6]; for i in 0..size(p) { out = set(out, 1, get(p, i)); }; return out; };" "Could not prove: get(return, 1) = 6 (in f)"
            , -- Scalar inference still works beside changing lists
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { a = [1, 2, 3]; b = [4, 5, 6]; i = 0; while i < n shrinks n - i { a = set(a, 0, 1); b = set(b, 0, 4); i = i + 1; }; affirm i = n; return 0; }; x = f(3);"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { a = [1, 2, 3]; b = [4, 5, 6]; i = 0; while i < n [{ affirm size(a) = 3; affirm get(a, 1) = 2; }] shrinks n - i { a = set(a, 0, 1); b = set(b, 0, 4); i = i + 1; }; affirm get(a, 1) = 2; return 0; }; x = f(3);"
            , -- A loop that returns infers its invariants too, one candidate at a time
              parseValidProgramHelper "fn f(a: List<Int>) -> Int { out = []; for i in 0..size(a) { if get(a, i) > 2 { return i; }; out = push(out, 0); }; return -1; };"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int { i = 0; while i < size(a) shrinks size(a) - i { if get(a, i) > 2 { return i; }; i = i + 1; }; affirm i = size(a); return -1; };"
            , parseValidateFailProgramHelper "fn f(a: List<Int>) -> Int { i = 0; while i < size(a) shrinks size(a) - i { if get(a, i) > 2 { return i; }; i = i + 1; }; affirm i = 0; return -1; };" "Could not prove: i = 0 (in f)"
            , -- Starting from something that is not a number: a copy of an argument, or a counter bounded by a parameter
              parseValidProgramHelper "fn f(a: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(a); }] { out = clone(a); for i in 0..size(a) { out = set(out, i, 0); }; return out; };"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int { c = clone(a); i = 0; while i < size(a) shrinks size(a) - i { c = set(c, i, 1); i = i + 1; }; affirm size(c) = size(a); return 0; };"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int { i = 0; n = size(a); while i < n shrinks n - i { i = i + 1; }; affirm i = n; return i; };"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = 0; while i < n shrinks n - i { i = i + 1; }; affirm i = n; return i; };"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int { i = 0; while i < n shrinks n - i { i = i + 1; }; affirm i = n; return i; };" "Could not prove: i = n"
            , parseValidateFailProgramHelper "fn f(a: List<Int>) -> Int { c = clone(a); i = 0; while i < size(a) shrinks size(a) - i { c = push(c, 0); i = i + 1; }; affirm size(c) = size(a); return 0; };" "Could not prove: size(c) = size(a)"
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
            , parseValidateFailProgramHelper (tree ++ "impl Clone for Tree { }; fn count(t: Box<Tree>) -> Int shrinks t { return match t { Tree::Leaf => 1, Tree::Branch { left: l, right: r } => count(clone(l)) + count(clone(t)) }; };") "Recursive call does not shrink the variant: t"
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
            , -- Two functions can call each other, but the cycle has to say what shrinks or be declared ~
              parseValidateFailProgramHelper "fn a(n: Int) -> Int { return b(n); }; fn b(n: Int) -> Int { return a(n); };" "Mutually recursive functions must say what shrinks"
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
                Right stmts -> case elaborateStatements stmts of
                    Ok (Elaborated [_, While _ _ (Just (Counting _)) _] _) -> Nothing
                    other -> Just ("Unexpected: " ++ show other)
            , case parseStatementBlock (tree ++ "t = Box::new(Tree::Leaf); while t is Tree::Branch shrinks t { t = (t as Tree::Branch).left; };") of
                Left err -> Just ("Parse error: " ++ show err)
                Right stmts -> case elaborateStatements stmts of
                    Ok (Elaborated [_, _, While _ _ (Just (Parts _)) _] _) -> Nothing
                    other -> Just ("Unexpected: " ++ show other)
            , case parseStatementBlock "fn f(n: Int) -> Int shrinks n { return 0; };" of
                Left err -> Just ("Parse error: " ++ show err)
                Right stmts -> case elaborateStatements stmts of
                    Ok (Elaborated [Assign _ (Val (VFunct _ _ _ (NativeFunct _ (Just (Counting _)) _) _))] _) -> Nothing
                    other -> Just ("Unexpected: " ++ show other)
            , parseValidateFailProgramHelper "x = [1]; while x = x shrinks x { x = x; };" "Loop variant does not shrink: x"
            , parseValidateFailProgramHelper "fn f(b: Bool) -> Int shrinks b { return 0; };" "shrinks needs an Int, an enum or a struct, got Bool"
            , -- Evaluation does not use any of it
              parseEvalProgramHelper "i = 0; while i < 3 shrinks 3 - i { i = i + 1; }; return i;" (Just (VInt 3))
            ]

-- Validation walks the control-flow graph of the MIR: the paths that meet are joined, loops are regions, a return ends a path
testCfgValidation :: Test
testCfgValidation =
    testCaseNamedSeq
        "testCfgValidation"
        (zip (map show [0 :: Int ..])
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
        , -- The variants earlier tests excluded are excluded at a block only when their false edges are the only way into it
          parseValidateFailProgramHelper "enum E { A, B, C }; fn f(e: E) -> Int { y = 0; if e is E::A { y = 1; }; if e is E::B { return 2; }; affirm y = 0; return y; }; x = f(E::A);" "Could not prove: y = 0"
        , parseValidateFailProgramHelper "enum E { A, B, C }; fn f(e: E) -> Int { y = 0; if e is E::A { y = 1; }; if e is E::B { return 2; }; return 10 / (1 - y); }; x = f(E::A);" "Could not prove"
        , bothEdgesOfATestIntoOneBlock
        ] ++
        [ ("p_constbool_a", parseValidateFailProgramHelper "fn f() -> Int { flag = false; flag = true; n = 1; while flag [{ affirm flag = true; }] shrinks n { affirm 1 = 2; flag = false; n = n - 1; }; return n; }; return f();" "Could not prove: an obligation could not be proved")
        , ("p_constbool_crash", parseValidateFailProgramHelper "fn f() -> Int { flag = false; flag = true; n = 1; x = 0; while flag [{ affirm flag = true; }] shrinks n { x = 10 / (n - 1); flag = false; n = n - 1; }; return x; }; return f();" "Could not prove: an obligation could not be proved")
        , ("q_while_false3", parseValidateFailProgramHelper "fn f() -> Int { n = 0; while false [{ affirm n >= 0; }] shrinks n { return 5; }; affirm 1 = 2; return n; }; return f();" "Could not prove: 1 = 2")
        , ("q_while_false4", parseValidateFailProgramHelper "fn f() -> Int { n = 0; while false [{ affirm n >= 0; }] shrinks n { return 5; }; x = 10 / n; return x; }; return f();" "Could not prove: an obligation could not be proved")
        , ("while-true-returns-inside", parseValidateEvalProgramHelper "fn f() -> Int [{ }] [{ affirm return = 5; }] { n = 0; while true shrinks n { return 5; }; return 0; }; return f();" (Just (VInt 5)))
        , ("while-true-counts-to-return", parseValidateEvalProgramHelper "i = 0; while true [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { if i = 3 { return i; }; i = i + 1; };" (Just (VInt 3)))
        , ("true-bool-local-returns-inside", parseValidateEvalProgramHelper "fn f() -> Int [{ }] [{ affirm return = 5; }] { flag = true; n = 0; while flag [{ affirm flag = true; }] shrinks n { return 5; }; return 0; }; return f();" (Just (VInt 5)))
        , ("reassigned-true-bool-local-returns-inside", parseValidateEvalProgramHelper "fn f() -> Int [{ }] [{ affirm return = 5; }] { flag = false; flag = true; n = 0; while flag [{ affirm flag = true; }] shrinks n { return 5; }; return 0; }; return f();" (Just (VInt 5)))
        , ("false-bool-local-skips-body", parseValidateEvalProgramHelper "fn f() -> Int [{ }] [{ affirm return = 0; }] { flag = false; n = 0; while flag [{ affirm flag = false; affirm n >= 0; }] shrinks n { return 5; }; affirm n = 0; return n; }; return f();" (Just (VInt 0)))
        , ("while-false-skips-body", parseValidateEvalProgramHelper "fn f() -> Int [{ }] [{ affirm return = 0; }] { n = 0; while false [{ affirm n >= 0; }] shrinks n { return 5; }; affirm n = 0; return n; }; return f();" (Just (VInt 0)))
        ] ++ sweepRegressions ++ loopCandidateRegressions)

-- One run per block: a branch costs its arms, an empty join forwards, a latch
-- and a return run once per arrival, and what only one arm knows is lost at
-- the merge (sequential ifs in a loop body are not correlated).
sweepRegressions :: [(String, TestResult)]
sweepRegressions =
    [ ( "sweep-nested-empty-joins-three-deep-in-a-loop"
      , parseValidProgramHelper "fn f(n: Int, a: Int, b: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { s = 0; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; affirm s <= i; }] shrinks n - i { if a > 0 { if b > 0 { if c > 0 { s = s + 1; }; }; }; i = i + 1; }; return s; }; return f(3, 1, 1, 1);" )
    , ( "sweep-eight-sequential-diamonds-in-a-loop"
      , parseValidProgramHelper
            ( "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { x = 0; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; affirm x >= 0; }] shrinks n - i { "
                ++ concat (replicate 8 "if c > 0 { x = x + 1; } else { x = x + 2; }; ")
                ++ "i = i + 1; }; return x; }; return f(2, 1);" ) )
    , ( "sweep-fourteen-ifs-in-a-loop-body"
      , parseValidProgramHelper
            ( "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { x = 0; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { "
                ++ concat (replicate 14 "if c > 0 { x = x + 1; } else { x = x + 2; }; ")
                ++ "i = i + 1; }; return x; }; return f(2, 1);" ) )
    , ( "sweep-fourteen-independent-ifs"
      , parseValidProgramHelper
            ( "fn f(c: Int) -> Int [{ }] [{ }] { x = 0; "
                ++ concat (replicate 14 "if c > 0 { x = x + 1; } else { x = x + 2; }; ")
                ++ "affirm x > 0; return x; }; return f(1);" ) )
    , ( "sweep-unequal-arms-with-a-nested-diamond"
      , parseValidProgramHelper "fn f(c: Bool, d: Bool) -> Int [{ }] [{ }] { x = 0; if c { x = x + 1; if d { x = x + 0; } else { x = x + 0; }; } else { x = x + 2; }; affirm x > 0; return x; }; return 0;" )
    , ( "sweep-unequal-arms-with-a-nested-diamond-reversed"
      , parseValidProgramHelper "fn f(c: Bool, d: Bool) -> Int [{ }] [{ }] { x = 0; if c { x = x + 2; } else { x = x + 1; if d { x = x + 0; } else { x = x + 0; }; }; affirm x > 0; return x; }; return 0;" )
    , ( "sweep-three-way-else-if"
      , parseValidProgramHelper "fn f(a: Int) -> Int [{ }] [{ }] { x = 0; if a > 5 { x = x + 1; } else { if a > 2 { x = x + 2; } else { x = x + 3; }; }; affirm x > 0; return x; }; return 0;" )
    , ( "sweep-nested-diamonds-in-both-arms"
      , parseValidProgramHelper "fn f(a: Int, b: Int) -> Int [{ }] [{ }] { x = 0; if a > 0 { if b > 0 { x = x + 1; } else { x = x + 2; }; } else { if b > 0 { x = x + 3; } else { x = x + 4; }; }; affirm x > 0; affirm x < 5; return x; }; return f(1, 1);" )
    , ( "sweep-sequential-matches"
      , parseValidProgramHelper "enum E { A, B, C }; fn f(e: E) -> Int [{ }] [{ }] { x = 0; if e is E::A { x = 1; } else { if e is E::B { x = 2; } else { x = 3; }; }; y = 0; if e is E::C { y = 1; } else { y = 2; }; affirm x > 0; affirm y > 0; return x + y; }; return f(E::A);" )
    , ( "sweep-guards-with-early-returns"
      , parseValidProgramHelper "fn f(n: Int) -> Int [{ }] [{ affirm return != 0; }] { if n > 3 { return 1; }; if n < 0 { return -1; }; if n = 2 { return 7; }; affirm n >= 0; affirm n <= 3; return n + 10; }; return f(1);" )
    , ( "sweep-return-postcondition-per-path"
      , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ }] [{ affirm return > 0; }] { if n > 3 { return 1; }; if n < 0 { return -1; }; return 7; }; return f(1);" "Could not prove: return > 0" )
    , ( "sweep-variant-changes-before-a-branch"
      , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; c = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { i = i + 1; if i > 2 { c = c + 1; } else { c = c + 2; }; }; return c; }; return f(3);" )
    , ( "sweep-nested-loop-with-an-early-return"
      , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= 0; }] { s = 0; for i in 0..n { for j in 0..n { if i + j > 3 { return i + j; }; s = s + 1; }; }; affirm s >= 0; return s; }; return f(3);" )
      -- The inner loop always returns, so its region does not reach the outer header
      -- and lies outside the outer loop's region
    , ( "sweep-always-returning-inner-loop-outside-the-outer-region"
      , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= 0; }] { i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { j = 0; while j < n [{ affirm j >= 0; }] shrinks n - j { return j; }; i = i + 1; }; return 0; }; return f(2);" )
    , ( "sweep-fail-false-equality-after-a-loop-body-merge"
      , parseValidateFailProgramHelper "fn f(n: Int, y: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { x = y; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { if c > 0 { x = y; } else { x = y + 1; }; affirm x = y; i = i + 1; }; return x; }; return 0;" "Could not prove: x = y" )
    , ( "sweep-fail-one-arm-resets-to-the-bound-in-a-loop"
      , parseValidateFailProgramHelper "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { x = 5; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { if c > 0 { x = x + 1; } else { x = 0; }; affirm x > 0; i = i + 1; }; return x; }; return 0;" "Could not prove: x > 0" )
    , ( "sweep-fail-literal-not-aliased-in-a-loop"
      , parseValidateFailProgramHelper "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { m = 1; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { if c > 0 { m = 1; } else { m = 2; }; affirm m >= 3; i = i + 1; }; return m; }; return 0;" "Could not prove: m >= 3" )
      -- The accepted limit: the second if's branch block runs once on the merge, so
      -- what the first if chose is gone; doing the work in the first if restates it
    , ( "sweep-fail-sequential-ifs-in-a-loop-are-not-correlated"
      , parseValidateFailProgramHelper "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { s = 0; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { y = 0; if c > 0 { y = 1; }; if c > 0 { s = s + 10 / y; }; i = i + 1; }; return s; }; return 0;" "Could not prove" )
    , ( "sweep-fail-and-loop-left-by-a-later-conjunct"
      , parseValidateFailProgramHelper "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; while i < n && c > 0 [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { i = i + 1; }; affirm i >= n; return i; }; return f(3, 1);" "Could not prove: i >= n" )
    , ( "sweep-and-loop-left-by-a-later-conjunct-keeps-the-invariant"
      , parseValidProgramHelper "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; while i < n && c > 0 [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { i = i + 1; }; affirm i <= n; return i; }; return f(3, 1);" )
      -- The inner loop's later conjunct leaves it straight to the outer loop's latch
    , ( "sweep-nested-and-loop-left-to-the-outer-latch"
      , parseValidProgramHelper "fn f(n: Int, m: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { i = i + 1; j = 0; while j < m && c > 0 [{ affirm j >= 0; }] shrinks m - j { j = j + 1; }; }; return i; }; return f(2, 2, 1);" )
    , ( "sweep-fail-nested-and-loop-exit-checks-the-outer-variant"
      , parseValidateFailProgramHelper "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { while i < n && c > 0 [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { i = i + 1; }; }; return i; }; return f(2, 1);" "Loop variant does not shrink" )
    , ( "sweep-fail-and-loop-returning-inside-an-outer-loop"
      , parseValidateFailProgramHelper "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= 1; }] { i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { j = 0; while j < n && c > 0 [{ affirm j >= 0; }] shrinks n - j { return j; }; i = i + 1; }; return 5; }; return f(2, 1);" "Could not prove: return >= 1" )
    , ( "sweep-sequential-ifs-in-a-loop-restated-as-one"
      , parseValidProgramHelper "fn f(n: Int, c: Int) -> Int [{ affirm n >= 0; }] [{ }] { s = 0; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { y = 0; if c > 0 { y = 1; s = s + 10 / y; }; i = i + 1; }; return s; }; return f(2, 1);" )
    ]

loopCandidateRegressions :: [(String, TestResult)]
loopCandidateRegressions =
    [ ("p_oob_withpush", rejected (emptyListBranch "a = push(clone(l), 7); affirm 1 = 2;"))
    , ("p_oob_read", rejected (emptyListBranch "a = push(clone(l), 7); x = 10 / (size(a) - 1);"))
    , ("p_oob_nopush", rejected (emptyListBranch "affirm 1 = 2;"))
    , ("p_oob_read_ctl", parseValidateEvalProgramHelper (emptyListBranch "a = push(clone(l), 7); x = 10 / (size(a) - 2);") (Just (VInt (-10))))
    , ("q_ic_crash", rejected "fn f(k: Int) -> Int [{ affirm k <= 20; }] [{ }] { l = [7, 8, 9]; i = k; x = 0; while i < 20 [{ affirm i <= 20; }] shrinks 20 - i { x = 10 / (i - i); l = set(l, 0, i); i = i + 1; }; return x; }; return f(0);")
    , ("inferred-scalar-distance-through-temporaries", parseValidateEvalProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 10; }] { a = 10; b = 13; c = 16; while a < n [{ affirm a <= n; }] shrinks n - a { a = a + 1; b = b + 1; c = c + 1; }; affirm b = a + 3; affirm c = b + 3; return c; }; return f(12);" (Just (VInt 18)))
    , ("inferred-size-counter-distance", parseValidateEvalProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { out = [7, 8, 9]; i = 0; while i < n [{ affirm i <= n; }] shrinks n - i { out = push(out, i); i = i + 1; }; affirm size(out) = i + 3; return size(out); }; return f(2);" (Just (VInt 5)))
    ] ++
    [ (name, rejected (constantLoop prefix ("affirm 1 = 2; " ++ body)))
    | (name, prefix, body) <-
        [ ("q_ic_a", "l = [7, 8, 9];", "x = get(l, 0); i = i + 1;")
        , ("q_ic_b", "l = [7, 8, 3];", "l = set(l, 0, i); i = i + 1;")
        , ("q_ic_c", "z = 3; l = [7, 8, 9];", "l = set(l, 0, i); i = i + 1;")
        , ("q_ic_d", "l = [7, 8, 9];", "l = set(l, 1, i); i = i + 1;")
        , ("q_ic_e", "l = [7, 8];", "l = set(l, 0, i); i = i + 1;")
        , ("q_ic_f", "l = [7];", "l = set(l, 0, i); i = i + 1;")
        , ("q_ic_g", "l = [7, 8, 9];", "l = push(l, i); i = i + 1;")
        , ("q_ic_h", "l = [7, 8, 9, 10, 11];", "l = set(l, 0, i); i = i + 1;")
        , ("q_ic_i", "l = [7, 8, 9];", "l = set(l, 2, i); i = i + 1;")
        , ("q_ic_j", "l = [7, 8]; z = 2;", "l = set(l, 0, i); i = i + 1;")
        , ("q_ic_k", "l = [7, 8, 9];", "l = set(l, 0, 7); i = i + 1;")
        , ("q_ic_l", "l = [7, 8, 9]; j = 0;", "l = set(l, 0, i); j = j + 1; i = i + 1;")
        , ("q_ic_m", "l = [7, 7, 7];", "l = set(l, 0, 7); i = i + 1;")
        , ("q_ic_n", "l = [7, 8, 9];", "l = set(l, 0, i); i = i + 5;")
        , ("q_ic_o", "l = [7, 8, 9];", "l = set(l, 0, 5); i = i + 5;")
        , ("q_ic_counters", "a = 10; b = 13; c = 16;", "a = a + 1; b = b + 1; c = c + 1; i = i + 1;")
        , ("q_ic_allconst_ctl", "l = [7, 8, 9];", "l = set(l, 0, 5); i = i + 5;")
        , ("q_ic_allconst", allConstants ++ "l = [7, 8, 9];", "l = set(l, 0, 5); i = i + 5;")
        ]
    ] ++
    [ ("q_ic_shift" ++ show count, rejected (constantLoop "l = [7, 8, 9];" ("affirm 1 = 2; " ++ concat ["w" ++ show w ++ " = i; " | w <- [1 .. count]] ++ "l = set(l, 0, 5); i = i + 5;")))
    | count <- [0, 1, 2, 3, 4, 6 :: Int]
    ] ++
    [ ("q_ic_p", rejected "fn f(k: Int, l0: List<Int>) -> Int [{ affirm k <= 20; affirm size(l0) = 3; }] [{ }] { l = l0; i = k; while i < 20 [{ affirm i <= 20; }] shrinks 20 - i { affirm 1 = 2; l = set(l, 0, i); i = i + 1; }; return i; }; return f(0, [1, 2, 3]);")
    ]
  where
    rejected source = parseValidateFailProgramHelper source "Could not prove: "
    emptyListBranch body = "fn f() -> Int { l = [5]; x = 0; i = 0; while i < 2 [{ affirm i >= 0; }] shrinks 2 - i { if size(l) = 0 { " ++ body ++ " } else { l = pop(l); }; i = i + 1; }; return x; }; return f();"
    constantLoop prefix body = "fn f(k: Int) -> Int [{ affirm k <= 20; }] [{ }] { " ++ prefix ++ " i = k; while i < 20 [{ affirm i <= 20; }] shrinks 20 - i { " ++ body ++ " }; return i; }; return f(0);"
    allConstants = concat ["z" ++ show index ++ " = " ++ (if value < 0 then "0 - " ++ show (-value) else show value) ++ "; " | (index, value) <- zip [0 :: Int ..] [-12 .. 24 :: Int]]

-- A test whose two edges go to the same block is two ways into it. Source
-- lowers each edge to a block of its own, so the program is lowered and its
-- first test is then pointed straight at the block both arms jump to.
bothEdgesOfATestIntoOneBlock :: TestResult
bothEdgesOfATestIntoOneBlock = case lowerSource True "enum E { A, B, C }; fn f(e: E) -> Int { if e is E::A { } else { }; if e is E::B { return 2; }; if e is E::A { affirm 1 = 2; }; return 0; }; x = f(E::A);" of
    Error e -> Just e
    Ok program
        | functions == M.progFunctions program -> Just "No test with two empty arms to join"
        | otherwise -> testAssertErrorContains "Could not prove: 1 = 2" (validateCompiled program{M.progFunctions = functions})
      where
        functions = Map.map joinArms (M.progFunctions program)
  where
    joinArms fn = case Map.lookup (M.BlockId 0) (M.fnBlocks fn) of
        Just (M.BasicBlock stmts (M.SwitchBool condition yes no))
            | Just target <- jumpOnly yes
            , jumpOnly no == Just target ->
                fn{M.fnBlocks = Map.insert (M.BlockId 0) (M.BasicBlock stmts (M.SwitchBool condition target target)) (Map.delete yes (Map.delete no (M.fnBlocks fn)))}
        _ -> fn
      where
        jumpOnly b = case Map.lookup b (M.fnBlocks fn) of
            Just (M.BasicBlock [] (M.Goto target)) -> Just target
            _ -> Nothing
