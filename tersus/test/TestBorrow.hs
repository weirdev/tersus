module TestBorrow (testBorrow) where

import TersusTypes
import TestHarness

-- &T: a parameter that the function only reads. A call lends the value, so it is not copied for the call and the caller keeps it; in
-- the function the parameter is its type, which it cannot assign.
testBorrow :: Test
testBorrow =
    let runs body expected = parseEvalProgramHelper body (Just expected)
        valid = parseValidProgramHelper
        rejected = parseValidateFailProgramHelper
        parseFails source = case parseValidProgramHelper source of
            Just err | take 11 err == "Parse faile" -> Nothing
            _ -> Just ("Expected a parse error for: " ++ source)
        total = "fn total(a: &List<Int>) -> Int [{ define s = size(a); affirm s >= 0; }] [{ }] { t = 0; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i { t = t + get(a, i); i = i + 1; }; return t; }; "
     in TestList
            "testBorrow"
            [ TestList
                "lending"
                [ testCase "a list is lent" (runs (total ++ "l = push(push([], 3), 4); return total(l);") (VInt 7))
                , testCase "and the caller keeps it" (runs (total ++ "l = push(push([], 3), 4); return total(l) + total(l) + size(l);") (VInt 16))
                , testCase "a value that is made for the call is lent" (runs (total ++ "return total(push(push([], 1), 2));") (VInt 3))
                , testCase "an array is lent" (runs "fn ends(a: &Array<Int, 4>) -> Int { return get(a, 0) + get(a, 3); }; x = #[1, 2, 3, 4]; return ends(x) + get(x, 1);" (VInt 7))
                , testCase "a struct is lent" (runs "struct S { xs: List<Int>, n: Int }; fn count(s: &S) -> Int { return size(s.xs) + s.n; }; s = S { xs: push([], 1), n: 10 }; return count(s) + size(s.xs);" (VInt 12))
                , testCase "an Int is lent too" (runs "fn twice(n: &Int) -> Int { return n * 2; }; return twice(4);" (VInt 8))
                , testCase "a lent parameter is passed on to a lent one" (runs "fn inner(a: &List<Int>) -> Int { return size(a); }; fn outer(a: &List<Int>) -> Int { return inner(a) + inner(a) + size(a); }; return outer(push([], 1));" (VInt 3))
                , testCase "and to one that is owned, which gets a copy" (runs "fn owner(a: List<Int>) -> Int { return size(push(a, 1)); }; fn mixed(a: &List<Int>) -> Int { return owner(a) + size(a); }; return mixed(push([], 1));" (VInt 3))
                , testCase "a lent parameter is returned as a copy" (runs "fn same(a: &List<Int>) -> List<Int> { return a; }; l = push([], 5); m = same(l); m = push(m, 6); return l;" (VList [VInt 5]))
                , testCase "a copy of it can be changed" (runs "fn more(a: &List<Int>) -> List<Int> { return push(a, 9); }; l = push([], 1); return more(l);" (VList [VInt 1, VInt 9]))
                , testCase "an array that is lent can give a changed copy" (runs "fn bump(a: &Array<Int, 3>) -> Array<Int, 3> { return set(a, 0, get(a, 0) + 1); }; x = #[1, 2, 3]; x = bump(x); return bump(x);" (VList [VInt 3, VInt 2, VInt 3]))
                , testCase "a lent parameter is also an owned one in one call" (runs "fn both(a: &List<Int>, b: List<Int>) -> Int { return size(a) + size(b); }; l = push([], 1); return both(l, l);" (VInt 2))
                , testCase "a value that is lent and given in one call is not shared" (runs "fn both(a: &List<Int>, b: List<Int>) -> Int { b = push(b, 9); return size(a) * 10 + size(b); }; l = push([], 1); return both(l, l);" (VInt 12))
                , testCase "an empty list is lent as the type of the parameter" (runs "fn count(a: &List<Bool>) -> Int { return size(a); }; return count([]) + count([true]);" (VInt 1))
                , testCase "a function with sizes lends" (runs "fn count<n>(a: &Array<Int, n>) -> Int { return n; }; return count(#[1, 2, 3]);" (VInt 3))
                ]
            , TestList
                "validation"
                [ testCase "the contract of a lent parameter is checked" (rejected "fn lead(a: &List<Int>) -> Int [{ define s = size(a); rewrite eqToGtZero s; affirm s > 0; }] [{ }] { return get(a, 0); }; return lead([]);" "Proof term is not greater than 0")
                , testCase "and met" (valid "fn lead(a: &List<Int>) -> Int [{ define s = size(a); rewrite eqToGtZero s; affirm s > 0; }] [{ }] { return get(a, 0); }; return lead([4]);")
                , testCase "what a lent value was is known after the call" (valid (total ++ "l = push([], 3); n = total(l); affirm size(l) = 1; return n;"))
                , testCase "an index past the end of a lent array" (rejected "fn past(a: &Array<Int, 2>) -> Int { return get(a, 2); }; return past(#[1, 2]);" "Relation lacks a proof")
                ]
            , TestList
                "types"
                [ testCase "a lent parameter is not assigned" (rejected "fn f(a: &List<Int>) -> Int { a = push(a, 1); return 0; }; return f([]);" "a is borrowed (&), so it is only read")
                , testCase "a call gives the value, not a reference" (rejected "fn f(a: &List<Int>) -> Int { return 0; }; return f(3);" "argument 1 of f: expected List<Int>, got Int")
                , testCase "a & is for a parameter, not a result" (rejected "fn f() -> &List<Int> { return []; }; return 0;" "& is for the parameter of a function")
                , testCase "nor a field" (rejected "struct S { a: &List<Int> }; return 0;" "& is for the parameter of a function")
                , testCase "nor a Box" (rejected "fn f(a: Box<&Int>) -> Int { return 0; }; return 0;" "& is for the parameter of a function")
                , testCase "a function value lends too" (valid "fn total(a: &List<Int>) -> Int { return size(a); }; f = total; return 0;")
                , testCase "a function that lends is not a function that does not" (rejected "fn total(a: &List<Int>) -> Int { return size(a); }; fn apply(f: fn(List<Int>) -> Int) -> Int { return 0; }; return apply(total);" "expected fn(List<Int>) -> Int, got fn(&List<Int>) -> Int")
                , testCase "the & can have spaces" (runs "fn f(a: & List<Int>) -> Int { return size(a); }; return f([1]);" (VInt 1))
                , testCase "a & needs a type" (parseFails "fn f(a: &) -> Int { return 0; }; return 0;")
                ]
            ]
