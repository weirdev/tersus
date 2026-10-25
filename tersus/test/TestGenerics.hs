module TestGenerics (testGenerics) where

import TersusTypes
import TestHarness

-- Type parameters: `fn first<T>(a: &List<T>) -> T` is written once for any type. A name that starts with a capital letter between the
-- `<>` is a type, any other is a size. The types are decided by the arguments, and native code is made for each list of them.
testGenerics :: Test
testGenerics =
    let runs body expected = parseEvalProgramHelper body (Just expected)
        valid = parseValidProgramHelper
        rejected = parseValidateFailProgramHelper
        parseFails source = case parseValidProgramHelper source of
            Just err | take 11 err == "Parse faile" -> Nothing
            _ -> Just ("Expected a parse error for: " ++ source)
        lead = "fn lead<T>(a: &List<T>) -> T [{ define s = size(a); rewrite eqToGtZero s; affirm s > 0; }] [{ }] { return get(a, 0); }; "
     in TestList
            "testGenerics"
            [ TestList
                "one function for any type"
                [ testCase "an Int" (runs (lead ++ "return lead(push([], 7)) + 1;") (VInt 8))
                , testCase "a Bool" (runs (lead ++ "return lead(push([], true));") (VBool True))
                , testCase "a list" (runs (lead ++ "return lead(push([], push([], 3)));") (VList [VInt 3]))
                , testCase "a struct" (runs (lead ++ "struct P { x: Int }; return lead(push([], P { x: 4 })).x;") (VInt 4))
                , testCase "several types in one program" (runs (lead ++ "return lead(push([], 7)) + size(lead(push([], push([], 1)))) + 10;") (VInt 18))
                , testCase "the type is a parameter and a result" (runs "fn id<T>(a: T) -> T { return a; }; l = id(push([], 3)); return id(l);" (VList [VInt 3]))
                , testCase "two arguments of one type" (runs "fn same<T>(a: T, b: T) -> Bool { return a = b; }; return same(1, 1) = same(true, false);" (VBool False))
                , testCase "two types" (runs "fn pick<A, B>(a: A, b: B) -> B { return b; }; return pick(1, push([], 3));" (VList [VInt 3]))
                , testCase "a type in an array and a list" (runs "fn pair<T>(a: T, b: T) -> Array<T, 2> { return set(array(2, a), 1, b); }; return pair(1, 2);" (VList [VInt 1, VInt 2]))
                , testCase "a list is grown" (runs "fn grow<T>(a: List<T>, x: T) -> List<T> { return push(a, x); }; return grow(grow(push([], true), false), true);" (VList [VBool True, VBool False, VBool True]))
                , testCase "a Box" (runs "fn wrap<T>(a: T) -> Box<T> { return Box::new(a); }; return Box::unbox(wrap(push([], 2)));" (VList [VInt 2]))
                , testCase "a loop that builds a list of any type" (runs "fn mk<T>(x: T, n: Int) -> List<T> [{ define s = n; affirm s >= 0; }] [{ }] { out = []; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { out = push(out, x); i = i + 1; }; return out; }; return mk(push([], 4), 2);" (VList [VList [VInt 4], VList [VInt 4]]))
                , testCase "a type and a size together" (runs "fn fill<T, n>(a: &Array<T, n>, x: T) -> Array<T, n> [{ define k = n; rewrite eqToGtZero k; affirm k > 0; }] [{ }] { return set(a, 0, x); }; return fill(#[true, true], false);" (VList [VBool False, VBool True]))
                , testCase "a function calls another with its type" (runs "fn count<T>(a: &List<T>) -> Int { return size(a); }; fn twice<T>(a: &List<T>) -> Int { return count(a) + count(a); }; return twice(push([], 1)) + twice(push([], true));" (VInt 4))
                , testCase "a type that nothing decides is an Int" (runs "fn nil<T>() -> List<T> { return []; }; return size(nil());" (VInt 0))
                , testCase "a lent parameter of a type" (runs "fn twice<T>(a: &T) -> Array<T, 2> { return array(2, a); }; return twice(push([], 5));" (VList [VList [VInt 5], VList [VInt 5]]))
                ]
            , TestList
                "validation"
                [ testCase "a contract about the values is checked" (rejected (lead ++ "return lead([]);") "Proof term is not greater than 0")
                , testCase "and met" (valid (lead ++ "return lead([5]);"))
                , testCase "an index past the end" (rejected "fn past<T>(a: &List<T>) -> T { return get(a, 0); }; return past([1]);" "Relation lacks a proof")
                ]
            , TestList
                "types"
                [ testCase "a type is not an Int" (rejected "fn bad<T>(a: T) -> Int { return a + 1; }; return 0;" "expected Int, got T")
                , testCase "the arguments agree on it" (rejected "fn same<T>(a: T, b: T) -> Bool { return a = b; }; return same(1, true);" "argument 2 of same: expected Int, got Bool")
                , testCase "a type has to be declared" (rejected "fn bad(a: T) -> Int { return 0; }; return 0;" "unknown type T")
                , testCase "a type is not a function" (rejected "fn id<T>(a: T) -> T { return a; }; fn inc(n: Int) -> Int { return n + 1; }; f = id(inc); return 0;" "a type parameter is not a function")
                , testCase "the function is called, not named" (rejected "fn id<T>(a: T) -> T { return a; }; h = id; return 0;" "id has parameters <T>, so it is called")
                , testCase "an impl has none" (rejected "struct S { x: Int }; impl S { fn f<T>(a: T) -> T { return a; }; }; return 0;" "type parameters, which a function of an impl cannot have yet")
                , testCase "a name that is not a capital is a size" (rejected "fn f<t>(a: t) -> Int { return 0; }; return 0;" "unknown type t")
                , testCase "a type is not in a nested function" (rejected "fn outer<T>(a: T) -> Int { fn inner(b: T) -> Int { return 0; }; return 0; }; return 0;" "unknown type T")
                , testCase "the declaration is parsed with spaces" (runs "fn second < A , B > (a: A, b: B) -> B { return b; }; return second(3, true);" (VBool True))
                ]
            ]
