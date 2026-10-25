module TestSequence (testSequence) where

import Data.List (isInfixOf, tails)

import Cli (Command (..), runSource)
import Pipeline (compileSource)
import TersusTypes
import TestHarness
import Utils

-- What a list written in the language needs: a contract that calls functions (`affirm i < size(v);`), an invariant that every value of a
-- struct meets, a trait with types (`trait Sequence<E>`) that a struct with types implements, and `size`, `get`, `set` and `push` that
-- are the functions of the impl when they are called on a struct. The list itself, `Vec<T>`, is the library of examples/vec.tersus.
testSequence :: Test
testSequence =
    let runs body expected = parseEvalProgramHelper body (Just expected)
        valid = parseValidProgramHelper
        rejected = parseValidateFailProgramHelper
        parseFails source = case parseValidProgramHelper source of
            Just err | take 11 err == "Parse faile" -> Nothing
            _ -> Just ("Expected a parse error for: " ++ source)
        double = "fn double(x: Int) -> Int [{ }] [{ affirm return = x * 2; }] { return x * 2; }; "
        counted = "struct V<T> { x: T, len: Int }; "
        trait2 = "trait Seq<E> { fn size(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; fn get(self: &Self, i: Int) -> E [{ affirm i >= 0; affirm i < size(self); }] [{ }]; fn push(self: Self, x: E) -> Self [{ }] [{ affirm size(return) = size(self) + 1; }]; }; "
        two = "struct Two<T> { a: T, b: T, n: Int } invariant [{ affirm n >= 0; }]; impl<T> Seq<T> for Two<T> { fn size(self: &Self) -> Int [{ }] [{ affirm return = self.n; }] { return self.n; }; fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < size(self); }] [{ }] { if i = 0 { return self.a; }; return self.b; }; fn push(self: Self, x: T) -> Self [{ }] [{ affirm size(return) = size(self) + 1; }] { return Self { a: self.a, b: x, n: self.n + 1 }; }; }; "
     in TestList
            "testSequence"
            [ TestList
                "functions in contracts"
                [ testCase "a call in a requires is proved from the promise of the function" (runs (double ++ "fn f(a: Int) -> Int [{ affirm double(a) > 4; }] [{ affirm return = double(a); }] { return a * 2; }; return f(3);") (VInt 6))
                , testCase "and a caller has to meet it" (rejected (double ++ "fn f(a: Int) -> Int [{ affirm double(a) > 4; }] [{ }] { return a * 2; }; return f(1);") "Could not prove: double(a) > 4")
                , testCase "the call has to meet the input contract of the function" (rejected "fn pos(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return = x; }] { return x; }; fn f(a: Int) -> Int [{ affirm pos(a) > 4; }] [{ }] { return a; }; return f(7);" "Could not prove: x > 0")
                , testCase "in a promise" (runs (double ++ "fn g(a: Int) -> Int [{ }] [{ affirm return = double(a); }] { return a + a; }; return g(4);") (VInt 8))
                , testCase "and one that is not true is refused" (rejected (double ++ "fn g(a: Int) -> Int [{ }] [{ affirm return = double(a) + 1; }] { return a + a; }; return g(4);") "Could not prove: return = double(a) + 1")
                , testCase "a call of a call" (runs (double ++ "fn g(a: Int) -> Int [{ }] [{ affirm double(double(a)) = a * 4; }] { return a; }; return g(2);") (VInt 2))
                , testCase "in an invariant of a loop" (runs (double ++ "i = 0; while i < 5 [{ affirm i >= 0; affirm i <= 5; affirm double(i) = i * 2; }] shrinks 5 - i { i = i + 1; }; return double(i);") (VInt 10))
                , testCase "a function with types" (runs (counted ++ "fn count<T>(s: &V<T>) -> Int [{ }] [{ affirm return = s.len; }] { return s.len; }; fn h<T>(s: V<T>) -> V<T> [{ }] [{ affirm count(return) = count(s) + 1; }] { return V<T> { x: s.x, len: s.len + 1 }; }; return h(V<Int> { x: 1, len: 1 }).len;") (VInt 2))
                , testCase "a function of an impl by its path" (runs (counted ++ "impl<T> V<T> { fn count(self: &Self) -> Int [{ }] [{ affirm return = self.len; }] { return self.len; }; fn bump(self: Self) -> Self [{ }] [{ affirm V::count(return) = V::count(self) + 1; }] { return Self { x: self.x, len: self.len + 1 }; }; }; return V<Int> { x: 1, len: 1 }.bump().len;") (VInt 2))
                , testCase "a function that may not end is not called" (rejected "fn spin(x: Int) -> Int [{ }] [{ affirm return = x; }] ~ { return spin(x); }; fn f(a: Int) -> Int [{ }] [{ affirm spin(a) = a; }] { return a; }; return f(1);" "declared ~")
                , testCase "a name that is not a function" (rejected "x = 1; affirm bogus(x); return 0;" "Variable not found in proof map: bogus")
                , testCase "its arguments have the types" (rejected (double ++ "fn f(a: Int) -> Int [{ affirm double(true) > 4; }] [{ }] { return a; }; return 0;") "argument 1 of double")
                ]
            , TestList
                "invariants of structs"
                [ testCase "a struct made to meet it" (runs "struct Counter { n: Int } invariant [{ affirm n >= 0; }]; fn bump(c: Counter) -> Counter [{ }] [{ affirm return.n >= 1; }] { return Counter { n: c.n + 1 }; }; fn zero() -> Counter [{ }] [{ }] { return Counter { n: 0 }; }; return bump(zero()).n;" (VInt 1))
                , testCase "one that does not is refused" (rejected "struct Counter { n: Int } invariant [{ affirm n >= 0; }]; fn drop1(c: Counter) -> Counter [{ }] [{ }] { return Counter { n: c.n - 1 }; }; return drop1(Counter { n: 5 }).n;" "A Counter is made that does not meet its invariant: Could not prove: n >= 0")
                , testCase "also when it is written as a constant" (rejected "struct Counter { n: Int } invariant [{ affirm n >= 0; }]; return Counter { n: 0 - 1 }.n;" "does not meet its invariant")
                , testCase "any value has it" (valid "struct Counter { n: Int } invariant [{ affirm n >= 0; }]; fn f(c: Counter) -> Int [{ }] [{ affirm return >= 0; }] { return c.n; }; return f(Counter { n: 3 });")
                , testCase "a field that is read has the invariant of its own struct" (valid "struct Counter { n: Int } invariant [{ affirm n >= 0; }]; struct Pair { a: Counter, b: Counter }; fn f(p: Pair) -> Int [{ }] [{ affirm return >= 0; }] { return p.a.n + p.b.n; }; return f(Pair { a: Counter { n: 1 }, b: Counter { n: 2 } });")
                , testCase "an update has to keep it" (rejected "struct R { lo: Int, hi: Int } invariant [{ affirm lo <= hi; }]; fn widen(r: R) -> R [{ }] [{ }] { return R { lo: r.hi + 1, ..r }; }; return widen(R { lo: 1, hi: 2 }).lo;" "does not meet its invariant")
                , testCase "of a struct with types" (runs "struct Box2<T> { a: T, n: Int } invariant [{ affirm n >= 0; }]; fn f<T>(b: Box2<T>) -> Int [{ }] [{ affirm return >= 0; }] { return b.n; }; return f(Box2<Bool> { a: true, n: 3 });" (VInt 3))
                , testCase "with a size in a field" (valid "struct Buf { data: Box<Array<Int>>, used: Int } invariant [{ affirm used >= 0; affirm used <= size(data); }]; fn fill(b: Buf) -> Int [{ }] [{ affirm return <= size(b.data); }] { return b.used; }; return fill(Buf { data: Array::boxed(4, 0), used: 2 });")
                , testCase "it names the fields" (rejected "struct Counter { n: Int } invariant [{ affirm m >= 0; }]; return Counter { n: 1 }.n;" "Variable not found in proof map: m")
                , testCase "and is about booleans" (rejected "struct Counter { n: Int } invariant [{ affirm n; }]; return 0;" "affirmed proof")
                ]
            , TestList
                "traits with types"
                [ testCase "a struct with types implements it" (runs (trait2 ++ two ++ "t = Two<Int> { a: 4, b: 5, n: 2 }; return get(t, 1) + size(t) * 10 + t.size() * 100;") (VInt 225))
                , testCase "and push is its impl's" (runs (trait2 ++ two ++ "t = push(Two<Int> { a: 4, b: 5, n: 2 }, 9); return t.b + t.n;") (VInt 12))
                , testCase "through the trait" (runs (trait2 ++ two ++ "t = Two<Int> { a: 4, b: 5, n: 2 }; return Seq::size(t) + Seq::get(t, 0);") (VInt 6))
                , testCase "a contract that calls a function of the type" (valid (trait2 ++ two ++ "fn lastOf<T>(t: &Two<T>) -> T [{ affirm size(t) > 0; }] [{ }] { return get(t, size(t) - 1); }; return 0;"))
                , testCase "an index past the size is refused" (rejected (trait2 ++ two ++ "t = Two<Int> { a: 4, b: 5, n: 2 }; return get(t, 2);") "Could not prove: i < <Two as Seq>::size(self)")
                , testCase "an impl that promises less than the trait is refused" (rejected (trait2 ++ "struct Two<T> { a: T, n: Int }; impl<T> Seq<T> for Two<T> { fn size(self: &Self) -> Int [{ }] [{ affirm return = self.n; }] { return self.n; }; fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < size(self); }] [{ }] { return self.a; }; fn push(self: Self, x: T) -> Self [{ }] [{ affirm size(return) = size(self) + 1; }] { return Self { a: x, n: self.n + 1 }; }; }; return 0;") "size does not meet what Seq declares")
                , testCase "the types are given" (parseFails (trait2 ++ "struct Two<T> { a: T, n: Int }; impl<T> Seq for Two<T> { }; return 0;"))
                , testCase "as many as the trait has" (parseFails "trait Seq<E> { fn size(self: &Self) -> Int; }; struct Two<T> { a: T, n: Int }; impl<T> Seq<T, T> for Two<T> { }; return 0;")
                , testCase "a trait without any is not given some" (parseFails "trait Plain { fn size(self: &Self) -> Int; }; struct Two<T> { a: T, n: Int }; impl<T> Plain<T> for Two<T> { }; return 0;")
                , testCase "a function of the impl with another type is refused" (rejected (trait2 ++ "struct Two<T> { a: T, n: Int }; impl<T> Seq<T> for Two<T> { fn size(self: &Self) -> Int { return 0; }; fn get(self: &Self, i: Int) -> Int { return 0; }; fn push(self: Self, x: T) -> Self { return self; }; }; return 0;") "get is fn")
                , testCase "a size of a struct without the function" (rejected "struct Plain { n: Int }; p = Plain { n: 1 }; return size(p);" "Plain::size is not defined before this call")
                , testCase "a trait has types, not sizes" (parseFails "trait Seq<n> { fn size(self: &Self) -> Int; }; return 0;")
                ]
            , TestList
                "a list written in Tersus"
                [ testCase "the library validates by itself" (valid vecLibrary)
                , testCase "pushed and read" (runs (vecLibrary ++ "v = Vec::new(0).push(5).push(6); return v.get(0) * 10 + v.get(1);") (VInt 56))
                , testCase "pushed past its capacity, in a loop" (runs (vecLibrary ++ "v = Vec::new(0); i = 0; while i < 10 [{ affirm i >= 0; affirm i <= 10; affirm size(v) = i; }] shrinks 10 - i { v = v.push(i * i); i = i + 1; }; return size(v) + v.get(9);") (VInt 91))
                , testCase "set" (runs (vecLibrary ++ "v = Vec::new(1).push(2).push(3).set(0, 9); return v.get(0) + v.get(1) * 10;") (VInt 39))
                , testCase "popped" (runs (vecLibrary ++ "v = Vec::new(false).push(true).push(false).pop(); return size(v);") (VInt 1))
                , testCase "a copy is a Vec of its own" (runs (vecLibrary ++ "a = Vec::new(0).push(1); b = a.set(0, 7); return a.get(0) * 10 + b.get(0);") (VInt 17))
                , testCase "of lists" (runs (vecLibrary ++ "rows = Vec::new(push([], 0)).push(push(push([], 4), 5)); return size(rows.get(0));") (VInt 2))
                , testCase "of Vecs" (runs (vecLibrary ++ "g = Vec::new(Vec::new(0)).push(Vec::new(0).push(8).push(9)); return size(g.get(0));") (VInt 2))
                , testCase "of structs that own a list" (runs (vecLibrary ++ "struct P { n: Int, xs: List<Int> }; ps = Vec::new(P { n: 0, xs: [] }).push(P { n: 3, xs: push([], 1) }); p = ps.get(0); return p.n + size(p.xs);") (VInt 4))
                , testCase "an index past the end is refused" (rejected (vecLibrary ++ "v = Vec::new(0).push(1); return v.get(1);") "Could not prove: i < self.len")
                , testCase "so is a pop of an empty one" (rejected (vecLibrary ++ "v = Vec::new(0).pop(); return size(v);") "Could not prove: self.len >= 1")
                , testCase "a function over any sequence of a Vec" (runs (vecLibrary ++ "fn firstOf<T>(v: &Vec<T>) -> T [{ affirm size(v) > 0; }] [{ }] { return v.get(0); }; return firstOf(Vec::new(3).push(8));") (VInt 8))
                ]
            , TestList
                "methods of lists"
                [ testCase "a list has its functions as methods" (runs "l = [1, 2, 3]; return l.size() + l.get(1) + l.first() + l.last();" (VInt 9))
                , testCase "push and set" (runs "l = [1]; l = l.push(5).push(6).set(0, 9); return l.get(0) * 100 + l.get(2) * 10 + l.size();" (VInt 963))
                , testCase "pop" (runs "l = [1, 2, 3]; l = l.pop(); return l.size() * 10 + l.last();" (VInt 22))
                , testCase "pop as a function" (runs "l = [1, 2, 3]; l = pop(pop(l)); return l.size() * 10 + l.last();" (VInt 11))
                , testCase "pop keeps the others" (valid "l = [1, 2, 3]; m = pop(l); affirm size(m) = 2; affirm get(m, 1) = 2; return size(m);")
                , testCase "a list that is empty is not popped" (rejected "l = push([], 1); l = pop(pop(l)); return 0;" "Relation does not hold")
                , testCase "pop is not a function of an array" (rejected "a = #[1, 2]; return size(pop(a));" "argument 1 of pop: expected List")
                , testCase "an array has them too" (runs "a = #[1, 2]; a = a.set(0, 9); return a.get(0) * 10 + a.size();" (VInt 92))
                , testCase "and a Box of an array" (runs "b = Array::boxed(3, 7); return b.size() + b.get(0);" (VInt 10))
                , testCase "a method that is not one" (rejected "l = [1]; return l.nothing();" "nothing is called on a List<Int>, which has no functions")
                , testCase "pop is a name of the language" (rejected "fn pop(l: List<Int>) -> List<Int> { return l; }; return 0;" "Function already defined: pop")
                ]
            , TestList
                "the prelude"
                [ TestCase "the tests build programs on the library of the example" $ do
                    exampleText <- readFile "examples/vec.tersus"
                    let code = [l | l <- lines exampleText, not (null (words l)), take 2 (dropWhile (== ' ') l) /= "//"]
                        library = lines vecLibrary
                    pure $ if any (\rest -> take (length library) rest == library) (tails code) then Nothing else Just "examples/vec.tersus does not hold vecLibrary"
                , testCase "a program that mentions Sequence has the trait" (runsAs (counter ++ "return Three { a: 4, n: 2 }.size() + get(Three { a: 4, n: 2 }, 0);") "6")
                , testCase "the trait is the one in lib/prelude.tersus" (errorHas (counter ++ "return get(Three { a: 4, n: 2 }, 3);") "Could not prove: i < <Three as Sequence>::size(self)")
                , testCase "a program with a Sequence of its own does not" (runsAs "trait Sequence { fn size(self: Self) -> Int; }; struct Box1 { n: Int }; impl Sequence for Box1 { fn size(self: Self) -> Int { return self.n; }; }; return Box1 { n: 3 }.size();" "3")
                , testCase "the names that native code makes a list of are not a program's" (errorHas "fn stdListNew() -> Int { return 7; }; return [1];" "stdListNew is reserved")
                , testCase "nor is the struct" (errorHas "struct StdList { x: Int }; return 1;" "StdList is reserved")
                , testCase "a program that mentions neither is as it was" (runsAs "return 4;" "4")
                , testCase "the lines of an error are those of the program" (errorHas "\n\nreturn ( ;" "line 3")
                , testCase "an error in the use of the library is the program's" (errorHas (counter ++ "x = Three { a: 1, n: 1 };\nreturn get(x, 5);") "Could not prove: i < <Three as Sequence>::size(self)")
                ]
            ]
  where
    -- A struct that implements the trait of the prelude: a number n of the same element a
    counter =
        "struct Three { a: Int, n: Int } invariant [{ affirm n >= 0; }]; impl Sequence<Int> for Three { fn size(self: &Self) -> Int [{ }] [{ affirm return = self.n; }] { return self.n; }; fn get(self: &Self, i: Int) -> Int [{ affirm i >= 0; affirm i < size(self); }] [{ affirm return = self.a; }] { return self.a; }; fn set(self: Self, i: Int, x: Int) -> Self [{ affirm i >= 0; affirm i < size(self); }] [{ affirm size(return) = size(self); affirm get(return, i) = x; }] { return Self { a: x, n: self.n }; }; fn push(self: Self, x: Int) -> Self [{ }] [{ affirm size(return) = size(self) + 1; affirm get(return, size(self)) = x; }] { return Self { a: x, n: self.n + 1 }; }; }; "
    runsAs source expected = case runSource Run source of
        Ok output -> if output == expected then Nothing else Just ("Expected " ++ expected ++ ", got " ++ output)
        Error e -> Just ("Failed: " ++ e)
    errorHas source expected = case compileSource source of
        Error e -> if expected `isInfixOf` e then Nothing else Just ("Expected an error with " ++ expected ++ ", got: " ++ e)
        Ok _ -> Just "Expected an error"
