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
        total = "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { sum = 0; i = 0; while i < size(s) [{ affirm i >= 0; affirm i <= size(s); }] shrinks size(s) - i { sum = sum + get(s, i); i = i + 1; }; return sum; }; "
        double = "fn double(x: Int) -> Int [{ }] [{ affirm return = x * 2; }] { return x * 2; }; "
        counted = "struct V<T> { x: T, len: Int }; "
        trait2 = "trait Seq<E> { fn size(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; fn get(self: &Self, i: Int) -> E [{ affirm i >= 0; affirm i < size(self); }] [{ }]; fn push(self: Self, x: E) -> Self [{ }] [{ affirm size(return) = size(self) + 1; }]; }; "
        two = "struct Two<T> { a: T, b: T, n: Int } invariant [{ affirm n >= 0; }]; impl<T> Seq<T> for Two<T> { fn size(self: &Self) -> Int [{ }] [{ affirm return = self.n; }] { return self.n; }; fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < size(self); }] [{ }] { if i = 0 { return clone(self.a); }; return clone(self.b); }; fn push(self: Self, x: T) -> Self [{ }] [{ affirm size(return) = size(self) + 1; }] { return Self { a: self.a, b: x, n: self.n + 1 }; }; }; "
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
                , testCase "an impl that promises less than the trait is refused" (rejected (trait2 ++ "struct Two<T> { a: T, n: Int }; impl<T> Seq<T> for Two<T> { fn size(self: &Self) -> Int [{ }] [{ affirm return = self.n; }] { return self.n; }; fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < size(self); }] [{ }] { return clone(self.a); }; fn push(self: Self, x: T) -> Self [{ }] [{ affirm size(return) = size(self) + 1; }] { return Self { a: x, n: self.n + 1 }; }; }; return 0;") "size does not meet what Seq declares")
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
                , testCase "a copy is a Vec of its own" (runs (vecLibrary ++ "a = Vec::new(0).push(1); b = a.clone().set(0, 7); return a.get(0) * 10 + b.get(0);") (VInt 17))
                , testCase "of lists" (runs (vecLibrary ++ "rows = Vec::new(push([], 0)).push(push(push([], 4), 5)); return size(rows.get(0));") (VInt 2))
                , testCase "of Vecs" (runs (vecLibrary ++ "g = Vec::new(Vec::new(0)).push(Vec::new(0).push(8).push(9)); return size(g.get(0));") (VInt 2))
                , testCase "of structs that own a list" (runs (vecLibrary ++ "struct P { n: Int, xs: List<Int> }; ps = Vec::new(P { n: 0, xs: [] }).push(P { n: 3, xs: push([], 1) }); p = ps.get(0); return p.n + size(p.xs);") (VInt 4))
                , testCase "an index past the end is refused" (rejected (vecLibrary ++ "v = Vec::new(0).push(1); return v.get(1);") "Could not prove: i < self.len")
                , testCase "so is a pop of an empty one" (rejected (vecLibrary ++ "v = Vec::new(0).pop(); return size(v);") "Could not prove: self.len >= 1")
                , testCase "a function over any sequence of a Vec" (runs (vecLibrary ++ "fn firstOf<T>(v: &Vec<T>) -> T [{ affirm size(v) > 0; }] [{ }] { return v.get(0); }; return firstOf(Vec::new(3).push(8));") (VInt 8))
                ]
            , TestList
                "bounded types"
                [ testCase "one function for a list, an array and a Vec" (runsAs (vecLibrary ++ total ++ "return total(Vec::new(0).push(10).push(20).push(30)) * 10000 + total(push(push([], 3), 4)) * 100 + total(array(3, 5));") "600715")
                , testCase "its contracts are proved for each type" (compiles (total ++ "fn twice<S: Sequence<Int>>(s: &S) -> Int [{ affirm size(s) > 0; }] [{ affirm return = get(s, 0) * 2; }] { return get(s, 0) * 2; }; return twice([4]) + twice(array(2, 1));"))
                , testCase "and the body is checked for the type" (errorHas "fn bad<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return get(s, 0); }; return bad(push([], 1));" "Could not prove")
                , testCase "a type of the bound is given by the argument" (runsAs "fn head<S: Sequence<E>, E>(s: &S) -> E [{ affirm size(s) > 0; }] [{ }] { return get(s, 0); }; return head(push([], 7)) + head(array(2, 5));" "12")
                , testCase "a bool one" (runsAs "fn head<S: Sequence<E>, E>(s: &S) -> E [{ affirm size(s) > 0; }] [{ }] { return get(s, 0); }; if head(push([], true)) { return 1; }; return 0;" "1")
                , testCase "a function with bounds calls another" (runsAs "fn head<S: Sequence<E>, E>(s: &S) -> E [{ affirm size(s) > 0; }] [{ }] { return get(s, 0); }; fn twice<S: Sequence<Int>>(s: &S) -> Int [{ affirm size(s) > 0; }] [{ affirm return = head(s) * 2; }] { return head(s) * 2; }; return twice(push([], 4));" "8")
                , testCase "in a contract" (compiles "fn head<S: Sequence<E>, E>(s: &S) -> E [{ affirm size(s) > 0; }] [{ affirm return = get(s, 0); }] { return get(s, 0); }; fn f(l: &List<Int>) -> Int [{ affirm size(l) > 0; }] [{ affirm return = head(l); }] { return get(l, 0); }; return f(push([], 1));")
                , testCase "Growable is for what grows" (runsAs "fn add<S: Growable<Int>>(s: S, x: Int) -> S [{ }] [{ affirm size(return) = size(s) + 1; affirm get(return, size(s)) = x; }] { return push(s, x); }; l = add(add([], 7), 8); return size(l) * 10 + get(l, 1);" "28")
                , testCase "an array does not grow" (errorHas "fn add<S: Growable<Int>>(s: S, x: Int) -> S [{ }] [{ }] { return push(s, x); }; return size(add(array(2, 1), 3));" "needs S to implement Growable, and Array<Int, 2> does not")
                , testCase "a Box of an array is a sequence" (runsAs "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return size(s); }; return total(Array::boxed(3, 1));" "3")
                , testCase "the types of the bound have to be the ones" (errorHas "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return size(s); }; return total(push([], true));" "total needs S to implement Sequence<Int>, and List<Bool> implements Sequence<Bool>")
                , testCase "a type that does not implement the trait" (errorHas "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return size(s); }; return total(3);" "needs S to implement Sequence, and Int does not")
                , testCase "a struct that implements it" (runsAs (counter ++ "fn total<S: Sequence<Int>>(s: &S) -> Int [{ affirm size(s) > 0; }] [{ }] { return size(s) * 10 + get(s, 0); }; return total(Three { a: 4, n: 2 });") "24")
                , testCase "one that implements it for a type of its own" (runsAs (counter ++ "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return size(s); }; return total(Three { a: 4, n: 2 }) + total([1]);") "3")
                , testCase "a bound of several traits" (runsAs "fn both<S: Sequence<Int> + Growable<Int>>(s: S) -> Int [{ }] [{ }] { return size(push(s, 1)); }; return both(push([], 5));" "2")
                , testCase "a trait that is not there" (errorHas "fn f<S: Missing>(s: &S) -> Int [{ }] [{ }] { return 0; }; return 0;" "unknown trait Missing")
                , testCase "the types of the trait are as many as it has" (errorHas "fn f<S: Sequence>(s: &S) -> Int [{ }] [{ }] { return 0; }; return 0;" "has parameters <E>")
                , testCase "a size has no bound" (parseFails "fn f<n: Sequence<Int>>(s: &List<Int>) -> Int { return 0; }; return 0;")
                , testCase "a type that a call cannot work out" (errorHas "fn head<S: Sequence<E>, E>(s: &S) -> E [{ }] [{ }] { return get(s, 0); }; return head([]);" "cannot be worked out")
                , testCase "a caller with a type of its own" (errorHas "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return size(s); }; fn h<T>(l: &List<T>) -> Int [{ }] [{ }] { return total(l); }; return 0;" "needs S to implement Sequence<Int>, and List<T> implements Sequence<T>")
                , testCase "a bound on a type that a later bound decides" (runsAs "fn f<E: Sequence<Int>, S: Sequence<E>>(s: &S) -> Int [{ }] [{ }] { return size(s); }; return f(push([], push([], 1)));" "1")
                , testCase "which is still checked" (errorHas "fn f<E: Sequence<Int>, S: Sequence<E>>(s: &S) -> Int [{ }] [{ }] { return size(s); }; return f(push([], push([], true)));" "f needs E to implement Sequence<Int>, and List<Bool> implements Sequence<Bool>")
                , testCase "a call of itself with a bigger type is refused" (errorHas "fn f<S: Sequence<E>, E>(s: &S) -> Int ~ { return f(push([], s)); }; return f(push([], 1));" "f calls itself with the types List<List<Int>>, List<Int>")
                , testCase "and with its own types is not" (runsAs "fn count<S: Sequence<Int>>(s: &S, k: Int) -> Int [{ affirm k >= 0; }] [{ }] shrinks k { if k = 0 { return size(s); }; return count(s, k - 1); }; return count(push([], 4), 3);" "1")
                , testCase "a size of the impl in the types of the bound" (runsAs "struct Packet<n> { cells: Array<Int, n> }; trait Holds<E> { }; impl<n> Holds<Array<Int, n>> for Packet<n> { }; fn g<S: Holds<Array<Int, 3>>>(s: &S) -> Int [{ }] [{ }] { return 2; }; return g(Packet<3> { cells: array(3, 0) });" "2")
                , testCase "it has a name of its own" (errorHas "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return 0; }; fn total(x: Int) -> Int { return x; }; return 0;" "is already defined")
                , testCase "and is not a builtin's" (errorHas "fn size<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return 0; }; return 0;" "size is already defined")
                , testCase "it is a function of the program only at the top" (errorHas "fn f() -> Int [{ }] [{ }] { fn g<S: Sequence<Int>>(s: &S) -> Int { return 0; }; return 0; }; return f();" "only be defined at the top")
                , testCase "an impl has none" (errorHas "struct A { n: Int }; impl A { fn f<S: Sequence<Int>>(self: &Self, s: &S) -> Int { return 0; }; }; return 0;" "cannot be written in an impl")
                , testCase "it is not a value" (errorHas "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return 0; }; f = total; return 0;" "Undefined variable: total")
                , testCase "a call with the wrong number of arguments" (errorHas "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return 0; }; return total([1], [2]);" "total takes 1 arguments, got 2")
                ]
            , TestList
                "methods of lists"
                [ testCase "a list has its functions as methods" (runs "l = [1, 2, 3]; return l.size() + l.get(1) + l.first() + l.last();" (VInt 9))
                , testCase "push and set" (runs "l = [1]; l = l.push(5).push(6).set(0, 9); return l.get(0) * 100 + l.get(2) * 10 + l.size();" (VInt 963))
                , testCase "pop" (runs "l = [1, 2, 3]; l = l.pop(); return l.size() * 10 + l.last();" (VInt 22))
                , testCase "a long chain is checked once" (runs ("l = push([], 1)" ++ concat (replicate 30 ".push(1)") ++ "; return l.size();") (VInt 31))
                , testCase "pop as a function" (runs "l = [1, 2, 3]; l = pop(pop(l)); return l.size() * 10 + l.last();" (VInt 11))
                , testCase "pop keeps the others" (valid "l = [1, 2, 3]; m = pop(l); affirm size(m) = 2; affirm get(m, 1) = 2; return size(m);")
                , testCase "a list that is empty is not popped" (rejected "l = push([], 1); l = pop(pop(l)); return 0;" "Relation does not hold")
                , testCase "pop is not a function of an array" (rejected "a = #[1, 2]; return size(pop(a));" "argument 1 of pop: expected List")
                , testCase "an array has them too" (runs "a = #[1, 2]; a = a.set(0, 9); return a.get(0) * 10 + a.size();" (VInt 92))
                , testCase "and a Box of an array" (runs "b = Array::boxed(3, 7); return b.size() + b.get(0);" (VInt 10))
                , testCase "a method that is not one" (rejected "l = [1]; return l.nothing();" "List::nothing is not defined before this call")
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
                , testCase "a list is a Sequence by the impl in lib/prelude.tersus" (runsAs "fn total<S: Sequence<Int>>(s: &S) -> Int { return size(s); }; return total(push([], 3));" "1")
                , testCase "and a Growable by it" (runsAs "fn add<S: Growable<Int>>(s: S, x: Int) -> S { return push(s, x); }; return size(add(push([], 3), 4));" "2")
                , testCase "called through the trait by its path" (runsAs "return Sequence::size(push([], 3)) + Sequence::get(push([], 3), 0);" "4")
                , testCase "an impl for a list is written for it" (runs "trait MySeq<E> { fn size(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl<T> MySeq<T> for List<T> { fn size(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return size(self); }; }; fn n<S: MySeq<Int>>(s: &S) -> Int { return size(s); }; return n(push([], 3));" (VInt 1))
                , testCase "an impl written for one type of list is not for another" (rejected "trait OnlyInts { fn n(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl OnlyInts for List<Int> { fn n(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return size(self); }; }; fn f<S: OnlyInts>(s: &S) -> Int { return 0; }; return f(push([], true));" "needs S to implement OnlyInts, and List<Bool> does not")
                , testCase "and is for that one" (runs "trait OnlyInts { fn n(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl OnlyInts for List<Int> { fn n(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return size(self); }; }; fn f<S: OnlyInts>(s: &S) -> Int { return 0; }; return f(push([], 1));" (VInt 0))
                , testCase "a function of a trait is called on a Box of an array by its path" (runsAs "return Sequence::size(Array::boxed(3, 5)) + Sequence::get(Array::boxed(2, 7), 1);" "10")
                , testCase "and on an array by its path" (runsAs "return Sequence::size(#[1, 2, 3]) + Sequence::get(#[4, 5], 1);" "8")
                , testCase "and on an array whose trait is the program's" (runs "trait Holds<E> { fn hold(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl<T, n> Holds<Array<T, n>> for Array<T, n> { fn hold(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return size(self); }; }; return Holds::hold(#[1, 2, 3]);" (VInt 3))
                , testCase "and on a struct with a size" (runs "struct Packet<n> { cells: Array<Int, n> }; trait Holds<E> { fn hold(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl<n> Holds<Array<Int, n>> for Packet<n> { fn hold(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return size(self.cells); }; }; return Holds::hold(Packet<3> { cells: #[1, 2, 3] });" (VInt 3))
                , testCase "a trait written for one size of array is not for another" (rejected "trait OfThree { }; impl OfThree for Array<Int, 3> { }; fn f<S: OfThree>(s: &S) -> Int { return 0; }; return f(#[1, 2]);" "needs S to implement OfThree, and Array<Int, 2> does not")
                , testCase "a trait written for an array of one type is not for another" (rejected "trait OfInts { }; impl OfInts for Array<Int, 3> { }; fn f<S: OfInts>(s: &S) -> Int { return 0; }; return f(#[true, false, true]);" "needs S to implement OfInts, and Array<Bool, 3> does not")
                , testCase "a Box of an array is a Sequence by the impl in lib/prelude.tersus" (runsAs "fn total<S: Sequence<Int>>(s: &S) -> Int { return size(s); }; return total(Array::boxed(3, 5)) * 10 + total(#[1, 2]);" "32")
                , testCase "an impl for an array is written for it" (runs "trait Holds<E> { }; impl<T, n> Holds<Array<T, n>> for Array<T, n> { }; fn g<S: Holds<Array<Int, 3>>>(s: &S) -> Int [{ }] [{ }] { return 2; }; return g(#[1, 2, 3]);" (VInt 2))
                , testCase "the trait is the one in lib/prelude.tersus" (errorHas (counter ++ "return get(Three { a: 4, n: 2 }, 3);") "Could not prove")
                , testCase "a program with a Sequence of its own does not" (runsAs "trait Sequence { fn size(self: Self) -> Int; }; struct Box1 { n: Int }; impl Sequence for Box1 { fn size(self: Self) -> Int { return self.n; }; }; return Box1 { n: 3 }.size();" "3")
                , testCase "the names that native code makes a list of are not a program's" (errorHas "fn stdListNew() -> Int { return 7; }; return [1];" "stdListNew is reserved")
                , testCase "nor is the struct" (errorHas "struct StdList { x: Int }; return 1;" "StdList is reserved")
                , testCase "nor are those of the Box of native code" (errorHas "struct StdBox { x: Int }; return 1;" "StdBox is reserved")
                , testCase "nor its functions" (errorHas "fn stdBoxNew(x: Int) -> Int { return x; }; return 1;" "stdBoxNew is reserved")
                , testCase "a program that mentions Deref has the trait" (runsAs "struct P { x: Int, y: Int }; impl Clone for P { }; struct W { v: P }; impl Deref<P> for W { fn deref(self: &Self) -> P [{ }] [{ affirm return = self.v; }] { return clone(self.v); }; }; w = W { v: P { x: 4, y: 5 } }; return w.x + w.y;" "9")
                , testCase "a program that mentions neither is as it was" (runsAs "return 4;" "4")
                , testCase "the lines of an error are those of the program" (errorHas "\n\nreturn ( ;" "line 3")
                , testCase "an error in the use of the library is the program's" (errorHas (counter ++ "x = Three { a: 1, n: 1 };\nreturn get(x, 5);") "Could not prove")
                ]
            ]
  where
    -- A struct that implements the trait of the prelude: a number n of the same element a
    counter =
        "struct Three { a: Int, n: Int } invariant [{ affirm n >= 0; }]; impl Sequence<Int> for Three { fn size(self: &Self) -> Int [{ }] [{ affirm return = self.n; }] { return self.n; }; fn get(self: &Self, i: Int) -> Int [{ affirm i >= 0; affirm i < size(self); }] [{ affirm return = self.a; }] { return self.a; }; fn set(self: Self, i: Int, x: Int) -> Self [{ affirm i >= 0; affirm i < size(self); }] [{ affirm size(return) = size(self); affirm get(return, i) = x; }] { return Self { a: x, n: self.n }; }; }; impl Growable<Int> for Three { fn push(self: Self, x: Int) -> Self [{ }] [{ affirm size(return) = size(self) + 1; affirm get(return, size(self)) = x; }] { return Self { a: x, n: self.n + 1 }; }; }; "
    compiles source = case compileSource source of
        Ok _ -> Nothing
        Error e -> Just ("Failed: " ++ e)
    runsAs source expected = case runSource Interpret source of
        Ok output -> if output == expected then Nothing else Just ("Expected " ++ expected ++ ", got " ++ output)
        Error e -> Just ("Failed: " ++ e)
    errorHas source expected = case compileSource source of
        Error e -> if expected `isInfixOf` e then Nothing else Just ("Expected an error with " ++ expected ++ ", got: " ++ e)
        Ok _ -> Just "Expected an error"
