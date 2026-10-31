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
        pairBox = "struct Box2<T> { a: T, b: T }; impl<T> Box2<T> { fn first(self: &Self) -> T { return clone(self.a); }; fn swap(self: Self) -> Self { return Self { a: self.b, b: self.a }; }; }; "
        lead = "fn lead<T>(a: &List<T>) -> T [{ define s = size(a); rewrite eqToGtZero s; affirm s > 0; }] [{ }] { return clone(get(a, 0)); }; "
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
                , testCase "a loop that builds a list of any type" (runs "fn mk<T>(x: T, n: Int) -> List<T> [{ define s = n; affirm s >= 0; }] [{ }] { out = []; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { out = push(out, clone(x)); i = i + 1; }; return out; }; return mk(push([], 4), 2);" (VList [VList [VInt 4], VList [VInt 4]]))
                , testCase "a type and a size together" (runs "fn fill<T, n>(a: &Array<T, n>, x: T) -> Array<T, n> [{ define k = n; rewrite eqToGtZero k; affirm k > 0; }] [{ }] { return set(clone(a), 0, x); }; return fill(#[true, true], false);" (VList [VBool False, VBool True]))
                , testCase "a function calls another with its type" (runs "fn count<T>(a: &List<T>) -> Int { return size(a); }; fn twice<T>(a: &List<T>) -> Int { return count(a) + count(a); }; return twice(push([], 1)) + twice(push([], true));" (VInt 4))
                , testCase "a type that is an empty list" (runs "fn same<T>(a: T, b: T) -> Bool { return a = b; }; return same([], []);" (VBool True))
                , testCase "a function calls itself with its type" (runs "fn f<T>(a: T, n: Int) -> Int [{ define k = n; affirm k >= 0; }] [{ }] shrinks n { if n = 0 { return 0; }; return 1 + f(a, n - 1); }; return f(push([], 2), 3);" (VInt 3))
                , testCase "or with its types in another order" (runs "fn f<A, B>(a: A, b: B, n: Int) -> Int [{ define k = n; affirm k >= 0; }] [{ }] shrinks n { if n = 0 { return 0; }; return 1 + f(b, a, n - 1); }; return f(1, true, 3);" (VInt 3))
                , testCase "or with a type of its own" (runs "fn f<T>(a: T, n: Int) -> Int [{ define k = n; affirm k >= 0; }] [{ }] shrinks n { if n = 0 { return 0; }; return 1 + f(1, n - 1); }; return f(true, 2);" (VInt 2))
                , testCase "a type that nothing decides is an Int" (runs "fn nil<T>() -> List<T> { return []; }; return size(nil());" (VInt 0))
                , testCase "a lent parameter of a type" (runs "fn twice<T>(a: &T) -> Array<T, 2> { return array(2, clone(a)); }; return twice(push([], 5));" (VList [VList [VInt 5], VList [VInt 5]]))
                ]
            , TestList
                "validation"
                [ testCase "a contract about the values is checked" (rejected (lead ++ "return lead([]);") "Proof term is not greater than 0")
                , testCase "and met" (valid (lead ++ "return lead([5]);"))
                , testCase "an index past the end" (rejected "fn past<T>(a: &List<T>) -> T { return clone(get(a, 0)); }; return past([1]);" "Relation lacks a proof")
                ]
            , TestList
                "types"
                [ testCase "a type is not an Int" (rejected "fn bad<T>(a: T) -> Int { return a + 1; }; return 0;" "expected Int, got T")
                , testCase "the arguments agree on it" (rejected "fn same<T>(a: T, b: T) -> Bool { return a = b; }; return same(1, true);" "argument 2 of same: expected Int, got Bool")
                , testCase "a type has to be declared" (rejected "fn bad(a: T) -> Int { return 0; }; return 0;" "unknown type T")
                , testCase "a function does not call itself with a type made of its own" (rejected "fn f<T>(a: T, n: Int) -> Int [{ define k = n; affirm k >= 0; }] [{ }] shrinks n { if n = 0 { return 0; }; return f(push([], a), n - 1); }; return f(1, 1);" "f calls itself with the type List<T> for T, which is made of its own type parameters")
                , testCase "a type is not a function" (rejected "fn id<T>(a: T) -> T { return a; }; fn inc(n: Int) -> Int { return n + 1; }; f = id(inc); return 0;" "a type parameter is not a function")
                , testCase "the function is called, not named" (rejected "fn id<T>(a: T) -> T { return a; }; h = id; return 0;" "id has parameters <T>, so it is called")
                , testCase "a function of an impl has them" (runs "struct S { x: Int }; impl S { fn f<T>(a: T) -> T { return a; }; }; return S::f(4);" (VInt 4))
                , testCase "a name that is not a capital is a size" (rejected "fn f<t>(a: t) -> Int { return 0; }; return 0;" "unknown type t")
                , testCase "a type is not in a nested function" (rejected "fn outer<T>(a: T) -> Int { fn inner(b: T) -> Int { return 0; }; return 0; }; return 0;" "unknown type T")
                , testCase "the declaration is parsed with spaces" (runs "fn second < A , B > (a: A, b: B) -> B { return b; }; return second(3, true);" (VBool True))
                ]
            , TestList
                "structs with types"
                [ testCase "a struct for a type" (runs "struct Pair<T> { a: T, b: T };  p = Pair<Int> { a: 1, b: 2 }; return p.a + p.b;" (VInt 3))
                , testCase "a value is printed as the struct" (runs "struct Pair<T> { a: T, b: T };  return Pair<Bool> { a: true, b: false };" (VData "Pair" [("a", VBool True), ("b", VBool False)]))
                , testCase "structs of two types in one program" (runs "struct Pair<T> { a: T, b: T };  x = Pair<Int> { a: 1, b: 2 }; y = Pair<List<Int>> { a: push([], 5), b: [] }; return size(y.a) + x.b;" (VInt 3))
                , testCase "the first field is an empty list and the second decides its type" (runs "struct Pair<T> { a: T, b: T };  y = Pair<List<Int>> { a: [], b: push([], 5) }; return size(y.a) + get(y.b, 0);" (VInt 5))
                , testCase "a returned instance has an empty list field" (runs "struct Pair<T> { a: T, b: T };  fn none() -> Pair<List<Int>> { return Pair<List<Int>> { a: [], b: [] }; }; return size(none().a);" (VInt 0))
                , testCase "an instance is made by pushing to an empty list in a generic function" (runs "struct Pair<T> { a: T, b: T };  fn wrap<T>(x: T) -> Pair<List<T>> { return Pair<List<T>> { a: push([], x), b: [] }; }; return get(wrap(3).a, 0);" (VInt 3))
                , testCase "a type is a type of its own" (rejected "struct Pair<T> { a: T, b: T };  fn f(p: Pair<Int>) -> Int { return p.a; }; return f(Pair<Bool> { a: true, b: false });" "argument 1 of f: expected Pair<Int>, got Pair<Bool>")
                , testCase "the fields have the type" (rejected "struct Pair<T> { a: T, b: T };  x = Pair<Int> { a: 1, b: true }; return 0;" "field b of Pair<Int>: expected Int, got Bool")
                , testCase "structs of one type are compared" (runs "struct Pair<T> { a: T, b: T };  return Pair<Int> { a: 1, b: 2 } = Pair<Int> { a: 1, b: 2 };" (VBool True))
                , testCase "a function over any type of one" (runs "struct Pair<T> { a: T, b: T };  fn swap<U>(p: &Pair<U>) -> Pair<U> { return Pair<U> { a: clone(p.b), b: clone(p.a) }; }; q = swap(Pair<List<Int>> { a: push([], 1), b: push(push([], 2), 3) }); return q;" (VData "Pair" [("a", VList [VInt 2, VInt 3]), ("b", VList [VInt 1])]))
                , testCase "its type is the type of the struct" (runs "struct Pair<T> { a: T, b: T };  fn first<U>(p: Pair<U>) -> U { return p.a; }; return first(Pair<Bool> { a: true, b: false });" (VBool True))
                , testCase "an update keeps the type" (runs "struct Pair<T> { a: T, b: T };  a = Pair<Int> { a: 1, b: 2 }; b = Pair<Int> { b: 9, ..a }; return b.a + b.b;" (VInt 10))
                , testCase "a struct that holds another of its type" (runs "struct Pair<T> { a: T, b: T };  struct Wrap<T> { inner: Pair<T>, tag: Int }; fn mk<T>(x: T, y: T) -> Wrap<T> { return Wrap<T> { inner: Pair<T> { a: x, b: y }, tag: 7 }; }; return mk(true, false).tag;" (VInt 7))
                , testCase "in a list, an array and a Box" (runs "trait Clone { }; struct Pair<T> { a: T, b: T }; impl<T> Clone for Pair<T> { }; l = push([], Pair<Int> { a: 1, b: 2 }); a = array(2, Pair<Bool> { a: true, b: true }); b = Box::new(Pair<Int> { a: 5, b: 6 }); return get(l, 0).b + b.a + size(a);" (VInt 9))
                , testCase "a type and a size" (runs "struct Vec<T, n> { cells: Array<T, n>, used: Int }; fn capacity<T, m>(v: &Vec<T, m>) -> Int { return m + v.used; }; return capacity(Vec<Int, 3> { cells: #[1, 2, 3], used: 1 }) * 10 + capacity(Vec<Bool, 2> { cells: #[true, false], used: 0 });" (VInt 42))
                , testCase "an array of the type and the size is known" (valid "struct Vec<T, n> { cells: Array<T, n>, used: Int }; v = Vec<Int, 3> { cells: #[1, 2, 3], used: 0 }; affirm size(v.cells) = 3; return get(v.cells, 2);")
                , testCase "a Box of an array of the type" (runs "struct Holder<T> { items: Box<Array<T>>, len: Int }; h = Holder<List<Int>> { items: Array::boxed(2, push([], 1)), len: 2 }; return clone(get(h.items, 1));" (VList [VInt 1]))
                , testCase "a contract about it" (valid "struct Holder<T> { items: Box<Array<T>>, len: Int }; fn holder<T>(x: T, n: Int) -> Holder<T> [{ define s = n; rewrite eqToGtZero s; affirm s > 0; }] [{ affirm size(return.items) = n; }] { return Holder<T> { items: Array::boxed(n, x), len: n }; }; fn at<T>(h: &Holder<T>, i: Int) -> T [{ define s = size(h.items); affirm i >= 0; affirm i < s; }] [{ }] { return clone(get(h.items, i)); }; h = holder(push([], 5), 3); return at(h, 2);")
                , testCase "a struct that holds itself in a Box" (valid "struct L<T> { v: T, next: Box<L<T>> }; return 0;")
                , testCase "or in a list" (runs "struct Chain<T> { value: T, rest: List<Chain<T>> }; c = Chain<Int> { value: 1, rest: push([], Chain<Int> { value: 2, rest: [] }) }; return get(c.rest, 0).value;" (VInt 2))
                , testCase "but not by value" (rejected "struct L<T> { v: T, next: L<T> }; return 0;" "L holds itself, so it would have no size")
                , testCase "its parameters are given" (rejected "struct Pair<T> { a: T, b: T };  fn f(p: Pair) -> Int { return 0; }; return 0;" "Pair has parameters <T>, which a type gives")
                , testCase "as many as it has" (parseFails "struct Pair<T> { a: T, b: T };  x = Pair<Int, Int> { a: 1, b: 2 }; return 0;")
                , testCase "a size where a type is wanted" (parseFails "struct Pair<T> { a: T, b: T };  x = Pair<3> { a: 1, b: 2 }; return 0;")
                , testCase "a type is not a function" (rejected "struct Pair<T> { a: T, b: T };  fn inc(n: Int) -> Int { return n + 1; }; x = Pair<fn(Int) -> Int> { a: inc, b: inc }; return 0;" "a type parameter is not a function")
                , testCase "a type has to be declared" (rejected "struct Q<T> { a: U }; return 0;" "unknown type U")
                , testCase "a function does not call itself with a struct of its type" (rejected "struct Wrap<T> { value: T }; fn f<T>(a: T, n: Int) -> Int [{ define k = n; affirm k >= 0; }] [{ }] shrinks n { if n = 0 { return 0; }; return f(Wrap<T> { value: a }, n - 1); }; return f(1, 1);" "f calls itself with the type Wrap<'T> for T")
                , testCase "a struct does not use itself with a type that grows" (rejected "struct Node<T> { next: List<Node<List<T>>> }; x = Node<Int> { next: [] }; return 0;" "Node uses itself with a type made of its own parameters")
                , testCase "but with its own types, in any order" (valid "struct Pair<A, B> { first: A, rest: List<Pair<B, A>> }; return 0;")
                , testCase "a struct with a name that starts with a small letter is a type" (runs "struct point { x: Int }; struct Holder<T> { value: T }; h = Holder<point> { value: point { x: 1 } }; return h.value.x;" (VInt 1))
                , testCase "also in a list" (runs "struct point { x: Int }; struct Holder<T> { value: T }; h = Holder<List<point>> { value: push([], point { x: 4 }) }; return get(h.value, 0).x;" (VInt 4))
                , testCase "a parameter is not named twice" (rejected "struct Q<T, T> { a: T }; return 0;" "names a parameter twice")
                , testCase "the declaration is parsed with spaces" (runs "struct Q < T , n > { a: T, b: Array<T, n> }; q = Q < Int , 2 > { a: 1, b: #[2, 3] }; return q.a + get(q.b, 1);" (VInt 4))
                ]
            , TestList
                "impl for a struct with parameters"
                [ testCase "a method" (runs (pairBox ++ "x = Box2<Int> { a: 1, b: 2 }.swap(); return x.first() * 10 + x.b;") (VInt 21))
                , testCase "for any type" (runs (pairBox ++ "x = Box2<List<Int>> { a: push([], 1), b: push(push([], 2), 3) }; return size(x.swap().first());") (VInt 2))
                , testCase "its own names for the parameters" (runs "struct Box2<T> { a: T, b: T }; impl<U> Box2<U> { fn second(self: &Self) -> U { return clone(self.b); }; }; return Box2<Int> { a: 1, b: 2 }.second();" (VInt 2))
                , testCase "a function without self is called through the type" (runs "struct Box2<T> { a: T, b: T }; impl<T> Box2<T> { fn both(x: T) -> Self { return Self { a: clone(x), b: x }; }; }; return Box2::both(4).b;" (VInt 4))
                , testCase "a size of the impl is a value" (runs "struct Packet<n> { cells: Array<Int, n>, tag: Int }; impl<n> Packet<n> { fn count(self: &Self) -> Int { return n + self.tag; }; }; return Packet<3> { cells: #[1, 2, 3], tag: 10 }.count();" (VInt 13))
                , testCase "a method calls another" (runs "struct Box2<T> { a: T, b: T }; impl<T> Box2<T> { fn swap(self: Self) -> Self { return Self { a: self.b, b: self.a }; }; fn back(self: Self) -> Self { return self.swap().swap(); }; }; return Box2<Int> { a: 1, b: 2 }.back().a;" (VInt 1))
                , testCase "validated against its contract" (rejected "struct Box2<T> { a: T, b: T }; impl<T> Box2<T> { fn pick(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < 2; }] [{ }] { return clone(self.a); }; }; return Box2<Int> { a: 1, b: 2 }.pick(5);" "Could not prove: i < 2")
                , testCase "the parameters are written" (parseFails "struct Box2<T> { a: T, b: T }; impl Box2 { fn first(self: &Self) -> Int { return 0; }; }; return 0;")
                , testCase "or none for a struct without any" (parseFails "struct S { a: Int }; impl<T> S { fn f(self: &Self) -> Int { return 0; }; }; return 0;")
                , testCase "a trait is implemented for these" (runs "struct Box2<T> { a: T, b: T }; trait Counted { fn count(self: &Self) -> Int; }; impl<T> Counted for Box2<T> { fn count(self: &Self) -> Int { return 2; }; }; return Box2<Int> { a: 1, b: 2 }.count();" (VInt 2))
                , testCase "the impl comes before its calls" (rejected "struct Box2<T> { a: T, b: T }; x = Box2<Int> { a: 1, b: 2 }; return x.first();" "is not defined before this call")
                ]
            ]
