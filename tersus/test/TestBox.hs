module TestBox (testBox) where

import TersusTypes
import TestHarness

-- Box<T>: a struct or an enum held in a Box. A Box has the value of what it holds, so it is looked into wherever the struct or the
-- enum is (a field read, `is`, `as`, `match`, a method call), and a type that holds itself holds the recursion in one.
testBox :: Test
testBox =
    let runs body expected = parseEvalProgramHelper body (Just expected)
        valid = parseValidProgramHelper
        rejected = parseValidateFailProgramHelper
        parseFails source = case parseValidProgramHelper source of
            Just err | take 11 err == "Parse faile" -> Nothing
            _ -> Just ("Expected a parse error for: " ++ source)
        tree =
            unlines
                [ "enum Tree { Leaf, Node { l: Box<Tree>, v: Int, r: Box<Tree> } };"
                , "fn leaf() -> Box<Tree> { return Box::new(Tree::Leaf); };"
                , "fn node(l: Box<Tree>, v: Int, r: Box<Tree>) -> Box<Tree> { return Box::new(Tree::Node { l: l, v: v, r: r }); };"
                , "fn sum(t: Box<Tree>) -> Int shrinks t { return match t { Tree::Leaf => 0, Tree::Node { l: l, v: v, r: r } => v + sum(l) + sum(r) }; };"
                ]
        point = "struct P { x: Int, y: Int };"
     in TestList
            "testBox"
            [ TestList
                "holding a value"
                [ testCase "a struct in a Box" (runs (point ++ "b = Box::new(P { x: 4, y: 5 }); return b.x + b.y;") (VInt 9))
                , testCase "an enum in a Box" (runs "enum E { A { v: Int }, B }; b = Box::new(E::A { v: 3 }); return b is E::A;" (VBool True))
                , testCase "a Box is cast to a variant" (runs "enum E { A { v: Int }, B }; b = Box::new(E::A { v: 3 }); return (b as E::A).v;" (VInt 3))
                , testCase "a Box is matched" (runs "enum E { A { v: Int }, B }; fn f(b: Box<E>) -> Int { return match b { E::A { v: v } => v, E::B => 0 }; }; return f(Box::new(E::A { v: 6 }));" (VInt 6))
                , testCase "a Box has the value of what it holds" (runs (point ++ "impl Eq for P { }; return Box::new(P { x: 1, y: 2 }) = Box::new(P { x: 1, y: 2 });") (VBool True))
                , testCase "boxes of different values differ" (runs (point ++ "impl Eq for P { }; return Box::new(P { x: 1, y: 2 }) != Box::new(P { x: 1, y: 3 });") (VBool True))
                , testCase "a Box is a parameter and a result" (runs (point ++ "fn mk(n: Int) -> Box<P> { return Box::new(P { x: n, y: n * 2 }); }; fn sum(p: Box<P>) -> Int { return p.x + p.y; }; return sum(mk(4));") (VInt 12))
                , testCase "a Box in a struct" (runs (point ++ "struct Q { p: Box<P>, n: Int }; q = Q { p: Box::new(P { x: 3, y: 4 }), n: 5 }; return q.p.x * 100 + q.p.y * 10 + q.n;") (VInt 345))
                , testCase "a Box in a list" (runs (point ++ "ps = push(push([], Box::new(P { x: 1, y: 2 })), Box::new(P { x: 3, y: 4 })); return get(ps, 1).y + size(ps);") (VInt 6))
                , testCase "a Box is read in an update" (runs (point ++ "b = Box::new(P { x: 1, y: 2 }); c = P { x: 9, ..b }; return c.x + c.y;") (VInt 11))
                , testCase "a method is called on what a Box holds" (runs (point ++ "impl P { fn total(self: Self) -> Int { return self.x + self.y; }; }; b = Box::new(P { x: 2, y: 3 }); return Box::unbox(b).total();") (VInt 5))
                , testCase "not on the Box" (rejected (point ++ "impl P { fn total(self: Self) -> Int { return self.x + self.y; }; }; b = Box::new(P { x: 2, y: 3 }); return b.total();") "total is called on a Box<P>, which has no functions: call it on the value inside, as in Box::unbox(b).total(...)")
                , testCase "unbox gives back what was held" (runs (point ++ "b = Box::new(P { x: 2, y: 3 }); p = Box::unbox(b); return p.x * 10 + p.y;") (VInt 23))
                , testCase "unbox of a Box is the value" (runs (point ++ "impl Eq for P { }; return Box::unbox(Box::new(P { x: 2, y: 3 })) = P { x: 2, y: 3 };") (VBool True))
                , testCase "the contents of a Box can be passed where the struct is wanted by a builtin test" (runs "enum E { A, B }; b = Box::new(E::B); if b is E::B { return 1; }; return 0;" (VInt 1))
                ]
            , TestList
                "a type that holds itself"
                [ testCase "a tree" (runs (tree ++ "return sum(node(node(leaf(), 1, leaf()), 2, node(leaf(), 3, leaf())));") (VInt 6))
                , testCase "a loop walks down a tree" (runs (tree ++ "fn depth(t: Box<Tree>) -> Int { d = 0; while t is Tree::Node shrinks t { t = (t as Tree::Node).l; d = d + 1; }; return d; }; return depth(node(node(node(leaf(), 1, leaf()), 2, leaf()), 3, leaf()));") (VInt 3))
                , testCase "a chain of links" (runs "enum Chain { End, Link { v: Int, rest: Box<Chain> } }; fn len(c: Box<Chain>) -> Int shrinks c { return match c { Chain::End => 0, Chain::Link { v: v, rest: r } => 1 + len(r) }; }; return len(Box::new(Chain::Link { v: 1, rest: Box::new(Chain::Link { v: 2, rest: Box::new(Chain::End) }) }));" (VInt 2))
                , testCase "a struct that holds itself in a Box" (valid "struct L { v: Int, next: Box<L> }; return 0;")
                , testCase "a struct that holds itself in a list" (runs "struct Node { v: Int, kids: List<Node> }; return size(Node { v: 1, kids: [] }.kids);" (VInt 0))
                , testCase "a struct that holds itself" (rejected "struct L { v: Int, next: L }; return 0;" "L holds itself, so it would have no size: hold the recursion in a Box, as in Box<L>")
                , testCase "an enum that holds itself" (rejected "enum T { Leaf, Node { l: T, r: T } }; return 0;" "T holds itself, so it would have no size")
                ]
            , TestList
                "validation"
                [ testCase "a function over a boxed tree ends because the tree shrinks" (valid (tree ++ "return sum(node(leaf(), 1, leaf()));"))
                , testCase "a call that does not shrink" (rejected "enum T { Leaf, Node { l: Box<T>, r: Box<T> } }; fn f(t: Box<T>) -> Int shrinks t { return match t { T::Leaf => 0, T::Node { l: l, r: r } => f(t) }; }; return f(Box::new(T::Leaf));" "Recursive call does not shrink the variant")
                , testCase "a contract about the variant of a Box" (valid "enum E { A { v: Int }, B }; fn v(b: Box<E>) -> Int [{ affirm b is E::A; }] [{ affirm return = (b as E::A).v; }] { return (b as E::A).v; }; return v(Box::new(E::A { v: 4 }));")
                , testCase "the contract is not met" (rejected "enum E { A { v: Int }, B }; fn v(b: Box<E>) -> Int [{ affirm b is E::A; }] [{ }] { return (b as E::A).v; }; return v(Box::new(E::B));" "Could not prove: b is E::A")
                , testCase "a field of a Box is known" (valid "struct P { x: Int }; b = Box::new(P { x: 4 }); affirm b.x = 4; return b.x;")
                ]
            , TestList
                "types"
                [ testCase "a Box is not what it holds" (rejected (point ++ "fn f(p: Box<P>) -> Int { return 0; }; return f(P { x: 1, y: 2 });") "argument 1 of f: expected Box<P>, got P")
                , testCase "what a Box holds is not a Box" (rejected (point ++ "fn f(p: P) -> Int { return 0; }; return f(Box::new(P { x: 1, y: 2 }));") "argument 1 of f: expected P, got Box<P>")
                , testCase "a Box holds an Int" (runs "return Box::unbox(Box::new(3)) + 1;" (VInt 4))
                , testCase "a Box holds a Bool" (runs "return Box::unbox(Box::new(true));" (VBool True))
                , testCase "a Box holds a list" (runs "b = Box::new(push([], 4)); return size(Box::unbox(b));" (VInt 1))
                , testCase "a Box holds an array" (runs "b = Box::new(#[1, 2, 3]); return get(b, 1) + size(b);" (VInt 5))
                , testCase "the type of a Box of an Int is written" (valid "fn f(b: Box<Int>) -> Int { return Box::unbox(b); }; return f(Box::new(2));")
                , testCase "an Int is not a Box of one" (rejected "fn f(b: Box<Int>) -> Int { return 0; }; return f(3);" "argument 1 of f: expected Box<Int>, got Int")
                , testCase "Box::new is called, not named" (parseFails "h = Box::new; return 0;")
                , testCase "unbox takes a Box" (rejected (point ++ "return Box::unbox(P { x: 1, y: 2 });") "Box::unbox takes a Box, got P")
                , testCase "unbox takes one argument" (rejected (point ++ "b = Box::new(P { x: 1, y: 2 }); return Box::unbox(b, b);") "Box::unbox takes 1 argument, got 2")
                , testCase "Box::new takes one value" (rejected (point ++ "return Box::new(P { x: 1, y: 2 }, 3);") "Box::new takes 1 argument, got 2")
                , testCase "a Box of a Box" (runs "return Box::unbox(Box::unbox(Box::new(Box::new(3))));" (VInt 3))
                , testCase "Box is not a name for a struct" (parseFails "struct Box { x: Int }; return 0;")
                , testCase "a Box needs a type" (parseFails "fn f(b: Box) -> Int { return 0; }; return 0;")
                ]
            , TestList
                "an array behind a Box"
                [ testCase "size, get, first and last look through a Box" (runs "b = Box::new(#[4, 5, 6]); return size(b) * 1000 + get(b, 1) * 100 + first(b) * 10 + last(b) - 40;" (VInt 3506))
                , testCase "set gives the Box back with the element changed" (runs "b = Box::new(#[4, 5, 6]); b = set(b, 0, 9); return b;" (VList [VInt 9, VInt 5, VInt 6]))
                , testCase "the validator knows the size of a Box of an array from its type" (valid "b = Box::new(#[1, 2, 3]); affirm size(b) = 3; return get(b, 2);")
                , testCase "an index past the end" (rejected "b = Box::new(#[1, 2, 3]); return get(b, 3);" "Relation does not hold")
                , testCase "Array::boxed makes n copies, n being any Int" (runs "n = 2 + 1; a = Array::boxed(n, 7); return a;" (VList [VInt 7, VInt 7, VInt 7]))
                , testCase "Array::empty is the array of no elements, of the type its use decides" (runs "struct B<T> { data: Box<Array<T>>, n: Int }; b = B<Int> { data: Array::empty(), n: 0 }; return size(b.data);" (VInt 0))
                , testCase "its size is known to be 0" (valid "struct B<T> { data: Box<Array<T>>, n: Int }; b = B<Bool> { data: Array::empty(), n: 0 }; affirm size(b.data) = 0; return 0;")
                , testCase "it takes no arguments" (rejected "e = Array::empty(3); return 0;" "Array::empty takes no arguments")
                , testCase "its type has no size" (runs "fn f(a: Box<Array<Int>>) -> Int [{ define s = size(a); affirm s > 0; }] [{ }] { return get(a, 0); }; return f(Array::boxed(2, 5));" (VInt 5))
                , testCase "Array<Int> behind a Box is Array<Int, ?>" (valid "fn f(a: Box<Array<Int, ?>>) -> Int { return size(a); }; return f(Array::boxed(2, 5));")
                , testCase "the validator knows what Array::boxed makes" (valid "n = 4; a = Array::boxed(n, 7); affirm size(a) = 4; affirm get(a, 3) = 7; return 0;")
                , testCase "a size that is not negative is needed" (rejected "a = Array::boxed(0 - 1, 7); return 0;" "Relation does not hold")
                , testCase "a size the program computes" (valid "fn f(n: Int) -> Int [{ define s = n; rewrite eqToGtZero s; affirm s > 0; }] [{ }] { a = Array::boxed(n, 0); return get(a, 0); }; return f(3);")
                , testCase "a Box of a size is given where a Box of any size is wanted" (runs "fn f(a: Box<Array<Int>>) -> Int { return size(a); }; return f(Box::new(#[1, 2, 3]));" (VInt 3))
                , testCase "the size the type had is kept" (valid "fn f(a: Box<Array<Int>>) -> Int [{ define s = size(a); affirm s = 3; }] [{ }] { return get(a, 2); }; return f(Box::new(#[1, 2, 3]));")
                , testCase "and is checked" (rejected "fn f(a: Box<Array<Int>>) -> Int [{ define s = size(a); affirm s = 3; }] [{ }] { return get(a, 2); }; return f(Box::new(#[1, 2]));" "Could not prove: s = 3")
                , testCase "at a returned value" (runs "fn f() -> Box<Array<Int>> { return Box::new(#[1, 2]); }; return f();" (VList [VInt 1, VInt 2]))
                , testCase "in a field" (runs "struct S { a: Box<Array<Int>> }; s = S { a: Box::new(#[1, 2, 3]) }; return s.a;" (VList [VInt 1, VInt 2, VInt 3]))
                , testCase "in an assignment" (runs "a = Array::boxed(1, 0); a = Box::new(#[1, 2]); return a;" (VList [VInt 1, VInt 2]))
                , testCase "arrays of different sizes meet in one type" (runs "fn f(a: Box<Array<Int>>) -> Int { return size(a); }; return f(Box::new(#[1])) * 10 + f(Array::boxed(4, 0));" (VInt 14))
                , testCase "a Box of an array of arrays" (runs "a = Array::boxed(2, #[1, 2]); return get(get(a, 1), 1);" (VInt 2))
                , testCase "boxes of equal arrays are equal whatever their sizes were written as" (runs "fn same(a: Box<Array<Int>>, b: Box<Array<Int>>) -> Bool { return a = b; }; return same(Box::new(#[1, 2]), Array::boxed(2, 1)) = false;" (VBool True))
                , testCase "an array of no size is not taken out of its Box" (rejected "a = Array::boxed(2, 0); return Box::unbox(a);" "Box::unbox cannot take an array of no size out of its Box")
                , testCase "a size in the type is still taken out" (runs "return Box::unbox(Box::new(#[1, 2]));" (VList [VInt 1, VInt 2]))
                , testCase "a Box of a size is not given where another size is wanted" (rejected "fn f(a: Box<Array<Int, 3>>) -> Int { return 0; }; return f(Box::new(#[1, 2]));" "expected Box<Array<Int, 3>>, got Box<Array<Int, 2>>")
                , testCase "a Box of any size is not given where a size is wanted" (rejected "fn f(a: Box<Array<Int, 3>>) -> Int { return 0; }; return f(Array::boxed(3, 1));" "expected Box<Array<Int, 3>>, got Box<Array<Int, ?>>")
                , testCase "the elements can be lists" (runs "a = Array::boxed(2, push([], 1)); a = set(a, 1, push(push([], 2), 3)); return a;" (VList [VList [VInt 1], VList [VInt 2, VInt 3]]))
                , testCase "or structs" (runs "trait Clone { }; struct P { x: Int }; impl Clone for P { }; a = Array::boxed(2, P { x: 1 }); return get(a, 1).x + size(a);" (VInt 3))
                , testCase "Array::boxed is called, not named" (parseFails "h = Array::boxed; return 0;")
                , testCase "Array::boxed takes a size and an element" (rejected "return Array::boxed(3);" "Array::boxed takes 2 arguments, got 1")
                , testCase "the size is an Int" (rejected "return Array::boxed(true, 1);" "argument 1 of Array::boxed: expected Int, got Bool")
                ]
            ]
