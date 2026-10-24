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
                , testCase "a Box has the value of what it holds" (runs (point ++ "return Box::new(P { x: 1, y: 2 }) = Box::new(P { x: 1, y: 2 });") (VBool True))
                , testCase "boxes of different values differ" (runs (point ++ "return Box::new(P { x: 1, y: 2 }) != Box::new(P { x: 1, y: 3 });") (VBool True))
                , testCase "a Box is a parameter and a result" (runs (point ++ "fn mk(n: Int) -> Box<P> { return Box::new(P { x: n, y: n * 2 }); }; fn sum(p: Box<P>) -> Int { return p.x + p.y; }; return sum(mk(4));") (VInt 12))
                , testCase "a Box in a struct" (runs (point ++ "struct Q { p: Box<P>, n: Int }; q = Q { p: Box::new(P { x: 3, y: 4 }), n: 5 }; return q.p.x * 100 + q.p.y * 10 + q.n;") (VInt 345))
                , testCase "a Box in a list" (runs (point ++ "ps = push(push([], Box::new(P { x: 1, y: 2 })), Box::new(P { x: 3, y: 4 })); return get(ps, 1).y + size(ps);") (VInt 6))
                , testCase "a Box is read in an update" (runs (point ++ "b = Box::new(P { x: 1, y: 2 }); c = P { x: 9, ..b }; return c.x + c.y;") (VInt 11))
                , testCase "a method is called on what a Box holds" (runs (point ++ "impl P { fn total(self: Self) -> Int { return self.x + self.y; }; }; b = Box::new(P { x: 2, y: 3 }); return Box::unbox(b).total();") (VInt 5))
                , testCase "not on the Box" (rejected (point ++ "impl P { fn total(self: Self) -> Int { return self.x + self.y; }; }; b = Box::new(P { x: 2, y: 3 }); return b.total();") "total is called on a Box<P>, which has no functions: call it on the value inside, as in Box::unbox(b).total(...)")
                , testCase "unbox gives back what was held" (runs (point ++ "b = Box::new(P { x: 2, y: 3 }); p = Box::unbox(b); return p.x * 10 + p.y;") (VInt 23))
                , testCase "unbox of a Box is the value" (runs (point ++ "return Box::unbox(Box::new(P { x: 2, y: 3 })) = P { x: 2, y: 3 };") (VBool True))
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
                , testCase "a Box holds a struct or an enum" (rejected "return Box::new(3);" "Box<T> holds a struct or an enum for now, not Int")
                , testCase "in a type too" (rejected "fn f(b: Box<Int>) -> Int { return 0; }; return 0;" "Box<T> holds a struct or an enum for now, not Int")
                , testCase "a list is not held in a Box" (rejected "fn f(b: Box<List<Int>>) -> Int { return 0; }; return 0;" "Box<T> holds a struct or an enum for now")
                , testCase "Box::new is called, not named" (parseFails "h = Box::new; return 0;")
                , testCase "unbox takes a Box" (rejected (point ++ "return Box::unbox(P { x: 1, y: 2 });") "Box::unbox takes a Box, got P")
                , testCase "unbox takes one argument" (rejected (point ++ "b = Box::new(P { x: 1, y: 2 }); return Box::unbox(b, b);") "Box::unbox takes 1 argument, got 2")
                , testCase "Box::new takes one value" (rejected (point ++ "return Box::new(P { x: 1, y: 2 }, 3);") "Box::new takes 1 argument, got 2")
                , testCase "a Box of a Box" (rejected (point ++ "fn f(b: Box<Box<P>>) -> Int { return 0; }; return 0;") "Box<T> holds a struct or an enum for now")
                , testCase "Box is not a name for a struct" (parseFails "struct Box { x: Int }; return 0;")
                , testCase "a Box needs a type" (parseFails "fn f(b: Box) -> Int { return 0; }; return 0;")
                ]
            ]
