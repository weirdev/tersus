module TestEq (testEq) where

import Data.List (isInfixOf)

import MirEval (fromMirValue)
import Pipeline (parseSource, runStatements, validateStatements)
import Types
import Syntax
import Solver
import TestHarness
import Utils

-- Eq (lib/eq.tersus): `=` and `!=` in code call Eq::eq for every type but the words, `impl Eq for T { };` is the impl that compares
-- the fields, and what eq promises is the validator's equality, so a test of `a = b` tells the validator `a = b` or `a != b`. The
-- programs are read as the command line reads them, with the libraries the pipeline puts in front of them.
testEq :: Test
testEq =
    let runs source expected = case parseSource source of
            Error e -> Just ("Parse failed: " ++ e)
            Ok stmts -> case runStatements stmts of
                Ok result -> testAssertEq (fmap fromMirValue result) (Just expected)
                Error e -> Just ("Evaluation failed with error: " ++ e)
        valid source = case parseSource source of
            Error e -> Just ("Parse failed: " ++ e)
            Ok stmts -> case validateStatements stmts of
                Ok _ -> Nothing
                Error e -> Just ("Validation failed with error: " ++ e)
        rejected source expected = case parseSource source of
            Error e -> if expected `isInfixOf` e then Nothing else Just ("Expected failure containing: " ++ show expected ++ "\nGot: " ++ e)
            Ok stmts -> testAssertErrorContains expected (validateStatements stmts)
        point = "struct P { x: Int, y: Int }; impl Eq for P { }; "
        shape = "enum S { A { v: Int }, B, C { w: Int, z: Bool } }; impl Eq for S { }; "
        tree = "enum Tree { Leaf, Branch { left: Box<Tree>, value: Int, right: Box<Tree> } }; impl Eq for Tree { }; "
        rose = "enum Rose { Leaf { n: Int }, Node { kids: List<Rose> } }; impl Eq for Rose { }; "
        leaf n = "Rose::Leaf { n: " ++ show (n :: Int) ++ " }"
     in TestList
            "testEq"
            [ TestList
                "the impl that compares the fields"
                [ testCase "a struct" (runs (point ++ "if P { x: 1, y: 2 } = P { y: 2, x: 1 } { if P { x: 1, y: 2 } != P { x: 1, y: 3 } { return 1; }; }; return 0;") (VInt 1))
                , testCase "an enum" (runs (shape ++ "r = 0; if S::A { v: 1 } = S::A { v: 1 } { r = r + 1; }; if S::A { v: 1 } != S::B { r = r + 10; }; if S::C { w: 1, z: true } != S::C { w: 1, z: false } { r = r + 100; }; if S::B = S::B { r = r + 1000; }; return r;") (VInt 1111))
                , testCase "a struct with types needs them to implement Eq" (runs "struct Pair<T> { a: T, b: T }; impl<T> Eq for Pair<T> { }; if Pair<Int> { a: 1, b: 2 } = Pair<Int> { a: 1, b: 2 } { return 1; }; return 0;" (VInt 1))
                , testCase "a struct with types of a type without Eq" (rejected "struct Pair<T> { a: T, b: T }; impl<T> Eq for Pair<T> { }; struct Q { x: Int }; if Pair<Q> { a: Q { x: 1 }, b: Q { x: 1 } } = Pair<Q> { a: Q { x: 1 }, b: Q { x: 1 } } { return 1; }; return 0;" "Pair<Q> is compared with =, which needs it to implement Eq, and Q does not: write impl Eq for Q { };")
                , testCase "a type that holds itself in a Box" (runs (tree ++ "t = Tree::Branch { left: Box::new(Tree::Leaf), value: 2, right: Box::new(Tree::Leaf) }; u = Tree::Branch { left: Box::new(Tree::Leaf), value: 3, right: Box::new(Tree::Leaf) }; if t = t { if t != u { return 1; }; }; return 0;") (VInt 1))
                , testCase "a type that holds a list of itself" (runs (rose ++ "a = Rose::Node { kids: push(push([], " ++ leaf 1 ++ "), " ++ leaf 2 ++ ") }; b = Rose::Node { kids: push(push([], " ++ leaf 1 ++ "), " ++ leaf 3 ++ ") }; if a = a { if a != b { return 1; }; }; return 0;") (VInt 1))
                , testCase "a field without Eq" (rejected "struct Q { x: Int }; struct P { q: Q }; impl Eq for P { }; return 0;" "Q is compared with =, which needs it to implement Eq")
                , testCase "a field that is a permission" (rejected "struct H { a: Addr<Int>, ghost b: Block<Int> }; impl Eq for H { }; return 0;" "holds a permission, which cannot be compared")
                ]
            , TestList
                "what the validator knows"
                [ testCase "a struct in both branches" (valid (point ++ "fn f(a: &P, b: &P) -> Int { if a = b { affirm a.x = b.x; return 1; }; affirm a != b; return 0; }; return f(P { x: 1, y: 2 }, P { x: 1, y: 2 });"))
                , testCase "a list in both branches" (valid "fn f(a: &List<Int>, b: &List<Int>) -> Int { if a != b { affirm a != b; return 0; }; affirm size(a) = size(b); return 1; }; return f([1], [1]);")
                , testCase "an array" (valid "fn f(a: &Array<Int, 3>, b: &Array<Int, 3>) -> Int [{ affirm a = b; }] [{ }] { return 1; }; x = array(3, 1); if x = array(3, 1) { return f(x, array(3, 1)); }; return 0;")
                , testCase "a Box is compared by what it holds" (valid (point ++ "fn f(a: &Box<P>, b: &Box<P>) -> Int { if a = b { affirm a = b; return 1; }; affirm a != b; return 0; }; return f(Box::new(P { x: 1, y: 2 }), Box::new(P { x: 1, y: 2 }));"))
                , testCase "a Box of an array of no size" (runs "b = Array::boxed(3, 1); if b = Array::boxed(3, 1) { if b != Array::boxed(2, 1) { return 1; }; }; return 0;" (VInt 1))
                , testCase "strings" (runs "s = \"ab\"; if s = \"ab\" { if s != \"abc\" { return 1; }; }; return 0;" (VInt 1))
                , testCase "a string in both branches" (valid "fn f(s: &String) -> Int { if s = \"hi\" { affirm s = \"hi\"; return 1; }; return 0; }; return f(\"hi\");")
                ]
            , TestList
                "impls with a body"
                [ testCase "a custom impl is called" (runs "struct P { x: Int, y: Int }; impl Eq for P { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }] { if self.y != other.y { return false; }; if self.x != other.x { return false; }; return true; }; }; if P { x: 1, y: 2 } = P { x: 1, y: 2 } { return 1; }; return 0;" (VInt 1))
                , testCase "a custom impl that does not give the equality" (rejected "struct P { x: Int, y: Int }; impl Eq for P { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ }] { return self.x = other.x; }; }; return 0;" "impl Eq for P: eq does not meet what Eq declares")
                , testCase "Eq::eq on a word is the builtin comparison" (runs "if Eq::eq(1, 1) { if Eq::eq(true, false) = false { return 1; }; }; return 0;" (VInt 1))
                , testCase "Eq::eq on a list and a Box of a sized array" (runs "xs = push([], Box::new(array(2, 1))); if xs = xs { if Box::new(#[1, 2]) = Box::new(#[1, 2]) { return 1; }; }; return 0;" (VInt 1))
                , testCase "Int implements Eq by the language" (rejected "impl Eq for Int { fn eq(self: &Self, other: &Self) -> Bool { return true; }; }; return 0;" "Int implements Eq by the language")
                ]
            , TestList
                "what cannot be compared"
                [ testCase "a type without Eq" (rejected "struct Q { x: Int }; if Q { x: 1 } = Q { x: 1 } { return 1; }; return 0;" "Q is compared with =, which needs it to implement Eq, and Q does not: write impl Eq for Q { }; to compare its fields")
                , testCase "a type parameter without a bound" (rejected "fn same<T>(a: &T, b: &T) -> Bool { return a = b; }; return 0;" "bound it, as in <T: Eq>")
                , testCase "a type parameter with a bound" (runs "fn same<T: Eq>(a: &T, b: &T) -> Bool { return a = b; }; if same(push([], 1), push([], 1)) { return 1; }; return 0;" (VInt 1))
                , testCase "functions" (rejected "fn f(x: Int) -> Int { return x; }; if f = f { return 1; }; return 0;" "functions cannot be compared")
                , testCase "a Box of an array of no size of elements without Eq" (rejected "struct Q { x: Int }; impl Clone for Q { }; b = Array::boxed(3, Q { x: 1 }); if b = Array::boxed(3, Q { x: 1 }) { return 1; }; return 0;" "Box<Array<Q, ?>> is compared with =, which needs its elements to implement Eq")
                , testCase "a program with an Eq of its own" (rejected "trait Eq { }; if [1] = [1] { return 1; }; return 0;" "List<Int> is compared with =")
                ]
            ]
