module TestCopies (testCopies) where

import Data.List (isInfixOf)

import Pipeline (compileSource)
import Syntax
import TestHarness
import Utils

-- A copy is made where the program writes `clone`, and a value that is not Copy is moved: Clone and Copy are traits that a type says it has,
-- and MirMoves reports a use of a value that was moved (see LANGUAGE.md, Moves, Clone And Copy).
testCopies :: Test
testCopies =
    let runs body expected = parseEvalProgramHelper body (Just expected)
        valid = parseValidProgramHelper
        rejected = parseValidateFailProgramHelper
        -- (the check is part of lowering, so a program that is run, and not validated, meets it)
        moveError source expected = parseEvalProgramFailHelper source expected
        -- (the traits are in the prelude of a program that is compiled by the pipeline; these programs are parsed without it)
        markers = "trait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; }; trait Copy { }; impl<T: Clone> Clone for List<T> { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }] { out = []; i = 0; while i < size(self) [{ affirm i >= 0; affirm i <= size(self); affirm size(out) = i; affirm forall j in 0..i: get(out, j) = get(self, j); }] shrinks size(self) - i { out = push(out, clone(get(self, i))); i = i + 1; }; return out; }; }; impl<T: Clone, n> Clone for Array<T, n> { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }] { out = []; i = 0; while i < size(self) [{ affirm i >= 0; affirm i <= size(self); affirm size(out) = i; affirm forall j in 0..i: get(out, j) = get(self, j); }] shrinks size(self) - i { out = push(out, clone(get(self, i))); i = i + 1; }; return Array::fromList(out); }; }; impl<T: Clone> Clone for Box<T> { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }] { return Box::new(clone(Box::unbox(self))); }; }; "
        point = markers ++ "struct P { x: Int, y: Int }; impl Clone for P { }; impl Copy for P { }; "
        named = markers ++ "struct N { xs: List<Int>, n: Int }; impl Clone for N { }; "
        -- (the place of the error comes with the program parsed by the pipeline, which keeps the line of each statement)
        placed source expected = case compileSource source of
            Ok _ -> Just ("Expected failure containing: " ++ show expected)
            Error e -> if expected `isInfixOf` e then Nothing else Just ("Expected failure containing: " ++ show expected ++ "\nGot: " ++ e)
        accepted source = case compileSource source of
            Ok _ -> Nothing
            Error e -> Just ("Expected to be accepted, got: " ++ e)
     in TestList
            "testCopies"
            [ TestList
                "clone"
                [ testCase "a list is cloned" (runs (markers ++ "xs = push([], 1); ys = clone(xs); ys = push(ys, 2); return size(xs) * 10 + size(ys);") (VInt 12))
                , testCase "and by a method" (runs (markers ++ "xs = push([], 1); ys = xs.clone(); ys = push(ys, 2); return size(xs) * 10 + size(ys);") (VInt 12))
                , testCase "a clone has the value of what it clones" (valid (markers ++ "xs = push(push([], 1), 2); ys = clone(xs); affirm ys = xs; affirm size(ys) = 2; affirm get(ys, 1) = 2; return size(ys);"))
                , testCase "and in a function that lends" (valid (markers ++ "fn dup(xs: &List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(xs); affirm forall j in 0..size(xs): get(return, j) = get(xs, j); }] { return clone(xs); }; return size(dup([1, 2]));"))
                , testCase "an array is cloned" (runs (markers ++ "a = array(2, 7); b = clone(a); b = set(b, 0, 1); return get(a, 0) * 10 + get(b, 0);") (VInt 71))
                , testCase "a list of lists is cloned to the depth" (runs (markers ++ "rows = push([], push([], 1)); copy = clone(rows); copy = set(copy, 0, push(clone(get(copy, 0)), 2)); return size(get(rows, 0)) * 10 + size(get(copy, 0));") (VInt 12))
                , testCase "a struct says that it is Clone" (runs (named ++ "a = N { xs: push([], 1), n: 2 }; b = clone(a); return size(a.xs) + b.n;") (VInt 3))
                , testCase "a struct that does not is not cloned" (rejected (markers ++ "struct S { n: Int }; s = S { n: 1 }; t = clone(s); return t.n;") "S does not implement Clone")
                , testCase "nor a list of them" (rejected (markers ++ "struct S { n: Int }; l = push([], S { n: 1 }); m = clone(l); return size(m);") "needs T to implement Clone, and S does not")
                , testCase "an impl Clone asks the fields to be Clone" (rejected (markers ++ "struct S { n: Int }; struct T { s: S }; impl Clone for T { }; return 1;") "S does not implement Clone")
                , testCase "an enum is Clone" (runs (markers ++ "enum E { A { xs: List<Int> }, B }; impl Clone for E { }; e = E::A { xs: push([], 1) }; f = clone(e); return f is E::A;") (VBool True))
                , testCase "clone takes one argument" (rejected "return clone(1, 2);" "clone takes 1 argument")
                , testCase "a function of the program can have the name" (runs "fn clone(x: Int) -> Int { return x + 1; }; return clone(1);" (VInt 2))
                ]
            , TestList
                "copy"
                [ testCase "an Int is copied wherever it is wanted" (runs "fn id(x: Int) -> Int { return x; }; n = 3; return id(n) + id(n) + n;" (VInt 9))
                , testCase "and a Bool and a function" (runs "fn id(f: fn(Int) -> Int, b: Bool) -> Int { if b { return f(1); }; return 0; }; fn inc(x: Int) -> Int { return x + 1; }; f = inc; return id(f, true) + id(f, true);" (VInt 4))
                , testCase "a struct that says it is Copy" (runs (point ++ "fn sum(p: P) -> Int { return p.x + p.y; }; p = P { x: 1, y: 2 }; return sum(p) + sum(p);") (VInt 6))
                , testCase "and one that does not is moved" (moveError "struct P { x: Int, y: Int }; fn sum(p: P) -> Int { return p.x + p.y; }; p = P { x: 1, y: 2 }; return sum(p) + sum(p);" "p was moved")
                , testCase "an enum of numbers that is Copy" (runs (markers ++ "enum C { Red, Green }; impl Clone for C { }; impl Copy for C { }; fn same(c: C) -> C { return c; }; c = C::Red; a = same(c); b = same(c); return a is C::Red;") (VBool True))
                , testCase "Copy needs Clone" (rejected (markers ++ "struct P { x: Int }; impl Copy for P { }; return 1;") "P is Copy only if it is Clone")
                , testCase "and fields that are Copy" (rejected (markers ++ "struct P { xs: List<Int> }; impl Clone for P { }; impl Copy for P { }; return 1;") "the field xs of P is List<Int>, which is not Copy")
                , testCase "a field that is a struct has to be Copy too" (rejected (markers ++ "struct Q { n: Int }; impl Clone for Q { }; struct P { q: Q }; impl Clone for P { }; impl Copy for P { }; return 1;") "the field q of P is Q, which is not Copy")
                , testCase "an array of Copy is Copy" (runs "fn first(a: Array<Int, 2>) -> Int { return get(a, 0); }; a = array(2, 5); return first(a) + first(a);" (VInt 10))
                , testCase "a list never is" (moveError "fn size2(a: List<Int>) -> Int { return size(a); }; l = [1]; return size2(l) + size2(l);" "l was moved")
                , testCase "a struct with types is Copy for the types that are" (runs (markers ++ "struct Pair<T> { a: T, b: T }; impl<T> Clone for Pair<T> { }; impl<T> Copy for Pair<T> { }; fn left(p: Pair<Int>) -> Int { return p.a; }; p = Pair<Int> { a: 1, b: 2 }; return left(p) + left(p) + p.b;") (VInt 4))
                , testCase "and not for the types that are not" (moveError (markers ++ "struct Pair<T> { a: T, b: T }; impl<T> Clone for Pair<T> { }; impl<T> Copy for Pair<T> { }; fn left(p: Pair<List<Int>>) -> Int { return size(p.a); }; p = Pair<List<Int>> { a: [1], b: [2] }; return left(p) + left(p);") "p was moved")
                ]
            , TestList
                "moves"
                [ testCase "a value that is moved cannot be used" (moveError "xs = [1]; ys = xs; return size(xs);" "xs was moved")
                , testCase "a clone keeps it" (runs (markers ++ "xs = [1]; ys = clone(xs); return size(xs) + size(ys);") (VInt 2))
                , testCase "a move into a call" (moveError "fn f(a: List<Int>) -> Int { return size(a); }; xs = [1]; return f(xs) + f(xs);" "xs was moved")
                , testCase "into a list" (moveError "xs = [1]; rows = push([], xs); return size(xs);" "xs was moved")
                , testCase "into a struct" (moveError "struct S { a: List<Int> }; xs = [1]; s = S { a: xs }; return size(xs);" "xs was moved")
                , testCase "by a return, so nothing is used after it" (runs "xs = [1]; return xs;" (VList [VInt 1]))
                , testCase "an assignment gives the variable a value again" (runs "xs = [1]; ys = xs; xs = [2, 3]; return size(xs) + size(ys);" (VInt 3))
                , testCase "xs = push(xs, 1) moves and gives back" (runs "xs = []; xs = push(xs, 1); xs = push(xs, 2); return size(xs);" (VInt 2))
                , testCase "in a loop too" (runs "xs = []; for i in 0..3 { xs = push(xs, i); }; return size(xs);" (VInt 3))
                , testCase "a move in one branch is a move" (moveError "fn f(c: Bool, a: List<Int>) -> Int { b = [0]; if c { b = a; }; return size(a); }; return f(true, [1]);" "a was moved")
                , testCase "and in both" (moveError "fn f(c: Bool, a: List<Int>) -> Int { b = [0]; if c { b = a; } else { b = a; }; return size(a); }; return f(true, [1]);" "a was moved")
                , testCase "a move that is not in the branch that continues" (runs "fn f(c: Bool, a: List<Int>) -> Int { if c { b = a; return size(b); }; return size(a); }; return f(true, [1]) + f(false, [1, 2]);" (VInt 3))
                , testCase "a move in a loop is used by the next iteration" (moveError "xs = [1]; ys = []; for i in 0..2 { ys = push(ys, xs); }; return size(ys);" "xs was moved")
                , testCase "unless the loop gives the variable a value" (runs "xs = [1]; ys = []; for i in 0..2 { ys = push(ys, xs); xs = push([], i); }; return size(ys);" (VInt 2))
                , testCase "a field can be moved while the others are kept" (runs "struct S { a: List<Int>, b: List<Int> }; s = S { a: [1], b: [2, 3] }; x = s.a; y = push(x, 0); return size(y) + size(s.b);" (VInt 4))
                , testCase "and the whole is then not used" (moveError "struct S { a: List<Int>, b: List<Int> }; s = S { a: [1], b: [2, 3] }; x = push(s.a, 0); t = s; return size(x);" "s.a was moved")
                , testCase "a field that is moved cannot be moved again" (moveError "struct S { a: List<Int> }; s = S { a: [1] }; x = push(s.a, 0); y = push(s.a, 1); return size(x) + size(y);" "s.a was moved")
                , testCase "a struct update moves the fields it takes" (moveError "struct S { a: List<Int>, b: List<Int> }; s = S { a: [1], b: [2] }; t = S { a: [0], ..s }; return size(s.b);" "s.b was moved")
                , testCase "the same local twice in one statement" (moveError "xs = [1]; ys = push(push([], xs), xs); return size(ys);" "xs was moved")
                , testCase "a clone of the first" (runs (markers ++ "xs = [1]; ys = push(push([], clone(xs)), xs); return size(ys);") (VInt 2))
                , testCase "a value that is only read is not moved" (runs "xs = [1, 2]; n = size(xs) + size(xs) + get(xs, 0); return n + size(xs);" (VInt 7))
                ]
            , TestList
                "views"
                [ testCase "an element that is read is not moved" (runs "rows = push(push([], [1]), [2, 3]); return size(get(rows, 1)) + size(first(rows)) + size(rows);" (VInt 5))
                , testCase "an element held in a variable and read" (runs "rows = push(push([], [1]), [2, 3]); row = get(rows, 1); return size(row) + get(row, 0) + size(rows);" (VInt 6))
                , testCase "cannot be moved out of its list" (moveError "rows = push([], [1]); row = get(rows, 0); row = push(row, 2); return size(rows);" "out of a list")
                , testCase "nor returned" (moveError "fn f(rows: &List<List<Int>>) -> List<Int> { return get(rows, 0); }; return f([[1]]);" "out of a list")
                , testCase "unless it is cloned" (runs (markers ++ "rows = push([], [1]); row = clone(get(rows, 0)); row = push(row, 2); return size(rows) * 10 + size(row);") (VInt 12))
                , testCase "the first and last are elements too" (moveError "fn f(rows: List<List<Int>>) -> List<Int> { return last(rows); }; return f([[1]]);" "out of a list")
                , testCase "a field of a parameter that is lent cannot be moved" (moveError "struct S { a: List<Int> }; fn f(s: &S) -> List<Int> { return s.a; }; return f(S { a: [1] });" "s.a is lent")
                , testCase "nor the parameter" (moveError "fn f(a: &List<Int>) -> List<Int> { return a; }; return f([1]);" "a is lent")
                , testCase "a clone of it is a value of its own" (runs (markers ++ "fn f(a: &List<Int>) -> List<Int> { return push(clone(a), 9); }; l = [1]; m = f(l); return size(l) * 10 + size(m);") (VInt 12))
                , testCase "a lent value given on to another that is lent" (runs "fn inner(a: &List<Int>) -> Int { return size(a); }; fn outer(a: &List<Int>) -> Int { return inner(a) + inner(a); }; return outer([1, 2]);" (VInt 4))
                , testCase "a lent value given to a parameter that is owned" (moveError "fn owner(a: List<Int>) -> Int { return size(a); }; fn outer(a: &List<Int>) -> Int { return owner(a); }; return outer([1]);" "a is lent")
                , testCase "a value that is lent and moved by one call" (moveError "fn both(a: &List<Int>, b: List<Int>) -> Int { return size(a) + size(b); }; l = [1]; return both(l, l);" "lent to this call and moved by it too")
                , testCase "a match reads what it is over" (runs "enum T { A { xs: List<Int> }, B }; fn count(t: &T) -> Int { return match t { T::A { xs: xs } => size(xs), T::B => 0 }; }; t = T::A { xs: [1, 2] }; return count(t) + count(t);" (VInt 4))
                , testCase "and a field it binds is a part of it" (moveError "enum T { A { xs: List<Int> }, B }; fn take(t: &T) -> List<Int> { return match t { T::A { xs: xs } => xs, T::B => [] }; }; return size(take(T::A { xs: [1] }));" "is lent")
                , testCase "a match on a value that is owned moves its fields" (runs "enum T { A { xs: List<Int> }, B }; fn take(t: T) -> List<Int> { return match t { T::A { xs: xs } => xs, T::B => [] }; }; return size(take(T::A { xs: [1, 2] }));" (VInt 2))
                , testCase "a for loop reads the list" (runs "xs = [1, 2, 3]; total = 0; for x in xs { total = total + x; }; return total + size(xs);" (VInt 9))
                , testCase "and an element it binds is read" (runs "rows = push(push([], [1]), [2, 3]); total = 0; for r in rows { total = total + size(r); }; return total + size(rows);" (VInt 5))
                , testCase "or cloned" (runs (markers ++ "rows = push(push([], [1]), [2, 3]); out = []; for r in rows { out = push(out, clone(r)); }; return size(out) + size(rows);") (VInt 4))
                , testCase "an element it binds is not moved" (moveError "rows = push([], [1]); out = []; for r in rows { out = push(out, r); }; return size(out);" "out of a list")
                , testCase "a box is read through" (runs "enum T { L, N { v: Int, next: Box<T> } }; fn depth(t: &T) -> Int { return match t { T::L => 0, T::N { v: v, next: n } => 1 + depth(Box::unbox(n)) }; }; t = T::N { v: 1, next: Box::new(T::L) }; return depth(t) + depth(t);" (VInt 2))
                ]
            , TestList
                "struct update"
                [ testCase "from a clone takes the fields one by one" (runs (named ++ "fn bump(a: &N) -> N { return N { n: a.n + 1, ..clone(a) }; }; a = N { xs: push([], 1), n: 2 }; b = bump(a); return size(a.xs) + b.n + size(b.xs);") (VInt 5))
                , testCase "of a struct that is not Clone, whose fields are" (runs (markers ++ "struct S { xs: List<Int>, n: Int }; fn bump(a: &S) -> S { return S { n: a.n + 1, ..clone(a) }; }; s = S { xs: [1], n: 1 }; t = bump(s); return size(s.xs) + t.n + size(t.xs);") (VInt 4))
                , testCase "from a lent value that is not cloned is an error" (moveError "struct S { xs: List<Int>, n: Int }; fn bump(a: &S) -> S { return S { n: a.n + 1, ..a }; }; return 1;" "is lent")
                , testCase "from an owned value takes its fields" (runs "struct S { xs: List<Int>, n: Int }; fn bump(a: S) -> S { return S { n: a.n + 1, ..a }; }; s = bump(S { xs: [1], n: 1 }); return size(s.xs) + s.n;" (VInt 3))
                , testCase "an enum variant too" (runs (markers ++ "enum E { A { xs: List<Int>, n: Int }, B }; impl Clone for E { }; fn bump(e: &E) -> E { return E::A { n: 9, ..clone(e) }; }; r = bump(E::A { xs: [1, 2], n: 1 }); return size((r as E::A).xs) + (r as E::A).n;") (VInt 11))
                ]
            , TestList
                "review"
                [ -- a loop down a recursive value reaches a fixed point (it used to add a step to the places at each round)
                  testCase "a loop down a recursive value ends" (runs "enum N { End, Next { tail: Box<N> } }; fn depth(root: &Box<N>) -> Int { node = Box::unbox(root); n = 0; while node is N::Next shrinks node { node = Box::unbox((node as N::Next).tail); n = n + 1; }; return n; }; return depth(Box::new(N::Next { tail: Box::new(N::End) }));" (VInt 1))
                , testCase "a view on one branch and a value of its own on the other is a view" (moveError "fn f(c: Bool, rows: &List<List<Int>>) -> List<Int> [{ affirm size(rows) > 0; }] [{ }] { row = []; if c { row = get(rows, 0); }; return row; }; return size(f(true, [[1]]));" "out of a list")
                , testCase "a user function named clone is called by a struct update" (runs "struct S { n: Int }; fn clone(s: &S) -> S { return S { n: s.n + 1 }; }; s = S { n: 1 }; t = S { ..clone(s) }; return t.n;" (VInt 2))
                ]
            , TestList
                "arrays of copies"
                [ testCase "array(n, x) moves x" (moveError (markers ++ "xs = [1]; a = array(2, xs); return size(xs);") "xs was moved")
                , testCase "of a type that is Clone" (rejected "struct S { n: Int }; a = array(2, S { n: 1 }); return 1;" "S does not implement Clone")
                , testCase "Array::boxed too" (moveError (markers ++ "xs = [1]; a = Array::boxed(2, xs); return size(xs);") "xs was moved")
                ]
            , TestList
                "type parameters"
                [ testCase "a type parameter is Clone" (runs "fn twice<T>(x: T) -> List<T> { return push(push([], clone(x)), x); }; return size(twice(3)) + size(twice([1]));" (VInt 4))
                , testCase "and moved" (moveError "fn twice<T>(x: T) -> List<T> { return push(push([], x), x); }; return size(twice(3));" "x was moved")
                , testCase "a bound asks for Clone" (runs (markers ++ "fn twice<T: Clone>(x: T) -> List<T> { return push(push([], clone(x)), x); }; return size(twice(3));") (VInt 2))
                , testCase "of the type it is given" (rejected (markers ++ "struct S { n: Int }; fn twice<T: Clone>(x: T) -> List<T> { return push(push([], clone(x)), x); }; return size(twice(S { n: 1 }));") "twice needs T to implement Clone, and S does not")
                , testCase "or Copy" (runs (markers ++ "fn twice<T: Copy>(x: T) -> List<T> { return push(push([], x), x); }; return size(twice(3));") (VInt 2))
                , testCase "a list is not" (rejected (markers ++ "fn twice<T: Copy>(x: T) -> List<T> { return push(push([], x), x); }; return size(twice([1]));") "twice needs T to implement Copy, and List<Int> does not")
                , testCase "an element of a generic list is cloned to be returned" (runs "fn head<T>(items: &List<T>) -> T { return clone(get(items, 0)); }; return size(head(push([], [1, 2])));" (VInt 2))
                , testCase "and moved out of it is an error" (moveError "fn head<T>(items: &List<T>) -> T { return get(items, 0); }; return head([1]);" "out of a list")
                ]
            , TestList
                "places"
                [ testCase "the error has the line of the statement" (placed "xs = [1];\nys = xs;\nn = size(xs);\nreturn n;" "line 3:1")
                , testCase "and the line where it was moved" (placed "xs = [1];\nys = xs;\nn = size(xs);\nreturn n;" "moved at line 2:1")
                , testCase "in a function" (placed "fn f(xs: List<Int>) -> Int {\n    ys = xs;\n    return size(xs);\n};\nreturn f([1]);" "in f, line 3:5")
                , testCase "in a branch" (placed "fn f(c: Bool, xs: List<Int>) -> Int {\n    if c {\n        ys = xs;\n    };\n    return size(xs);\n};\nreturn f(true, [1]);" "in f, line 5:5")
                , testCase "and the name of a variable that is read" (placed "rows = push([], [1]);\nrow = get(rows, 0);\nrow = push(row, 2);\nreturn 0;" "cannot move row (rows[..]) out of a list")
                , testCase "a program that is fine is accepted" (accepted "xs = [1];\nys = clone(xs);\nreturn size(xs) + size(ys);")
                , testCase "several errors are reported" (placed "xs = [1];\nys = xs;\nzs = xs;\nn = size(xs);\nreturn n;" "line 4:1")
                ]
            ]
