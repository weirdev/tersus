{-# LANGUAGE PatternSynonyms #-}

module TestBorrow (testBorrow) where

import Data.List (intercalate, isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Compile (elaborateStatements, lowerSource)
import qualified Mir as M
import MirMoves (checkMoves, finishLowered)
import Syntax
import TestHarness
import TestParserFragments (parseStatementBlock)
import Types (Arg (..), Storage (..), Type (..), instanceName)
import TestStorage (pattern TBox, pattern TList, stdProtocols, stdStorage)
import Utils (Result (..))
import ValidatorNative (validateCompiled)

-- &T: a parameter that the function only reads. A call lends the value, so it is not copied for the call and the caller keeps it; in
-- the function the parameter is its type, which it cannot assign.
testBorrow :: Test
testBorrow =
    let runs body expected = parseEvalProgramHelper body (Just expected)
        valid = parseValidProgramHelper
        checks body expected = parseValidateEvalProgramHelper body (Just (VInt expected))
        holder = "struct H { r: &mut Int }; fn put(h: &mut H, r: &mut Int) -> Int { *h = H { r: &mut *r }; return 0; }; "
        rejected = parseValidateFailProgramHelper
        readOnlyIn fn how = "Move error: in " ++ fn ++ ": the value in _2 may be reached through a shared reference or a parameter lent to be read (&T), so nothing can be changed through it: it cannot be " ++ how
        readOnly fn local how = "Move error: in " ++ fn ++ ": " ++ local ++ " may be reached through a shared reference or a parameter lent to be read (&T), so nothing can be changed through it: it cannot be " ++ how
        sharedHolder = "struct W { r: &mut Int }; "
        pairHolder = "struct H { r: &mut Int, n: Int }; "
        nestedHolder = "struct A { r: &mut Int, n: Int }; struct B { a: A, n: Int }; "
        parseFails source = case parseValidProgramHelper source of
            Just err | take 11 err == "Parse faile" -> Nothing
            _ -> Just ("Expected a parse error for: " ++ source)
        total = "fn total(a: &List<Int>) -> Int [{ define s = size(a); affirm s >= 0; }] [{ }] { t = 0; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i { t = t + get(a, i); i = i + 1; }; return t; }; "
     in TestList
            "testBorrow"
            [ loanTableCases
            , permissionCases
            , TestList
                "lending"
                [ testCase "a list is lent" (runs (total ++ "l = push(push([], 3), 4); return total(l);") (VInt 7))
                , testCase "and the caller keeps it" (runs (total ++ "l = push(push([], 3), 4); return total(l) + total(l) + size(l);") (VInt 16))
                , testCase "a value that is made for the call is lent" (runs (total ++ "return total(push(push([], 1), 2));") (VInt 3))
                , testCase "an array is lent" (runs "fn ends(a: &Array<Int, 4>) -> Int { return get(a, 0) + get(a, 3); }; x = #[1, 2, 3, 4]; return ends(x) + get(x, 1);" (VInt 7))
                , testCase "a struct is lent" (runs "struct S { xs: List<Int>, n: Int }; fn count(s: &S) -> Int { return size(s.xs) + s.n; }; s = S { xs: push([], 1), n: 10 }; return count(s) + size(s.xs);" (VInt 12))
                , testCase "an Int is lent too" (runs "fn twice(n: &Int) -> Int { return n * 2; }; return twice(4);" (VInt 8))
                , testCase "an update borrow is given to a read reference parameter" (runs "fn read(n: &Int) -> Int { return n; }; x = 1; return read(&mut x);" (VInt 1))
                , testCase "a lent parameter is passed on to a lent one" (runs "fn inner(a: &List<Int>) -> Int { return size(a); }; fn outer(a: &List<Int>) -> Int { return inner(a) + inner(a) + size(a); }; return outer(push([], 1));" (VInt 3))
                , testCase "and to one that is owned, which gets a copy" (runs "fn owner(a: List<Int>) -> Int { return size(push(a, 1)); }; fn mixed(a: &List<Int>) -> Int { return owner(clone(a)) + size(a); }; return mixed(push([], 1));" (VInt 3))
                , testCase "a lent parameter is returned as a copy" (runs "fn same(a: &List<Int>) -> List<Int> { return clone(a); }; l = push([], 5); m = same(l); m = push(m, 6); return l;" (VList [VInt 5]))
                , testCase "a copy of it can be changed" (runs "fn more(a: &List<Int>) -> List<Int> { return push(clone(a), 9); }; l = push([], 1); return more(l);" (VList [VInt 1, VInt 9]))
                , testCase "an array that is lent can give a changed copy" (runs "fn bump(a: &Array<Int, 3>) -> Array<Int, 3> { return set(a, 0, get(a, 0) + 1); }; x = #[1, 2, 3]; x = bump(x); return bump(x);" (VList [VInt 3, VInt 2, VInt 3]))
                , testCase "a lent parameter is also an owned one in one call" (runs "fn both(a: &List<Int>, b: List<Int>) -> Int { return size(a) + size(b); }; l = push([], 1); return both(l, clone(l));" (VInt 2))
                , testCase "a value that is lent and given in one call is not shared" (runs "fn both(a: &List<Int>, b: List<Int>) -> Int { b = push(b, 9); return size(a) * 10 + size(b); }; l = push([], 1); return both(l, clone(l));" (VInt 12))
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
                , testCase "a & result has to be from a parameter" (rejected "fn f() -> &List<Int> { return []; }; return 0;" "no parameter of it is a reference for the result to be from")
                , testCase "a field can be a read reference" (runs "struct S { a: &List<Int> }; xs = [1, 2]; s = S { a: &xs }; r = s.a; return size(*r);" (VInt 2))
                , testCase "nor a Box" (runs "fn f(a: Box<&Int>) -> Int { r = Box::unbox(a); return *r; }; x = 41; return f(Box::new(&x));" (VInt 41))
                , testCase "a function value lends too" (valid "fn total(a: &List<Int>) -> Int { return size(a); }; f = total; return 0;")
                , testCase "a function that lends is not a function that does not" (rejected "fn total(a: &List<Int>) -> Int { return size(a); }; fn apply(f: fn(List<Int>) -> Int) -> Int { return 0; }; return apply(total);" "expected fn(List<Int>) -> Int, got fn(&List<Int>) -> Int")
                , testCase "the & can have spaces" (runs "fn f(a: & List<Int>) -> Int { return size(a); }; return f([1]);" (VInt 1))
                , testCase "a & needs a type" (parseFails "fn f(a: &) -> Int { return 0; }; return 0;")
                ]
            , TestList
                "local read references"
                [ testCase "a local borrow reads what it is to" (runs "xs = [1, 2, 3]; r = &xs; return size(*r) + get(*r, 0);" (VInt 4))
                , testCase "a reference local is given to a lent builtin" (runs "xs = [1, 2]; r = &xs; return size(r) + first(r);" (VInt 3))
                , testCase "a generic lent parameter takes a reference local" (runs "fn f<T>(xs: &List<T>) -> Int { return size(xs); }; ys = [1, 2]; r = &ys; return f(r);" (VInt 2))
                , testCase "an element borrowed with get is read where it is" (runs "xss = push(push([], push(push([], 1), 2)), push([], 3)); e = &get(xss, 0); return size(e) * 10 + get(e, 1);" (VInt 22))
                , testCase "a borrow of a field" (runs "struct Point { x: Int, y: Int }; p = Point { x: 3, y: 4 }; r = &p.y; return *r;" (VInt 4))
                , testCase "a borrow of an element" (runs "xs = [5, 6]; r = &get(xs, 1); return *r;" (VInt 6))
                , testCase "a reference is given on to a lent parameter" (runs "fn total(a: &List<Int>) -> Int { return size(a); }; xs = [1, 2]; r = &xs; return total(r) + total(&xs);" (VInt 4))
                , testCase "a place can be used again after the borrow's last use" (runs "xs = [1, 2, 3]; r = &xs; a = size(*r); xs = push(xs, 4); return a * 10 + size(xs);" (VInt 34))
                , testCase "a read reborrow of an update reference" (runs "x = 4; r = &mut x; s = &*r; a = *s; *r = 9; return a * 10 + *r;" (VInt 49))
                , testCase "a local reference cannot escape as a value" (rejected "fn f() -> Int { x = 1; r = &x; return r; }; return f();" "got &Int")
                ]
            , TestList
                "update references"
                [ testCase "an update through a local reference" (runs "x = 4; r = &mut x; *r = *r + 1; return x;" (VInt 5))
                , testCase "an update of a whole list through a reference" (runs "xs = [1, 2, 3]; r = &mut xs; *r = push(clone(*r), 4); return size(xs) * 10 + get(xs, 3);" (VInt 44))
                , testCase "an update of an element through a reference" (runs "xs = [1, 2, 3]; r = &mut get(xs, 0); *r = 9; return get(xs, 0) * 10 + get(xs, 1);" (VInt 92))
                , testCase "disjoint fields can be borrowed for updating together" (runs "struct Point { x: Int, y: Int }; p = Point { x: 1, y: 2 }; a = &mut p.x; b = &mut p.y; *a = 5; *b = 6; return p.x * 10 + p.y;" (VInt 56))
                , testCase "an update parameter with its contract" (runs "fn increment(n: &mut Int) -> Int writes(n) [{ affirm *n < 100; }] [{ affirm *n = old(*n) + 1; affirm return = *n; }] { *n = *n + 1; return *n; }; x = 4; y = increment(&mut x); return x * 10 + y;" (VInt 55))
                , testCase "a field update through a parameter, with the rest kept" (runs "struct Point { x: Int, y: Int }; fn bumpX(p: &mut Point) -> Int writes(p.x) [{ }] [{ affirm (*p).x = old((*p).x) + 1; affirm (*p).y = old((*p).y); }] { (*p).x = (*p).x + 1; return (*p).x; }; pt = Point { x: 1, y: 2 }; n = bumpX(&mut pt); return n * 100 + pt.x * 10 + pt.y;" (VInt 222))
                , testCase "an update in a loop" (runs "fn inc(n: &mut Int) -> Int [{ }] [{ affirm *n = old(*n) + 1; }] { *n = *n + 1; return *n; }; x = 0; while x < 3 [{ affirm x >= 0; affirm x <= 3; }] shrinks 3 - x { y = inc(&mut x); }; return x;" (VInt 3))
                , testCase "an update reference is not lent silently" (rejected "fn inc(n: &mut Int) -> Int { *n = *n + 1; return *n; }; x = 4; return inc(x);" "is not lent silently")
                , testCase "assignment is only through an update reference" (rejected "x = 4; r = &x; *r = 5; return x;" "assignment is through a read reference")
                , testCase "an update parameter is not assigned itself" (rejected "fn f(n: &mut Int) -> Int { n = 5; return *n; }; x = 1; return f(&mut x);" "is borrowed (&mut), so it is assigned through it")
                , testCase "the writes clause bounds what may change" (rejected "struct Point { x: Int, y: Int }; fn bad(p: &mut Point) -> Int writes(p.x) [{ }] [{ }] { (*p).y = 9; return (*p).y; }; pt = Point { x: 1, y: 2 }; return bad(&mut pt);" "writes clause of the function does not allow")
                , testCase "an old fact is not a fact about the updated value" (rejected "fn inc(n: &mut Int) -> Int [{ }] [{ }] { *n = *n + 1; return *n; }; x = 4; y = inc(&mut x); affirm x = 4; return y;" "Could not prove: x = 4")
                , testCase "the new fact is the one the contract gives" (valid "fn inc(n: &mut Int) -> Int [{ }] [{ affirm *n = old(*n) + 1; }] { *n = *n + 1; return *n; }; x = 4; y = inc(&mut x); affirm x = 5; return y;")
                , testCase "an element reference is to the element the index named when it was made" (runs "xs = [1, 2]; i = 0; r = &mut get(xs, i); i = 1; *r = 9; affirm get(xs, 0) = 9; return get(xs, 0) * 10 + get(xs, 1);" (VInt 92))
                , testCase "a reference to an element that is not there is not made" (rejected "xs = [1]; r = &get(xs, 1); return *r;" "not known to be in the value it borrows")
                , testCase "a write through a reference has to meet the invariant of the struct it rebuilds" (rejected "struct S { n: Int } invariant [{ affirm n >= 0; }]; s = S { n: 0 }; r = &mut s.n; *r = -1; return s.n;" "does not meet its invariant")
                , testCase "and of a struct inside it" (rejected "struct A { n: Int } invariant [{ affirm n >= 0; }]; struct S { a: A, m: Int }; s = S { a: A { n: 1 }, m: 2 }; r = &mut s.a.n; *r = -3; return s.m;" "does not meet its invariant")
                , testCase "a write that meets the invariant is proved, and the invariant is known after it" (runs "struct S { n: Int } invariant [{ affirm n >= 0; }]; s = S { n: 0 }; r = &mut s.n; *r = 5; affirm s.n >= 0; return s.n;" (VInt 5))
                , testCase "the writes clause binds a reference a local holds" (rejected "struct Point { x: Int, y: Int }; fn bad(p: &mut Point) -> Int writes(p.x) [{ }] [{ }] { q = &mut (*p).y; *q = 9; return (*p).y; }; pt = Point { x: 1, y: 2 }; return bad(&mut pt);" "writes clause of the function does not allow")
                , testCase "and a place given on to a call" (rejected "struct Point { x: Int, y: Int }; fn touch(q: &mut Int) -> Int [{ }] [{ }] { *q = 5; return *q; }; fn bad(p: &mut Point) -> Int writes(p.x) [{ }] [{ }] { z = touch(&mut (*p).y); return z; }; pt = Point { x: 1, y: 2 }; return bad(&mut pt);" "this call may change p.y")
                , testCase "the writes clause allows its field through a local reference" (runs "struct Point { x: Int, y: Int }; fn good(p: &mut Point) -> Int writes(p.x) [{ }] [{ }] { q = &mut (*p).x; *q = 9; return (*p).x; }; pt = Point { x: 1, y: 2 }; return good(&mut pt);" (VInt 9))
                ]
            , TestList
                "returned references"
                [ testCase "a result that is a reference reads the place it is from" (runs "fn headOf(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ affirm *return = get(xs, 0); }] { return &get(xs, 0); }; ys = [10, 20, 30]; r = headOf(ys); return *r;" (VInt 10))
                , testCase "the one reference parameter is what the result is from, without saying so" (runs "fn headOf(xs: &List<Int>) -> &Int [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); }; ys = [10, 20]; r = headOf(ys); return *r;" (VInt 10))
                , testCase "a result may be from either of two parameters" (runs "fn choose(flag: Bool, a: &Int, b: &Int) -> &Int from (a, b) { if flag { return a; } else { return b; }; }; x = 1; y = 2; r = choose(true, x, y); return *r;" (VInt 1))
                , testCase "either candidate is frozen while the result is live" (rejected "fn choose(flag: Bool, a: &Int, b: &Int) -> &Int from (a, b) { if flag { return a; } else { return b; }; }; x = 1; y = 2; r = choose(false, x, y); x = 9; return *r;" "cannot be assigned while it is borrowed")
                , testCase "a returned reference goes through another function" (runs "fn headOf(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); }; fn again(ys: &List<Int>) -> &Int from ys [{ affirm size(ys) > 0; }] [{ }] { return headOf(ys); }; zs = [7, 8]; r = again(zs); return *r;" (VInt 7))
                , testCase "and through a generic one" (runs "fn headOf<T>(xs: &List<T>) -> &T from xs [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); }; ys = [10, 20]; r = headOf(ys); return *r;" (VInt 10))
                , testCase "what the caller proves of the result comes from the contract" (valid "fn headOf(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ affirm *return = get(xs, 0); }] { return &get(xs, 0); }; ys = [10, 20]; r = headOf(ys); affirm *r = 10; return 0;")
                , testCase "a reference to a local cannot be returned" (rejected "fn bad(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ }] { local = [99]; return &get(local, 0); }; ys = [10, 20, 30]; r = bad(ys); return *r;" "is not a reference from xs")
                , testCase "the place a result is from is frozen while it is live" (rejected "fn headOf(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); }; ys = [10, 20, 30]; r = headOf(ys); ys = [40, 50]; return *r;" "cannot be assigned while it is borrowed")
                , testCase "several reference parameters and no from is refused" (rejected "fn pick(a: &Int, b: &Int) -> &Int { return a; }; x = 1; y = 2; r = pick(x, y); return *r;" "say which the result is from")
                , testCase "an update reference can be returned" (runs "fn upd(n: &mut Int) -> &mut Int from n [{ }] [{ }] { return n; }; x = 1; r = upd(&mut x); *r = 7; return x;" (VInt 7))
                , testCase "the program cannot return a reference" (rejected "fn headOf(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); }; ys = [10, 20]; return headOf(ys);" "the program cannot return a reference")
                , testCase "a returned parameter is a reference to what the result says" (rejected "fn bad(x: &Bool) -> &Int from x { return x; }; b = true; r = bad(b); return *r;" "expected Int, got Bool")
                , testCase "every candidate of a returned call counts, not only the first" (rejected "fn choose(flag: Bool, a: &Int, b: &Int) -> &Int from (a, b) { if flag { return a; } else { return b; }; }; fn outer(xs: &Int) -> &Int from xs { local = 5; return choose(false, xs, &local); }; x = 1; r = outer(x); return *r;" "is not a reference from xs")
                , testCase "a result that may be from several places still freezes them all through another call" (rejected "fn choose(flag: Bool, a: &Int, b: &Int) -> &Int from (a, b) { if flag { return a; } else { return b; }; }; fn identity(v: &Int) -> &Int from v { return v; }; x = 1; y = 2; r = choose(false, x, y); s = identity(r); y = 9; return *s;" "cannot be assigned while it is borrowed")
                ]
            , TestList
                "reference fields"
                [ testCase "a struct can hold read references, and they are read where they point" (runs "struct Window { first: &Int, last: &Int }; xs = [10, 20, 30]; w = Window { first: &get(xs, 0), last: &get(xs, 2) }; f = w.first; l = w.last; return *f + *l;" (VInt 40))
                , testCase "in a generic struct too" (runs "struct Window<T> { first: &T, last: &T }; xs = [10, 20, 30]; w = Window<Int> { first: &get(xs, 0), last: &get(xs, 2) }; f = w.first; l = w.last; return *f + *l;" (VInt 40))
                , testCase "a struct of references is returned under a from bound" (runs "struct Window { first: &Int, last: &Int }; fn ends(xs: &List<Int>) -> Window from xs [{ affirm size(xs) > 0; }] [{ }] { return Window { first: &get(xs, 0), last: &get(xs, size(xs) - 1) }; }; ys = [10, 20, 30]; w = ends(ys); f = w.first; return *f;" (VInt 10))
                , testCase "the place a returned struct's fields are from is frozen while it is held" (rejected "struct Window { first: &Int, last: &Int }; fn ends(xs: &List<Int>) -> Window from xs [{ affirm size(xs) > 0; }] [{ }] { return Window { first: &get(xs, 0), last: &get(xs, size(xs) - 1) }; }; ys = [10, 20, 30]; w = ends(ys); ys = [40, 50]; f = w.first; return *f;" "cannot be assigned while it is borrowed")
                , testCase "every field of a returned struct has to be from a named parameter" (rejected "struct Window { first: &Int, last: &Int }; fn ends(xs: &List<Int>, other: &List<Int>) -> Window from xs [{ affirm size(xs) > 0; affirm size(other) > 0; }] [{ }] { return Window { first: &get(xs, 0), last: &get(other, 0) }; }; ys = [10, 20]; zs = [30, 40]; w = ends(ys, zs); f = w.first; return *f;" "is not a reference from xs")
                , testCase "a field read out of a moved holder still freezes its place" (rejected "struct Window { first: &Int, last: &Int }; xs = [10, 20, 30]; w = Window { first: &get(xs, 0), last: &get(xs, 2) }; w2 = w; f = w2.last; xs = [99]; return *f;" "cannot be assigned while it is borrowed")
                , testCase "a struct update keeps the fields it does not name" (runs "struct Window { first: &Int, last: &Int }; xs = [10, 20, 30]; w = Window { first: &get(xs, 0), last: &get(xs, 2) }; w2 = Window { first: &get(xs, 1), ..w }; f = w2.first; l = w2.last; return *f + *l;" (VInt 50))
                , testCase "an update reference can be a field" (runs "struct W { r: &mut Int }; x = 1; w = W { r: &mut x }; *w.r = 41; return x;" (VInt 41))
                , testCase "and is written through after the paths join" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; d = 0; if c > 0 { d = 1; } else { d = 2; }; p = w.r; *p = 41; q = *p; return q + d; }; return f(1);" (VInt 42))
                , testCase "a holder of a reference is followed across many branches" (runs ("struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn f(" ++ intercalate ", " ["p" ++ show k ++ ": Int" | k <- [0 .. 15 :: Int]] ++ ") -> Int { s = S { xs: [1, 2, 3], n: 4 }; w = W { r: &s.xs, ys: [7] }; " ++ concat ["if p" ++ show k ++ " > 0 { c" ++ show k ++ " = 1; } else { c" ++ show k ++ " = 2; }; " | k <- [0 .. 15 :: Int]] ++ "r = w.r; return size(*r); }; return f(" ++ intercalate ", " (replicate 16 "1") ++ ");") (VInt 3))
                , testCase "a struct can hold a value that holds references" (runs "struct Window { first: &Int, last: &Int }; struct Outer { w: Window, n: Int }; xs = [10, 20, 30]; w = Window { first: &get(xs, 0), last: &get(xs, 2) }; o = Outer { w: w, n: 1 }; f = o.w.first; return *f + o.n;" (VInt 11))
                , testCase "a value that holds references can be given to a function" (runs "struct Window { first: &Int, last: &Int }; fn total(w: Window) -> Int { f = w.first; return *f; }; xs = [10, 20, 30]; w = Window { first: &get(xs, 0), last: &get(xs, 2) }; return total(w);" (VInt 10))
                , testCase "and put in a list" (runs "struct Window { first: &Int, last: &Int }; xs = [10, 20, 30]; w = Window { first: &get(xs, 0), last: &get(xs, 2) }; ws = push([], w); w0 = get(ws, 0); f = w0.first; return *f + size(ws);" (VInt 11))
                , testCase "a holder of a shared reference is Clone" (runs "struct S { r: &Int }; impl Clone for S { }; x = 1; s = S { r: &x }; t = clone(s); return *t.r;" (VInt 1))
                , testCase "a cloned shared reference holder keeps its loan" (rejected "struct S { r: &Int }; impl Clone for S { }; x = 1; s = S { r: &x }; t = clone(s); x = 2; return *t.r;" "cannot be assigned while it is borrowed")
                , testCase "a holder cannot clone its update reference" (rejected "struct S { r: &mut Int }; impl Clone for S { }; x = 1; s = S { r: &mut x }; t = clone(s); return 0;" "lent")
                , testCase "a holder made in the function is returned from what its fields are from" (runs "struct S { r: &Int }; fn f(x: &Int) -> S from x { s = S { r: &x }; return s; }; x = 3; w = f(x); g = w.r; return *g;" (VInt 3))
                , testCase "an ordinary field is not an origin" (runs "struct S { r: &Int, n: Int }; fn f(x: &Int) -> S from x { n = 1; return S { r: &x, n: n }; }; x = 3; w = f(x); g = w.r; return *g + w.n;" (VInt 4))
                ]
            , TestList
                "update references read out of a value"
                [ testCase "two update references read out of one holder, each written while the other is live" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; p = w.r; *p = 41; *q = 42; return x; }; return f(1);" "Move error: in f: x is borrowed by q, so another update reference to it cannot be read out of w.r while that borrow is live: the borrow ends at the last use of q")
                , testCase "and after the paths join" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; d = 0; if c > 0 { d = 1; } else { d = 2; }; p = w.r; *p = 41; *q = 42; return d; }; return f(1);" "Move error: in f: x is borrowed by q, so another update reference to it cannot be read out of w.r while that borrow is live: the borrow ends at the last use of q")
                , testCase "the holder writes through its field while a reference read out of it is live" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; p = w.r; d = 0; *w.r = 7; *p = 41; return d; }; return f(1);" "Move error: in f: x is borrowed by p, so another update reference to it cannot be read out of w.r while that borrow is live: the borrow ends at the last use of p")
                , testCase "and after the paths join" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; p = w.r; d = 0; if c > 0 { d = 1; } else { d = 2; }; *w.r = 7; *p = 41; return d; }; return f(1);" "Move error: in f: x is borrowed by p, so another update reference to it cannot be read out of w.r while that borrow is live: the borrow ends at the last use of p")
                , testCase "two update references read out of one element of a list" (rejected "fn f(c: Int) -> Int { x = 1; rs = push([], &mut x); p = get(rs, 0); q = get(rs, 0); *p = 41; *q = 42; return x; }; return f(1);" "Move error: in f: x is borrowed by p, so another update reference to it cannot be read out of rs[0] while that borrow is live: the borrow ends at the last use of p")
                , testCase "two update references read out of one Box" (rejected "fn f(c: Int) -> Int { x = 1; b = Box::new(&mut x); p = Box::unbox(b); q = Box::unbox(b); *p = 41; *q = 42; return x; }; return f(1);" "Move error: in f: x is borrowed by p, so another update reference to it cannot be read out of b while that borrow is live: the borrow ends at the last use of p")
                , testCase "one update reference read out and used alone" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; p = w.r; *p = 41; return x; }; return f(1);" (VInt 41))
                , testCase "a second one read out after the first is dead" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; y = *q; p = w.r; *p = 41; return x + y; }; return f(1);" (VInt 42))
                , testCase "a reborrow of one read out is its child, not a second one" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; p = &mut *q; *p = 1; *q = 2; return x; }; return f(1);" (VInt 2))
                , testCase "nor is a holder made of that reborrow" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; w2 = W { r: &mut *q }; p = w2.r; *p = 1; *q = 2; return x; }; return f(1);" (VInt 2))
                ]
            , TestList
                "a reborrow suspends the reference it is made from"
                [ testCase "a reference is assigned through while its reborrow is live" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; *q = 2; *p = 1; return 0; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "or read through" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; y = *q; *p = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be read through q while that borrow is live: the borrow ends at the last use of p")
                , testCase "or lent to a call" (rejected "fn h(n: &Int) -> Int { return *n; }; fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; y = h(q); *p = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be read through q while that borrow is live: the borrow ends at the last use of p")
                , testCase "and after the paths join" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; d = 0; if c > 0 { d = 1; } else { d = 2; }; *q = 2; *p = 1; return d; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "and in a loop" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { *q = i; *p = 1; i = i + 1; }; return 0; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "and with the reborrow made in the loop" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { p = &mut *q; *q = i; *p = 1; i = i + 1; }; return 0; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "a reborrow read out of a holder suspends its parent too" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; q = &mut x; w = W { r: &mut *q }; p = w.r; *q = 2; *p = 1; return 0; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "and the parent cannot be read through either" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; q = &mut x; w = W { r: &mut *q }; p = w.r; y = *q; *p = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be read through q while that borrow is live: the borrow ends at the last use of p")
                , testCase "a reborrow of a reborrow suspends both" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; s = &mut *p; *p = 2; *s = 1; return 0; }; return f(1);" "Move error: in f: x is borrowed by s, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of s")
                , testCase "the first of them too" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; s = &mut *p; y = *q; *s = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by s, so it cannot be read through q while that borrow is live: the borrow ends at the last use of s")
                , testCase "a reborrow is used, then its parent" (runs "fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; *p = 1; *q = 2; return x; }; return f(1);" (VInt 2))
                , testCase "a chain of reborrows is used from the last back" (runs "fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; s = &mut *p; *s = 1; *p = 2; *q = 3; return x; }; return f(1);" (VInt 3))
                , testCase "a reborrow is read while its parent waits" (runs "fn f(c: Int) -> Int { x = 1; q = &mut x; p = &mut *q; *p = 2; y = *p; *q = 3; return x + y; }; return f(1);" (VInt 5))
                , testCase "reborrows of two fields are assigned through while their parent waits" (runs "struct P { a: Int, b: Int }; fn f(c: Int) -> Int { v = P { a: 1, b: 2 }; q = &mut v; p = &mut (*q).a; s = &mut (*q).b; *p = 3; *s = 4; return v.a + v.b; }; return f(1);" (VInt 7))
                , testCase "a holder assigns through its field twice" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; *w.r = 1; *w.r = 2; return x; }; return f(1);" (VInt 2))
                , testCase "a reference read out of a holder is assigned through, then another" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; *q = 42; p = w.r; *p = 41; return x; }; return f(1);" (VInt 41))
                , testCase "and out of a list" (runs "fn f(c: Int) -> Int { x = 1; rs = push([], &mut x); p = get(rs, 0); *p = 41; q = get(rs, 0); *q = 42; return x; }; return f(1);" (VInt 42))
                , testCase "and out of a Box" (runs "fn f(c: Int) -> Int { x = 1; b = Box::new(&mut x); p = Box::unbox(b); *p = 41; q = Box::unbox(b); *q = 42; return x; }; return f(1);" (VInt 42))
                , testCase "a holder that was moved assigns through its field twice" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; w2 = w; *w2.r = 1; *w2.r = 2; return x; }; return f(1);" (VInt 2))
                , testCase "and one held in another struct" (runs "struct W { r: &mut Int }; struct O { w: W }; fn f(c: Int) -> Int { x = 1; o = O { w: W { r: &mut x } }; *o.w.r = 1; *o.w.r = 2; return x; }; return f(1);" (VInt 2))
                , testCase "the holder assigns through its field after a reborrow of a reference read out of it" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; p = &mut *q; *p = 1; *q = 2; *w.r = 3; return x; }; return f(1);" (VInt 3))
                , testCase "a reborrow of a reference read out of a holder is assigned through twice" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; p = &mut *q; *p = 2; *p = 1; return x; }; return f(1);" (VInt 1))
                , testCase "references read out of two fields of a holder are assigned through together" (runs "struct V { a: &mut Int, b: &mut Int }; fn f(c: Int) -> Int { x = 1; y = 2; v = V { a: &mut x, b: &mut y }; p = v.a; q = v.b; *p = 3; *q = 4; return x + y; }; return f(1);" (VInt 7))
                ]
            , TestList
                "a reborrow of an update parameter, a read-out or a call result suspends it too"
                [ testCase "a reference read out of a holder is assigned through while its reborrow is live" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; p = &mut *q; *q = 2; *p = 1; return 0; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "or read through" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; p = &mut *q; y = *q; *p = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be read through q while that borrow is live: the borrow ends at the last use of p")
                , testCase "a field of one, through a reborrow of that field" (rejected "struct S { a: Int, b: Int }; struct WS { r: &mut S }; fn f(c: Int) -> Int { x = S { a: 1, b: 2 }; w = WS { r: &mut x }; q = w.r; p = &mut (*q).a; (*q).a = 3; *p = 5; return 0; }; return f(1);" "Move error: in f: x.a is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "a reference a call returned is assigned through while its reborrow is live" (rejected "fn idm(n: &mut Int) -> &mut Int from n [{ }] [{ }] { return &mut *n; }; fn f(c: Int) -> Int { x = 1; q = idm(&mut x); p = &mut *q; *q = 2; *p = 1; return 0; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "or read through" (rejected "fn idm(n: &mut Int) -> &mut Int from n [{ }] [{ }] { return &mut *n; }; fn f(c: Int) -> Int { x = 1; q = idm(&mut x); p = &mut *q; y = *q; *p = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be read through q while that borrow is live: the borrow ends at the last use of p")
                , testCase "an update parameter is assigned through while its reborrow is live" (rejected "fn g(n: &mut Int) -> Int [{ }] [{ }] { p = &mut *n; *n = 2; *p = 1; return 0; }; fn f(c: Int) -> Int { x = 1; return g(&mut x); }; return f(1);" "Move error: in g: n is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "a field of one, through a reborrow of that field" (rejected "struct P { a: Int, b: Int }; fn g(n: &mut P) -> Int [{ }] [{ }] { p = &mut (*n).a; (*n).a = 2; *p = 1; return 0; }; fn f(c: Int) -> Int { x = P { a: 1, b: 2 }; return g(&mut x); }; return f(1);" "Move error: in g: n.a is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "in a loop" (rejected "fn g(n: &mut Int) -> Int [{ }] [{ }] { p = &mut *n; i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { *n = i; *p = i; i = i + 1; }; return 0; }; fn f(c: Int) -> Int { x = 1; return g(&mut x); }; return f(1);" "Move error: in g: n is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "in one arm" (rejected "fn g(n: &mut Int, c: Bool) -> Int [{ }] [{ }] { p = &mut *n; if c { *n = 2; }; *p = 1; return 0; }; fn f(c: Int) -> Int { x = 1; return g(&mut x, true); }; return f(1);" "Move error: in g: n is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "an update parameter is read while its reborrow is live" (rejected "fn g(n: &mut Int) -> Int [{ }] [{ }] { p = &mut *n; y = *n; *p = 1; return y; }; fn f(c: Int) -> Int { x = 1; return g(&mut x); }; return f(1);" "Move error: in g: n is borrowed by p, so it cannot be read while that borrow is live: the borrow ends at the last use of p")
                , testCase "or lent to a call" (rejected "fn h(n: &Int) -> Int { return *n; }; fn g(n: &mut Int) -> Int [{ }] [{ }] { p = &mut *n; y = h(n); *p = 1; return y; }; fn f(c: Int) -> Int { x = 1; return g(&mut x); }; return f(1);" "Move error: in g: n is borrowed by p, so it cannot be read while that borrow is live: the borrow ends at the last use of p")
                , testCase "a reborrow of an update parameter is used, then the parameter" (runs "fn g(n: &mut Int) -> Int [{ }] [{ }] { p = &mut *n; *p = 1; *n = 2; return 0; }; fn f(c: Int) -> Int { x = 1; y = g(&mut x); return x + y; }; return f(1);" (VInt 2))
                , testCase "and read after" (runs "fn g(n: &mut Int) -> Int [{ }] [{ }] { p = &mut *n; *p = 1; y = *n; return y; }; fn f(c: Int) -> Int { x = 1; return g(&mut x); }; return f(1);" (VInt 1))
                , testCase "two reborrows of it one after the other" (runs "fn g(n: &mut Int) -> Int [{ }] [{ affirm *n = 2; }] { p = &mut *n; *p = 1; p2 = &mut *n; *p2 = 2; return 0; }; fn f(c: Int) -> Int { x = 1; y = g(&mut x); return x + y; }; return f(1);" (VInt 2))
                , testCase "a reborrow made in each iteration" (runs "fn g(n: &mut Int) -> Int [{ }] [{ }] { i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { p = &mut *n; *p = i; *n = i + 1; i = i + 1; }; return *n; }; fn f(c: Int) -> Int { x = 1; return g(&mut x); }; return f(1);" (VInt 3))
                , testCase "a chain of reborrows of it used from the last back" (runs "fn g(n: &mut Int) -> Int [{ }] [{ }] { p = &mut *n; s = &mut *p; *s = 1; *p = 2; *n = 3; return *n; }; fn f(c: Int) -> Int { x = 1; return g(&mut x); }; return f(1);" (VInt 3))
                , testCase "another field written while a reborrow of one is live" (runs "struct P { a: Int, b: Int }; fn g(n: &mut P) -> Int [{ }] [{ }] { p = &mut (*n).a; (*n).b = 2; *p = 1; return (*n).a; }; fn f(c: Int) -> Int { x = P { a: 1, b: 2 }; return g(&mut x); }; return f(1);" (VInt 1))
                , testCase "a reborrow of a reference read out of a holder is used, then read through the reference" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; q = w.r; p = &mut *q; *p = 4; y = *q; return y; }; return f(1);" (VInt 4))
                , testCase "another field of it written while a reborrow of one is live" (runs "struct S { a: Int, b: Int }; struct WS { r: &mut S }; fn f(c: Int) -> Int { x = S { a: 1, b: 2 }; w = WS { r: &mut x }; q = w.r; p = &mut (*q).a; (*q).b = 3; *p = 5; return (*q).a + (*q).b; }; return f(1);" (VInt 8))
                , testCase "a reborrow of a reference a call returned is used, then the reference" (runs "fn idm(n: &mut Int) -> &mut Int from n [{ }] [{ }] { return &mut *n; }; fn f(c: Int) -> Int { x = 1; q = idm(&mut x); p = &mut *q; *p = 1; *q = 2; y = *q; return y; }; return f(1);" (VInt 2))
                , testCase "a reborrow of a reference held in a field is to what that reference is to" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; p = &mut *w.r; *p = 5; return x; }; return f(1);" (VInt 5))
                , testCase "and a reborrow of a field of what it is to" (runs "struct S { a: Int, b: Int }; struct WS { r: &mut S }; fn f(c: Int) -> Int { x = S { a: 1, b: 2 }; w = WS { r: &mut x }; p = &mut (*w.r).a; *p = 5; return x.a + x.b; }; return f(1);" (VInt 7))
                , testCase "and of a reference held in a list" (runs "fn f(c: Int) -> Int { x = 1; rs = push([], &mut x); p = &mut *get(rs, 0); *p = 5; return x; }; return f(1);" (VInt 5))
                ]
            , TestList
                "a reference given something other than a borrow is written through as itself"
                [ testCase "a reference given a read-out after a borrow writes through the read-out" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; y = 1; w = W { r: &mut y }; p = &mut x; *p = 2; p = w.r; *p = 5; return x * 10 + y; }; return f(1);" (VInt 25))
                , testCase "in a loop" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; y = 1; w = W { r: &mut y }; p = &mut x; i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { *p = i + 2; p = w.r; i = i + 1; }; return x * 10 + y; }; return f(1);" (VInt 23))
                , testCase "in one branch" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; y = 1; w = W { r: &mut y }; p = &mut x; *p = 2; if c > 0 { p = w.r; } else { }; *p = 5; return x * 10 + y; }; return f(1) * 100 + f(0);" (VInt 2551))
                , testCase "a borrow made in one branch is not what it holds after the branches meet" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; y = 1; w = W { r: &mut y }; p = w.r; if c > 0 { p = &mut x; } else { }; *p = 5; return x * 10 + y; }; return f(1) * 100 + f(0);" (VInt 5115))
                , testCase "nor in the other branch" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; y = 1; w = W { r: &mut y }; p = w.r; if c > 0 { } else { p = &mut x; }; *p = 5; return x * 10 + y; }; return f(1) * 100 + f(0);" (VInt 1551))
                , testCase "a reborrow given a read-out after it was written through" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; y = 1; w = W { r: &mut y }; q = &mut x; p = &mut *q; *p = 2; p = w.r; *p = 5; return x * 10 + y; }; return f(1);" (VInt 25))
                ]
            , TestList
                "a reference read out of a list or an Uninit is to its place"
                [ testCase "out of a list in a struct" (runs "struct H { rs: List<&mut Int> }; fn f(c: Int) -> Int { x = 1; h = H { rs: push([], &mut x) }; p = get(h.rs, 0); *p = 41; return x; }; return f(1);" (VInt 41))
                , testCase "out of a list of lists" (runs "fn f(c: Int) -> Int { x = 1; rss = push([], push([], &mut x)); rs = get(rss, 0); p = get(rs, 0); *p = 41; return x; }; return f(1);" (VInt 41))
                , testCase "out of a list in a Box" (runs "fn f(c: Int) -> Int { x = 1; b = Box::new(push([], &mut x)); rs = Box::unbox(b); p = get(rs, 0); *p = 41; return x; }; return f(1);" (VInt 41))
                , testCase "out of a Box in a list" (runs "fn f(c: Int) -> Int { x = 1; bs = push([], Box::new(&mut x)); b = get(bs, 0); p = Box::unbox(b); *p = 41; return x; }; return f(1);" (VInt 41))
                , testCase "one that was set into the list" (runs "fn f(c: Int) -> Int { x = 1; y = 2; rs = push([], &mut x); rs = set(rs, 0, &mut y); p = get(rs, 0); *p = 41; return x * 100 + y; }; return f(1);" (VInt 141))
                , testCase "one of two in the list" (runs "fn f(c: Int) -> Int { x = 1; y = 2; rs = push(push([], &mut x), &mut y); p = get(rs, 1); *p = 41; q = get(rs, 0); *q = 40; return x + y; }; return f(1);" (VInt 81))
                , testCase "read, then written" (runs "fn f(c: Int) -> Int { x = 1; rs = push([], &mut x); p = get(rs, 0); y = *p; *p = y + 40; return x; }; return f(1);" (VInt 41))
                , testCase "to an element of a list" (runs "fn f(c: Int) -> Int { xs = [1, 2]; rs = push([], &mut get(xs, 1)); p = get(rs, 0); *p = 41; return get(xs, 1); }; return f(1);" (VInt 41))
                , testCase "to a field" (runs "struct P { a: Int, b: Int }; fn f(c: Int) -> Int { v = P { a: 1, b: 2 }; rs = push([], &mut v.b); p = get(rs, 0); *p = 41; return v.b; }; return f(1);" (VInt 41))
                , testCase "returned by a call" (runs "fn id(r: &mut Int) -> &mut Int from r { return r; }; fn f(c: Int) -> Int { x = 1; rs = push([], id(&mut x)); p = get(rs, 0); *p = 41; return x; }; return f(1);" (VInt 41))
                , testCase "to an update parameter" (runs "fn g(r: &mut Int) -> Int { rs = push([], &mut r); q = get(rs, 0); *q = 41; return 0; }; fn f(c: Int) -> Int { x = 1; y = g(&mut x); return x + y; }; return f(1);" (VInt 41))
                , testCase "in a function the list is lent to for updating" (runs "fn g(rs: &mut List<&mut Int>) -> Int [{ affirm size(*rs) > 0; }] [{ }] { q = get(*rs, 0); *q = 41; return 0; }; fn f(c: Int) -> Int { x = 1; rs = push([], &mut x); y = g(&mut rs); return x + y; }; return f(1);" (VInt 41))
                , testCase "in a loop" (runs "fn f(c: Int) -> Int { x = 1; rs = push([], &mut x); i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { p = get(rs, 0); *p = *p + 1; i = i + 1; }; return x; }; return f(1);" (VInt 4))
                , testCase "in one branch" (runs "fn f(c: Int) -> Int { x = 1; rs = push([], &mut x); if c > 0 { p = get(rs, 0); *p = 41; } else { }; return x; }; return f(1) * 100 + f(0);" (VInt 4101))
                , testCase "outside a function" (runs "x = 1; rs = push([], &mut x); p = get(rs, 0); *p = 41; return x;" (VInt 41))
                , testCase "taken out of an Uninit" (runs "fn f(c: Int) -> Int { x = 1; u = Uninit::new(&mut x); p = Uninit::take(u); *p = 41; return x; }; return f(1);" (VInt 41))
                , testCase "read out of an Uninit" (runs "fn f(c: Int) -> Int { x = 1; u = Uninit::new(&mut x); p = Uninit::get(u); *p = 41; return x; }; return f(1);" (VInt 41))
                ]
            , TestList
                "no other read while an update borrow is live"
                [ testCase "a shared borrow while a holder carries an update reference to the place" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; s = &x; y = *s; *w.r = 5; return y; }; return f(1);" "Move error: in f: x is borrowed by w, so it cannot be borrowed while that borrow is live: the borrow ends at the last use of w")
                , testCase "and when the holder's reference is read out of it after" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; s = &x; y = *s; p = w.r; *p = 5; return y; }; return f(1);" "Move error: in f: x is borrowed by w, so it cannot be borrowed while that borrow is live: the borrow ends at the last use of w")
                , testCase "and after the paths join" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; d = 0; if c > 0 { d = 1; } else { d = 2; }; s = &x; y = *s; *w.r = 5; return y + d; }; return f(1);" "Move error: in f: x is borrowed by w, so it cannot be borrowed while that borrow is live: the borrow ends at the last use of w")
                , testCase "and through a list" (rejected "fn f(c: Int) -> Int { x = 1; rs = push([], &mut x); s = &x; y = *s; p = get(rs, 0); *p = 5; return y; }; return f(1);" "Move error: in f: x is borrowed by rs, so it cannot be borrowed while that borrow is live: the borrow ends at the last use of rs")
                , testCase "and through a Box" (rejected "fn f(c: Int) -> Int { x = 1; b = Box::new(&mut x); s = &x; y = *s; p = Box::unbox(b); *p = 5; return y; }; return f(1);" "Move error: in f: x is borrowed by b, so it cannot be borrowed while that borrow is live: the borrow ends at the last use of b")
                , testCase "and through a holder held in another struct" (rejected "struct W { r: &mut Int }; struct O { w: W }; fn f(c: Int) -> Int { x = 1; o = O { w: W { r: &mut x } }; s = &x; y = *s; *o.w.r = 5; return y; }; return f(1);" "Move error: in f: x is borrowed by o, so it cannot be borrowed while that borrow is live: the borrow ends at the last use of o")
                , testCase "a shared borrow after the holder is dead" (runs "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; *w.r = 5; s = &x; return *s; }; return f(1);" (VInt 5))
                , testCase "a shared borrow alongside a holder of a shared reference" (runs "struct S { r: &Int }; fn f(c: Int) -> Int { x = 1; w = S { r: &x }; s = &x; y = *s; z = w.r; return y + *z; }; return f(1);" (VInt 2))
                , testCase "or alongside a holder of a shared reborrow of an update reference that is dead" (runs "struct S { r: &Int }; fn f(c: Int) -> Int { x = 1; q = &mut x; w = S { r: &*q }; s = &x; y = *s; z = w.r; return y + *z; }; return f(1);" (VInt 2))
                , testCase "a shared borrow of another field than the holder's" (runs "struct W { r: &mut Int }; struct V { a: Int, b: Int }; fn f(c: Int) -> Int { v = V { a: 1, b: 2 }; w = W { r: &mut v.a }; s = &v.b; y = *s; *w.r = 5; return y; }; return f(1);" (VInt 2))
                , testCase "the owner is read while an update borrow of it is live" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; y = x; *q = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by q, so it cannot be read while that borrow is live: the borrow ends at the last use of q")
                , testCase "and while a holder carries one" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; y = x; *w.r = 5; return y; }; return f(1);" "Move error: in f: x is borrowed by w, so it cannot be read while that borrow is live: the borrow ends at the last use of w")
                , testCase "a field is read while it is borrowed for updating" (rejected "struct V { a: Int, b: Int }; fn f(c: Int) -> Int { v = V { a: 1, b: 2 }; p = &mut v.a; y = v.a; *p = 3; return y; }; return f(1);" "Move error: in f: v.a is borrowed by p, so it cannot be read while that borrow is live: the borrow ends at the last use of p")
                , testCase "and an element of a list" (rejected "fn f(c: Int) -> Int { xs = [1, 2]; p = &mut get(xs, 0); y = get(xs, 0); *p = 3; return y; }; return f(1);" "Move error: in f: xs[0] is borrowed by p, so it cannot be read while that borrow is live: the borrow ends at the last use of p")
                , testCase "the owner is read in an arm" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; y = 0; if c > 0 { y = x; } else { y = 2; }; *q = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by q, so it cannot be read while that borrow is live: the borrow ends at the last use of q")
                , testCase "in a loop" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; y = 0; i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { y = y + x; *q = i; i = i + 1; }; return y; }; return f(1);" "Move error: in f: x is borrowed by q, so it cannot be read while that borrow is live: the borrow ends at the last use of q")
                , testCase "given to a call" (rejected "fn h(n: &Int) -> Int { return *n; }; fn f(c: Int) -> Int { x = 1; q = &mut x; y = h(x); *q = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by q, so it cannot be read while that borrow is live: the borrow ends at the last use of q")
                , testCase "or tested" (rejected "fn f(c: Int) -> Int { x = 1; q = &mut x; y = 0; if x > 0 { y = 1; } else { y = 2; }; *q = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by q, so it cannot be read while that borrow is live: the borrow ends at the last use of q")
                , testCase "a field is read through a reference while a reborrow of that field is live" (rejected "struct V { a: Int, b: Int }; fn f(c: Int) -> Int { v = V { a: 1, b: 2 }; q = &mut v; p = &mut (*q).a; y = (*q).a; *p = 3; return y; }; return f(1);" "Move error: in f: v.a is borrowed by p, so it cannot be read through q while that borrow is live: the borrow ends at the last use of p")
                , testCase "the owner is read after the update borrow is dead" (runs "fn f(c: Int) -> Int { x = 1; q = &mut x; *q = 1; y = x; return y; }; return f(1);" (VInt 1))
                , testCase "the owner is read alongside a shared borrow" (runs "fn f(c: Int) -> Int { x = 1; s = &x; y = x; return y + *s; }; return f(1);" (VInt 2))
                , testCase "another field is read while one is borrowed for updating" (runs "struct V { a: Int, b: Int }; fn f(c: Int) -> Int { v = V { a: 1, b: 2 }; p = &mut v.a; y = v.b; *p = 3; return y; }; return f(1);" (VInt 2))
                , testCase "another element at a known index" (runs "fn f(c: Int) -> Int { xs = [1, 2]; p = &mut get(xs, 0); y = get(xs, 1); *p = 3; return y; }; return f(1);" (VInt 2))
                , testCase "the size of a list while an element is borrowed for updating" (runs "fn f(c: Int) -> Int { xs = [1, 2]; p = &mut get(xs, 0); n = size(xs); *p = 3; return n; }; return f(1);" (VInt 2))
                , testCase "another field is read through the reference while a reborrow of one is live" (runs "struct V { a: Int, b: Int }; fn f(c: Int) -> Int { v = V { a: 1, b: 2 }; q = &mut v; p = &mut (*q).a; y = (*q).b; *p = 3; return y; }; return f(1);" (VInt 2))
                , testCase "a reborrow is read through itself" (runs "struct V { a: Int, b: Int }; fn f(c: Int) -> Int { v = V { a: 1, b: 2 }; q = &mut v; p = &mut (*q).a; *p = 3; y = *p; return y; }; return f(1);" (VInt 3))
                ]
            , TestList
                "a call's other arguments while one is lent for updating"
                [ testCase "a field lent for updating and read by another argument" (rejected "struct S { xs: List<Int>, n: Int }; fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; s = S { xs: [1, 2, 3], n: 5 }; return f(&mut s.xs, s.xs);" "Move error: in main: s.xs is lent to this call and lent to it for updating too: write clone(s.xs) for the one that is read")
                , testCase "the whole lent for updating and a field read by another argument" (rejected "struct S { xs: List<Int>, n: Int }; fn fs(a: &mut S, b: &List<Int>) -> Int writes(a) { return size(b); }; s = S { xs: [1, 2, 3], n: 5 }; return fs(&mut s, s.xs);" "Move error: in main: s.xs is lent to this call, and s is lent to it for updating: write clone(s.xs) for the one that is read")
                , testCase "a field lent for updating and the whole read by another argument" (rejected "struct S { xs: List<Int>, n: Int }; fn fw(a: &mut List<Int>, b: &S) -> Int writes(a) { return b.n; }; s = S { xs: [1, 2, 3], n: 5 }; return fw(&mut s.xs, s);" "Move error: in main: s is lent to this call, and s.xs is lent to it for updating: write clone(s) for the one that is read")
                , testCase "a whole Copy variable lent for updating and read by another argument" (rejected "fn fn2(a: &mut Int, b: &Int) -> Int writes(a) { *a = 9; return b; }; n = 5; return fn2(&mut n, n);" "Move error: in main: n is lent to this call and lent to it for updating too: write clone(n) for the one that is read")
                , testCase "a field lent for updating and borrowed by another argument" (rejected "struct S { xs: List<Int>, n: Int }; fn fr(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { return size(b); }; s = S { xs: [1, 2, 3], n: 5 }; return fr(&mut s.xs, &s.xs);" "Move error: in main: s.xs is borrowed by the value in _2, so it cannot be borrowed while that borrow is live: the borrow ends at the last use of the value in _2")
                , testCase "a Copy field lent for updating and borrowed by another argument" (rejected "struct S { xs: List<Int>, n: Int }; fn fi(a: &mut Int, b: &Int) -> Int writes(a) { *a = 9; return b; }; s = S { xs: [1, 2, 3], n: 5 }; return fi(&mut s.n, &s.n);" "Move error: in main: s.n is borrowed by the value in _2, so it cannot be borrowed while that borrow is live: the borrow ends at the last use of the value in _2")
                , testCase "a field lent for updating and moved by another argument" (rejected "struct S { xs: List<Int>, n: Int }; fn fm(a: &mut List<Int>, b: List<Int>) -> Int writes(a) { return size(b); }; s = S { xs: [1, 2, 3], n: 5 }; return fm(&mut s.xs, s.xs);" "Move error: in main: s.xs is lent to this call and moved by it too: write clone(s.xs) for one of them")
                , testCase "a field lent for updating and its size taken by another argument" (rejected "struct S { xs: List<Int>, n: Int }; fn fv(a: &mut List<Int>, b: Int) -> Int writes(a) { return b; }; s = S { xs: [1, 2, 3], n: 5 }; return fv(&mut s.xs, size(s.xs));" "Move error: in main: s.xs is borrowed by the value in _2, so it cannot be read while that borrow is live: the borrow ends at the last use of the value in _2")
                , testCase "a Copy field lent for updating and read inside another argument" (rejected "struct S { xs: List<Int>, n: Int }; fn fi(a: &mut Int, b: &Int) -> Int writes(a) { *a = 9; return b; }; s = S { xs: [1, 2, 3], n: 5 }; return fi(&mut s.n, s.n + 1);" "Move error: in main: s.n is borrowed by the value in _2, so it cannot be read while that borrow is live: the borrow ends at the last use of the value in _2")
                , testCase "a Copy field lent for updating and read into another argument" (runs "struct S { xs: List<Int>, n: Int }; fn fi(a: &mut Int, b: &Int) -> Int writes(a) { *a = 9; return b; }; s = S { xs: [1, 2, 3], n: 5 }; return fi(&mut s.n, s.n) * 10 + s.n;" (VInt 59))
                , testCase "a Copy element lent for updating and read into another argument" (runs "fn fi(a: &mut Int, b: &Int) -> Int writes(a) { *a = 9; return b; }; xs = [1, 2]; return fi(&mut get(xs, 0), get(xs, 0)) * 10 + get(xs, 0);" (VInt 19))
                ]
            , TestList
                "a reborrow given to a call ends when the call returns"
                [ testCase "a reference is assigned through after a reborrow of it is given to a call" (runs "fn h(n: &mut Int) -> Int writes(n) { *n = *n + 1; return 0; }; fn f(c: Int) -> Int { x = 1; q = &mut x; n = h(&mut *q); *q = 5; return n + x; }; return f(1);" (VInt 5))
                , testCase "or read through" (runs "fn h(n: &mut Int) -> Int writes(n) { *n = *n + 1; return 0; }; fn f(c: Int) -> Int { x = 1; q = &mut x; n = h(&mut *q); y = *q; return n + y; }; return f(1);" (VInt 2))
                , testCase "or reborrowed for another call" (runs "fn h(n: &mut Int) -> Int writes(n) { *n = *n + 1; return 0; }; fn f(c: Int) -> Int { x = 1; q = &mut x; n = h(&mut *q); m = h(&mut *q); *q = *q + 10; return n + m + x; }; return f(1);" (VInt 13))
                , testCase "or given to calls that read it" (runs "fn h(n: &mut Int) -> Int writes(n) { *n = *n + 1; return 0; }; fn g2(n: &Int) -> Int { return *n; }; fn f(c: Int) -> Int { x = 1; q = &mut x; n = h(&mut *q); y = g2(q); z = g2(&*q); return n + y + z; }; return f(1);" (VInt 4))
                , testCase "a reborrow of a field is given to a call, then the parent writes another" (runs "struct V { a: Int, b: Int }; fn hf(n: &mut Int) -> Int writes(n) { *n = 7; return 0; }; fn f(c: Int) -> Int { v = V { a: 1, b: 2 }; q = &mut v; n = hf(&mut (*q).a); (*q).b = 3; return n + v.a + v.b; }; return f(1);" (VInt 10))
                , testCase "a reborrow of a reference read out of a holder is given to a call, then the holder writes" (runs "struct W { r: &mut Int }; fn h(n: &mut Int) -> Int writes(n) { *n = *n + 1; return 0; }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; n = h(&mut *w.r); *w.r = 5; return n + x; }; return f(1);" (VInt 5))
                , testCase "and in a loop" (runs "fn h(n: &mut Int) -> Int writes(n) { *n = *n + 1; return 0; }; fn f(c: Int) -> Int { x = 1; q = &mut x; i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { n = h(&mut *q); *q = *q + 1; i = i + 1; }; return x; }; return f(1);" (VInt 7))
                , testCase "and after the paths join" (runs "fn h(n: &mut Int) -> Int writes(n) { *n = *n + 1; return 0; }; fn f(c: Int) -> Int { x = 1; q = &mut x; n = 0; if c > 0 { n = h(&mut *q); } else { n = 1; }; *q = *q + 1; return n + x; }; return f(1);" (VInt 3))
                , testCase "a result from another argument keeps only that argument" (runs "fn pick(a: &mut Int, b: &Int) -> &Int from b { *a = 4; return b; }; fn f(c: Int) -> Int { x = 1; y = 3; q = &mut x; r = pick(&mut *q, &y); *q = 2; return *r + x; }; return f(1);" (VInt 5))
                , testCase "a result from the reborrow is used, then the reference" (runs "fn idm(n: &mut Int) -> &mut Int from n { return &mut *n; }; fn f(c: Int) -> Int { x = 1; q = &mut x; p = idm(&mut *q); *p = 7; *q = *q + 1; return x; }; return f(1);" (VInt 8))
                , testCase "and a holder the call returns" (runs "struct W { r: &mut Int }; fn wrap(n: &mut Int) -> W from n { return W { r: &mut *n }; }; fn f(c: Int) -> Int { x = 1; q = &mut x; w = wrap(&mut *q); *w.r = 7; *q = *q + 1; return x; }; return f(1);" (VInt 8))
                , testCase "a result from the reborrow is live while the reference is assigned through" (rejected "fn idm(n: &mut Int) -> &mut Int from n { return &mut *n; }; fn f(c: Int) -> Int { x = 1; q = &mut x; p = idm(&mut *q); *q = 2; *p = 1; return x; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of p")
                , testCase "or read through" (rejected "fn idm(n: &mut Int) -> &mut Int from n { return &mut *n; }; fn f(c: Int) -> Int { x = 1; q = &mut x; p = idm(&mut *q); y = *q; *p = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be read through q while that borrow is live: the borrow ends at the last use of p")
                , testCase "or given to a call that reads it" (rejected "fn idm(n: &mut Int) -> &mut Int from n { return &mut *n; }; fn g2(n: &Int) -> Int { return *n; }; fn f(c: Int) -> Int { x = 1; q = &mut x; p = idm(&mut *q); y = g2(q); *p = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be read through q while that borrow is live: the borrow ends at the last use of p")
                , testCase "or reborrowed" (rejected "fn idm(n: &mut Int) -> &mut Int from n { return &mut *n; }; fn h(n: &mut Int) -> Int writes(n) { *n = *n + 1; return 0; }; fn f(c: Int) -> Int { x = 1; q = &mut x; p = idm(&mut *q); n = h(&mut *q); *p = 1; return n; }; return f(1);" "Move error: in f: x is borrowed by p, so it cannot be borrowed for updating while that borrow is live: the borrow ends at the last use of p")
                , testCase "a holder the call made of the reborrow is live while the reference is assigned through" (rejected "struct W { r: &mut Int }; fn wrap(n: &mut Int) -> W from n { return W { r: &mut *n }; }; fn f(c: Int) -> Int { x = 1; q = &mut x; w = wrap(&mut *q); *q = 2; *w.r = 1; return x; }; return f(1);" "Move error: in f: x is borrowed by w, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of w")
                , testCase "or read through" (rejected "struct W { r: &mut Int }; fn wrap(n: &mut Int) -> W from n { return W { r: &mut *n }; }; fn f(c: Int) -> Int { x = 1; q = &mut x; w = wrap(&mut *q); y = *q; *w.r = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by w, so it cannot be read through q while that borrow is live: the borrow ends at the last use of w")
                , testCase "or reborrowed" (rejected "struct W { r: &mut Int }; fn wrap(n: &mut Int) -> W from n { return W { r: &mut *n }; }; fn h(n: &mut Int) -> Int writes(n) { *n = *n + 1; return 0; }; fn f(c: Int) -> Int { x = 1; q = &mut x; w = wrap(&mut *q); n = h(&mut *q); *w.r = 1; return n; }; return f(1);" "Move error: in f: x is borrowed by w, so it cannot be borrowed for updating while that borrow is live: the borrow ends at the last use of w")
                , testCase "a holder made of a reborrow is live while the reference is read through" (rejected "struct W { r: &mut Int }; fn f(c: Int) -> Int { x = 1; q = &mut x; w = W { r: &mut *q }; y = *q; *w.r = 1; return y; }; return f(1);" "Move error: in f: x is borrowed by w, so it cannot be read through q while that borrow is live: the borrow ends at the last use of w")
                , testCase "a call stores the reborrow into a holder it is lent, which is live while the reference is assigned through" (rejected "struct W { r: &mut Int }; struct WS { r: &Int }; struct H { r: &mut Int }; struct V { a: Int, b: Int }; fn idm(r: &mut Int) -> &mut Int from r { return &mut *r; }; fn wrap(r: &mut Int) -> W from r { return W { r: &mut *r }; }; fn g(r: &mut Int) -> Int { *r = *r + 1; return 0; }; fn g2(a: &mut Int, b: &mut Int) -> Int { *a = 1; *b = 2; return 0; }; fn gv(a: &mut Int, k: Int) -> Int { *a = k; return k; }; fn rd(a: &Int) -> Int { return *a; }; fn put(h: &mut H, r: &mut Int) -> Int { *h = H { r: &mut *r }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; q = &mut x; h = H { r: &mut y }; k = put(&mut h, &mut *q); *q = 2; *h.r = 1; return x; }; return f(1);" "Move error: in f: x is borrowed by h, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of h")
                , testCase "or read through" (rejected "struct H { r: &mut Int }; fn put(h: &mut H, r: &mut Int) -> Int { *h = H { r: &mut *r }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; q = &mut x; h = H { r: &mut y }; k = put(&mut h, &mut *q); z = *q; *h.r = 7; return z * 10 + x; }; return f(1);" "Move error: in f: x is borrowed by h, so it cannot be read through q while that borrow is live: the borrow ends at the last use of h")
                , testCase "and a reborrow of a list" (rejected "struct HL { r: &mut List<Int> }; fn put(h: &mut HL, r: &mut List<Int>) -> Int { *h = HL { r: &mut *r }; return 0; }; fn f(c: Int) -> Int { x = [1]; y = [0]; q = &mut x; h = HL { r: &mut y }; k = put(&mut h, &mut *q); *q = [2, 3]; *h.r = [4]; return size(x); }; return f(1);" "Move error: in f: x is borrowed by h, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of h")
                , testCase "and a shared reborrow" (rejected "struct H { r: &mut Int }; struct N { h: H }; struct L { rs: List<&mut Int> }; struct B { b: Box<&mut Int> }; struct HS { r: &Int }; struct NS { h: HS }; struct LS { rs: List<&Int> }; struct BS { b: Box<&Int> }; struct HB { r: &mut Bool }; struct HSB { r: &Bool }; fn put(h: &mut HS, r: &Int) -> Int { *h = HS { r: &r }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; v = 0; q = &mut x; h = HS { r: &y }; k = put(&mut h, &*q); *q = 2; z = h.r; t = *z; return x; }; return f(1);" "Move error: in f: x is borrowed by h, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of h")
                , testCase "a call stores a reborrow of a field of the reborrow, then the field is assigned through the reference" (rejected "struct W { r: &mut Int }; struct V { a: Int, b: Int }; fn put(h: &mut W, r: &mut V) -> Int { *h = W { r: &mut (*r).a }; return 0; }; fn f(c: Int) -> Int { v = V { a: 1, b: 2 }; y = 0; q = &mut v; h = W { r: &mut y }; k = put(&mut h, &mut *q); (*q).a = 2; *h.r = 1; return v.a; }; return f(1);" "Move error: in f: v.a is borrowed by h, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of h")
                , testCase "or read through it" (rejected "struct W { r: &mut Int }; struct V { a: Int, b: Int }; fn put(h: &mut W, r: &mut V) -> Int { *h = W { r: &mut (*r).a }; return 0; }; fn f(c: Int) -> Int { v = V { a: 1, b: 2 }; y = 0; q = &mut v; h = W { r: &mut y }; k = put(&mut h, &mut *q); z = (*q).a; *h.r = 7; return z * 10 + v.a; }; return f(1);" "Move error: in f: v is borrowed by h, so it cannot be read through q while that borrow is live: the borrow ends at the last use of h")
                , testCase "a call stores a reborrow of what a reference in the reborrow is to" (rejected "struct W { r: &mut Int }; struct V2 { r2: &mut Int }; fn put(h: &mut W, r: &mut V2) -> Int { *h = W { r: &mut *(*r).r2 }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; v2 = V2 { r2: &mut x }; q = &mut v2; h = W { r: &mut y }; k = put(&mut h, &mut *q); *(*q).r2 = 2; *h.r = 1; return x; }; return f(1);" "Move error: in f: v2 is borrowed by h, so it cannot be read through q while that borrow is live: the borrow ends at the last use of h")
                , testCase "the holder is dead before the reference is used" (runs "struct H { r: &mut Int }; struct N { h: H }; struct L { rs: List<&mut Int> }; struct B { b: Box<&mut Int> }; struct HS { r: &Int }; struct NS { h: HS }; struct LS { rs: List<&Int> }; struct BS { b: Box<&Int> }; struct HB { r: &mut Bool }; struct HSB { r: &Bool }; fn put(h: &mut H, r: &mut Int) -> Int { *h = H { r: &mut *r }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; v = 0; q = &mut x; h = H { r: &mut y }; k = put(&mut h, &mut *q); *h.r = 1; *q = 2; return x; }; return f(1);" (VInt 2))
                , testCase "a holder lent for updating is tied to the reborrow whatever its slots" (rejected "struct H { r: &mut Int }; struct N { h: H }; struct L { rs: List<&mut Int> }; struct B { b: Box<&mut Int> }; struct HS { r: &Int }; struct NS { h: HS }; struct LS { rs: List<&Int> }; struct BS { b: Box<&Int> }; struct HB { r: &mut Bool }; struct HSB { r: &Bool }; fn put(h: &mut HB, r: &mut Int) -> Int { return 0; }; fn f(c: Int) -> Int { x = 1; b = true; q = &mut x; h = HB { r: &mut b }; k = put(&mut h, &mut *q); *q = 2; *h.r = false; return x; }; return f(1);" "Move error: in f: x is borrowed by h, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of h")
                , testCase "and to a shared reborrow" (rejected "struct H { r: &mut Int }; struct N { h: H }; struct L { rs: List<&mut Int> }; struct B { b: Box<&mut Int> }; struct HS { r: &Int }; struct NS { h: HS }; struct LS { rs: List<&Int> }; struct BS { b: Box<&Int> }; struct HB { r: &mut Bool }; struct HSB { r: &Bool }; fn put(h: &mut HSB, r: &Int) -> Int { return 0; }; fn f(c: Int) -> Int { x = 1; b = true; q = &mut x; h = HSB { r: &b }; k = put(&mut h, &*q); *q = 2; z = h.r; t = *z; return x; }; return f(1);" "Move error: in f: x is borrowed by h, so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of h")
                ]
            , TestList
                "a call may store any reference it is given into a holder it reaches"
                [ testCase "a borrow is stored into a holder lent for updating, which is live while the borrowed place is read" (rejected (holder ++ "fn f(c: Int) -> Int { x = 1; y = 0; h = H { r: &mut y }; k = put(&mut h, &mut x); v = x; *h.r = 7; return v * 10 + x; }; return f(1);") "Move error: in f: x is borrowed by h, so it cannot be read while that borrow is live: the borrow ends at the last use of h")
                , testCase "the holder is either place the update argument may be" (rejected (holder ++ "fn f(c: Bool) -> Int { x = 1; y = 0; y2 = 0; h1 = H { r: &mut y }; h2 = H { r: &mut y2 }; r = if c { &mut h1 } else { &mut h2 }; k = put(&mut *r, &mut x); v = x; *h1.r = 7; return v * 10 + x; }; return f(true);") "Move error: in f: x is borrowed by h1, so it cannot be read while that borrow is live: the borrow ends at the last use of h1")
                , testCase "or the other" (rejected (holder ++ "fn f(c: Bool) -> Int { x = 1; y = 0; y2 = 0; h1 = H { r: &mut y }; h2 = H { r: &mut y2 }; r = if c { &mut h1 } else { &mut h2 }; k = put(&mut *r, &mut x); v = x; *h2.r = 7; return v * 10 + x; }; return f(false);") "Move error: in f: x is borrowed by h2, so it cannot be read while that borrow is live: the borrow ends at the last use of h2")
                , testCase "a holder reached through a reference that an update argument holds" (rejected "struct H { r: &mut Int }; struct Wr { c: &mut H, n: Int }; fn put(w: &mut Wr, r: &mut Int) -> Int { p = (*w).c; *p = H { r: &mut *r }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; h = H { r: &mut y }; w = Wr { c: &mut h, n: 0 }; k = put(&mut w, &mut x); v = x; *h.r = 7; return v * 10 + x; }; return f(1);" "Move error: in f: x is borrowed by h, so it cannot be read while that borrow is live: the borrow ends at the last use of h")
                , testCase "or that an argument given by value holds" (rejected "struct H { r: &mut Int }; struct Wb { c: &mut H }; fn put(w: Wb, r: &mut Int) -> Int { *w.c = H { r: &mut *r }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; h = H { r: &mut y }; k = put(Wb { c: &mut h }, &mut x); v = x; *h.r = 7; return v * 10 + x; }; return f(1);" "Move error: in f: x is borrowed by h, so it cannot be read while that borrow is live: the borrow ends at the last use of h")
                , testCase "and is tied to the other references that argument holds" (rejected "struct H { r: &mut Int }; struct W2 { c: &mut H, d: &mut Int }; fn put(w: W2) -> Int { *w.c = H { r: &mut *w.d }; return 0; }; fn f(c: Int) -> Int { z = 1; y = 0; h = H { r: &mut y }; k = put(W2 { c: &mut h, d: &mut z }); v = z; *h.r = 7; return v * 10 + z; }; return f(1);" "Move error: in f: z is borrowed by h, so it cannot be read while that borrow is live: the borrow ends at the last use of h")
                , testCase "a generic call stores a borrow into a holder of a reference type" (rejected "struct Holder<T> { v: T, n: Int }; fn put<T>(c: &mut Holder<T>, x: T) -> Int { (*c).v = x; return 0; }; fn f(k: Int) -> Int { x = 1; y = 0; c = Holder<&mut Int> { v: &mut y, n: 0 }; z = put(&mut c, &mut x); x = 2; p = c.v; *p = 7; return x; }; return f(1);" "Move error: in f: x cannot be assigned while it is borrowed by c: the borrow ends at the last use of c")
                , testCase "or a shared borrow" (rejected "struct Holder<T> { v: T, n: Int }; fn put<T>(c: &mut Holder<T>, x: T) -> Int { (*c).v = x; return 0; }; fn f(k: Int) -> Int { y = 1; c = Holder<&Int> { v: &y, n: 0 }; z = 2; n = put(&mut c, &z); z = 3; q = c.v; return *q; }; return f(0);" "Move error: in f: z cannot be assigned while it is borrowed by c: the borrow ends at the last use of c")
                , testCase "and a generic method stores it into its receiver" (rejected "struct Bag<U> { n: Int, last: List<U> }; impl<U> Bag<U> { fn put(self: &mut Self, u: U) -> Int { (*self).last = push([], u); return 0; }; }; fn f(k: Int) -> Int { x = 1; b = Bag<&Int> { n: 0, last: [] }; z = Bag::put(&mut b, &x); x = 2; t = 0; if size(b.last) > 0 { q = get(b.last, 0); t = *q; } else { }; return t + x; }; return f(1);" "Move error: in f: x cannot be assigned while it is borrowed by b: the borrow ends at the last use of b")
                , testCase "the holder is dead before the borrowed place is used" (checks (holder ++ "fn f(c: Int) -> Int { x = 1; y = 0; h = H { r: &mut y }; k = put(&mut h, &mut x); *h.r = 7; return x; }; return f(1);") 7)
                , testCase "and when it is reached through an update argument" (checks "struct H { r: &mut Int }; struct Wr { c: &mut H, n: Int }; fn put(w: &mut Wr, r: &mut Int) -> Int { p = (*w).c; *p = H { r: &mut *r }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; h = H { r: &mut y }; w = Wr { c: &mut h, n: 0 }; k = put(&mut w, &mut x); *h.r = 7; return x; }; return f(1);" 7)
                , testCase "or through an argument given by value" (checks "struct H { r: &mut Int }; struct Wb { c: &mut H }; fn put(w: Wb, r: &mut Int) -> Int { *w.c = H { r: &mut *r }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; h = H { r: &mut y }; k = put(Wb { c: &mut h }, &mut x); *h.r = 7; return x; }; return f(1);" 7)
                , testCase "a holder lent as a part of a local is that local, read after the call" (checks "struct HS { r: &Int }; struct NS { h: HS, n: Int }; fn put(h: &mut HS, r: &Int) -> Int { *h = HS { r: &r }; return 0; }; fn f(c: Int) -> Int { x = 2; y = 1; m = NS { h: HS { r: &y }, n: 3 }; k = put(&mut m.h, &x); z = m.h.r; return *z; }; return f(1);" 2)
                , testCase "a holder reached through a lent argument is not tied" (checks "struct H { r: &mut Int }; struct Wb { c: &mut H }; fn rd(w: &Wb, x: &mut Int) -> Int { return *x; }; fn f(c: Int) -> Int { x = 1; y = 0; h = H { r: &mut y }; w = Wb { c: &mut h }; k = rd(w, &mut x); v = x; *h.r = 1; return v * 10 + y; }; return f(1);" 11)
                , testCase "a holder that is stored into can be moved" (checks (holder ++ "fn f(c: Int) -> Int { x = 1; y = 0; h = H { r: &mut y }; k = put(&mut h, &mut x); g = h; *g.r = 4; return x; }; return f(1);") 4)
                , testCase "and so can one reached through an argument given by value" (checks "struct H { r: &mut Int }; struct Wb { c: &mut H }; fn put(w: Wb, r: &mut Int) -> Int { *w.c = H { r: &mut *r }; return 0; }; fn f(c: Int) -> Int { x = 1; y = 0; h = H { r: &mut y }; k = put(Wb { c: &mut h }, &mut x); g = h; *g.r = 4; return x; }; return f(1);" 4)
                , testCase "a value with a function in it holds no reference" (checks "fn dbl(n: Int) -> Int { return n * 2; }; struct Acc { f: fn(Int) -> Int, total: Int }; fn add(a: &mut Acc, x: &mut Int) -> Int { (*a).total = (*a).total + *x; return 0; }; fn f(k: Int) -> Int { y = 3; a = Acc { f: dbl, total: 1 }; n = add(&mut a, &mut y); v = y; n2 = add(&mut a, &mut y); return a.total + 0 * v; }; return f(0);" 7)
                , testCase "so the borrow it is updated with can end" (checks "fn dbl(n: Int) -> Int { return n * 2; }; struct Acc { f: fn(Int) -> Int, total: Int }; fn add(a: &mut Acc, x: &Int) -> Int { (*a).total = (*a).total + *x; return 0; }; fn f(k: Int) -> Int { y = 3; a = Acc { f: dbl, total: 1 }; n = add(&mut a, &y); y = 4; n2 = add(&mut a, &y); return a.total; }; return f(0);" 8)
                , testCase "a holder of a type that holds no reference is not tied" (checks "struct Holder<T> { v: T, n: Int }; fn bump<T>(c: &mut Holder<T>, x: &Int) -> Int { (*c).n = (*c).n + *x; return 0; }; fn f(k: Int) -> Int { y = 3; c = Holder<Int> { v: 0, n: 1 }; n = bump(&mut c, &y); y = 5; return c.n; }; return f(0);" 4)
                , testCase "nor is a holder of a type parameter in its own generic body" (checks "struct Holder<T> { v: T, n: Int }; fn bump<T>(c: &mut Holder<T>, x: &Int) -> Int { (*c).n = (*c).n + *x; return 0; }; fn twice<T>(c: &mut Holder<T>) -> Int { y = 1; n = bump(&mut *c, &y); y = 2; n2 = bump(&mut *c, &y); return (*c).n; }; fn f(k: Int) -> Int { c = Holder<Int> { v: 0, n: 1 }; return twice(&mut c); }; return f(0);" 4)
                , testCase "a holder of a type with no declaration may hold a reference" undeclaredHolder
                ]
            , TestList
                "the rest of the plan"
                [ testCase "an update reference can be returned" (runs "fn f(x: &mut Int) -> &mut Int from x { return x; }; a = 1; r = f(&mut a); *r = 9; return a;" (VInt 9))
                , testCase "and made through the parameter" (runs "fn f(x: &mut Int) -> &mut Int from x { return &mut *x; }; a = 1; r = f(&mut a); *r = 9; return a;" (VInt 9))
                , testCase "a variant can hold a reference" (runs "enum E { A { r: &Int }, B { n: Int } }; a = 5; e = E::A { r: &a }; x = 0; x = match e { E::A { r: r } => *r, E::B { n: n } => n }; return x;" (VInt 5))
                , testCase "borrows of different elements are disjoint" (runs "xs = [1, 2, 3]; a = &get(xs, 0); b = &mut get(xs, 1); *b = 9; return *a + get(xs, 1);" (VInt 10))
                , testCase "borrows of the same element still conflict" (rejected "xs = [1, 2, 3]; a = &get(xs, 0); b = &mut get(xs, 0); *b = 9; return *a;" "cannot be borrowed for updating while that borrow is live")
                , testCase "a returned reference can come through a trait" (runs "trait Ref { fn getr(self: Self, x: &Int) -> &Int from x; }; struct A { n: Int }; impl Ref for A { fn getr(self: Self, x: &Int) -> &Int from x { return x; }; }; fn useit(a: &Int) -> &Int from a { v = A { n: 1 }; return Ref::getr(v, a); }; a = 3; r = useit(&a); return *r;" (VInt 3))
                , testCase "and through a function value" (runs "fn idr(x: &Int) -> &Int from x { return x; }; g = idr; a = 3; r = g(&a); return *r;" (VInt 3))
                , testCase "a reference in a list still freezes its place" (rejected "xs = [1]; rs = push([], &get(xs, 0)); xs = [2]; r = get(rs, 0); return *r;" "cannot be assigned while it is borrowed")
                , testCase "a reference read out of a list reads its place" (runs "xs = [1, 2]; rs = push([], &get(xs, 0)); r = get(rs, 0); return *r;" (VInt 1))
                , testCase "a result through a function value still freezes its place" (rejected "fn head(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); }; g = head; xs = [1]; r = g(xs); xs = [2]; return *r;" "cannot be assigned while it is borrowed")
                , testCase "an update result is read after it is written through" (runs "fn f(x: &mut Int) -> &mut Int from x { return x; }; a = 1; r = f(&mut a); *r = 9; return *r;" (VInt 9))
                , testCase "a reference to an unsized array can be sized" (runs "fn f(b: Box<Array<Int>>) -> Int { a = &*b; return size(*a); }; return f(Box::new(#[10, 20]));" (VInt 2))
                ]
            , TestList
                "conflicts"
                [ testCase "a second update borrow while the first is live" (rejected "x = 4; a = &mut x; b = &mut x; *a = 1; return *b;" "cannot be borrowed for updating while that borrow is live")
                , testCase "an update borrow while a read borrow is live" (rejected "fn inc(n: &mut Int) -> Int [{ }] [{ }] { *n = *n + 1; return *n; }; x = 1; r = &x; y = inc(&mut x); return *r + y;" "cannot be borrowed for updating while that borrow is live")
                , testCase "a move while a borrow is live" (rejected "xs = [1, 2]; r = &xs; ys = xs; return size(*r) + size(ys);" "cannot be moved while that borrow is live")
                , testCase "an owner is not assigned while borrowed" (rejected "x = 4; r = &mut x; x = 9; return *r;" "cannot be assigned while it is borrowed")
                , testCase "a value is not moved out of a reference" (rejected "xs = [1, 2]; r = &xs; return *r;" "cannot move")
                , testCase "a value read through a reference is a view, not a move" (runs "xs = [1, 2]; r = &xs; ys = *r; return size(ys) + size(xs);" (VInt 4))
                , testCase "a Box owner cannot be moved while its payload is borrowed" (rejected "struct Payload { xs: List<Int> }; b = Box::new(Payload { xs: [1] }); r = &*b; moved = b; return size((*r).xs);" "cannot be moved while that borrow is live")
                , testCase "a Box owner cannot be replaced while its payload is borrowed" (rejected "struct Payload { xs: List<Int> }; b = Box::new(Payload { xs: [1] }); r = &*b; b = Box::new(Payload { xs: [2] }); return size((*r).xs);" "cannot be assigned while it is borrowed")
                , testCase "a boxed payload cannot be moved out of a read reference" (rejected "struct Payload { xs: List<Int> }; b = Box::new(Payload { xs: [1] }); r = &*b; return *r;" "cannot move")
                , testCase "a cloned boxed payload releases its source loan" (runs "struct Payload { xs: List<Int> }; impl Clone for Payload { }; b = Box::new(Payload { xs: [1] }); copy = clone(Box::unbox(b)); b = Box::new(Payload { xs: [2, 3] }); return size(b.xs) * 10 + size(copy.xs);" (VInt 21))
                , testCase "no update borrow of what a read borrow is to" (rejected "x = 4; r = &x; s = &mut *r; *s = 5; return x;" "cannot be made through a read reference")
                ]
            , TestList
                "a call that moves what it is lent"
                [ testCase "a borrow of a field and the value that holds it" (rejected "struct S { xs: List<Int>, n: Int }; fn f(s: S, xs: &List<Int>) -> Int { return size(xs) + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(s, &s.xs);" "s.xs is lent to this call, and s, which holds it, is moved by it too")
                , testCase "in the other order" (rejected "struct S { xs: List<Int>, n: Int }; fn f(xs: &List<Int>, s: S) -> Int { return size(xs) + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(&s.xs, s);" "s.xs is lent to this call, and s, which holds it, is moved by it too")
                , testCase "a borrow of the whole value" (rejected "struct S { xs: List<Int>, n: Int }; fn f(s: S, t: &S) -> Int { return size(t.xs) + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(s, &s);" "s is lent to this call and moved by it too")
                , testCase "a borrow of the whole value in the other order" (rejected "struct S { xs: List<Int>, n: Int }; fn f(t: &S, s: S) -> Int { return size(t.xs) + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(&s, s);" "s is lent to this call and moved by it too")
                , testCase "a borrow of a nested field" (rejected "struct S { xs: List<Int>, n: Int }; struct T { s: S, k: Int }; fn f(t: T, xs: &List<Int>) -> Int { return size(xs) + t.k; }; t = T { s: S { xs: [1, 2, 3], n: 0 }, k: 0 }; return f(t, &t.s.xs);" "t.s.xs is lent to this call, and t, which holds it, is moved by it too")
                , testCase "an update borrow of a field" (rejected "struct S { xs: List<Int>, n: Int }; fn f(s: S, xs: &mut List<Int>) -> Int writes(xs) { *xs = push(clone(*xs), 4); return size(*xs) + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(s, &mut s.xs);" "s.xs is lent to this call, and s, which holds it, is moved by it too")
                , testCase "a part moved while the whole is lent" (rejected "struct S { xs: List<Int>, n: Int }; fn f(xs: List<Int>, t: &S) -> Int { return size(xs) + t.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(s.xs, &s);" "s is lent to this call, and s.xs, a part of it, is moved by it too")
                , testCase "a reference local whose last use is the call" (rejected "struct S { xs: List<Int>, n: Int }; fn f(s: S, xs: &List<Int>) -> Int { return size(xs) + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; r = &s.xs; return f(s, r);" "s.xs is lent to this call, and s, which holds it, is moved by it too")
                , testCase "a holder of a reference given to the call" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int> }; fn f(s: S, w: W) -> Int { x = w.r; return size(*x) + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(s, W { r: &s.xs });" "s.xs is lent to this call, and s, which holds it, is moved by it too")
                , testCase "a struct made of a value and a borrow of it" (rejected "struct S { xs: List<Int>, n: Int }; struct W { s: S, r: &List<Int> }; fn f(w: W) -> Int { return size(*w.r) + w.s.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(W { s: s, r: &s.xs });" "s.xs is borrowed in this expression, and s, which holds it, is moved by it too")
                , testCase "a field read through a reference to the value" (rejected "struct S { xs: List<Int>, n: Int }; fn f(xs: List<Int>, b: &List<Int>) -> Int { return size(xs) + size(b); }; s = S { xs: [1, 2, 3], n: 0 }; r = &s; return f(s.xs, (*r).xs);" "s.xs is lent to this call and moved by it too")
                , testCase "and the value that holds it moved" (rejected "struct S { xs: List<Int>, n: Int }; fn f(s: S, b: &List<Int>) -> Int { return size(b) + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; r = &s; return f(s, (*r).xs);" "s.xs is lent to this call, and s, which holds it, is moved by it too")
                , testCase "a field of another value read through a reference" (runs "struct S { xs: List<Int>, n: Int }; fn f(xs: List<Int>, b: &List<Int>) -> Int { return size(xs) + size(b); }; s = S { xs: [1, 2, 3], n: 4 }; t = S { xs: [5], n: 0 }; r = &t; return f(s.xs, (*r).xs);" (VInt 4))
                , testCase "a field that a holder of a borrow owns" (runs "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn mk(s: &S) -> W from s { return W { r: &s.xs, ys: [7] }; }; fn f(s: S, ys: &List<Int>) -> Int { return size(ys) * 10 + s.n; }; s = S { xs: [1, 2, 3], n: 4 }; w = mk(&s); return f(s, w.ys);" (VInt 14))
                , testCase "a reborrow of a field" (rejected "struct S { xs: List<Int>, n: Int }; fn f(s: S, xs: &List<Int>) -> Int { return size(xs) + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; r = &s; return f(s, &(*r).xs);" "s.xs is lent to this call, and s, which holds it, is moved by it too")
                , testCase "a result from a field" (rejected "struct S { xs: List<Int>, n: Int }; struct T { s: S, k: Int }; fn getxs(s: &S) -> &List<Int> from s { return &s.xs; }; fn f(t: T, xs: &List<Int>) -> Int { return size(xs) + t.k; }; t = T { s: S { xs: [1, 2, 3], n: 0 }, k: 0 }; return f(t, getxs(t.s));" "t.s is lent to this call, and t, which holds it, is moved by it too")
                , testCase "a method that takes its receiver" (rejected "struct S { xs: List<Int>, n: Int }; impl S { fn take(self: Self, xs: &List<Int>) -> Int { return size(xs) + self.n; }; }; s = S { xs: [1, 2, 3], n: 0 }; return s.take(&s.xs);" "s.xs is lent to this call, and s, which holds it, is moved by it too")
                , testCase "a call through a function value" (rejected "struct S { xs: List<Int>, n: Int }; fn f(s: S, xs: &List<Int>) -> Int { return size(xs) + s.n; }; g = f; s = S { xs: [1, 2, 3], n: 0 }; return g(s, &s.xs);" "s.xs is lent to this call, and s, which holds it, is moved by it too")
                , testCase "another field can be moved" (runs "struct S { xs: List<Int>, n: Int }; fn f(xs: List<Int>, n: &Int) -> Int { return size(xs) + *n; }; s = S { xs: [1, 2, 3], n: 4 }; return f(s.xs, &s.n);" (VInt 7))
                , testCase "a borrow that ends before the call can be of what it moves" (runs "struct S { xs: List<Int>, n: Int }; fn g(xs: &List<Int>) -> Int { return size(xs); }; fn f(s: S, k: Int) -> Int { return k + s.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(s, g(&s.xs));" (VInt 3))
                , testCase "two borrows of a value and its field" (runs "struct S { xs: List<Int>, n: Int }; fn f(t: &S, xs: &List<Int>) -> Int { return size(xs) + t.n; }; s = S { xs: [1, 2, 3], n: 0 }; return f(&s, &s.xs) + size(s.xs);" (VInt 6))
                ]
            , TestList
                "borrows of values that hold references"
                [ testCase "a field a returned holder owns is lent while what it borrows is moved" (runs "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn mk(s: &S) -> W from s { return W { r: &s.xs, ys: [7] }; }; fn f(s: S, ys: &List<Int>) -> Int { return size(ys) * 10 + s.n; }; s = S { xs: [1, 2, 3], n: 4 }; w = mk(&s); return f(s, &w.ys);" (VInt 14))
                , testCase "a borrow of such a field is live while what it borrows is moved" (runs "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn mk(s: &S) -> W from s { return W { r: &s.xs, ys: [7] }; }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; w = mk(&s); q = &w.ys; a = g(s); return size(*q) + a;" (VInt 5))
                , testCase "and of a field a made holder owns" (runs "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; w = W { r: &s.xs, ys: [7] }; q = &w.ys; a = g(s); return size(*q) + a;" (VInt 5))
                , testCase "and of a plain field of a value that holds a holder" (runs "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; struct O { w: W, k: Int }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; o = O { w: W { r: &s.xs, ys: [7] }, k: 1 }; q = &o.k; a = g(s); return *q + a;" (VInt 5))
                , testCase "a borrow of a returned holder freezes what it borrows" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn mk(s: &S) -> W from s { return W { r: &s.xs, ys: [7] }; }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; w = mk(&s); q = &w; a = g(s); r = (*q).r; return size(*r) + a;" "s is borrowed by q, so it cannot be moved while that borrow is live")
                , testCase "and of a made holder" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; w = W { r: &s.xs, ys: [7] }; q = &w; a = g(s); r = (*q).r; return size(*r) + a;" "s is borrowed by q, so it cannot be moved while that borrow is live")
                , testCase "a reference read through a borrow of a holder freezes what it is to" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; w = W { r: &s.xs, ys: [7] }; q = &w; r = (*q).r; a = g(s); return size(*r) + a;" "s is borrowed by r, so it cannot be moved while that borrow is live")
                , testCase "and through a borrow of a returned holder" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn mk(s: &S) -> W from s { return W { r: &s.xs, ys: [7] }; }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; w = mk(&s); q = &w; r = (*q).r; a = g(s); return size(*r) + a;" "s is borrowed by r, so it cannot be moved while that borrow is live")
                , testCase "a borrow of a field that is a holder freezes what it borrows" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; struct O { w: W, k: Int }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; o = O { w: W { r: &s.xs, ys: [7] }, k: 1 }; q = &o.w; a = g(s); t = *q; r = t.r; return size(*r) + a;" "s is borrowed by q, so it cannot be moved while that borrow is live")
                , testCase "a reference read out of an enum returned under from" (rejected "struct S { xs: List<Int>, n: Int }; fn g(s: S) -> Int { return s.n; }; enum E { Some { r: &List<Int> }, None }; fn mk(s: &S) -> E from s { return E::Some { r: &s.xs }; }; s = S { xs: [1, 2, 3], n: 4 }; e = mk(&s); v = e as E::Some; y = v.r; a = g(s); return size(*y) + a;" "s is borrowed by y, so it cannot be moved while that borrow is live")
                , testCase "a reference read out of a holder in a Box" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; b = Box::new(W { r: &s.xs, ys: [7] }); y = b.r; a = g(s); return size(*y) + a;" "s is borrowed by y, so it cannot be moved while that borrow is live")
                , testCase "a reference read out of a holder nested in a returned value" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; struct O { w: W, k: Int }; fn g(s: S) -> Int { return s.n; }; fn mk(s: &S) -> O from s { return O { w: W { r: &s.xs, ys: [7] }, k: 1 }; }; s = S { xs: [1, 2, 3], n: 4 }; o = mk(&s); x = o.w; y = x.r; a = g(s); return size(*y) + a;" "s is borrowed by y, so it cannot be moved while that borrow is live")
                , testCase "a borrow of a plain field of such a value freezes nothing it borrows" (runs "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; struct O { w: W, k: Int }; fn g(s: S) -> Int { return s.n; }; fn mk(s: &S) -> O from s { return O { w: W { r: &s.xs, ys: [7] }, k: 1 }; }; s = S { xs: [1, 2, 3], n: 4 }; o = mk(&s); q = &o.k; a = g(s); return *q + a;" (VInt 5))
                , testCase "a borrow of a holder field of a returned value that also holds a reference of its own" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; struct O { direct: &List<Int>, w: W }; fn g(s: S) -> Int { return s.n; }; fn mk(s: &S) -> O from s { return O { direct: &s.xs, w: W { r: &s.xs, ys: [7] } }; }; s = S { xs: [1, 2, 3], n: 4 }; o = mk(&s); q = &o.w; a = g(s); r = (*q).r; return size(*r) + a;" "s is borrowed by q, so it cannot be moved while that borrow is live")
                , testCase "and a reborrow of a borrow of a holder" (rejected "struct S { xs: List<Int>, n: Int }; struct W { r: &List<Int>, ys: List<Int> }; fn g(s: S) -> Int { return s.n; }; s = S { xs: [1, 2, 3], n: 4 }; w = W { r: &s.xs, ys: [7] }; q = &w; t = &*q; a = g(s); u = (*t).r; return size(*u) + a;" "s is borrowed by t, so it cannot be moved while that borrow is live")
                ]
            , TestList
                "a call that reads what it updates"
                [ testCase "a field lent for updating and lent by the signature" (rejected "struct S { xs: List<Int>, n: Int }; fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; s = S { xs: [1, 2, 3], n: 0 }; return f(&mut s.xs, s.xs);" "s.xs is lent to this call and lent to it for updating too")
                , testCase "in the other order" (rejected "struct S { xs: List<Int>, n: Int }; fn f(b: &List<Int>, a: &mut List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; s = S { xs: [1, 2, 3], n: 0 }; return f(s.xs, &mut s.xs);" "s.xs is lent to this call and lent to it for updating too")
                , testCase "the whole lent for updating and a field lent" (rejected "struct S { xs: List<Int>, n: Int }; fn f(a: &mut S, b: &List<Int>) -> Int writes(a) { (*a).xs = [7, 7, 7, 7]; return size(b); }; s = S { xs: [1, 2, 3], n: 0 }; return f(&mut s, s.xs);" "s.xs is lent to this call, and s is lent to it for updating")
                , testCase "a field lent for updating and the whole lent" (rejected "struct S { xs: List<Int>, n: Int }; fn f(a: &mut List<Int>, b: &S) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b.xs); }; s = S { xs: [1, 2, 3], n: 0 }; return f(&mut s.xs, s);" "s is lent to this call, and s.xs is lent to it for updating")
                , testCase "an update reference local whose last use is the call" (rejected "struct S { xs: List<Int>, n: Int }; fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; s = S { xs: [1, 2, 3], n: 0 }; r = &mut s.xs; return f(r, s.xs);" "s.xs is lent to this call and lent to it for updating too")
                , testCase "a field read through a reference to the value" (rejected "struct S { xs: List<Int>, n: Int }; fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; s = S { xs: [1, 2, 3], n: 0 }; r = &s; return f(&mut s.xs, (*r).xs);" "s.xs is lent to this call and lent to it for updating too")
                , testCase "another field can be read" (runs "struct S { xs: List<Int>, n: Int }; fn f(a: &mut List<Int>, b: &Int) -> Int writes(a) { *a = [7, 7, 7, 7]; return b; }; s = S { xs: [1, 2, 3], n: 5 }; return f(&mut s.xs, s.n);" (VInt 5))
                , testCase "a Copy field is read as it was before the call" (runs "struct S { xs: List<Int>, n: Int }; fn f(a: &mut Int, b: &Int) -> Int writes(a) { *a = 9; return b; }; s = S { xs: [1, 2, 3], n: 5 }; return f(&mut s.n, s.n) * 10 + s.n;" (VInt 59))
                , testCase "a field of another value read through a reference" (runs "struct S { xs: List<Int>, n: Int }; fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; s = S { xs: [1, 2, 3], n: 0 }; t = S { xs: [5], n: 0 }; r = &t; return f(&mut s.xs, (*r).xs);" (VInt 1))
                , testCase "a whole Copy variable is lent, not copied" (rejected "fn f(a: &mut Int, b: &Int) -> Int writes(a) { *a = 9; return b; }; n = 5; return f(&mut n, n) * 10 + n;" "n is lent to this call and lent to it for updating too")
                , testCase "elements at different known indexes" (runs "fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; xs = [[1, 2, 3], [5]]; return f(&mut get(xs, 0), get(xs, 1));" (VInt 1))
                , testCase "an index changed through an update borrow is not known" (rejected "fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; fn setOne(i: &mut Int) -> Int writes(i) { *i = 1; return 0; }; xs = [[1, 2, 3], [5]]; i = 0; k = setOne(&mut i); return f(&mut get(xs, 1), get(xs, i));" "is lent to this call, and xs[1] is lent to it for updating")
                , testCase "and a view at it still overlaps an update borrow" (rejected "fn setOne(i: &mut Int) -> Int writes(i) { *i = 1; return 0; }; xs = [[1, 2, 3], [5]]; i = 0; k = setOne(&mut i); row = get(xs, i); r = &row; w = &mut get(xs, 1); *w = [9]; return size(*r);" "cannot be borrowed for updating while that borrow is live")
                , testCase "nor one a call gave" (rejected "fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; fn one() -> Int { return 1; }; xs = [[1, 2, 3], [5]]; i = 0; i = one(); return f(&mut get(xs, 1), get(xs, i));" "is lent to this call, and xs[1] is lent to it for updating")
                , testCase "nor one that differs on the paths that meet" (rejected "fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; fn g(c: Bool) -> Int { xs = [[1, 2, 3], [5]]; i = 0; if c { i = 1; }; return f(&mut get(xs, 1), get(xs, i)); }; return g(true);" "is lent to this call, and xs[1] is lent to it for updating")
                , testCase "the same element" (rejected "fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; xs = [[1, 2, 3], [5]]; return f(&mut get(xs, 0), get(xs, 0));" "xs[0] is lent to this call and lent to it for updating too")
                , testCase "an element at an index that is not known" (rejected "fn f(a: &mut List<Int>, b: &List<Int>) -> Int writes(a) { *a = [7, 7, 7, 7]; return size(b); }; fn g(xs: List<List<Int>>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(xs); affirm size(xs) > 1; }] [{ }] { return f(&mut get(xs, 1), get(xs, i)); }; return g([[1, 2, 3], [5]], 0);" "is lent to this call, and xs[1] is lent to it for updating")
                ]
            , TestList
                "closure captures"
                [ testCase "a variable a closure borrows for reading cannot be assigned while the closure is live" (rejected "xs = push(push([], 1), 2); f = fn() -> Int => size(xs); xs = push(xs, 3); return f();" "cannot be assigned while it is borrowed")
                , testCase "a variable a closure borrows for updating cannot be read while the closure is live" (rejected "count = 0; f = fn() -> Int { count = count + 1; return count; }; a = count; b = f(); return a + b;" "cannot be read while that borrow is live")
                , testCase "a borrowed capture can be used again after the closure's last use" (runs "xs = push(push([], 1), 2); f = fn() -> Int => size(xs); a = f(); xs = push(xs, 3); return a * 10 + size(xs);" (VInt 23))
                ]
            , TestList
                "an update reference reached through a shared path is read-only"
                [ testCase "in a function the list is lent to" (rejected "fn g(rs: &List<&mut Int>) -> Int [{ affirm size(rs) > 0; }] [{ }] { q = get(rs, 0); *q = 41; return 0; }; fn f(c: Int) -> Int { x = 1; rs = push([], &mut x); y = g(rs); return x + y; }; return f(1);" (readOnly "g" "q" "written through"))
                , testCase "held by a holder lent to be read" (rejected (sharedHolder ++ "fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; n = mutate(w); return x; }; return f(0);") (readOnlyIn "mutate" "written through"))
                , testCase "held by a receiver lent to a method" (rejected (sharedHolder ++ "impl W { fn bump(self: &Self) -> Int { p = self.r; *p = 5; return 0; }; }; fn f(c: Int) -> Int { x = 0; w = W { r: &mut x }; n = w.bump(); return x; }; return f(0);") (readOnly "<W>::bump" "p" "written through"))
                , testCase "an element of a list lent to a for loop" (rejected "fn g(l: &List<&mut Int>) -> Int { for p in l { *p = 5; }; return 0; }; fn f(c: Int) -> Int { x = 0; l = push([], &mut x); n = g(l); return x; }; return f(0);" (readOnly "g" "p" "written through"))
                , testCase "a payload of an enum lent to a match" (rejected "enum E { Some { r: &mut Int }, Nothing }; fn g(e: &E) -> Int { match e { E::Some { r: r } => { *r = 5; }, E::Nothing => { } }; return 0; }; fn f(c: Int) -> Int { x = 0; e = E::Some { r: &mut x }; n = g(e); return x; }; return f(0);" (readOnly "g" "r" "written through"))
                , testCase "the value of a Box lent to be read" (rejected (sharedHolder ++ "fn g(b: &Box<W>) -> Int { u = Box::unbox(b); p = u.r; *p = 5; return 0; }; fn f(c: Int) -> Int { x = 0; b = Box::new(W { r: &mut x }); n = g(b); return x; }; return f(0);") (readOnly "g" "p" "written through"))
                , testCase "read through a shared reference to a holder of the function's own" (rejected (sharedHolder ++ "fn f(c: Int) -> Int { x = 0; w = W { r: &mut x }; s = &w; p = (*s).r; *p = 5; return x; }; return f(0);") (readOnly "f" "p" "written through"))
                , testCase "it cannot be reborrowed for updating" (rejected (sharedHolder ++ "fn g(w: &W) -> Int { p = w.r; q = &mut *p; *q = 5; return 0; }; fn f(c: Int) -> Int { x = 0; w = W { r: &mut x }; n = g(w); return x; }; return f(0);") (readOnly "g" "p" "lent for updating"))
                , testCase "nor lent to an update parameter" (rejected (sharedHolder ++ "fn up(r: &mut Int) -> Int { *r = 5; return 0; }; fn g(w: &W) -> Int { p = w.r; return up(p); }; fn f(c: Int) -> Int { x = 0; w = W { r: &mut x }; n = g(w); return x; }; return f(0);") (readOnly "g" "p" "lent for updating"))
                , testCase "nor put into a value given on" (rejected (sharedHolder ++ "fn wv(v: W) -> Int { *v.r = 5; return 0; }; fn g(w: &W) -> Int { p = w.r; return wv(W { r: p }); }; fn f(c: Int) -> Int { x = 0; w = W { r: &mut x }; n = g(w); return x; }; return f(0);") "Move error: in g: w.r is lent (&T) to this function and can only be read")
                , testCase "nor given by value to a generic function" (rejected (sharedHolder ++ "fn keep<T>(v: T) -> Int { return 0; }; fn g(w: &W) -> Int { p = w.r; return keep(p); }; fn f(c: Int) -> Int { x = 0; w = W { r: &mut x }; n = g(w); return x; }; return f(0);") "Move error: in g: w.r is lent (&T) to this function and can only be read")
                , testCase "nor given on when it is read out of a holder that may be shared" (rejected (pairHolder ++ "fn wv(v: H) -> Int { *v.r = 5; return 0; }; fn g(l: &List<H>, c: Bool) -> Int [{ affirm size(l) > 0; }] [{ }] { y = 0; h = get(l, 0); if c { } else { h = H { r: &mut y, n: 0 }; }; p = h.r; return wv(H { r: p, n: 0 }); }; fn f(c: Int) -> Int { x = 1; l = push([], H { r: &mut x, n: 0 }); n = g(l, true); return x; }; return f(0);") (readOnly "g" "p" "given on"))
                , testCase "nor captured for updating by a closure" (rejected (sharedHolder ++ "fn g(w: &W) -> Int { k = fn() -> Int { *w.r = 5; return 0; }; return k(); }; fn f(c: Int) -> Int { x = 0; w = W { r: &mut x }; n = g(w); return x; }; return f(0);") "w is lent (&T) to this function and can only be read, so it cannot be borrowed for updating")
                , testCase "when the paths that meet give a shared holder on one" (rejected (pairHolder ++ "fn g(l: &List<H>, c: Bool) -> Int [{ affirm size(l) > 0; }] [{ }] { y = 0; h = get(l, 0); if c { } else { h = H { r: &mut y, n: 0 }; }; p = h.r; *p = 5; return y; }; fn f(c: Int) -> Int { x = 1; l = push([], H { r: &mut x, n: 0 }); n = g(l, true); return x; }; return f(0);") (readOnly "g" "p" "written through"))
                , testCase "whichever of the paths gives the shared holder" (rejected (pairHolder ++ "fn g(l: &List<H>, c: Bool) -> Int [{ affirm size(l) > 0; }] [{ }] { y = 0; h = H { r: &mut y, n: 0 }; if c { } else { h = get(l, 0); }; p = h.r; *p = 5; return y; }; fn f(c: Int) -> Int { x = 1; l = push([], H { r: &mut x, n: 0 }); n = g(l, false); return x; }; return f(0);") (readOnly "g" "p" "written through"))
                , testCase "when a loop gives the shared holder on its way back" (rejected (pairHolder ++ "fn g(l: &List<H>) -> Int [{ affirm size(l) > 0; }] [{ }] { y = 0; h = H { r: &mut y, n: 0 }; i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { p = h.r; *p = 5; h = get(l, 0); i = i + 1; }; return y; }; fn f(c: Int) -> Int { x = 1; l = push([], H { r: &mut x, n: 0 }); n = g(l); return x; }; return f(0);") (readOnly "g" "p" "written through"))
                , testCase "a part of a joined holder cannot be moved on" (rejected (nestedHolder ++ "fn g(l: &List<B>, c: Bool) -> Int [{ affirm size(l) > 0; }] [{ }] { y = 0; h = get(l, 0); if c { } else { h = B { a: A { r: &mut y, n: 0 }, n: 0 }; }; t = h.a; u = t; return u.n; }; fn f(c: Int) -> Int { x = 1; l = push([], B { a: A { r: &mut x, n: 0 }, n: 0 }); n = g(l, true); return x; }; return f(0);") (readOnly "g" "t" "given on"))
                , testCase "nor put into a value of the function's own" (rejected (nestedHolder ++ "fn g(l: &List<B>, c: Bool) -> Int [{ affirm size(l) > 0; }] [{ }] { y = 0; h = get(l, 0); if c { } else { h = B { a: A { r: &mut y, n: 0 }, n: 0 }; }; t = h.a; v = B { a: t, n: 0 }; return v.n; }; fn f(c: Int) -> Int { x = 1; l = push([], B { a: A { r: &mut x, n: 0 }, n: 0 }); n = g(l, true); return x; }; return f(0);") (readOnly "g" "t" "given on"))
                , testCase "and a payload of a joined value taken apart by a match is read-only" (rejected "struct A { r: &mut Int, n: Int }; enum F { Some { a: A }, Nothing }; fn g(l: &List<F>, c: Bool) -> Int [{ affirm size(l) > 0; }] [{ }] { y = 0; h = get(l, 0); if c { } else { h = F::Some { a: A { r: &mut y, n: 0 } }; }; n = match h { F::Some { a: t } => { q = &mut *t.r; 0 }, F::Nothing => 0, }; return n; }; fn f(c: Int) -> Int { x = 1; l = push([], F::Some { a: A { r: &mut x, n: 0 } }); n = g(l, true); return x; }; return f(0);" "so nothing can be changed through it: it cannot be lent for updating")
                , testCase "nor cloned by a generic function, since an update reference is not Clone" (rejected "fn firstOf<T: Clone>(l: &List<T>) -> T [{ affirm size(l) > 0; }] [{ }] { return get(l, 0).clone(); }; fn g(l: &List<&mut Int>) -> Int [{ affirm size(l) > 0; }] [{ }] { p = firstOf(l); *p = 5; return 0; }; fn f(c: Int) -> Int { x = 1; l = push([], &mut x); n = g(l); return x; }; return f(0);" "firstOf needs T to implement Clone, and &mut Int does not")
                , testCase "nor by its holder's Clone" (rejected (sharedHolder ++ "impl Clone for W { }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; v = clone(w); return 0; }; return f(0);") "Move error: in <W as Clone>::clone")
                , testCase "a holder lent for updating can be written through" (runs (sharedHolder ++ "fn mutate(w: &mut W) -> Int { *w.r = 4; return 0; }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; n = mutate(&mut w); return x; }; return f(0);") (VInt 4))
                , testCase "a holder given by value can be written through" (runs (sharedHolder ++ "fn mutate(w: W) -> Int { *w.r = 4; return 0; }; fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; n = mutate(w); return x; }; return f(0);") (VInt 4))
                , testCase "a holder lent to be read can be read through and lent on to be read" (runs (sharedHolder ++ "fn peek(w: &W) -> Int { return *w.r; }; fn g(w: &W) -> Int { p = w.r; q = &*p; return *p + *q + peek(w); }; fn f(c: Int) -> Int { x = 2; w = W { r: &mut x }; return g(w); }; return f(0);") (VInt 6))
                , testCase "holders of the function's own on every path can be written through" (runs (pairHolder ++ "fn g(c: Bool) -> Int { y = 0; z = 0; h = H { r: &mut y, n: 0 }; if c { } else { h = H { r: &mut z, n: 0 }; }; p = h.r; *p = 5; return y * 10 + z; }; return g(true) * 100 + g(false);") (VInt 5005))
                , testCase "a part of a holder of the function's own can be moved on" (runs (nestedHolder ++ "fn g(c: Bool) -> Int { y = 0; z = 0; h = B { a: A { r: &mut z, n: 0 }, n: 0 }; if c { } else { h = B { a: A { r: &mut y, n: 0 }, n: 0 }; }; t = h.a; u = t; p = u.r; *p = 5; return y * 10 + z; }; return g(true) * 100 + g(false);") (VInt 550))
                , testCase "a closure can write through a holder of the function's own" (runs (sharedHolder ++ "fn f(c: Int) -> Int { x = 1; w = W { r: &mut x }; k = fn() -> Int { *w.r = 7; return 0; }; n = k(); return x; }; return f(0);") (VInt 7))
                , testCase "a holder given a value of the function's own after a shared one can be written through" (runs (pairHolder ++ "fn g(l: &List<H>) -> Int [{ affirm size(l) > 0; }] [{ }] { y = 0; h = get(l, 0); k = *h.r; h = H { r: &mut y, n: 0 }; p = h.r; *p = 5 + k; return y; }; fn f(c: Int) -> Int { x = 1; l = push([], H { r: &mut x, n: 0 }); return g(l); }; return f(0);") (VInt 6))
                , testCase "a copy of a number lent to be read is a value of its own" (runs "fn g(n: &Int) -> Int { xs = [1, 2]; xs = set(xs, 0, n); ys = xs; return get(ys, 0) + size(ys); }; return g(5);" (VInt 7))
                , testCase "a closure can read through a holder lent to be read" (runs (sharedHolder ++ "fn g(w: &W) -> Int { k = fn() -> Int => *w.r; return k(); }; fn f(c: Int) -> Int { x = 3; w = W { r: &mut x }; return g(w); }; return f(0);") (VInt 3))
                ]
            ]

-- (every type has its declaration once a program is lowered, so this one is taken out of the lowered program)
undeclaredHolder :: TestResult
undeclaredHolder = case parseStatementBlock source of
    Left err -> Just ("Parse error: " ++ err)
    Right stmts -> case elaborateStatements stmts of
        Error e -> Just e
        Ok lowered -> case finishLowered lowered of
            Error e -> Just ("Refused with the declaration: " ++ e)
            Ok _ -> testAssertErrorContains "Move error: in f: x is borrowed by h, so it cannot be read while that borrow is live" (finishLowered (withoutDeclaration lowered))
  where
    source = "struct HB { n: Int }; fn put(h: &mut HB, r: &mut Int) -> Int { return 0; }; fn f(c: Int) -> Int { x = 1; h = HB { n: 0 }; k = put(&mut h, &mut x); v = x; return v + h.n; }; return f(1);"
    withoutDeclaration lowered = lowered{M.lowProgram = (M.lowProgram lowered){M.progTypes = Map.delete "HB" (M.progTypes (M.lowProgram lowered))}}

loanTableCases :: Test
loanTableCases = TestList "MIR loan rules"
    ( [ testCase label (withLoan [(1, TInt), (2, r), (3, input), (4, output)] setup (M.Assign (l 4) rv) use)
      | (label, input, output, setup, rv, use) <- transferCases
      ]
    ++ [ testCase "TakeField is not available before ownership" (refuse "the loans of result are not modelled" [(3, holder), (4, r)] [mkHolder, M.Assign (l 4) (M.TakeField (l 3) "LoanHolder" "ref")])
       , testCase "Peek is not available before ownership" (refuse "the loans of result are not modelled" [(3, holder), (4, r)] [mkHolder, M.Peek (l 4) (M.ReadField (cp 3) "LoanHolder" "ref")])
       , testCase "a scalar TakeField has no reference loans" (testAssertEq (check [] Map.empty [(3, scalar), (4, TInt)] (end [M.Assign (l 4) (M.TakeField (l 3) "Scalar" "n")])) [])
       , testCase "an unsourced non-generic reference result is refused" unsourced
       , testCase "a permission returning a local loan is refused" returnsOwn
       , testCase "a reference-capable foreign result is refused" (foreignCase (TBlock r) [] (Just "importSlots is an extern fn and gives a value that can hold a reference"))
       , testCase "a reference-capable foreign permission argument is refused" (foreignCase TInt [(3, TBlock r)] (Just "importSlots is an extern fn and cannot accept a Block that may hold a reference"))
       , testCase "reference-free foreign permission arguments still work" (foreignCase TInt [(3, TBlock TInt)] Nothing)
       , testCase "a reference-capable extern is not an assignable value" (foreignValue False)
       , testCase "the extern value guard also covers stores through a reference" (foreignValue True)
       , testCase "unknown extern values fail closed" (requireError "importSlots is an extern fn that gives a value that can hold a reference" (check [] Map.empty [(4, TFn [] TInt)] (end [set 4 (M.Use (M.Const (M.CFn externName)))])))
       , testCase "mutable raw slot views are deferred" (slotGuard (TMutRef TInt))
       , testCase "the slot guard inspects nested update references" (slotGuard updateHolder)
       , testCase "the slot guard follows the fields of a declared Box" (slotGuard (TBox TInt))
       , testCase "the slot guard follows the fields of a declared List" (slotGuard (TList TBool))
       , testCase "ordinary primitive scalar containers have no update slot" (testAssertEq (slotErrors (TList TInt) ++ slotErrors (TBox TBool)) [])
       , testCase "foreign result checks inspect a declared Box" (foreignCase (TBlock (TBox TInt)) [] (Just "is an extern fn and gives a value that can hold a reference"))
       , testCase "foreign input checks inspect a declared List" (foreignCase TInt [(3, TBlock (TList TBool))] (Just "is an extern fn and cannot accept a Block that may hold a reference"))
       , testCase "a declared container is not exempt from default-deny" (refuse "the loans of result are not modelled" [(3, holder), (4, TBox TInt)] [mkHolder, M.Peek (l 4) (M.ReadField (cp 3) "LoanHolder" "ref")])
       , testCase "the slot guard does not assume an opaque declaration is immutable" (slotGuard (TNamed "OpaqueSlot" []))
       , testCase "a reference stored through an element borrow stays a loan of the list" (refuse "owner cannot be assigned while it is borrowed by result" elementStoreLocals (elementStore ++ [set 1 (M.Use (int 2))] ++ useList))
       , testCase "a reference stored through an element borrow ends with the list's last use" (testAssertEq (check [] Map.empty ([(1, TInt), (2, r)] ++ elementStoreLocals) (end (borrow ++ elementStore ++ useList ++ [set 1 (M.Use (int 2))]))) [])
       ] ++ [testCase ("declared from: " ++ label ++ " / " ++ input) (declaredResult ty aggregate expected)
            | (label, ty, expected) <- [("nested reference-bearing Block", envelope r, True), ("nested scalar Block", envelope TInt, False), ("ordinary reference holder", holder, False)]
            , (input, aggregate) <- [("lent input", False), ("by-value reference holder", True)]
            ] ++ sharedPathCases)
  where
    l = M.Local
    cp = M.Copy . l
    mv = M.Move . l
    int = M.Const . M.CInt
    set n = M.Assign (l n)
    r = TRef TInt
    block = TBlock r
    addr = TAddr r
    holder = TNamed "LoanHolder" []
    updateHolder = TNamed "UpdateHolder" []
    scalar = TNamed "Scalar" []
    b0 = M.BlockId 0
    b1 = M.BlockId 1
    end ss = [(b0, M.BasicBlock ss M.Unreachable)]
    locals = Map.fromList . map (\(n, ty) -> (l n, M.LocalDecl ty (Just (case n of 1 -> "owner"; 4 -> "result"; _ -> "v" ++ show n))))
    fn name params ret ls bs = M.Function name (map l params) ret (locals ls) (Map.fromList bs) [] [] [] [] [] M.emptySpec
    types = Map.fromList [("LoanHolder", M.StructDecl [("ref", r)]), ("UpdateHolder", M.StructDecl [("ref", TMutRef TInt)]), ("Scalar", M.StructDecl [("n", TInt)]), ("Option", M.EnumDecl [("Option::Some", [("ref", r)])]), ("UpdateOption", M.EnumDecl [("UpdateOption::Some", [("ref", TMutRef TInt)])])]
    envelope t = TNamed "Envelope" [ArgType t]
    generics = Map.fromList
        [ ("Envelope", (["T"], [("ref", r), ("wrapped", TNamed "Slots" [ArgType (TParam "T")])]))
        , ("Slots", (["T"], [("slot", TBlock (TParam "T"))]))
        ]
    check params fs ls bs = checkMoves Set.empty Set.empty Set.empty (M.Program declarations fs (fn "loans" params Nothing ls bs) generics Map.empty Map.empty Map.empty stdProtocols Nothing)
    declarations = Map.union types (Map.fromList
        [(instanceName base [ArgType ty], M.StructDecl [("update", TMutRef TInt)]) | (base, ty) <- [(storageBox stdStorage, TInt), (storageList stdStorage, TBool)]])
    declaredResult ty aggregate expectsLoan =
        let pty = if aggregate then holder else r
            param = if aggregate then 7 else 2
            callee = (fn "wrap" [8, param] (Just ty) [(0, ty), (8, r), (param, pty)] [])
                { M.fnBorrowed = [l 8] ++ [l param | not aggregate], M.fnSpec = M.emptySpec{M.specFrom = ["v8"]} }
            callerLocals = [(1, TInt), (2, r), (3, holder), (4, ty), (5, ty), (7, holder), (8, r), (9, TInt)]
            firstBlock = borrow ++ [set 9 (M.Use (int 5)), set 8 (M.Borrow (l 9) [] False)] ++
                [set 7 (M.MakeData "LoanHolder" [("ref", cp 2)]) | aggregate]
            call = M.Call (M.Const (M.CFn "wrap")) [cp 8, if aggregate then mv 7 else cp 2] (l 4) b1
            blocks = [(b0, M.BasicBlock firstBlock call), (b1, M.BasicBlock [set 1 (M.Use (int 2)), set 5 (M.Use (mv 4))] M.Unreachable)]
            es = check [] (Map.singleton "wrap" callee) callerLocals blocks
         in if expectsLoan then requireError "owner cannot be assigned while it is borrowed by result" es else testAssertEq [] es
    requireError msg es = if any (isInfixOf msg) es then Nothing else Just ("Expected " ++ show msg ++ "; got " ++ show es)
    borrow = [set 1 (M.Use (int 1)), set 2 (M.Borrow (l 1) [] False)]
    mkHolder = set 3 (M.MakeData "LoanHolder" [("ref", cp 2)])
    mkList = set 3 (M.MakeList [cp 2, cp 2])
    writeBlock = [set 3 (M.ListOp M.AddrWrite [int 0, int 0, cp 2, mv 3])]
    list = TList r
    uninit = TUninit r
    op tag = M.ListOp tag
    readRef = [set 6 (M.Deref (cp 4))]
    useHolder = [set 5 (M.ReadField (cp 4) "LoanHolder" "ref"), set 6 (M.Deref (cp 5))]
    useList = [set 5 (op M.First [cp 4]), set 6 (M.Deref (cp 5))]
    useUninit = [set 5 (op M.UninitGet [cp 4]), set 6 (M.Deref (cp 5))]
    useBlock = [set 5 (op M.AddrGet [int 0, int 0, cp 4]), set 6 (M.Deref (cp 5)), set 6 (op M.AddrFree [int 0, mv 4])]
    elementStoreLocals = [(3, TMutRef r), (4, list), (5, r), (6, TInt), (7, r), (8, TInt)]
    elementStore = [set 8 (M.Use (int 0)), set 7 (M.Borrow (l 8) [] False), set 4 (M.MakeList [mv 7]), set 3 (M.Borrow (l 4) [M.RefIndex (int 0)] True), M.AssignRef (l 3) [] (M.Use (cp 2))]
    transferCases =
        [ ("pop carries element loans", list, list, [mkList], op M.Pop [mv 3], useList)
        , ("first carries the element loan", list, r, [mkList], op M.First [cp 3], readRef)
        , ("last carries the element loan", list, r, [mkList], op M.Last [cp 3], readRef)
        , ("Uninit creation carries the value's loan", TInt, uninit, [], op M.UninitNew [cp 2], useUninit)
        , ("Uninit get carries the value's loan", uninit, r, [set 3 (op M.UninitNew [cp 2])], op M.UninitGet [cp 3], readRef)
        , ("Uninit take carries the value's loan", uninit, r, [set 3 (op M.UninitNew [cp 2])], op M.UninitTake [mv 3], readRef)
        , ("variant projection carries the payload loan", TNamed "Option" [], TVariant "Option::Some", [set 3 (M.MakeData "Option::Some" [("ref", cp 2)])], M.AsVariant (cp 3) "Option::Some", [set 5 (M.ReadField (cp 4) "Option::Some" "ref"), set 6 (M.Deref (cp 5))])
        , ("unbox carries loans in a holder", TBox holder, holder, [set 7 (M.MakeData "LoanHolder" [("ref", cp 2)]), set 3 (M.MakeBox (mv 7))], M.Unbox (cp 3), useHolder)
        , ("dereferencing a borrowed field carries the held loan", TRef r, r, [set 7 (M.MakeData "LoanHolder" [("ref", cp 2)]), set 3 (M.Borrow (l 7) [M.RefField "LoanHolder" "ref"] False)], M.Deref (cp 3), readRef)
        , ("Addr write carries the written loan", block, block, [set 3 (op M.BlockNew [int 0, int 1])], op M.AddrWrite [int 0, int 0, cp 2, mv 3], useBlock)
        , ("Addr get carries the slot loan", block, r, [set 3 (op M.BlockNew [int 0, int 1])] ++ writeBlock, op M.AddrGet [int 0, int 0, cp 3], readRef ++ [set 6 (op M.AddrFree [int 0, mv 3])])
        , ("Addr take carries the slot loan even without a tuple", block, r, [set 3 (op M.BlockNew [int 0, int 1])] ++ writeBlock, op M.AddrTake [int 0, int 0, cp 3], [set 6 (op M.AddrFree [int 0, mv 3])] ++ readRef)
        , ("Block split low carries the slot loans", block, block, [set 3 (op M.BlockNew [int 0, int 1])] ++ writeBlock, op M.BlockSplitLo [cp 3, int 1], useBlock ++ [set 6 (op M.AddrFree [int 0, mv 3])])
        , ("Block split high carries the slot loans", block, block, [set 3 (op M.BlockNew [int 0, int 1])] ++ writeBlock, op M.BlockSplitHi [mv 3, int 1], useBlock)
        , ("Block resize carries the slot loans", block, block, [set 3 (op M.BlockNew [int 0, int 1])] ++ writeBlock, op M.BlockResized [mv 3, int 2, int 4], useBlock)
        ]
    withLoan ls setup result use = requireError "owner cannot be assigned while it is borrowed by result" (check [] Map.empty (ls ++ [(5, r), (6, TInt), (7, holder)]) (end (borrow ++ setup ++ [result, set 1 (M.Use (int 2))] ++ use)))
    refuse msg ls ss = requireError msg (check [] Map.empty ([(1, TInt), (2, r)] ++ ls) (end (borrow ++ ss)))
    unsourced = requireError "the call gives a value that can hold a reference and is given nothing it could hold or borrow" $
        check [] (Map.singleton "source" (fn "source" [] (Just r) [(0, r)] [])) [(4, r)]
            [(b0, M.BasicBlock [] (M.Call (M.Const (M.CFn "source")) [] (l 4) b1)), (b1, M.BasicBlock [] M.Unreachable)]
    returnsOwn = requireError "the value returned holds a reference to owner" $
        check [] Map.empty [(0, block), (1, TInt), (2, r), (3, block)]
            [(b0, M.BasicBlock (borrow ++ [set 3 (op M.BlockNew [int 0, int 1])] ++ writeBlock ++ [set 0 (M.Use (mv 3))]) M.Return)]
    externName = "extern importSlots"
    -- Rule 6 over the MIR forms: holder 3 in each state, update reference 5 derived from it by each alias-preserving
    -- operation, then each use of 5. Mutating uses are refused exactly when 3 may be reached through a shared path.
    sharedPathCases =
        [ testCase ("shared path: " ++ sname ++ " / " ++ dname ++ " / " ++ uname) (expectShared shared (moving || consumes && not (null borrowed)) mutating consumes (sharedPathProgram params borrowed mutBorrowed setup derive use))
        | (sname, shared, params, borrowed, mutBorrowed, setup) <- holderStates
        , (dname, moving, derive) <- holderDerivations
        , (uname, mutating, consumes, use) <- referenceUses
        ] ++
        [ testCase "shared path: a cast of an enum lent to be read" (expectShared True False True False (sharedPathProgram [15, 9] [15] [] [] [set 16 (M.AsVariant (cp 15) "UpdateOption::Some"), set 5 (M.ReadField (cp 16) "UpdateOption::Some" "ref")] writeThrough))
        , testCase "shared path: a cast of an enum given by value" (expectShared False False True False (sharedPathProgram [15, 9] [] [] [] [set 16 (M.AsVariant (cp 15) "UpdateOption::Some"), set 5 (M.ReadField (cp 16) "UpdateOption::Some" "ref")] writeThrough))
        , testCase "shared path: a store through a reference makes its target shared" (expectShared True False True False (sharedPathProgram [3, 9] [3] [] ownHolder4 storeCopy writeThrough))
        , testCase "shared path: a store of an own value leaves its target writable" (expectShared False False True False (sharedPathProgram [3, 9] [] [] ownHolder4 storeCopy writeThrough))
        , testCase "shared path: lent for updating through a function value" (expectShared True False True False (sharedPathProgram [3, 9, 23] [3] [] [] [set 5 (M.ReadField (cp 3) "UpdateHolder" "ref")] ([], Just (M.Call (cp 23) [cp 5] (l 7) b1))))
        , testCase "shared path: a loop's back edge that changes only the mark is seen on the next turn" (testAssertEq ["in loans: p may be reached through a shared reference or a parameter lent to be read (&T), so nothing can be changed through it: it cannot be given on"] (markOnlyLoop True))
        , testCase "shared path: the same loop over a parameter given by value stays writable" (testAssertEq [] (markOnlyLoop False))
        , testCase "shared path: a drop writes through what it is given" (testAssertEq [] (checkMoves Set.empty Set.empty (Set.singleton "UpdateHolder") (M.Program declarations Map.empty dropFn generics Map.empty Map.empty Map.empty stdProtocols Nothing)))
        ]
    sharedNames = Map.fromList [(6, "$match"), (5, "p")]
    -- (the holder is a clone, on entry of a parameter given by value and on the back edge of one lent to be read: clones have
    -- no view, and the two parameters have the same loans and no parents, so only the shared-path mark tells the turns apart.
    -- Each turn reads the update reference out and gives it to a call, after which the holder gets its next value.)
    markOnlyLoop lentToRead =
        let ls = [(3, updateHolder), (5, TMutRef TInt), (7, TInt), (9, TBool), (24, updateHolder), (25, updateHolder)]
            decls = Map.fromList [(l n, M.LocalDecl ty (Just (Map.findWithDefault ("v" ++ show n) n sharedNames))) | (n, ty) <- ls]
            giveOn next = M.Call (M.Const (M.CFn "keep")) [mv 5] (l 7) next
            b5 = M.BlockId 5
            blocks =
                [ (b0, M.BasicBlock [set 3 (M.CopyOf (cp 25)), readRefOf 3] (giveOn b5))
                , (b5, M.BasicBlock [set 3 (M.CopyOf (cp 25))] (M.Goto b2))
                , (b2, M.BasicBlock [] (M.SwitchBool (cp 9) b3 b1))
                , (b3, M.BasicBlock [readRefOf 3] (giveOn b4))
                , (b4, M.BasicBlock [set 3 (M.CopyOf (cp 24))] (M.Goto b2))
                , (b1, M.BasicBlock [] M.Unreachable)
                ]
            main = M.Function "loans" (map l [24, 25, 9]) Nothing decls (Map.fromList blocks) [] [] [l 24 | lentToRead] [] [] M.emptySpec
         in checkMoves Set.empty Set.empty Set.empty (M.Program declarations calleeFns main generics Map.empty Map.empty Map.empty stdProtocols Nothing)
    sharedLocals = [(1, TInt), (3, updateHolder), (4, updateHolder), (5, TMutRef TInt), (6, updateHolder), (7, TInt), (8, TRef updateHolder), (9, TBool), (10, TMutRef TInt), (11, TInt), (12, TMutRef TInt), (13, TList updateHolder), (14, TBox updateHolder), (15, updateOption), (16, TVariant "UpdateOption::Some"), (17, TUninit updateHolder), (18, TRef TInt), (19, TMutRef updateHolder), (21, TList updateHolder), (22, updateHolder), (23, TFn [TMutRef TInt] TInt)]
    updateOption = TNamed "UpdateOption" []
    calleeFns = Map.fromList
        [ ("up", (fn "up" [1] (Just TInt) [(0, TInt), (1, TInt)] []){M.fnBorrowed = [l 1], M.fnMutBorrowed = [l 1], M.fnSpec = M.emptySpec{M.specMutParams = ["owner"]}})
        , ("peek", (fn "peek" [1] (Just TInt) [(0, TInt), (1, TInt)] []){M.fnBorrowed = [l 1]})
        , ("keep", fn "keep" [1] (Just TInt) [(0, TInt), (1, TMutRef TInt)] [])
        ]
    sharedPathProgram params borrowed mutBorrowed setup derive (useStmts, call) =
        let decls = Map.fromList [(l n, M.LocalDecl ty (Just (Map.findWithDefault ("v" ++ show n) n sharedNames))) | (n, ty) <- sharedLocals]
            final = derive ++ useStmts
            joined = null setup && 13 `elem` params
            looped = not (null setup) && 13 `elem` params
            nextTurn (Just (M.Call f as d _)) = M.Call f as d b4
            nextTurn _ = M.Goto b4
            blocks
                | looped = [(b0, M.BasicBlock setup (M.Goto b2)), (b2, M.BasicBlock [] (M.SwitchBool (cp 9) b3 b1)), (b3, M.BasicBlock final (nextTurn call)), (b4, M.BasicBlock [set 3 (op M.Get [cp 13, int 0])] (M.Goto b2))]
                | joined = [(b0, M.BasicBlock [] (M.SwitchBool (cp 9) b2 b3)), (b2, M.BasicBlock [set 3 (op M.Get [cp 13, int 0])] (M.Goto b4)), (b3, M.BasicBlock ownHolder3 (M.Goto b4)), (b4, M.BasicBlock final (maybe M.Unreachable id call))]
                | otherwise = [(b0, M.BasicBlock (setup ++ final) (maybe M.Unreachable id call))]
            ends = [(b1, M.BasicBlock [] M.Unreachable)]
            main = (M.Function "loans" (map l params) Nothing decls (Map.fromList (blocks ++ ends)) [] [] (map l borrowed) (map l mutBorrowed) [] M.emptySpec)
         in checkMoves Set.empty Set.empty Set.empty (M.Program declarations calleeFns main generics Map.empty Map.empty Map.empty stdProtocols Nothing)
    b2 = M.BlockId 2
    b3 = M.BlockId 3
    b4 = M.BlockId 4
    ownHolder3 = [set 11 (M.Use (int 0)), set 12 (M.Borrow (l 11) [] True), set 3 (M.MakeData "UpdateHolder" [("ref", mv 12)])]
    ownHolder4 = [set 1 (M.Use (int 0)), set 10 (M.Borrow (l 1) [] True), set 4 (M.MakeData "UpdateHolder" [("ref", mv 10)])]
    holderStates =
        [ ("lent to be read", True, [3, 9], [3], [], [])
        , ("lent for updating", False, [3, 9], [3], [3], [])
        , ("given by value", False, [3, 9], [], [], [])
        , ("of the function's own", False, [9], [], [], ownHolder3)
        , ("read through a shared reference", True, [9], [], [], ownHolder4 ++ [set 8 (M.Borrow (l 4) [] False), set 3 (M.Deref (cp 8))])
        , ("lent on one path only", True, [9, 13], [13], [], [])
        , ("lent on a later turn of a loop", True, [9, 13], [13], [], ownHolder3)
        ]
    readRefOf n = set 5 (M.ReadField (cp n) "UpdateHolder" "ref")
    holderDerivations =
        [ ("a field read", False, [readRefOf 3])
        , ("a copy", False, [set 6 (M.CopyOf (cp 3)), readRefOf 6])
        , ("a match on it", False, [set 6 (M.Use (cp 3)), readRefOf 6])
        , ("a move", True, [set 22 (M.Use (mv 3)), readRefOf 22])
        , ("a Box", True, [set 14 (M.MakeBox (mv 3)), set 22 (M.Unbox (cp 14)), readRefOf 22])
        , ("a list", True, [set 21 (M.MakeList [mv 3]), set 22 (op M.Get [cp 21, int 0]), readRefOf 22])
        , ("an Uninit", True, [set 17 (op M.UninitNew [mv 3]), set 22 (op M.UninitGet [cp 17]), readRefOf 22])
        ]
    writeThrough = ([M.AssignRef (l 5) [] (M.Use (int 7))], Nothing)
    referenceUses =
        [ ("written through", True, False, writeThrough)
        , ("reborrowed for updating", True, False, ([set 10 (M.Borrow (l 5) [] True)], Nothing))
        , ("lent to an update parameter", True, False, ([], Just (M.Call (M.Const (M.CFn "up")) [cp 5] (l 7) b1)))
        , ("given to a call by value", True, True, ([], Just (M.Call (M.Const (M.CFn "keep")) [mv 5] (l 7) b1)))
        , ("put into a value", True, True, ([set 22 (M.MakeData "UpdateHolder" [("ref", mv 5)])], Nothing))
        , ("read through", False, False, ([set 7 (M.Deref (cp 5))], Nothing))
        , ("reborrowed to be read", False, False, ([set 18 (M.Borrow (l 5) [] False)], Nothing))
        , ("lent to a parameter lent to be read", False, False, ([], Just (M.Call (M.Const (M.CFn "peek")) [cp 5] (l 7) b1)))
        ]
    storeCopy = [set 19 (M.Borrow (l 4) [] True), M.AssignRef (l 19) [] (M.CopyOf (cp 3)), readRefOf 4]
    readOnlyText = "so nothing can be changed through it"
    -- (a move out of a lent parameter or a view of one is refused by the move rules whether or not it is shared; rule 6 adds
    -- the refusal where they do not see the shared path, and the refusals of what does not move)
    expectShared shared moving mutating consumes es
        | shared && (moving || consumes) = if null es then Just "Expected a refusal of a move out of a shared path" else Nothing
        | shared && mutating = requireError readOnlyText es
        | any (isInfixOf readOnlyText) es = Just ("Unexpected rule 6 refusal: " ++ show es)
        | moving = Nothing
        | otherwise = testAssertEq [] es
    dropFn =
        let name = "<UpdateHolder as Drop>::drop"
            decls = Map.fromList [(l 0, M.LocalDecl TInt Nothing), (l 1, M.LocalDecl updateHolder (Just "self")), (l 5, M.LocalDecl (TMutRef TInt) (Just "p"))]
         in M.Function name [l 1] (Just TInt) decls (Map.fromList [(b0, M.BasicBlock [readRefOf 1, M.AssignRef (l 5) [] (M.Use (int 0)), set 0 (M.Use (int 0))] M.Unreachable)]) [] [] [] [] [] M.emptySpec
    foreignCase ret args expected =
        let foreignFn = fn externName (map fst args) (Just ret) ((0, ret) : args) []
            es = check (map fst args) (Map.singleton externName foreignFn) ((4, ret) : args)
                [(b0, M.BasicBlock [] (M.Call (M.Const (M.CFn externName)) (map (mv . fst) args) (l 4) b1)), (b1, M.BasicBlock (if ret == block then [set 4 (op M.AddrFree [int 0, mv 4])] else []) M.Unreachable)]
         in maybe (testAssertEq es []) (`requireError` es) expected
    foreignValue viaStore =
        let sig = TFn [] block
            value = M.Use (M.Const (M.CFn externName))
            ls = [(3, TMutRef sig), (4, sig)]
            action = if viaStore then M.AssignRef (l 3) [] value else set 4 value
         in requireError "importSlots is an extern fn that gives a value that can hold a reference, so it cannot be used as a value" $
            check [] (Map.singleton externName (fn externName [] (Just block) [(0, block)] [])) ls (end [action])
    slotGuard ty = requireError "Addr::get cannot read a slot that may hold an update reference yet" (slotErrors ty)
    slotErrors ty =
        check [3] Map.empty [(3, TBlock ty), (4, ty), (6, TInt)] (end [set 4 (op M.AddrGet [int 0, int 0, cp 3]), set 6 (op M.AddrFree [int 0, mv 3])])

permissionCases :: Test
permissionCases = TestList "loans in permissions and at calls"
    [ testCase "a copy of the shared slot reference outlives the permission" (pipelineRuns "x = 12; (p, b) = Addr::alloc(1); b = Addr::write(p, 0, &x, b); r = Addr::get(p, 0, b); b = Addr::dropValue(p, 0, b); d = Addr::free(p, b); return *r + d;" (VInt 12))
    , testCase "take a mutable slot before updating it" (pipelineRuns "x = 3; (p, b) = Addr::alloc(1); b = Addr::write(p, 0, &mut x, b); (r, b) = Addr::take(p, 0, b); d = Addr::free(p, b); *r = 8; return x + d;" (VInt 8))
    , testCase "the validator forgets an old pointee fact after a slot is taken and updated" (pipelineRejected "x = 3; (p, b) = Addr::alloc(1); b = Addr::write(p, 0, &mut x, b); (r, b) = Addr::take(p, 0, b); d = Addr::free(p, b); *r = 8; affirm x = 3; return x + d;" "Could not prove: x = 3")
    , testCase "a write through another permission's taken reference validates and runs" (pipelineRuns "x = 4; y = 2; (p, b) = Addr::alloc(1); b = Addr::write(p, 0, &x, b); (q, c) = Addr::alloc(1); c = Addr::write(q, 0, &mut y, c); (u, c) = Addr::take(q, 0, c); k = Addr::free(q, c); *u = 3; affirm base(b) = p; (r, b) = Addr::take(p, 0, b); d = Addr::free(p, b); return *r + y + k + d;" (VInt 7))
    , testCase "a bound call without from keeps the storage it lends" (pipelineRejected "fn g<S: Sequence<Int>>(s: S) -> Int [{ affirm size(s) > 0; }] [{ }] { r = s.getRef(0); t = s; return *r + size(t); }; l = push(push([], 4), 5); return g(l);" "s is borrowed by r, so it cannot be moved while that borrow is live")
    , testCase "a bridge holder with no declaration is conservatively reference-bearing" undeclaredBridgeHolder
    , testCase "a nongeneric user struct named Box stays distinct from builtin Box<T>" (parseEvalProgramHelper "struct Box { item: Int }; b = Box { item: 8 }; return b.item;" (Just (VInt 8)))
    , testCase "primitive list and Box operations keep scalar behavior" (pipelineRuns "xs = push([], 4); b = Box::new(7); return first(xs) + Box::unbox(b);" (VInt 11))
    , testCase "a no-argument function can return a function value" (pipelineRuns "fn dbl(n: Int) -> Int { return n * 2; }; fn pick() -> fn(Int) -> Int { return dbl; }; g = pick(); return g(4);" (VInt 8))
    ]

undeclaredBridgeHolder :: TestResult
undeclaredBridgeHolder = case lowerSource True source of
    Error e -> Just e
    Ok program -> case validateCompiled program of
        Error e -> Just ("Refused with the declaration: " ++ e)
        Ok () -> case validateCompiled program{M.progTypes = Map.delete "S" (M.progTypes program)} of
            Ok () -> Just "validated after removing the holder's declaration"
            Error _ -> Nothing
  where
    source = "struct S { n: Int }; fn f(c: Int) -> Int { x = 1; s = S { n: 5 }; rs = push([], &mut x); p = get(rs, 0); *p = 2; affirm s.n = 5; return s.n + x; }; return f(1);"
