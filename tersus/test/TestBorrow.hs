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
                , testCase "a struct can hold a value that holds references" (runs "struct Window { first: &Int, last: &Int }; struct Outer { w: Window, n: Int }; xs = [10, 20, 30]; w = Window { first: &get(xs, 0), last: &get(xs, 2) }; o = Outer { w: w, n: 1 }; f = o.w.first; return *f + o.n;" (VInt 11))
                , testCase "a value that holds references can be given to a function" (runs "struct Window { first: &Int, last: &Int }; fn total(w: Window) -> Int { f = w.first; return *f; }; xs = [10, 20, 30]; w = Window { first: &get(xs, 0), last: &get(xs, 2) }; return total(w);" (VInt 10))
                , testCase "and put in a list" (runs "struct Window { first: &Int, last: &Int }; xs = [10, 20, 30]; w = Window { first: &get(xs, 0), last: &get(xs, 2) }; ws = push([], w); w0 = get(ws, 0); f = w0.first; return *f + size(ws);" (VInt 11))
                , testCase "a clone of a holder holds its references too" (rejected "trait Clone { }; struct S { r: &Int }; impl Clone for S { }; x = 1; s = S { r: &x }; t = clone(s); x = 2; f = t.r; return *f;" "cannot be assigned while it is borrowed")
                , testCase "a holder made in the function is returned from what its fields are from" (runs "struct S { r: &Int }; fn f(x: &Int) -> S from x { s = S { r: &x }; return s; }; x = 3; w = f(x); g = w.r; return *g;" (VInt 3))
                , testCase "an ordinary field is not an origin" (runs "struct S { r: &Int, n: Int }; fn f(x: &Int) -> S from x { n = 1; return S { r: &x, n: n }; }; x = 3; w = f(x); g = w.r; return *g + w.n;" (VInt 4))
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
                , testCase "no update borrow of what a read borrow is to" (rejected "x = 4; r = &x; s = &mut *r; *s = 5; return x;" "cannot be made through a read reference")
                ]
            ]
