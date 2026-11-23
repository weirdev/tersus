module TestPointers (testPointers) where

import Data.List (intercalate, isInfixOf)

import Cli (Command (..), runSource)
import Pipeline (assumptionsOf)
import TestHarness
import Utils

-- Tuples, addresses and permissions (POINTERS.md, LANGUAGE.md): what a program that manages memory by hand gives when it runs, and the
-- program refused for each thing that the contracts of the operations and the linear check of permissions rule out. A program here goes
-- through the whole pipeline (the checker, the moves, the validator, the erasure of permissions and the executor of the MIR); native code
-- runs `examples/addresses.tersus` (TestNative), and both emitters write the same IR for it (TestMirEmit).
testPointers :: Test
testPointers =
    let thirtyTwo = intercalate ", " (map show [1 .. 32 :: Int])
     in
    TestList
        "testPointers"
        [ TestList
            "tuples"
            [ testCase "a tuple is made and read" (runs "t = (1, true); if t.1 { return t.0; }; return 0;" "1")
            , testCase "a tuple is taken apart" (runs "(a, b) = (3, 4); return a * 10 + b;" "34")
            , testCase "a function returns two values" (runs "fn qr(a: Int, b: Int) -> (Int, Int) [{ affirm b > 0; }] [{ affirm return.0 = a / b; }] { return (a / b, a % b); }; (q, r) = qr(17, 5); return q * 10 + r;" "32")
            , testCase "the parts of a tuple are moved on their own" (runs "fn two() -> (List<Int>, List<Int>) { return (push([], 1), push(push([], 2), 3)); }; (a, b) = two(); c = push(b, 4); return size(a) + size(c);" "4")
            , testCase "a tuple of Copy parts is Copy" (runs "t = (1, 2); u = t; return t.0 + u.1;" "3")
            , testCase "a tuple in a tuple" (runs "t = (1, (2, 3)); return t.1.1;" "3")
            , testCase "the contract of a part" (valid "fn f(n: Int) -> (Int, Int) [{ }] [{ affirm return.0 = n; affirm return.1 = n + 1; }] { return (n, n + 1); }; (a, b) = f(4); affirm b = a + 1; return b;")
            , testCase "a part used after it was moved" (rejected "(a, b) = (push([], 1), push([], 2)); c = a; return size(a);" "a was moved")
            , testCase "parentheses around a type only group" (runs "fn f(t: (Int)) -> (Int) { return t + 1; }; return f(4);" "5")
            , testCase "parentheses around a value only group" (runs "x = (3); return (x) * 2;" "6")
            , testCase "a tuple of one part is written with a trailing comma" (runs "fn f(n: Int) -> (Int,) { return (n + 1,); }; t = f(4); return t.0;" "5")
            , testCase "a tuple of one part is taken apart with a trailing comma" (runs "(a,) = (7,); return a;" "7")
            , testCase "a tuple of one part is not taken apart without the comma" (rejected "(a) = (7,); return a;" "taken apart as (x,)")
            , testCase "the empty tuple" (runs "fn f() -> () { return (); }; t = f(); u = (); return 1;" "1")
            , testCase "a trailing comma after two parts" (runs "fn f() -> (Int, Int,) { return (1, 2,); }; (a, b,) = f(); return a * 10 + b;" "12")
            , testCase "a tuple of 32 parts" (runs ("t = (" ++ thirtyTwo ++ "); return t.31;") "32")
            , testCase "a tuple of 33 parts is refused" (rejected ("t = (" ++ thirtyTwo ++ ", 33); return 0;") "at most 32 parts")
            , testCase "a contract on a one-part tuple" (valid "fn f(n: Int) -> (Int,) [{ }] [{ affirm return.0 = n; }] { return (n,); }; (a,) = f(4); affirm a = 4; return a;")
            , testCase "the name of the struct of tuples is the language's" (rejected "struct Tuple2<A, B> { x: A, y: B }; return 0;" "builtin type")
            ]
        , TestList
            "memory"
            [ testCase "write, read, take, drop and free" (runs memory "30")
            , testCase "an address is offset" (runs "(p, b) = Addr::alloc(3); q = Addr::offset(p, 2); b = Addr::write(p, 2, 7, b); x = Addr::get(p, 2, b); b = Addr::dropValue(p, 2, b); return x + Addr::free(p, b) + Addr::toInt(Addr::offset(q, 0 - 2)) - Addr::toInt(p);" "7")
            , testCase "the null address" (runs "p = Addr::null(); q = Addr::fromInt(0); return Addr::toInt(p) + Addr::toInt(q);" "0")
            , testCase "memory is resized" (runs resized "11")
            , testCase "values that own something" (runs owning "5")
            -- (a read reached back through three writes: the value written there, never another)
            , testCase "a read after a chain of writes gives what was written there" (valid (chain "10"))
            , testCase "a read after a chain of writes is not what a later write put elsewhere" (rejected (chain "20") "Could not prove: x = 20")
            , testCase "a block is split and joined" (runs splitJoin "7")
            , testCase "a permission in a struct" (runs buffer "0")
            , testCase "a function takes a block and gives it back" (runs giveBack "9")
            , testCase "a function is lent a block" (runs lent "6")
            , testCase "a block of one type as another" (runs "struct Two { a: I32, b: I32 }; impl Clone for Two { }; impl Copy for Two { }; (p, b) = Addr::alloc(2); c = Block::cast(b); q = Addr::cast(p); c = Addr::write(q, 0, Two { a: -1, b: 2 }, c); x = Addr::get(q, 0, c); c = Addr::dropValue(q, 0, c); d = Addr::free(q, c); return toInt(x.a) + toInt(x.b);" "1")
            , testCase "a block of slots of another size" (rejected "(p, b) = Addr::alloc(2); c = Block::cast(b); q = Addr::cast(p); c = Addr::write(q, 0, true, c); c = Addr::dropValue(q, 0, c); return Addr::free(q, c);" "are not the same size")
            , testCase "the permission to memory the program did not allocate is an assumption" (valid "p = Addr::fromInt(4096); b = Block::assume(p, 2); b = Addr::write(p, 0, 5, b); b = Addr::dropValue(p, 0, b); return Addr::free(p, b);")
            , testCase "an emptied slot is known empty" (valid "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); b = Addr::dropValue(p, 0, b); affirm filled(b, 0) = false; return Addr::free(p, b);")
            -- (what a function that only allocates gives is still one value a
            -- proof may name, unlike what the world gives)
            , testCase "a proof names a function that allocates" (valid "fn f() -> Int { (p, b) = Addr::alloc(1); x = Addr::free(p, b); return x; }; affirm f() = f(); return 0;")
            , testCase "a Vec on an address" (runs vec "1")
            ]
        , TestList
            "refused"
            [ TestList "permission refusals by invariant" [ testCase name (rejected source expected) | (name, source, expected) <- permissionRefusals ]
            ]
        , TestList
            "linear types"
            [ testCase "a linear value is used by its impl" (runs (handle ++ "h = Handle::open(3); return h.close();") "3")
            , testCase "a linear value given on" (runs (handle ++ "fn pass(h: Handle) -> Handle { return h; }; h = pass(Handle::open(4)); return h.close();") "4")
            , testCase "a linear value in a struct" (runs (handle ++ "struct Two { a: Handle, n: Int }; t = Two { a: Handle::open(1), n: 2 }; return t.a.close() + t.n;") "3")
            , testCase "a linear enum" (runs "linear enum Token { Some { n: Int }, None }; impl Token { fn spend(self: Self) -> Int { return match self { Token::Some { n: n } => n, Token::None => 0 }; }; }; t = Token::Some { n: 5 }; return t.spend();" "5")
            , testCase "a linear value that is not used" (rejected (handle ++ "h = Handle::open(3); return 0;") "h is a value of a linear type given at line")
            , testCase "a linear value used twice" (rejected (handle ++ "h = Handle::open(3); a = h.close(); return a + h.close();") "h was moved")
            , testCase "a linear value taken apart outside its impl" (rejected (handle ++ "h = Handle::open(3); return h.fd;") "h is a value of a linear type")
            , testCase "a linear value in a struct that is not used" (rejected (handle ++ "struct Two { a: Handle, n: Int }; t = Two { a: Handle::open(1), n: 2 }; return t.n;") "t.a is a value of a linear type (in t)")
            , testCase "a linear type is not copied" (rejected (handle ++ "impl Clone for Handle { }; return 0;") "Handle is linear")
            , testCase "a list of linear values" (rejected (handle ++ "fn f(l: List<Handle>) -> Int { return 0; }; return 0;") "a list cannot hold Handle")
            , testCase "linear before something else" (rejected "linear fn f() -> Int { return 0; }; return 0;" "Parse error")
            ]
        , TestList
            "uninit and replace"
            [ testCase "an array of slots that may hold nothing" (runs "a = array(3, Uninit::empty()); a = set(a, 1, Uninit::new(7)); u = get(a, 1); affirm filled(u) = true; return Uninit::get(u);" "7")
            , testCase "Array::uninit" (runs "a = Array::uninit(4); a = set(a, 3, Uninit::new(true)); u = get(a, 3); if Uninit::get(u) { return 1; }; return 0;" "1")
            , testCase "a value that owns something is taken out" (runs "u = Uninit::new(push(push([], 1), 2)); l = Uninit::take(u); return size(l);" "2")
            , testCase "an empty Uninit is discarded" (runs "u = Uninit::empty(); return Uninit::discard(u) + 1;" "1")
            , testCase "what an Uninit holds is known" (valid "u = Uninit::new(5); affirm filled(u) = true; affirm at(u) = 5; x = Uninit::get(u); affirm x = 5; return x;")
            , testCase "replace gives the element that was there" (runs "(l, old) = replace(push(push([], 1), 2), 0, 9); affirm old = 1; return get(l, 0) * 10 + old;" "91")
            , testCase "replace on an array" (runs "(a, old) = replace(#[4, 5, 6], 2, 0); return old + get(a, 2);" "6")
            , testCase "a read of an empty Uninit" (rejected "u = Uninit::empty(); return Uninit::get(u);" "Could not prove: filled(u) = true")
            , testCase "a discard of a filled Uninit" (rejected "u = Uninit::new(1); return Uninit::discard(u);" "Could not prove: filled(u) = false")
            , testCase "an Uninit of a value that owns something is linear" (rejected "u = Uninit::new(push([], 1)); return 0;" "u is a value of a linear type")
            , testCase "it is not copied" (rejected "u = Uninit::new(push([], 1)); v = clone(u); l = Uninit::take(u); return size(l);" "it is not copied")
            , testCase "an Uninit is not compared" (rejected "u = Uninit::new(1); v = Uninit::new(1); return u = v;" "an Uninit cannot be compared")
            , testCase "a view of an Uninit after it was taken" (rejected "u = Uninit::new(push([], 1)); x = Uninit::get(u); l = Uninit::take(u); return size(x);" "u was moved")
            ]
        , TestList
            "extern functions"
            [ testCase "an extern function is assumed to keep its contract" (valid "extern fn labs(x: Int) -> Int [{ }] [{ affirm return >= 0; }]; a = labs(0 - 3); affirm a >= 0; return a;")
            , testCase "its input contract is checked" (rejected "extern fn half(x: Int) -> Int [{ affirm x > 0; }] [{ }]; return half(0);" "Could not prove: x > 0")
            , testCase "the interpreter does not run C" (testAssertErrorContains "is a function of C" (runSource Interpret "extern fn labs(x: Int) -> Int [{ }] [{ }]; return labs(1);"))
            , testCase "it takes words" (rejected "extern fn f(l: List<Int>) -> Int [{ }] [{ }]; return 0;" "is not an Int, a Byte, a Bool, an address or a permission")
            , testCase "it is an assumption" (testAssertEq (runSource Assumptions "extern fn labs(x: Int) -> Int [{ }] [{ }];\nreturn labs(1);") (Ok "line 1:1: extern fn labs"))
            ]
        , TestList
            "drops"
            [ testCase "a value with a drop is dropped where it goes out of scope" (runs (dropper ++ "v = V::new(3); w = V::new(4); return v.n + w.n;") "7")
            , testCase "a type that holds a permission and has a drop is not linear" (valid (dropper ++ "fn f() -> Int { v = V::new(2); return 1; }; return f();"))
            , testCase "a type that holds a permission and has no drop is linear" (rejected (owner ++ "v = V::new(3); return v.n;") "that is not used")
            , testCase "a value is taken apart without its drop" (runs (dropper ++ "v = V::new(3); V { addr: a, n: k, blk: b } = v; return Addr::free(a, b) + k;") "3")
            , testCase "what a value taken apart holds is used" (rejected (dropper ++ "v = V::new(3); V { addr: a, n: k, blk: b } = v; return k;") "b is a permission")
            , testCase "a value with a drop in a struct, an enum, a list and a box" (runs (dropper ++ "struct W { v: V, k: Int }; enum E { A { v: V }, B { k: Int } }; w = W { v: V::new(2), k: 5 }; e = E::A { v: V::new(2) }; l = push(push([], V::new(1)), V::new(2)); b = Box::new(V::new(3)); return w.k + size(l);") "7")
            , testCase "a generic drop" (runs "struct G<T> { addr: Addr<T>, ghost blk: Block<T> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; }]; impl<T> Drop for G<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> G<T> { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, blk: b }; }; }; fn one(x: G<Int>) -> Int { return 1; }; fn other(y: G<Bool>) -> Int { return 1; }; return one(G::new()) + other(G::new());" "2")
            , testCase "a permission moved out of a value with a drop" (rejected (dropper ++ "v = V::new(3); b = v.blk; return Addr::free(v.addr, b);") "which has a drop that would free the memory again")
            , testCase "a list moved out of a value with a drop" (rejected (holder ++ "fn eat(l: List<Int>) -> Int { return size(l); }; fn g(h: H) -> Int { ys = h.xs; return eat(ys); }; return g(H::new());") "cannot move ys (h.xs) out of a value of H, whose drop is given the whole value")
            , testCase "a list read or cloned out of a value with a drop" (runs (holder ++ "fn g(h: H) -> Int { ys = clone(h.xs); return size(ys) + size(h.xs); }; return g(H::new());") "4")
            , testCase "a field of a value with a drop nested in a struct" (rejected (nested ++ "struct O { g: G, n: Int }; fn f(o: O) -> Int { x = o.g.h; return eat(x); }; return f(O { g: G::new(), n: 1 });") "cannot move x (o.g.h) out of a value of G, whose drop is given the whole value")
            , testCase "a field of a value with a drop in a tuple" (rejected (nested ++ "fn eatList(l: List<Int>) -> Int { return size(l); }; fn f(t: (H, Int)) -> Int { x = t.0.xs; return eatList(x); }; return f((H::new(), 1));") "out of a value of H, whose drop is given the whole value")
            , testCase "a field of a value with a drop bound by a match" (rejected (nested ++ "enum E { A { g: G }, B }; fn f(e: E) -> Int { return match e { E::A { g: w } => eat(w.h), E::B => 0 }; }; return f(E::A { g: G::new() });") "out of a value of G, whose drop is given the whole value")
            , testCase "a field of a value with a drop in a Box" (rejected (nested ++ "struct O { b: Box<G> }; fn f(o: O) -> Int { x = o.b.h; return eat(x); }; return f(O { b: Box::new(G::new()) });") "cannot move x (o.b.h) out of a value of G, whose drop is given the whole value")
            , testCase "a value looked at is given another value" (rejected (nested ++ "fn f(g: G) -> Int { h = g.h; g = G::new(); return size(h.xs); }; return f(G::new());") "g is given another value here while h still looks at g.h, which holds a value with a drop and cannot be copied")
            , testCase "a value looked at is updated" (rejected (nested ++ "struct O { g: G, n: Int }; fn f(o: O) -> Int { h = o.g.h; o = O { n: 2, ..o }; return size(h.xs) + o.n; }; return f(O { g: G::new(), n: 1 });") "o.g is moved here while h still looks at o.g.h")
            , testCase "a value looked at is moved" (rejected (nested ++ "fn keep(g: G) -> Int { return 1; }; fn f(g: G) -> Int { h = g.h; n = keep(g); return n + size(h.xs); }; return f(G::new());") "g is moved here while h still looks at g.h")
            , testCase "a value looked at is lent for updating" (rejected (nested ++ "fn bump(g: &mut G) -> Int { return 0; }; fn f(g: G) -> Int { h = g.h; n = bump(&mut g); return n + size(h.xs); }; return f(G::new());") "g is lent for updating here while h still looks at g.h")
            , testCase "a part moved out of a value whose rest is looked at" (rejected (nested ++ "struct P { v: H, n: Int }; struct O { p: P }; fn f(o: O) -> Int { p = o.p; v = p.v; return eat(v) + p.n; }; return f(O { p: P { v: H::new(), n: 1 } });") "o.p.v is moved here while p still looks at o.p")
            , testCase "a look at a value with a drop given a value elsewhere" (rejected (nested ++ "fn f(g: G, k: G, c: Bool) -> Int { h = g.h; if c { h = k.h; }; return size(h.xs); }; return f(G::new(), G::new(), true);") "h looks at g.h, which holds a value with a drop, and is given a value elsewhere too")
            , testCase "a look at a value with a drop given a value of its own later" (rejected (nested ++ "struct O { g: G, n: Int }; fn f(o: O) -> Int { g = o.g; n = size(g.h.xs); g = G::new(); return n + size(g.h.xs) + o.n; }; return f(O { g: G::new(), n: 1 });") "g looks at o.g, which holds a value with a drop, and is given a value elsewhere too")
            , testCase "a look into a Box of a value with a drop whose owner changes" (rejected (nested ++ "struct L { addr: Addr<Int>, ks: List<H>, bk: Box<H>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl Drop for L { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl L { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, ks: push(push([], H::new()), H::new()), bk: Box::new(H::new()), blk: b }; }; }; fn tot(ks: &List<H>) -> Int { return size(ks); }; " ++ "fn f(l: L, l2: L) -> Int { v = l.bk; l = l2; return size(v.xs); }; return f(L::new(), L::new());") "l is given another value here while v still looks at l.bk, which holds a value with a drop")
            , testCase "a look into a list of values with a drop whose owner changes" (rejected (nested ++ "struct L { addr: Addr<Int>, ks: List<H>, bk: Box<H>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl Drop for L { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl L { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, ks: push(push([], H::new()), H::new()), bk: Box::new(H::new()), blk: b }; }; }; fn tot(ks: &List<H>) -> Int { return size(ks); }; " ++ "fn f(l: L, l2: L) -> Int { v = l.ks; l = l2; return tot(v); }; return f(L::new(), L::new());") "l is given another value here while v still looks at l.ks, which holds a value with a drop")
            , testCase "a look into a value with a drop whose owner changes, concretely" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "fn f(w: W<H>, w2: W<H>) -> Int { v = w.x; w = w2; return v.sz(); }; return f(W::new(H::new()), W::new(H::new()));") "w is given another value here while v still looks at w.x")
            , testCase "a look through a call's reference result from two arguments whose owner changes" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "fn pick(a: &W<H>, b: &W<H>, c: Bool) -> &H from (a, b) { if c { return &a.x; }; return &b.x; }; fn f(o: W<H>, p: W<H>, p2: W<H>) -> Int { r = pick(&o, &p, false); v = *r; p = p2; return v.sz(); }; return f(W::new(H::new()), W::new(H::new()), W::new(H::new()));") "p is given another value here while v still looks at")
            , testCase "a look through a reference held in a struct whose owner changes" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "struct R { r: &W<H> }; fn f(o: W<H>, o2: W<H>) -> Int { h = R { r: &o }; v = (*h.r).x; o = o2; return v.sz(); }; return f(W::new(H::new()), W::new(H::new()));") "o is given another value here while v still looks at o.x")
            , testCase "a look through a reborrow whose owner changes" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "fn f(o: W<H>, o2: W<H>) -> Int { r = &o; q = &*r; v = (*q).x; o = o2; return v.sz(); }; return f(W::new(H::new()), W::new(H::new()));") "o is given another value here while v still looks at o.x")
            , testCase "a look through a reference whose owner changes" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "fn f(o: W<H>, o2: W<H>) -> Int { r = &o; v = (*r).x; o = o2; return v.sz(); }; return f(W::new(H::new()), W::new(H::new()));") "o is given another value here while v still looks at o.x")
            , testCase "a look through a call's reference result whose owner changes" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "fn xr(w: &W<H>) -> &H from w { return &w.x; }; fn f(o: W<H>, o2: W<H>) -> Int { r = xr(&o); v = *r; o = o2; return v.sz(); }; return f(W::new(H::new()), W::new(H::new()));") "o is given another value here while v still looks at")
            , testCase "a look through a generic call's reference result whose owner changes" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "fn xr<T>(w: &W<T>) -> &T from w { return &w.x; }; fn f(o: W<H>, o2: W<H>) -> Int { r = xr(&o); v = *r; o = o2; return v.sz(); }; return f(W::new(H::new()), W::new(H::new()));") "o is given another value here while v still looks at")
            , testCase "a look at an instance whose Clone needs its argument's, whose owner changes" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "struct V<T> { x: T, n: Int }; impl<T: Clone> Clone for V<T> { }; " ++ "fn f(w: W<V<H>>, w2: W<V<H>>) -> Int { v = w.x; w = w2; return v.n + size(v.x.xs); }; k = clone(V { x: 1, n: 2 }); return f(W::new(V { x: H::new(), n: 3 }), W::new(V { x: H::new(), n: 4 })) + k.n;") "w is given another value here while v still looks at w.x")
            , testCase "a look at a value with a drop nine Boxes deep whose owner changes" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "struct D { b: Box<Box<Box<Box<Box<Box<Box<Box<Box<H>>>>>>>>>, n: Int }; fn f(w: W<D>, w2: W<D>) -> Int { v = w.x; w = w2; return v.n; }; fn mk() -> D { return D { b: Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(H::new()))))))))), n: 2 }; }; return f(W::new(mk()), W::new(mk()));") "w is given another value here while v still looks at w.x")
            , testCase "a look at a part of a look whose owner changes" (rejected (nested ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; " ++ "struct A { x: H, n: Int }; fn f(w: W<A>, w2: W<A>) -> Int { a = w.x; v = a.x; w = w2; return v.sz(); }; return f(W::new(A { x: H::new(), n: 1 }), W::new(A { x: H::new(), n: 2 }));") "w is given another value here while v still looks at w.x.x")
            , testCase "a look assigned to a parameter" (rejected (nested ++ "fn f(g: G, h: H) -> Int { h = g.h; return size(h.xs); }; return f(G::new(), H::new());") "h looks at g.h, which holds a value with a drop, and is given a value elsewhere too")
            , testCase "a look assigned to a parameter in a branch" (rejected (nested ++ "fn f(g: G, h: H, c: Bool) -> Int { if c { h = g.h; }; return size(h.xs); }; return f(G::new(), H::new(), true);") "h looks at g.h, which holds a value with a drop, and is given a value elsewhere too")
            , testCase "a look into a tuple whose owner changes" (rejected (nested ++ "fn f(t: (G, Int), u: (G, Int)) -> Int { h = t.0.h; t = u; return size(h.xs); }; return f((G::new(), 1), (G::new(), 2));") "t is given another value here while h still looks at t.0.h")
            , testCase "a look whose owner changes on the next turn of a loop" (rejected (nested ++ "fn f(g: G) -> Int { h = g.h; t = 0; i = 0; while i < 3 [{ affirm i >= 0; }] shrinks 3 - i { t = t + size(h.xs); g = G::new(); i = i + 1; }; return t; }; return f(G::new());") "g is given another value here while h still looks at g.h")
            , testCase "a look into a Box that is moved" (rejected (nested ++ "fn keep(b: Box<G>) -> Int { return 1; }; fn f(b: Box<G>) -> Int { h = b.h; n = keep(b); return n + size(h.xs); }; return f(Box::new(G::new()));") "b is moved here while h still looks at b.h")
            , testCase "a list taken out of a value with a drop that is taken apart" (runs (holder ++ "fn g(h: H) -> Int { H { addr: a, xs: ys, blk: b } = h; return Addr::free(a, b) + size(ys); }; return g(H::new());") "2")
            , testCase "a permission in a value that is lent is not used up" (rejected (dropper ++ "fn f(v: &V) -> Int { return Addr::free(v.addr, v.blk); }; v = V::new(2); return f(v);") "is a permission in a value that is lent (&T) to this function")
            , testCase "a drop uses a permission once" (rejected (owner ++ "impl Drop for V { fn drop(self: Self) -> Int { d = Addr::free(self.addr, self.blk); return d + Addr::free(self.addr, self.blk); }; }; v = V::new(2); return v.n;") "self.blk was moved")
            , testCase "a type is recursive through an address, as through a Box" (runs "struct Node { v: Int, next: Addr<Node> }; enum T { Leaf, Node { l: Addr<T>, v: Int } }; n = Node { v: 1, next: Addr::null() }; return n.v;" "1")
            , testCase "a type with a drop holds a permission" (rejected "struct H { n: Int }; impl Drop for H { fn drop(self: Self) -> Int { return self.n; }; }; return 1;" "H holds no permission")
            , testCase "a drop is not called by the program" (rejected (dropper ++ "v = V::new(3); return v.drop();") "is a drop, which is called where a value goes out of scope")
            , testCase "a drop of the wrong type" (rejected (owner ++ "impl Drop for V { fn drop(self: Self) -> Bool { return true; }; }; return 0;") "but Drop declares fn(V) -> Int")
            , testCase "a value with a drop is not copied" (rejected (dropper ++ "impl Clone for V { }; return 0;") "V has a drop")
            ]
        , TestList
            "assumptions"
            [ testCase "assume gives a fact" (valid "fn f(x: Int) -> Int [{ }] [{ affirm return > 0; }] { assume x > 0; return x; }; return f(1);")
            , testCase "the assumptions of a program are listed" (testAssertEq (assumptionsOf "assume 1 > 0;\nfn f(n: Int) -> Int { assume n = n; return n; };\n(p, b) = Addr::alloc(1);\nc = Block::assume(p, 0);\naxiom twice(x) [{ }] [{ affirm x + x = 2 * x; }];\nd = Addr::free(p, b);\nreturn d;") (Ok ["line 1:1: assume 1 > 0", "line 2:23: assume n = n", "line 4:1: Block::assume(p, 0)", "line 5:1: axiom twice(x)"]))
            , testCase "none" (testAssertEq (runSource Assumptions "return 1;") (Ok "No assumptions"))
            , testCase "each assumption of a permission is a permission of its own" (rejected "p = Addr::fromInt(4096); b1 = Block::assume(p, 2); b2 = Block::assume(p, 2); affirm origin(b1) = origin(b2); x = Addr::free(p, b1); return x + Addr::free(p, b2);" "Could not prove: origin(b1) = origin(b2)")
            ]
        ]
  where
    runs source expected = testAssertEq (runSource Interpret source) (Ok expected)
    valid source = case runSource Check source of
        Ok _ -> Nothing
        Error e -> Just ("Expected the program to validate, but: " ++ e)
    -- (the validator written in Tersus gives its own failure messages:
    -- what is checked here is the refusal, as in TestHarness)
    rejected source expected = case runSource Check source of
        Ok _ -> Just "Expected the program to be refused"
        Error e -> if expected `isInfixOf` e then Nothing else Just ("Expected failure containing: " ++ show expected ++ "\nGot: " ++ e)
    permissionRefusals =
        [ ("a read of an empty slot", "(p, b) = Addr::alloc(2); x = Addr::get(p, 1, b); d = Addr::free(p, b); return x;", "Could not prove: filled(b, i) = true")
        , ("a write over a filled slot", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 1, b); b = Addr::write(p, 0, 2, b); b = Addr::dropValue(p, 0, b); return Addr::free(p, b);", "Could not prove: filled(b, i) = false")
        , ("a slot out of bounds", "(p, b) = Addr::alloc(2); b = Addr::write(p, 2, 1, b); b = Addr::dropValue(p, 2, b); return Addr::free(p, b);", "Could not prove: i < cap(b)")
        , ("a negative slot", "(p, b) = Addr::alloc(2); b = Addr::write(p, 0 - 1, 1, b); b = Addr::dropValue(p, 0 - 1, b); return Addr::free(p, b);", "Could not prove: i >= 0")
        , ("the permission of one block with the address of another", "(p, b) = Addr::alloc(1); (q, c) = Addr::alloc(1); b = Addr::write(q, 0, 1, b); b = Addr::dropValue(p, 0, b); d = Addr::free(p, b); return d + Addr::free(q, c);", "Could not prove: base(b) = p")
        , ("an old address after a resize", "(p, b) = Addr::alloc(1); (q, b) = Addr::resize(p, 2, b); b = Addr::write(p, 0, 1, b); b = Addr::dropValue(q, 0, b); return Addr::free(q, b);", "Could not prove: base(b) = p")
        , ("a free of a part of an allocation", "(p, b) = Addr::alloc(4); (lo, hi) = Block::split(b, 2); d = Addr::free(p, lo); return d + Addr::free(Addr::offset(p, 2), hi);", "Could not prove: cap(b) = extent(origin(b))")
        , ("a join of blocks from two allocations", "(p, b) = Addr::alloc(2); (q, c) = Addr::alloc(2); r = Block::join(b, c); return Addr::free(p, r);", "Could not prove: origin(lo) = origin(hi)")
        , ("a join of the parts in the wrong order", "(p, b) = Addr::alloc(4); (lo, hi) = Block::split(b, 2); r = Block::join(hi, lo); return Addr::free(p, r);", "Could not prove: start(hi) = start(lo) + cap(lo)")
        , ("an emptied slot is not still filled", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); b = Addr::dropValue(p, 0, b); affirm filled(b, 0) = true; return Addr::free(p, b);", "Could not prove: filled(b, 0) = true")
        , ("a slot taken from is not still filled", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); (x, b) = Addr::take(p, 0, b); affirm filled(b, 0) = true; return x + Addr::free(p, b);", "Could not prove: filled(b, 0) = true")
        , ("a dropped range is not still filled", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); b = Addr::dropRange(p, 0, 1, b); affirm filled(b, 0) = true; return Addr::free(p, b);", "Could not prove: filled(b, 0) = true")
        , ("a free with a slot filled", "(p, b) = Addr::alloc(2); b = Addr::write(p, 0, 1, b); return Addr::free(p, b);", "Could not prove: count(b) = 0")
        , ("a resize that would lose a value", "(p, b) = Addr::alloc(2); b = Addr::write(p, 1, 1, b); (q, b) = Addr::resize(p, 1, b); b = Addr::dropValue(q, 0, b); return Addr::free(q, b);", "Could not prove: forall j in n..cap(b): filled(b, j) = false")
        , ("a cast of a block that holds a value", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 1, b); c = Block::cast(b); q = Addr::cast(p); c = Addr::dropValue(q, 0, c); d = Addr::free(q, c); return 0;", "Could not prove: count(b) = 0")
        , ("a cast to slots of another size", "struct P { x: Int, y: Int }; (p, b) = Addr::alloc(1); c = Block::cast(b); q = Addr::cast(p); d = Addr::free(q, c); x = Addr::get(q, 0, c); return 0;", "c was moved at line 1:94 and cannot be used again")
        , ("an offset of a cast address is not an offset of the address", "(p, b) = Addr::alloc(2); (lo, hi) = Block::split(b, 1); r = Addr::cast(Addr::offset(Addr::cast(p), 1)); hi = Addr::write(r, 0, 5, hi); hi = Addr::dropValue(r, 0, hi); return Addr::free(p, Block::join(lo, hi));", "Could not prove: base(b) = p")
        , ("a cast to slots of lists, which take three words", "(p, b) = Addr::alloc(1); c = Block::cast(b); q = Addr::cast(p); c = Addr::write(q, 0, [1, 2, 3], c); c = Addr::dropValue(q, 0, c); return Addr::free(q, c);", "(8,8) and (24,8)")
        , ("a cast from slots of a type parameter", "fn f<T>(p: Addr<T>, ghost b: Block<T>) -> Int [{ affirm base(b) = p; affirm whole(b); affirm cap(b) >= 1; affirm count(b) = 0; }] [{ }] { c = Block::cast(b); q = Addr::cast(p); c = Addr::write(q, 0, 7, c); c = Addr::dropValue(q, 0, c); return Addr::free(q, c); }; (p, b) = Addr::alloc(1); return f(p, b);", "layout of a type parameter")
        , ("a use after free", "(p, b) = Addr::alloc(1); d = Addr::free(p, b); b = Addr::write(p, 0, 1, b); return d;", "b was moved at line 1:26 and cannot be used again")
        , ("a view used after its block changed", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, push([], 1), b); x = Addr::get(p, 0, b); b = Addr::dropValue(p, 0, b); d = Addr::free(p, b); return size(x);", "b[slot] is a part of it")
        , ("a value moved out of a slot that still holds it", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, push([], 1), b); x = Addr::get(p, 0, b); (y, b) = Addr::take(p, 0, b); d = Addr::free(p, b); return x;", "out of the memory of a permission")
        , ("a permission that is dropped", "(p, b) = Addr::alloc(2); return 0;", "b is a permission given at line")
        , ("a permission that is used on one path only", "fn f(c: Bool) -> Int { (p, b) = Addr::alloc(1); if c { d = Addr::free(p, b); }; return 0; }; return f(true);", "is a permission given at line")
        , ("a permission lost by giving its local another value", "(p, b) = Addr::alloc(1); (p, b) = Addr::alloc(2); return Addr::free(p, b);", "is given another value here")
        , ("a struct that holds a permission is dropped", "struct Buf { addr: Addr<Int>, ghost blk: Block<Int> }; (a, b) = Addr::alloc(1); x = Buf { addr: a, blk: b }; return 0;", "x.blk is a permission (in x)")
        , ("a permission given to a function is not used", "fn f(p: Addr<Int>, ghost b: Block<Int>) -> Int { return 0; }; (p, b) = Addr::alloc(1); return f(p, b);", "b is a permission")
        , ("a permission is copied", "(p, b) = Addr::alloc(1); c = clone(b); return Addr::free(p, b);", "is a permission, which is never copied")
        , ("permissions are compared", "(p, b) = Addr::alloc(1); (q, c) = Addr::alloc(1); x = b = c; return 0;", "holds a permission, which cannot be compared")
        , ("a list of permissions", "fn f(l: List<Block<Int>>) -> Int { return 0; }; return 0;", "a list cannot hold Block<Int>")
        , ("a permission given to a type parameter", "fn id<T>(x: T) -> T { return x; }; (p, b) = Addr::alloc(1); c = id(b); return Addr::free(p, c);", "a type parameter is not one")
        , ("what is known of a permission is not a value", "(p, b) = Addr::alloc(1); n = cap(b); return Addr::free(p, b) + n;", "is not a value the program has")
        , ("ghost before a type that is not a permission", "fn f(ghost n: Int) -> Int { return n; }; return f(1);", "ghost is written before a type that is a permission")
        , ("an allocation of a negative size", "(p, b) = Addr::alloc(0 - 1); return Addr::free(p, b);", "Could not prove: n >= 0")
        ]
    -- (a struct that holds a permission, which is linear unless it has a drop)
    owner = "struct V { addr: Addr<Int>, n: Int, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = n; affirm count(blk) = 0; affirm n >= 0; }]; impl V { fn new(n: Int) -> Self [{ affirm n >= 0; }] [{ }] { (a, b) = Addr::alloc(n); return Self { addr: a, n: n, blk: b }; }; };"
    dropper = owner ++ "impl Drop for V { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; };"
    nested = holder ++ "struct G { addr: Addr<Int>, h: H, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl Drop for G { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl G { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, h: H::new(), blk: b }; }; }; fn eat(h: H) -> Int { return size(h.xs); };"
    holder = "struct H { addr: Addr<Int>, xs: List<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl Drop for H { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl H { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, xs: [1, 2], blk: b }; }; };"
    handle = "linear struct Handle { fd: Int }; impl Handle { fn open(n: Int) -> Self { return Self { fd: n }; }; fn close(self: Self) -> Int { return self.fd; }; };"
    memory =
        unlines
            [ "(p, b) = Addr::alloc(2);"
            , "affirm start(b) = 0; affirm cap(b) = extent(origin(b)); affirm count(b) = 0;"
            , "b = Addr::write(p, 0, 10, b);"
            , "b = Addr::write(p, 1, 20, b);"
            , "x = Addr::get(p, 1, b);"
            , "affirm x = 20;"
            , "(y, b) = Addr::take(p, 0, b);"
            , "affirm cap(b) = extent(origin(b)); affirm count(b) = 1;"
            , "affirm y = 10;"
            , "b = Addr::dropValue(p, 1, b);"
            , "return x + y + Addr::free(p, b);"
            ]
    resized =
        unlines
            [ "(p, b) = Addr::alloc(1);"
            , "affirm count(b) = 0;"
            , "b = Addr::write(p, 0, 5, b);"
            , "(q, b) = Addr::resize(p, 2, b);"
            , "affirm filled(b, 0) = true; affirm at(b, 0) = 5; affirm cap(b) = extent(origin(b));"
            , "b = Addr::write(q, 1, 6, b);"
            , "x = Addr::get(q, 0, b);"
            , "affirm x = 5;"
            , "y = Addr::get(q, 1, b);"
            , "b = Addr::dropRange(q, 0, 2, b);"
            , "return x + y + Addr::free(q, b);"
            ]
    chain value = "(p, b) = Addr::alloc(3); affirm cap(b) = extent(origin(b)); b = Addr::write(p, 0, 10, b); b = Addr::write(p, 1, 20, b); b = Addr::write(p, 2, 30, b); x = Addr::get(p, 0, b); affirm x = " ++ value ++ "; b = Addr::dropRange(p, 0, 3, b); return x + Addr::free(p, b);"
    owning =
        unlines
            [ "(p, b) = Addr::alloc(2);"
            , "affirm cap(b) = extent(origin(b));"
            , "b = Addr::write(p, 0, push(push([], 1), 2), b);"
            , "b = Addr::write(p, 1, push([], 3), b);"
            , "(l, b) = Addr::take(p, 0, b);"
            , "m = Addr::get(p, 1, b);"
            , "n = size(l) + size(m);"
            , "b = Addr::dropValue(p, 1, b);"
            , "return n + Addr::free(p, b) + 2;"
            ]
    splitJoin =
        unlines
            [ "(p, b) = Addr::alloc(4);"
            , "(lo, hi) = Block::split(b, 2);"
            , "affirm count(lo) = 0; affirm count(hi) = 0; affirm start(lo) = 0; affirm cap(hi) = 2; affirm extent(origin(lo)) = 4;"
            , "hi = Addr::write(Addr::offset(p, 2), 0, 7, hi);"
            , "affirm start(hi) = start(lo) + cap(lo); affirm origin(hi) = origin(lo);"
            , "x = Addr::get(Addr::offset(p, 2), 0, hi);"
            , "hi = Addr::dropValue(Addr::offset(p, 2), 0, hi);"
            , "b = Block::join(lo, hi);"
            , "return x + Addr::free(p, b);"
            ]
    buffer =
        unlines
            [ "struct Buf { addr: Addr<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm count(blk) = 0; }];"
            , "fn mk(n: Int) -> Buf [{ affirm n >= 0; }] [{ affirm cap(return.blk) = n; }] {"
            , "    (a, b) = Addr::alloc(n);"
            , "    return Buf { addr: a, blk: b };"
            , "};"
            , "fn release(x: Buf) -> Int { return Addr::free(x.addr, x.blk); };"
            , "return release(mk(3));"
            ]
    giveBack =
        unlines
            [ "fn put(p: Addr<Int>, ghost b: Block<Int>, x: Int) -> Block<Int> [{ affirm base(b) = p; affirm cap(b) >= 1; affirm filled(b, 0) = false; }]"
            , "    [{ affirm base(return) = base(b); affirm cap(return) = cap(b); affirm origin(return) = origin(b); affirm start(return) = start(b); affirm count(return) = count(b) + 1;"
            , "       affirm filled(return, 0) = true; affirm at(return, 0) = x; }] {"
            , "    return Addr::write(p, 0, x, b);"
            , "};"
            , "(p, b) = Addr::alloc(1);"
            , "b = put(p, b, 9);"
            , "(x, b) = Addr::take(p, 0, b);"
            , "affirm x = 9;"
            , "return x + Addr::free(p, b);"
            ]
    lent =
        unlines
            [ "fn head(p: Addr<Int>, ghost b: &Block<Int>) -> Int [{ affirm base(b) = p; affirm cap(b) >= 1; affirm filled(b, 0) = true; }] [{ affirm return = at(b, 0); }] {"
            , "    return Addr::get(p, 0, b);"
            , "};"
            , "(p, b) = Addr::alloc(1);"
            , "b = Addr::write(p, 0, 6, b);"
            , "x = head(p, b);"
            , "affirm x = 6;"
            , "b = Addr::dropValue(p, 0, b);"
            , "return x + Addr::free(p, b);"
            ]
    vec =
        unlines
            [ "struct Vec<T> { addr: Addr<T>, cap: Int, len: Int, ghost blk: Block<T> } invariant [{"
            , "    affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = cap; affirm count(blk) = len; affirm 0 <= len; affirm len <= cap;"
            , "    affirm forall j in 0..len: filled(blk, j) = true; affirm forall j in len..cap: filled(blk, j) = false; }];"
            , "impl<T> Vec<T> {"
            , "    fn new() -> Self [{ }] [{ affirm return.len = 0; }] { (a, b) = Addr::alloc(1); return Self { addr: a, cap: 1, len: 0, blk: b }; };"
            , "    fn push(self: Self, x: T) -> Self [{ }] [{ affirm return.len = self.len + 1; }] {"
            , "        if self.len = self.cap {"
            , "            cap = self.cap * 2 + 1;"
            , "            (a, b) = Addr::resize(self.addr, cap, self.blk);"
            , "            return Self { addr: a, cap: cap, len: self.len + 1, blk: Addr::write(a, self.len, x, b) };"
            , "        };"
            , "        return Self { addr: self.addr, cap: self.cap, len: self.len + 1, blk: Addr::write(self.addr, self.len, x, self.blk) };"
            , "    };"
            , "    fn free(self: Self) -> Int { return Addr::free(self.addr, Addr::dropRange(self.addr, 0, self.len, self.blk)); };"
            , "};"
            , "v = Vec::new(); v = v.push(true); v = v.push(false); v = v.push(true);"
            , "n = v.len + v.cap - 5;"
            , "return n + v.free();"
            ]
