module TestPointers (testPointers) where

import Data.List (isInfixOf)

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
            , testCase "a tuple of one part" (rejected "t: (Int) = 1; return 0;" "")
            , testCase "the name of the struct of tuples is the language's" (rejected "struct Tuple2<A, B> { x: A, y: B }; return 0;" "builtin type")
            ]
        , TestList
            "memory"
            [ testCase "write, read, take, drop and free" (runs memory "30")
            , testCase "an address is offset" (runs "(p, b) = Addr::alloc(3); q = Addr::offset(p, 2); b = Addr::write(p, 2, 7, b); x = Addr::get(p, 2, b); b = Addr::dropValue(p, 2, b); return x + Addr::free(p, b) + Addr::toInt(Addr::offset(q, 0 - 2)) - Addr::toInt(p);" "7")
            , testCase "the null address" (runs "p = Addr::null(); q = Addr::fromInt(0); return Addr::toInt(p) + Addr::toInt(q);" "0")
            , testCase "memory is resized" (runs resized "11")
            , testCase "values that own something" (runs owning "5")
            , testCase "a block is split and joined" (runs splitJoin "7")
            , testCase "a permission in a struct" (runs buffer "0")
            , testCase "a function takes a block and gives it back" (runs giveBack "9")
            , testCase "a function is lent a block" (runs lent "6")
            , testCase "a block of one type as another" (runs "struct Two { a: I32, b: I32 }; impl Clone for Two { }; impl Copy for Two { }; (p, b) = Addr::alloc(2); c = Block::cast(b); q = Addr::cast(p); c = Addr::write(q, 0, Two { a: -1, b: 2 }, c); x = Addr::get(q, 0, c); c = Addr::dropValue(q, 0, c); d = Addr::free(q, c); return toInt(x.a) + toInt(x.b);" "1")
            , testCase "a block of slots of another size" (rejected "(p, b) = Addr::alloc(2); c = Block::cast(b); q = Addr::cast(p); c = Addr::write(q, 0, true, c); c = Addr::dropValue(q, 0, c); return Addr::free(q, c);" "are not the same size")
            , testCase "the permission to memory the program did not allocate is an assumption" (valid "p = Addr::fromInt(4096); b = Block::assume(p, 2); b = Addr::write(p, 0, 5, b); b = Addr::dropValue(p, 0, b); return Addr::free(p, b);")
            , testCase "a Vec on an address" (runs vec "1")
            ]
        , TestList
            "refused"
            [ testCase "a read of an empty slot" (rejected "(p, b) = Addr::alloc(2); x = Addr::get(p, 1, b); d = Addr::free(p, b); return x;" "Could not prove: filled(b, i) = true")
            , testCase "a write over a filled slot" (rejected "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 1, b); b = Addr::write(p, 0, 2, b); b = Addr::dropValue(p, 0, b); return Addr::free(p, b);" "Could not prove: filled(b, i) = false")
            , testCase "a slot out of bounds" (rejected "(p, b) = Addr::alloc(2); b = Addr::write(p, 2, 1, b); b = Addr::dropValue(p, 2, b); return Addr::free(p, b);" "Could not prove: i < cap(b)")
            , testCase "a negative slot" (rejected "(p, b) = Addr::alloc(2); b = Addr::write(p, 0 - 1, 1, b); b = Addr::dropValue(p, 0 - 1, b); return Addr::free(p, b);" "Could not prove: i >= 0")
            , testCase "the permission of one block with the address of another" (rejected "(p, b) = Addr::alloc(1); (q, c) = Addr::alloc(1); b = Addr::write(q, 0, 1, b); b = Addr::dropValue(p, 0, b); d = Addr::free(p, b); return d + Addr::free(q, c);" "Could not prove: base(b) = p")
            , testCase "an old address after a resize" (rejected "(p, b) = Addr::alloc(1); (q, b) = Addr::resize(p, 2, b); b = Addr::write(p, 0, 1, b); b = Addr::dropValue(q, 0, b); return Addr::free(q, b);" "Could not prove: base(b) = p")
            , testCase "a free of a part of an allocation" (rejected "(p, b) = Addr::alloc(4); (lo, hi) = Block::split(b, 2); d = Addr::free(p, lo); return d + Addr::free(Addr::offset(p, 2), hi);" "Could not prove: cap(b) = extent(origin(b))")
            , testCase "a join of blocks from two allocations" (rejected "(p, b) = Addr::alloc(2); (q, c) = Addr::alloc(2); r = Block::join(b, c); return Addr::free(p, r);" "Could not prove: origin(lo) = origin(hi)")
            , testCase "a join of the parts in the wrong order" (rejected "(p, b) = Addr::alloc(4); (lo, hi) = Block::split(b, 2); r = Block::join(hi, lo); return Addr::free(p, r);" "Could not prove: start(hi) = start(lo) + cap(lo)")
            , testCase "a free with a slot filled" (rejected "(p, b) = Addr::alloc(2); b = Addr::write(p, 0, 1, b); return Addr::free(p, b);" "Could not prove: count(b) = 0")
            , testCase "a resize that would lose a value" (rejected "(p, b) = Addr::alloc(2); b = Addr::write(p, 1, 1, b); (q, b) = Addr::resize(p, 1, b); b = Addr::dropValue(q, 0, b); return Addr::free(q, b);" "Could not prove: forall j in n..cap(b): filled(b, j) = false")
            , testCase "a cast of a block that holds a value" (rejected "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 1, b); c = Block::cast(b); q = Addr::cast(p); c = Addr::dropValue(q, 0, c); d = Addr::free(q, c); return 0;" "Could not prove: count(b) = 0")
            , testCase "a cast to slots of another size" (rejected "struct P { x: Int, y: Int }; (p, b) = Addr::alloc(1); c = Block::cast(b); q = Addr::cast(p); d = Addr::free(q, c); x = Addr::get(q, 0, c); return 0;" "")
            , testCase "a use after free" (rejected "(p, b) = Addr::alloc(1); d = Addr::free(p, b); b = Addr::write(p, 0, 1, b); return d;" "b was moved at line 1:26 and cannot be used again")
            , testCase "a view used after its block changed" (rejected "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, push([], 1), b); x = Addr::get(p, 0, b); b = Addr::dropValue(p, 0, b); d = Addr::free(p, b); return size(x);" "b[slot] is a part of it")
            , testCase "a value moved out of a slot that still holds it" (rejected "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, push([], 1), b); x = Addr::get(p, 0, b); (y, b) = Addr::take(p, 0, b); d = Addr::free(p, b); return x;" "out of the memory of a permission")
            , testCase "a permission that is dropped" (rejected "(p, b) = Addr::alloc(2); return 0;" "b is a permission given at line")
            , testCase "a permission that is used on one path only" (rejected "fn f(c: Bool) -> Int { (p, b) = Addr::alloc(1); if c { d = Addr::free(p, b); }; return 0; }; return f(true);" "is a permission given at line")
            , testCase "a permission lost by giving its local another value" (rejected "(p, b) = Addr::alloc(1); (p, b) = Addr::alloc(2); return Addr::free(p, b);" "is given another value here")
            , testCase "a struct that holds a permission is dropped" (rejected "struct Buf { addr: Addr<Int>, ghost blk: Block<Int> }; (a, b) = Addr::alloc(1); x = Buf { addr: a, blk: b }; return 0;" "x.blk is a permission (in x)")
            , testCase "a permission given to a function is not used" (rejected "fn f(p: Addr<Int>, ghost b: Block<Int>) -> Int { return 0; }; (p, b) = Addr::alloc(1); return f(p, b);" "b is a permission")
            , testCase "a permission is copied" (rejected "(p, b) = Addr::alloc(1); c = clone(b); return Addr::free(p, b);" "is a permission, which is never copied")
            , testCase "permissions are compared" (rejected "(p, b) = Addr::alloc(1); (q, c) = Addr::alloc(1); x = b = c; return 0;" "holds a permission, which cannot be compared")
            , testCase "a list of permissions" (rejected "fn f(l: List<Block<Int>>) -> Int { return 0; }; return 0;" "a list cannot hold Block<Int>")
            , testCase "a permission given to a type parameter" (rejected "fn id<T>(x: T) -> T { return x; }; (p, b) = Addr::alloc(1); c = id(b); return Addr::free(p, c);" "a type parameter is not one")
            , testCase "what is known of a permission is not a value" (rejected "(p, b) = Addr::alloc(1); n = cap(b); return Addr::free(p, b) + n;" "is not a value the program has")
            , testCase "ghost before a type that is not a permission" (rejected "fn f(ghost n: Int) -> Int { return n; }; return f(1);" "ghost is written before a type that is a permission")
            , testCase "an allocation of a negative size" (rejected "(p, b) = Addr::alloc(0 - 1); return Addr::free(p, b);" "Could not prove: n >= 0")
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
            "assumptions"
            [ testCase "assume gives a fact" (valid "fn f(x: Int) -> Int [{ }] [{ affirm return > 0; }] { assume x > 0; return x; }; return f(1);")
            , testCase "the assumptions of a program are listed" (testAssertEq (assumptionsOf "assume 1 > 0;\nfn f(n: Int) -> Int { assume n = n; return n; };\n(p, b) = Addr::alloc(1);\nc = Block::assume(p, 0);\naxiom twice(x) [{ }] [{ affirm x + x = 2 * x; }];\nd = Addr::free(p, b);\nreturn d;") (Ok ["line 1:1: assume 1 > 0", "line 2:23: assume n = n", "line 4:1: Block::assume(p, 0)", "line 5:1: axiom twice(x)"]))
            , testCase "none" (testAssertEq (runSource Assumptions "return 1;") (Ok "No assumptions"))
            ]
        ]
  where
    runs source expected = testAssertEq (runSource Interpret source) (Ok expected)
    valid source = case runSource Check source of
        Ok _ -> Nothing
        Error e -> Just ("Expected the program to validate, but: " ++ e)
    rejected source expected = case runSource Check source of
        Ok _ -> Just ("Expected the program to be refused with " ++ show expected)
        Error e
            | expected `isInfixOf` e -> Nothing
            | otherwise -> Just ("Expected an error with " ++ show expected ++ ", got: " ++ e)
    handle = "linear struct Handle { fd: Int }; impl Handle { fn open(n: Int) -> Self { return Self { fd: n }; }; fn close(self: Self) -> Int { return self.fd; }; };"
    memory =
        unlines
            [ "(p, b) = Addr::alloc(2);"
            , "b = Addr::write(p, 0, 10, b);"
            , "b = Addr::write(p, 1, 20, b);"
            , "x = Addr::get(p, 1, b);"
            , "affirm x = 20;"
            , "(y, b) = Addr::take(p, 0, b);"
            , "affirm y = 10;"
            , "b = Addr::dropValue(p, 1, b);"
            , "return x + y + Addr::free(p, b);"
            ]
    resized =
        unlines
            [ "(p, b) = Addr::alloc(1);"
            , "b = Addr::write(p, 0, 5, b);"
            , "(q, b) = Addr::resize(p, 2, b);"
            , "b = Addr::write(q, 1, 6, b);"
            , "x = Addr::get(q, 0, b);"
            , "affirm x = 5;"
            , "y = Addr::get(q, 1, b);"
            , "b = Addr::dropRange(q, 0, 2, b);"
            , "return x + y + Addr::free(q, b);"
            ]
    owning =
        unlines
            [ "(p, b) = Addr::alloc(2);"
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
            , "hi = Addr::write(Addr::offset(p, 2), 0, 7, hi);"
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
