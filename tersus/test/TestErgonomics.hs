module TestErgonomics (testErgonomics, ergonomicsPrograms, ergonomicsFunctionPrograms) where

import Data.List (isInfixOf)
import AstData (readParsed, writeParsed, readElaborated, writeElaborated)
import Compile (lowerSourceParts)
import qualified TersusParser
import Pipeline (parseSource, validateStatements, assumptionsOf, loadFromEntry, compileModules, assumptionsOfPackage)
import qualified Modules
import TestHarness
import TestParserFragments (parseExpression)
import TypeCheck (elaborate)
import Syntax
import Utils

point :: String
point = "struct P { x: Int }; impl Clone for P {}; impl Copy for P {}; "

enum :: String
enum = "enum E { A { x: Int }, B { x: Int } }; impl Clone for E {}; impl Copy for E {}; "

ownedEnum :: String
ownedEnum = "enum E { A { x: List<Int> }, B }; "

resource :: String
resource = "struct Token { addr: Addr<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; }]; impl Token { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, blk: b }; }; }; impl Drop for Token { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; "

positive :: [(String, String, Value)]
positive =
    [ ("list variable and arithmetic", "x = 3; return [x, x + 1, x * 2];", VList [VInt 3, VInt 4, VInt 6])
    , ("list calls", "fn inc(x: Int) -> Int [{ }] [{ affirm return = x + 1; }] { return x + 1; }; return [inc(1), inc(2)];", VList [VInt 2, VInt 3])
    , ("nested expression lists", "x = 2; return [[x], [x + 1, x + 2]];", VList [VList [VInt 2], VList [VInt 3, VInt 4]])
    , ("string expressions", "s = \"ab\"; xs = [clone(s), \"cd\"]; return size(xs) + size(s) + size(get(xs, 1));", VInt 6)
    , ("struct expressions", point ++ "x = P { x: 4 }; xs = [x, P { x: 5 }]; return first(xs).x + get(xs, 1).x;", VInt 9)
    , ("enum expressions", enum ++ "x = E::A { x: 4 }; xs = [x, E::B { x: 5 }]; return match get(xs, 1) { E::A { x: n } => n, E::B { x: n } => n + 1 };", VInt 6)
    , ("tuple expressions", "x = 3; xs = [(x, true), (x + 1, false)]; return first(xs).0 + get(xs, 1).0;", VInt 7)
    , ("literal list proofs unchanged", "xs = [[1, 2], [3]]; affirm size(xs) = 2; affirm get(get(xs, 0), 1) = 2; return 0;", VInt 0)
    , ("expression list element facts", "x = 3; xs = [x, x + 1]; affirm size(xs) = 2; affirm get(xs, 0) = x; affirm get(xs, 1) = x + 1; return 0;", VInt 0)
    , ("if initializes assignment", "x = if true { 3 } else { 4 }; return x;", VInt 3)
    , ("if initializes let", "let x = if false { 3 } else { 4 }; return x;", VInt 4)
    , ("nested else if", "return 1 + if false { 2 } else if true { 3 } else { 4 };", VInt 4)
    , ("if in arguments", "fn add(a: Int, b: Int) -> Int { return a + b; }; return add(if true { 3 } else { 4 }, 5);", VInt 8)
    , ("if in tuple", "t = (if false { 0 } else { 3 }, 4); return t.0 + t.1;", VInt 7)
    , ("if in list", "return [if true { 3 } else { 4 }, if false { 5 } else { 6 }];", VList [VInt 3, VInt 6])
    , ("if in record", point ++ "p = P { x: if true { 3 } else { 4 } }; return p.x;", VInt 3)
    , ("value block statements", "let x = if true { let y = 3; affirm y > 0; y + 1 } else { 5 }; return x;", VInt 4)
    , ("let shadow and assignment", "x = 3; { let x: Bool = true; x = false; affirm x = false; }; return x;", VInt 3)
    , ("let RHS sees previous binding", "let x = 2; let x = x + 3; return x;", VInt 5)
    , ("assignment still updates outer", "let x = 3; { x = 4; }; return x;", VInt 4)
    , ("typed empty strings", "let names: List<String> = []; names = push(names, \"ab\"); return size(first(names));", VInt 2)
    , ("typed empty branch", "let names: List<String> = if true { [] } else { [\"ab\"] }; return size(names);", VInt 0)
    , ("typed byte branches", "let b: Byte = if true { 65 } else { 66 }; return toInt(b);", VInt 65)
    , ("match initializes assignment", enum ++ "e = E::A { x: 3 }; result = match e { E::A { x: x } => x, E::B { x: x } => x + 1 }; return result;", VInt 3)
    , ("match in arithmetic and argument", enum ++ "fn twice(x: Int) -> Int { return x * 2; }; e = E::B { x: 3 }; return 1 + twice(match e { E::A { x: x } => x, E::B { x: x } => x + 1 });", VInt 9)
    , ("match in list and record", point ++ enum ++ "e = E::A { x: 3 }; xs = [P { x: match e { E::A { x: x } => x, E::B { x: x } => x + 1 } }]; return first(xs).x;", VInt 3)
    , ("nested match scopes", enum ++ "e = E::A { x: 2 }; return match e { E::A { x: x } => x + match E::B { x: 3 } { E::A { x: x } => x, E::B { x: x } => x }, E::B { x: x } => x };", VInt 5)
    , ("if let success shadows", enum ++ "x = 9; e = E::A { x: 3 }; y = 0; if let E::A { x: x } = e { y = x; } else { y = 4; }; return x + y;", VInt 12)
    , ("if let failure leaves bindings", enum ++ "x = 9; e = E::B { x: 3 }; y = 0; if let E::A { x: x } = e { y = x; } else { y = x + 1; }; return y;", VInt 10)
    , ("if let as expression", enum ++ "e = E::A { x: 3 }; let y = if let E::A { x: x } = e { x + 1 } else { 0 }; return y;", VInt 4)
    , ("if let checked cast", enum ++ "e = E::A { x: 3 }; if let E::A {} = e { return (e as E::A).x; } else { return 0; };", VInt 3)
    , ("list left to right once", "fn next(n: &mut Int) -> Int { old = n; *n = n + 1; return old; }; n = 0; xs = [next(&mut n), next(&mut n), next(&mut n)]; return n * 1000 + get(xs, 0) * 100 + get(xs, 1) * 10 + get(xs, 2);", VInt 3012)
    , ("lazy branch effects", "fn next(n: &mut Int) -> Int { *n = n + 1; return n; }; n = 0; x = if true { next(&mut n) } else { next(&mut n) + next(&mut n) }; return n * 10 + x;", VInt 11)
    , ("if let subject once", enum ++ "fn make(n: &mut Int) -> E { *n = n + 1; return E::A { x: n }; }; n = 0; x = if let E::A { x: x } = make(&mut n) { x } else { 0 }; return n * 10 + x;", VInt 11)
    , ("owning conditional result", "xs = if true { [1, 2] } else { [3] }; return size(xs);", VInt 2)
    , ("explicit clone into list", "xs = [1, 2]; ys = [clone(xs), [3]]; return size(xs) + size(first(ys));", VInt 4)
    , ("non-Clone owners in expression lists", resource ++ "xs = [Token::new(), Token::new()]; return size(xs);", VInt 2)
    , ("non-Clone owning branch result", resource ++ "xs = if true { [Token::new()] } else { [Token::new(), Token::new()] }; return size(xs);", VInt 1)
    , ("sibling arithmetic captures old variable", "n = 1; return n + if true { n = 4; n } else { 5 };", VInt 5)
    , ("sibling tuple captures old variable", "n = 1; t = (n, if true { n = 4; n } else { 5 }); return t.0 * 10 + t.1;", VInt 14)
    , ("sibling record captures old variable", "struct Pair { a: Int, b: Int }; n = 1; p = Pair { a: n, b: if true { n = 4; n } else { 5 } }; return p.a * 10 + p.b;", VInt 14)
    , ("sibling call captures old variable", "fn pair(a: Int, b: Int) -> Int { return a * 10 + b; }; n = 1; return pair(n, if true { n = 4; n } else { 5 });", VInt 14)
    , ("owning sibling move before reassignment", "xs = [1]; t = (xs, if true { xs = [2, 3]; 0 } else { xs = [4]; 1 }); return size(t.0) * 10 + size(xs);", VInt 12)
    , ("mixed Byte branches in declaration", "let b: Byte = if true { toByte(65) } else { 66 }; return toInt(b);", VInt 65)
    , ("mixed Byte branches reversed", "let b: Byte = if false { 66 } else { toByte(65) }; return toInt(b);", VInt 65)
    , ("mixed Byte branches in record", "struct B { b: Byte }; b = B { b: if true { toByte(65) } else { 66 } }; return toInt(b.b);", VInt 65)
    , ("mixed Byte branches in call", "fn value(b: Byte) -> Int { return toInt(b); }; return value(if true { 66 } else { toByte(65) });", VInt 66)
    , ("typed dynamic byte list", "let bs: List<Byte> = [toByte(65), 66]; return toInt(get(bs, 0)) + toInt(get(bs, 1));", VInt 131)
    , ("typed dynamic byte list in record", "struct B { bs: List<Byte> }; b = B { bs: [toByte(65), 66] }; return toInt(get(b.bs, 1));", VInt 66)
    , ("typed dynamic byte list in call", "fn firstByte(bs: &List<Byte>) -> Int [{ affirm size(bs) > 0; }] [{ }] { return toInt(first(bs)); }; return firstByte([toByte(65), 66]);", VInt 65)
    , ("array Box branch unsizing", "fn f(c: Bool) -> Box<Array<Int>> { return if c { Box::new(#[1]) } else { Array::boxed(2, 0) }; }; return size(f(true)) + size(f(false));", VInt 3)
    , ("borrowed return if", "fn choose(c: Bool, a: &Int, b: &Int) -> &Int from (a, b) { return if c { a } else { b }; }; x = 1; y = 2; r = choose(true, x, y); return *r;", VInt 1)
    , ("borrowed return match", "enum Choice { A, B }; fn choose(c: Choice, a: &Int, b: &Int) -> &Int from (a, b) { return match c { Choice::A => a, Choice::B => b }; }; x = 1; y = 2; r = choose(Choice::B, x, y); return *r;", VInt 2)
    , ("conditional reference field mutation", "struct P { x: Int, y: Int }; fn update(p: &mut P, c: Bool) -> Int writes(p) { r = if c { &mut (*p).x } else { &mut (*p).y }; *r = 9; return 0; }; p = P { x: 1, y: 2 }; update(&mut p, false); return p.x * 10 + p.y;", VInt 19)
    , ("precise allowed conditional reference", "struct P { x: Int, y: Int }; fn update(p: &mut P, c: Bool) -> Int writes(p.x) { r = if c { &mut (*p).x } else { &mut (*p).x }; *r = 9; return 0; }; p = P { x: 1, y: 2 }; update(&mut p, true); return p.x * 10 + p.y;", VInt 92)
    , ("non-Clone sibling move before reassignment", resource ++ "xs = [Token::new()]; t = (xs, if true { xs = [Token::new(), Token::new()]; 0 } else { xs = [Token::new()]; 1 }); return size(t.0) * 10 + size(xs);", VInt 12)
    , ("loop carried references follow reassignment", "x = 1; y = 2; r = if true { &mut x } else { &mut x }; i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { *r = 9; r = &mut y; i = i + 1; }; return x * 10 + y;", VInt 99)
    , ("local function mutation preserves earlier read", "fn outer(p: &mut Int) -> Int { return p + if true { fn local(q: &mut Int) -> Int { *q = 4; return 0; }; local(p) } else { 0 }; }; n = 1; return outer(&mut n);", VInt 1)
    , ("sibling assignment locals have separate provenance", "fn f(a: &Int, b: &Int, c: Bool) -> &Int from a { return if c { r = &a; r } else { r = &b; &a }; }; x = 1; y = 2; r = f(x, y, true); return *r;", VInt 1)
    , ("earlier yield survives outer ref reassignment", "fn f(a: &Int, b: &Int, c: Bool) -> &Int from a { r = &a; return if c { r } else { r = &b; &a }; }; x = 1; y = 2; r = f(x, y, true); return *r;", VInt 1)
    , ("sequence holder releases ended child loan", "struct W { r: &mut Int }; fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; rows = [W { r: &mut n }]; w = first(rows); parent = w.r; child = &*parent; before = *child; mutate(w); return before + n;", VInt 5)
    , ("returned read reference copies owned-pointee field", "struct W { r: &List<Int> }; fn extract(w: &W) -> &List<Int> from w { return w.r; }; a = [1]; w = W { r: &a }; saved = extract(w); return size(*saved);", VInt 1)
    , ("returned holder retains independent storage", "struct W { r: &List<Int> }; fn wrap(a: &List<Int>) -> W from a { return W { r: &a }; }; a = [1]; b = [2]; w = wrap(a); p = &mut w; (*p).r = &b; a = [3]; saved = w.r; return size(*saved);", VInt 1)
    , ("nested holder preserves capability through helper", "struct W { r: &mut Int }; struct H { inner: W }; fn observe(h: &H) -> Int { return *h.inner.r; }; fn mutate(h: &H) -> Int { *h.inner.r = 4; return observe(h); }; fn forward(h: &H) -> Int { return mutate(h); }; n = 1; h = H { inner: W { r: &mut n } }; return forward(h);", VInt 4)
    , ("variant holder forwards capability", "enum E { A { r: &mut Int }, B }; fn mutate(v: E::A) -> Int { *v.r = 4; return 0; }; fn forward(v: E::A) -> Int { return mutate(v); }; n = 1; e = E::A { r: &mut n }; return forward(e as E::A);", VInt 0)
    , ("readonly holder forwards declared update capability", "struct W { r: &mut Int }; fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; fn forward(w: &W) -> Int { return mutate(w); }; n = 1; w = W { r: &mut n }; return forward(w);", VInt 0)
    , ("ended joined reborrow releases candidates", "fn writeNine(p: &mut Int) -> Int { *p = 9; return 0; }; fn f(c: Bool) -> Int { x = 1; y = 2; parent = if c { &mut x } else { &mut y }; child = &*parent; before = *child; writeNine(&mut y); return before; }; return f(true) + f(false);", VInt 3)
    , ("readonly holder call accepts ended child loan", "struct W { r: &mut Int }; fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; parent = w.r; child = &*parent; before = *child; mutate(w); return before + n;", VInt 5)
    , ("owned mutable-ref holder is effectful", "struct W { r: &mut Int }; fn mutate(w: W) -> Int { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; return n + if true { mutate(w) } else { 0 };", VInt 1)
    , ("borrowed index captures old reference root", "a = [10]; b = [20]; r = &a; p = &get(r, if true { r = &b; 0 } else { 0 }); return *p;", VInt 10)
    , ("joined reference retains new and saved values", "fn f(c: Bool) -> Int { x = 1; y = 2; r = if c { &mut x } else { &mut y }; before = *r; *r = 9; affirm *r = 9; affirm before > 0; return before * 10 + *r; }; return f(true) + f(false);", VInt 48)
    , ("joined mutable call retains selected postvalue", "fn writeNine(p: &mut Int) -> Int [{ }] [{ affirm p = 9; }] { *p = 9; return 0; }; fn f(c: Bool) -> Int { x = 1; y = 2; r = if c { &mut x } else { &mut y }; writeNine(r); affirm *r = 9; return *r; }; return f(true) + f(false);", VInt 18)
    , ("returned mutable reference updates its owner", "fn idr(n: &mut Int) -> &mut Int from n [{ }] [{ affirm n = old(n); }] { return n; }; x = 1; r = idr(&mut x); *r = 9; affirm x = 9; return x;", VInt 9)
    , ("readonly mutable-ref holder is effectful", "struct W { r: &mut Int }; fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; return n + if true { mutate(w) } else { 0 };", VInt 1)
    , ("variant mutable-ref holder is effectful", "enum E { A { r: &mut Int }, B }; fn mutate(v: E::A) -> Int { *v.r = 4; return 0; }; n = 1; e = E::A { r: &mut n }; return n + if true { mutate(e as E::A) } else { 0 };", VInt 1)
    , ("reference field replacement removes old origin", "struct W { r: &Int }; fn f(a: &Int, b: &Int) -> &Int from a { w = W { r: &b }; p = &mut w; (*p).r = &a; return if true { w.r } else { &a }; }; x = 1; y = 2; r = f(x, y); return *r;", VInt 1)
    , ("for body let shadows counter", "count = 0; for i in 0..3 { let i = 99; count = count + 1; }; return count;", VInt 3)
    , ("for shadow assignment does not change generated step", "count = 0; for i in 0..3 { let i = i + 99; i = i + 1; count = count + 1; }; return count;", VInt 3)
    , ("for match pattern shadows counter", enum ++ "count = 0; for i in 0..3 { e = E::A { x: 9 }; n = match e { E::A { x: i } => { i = i + 1; i }, E::B { x: n } => n }; count = count + 1; }; return count;", VInt 3)
    , ("for counter read borrow and copied mutable value", "count = 0; for i in 0..3 { read = &i; copied = *read; p = &mut copied; *p = 99; count = count + 1; }; return count;", VInt 3)
    , ("for shadow mutable borrow is local", "count = 0; for i in 0..3 { let i = 99; p = &mut i; *p = 2; count = count + 1; }; return count;", VInt 3)
    , ("for nested function does not capture counter", "count = 0; for i in 0..3 { fn local(i: Int) -> Int { i = 2; return i; }; count = count + 1; }; return count;", VInt 3)
    , ("whole borrowed holder keeps storage origin", "struct W { r: &Int }; fn f(p: &mut W, b: &Int) -> &mut W from p { (*p).r = &b; return p; }; a = 1; b = 2; w = W { r: &a }; p = f(&mut w, b); r = (*p).r; return *r;", VInt 2)
    , ("replaced field releases old owned pointee", "struct W { r: &List<Int> }; a = [1]; b = [2, 3]; w = W { r: &a }; p = &mut w; (*p).r = &b; saved = w.r; a = [4]; return size(*saved) + size(a);", VInt 3)
    , ("owning match result", ownedEnum ++ "e = E::A { x: [1, 2] }; xs = match e { E::A { x: x } => x, E::B => [] }; return size(xs);", VInt 2)
    ]

ergonomicsPrograms :: [(String, String)]
ergonomicsPrograms = [(name, source) | (name, source, _) <- positive]

ergonomicsFunctionPrograms :: [(String, String)]
ergonomicsFunctionPrograms =
    [ ("conditional callable head", functions ++ "return (if true { f } else { g })(3);")
    , ("block callable head", functions ++ "return ({ let chosen = f; chosen })(3);")
    , ("expression assignment to existing function", functions ++ "n = if true { f = g; 0 } else { 0 }; return f(3);" )
    , ("statement assignment to existing function", functions ++ "if true { f = g; } else {}; return f(3);" )
    , ("callable head precedes argument mutation", functions ++ "return f(if true { f = g; 3 } else { 0 });")
    , ("mutating computed head captures parameter read", "fn f(p: &mut Int) -> Int { *p = 4; return 0; }; fn g(p: &mut Int) -> Int { *p = 5; return 0; }; fn outer(p: &mut Int) -> Int { return p + (if true { f } else { g })(p); }; n = 1; return outer(&mut n);")
    , ("match callable head", functions ++ "enum Which { F, G }; w = Which::F; return (match w { Which::F => f, Which::G => g })(3);")
    ]
  where
    functions = "fn f(x: Int) -> Int { return x + 1; }; fn g(x: Int) -> Int { return x + 2; }; "

ergonomicsRejected :: String -> String -> TestResult
ergonomicsRejected source expected = case parseSource source of
    Error err -> check err
    Ok statements -> case validateStatements statements of
        Ok _ -> Just ("Expected rejection containing: " ++ expected)
        Error err -> check err
  where
    check err
        | expected `isInfixOf` err && not ("does not model yet" `isInfixOf` err) = Nothing
        | otherwise = Just ("Expected modeled rejection containing: " ++ expected ++ "\nGot: " ++ err)

sourceAccepted :: String -> TestResult
sourceAccepted source = case TersusParser.parseSourceParts True source of
    Error err -> Just err
    Ok parts -> case lowerSourceParts True parts of
        Error err -> Just err
        Ok _ -> Nothing

indirectHolder :: String
indirectHolder = "struct Inner { r: &Int }; struct Outer { slot: &mut Inner }; "

referenceChain :: String
referenceChain = "enum E { End, Link { next: &E } }; fn step(e: &E) -> &E from e { return if let E::Link { next: r } = e { r } else { e }; }; "

testErgonomics :: Test
testErgonomics = TestList "testErgonomics"
    [ testCaseNamedSeq "source reference bounds (without native proof credit)"
        [(name, sourceAccepted source) | (name, source) <-
            [ ("readonly carrier stores a borrowed source", indirectHolder ++ "fn store(o: &Outer, b: &Int) -> Int { (*o.slot).r = &b; return 0; }; a = 1; b = 2; inner = Inner { r: &a }; o = Outer { slot: &mut inner }; store(o, b); saved = (*o.slot).r; return *saved;")
            , ("by-value carrier stores a borrowed source", indirectHolder ++ "fn store(o: Outer, b: &Int) -> Int { (*o.slot).r = &b; return 0; }; a = 1; b = 2; inner = Inner { r: &a }; o = Outer { slot: &mut inner }; store(o, b); saved = inner.r; return *saved;")
            , ("by-value parameter storage stays local", "struct Inner { r: &Int }; fn local(w: Inner) -> Int { n = 3; p = &mut w; (*p).r = &n; saved = (*p).r; return *saved; }; return 0;")
            , ("ended returned reference releases transitive bounds", referenceChain ++ "base = E::End; b = E::End; a = E::Link { next: &b }; saved = step(a); before = *saved is E::End; b = E::Link { next: &base }; return before;")
            , ("generic calls classify instantiated reference inputs", "fn count<K>(xs: &List<K>) -> Int { return size(xs); }; fn twice<K>(xs: &List<K>) -> Int { return count(xs) + count(xs); }; return twice([1]);")
            ]]
    , testCaseNamedSeq "validation and evaluation"
        [(name, pipelineValid source <> pipelineRuns source expected) | (name, source, expected) <- positive]
    , testCaseNamedSeq "symbolic branch facts"
        [(name, pipelineValid source) | (name, source) <-
            [ ("guarded bounds", "fn safe(xs: &List<Int>) -> Int { return if size(xs) > 0 { first(xs) } else { 0 }; }; return safe([]);")
            , ("guarded division", "fn safe(n: Int) -> Int { return 1 + if n != 0 { 10 / n } else { 0 }; }; return safe(0);")
            , ("joined bound", "fn f(c: Bool) -> Int { let x = if c { 1 } else { 2 }; affirm x > 0; return get([3, 4, 5], x); }; return f(true);")
            , ("return contract joins", "fn f(c: Bool) -> Int [{ }] [{ affirm return > 0; }] { return if c { 1 } else { 2 }; }; return f(true);")
            , ("match bounds", enum ++ "fn f(e: E) -> Int { return get([3, 4], match e { E::A { x: x } => 0, E::B { x: x } => 1 }); }; return f(E::A { x: 0 });")
            , ("borrowed if-let fields", ownedEnum ++ "fn f(e: &E) -> Int { return if let E::A { x: x } = e { size(x) } else { 0 }; }; e = E::A { x: [1, 2] }; x = f(e); return x + f(e);")
            , ("let shadows borrowed parameter", "fn f(xs: &List<Int>) -> Int { let xs = [3, 4]; return size(xs); }; return f([]);")
            ]]
    , testCaseNamedSeq "rejected programs"
        [(name, ergonomicsRejected source expected) | (name, source, expected) <-
            [ ("readonly carrier cannot retain a callee local", indirectHolder ++ "fn leak(o: &Outer) -> Int { local = 1; (*o.slot).r = &local; return 0; }; return 0;", "reference")
            , ("by-value carrier cannot retain a callee local", indirectHolder ++ "fn leak(o: Outer) -> Int { local = 1; (*o.slot).r = &local; return 0; }; return 0;", "reference")
            , ("readonly carrier call freezes transferred source", indirectHolder ++ "fn store(o: &Outer, b: &Int) -> Int { (*o.slot).r = &b; return 0; }; a = 1; b = 2; inner = Inner { r: &a }; o = Outer { slot: &mut inner }; store(o, b); saved = (*o.slot).r; b = 3; return *saved;", "borrow")
            , ("by-value carrier call freezes transferred source", indirectHolder ++ "fn store(o: Outer, b: &Int) -> Int { (*o.slot).r = &b; return 0; }; a = 1; b = 2; inner = Inner { r: &a }; o = Outer { slot: &mut inner }; store(o, b); saved = inner.r; b = 3; return *saved;", "borrow")
            , ("mutable holder storage preserves readonly child", "struct Inner { r: &Int }; fn local(w: Inner) -> Int { n = 3; p = &mut w; child = &*p; (*p).r = &n; saved = (*child).r; return *saved; }; return 0;", "borrow")
            , ("same-type return retains contained reference bounds", referenceChain ++ "base = E::End; b = E::End; a = E::Link { next: &b }; saved = step(a); b = E::Link { next: &base }; return *saved is E::End;", "borrow")
            , ("same-type return retains grandchild reference bounds", referenceChain ++ "base = E::End; c = E::End; b = E::Link { next: &c }; a = E::Link { next: &b }; saved = step(step(a)); c = E::Link { next: &base }; return *saved is E::End;", "borrow")
            , ("proof cannot hide branching", "define x = if true { 1 } else { 2 }; return 0;", "proof cannot")
            , ("heterogeneous list", "x = 1; return [x, true];", "Type error")
            , ("branch types disagree", "return if true { 1 } else { false };", "Type error")
            , ("annotation mismatch", "let x: Bool = 1; return x;", "Type error")
            , ("annotation narrows wrong branch", "let b: Byte = if true { 65 } else { 256 }; return toInt(b);", "not a Byte")
            , ("let does not update outer type", "x = 1; { let x = true; }; return !x;", "Type error")
            , ("branch local inaccessible", "x = if true { let y = 1; y } else { 2 }; return y;", "Undefined variable")
            , ("if-let binding inaccessible", enum ++ "e = E::A { x: 1 }; if let E::A { x: x } = e {}; return x;", "Undefined variable")
            , ("if-let binding absent in else", enum ++ "e = E::B { x: 1 }; if let E::A { x: x } = e {} else { y = x; }; return 0;", "Undefined variable")
            , ("selected branch fact does not leak", "fn f(c: Int) -> Int { let x = if c > 0 { 1 } else { 2 }; affirm c > 0; return x; }; return 0;", "Could not prove")
            , ("one bad result rejects join", "fn f(c: Bool) -> Int [{ }] [{ affirm return > 0; }] { return if c { 1 } else { -1 }; }; return 0;", "Could not prove")
            , ("reachable variant branch remains checked", enum ++ "fn f(e: E) -> Int { n = if let E::A { x: x } = e { 7 } else { 0 }; affirm n = 7; return n; }; return 0;", "Could not prove")
            , ("empty list through builtin function value", "f = first; let xs: List<Int> = []; return f(xs);", "Could not prove")
            , ("unguarded bounds still rejected", "fn f(xs: &List<Int>, c: Bool) -> Int { return if c { first(xs) } else { 0 }; }; return 0;", "Could not prove")
            , ("list consumes source", "xs = [1]; ys = [xs]; return size(xs);", "was moved")
            , ("branch consumes source on one path", "fn f(c: Bool) -> Int { xs = [1]; ys = if c { xs } else { [2] }; return size(xs); }; return 0;", "was moved")
            , ("if-let failure cannot cast success variant", enum ++ "fn f(e: E) -> Int { if let E::A { x: x } = e { return x; } else { return (e as E::A).x; }; }; return 0;", "Could not prove")
            , ("borrowed pattern cannot move field", ownedEnum ++ "fn f(e: &E) -> List<Int> { return if let E::A { x: x } = e { x } else { [] }; }; return 0;", "is lent")
            , ("conditional mutable assignment respects all footprints", "struct P { x: Int, y: Int }; fn f(p: &mut P, c: Bool) -> Int writes(p.x) { r = if c { &mut (*p).y } else { &mut (*p).x }; *r = 9; return 0; }; return 0;", "writes clause")
            , ("conditional mutable call respects all footprints", "struct P { x: Int, y: Int }; fn touch(x: &mut Int) -> Int { *x = 9; return 0; }; fn f(p: &mut P, c: Bool) -> Int writes(p.x) { return touch(if c { &mut (*p).y } else { &mut (*p).x }); }; return 0;", "writes clause")
            , ("scoped mutable result retains footprint", "struct P { x: Int, y: Int }; fn f(p: &mut P) -> Int writes(p.x) { r = { let inner = &mut (*p).y; inner }; *r = 9; return 0; }; return 0;", "writes clause")
            , ("branch reassignment retains all footprints", "struct P { x: Int, y: Int }; fn f(p: &mut P, c: Bool) -> Int writes(p.x) { r = &mut (*p).x; if c { r = &mut (*p).y; }; *r = 9; return 0; }; return 0;", "writes clause")
            , ("mixed Byte out of range", "let b: Byte = if true { toByte(65) } else { 256 }; return 0;", "not a Byte")
            , ("dynamic byte list out of range", "let bs: List<Byte> = [toByte(65), 256]; return 0;", "not a Byte")
            , ("conditional reference cannot prove one chosen field", "struct P { x: Int, y: Int }; fn f(p: &mut P, c: Bool) -> Int writes(p) [{ }] [{ affirm p.y = 9; }] { r = if c { &mut (*p).x } else { &mut (*p).y }; *r = 9; return 0; }; return 0;", "Could not prove")
            , ("mixed read/mut branches cannot grant update", "x = 1; y = 2; r = if true { &mut x } else { &y }; *r = 9; return 0;", "read reference")
            , ("explicit mut annotation cannot upgrade read branch", "x = 1; y = 2; let r: &mut Int = if true { &mut x } else { &y }; *r = 9; return 0;", "read reference")
            , ("loop carried references respect later footprints", "struct P { x: Int, y: Int }; fn f(p: &mut P) -> Int writes(p.x) { r = &mut (*p).x; i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { *r = 9; r = &mut (*p).y; i = i + 1; }; return 0; }; return 0;", "writes clause")
            , ("rhs evaluation precedes dereference target", "struct P { x: Int, y: Int }; fn f(p: &mut P) -> Int writes(p.x) { r = &mut (*p).x; *r = { r = &mut (*p).y; 9 }; return 0; }; return 0;", "writes clause")
            , ("loop holder references cannot escape local", "struct W { r: &Int }; fn f(a: &Int) -> &Int from a { x = 1; w = W { r: &a }; i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { if i = 1 { return w.r; }; w = W { r: &x }; i = i + 1; }; return &a; }; return 0;", "not a reference from")
            , ("loop hidden rhs reference updates retain footprints", "struct P { x: Int, y: Int }; fn touch(r: &mut Int) -> Int { *r = 9; return 0; }; fn f(p: &mut P) -> Int writes(p.x) { local = 0; s = &mut local; r = &mut (*p).x; i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { touch(r); *s = { r = &mut (*p).y; 0 }; i = i + 1; }; return 0; }; return 0;", "writes clause")
            , ("ambiguous write invalidates prior equality", "x = 1; y = 1; r = if true { &mut x } else { &mut y }; *r = 2; affirm x = 1; return 0;", "Could not prove")
            , ("ambiguous field write rechecks owner invariant", "struct R { lo: Int, hi: Int } invariant [{ affirm lo <= hi; }]; fn f(p: &mut R, c: Bool) -> Int writes(p) { r = if c { &mut (*p).lo } else { &mut (*p).hi }; *r = 9; return 0; }; return 0;", "Could not prove")
            , ("ambiguous write cannot preserve nonzero fact", "x = 1; y = 1; r = if true { &mut x } else { &mut y }; *r = 0; return 10 / x;", "Could not prove")
            , ("symbolic joined write invalidates x equality", "fn f(c: Bool) -> Int { x = 1; y = 2; r = if c { &mut x } else { &mut y }; *r = 9; affirm x = 1; return 0; }; return 0;", "Could not prove")
            , ("symbolic joined call invalidates y equality", "fn writeNine(p: &mut Int) -> Int [{ }] [{ affirm p = 9; }] { *p = 9; return 0; }; fn f(c: Bool) -> Int { x = 1; y = 2; r = if c { &mut x } else { &mut y }; writeNine(r); affirm y = 2; return 0; }; return 0;", "Could not prove")
            , ("alternative invariant checks do not update both fields", "struct P { x: Int, y: Int } invariant [{ affirm x = y; }]; fn f(p: &mut P, c: Bool) -> Int writes(p) { r = if c { &mut (*p).x } else { &mut (*p).y }; *r = 9; return 0; }; return 0;", "Could not prove")
            , ("returned ref write invalidates owner equality", "fn idr(n: &mut Int) -> &mut Int from n [{ }] [{ affirm n = old(n); }] { return n; }; x = 1; r = idr(&mut x); *r = 9; affirm x = 1; return 0;", "Could not prove")
            , ("from list is not an exact pointee value", "fn head(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ affirm *return = first(xs); }] { return &get(xs, 0); }; xs = [1, 2]; r = head(xs); affirm *r = 2; return 0;", "Could not prove")
            , ("loop refreshes parent reference aliases", "x = 1; r = &mut x; s = &mut *r; i = 0; while i < 1 [{ affirm i >= 0; affirm i <= 1; }] shrinks 1 - i { *s = 9; i = i + 1; }; affirm *r = 1; return 0;", "Could not prove")
            , ("reference field write cannot hide local origin", "struct W { r: &Int }; fn f(a: &Int) -> &Int from a { x = 1; w = W { r: &a }; p = &mut w; (*p).r = &x; return if true { w.r } else { &a }; }; return 0;", "not a reference from")
            , ("partial borrowed holder write preserves untouched origins", "struct W { first: &Int, last: &Int }; fn wrong(p: &mut W, b: &Int) -> &Int from b { (*p).first = &b; return p.last; }; return 0;", "not a reference from")
            , ("whole joined holder replacement freezes new owned pointee", "struct W { r: &List<Int> }; fn f(c: Bool) -> Int { a = [1]; b = [2, 3]; w1 = W { r: &a }; w2 = W { r: &a }; p = if c { &mut w1 } else { &mut w2 }; *p = W { r: &b }; saved = w1.r; b = [4]; return size(*saved); }; return f(true);", "borrow")
            , ("sequence holder preserves live child loan", "struct W { r: &mut Int }; fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; rows = [W { r: &mut n }]; w = get(rows, 0); parent = w.r; child = &*parent; mutate(w); return *child;", "borrow")
            , ("last sequence holder preserves live child loan", "struct W { r: &mut Int }; fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; rows = [W { r: &mut n }]; w = last(rows); parent = w.r; child = &*parent; mutate(w); return *child;", "borrow")
            , ("callee local cannot escape through borrowed holder", "struct W { r: &List<Int> }; fn store(p: &mut W) -> Int { local = [1]; (*p).r = &local; return 0; }; a = [2]; w = W { r: &a }; store(&mut w); saved = w.r; return size(*saved);", "reference")
            , ("by-value input local cannot escape through borrowed holder", "struct W { r: &List<Int> }; fn store(p: &mut W, b: List<Int>) -> Int { (*p).r = &b; return 0; }; a = [1]; w = W { r: &a }; store(&mut w, [2]); return 0;", "reference")
            , ("borrowed holder call freezes transferred source", "struct W { r: &List<Int> }; fn store(p: &mut W, b: &List<Int>) -> Int { (*p).r = &b; return 0; }; a = [1]; b = [2]; w = W { r: &a }; store(&mut w, b); saved = w.r; b = [3]; return size(*saved);", "borrow")
            , ("returned reference preserves holder pointee loan", "struct W { r: &List<Int> }; fn extract(w: &W) -> &List<Int> from w { return w.r; }; a = [1]; w = W { r: &a }; saved = extract(w); a = [2]; return size(*saved);", "borrow")
            , ("nested holder child blocks updates", "struct W { r: &mut Int }; struct H { inner: W }; fn mutate(h: &H) -> Int { *h.inner.r = 4; return 0; }; fn forward(h: &H) -> Int { child = &*h.inner.r; mutate(h); return *child; }; n = 1; h = H { inner: W { r: &mut n } }; return forward(h);", "borrow")
            , ("forwarder preserves live child restriction", "struct W { r: &mut Int }; fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; fn forward(w: &W) -> Int { parent = w.r; child = &*parent; mutate(w); return *child; }; n = 1; w = W { r: &mut n }; return forward(w);", "borrow")
            , ("joined reborrow freezes every candidate", "fn writeNine(p: &mut Int) -> Int { *p = 9; return 0; }; fn f(c: Bool) -> Int { x = 1; y = 2; parent = if c { &mut x } else { &mut y }; child = &*parent; writeNine(&mut y); return *child; }; return f(false);", "borrow")
            , ("borrowed call argument stays live during call", "struct W { r: &mut Int }; fn mutate(w: &W, p: &Int) -> Int { *w.r = 4; return p; }; n = 1; w = W { r: &mut n }; parent = w.r; child = &*parent; return mutate(w, child);", "borrow")
            , ("direct borrowed call argument stays live", "fn mutate(p: &mut Int, q: &Int) -> Int { *p = 4; return q; }; n = 1; parent = &mut n; child = &*parent; return mutate(parent, child);", "borrow")
            , ("readonly holder call cannot hide live child loan", "struct W { r: &mut Int }; fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; parent = w.r; child = &*parent; mutate(w); return *child;", "borrow")
            , ("direct mutable call rejects live child loan", "fn mutate(p: &mut Int) -> Int { *p = 4; return 0; }; n = 1; parent = &mut n; child = &*parent; mutate(parent); return *child;", "borrow")
            , ("dynamic reference field freezes new owned pointee", "struct W { r: &List<Int> }; fn f(c: Bool) -> Int { a = [1]; b = [2, 3]; w1 = W { r: &a }; w2 = W { r: &a }; p = if c { &mut w1 } else { &mut w2 }; (*p).r = &b; saved = w1.r; b = [4]; return size(*saved); }; return f(true);", "borrow")
            , ("saved old reference keeps old owned pointee frozen", "struct W { r: &List<Int> }; a = [1]; b = [2]; w = W { r: &a }; old = w.r; p = &mut w; (*p).r = &b; a = [3]; return size(*old);", "borrow")
            , ("conditional reference cannot escape local", "fn f(a: &Int, c: Bool) -> &Int from a { x = 1; return if c { &a } else { &x }; }; return 0;", "not a reference from")
            ]]
    , testCaseNamedSeq "parser refusals"
        [(name, parseFailsWithHelper source expected) | (name, source, expected) <-
            [ ("if result needs else", "x = if true { 1 };", "else")
            , ("if branch needs value", "x = if true {} else { 1 };", "final expression")
            , ("match exhaustive", enum ++ "x = match E::A { x: 0 } { E::A { x: x } => x };", "does not cover")
            , ("match duplicate arm", enum ++ "x = match E::A { x: 0 } { E::A { x: x } => x, E::A { x: x } => x, E::B { x: x } => x };", "repeats a variant")
            , ("if-let no shorthand", enum ++ "if let E::A { x } = E::A { x: 0 } {};", "expected :")
            , ("if-let unknown field", enum ++ "if let E::A { y: x } = E::A { x: 0 } {};", "has no field")
            , ("if-let duplicate binding", "enum E { A { x: Int, y: Int }, B }; if let E::A { x: a, y: a } = E::B {};", "repeats")
            , ("for mutable counter alias", "for i in 0..3 { p = &mut i; *p = 2; }; return 0;", "cannot assign its loop variable")
            , ("for mutable counter call argument", "fn set(p: &mut Int) -> Int { *p = 2; return 0; }; for i in 0..3 { z = if true { set(&mut i) } else { 0 }; }; return 0;", "cannot assign its loop variable")
            , ("for direct counter write", "for i in 0..3 { i = 2; }; return 0;", "cannot assign its loop variable")
            , ("for hidden counter write in if", "count = 0; for i in 0..3 { count = count + 1; z = if true { i = 2; 0 } else { 0 }; }; return count;", "cannot assign its loop variable")
            , ("for hidden counter write in match", enum ++ "for i in 0..3 { z = match E::A { x: 0 } { E::A { x: n } => { i = 2; n }, E::B { x: n } => n }; }; return 0;", "cannot assign its loop variable")
            , ("for hidden counter write in list", "for i in 0..3 { xs = [if true { i = 2; 0 } else { 0 }]; }; return 0;", "cannot assign its loop variable")
            , ("for hidden counter write in call argument", "fn f(n: Int) -> Int { return n; }; for i in 0..3 { z = f(if true { i = 2; 0 } else { 0 }); }; return 0;", "cannot assign its loop variable")
            , ("for hidden counter write in dereference RHS", "x = 0; p = &mut x; for i in 0..3 { *p = if true { i = 2; 0 } else { 0 }; }; return x;", "cannot assign its loop variable")
            , ("for hidden counter write in condition", "for i in 0..3 { if if true { i = 2; true } else { false } {}; }; return 0;", "cannot assign its loop variable")
            , ("for let initializer sees outer counter", "for i in 0..3 { let i = if true { i = 2; 0 } else { 0 }; }; return 0;", "cannot assign its loop variable")
            , ("for block shadow does not hide later outer write", "for i in 0..3 { { let i = 99; i = 2; }; i = 2; }; return 0;", "cannot assign its loop variable")
            , ("array expressions remain excluded", "x = 1; return #[x, 2];", "")
            ]]
    , testCaseNamedSeq "callable heads (reference, without validating function objects)"
        [(name, pipelineRuns source (VInt (if "mutating" `isInfixOf` name then 1 else if "assignment" `isInfixOf` name then 5 else 4))) | (name, source) <- ergonomicsFunctionPrograms]
    , TestList "package assumptions"
        [testCase name (packageAssumptions source) | (name, source) <-
            [ ("if branch", "fn f(c: Bool) -> Int { return if c { assume false; 1 } else { 2 }; }; return f(true);")
            , ("match branch", "enum E { A, B }; fn f(c: E) -> Int { return match c { E::A => { assume false; 1 }, E::B => 2 }; }; return f(E::A);")
            , ("Block::assume", "p = Addr::null(); b = Block::assume(p, 1); return Addr::free(p, b);")
            ]]
    , testCase "assumptions traverse dereference RHS" $ case assumptionsOf "x = 0; r = &mut x; *r = if true { assume false; 1 } else { 2 }; return x;" of
        Error err -> Just err
        Ok records -> testAssertTrue (any (isInfixOf "assume false") records)
    , testCase "assumptions render branching arguments without treating them as proofs" $ case assumptionsOf "p = Addr::null(); b = Block::assume(p, if true { 1 } else { 2 }); return 0;" of
        Error err -> Just err
        Ok records -> if null records then Just "missing Block::assume" else testAssertTrue (all (not . null) records)
    , testCase "expression fragment" $ case parseExpression "if true { 1 } else { 2 }" of
        Left err -> Just err
        Right IfExpr{} -> Nothing
        Right expr -> Just ("expected IfExpr, got " ++ show expr)
    , testCase "AST parsed and elaborated control-flow round trip" $ case parseSource "let x: Int = if true { let y = 1; y } else { 2 }; return x;" of
        Error err -> Just err
        Ok stmts -> case writeParsed stmts of
            Error err -> Just err
            Ok wire -> case readParsed wire of
                Error err -> Just err
                Ok parsed -> testAssertEq parsed stmts <> case elaborate parsed of
                    Error err -> Just err
                    Ok elaborated@(Elaborated code types) -> case writeElaborated elaborated of
                        Error err -> Just err
                        Ok text -> case readElaborated text of
                            Error err -> Just err
                            Ok (Elaborated code' types') -> testAssertEq (code', types') (code, types)
    ]

packageAssumptions :: String -> TestResult
packageAssumptions source =
    let files = [("ergopkg/package.tersus", ""), ("ergopkg/main.tersus", source)]
     in case loadFromEntry (Modules.resolverFromFiles files) "ergopkg/main.tersus" of
        Left err -> Just err
        Right (Modules.PackageResult pkg) -> case compileModules pkg of
            Error err -> Just err
            Ok compiled -> testAssertTrue (any (\line -> "assume false" `isInfixOf` line || "Block::assume" `isInfixOf` line) (assumptionsOfPackage compiled))
        Right _ -> Just "expected a package"
