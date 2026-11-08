module TestHeldReferences (testHeldReferences, heldPrograms, forwardedUpdateSource) where

import Bootstrap (tersusLlvm)
import CacheLock (openTempFileCloexec)
import Control.Exception (finally)
import Control.Monad (when)
import Data.List (isInfixOf, isPrefixOf)
import Native (buildExecutableFast, readProcessOutput)
import Pipeline (parseSource, validateStatements)
import System.Directory (doesFileExist, getTemporaryDirectory, removeFile)
import System.Exit (ExitCode (..))
import System.IO (hClose)
import System.Process (proc)
import TestHarness
import Utils (Result (..))

forwardedUpdateSource :: String
forwardedUpdateSource = "fn g(r: &mut List<Int>) -> Int writes(r) [{ }] [{ affirm size(*r) = old(size(*r)) + 1; }] { *r = push(clone(*r), 1); return 0; }; fn f(r: &mut List<Int>) -> Int writes(r) [{ }] [{ affirm size(*r) = old(size(*r)) + 1; }] { return g(r); }; xs = [7]; f(&mut xs); affirm size(xs) = 2; return size(xs);"

heldPrograms :: [(String, String, Integer)]
heldPrograms =
    [ ("forwarded incoming update parameter", forwardedUpdateSource, 2)
    , ("overlapping read call arguments", "fn read(a: &Int, b: &Int) -> Int { return *a + *b; }; n = 3; return read(n, n);", 6)
    , ("disjoint mutable and read call arguments", "struct P { x: Int, y: Int }; fn step(a: &mut Int, b: &Int) -> Int writes(a) [{ affirm *a < 100; }] [{ affirm *a = old(*a) + 1; affirm return = *b; }] { *a = *a + 1; return *b; }; p = P { x: 1, y: 7 }; before = step(&mut p.x, &p.y); return p.x + before;", 9)
    , ("cloned shared-reference holder", "trait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; }; struct S { r: &Int }; impl Clone for S { }; x = 1; s = S { r: &x }; t = clone(s); return *t.r;", 1)
    , ("reference carried by Box", "xs = [[7]]; r = &mut xs; b = Box::new(r); t = get(xs, 0); r2 = Box::unbox(b); *r2 = [[9]]; return size(t);", 1)
    , ("intermediate shared reference field", "struct W { r: &List<Int> }; xs = [7]; w = W { r: &xs }; z = &get(*w.r, 0); return *z;", 7)
    , ("readonly scalar holder", w ++ "fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; mutate(w); return n;", 4)
    , ("owned scalar holder", w ++ "fn mutate(w: W) -> Int { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; return n + if true { mutate(w) } else { 0 };", 1)
    , ("readonly ended child", w ++ "fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; parent = w.r; child = &*parent; before = *child; mutate(w); return before + n;", 5)
    , ("variant scalar holder", "enum E { A { r: &mut Int }, B }; fn mutate(v: E::A) -> Int { *v.r = 4; return 0; }; n = 1; e = E::A { r: &mut n }; return n + if true { mutate(e as E::A) } else { 0 };", 1)
    , ("nested scalar holder", w ++ "struct O { w: W, n: Int }; fn mutate(o: &O) -> Int { *o.w.r = 4; return 0; }; n = 1; o = O { w: W { r: &mut n }, n: 7 }; mutate(o); affirm o.n = 7; return n + o.n;", 11)
    , ("explicit selected postfield", w ++ "fn mutate(w: &W) -> Int [{ }] [{ affirm *w.r = 4; }] { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; mutate(w); affirm n = 4; affirm *w.r = 4; return n;", 4)
    , ("implicit invariant postfield", "struct W { r: &mut Int, lo: Int } invariant [{ affirm *r >= lo; }]; fn mutate(w: &W) -> Int { *w.r = w.lo; return 0; }; n = 1; w = W { r: &mut n, lo: 1 }; mutate(w); affirm n >= 1; affirm w.lo = 1; return n;", 1)
    , ("loop preserves private holder frame", "struct W { r: &mut Int, n: Int }; fn tick(w: &W) -> Int [{ }] [{ affirm *w.r = 4; }] { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n, n: 7 }; i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { tick(w); affirm w.n = 7; i = i + 1; }; affirm w.n = 7; return n + w.n;", 11)
    , ("ambiguous owner retains selected holder postfield", w ++ "fn mutate(w: &W) -> Int [{ }] [{ affirm *w.r = 4; }] { *w.r = 4; return 0; }; fn f(c: Bool) -> Int { n = 1; m = 2; r = if c { &mut n } else { &mut m }; w = W { r: r }; mutate(w); affirm *w.r = 4; return *w.r; }; return f(true) + f(false);", 8)
    , ("whole-holder view reads current pointee", w ++ "n = 1; w = W { r: &mut n }; whole = &w; p = w.r; *p = 4; affirm *(*whole).r = 4; return *(*whole).r;", 4)
    , ("input definition retains pre-pointee", w ++ "fn inc(w: &W) -> Int [{ define prior = *w.r; affirm prior < 100; }] [{ affirm *w.r = prior + 1; }] { *w.r = *w.r + 1; return 0; }; n = 1; w = W { r: &mut n }; inc(w); affirm n = 2; return n;", 2)
    , ("ended holder does not constrain reassignment", "struct W { r: &mut Int } invariant [{ affirm *r >= 0; }]; n = 1; w = W { r: &mut n }; p = w.r; before = *p; n = -1; affirm n = -1; return before + n;", 0)
    , ("current pointee at helper call", w ++ "fn read(w: &W) -> Int [{ affirm *w.r = 4; }] [{ affirm return = *w.r; }] { return *w.r; }; fn mutate(w: &W) -> Int { *w.r = 4; return read(w); }; n = 1; w = W { r: &mut n }; return mutate(w);", 4)
    , ("shared reference slot replacement", "struct W { r: &Int }; fn f(a: &Int, b: &Int) -> &Int from a { w = W { r: &b }; p = &mut w; (*p).r = &a; return if true { w.r } else { &a }; }; x = 1; y = 2; r = f(x, y); return *r;", 1)
    , ("whole borrowed shared holder", "struct W { r: &Int }; fn f(p: &mut W, b: &Int) -> &mut W from p { (*p).r = &b; return p; }; a = 1; b = 2; w = W { r: &a }; p = f(&mut w, b); r = (*p).r; return *r;", 2)
    , ("sequence holder releases ended child loan", w ++ "fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; rows = [W { r: &mut n }]; w = first(rows); parent = w.r; child = &*parent; before = *child; mutate(w); return before + n;", 5)
    , ("returned read reference copies owned-pointee field", "struct W { r: &List<Int> }; fn extract(w: &W) -> &List<Int> from w { return w.r; }; a = [1]; w = W { r: &a }; saved = extract(w); return size(*saved);", 1)
    , ("returned holder retains independent storage", "struct W { r: &List<Int> }; fn wrap(a: &List<Int>) -> W from a { return W { r: &a }; }; a = [1]; b = [2]; w = wrap(a); p = &mut w; (*p).r = &b; a = [3]; saved = w.r; return size(*saved);", 1)
    , ("loop private tag changes", "struct W { r: &mut Int, tag: Int }; n = 1; w = W { r: &mut n, tag: 7 }; p = &mut w.tag; i = 0; while i < 1 [{ affirm i >= 0; affirm i <= 1; affirm w.tag = 7 + i; }] shrinks 1 - i { *p = 8; i = i + 1; }; affirm w.tag = 8; return w.tag;", 8)
    , ("cross-holder call updates private tag", "struct W { r: &mut Int }; struct O { r: &mut Int, tag: Int }; fn tick(w: &W) -> Int [{ }] [{ affirm *w.r = 8; }] { *w.r = 8; return 0; }; n = 1; o = O { r: &mut n, tag: 7 }; w = W { r: &mut o.tag }; i = 0; while i < 1 [{ affirm i >= 0; affirm i <= 1; affirm o.tag = 7 + i; }] shrinks 1 - i { tick(w); i = i + 1; }; affirm o.tag = 8; return o.tag;", 8)
    , ("replaced slot retains new list", "struct W { r: &List<Int> }; a = [1]; b = [2, 3]; w = W { r: &a }; p = &mut w; (*p).r = &b; saved = w.r; a = [4]; return size(*saved) + size(a);", 3)
    ]
  where
    w = "struct W { r: &mut Int }; "

rejectedPrograms :: [(String, String, String)]
rejectedPrograms =
    [ ("stale owner equality after holder call", w ++ "fn mutate(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; mutate(w); affirm n = 1; return 0;", "Could not prove: n = 1")
    , ("stale holder equality after direct write", w ++ "n = 1; w = W { r: &mut n }; p = w.r; *p = 4; affirm *w.r = 1; return 0;", "Could not prove:")
    , ("unproved dependent holder invariant", "struct W { r: &mut Int } invariant [{ affirm *r >= 0; }]; n = 1; w = W { r: &mut n }; p = w.r; *p = -1; return 0;", "Could not prove:")
    , ("temporary violation cannot enter helper", "struct W { r: &mut Int } invariant [{ affirm *r >= 0; }]; fn read(w: &W) -> Int { return *w.r; }; fn bad(w: &W) -> Int { *w.r = -1; read(w); *w.r = 1; return 0; }; return 0;", "Could not prove:")
    , ("callee postfield fails owner invariant", "struct P { n: Int } invariant [{ affirm n >= 0; }]; struct W { r: &mut Int }; fn mutate(w: &W) -> Int [{ }] [{ affirm *w.r = -1; }] { *w.r = -1; return 0; }; p = P { n: 1 }; w = W { r: &mut p.n }; mutate(w); return 0;", "Could not prove:")
    , ("loop cannot retain stale holder pointee", w ++ "fn tick(w: &W) -> Int { *w.r = 4; return 0; }; n = 1; w = W { r: &mut n }; i = 0; while i < 1 [{ affirm i >= 0; affirm i <= 1; }] shrinks 1 - i { tick(w); i = i + 1; }; affirm *w.r = 1; return 0;", "Could not prove:")
    , ("loop cannot freeze changing private tag", "struct W { r: &mut Int, tag: Int }; n = 1; w = W { r: &mut n, tag: 7 }; p = &mut w.tag; i = 0; while i < 1 [{ affirm i >= 0; affirm i <= 1; }] shrinks 1 - i { *p = 8; i = i + 1; }; affirm w.tag = 7; return 0;", "Could not prove:")
    , ("cross-holder call cannot freeze private tag", "struct W { r: &mut Int }; struct O { r: &mut Int, tag: Int }; fn tick(w: &W) -> Int { *w.r = 8; return 0; }; n = 1; o = O { r: &mut n, tag: 7 }; w = W { r: &mut o.tag }; i = 0; while i < 1 [{ affirm i >= 0; affirm i <= 1; }] shrinks 1 - i { tick(w); i = i + 1; }; affirm o.tag = 7; return 0;", "Could not prove:")
    , ("unknown postfield cannot keep divisor", w ++ "fn mutate(w: &W) -> Int { *w.r = 0; return 0; }; n = 1; w = W { r: &mut n }; mutate(w); return 10 / n;", "Could not prove:")
    ]
  where
    w = "struct W { r: &mut Int }; "

strictRejected :: String -> String -> TestResult
strictRejected source expected = case parseSource source of
    Error err -> Just ("unexpected parse failure: " ++ err)
    Ok statements -> case validateStatements statements of
        Error err | "Could not prove:" `isPrefixOf` err && expected `isInfixOf` err && not ("does not model yet" `isInfixOf` err) -> Nothing
        Error err -> Just ("wrong rejection: " ++ err)
        Ok _ -> Just "invalid program validated"

nativeResult :: String -> Integer -> IO TestResult
nativeResult source expected = do
    ir <- tersusLlvm source
    case ir of
        Error err -> pure (Just err)
        Ok text -> do
            tmp <- getTemporaryDirectory
            (exe, handle) <- openTempFileCloexec tmp "tersus-held-test"
            hClose handle
            removeFile exe
            (do
                built <- buildExecutableFast [] exe text
                case built of
                    Error err -> pure (Just err)
                    Ok () -> do
                        result <- readProcessOutput (proc exe []) ""
                        pure (testAssertEq result (ExitSuccess, show expected ++ "\n", "")))
                `finally` (doesFileExist exe >>= \exists -> when exists (removeFile exe))

testHeldReferences :: Test
testHeldReferences = TestList "testHeldReferences"
    ([TestCase name (nativeResult source expected) | (name, source, expected) <- heldPrograms]
        ++ [testCase name (strictRejected source expected) | (name, source, expected) <- rejectedPrograms])
