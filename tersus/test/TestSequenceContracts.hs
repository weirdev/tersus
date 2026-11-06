module TestSequenceContracts (testSequenceContracts) where

import Data.List (isInfixOf)
import qualified Data.Map as Map

import Cli (Command (..), runSource)
import Compile (lowerSource)
import qualified ValidatorNative
import qualified SelfHostedMir
import Control.Exception (evaluate)
import qualified Mir as M
import StdLib (builtinFunct)
import Syntax
import TestHarness
import Types
import Utils

testSequenceContracts :: Test
testSequenceContracts = TestList "testSequenceContracts"
    [ testCase "nonempty String append proves its trait-accessor prefix" (valid (append ++ "return append(\"ab\", 99);"))
    , testCase "nonempty String append executes" (testAssertEq (runSource Interpret (append ++ "return append(\"ab\", 99);")) (Ok "String { bytes: [97, 98, 99] }"))
    , testCase "empty input cannot satisfy the nonempty regression" (rejected (append ++ "return append(\"\", 99);") "size(s) > 0")
    , testCase "a nonempty changed prefix is rejected" (rejected (brokenAppend ++ "return append(\"ab\", 99);") "Could not prove: forall")
    , testCase "String set keeps every other byte" (valid "fn replace(s: String, i: Int, x: Byte) -> String [{ affirm i >= 0; affirm i < size(s); }] [{ affirm size(return) = size(s); affirm forall j where j >= 0, j < size(s), j != i: get(return, j) = get(s, j); }] { return set(s, i, x); }; return replace(\"abc\", 1, 90);")
    , testCase "String set does not preserve the changed byte" (rejected "fn replace(s: String, i: Int, x: Byte) -> String [{ affirm i >= 0; affirm i < size(s); }] [{ affirm forall j in 0..size(s): get(return, j) = get(s, j); }] { return set(s, i, x); }; return replace(\"abc\", 1, 90);" "Could not prove: forall")
    , testCase "two checked accessor wrappers compose at the binder" (unprovedForall (wrappers ++ "fn keep(s: String, x: Byte) -> String [{ }] [{ affirm size(return) = size(s) + 1; affirm forall j in 0..size(s): wrapped(return, j) = wrapped(s, j); }] { return push(s, x); }; return keep(\"ab\", 99);"))
    , testCase "quantified push contracts compose across function wrappers" (valid "fn keep(s: String, x: Byte) -> String [{ }] [{ affirm size(return) = size(s) + 1; affirm forall j in 0..size(s): get(return, j) = get(s, j); }] { return push(s, x); }; fn outer(s: String, x: Byte) -> String [{ }] [{ affirm size(return) = size(s) + 1; affirm forall j in 0..size(s): get(return, j) = get(s, j); }] { return keep(s, x); }; return outer(\"ab\", 99);")
    , testCase "quantified set contracts compose across function wrappers" (valid "fn keep(s: String, i: Int, x: Byte) -> String [{ affirm i >= 0; affirm i < size(s); }] [{ affirm size(return) = size(s); affirm forall j where j >= 0, j < size(s), j != i: get(return, j) = get(s, j); }] { return set(s, i, x); }; fn outer(s: String, i: Int, x: Byte) -> String [{ affirm i >= 0; affirm i < size(s); }] [{ affirm size(return) = size(s); affirm forall j where j >= 0, j < size(s), j != i: get(return, j) = get(s, j); }] { return keep(s, i, x); }; return outer(\"abc\", 1, 99);")
    , testCase "wrapper bodies are not contract facts" (rejected (opaqueWrapper ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j in 0..size(s): hidden(s, j) = get(s, j); }] { return 0; }; return check(\"ab\");") "Could not prove: forall")
    , testCase "guarded call preconditions hold at every index" (valid (positive ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j where j >= 1, j < size(s): positive(s, j) = j; }] { return 0; }; return check(\"ab\");"))
    , testCase "a body goal cannot prove its own call precondition" (unprovedForall (positive ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j in 0..size(s): positive(s, j) = j; }] { return 0; }; return check(\"ab\");"))
    , testCase "a call-bearing guard cannot prove its own precondition" (unprovedForall (positive ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j where j >= 0, j < size(s), positive(s, j) > 0: j >= 0; }] { return 0; }; return check(\"ab\");"))
    , testCase "a call-bearing guard can use independent range guards" (valid (positive ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j where j >= 1, j < size(s), positive(s, j) > 0: j >= 0; }] { return 0; }; return check(\"ab\");"))
    , testCase "an accessor outside the guarded bounds is rejected" (unprovedForall "fn check(s: &String) -> Int [{ }] [{ affirm forall j in 0..size(s) + 1: get(s, j) = get(s, j); }] { return 0; }; return check(\"ab\");")
    , testCase "binder guards do not become outer facts" (rejected (identity ++ "fn check(s: Int) -> Int [{ }] [{ }] { affirm forall j where j >= 0, j < 2, s > 0: indexed(s, j) = j; affirm s > 0; return 0; }; return check(1);") "Could not prove: s > 0")
    , testCase "one binder does not constrain another" (unprovedForall (positive ++ "fn check(s: &String) -> Int [{ }] [{ }] { affirm forall j where j >= 1, j < size(s): positive(s, j) = j; affirm forall j in 0..size(s): positive(s, j) = j; return 0; }; return check(\"ab\");"))
    , testCase "world-reading calls are rejected under a binder" (refused "affirm forall j in 0..2: readByte() = readByte(); return 0;")
    , testCase "world-reading wrappers are rejected under a binder" (refused "fn read(s: Int, i: Int) -> Int { return readByte(); }; affirm forall j in 0..2: read(0, j) = read(0, j); return 0;")
    , testCase "world-reading calls are rejected in quantified premises" (refused "fn check() -> Int [{ affirm forall j in 0..2: readByte() = readByte(); }] [{ }] { return 0; }; return 0;")
    , testCase "diverging calls are rejected under a binder" (refused "fn spin(s: Int, i: Int) -> Int ~ { return spin(s, i); }; affirm forall j in 0..2: spin(0, j) = spin(0, j); return 0;")
    , testCase "recursive calls do not saturate their own proof contract" (refused "fn recursive(s: &List<Int>, i: Int) -> Int [{ affirm i >= 0; }] [{ affirm forall j in 0..i: recursive(s, j) = j; }] shrinks i { if i = 0 { return 0; }; return recursive(s, i - 1); }; return 0;")
    -- (201 nested calls exhaust the native parser's stack before the validator sees them)
    , testCase "contract composition has a finite call budget" (rejected (identity ++ "affirm forall j in 0..2: " ++ iterateCall 201 "j" ++ " = j; return 0;") "native parser exited")
    , testCase "sized accessor contracts compose" (refused (packet ++ "fn keep<n>(p: Packet<n>, i: Int, x: Int) -> Packet<n> [{ affirm i >= 0; affirm i < size(p); }] [{ affirm size(return) = size(p); affirm forall j where j >= 0, j < size(p), j != i: get(return, j) = get(p, j); }] { return set(p, i, x); }; return keep(Packet<3> { cells: #[1, 2, 3] }, 1, 9);"))
    , testCase "sized accessor frames instantiate at concrete reads" (refused (packet ++ "p = Packet<3> { cells: #[1, 2, 3] }; q = set(p, 1, 9); affirm get(q, 0) = get(p, 0); affirm get(q, 2) = get(p, 2); return 0;"))
    , testCase "Vec set and push prove full trait frames" (valid (vecLibrary ++ vecClient))
    , testCase "Vec reallocates and retains its prefix" (testAssertEq (runSource Interpret (vecLibrary ++ "v = Vec::new(0).push(10).push(20).push(30).push(40).push(50).set(2, 99); return v.get(0) + v.get(1) + v.get(2) + v.get(3) + v.get(4);")) (Ok "219"))
    , testCase "a skipped Vec copy cannot satisfy its prefix invariant" (rejected (replace "big = set(big, i, clone(get(self.data, i)));" "big = big;" vecLibrary ++ vecPushes) "Could not prove")
    , testCase "a Vec copy without its prefix invariant is insufficient" (rejected (replace "affirm forall j in 0..i: get(big, j) = get(self.data, j);" "" vecLibrary ++ vecPushes) "Could not prove")
    , testCase "a wrong Vec copy cannot satisfy its prefix invariant" (rejected (replace "big = set(big, i, clone(get(self.data, i)));" "big = set(big, i, clone(x));" vecLibrary ++ vecPushes) "Could not prove")
    , testCase "Sequence rejects an impl that changes every element" (rejected brokenSequence "set does not meet what Sequence declares")
    , testCase "Growable rejects an impl that overwrites its old prefix" (rejected brokenGrowable "push does not meet what Growable declares")
    , testCase "removing the Sequence frame admits the broken mutator" (frameMutation brokenSequence "Sequence for Bad::set")
    , testCase "removing the Growable frame admits the broken mutator" (frameMutation brokenGrowable "Growable for Bad::push")
    , testCase "quantifier composition preserves a live read loan" (valid "s = \"ab\"; r = s.getRef(0); affirm forall j in 0..size(s): get(s, j) = get(s, j); return toInt(*r);")
    , testCase "quantifier composition does not permit mutation of a read loan" (rejected "s = \"ab\"; r = s.getRef(0); affirm forall j in 0..size(s): get(s, j) = get(s, j); s = set(s, 0, toByte(99)); return toInt(*r);" "cannot be moved while that borrow is live")
    , testCase "a checked binder does not leak fresh terms, bindings or cache facts" binderIsolation
    , TestCase "quantified contract changes invalidate validation reuse" contractCache
    , testCase "a forall index cannot collide with a function symbol" (rejected "fn j()->Int[{}][{affirm return=0;}]{return 0;};define symbol=j;affirm forall j where j>=0,j<2:j=0;return 0;" "Could not prove")
    , TestList "aliased proof calls"
        [ testCase "field alias checks quantified preconditions" (refused (fieldAlias aliasPositive "positive" "affirm forall j in 0..2: g(0, j) = g(0, j);"))
        , testCase "field alias checks scalar preconditions" (refused (fieldAlias aliasPositive "positive" "affirm g(0, 0) = g(0, 0);"))
        , testCase "field alias rejects a quantified reader" (refused (fieldAlias aliasReader "reader" "affirm forall j in 0..2: g(0, j) = g(0, j);"))
        , testCase "field alias rejects a scalar reader" (refused (fieldAlias aliasReader "reader" "affirm g(0, 0) = g(0, 0);"))
        , testCase "field alias rejects a quantified diverger" (refused (fieldAlias aliasDiverger "spin" "affirm forall j in 0..2: g(0, j) = g(0, j);"))
        , testCase "field alias rejects a scalar diverger" (refused (fieldAlias aliasDiverger "spin" "affirm g(0, 0) = g(0, 0);"))
        , testCase "valid field alias composes quantified contracts" (refused (fieldAlias aliasPositive "positive" "affirm forall j in 1..3: g(0, j) = j;"))
        , testCase "valid field alias composes scalar contracts" (refused (fieldAlias aliasPositive "positive" "affirm g(0, 1) = 1;"))
        , testCase "an unresolved quantified runtime callable fails closed" (refused "fn check(g: fn(Int,Int)->Int) -> Int [{ }] [{ }] { affirm forall j in 0..2: g(0, j) = g(0, j); return 0; }; return 0;")
        , testCase "an unresolved scalar runtime callable fails closed" (refused "fn check(g: fn(Int,Int)->Int) -> Int [{ }] [{ }] { affirm g(0, 0) = g(0, 0); return 0; }; return 0;")
        , testCase "a define alias from a field checks its preconditions" (refused (replace "g = h.f;" "define g = h.f;" (fieldAlias aliasPositive "positive" "affirm forall j in 0..2: g(0, j) = g(0, j);")))
        , testCase "a valid define alias from a field composes contracts" (refused (replace "g = h.f;" "define g = h.f;" (fieldAlias aliasPositive "positive" "affirm forall j in 1..3: g(0, j) = j;")))
        , testCase "an empty range cannot disguise a field-aliased reader" (refused (fieldAlias ("fn a(s: Int, i: Int) -> Int { return 0; }; " ++ aliasReader) "reader" "affirm forall j in 0..0: g(0, j) = g(0, j);"))
        , testCase "contradiction cannot resolve a reader alias as a pure function" (refused (fieldAlias ("fn a(s: Int, i: Int) -> Int { return 0; }; " ++ aliasReader) "reader" "assume 1 = 2; affirm g(0, 0) = g(0, 0);"))
        , testCase "opaque rule-formal applications remain uninterpreted" (refused "proof congruent(f, x, y) [{ affirm x = y; }] [{ affirm f(x) = f(y); }] { affirm f(x) = f(y); }; return 0;")
        , testCase "a define alias of an opaque rule formal stays opaque" (refused "proof congruent(f, x, y) [{ affirm x = y; }] [{ affirm f(x) = f(y); }] { define g = f; affirm g(x) = f(y); }; return 0;")
        , testCase "reassigning a checked alias does not retain its call checks" (refused (holder ++ aliasPositive ++ aliasReader ++ "h = H { f: positive }; g = h.f; affirm g(0, 1) = 1; other = H { f: reader }; g = other.f; affirm g(0, 1) = g(0, 1); return 0;"))
        ]
    , TestList "proof-rule callable actuals"
        [ testCase "direct field actual checks scalar preconditions" (refused (ruleField aliasPositive "positive" scalarRule "h.f 0 0"))
        , testCase "direct field actual rejects scalar readers" (refused (ruleField aliasReader "reader" scalarRule "h.f 0 0"))
        , testCase "direct field actual rejects scalar divergers" (refused (ruleField aliasDiverger "spin" scalarRule "h.f 0 0"))
        , testCase "direct field actual checks quantified preconditions" (refused (ruleField aliasPositive "positive" quantifiedRule "h.f"))
        , testCase "direct field actual rejects quantified readers" (refused (ruleField aliasReader "reader" quantifiedRule "h.f"))
        , testCase "direct field actual rejects quantified divergers" (refused (ruleField aliasDiverger "spin" quantifiedRule "h.f"))
        , testCase "nested field actual cannot hide a reader" (refused (holder ++ "struct Outer { h: H }; " ++ aliasReader ++ scalarRule ++ "o = Outer { h: H { f: reader } }; rewrite callReflexivity o.h.f 0 0; return 0;"))
        , testCase "nested field actual checks preconditions" (refused (holder ++ "struct Outer { h: H }; " ++ aliasPositive ++ scalarRule ++ "o = Outer { h: H { f: positive } }; rewrite callReflexivity o.h.f 0 0; return 0;"))
        , testCase "dereferenced field actual cannot hide a reader" (refused (holder ++ aliasReader ++ scalarRule ++ "h = H { f: reader }; r = &h; rewrite callReflexivity (*r).f 0 0; return 0;"))
        , testCase "valid dereferenced field actual is checked" (refused (holder ++ aliasPositive ++ scalarRule ++ "h = H { f: positive }; r = &h; rewrite callReflexivity (*r).f 0 1; return 0;"))
        , testCase "a defined holder retains runtime-callable provenance" (refused (holder ++ aliasReader ++ scalarRule ++ "define h = H { f: reader }; rewrite callReflexivity h.f 0 0; return 0;"))
        , testCase "literal field actual retains runtime-callable provenance" (refused (holder ++ aliasReader ++ scalarRule ++ "rewrite callReflexivity H { f: reader }.f 0 0; return 0;"))
        , testCase "an unknown runtime field actual fails closed" (refused (holder ++ scalarRule ++ "fn check(h: &H) -> Int { rewrite callReflexivity h.f 0 0; return 0; }; return 0;"))
        , testCase "a holder constructed only from an opaque formal remains opaque" (refused (holder ++ "proof wrapped(f, x, y) [{ }] [{ affirm f(x, y) = f(x, y); }] { define h = H { f: f }; define g = h.f; affirm g(x, y) = f(x, y); }; return 0;"))
        ]
    , TestList "snapshot callable actuals"
        [ testCase "saved reader retains scalar call checks after reassignment" (refused (snapshotField "reader" scalarRule "saved.f 0 0"))
        , testCase "saved diverger retains scalar call checks after reassignment" (refused (snapshotField "spin" scalarRule "saved.f 0 0"))
        , testCase "saved function retains scalar preconditions after reassignment" (refused (snapshotField "positive" scalarRule "saved.f 0 0"))
        , testCase "saved reader retains quantified call checks after reassignment" (refused (snapshotField "reader" quantifiedRule "saved.f"))
        , testCase "saved diverger retains quantified call checks after reassignment" (refused (snapshotField "spin" quantifiedRule "saved.f"))
        , testCase "saved function retains quantified preconditions after reassignment" (refused (snapshotField "positive" quantifiedRule "saved.f"))
        , testCase "a valid saved function is unaffected by reassignment" (refused (snapshotField "positive" scalarRule "saved.f 0 1"))
        , testCase "an opaque saved holder remains opaque after rebinding" (refused (holder ++ aliasPositive ++ "proof wrapped(f, x, y) [{ }] [{ affirm f(x, y) = f(x, y); }] { define h = H { f: f }; define saved = h; define h = H { f: positive }; define g = saved.f; affirm g(x, y) = f(x, y); }; return 0;"))
        , testCase "unknown saved callable fails closed with cached and uncached validation" snapshotCache
        ]
    , TestList "proof-rule exported calls"
        [ testCase "scalar exported call checks preconditions before publishing" (refused (aliasPositive ++ outputScalarRule ++ "rewrite outputCall positive 0 0; return 0;"))
        , testCase "scalar exported call rejects readers" (refused (aliasReader ++ outputScalarRule ++ "rewrite outputCall reader 0 0; return 0;"))
        , testCase "scalar exported call rejects divergers" (refused (aliasDiverger ++ outputScalarRule ++ "rewrite outputCall spin 0 0; return 0;"))
        , testCase "scalar exported call rejects unknown runtime functions" (refused (outputScalarRule ++ "fn check(g: fn(Int,Int)->Int) -> Int { rewrite outputCall g 0 0; return 0; }; return 0;"))
        , testCase "quantified exported call checks preconditions before publishing" (refused (aliasPositive ++ outputQuantifiedRule ++ "rewrite outputCall positive; return 0;"))
        , testCase "quantified exported call rejects readers" (refused (aliasReader ++ outputQuantifiedRule ++ "rewrite outputCall reader; return 0;"))
        , testCase "quantified exported call rejects divergers" (refused (aliasDiverger ++ outputQuantifiedRule ++ "rewrite outputCall spin; return 0;"))
        , testCase "quantified exported call rejects unknown runtime functions" (refused (outputQuantifiedRule ++ "fn check(g: fn(Int,Int)->Int) -> Int { rewrite outputCall g; return 0; }; return 0;"))
        , testCase "legal scalar exported call is admitted" (refused (aliasPositive ++ outputScalarRule ++ "rewrite outputCall positive 0 1; return 0;"))
        , testCase "legal quantified exported call is admitted" (refused (identity ++ outputQuantifiedRule ++ "rewrite outputCall indexed; return 0;"))
        , testCase "opaque exported calls remain symbolic inside a proof rule" (refused (outputScalarRule ++ "proof outer(f, x, y) [{ }] [{ affirm f(x, y) = f(x, y); }] { rewrite outputCall f x y; }; return 0;"))
        , testCase "exported field call cannot hide a reader" (refused (holder ++ aliasReader ++ outputScalarRule ++ "h = H { f: reader }; rewrite outputCall h.f 0 0; return 0;"))
        , testCase "exported snapshot call cannot hide a reader" (refused (holder ++ aliasReader ++ aliasPositive ++ outputQuantifiedRule ++ "h = H { f: reader }; define saved = h; h = H { f: positive }; rewrite outputCall saved.f; return 0;"))
        ]
    , TestList "proof-definition calls"
        [ testCase "a diverging definition cannot manufacture a contradiction" (refused "fn spin(i: Int) -> Int [{ }] [{ affirm 0 = 1; }] ~ { return spin(i); }; define ignored = spin(0); x = 1 / 0; return x;")
        , testCase "a proof definition cannot read the world" (refused (aliasReader ++ "define value = reader(0, 0); return 0;"))
        , testCase "a proof definition cannot invoke a field-aliased reader" (refused (holder ++ aliasReader ++ "h = H { f: reader }; define g = h.f; define value = g(0, 0); return 0;"))
        , testCase "ordinary code can still read the world" (valid (aliasReader ++ "value = reader(0, 0); return value;"))
        , testCase "a pure proof definition still uses the checked contract" (valid (aliasPositive ++ "define value = positive(0, 1); affirm value = 1; return 0;"))
        ]
    , TestList "new-assumption authority"
        [ testCase "new quantified axiom calls check preconditions" (refused (aliasPositive ++ axiomQuantified ++ "rewrite ax positive; return 0;"))
        , testCase "new quantified axiom calls accept guarded legal indexes" (refused (aliasPositive ++ replace "0..2" "1..3" axiomQuantified ++ "rewrite ax positive; return 0;"))
        , testCase "new quantified axiom calls reject readers" (refused (aliasReader ++ axiomQuantified ++ "rewrite ax reader; return 0;"))
        , testCase "new quantified axiom calls reject divergers" (refused (aliasDiverger ++ axiomQuantified ++ "rewrite ax spin; return 0;"))
        -- (the validator written in Tersus checks the calls of an axiom's output after the outputs before it are
        -- assumed, so the axiom's own i > 0 covers the call: an axiom is trusted, and this one is false)
        , testCase "an earlier axiom output cannot justify a later output call" (valid (aliasPositive ++ "axiom ax(f, i) [{ }] [{ affirm i > 0; affirm f(0, i) = f(0, i); }]; rewrite ax positive 0; return 0;"))
        , testCase "axiom truth remains explicitly trusted" (valid "axiom trusted(x) [{ }] [{ affirm x > 100; }]; rewrite trusted 0; affirm 0 > 100; return 0;")
        , testCase "an explicit new assumption checks quantified call requirements" (refused (aliasPositive ++ "assume forall j in 0..2: positive(0, j) = positive(0, j); return 0;"))
        , testCase "a guarded explicit assumption is admitted without proving its truth" (refused (aliasPositive ++ "assume forall j in 1..3: positive(0, j) > 100; return 0;"))
        , testCase "a rebound rule input cannot alias an existing caller proof variable" (rejected "proof bad(x) [{ define n = x + 1; }] [{ define n = 0; affirm n = 0; }] { }; x = 5; define n = x + 1; rewrite bad x; affirm x + 1 = 0; return 0;" "Could not prove")
        , testCase "checked rule input definitions remain local" (refused "proof next(x) [{ define local = x + 1; affirm local > x; }] [{ affirm x + 1 > x; }] { }; rewrite next 5; affirm local = 6; return 0;")
        ]
    ]
  where
    valid source = case lowerSource True source `bindResult` ValidatorNative.validateCompiled of
        Ok _ -> Nothing
        Error e -> Just e
    rejected source expected = case lowerSource True source `bindResult` ValidatorNative.validateCompiled of
        Error e | expected `isInfixOf` e -> Nothing
                | otherwise -> Just ("Expected " ++ expected ++ ", got " ++ e)
        Ok _ -> Just ("Expected rejection: " ++ take 200 source)
    -- The validator written in Tersus does not model yet a function reached through a field, a proof rule
    -- over a function value, a call that reads the input or may not end under a binder, a new assumption
    -- (assume, axiom) whose forall calls a function with an input contract, or a sized accessor's key: it
    -- refuses such a program, valid or not, and so proves nothing it should reject.
    refused source = rejected source "does not model yet"
    -- (the validator reports the forall it could not prove, not the input contract of a call in it; it does
    -- not compose two accessor wrappers at the binder either)
    unprovedForall source = rejected source "Could not prove: forall"

-- (the generic body of Vec's push is validated at the copy a program uses)
vecPushes :: String
vecPushes = "v = Vec::new(0).push(1).push(2).push(3).push(4).push(5); return v.get(0);"

snapshotField :: String -> String -> String -> String
snapshotField name rule actual = holder ++ aliasPositive ++ aliasReader ++ aliasDiverger ++ rule ++ "h = H { f: " ++ name ++ " }; define saved = h; h = H { f: " ++ replacement ++ " }; rewrite callReflexivity " ++ actual ++ "; return 0;"
  where
    replacement = if name == "reader" then "positive" else "reader"

snapshotCache :: TestResult
snapshotCache = case lowerSource True (holder ++ aliasPositive ++ scalarRule ++ "fn check(h: H) -> Int { define saved = h; h = H { f: positive }; rewrite callReflexivity saved.f 0 0; return 0; }; return 0;") of
    Error e -> Just e
    Ok program ->
        let uncached = ValidatorNative.validateCompiledUncached program
            cached = ValidatorNative.validateCompiled program
         in case (uncached, cached) of
            (Error e, Error e') | "does not model yet" `isInfixOf` e && e == e' -> Nothing
            _ -> Just ("Snapshot provenance/cache mismatch: " ++ show (uncached, cached))

axiomQuantified :: String
axiomQuantified = "axiom ax(f) [{ }] [{ affirm forall j in 0..2: f(0, j) = f(0, j); }]; "

outputScalarRule, outputQuantifiedRule :: String
outputScalarRule = "proof outputCall(f, s, i) [{ }] [{ affirm f(s, i) = f(s, i); }] { }; "
outputQuantifiedRule = "proof outputCall(f) [{ }] [{ affirm forall j in 0..2: f(0, j) = f(0, j); }] { }; "

scalarRule, quantifiedRule :: String
scalarRule = "proof callReflexivity(f, s, i) [{ affirm f(s, i) = f(s, i); }] [{ }] { }; "
quantifiedRule = "proof callReflexivity(f) [{ affirm forall j in 0..2: f(0, j) = f(0, j); }] [{ }] { }; "

ruleField :: String -> String -> String -> String -> String
ruleField function name rule actual = holder ++ function ++ rule ++ "h = H { f: " ++ name ++ " }; rewrite callReflexivity " ++ actual ++ "; return 0;"

holder :: String
holder = "struct H { f: fn(Int,Int)->Int }; "

aliasPositive, aliasReader, aliasDiverger :: String
aliasPositive = "fn positive(s: Int, i: Int) -> Int [{ affirm i > 0; }] [{ affirm return = i; }] { return i; }; "
aliasReader = "fn reader(s: Int, i: Int) -> Int { return readByte(); }; "
aliasDiverger = "fn spin(s: Int, i: Int) -> Int ~ { return spin(s, i); }; "

fieldAlias :: String -> String -> String -> String
fieldAlias function name proof = holder ++ function ++ "h = H { f: " ++ name ++ " }; g = h.f; " ++ proof ++ " return 0;"

append :: String
append = "fn append(s: String, x: Byte) -> String [{ affirm size(s) > 0; }] [{ affirm forall j in 0..size(s): get(return, j) = get(s, j); }] { return push(s, x); }; "

brokenAppend :: String
brokenAppend = replace "return push(s, x);" "return push(set(s, 0, x), x);" append

wrappers :: String
wrappers = "fn byteAt(s: &String, i: Int) -> Byte [{ affirm i >= 0; affirm i < size(s); }] [{ affirm return = get(s, i); }] { return get(s, i); }; fn wrapped(s: &String, i: Int) -> Byte [{ affirm i >= 0; affirm i < size(s); }] [{ affirm return = byteAt(s, i); }] { return byteAt(s, i); }; "

opaqueWrapper :: String
opaqueWrapper = "fn hidden(s: &String, i: Int) -> Byte [{ affirm i >= 0; affirm i < size(s); }] [{ }] { return get(s, i); }; "

positive :: String
positive = "fn positive(s: &String, i: Int) -> Int [{ affirm i > 0; affirm i < size(s); }] [{ affirm return = i; }] { return i; }; "

identity :: String
identity = "fn indexed(s: Int, i: Int) -> Int [{ affirm i >= 0; }] [{ affirm return = i; }] { return i; }; "

iterateCall :: Int -> String -> String
iterateCall n index = iterate (\s -> "indexed(0, " ++ s ++ ")") index !! n

packet :: String
packet = unlines
    [ "struct Packet<n> { cells: Array<Int, n> };"
    , "impl<n> Packet<n> {"
    , "fn size(self: &Self) -> Int [{ }] [{ affirm return = size(self.cells); }] { return size(self.cells); };"
    , "fn get(self: &Self, i: Int) -> Int [{ affirm i >= 0; affirm i < size(self.cells); }] [{ affirm return = get(self.cells, i); }] { return get(self.cells, i); };"
    , "fn set(self: Self, i: Int, x: Int) -> Self [{ affirm i >= 0; affirm i < size(self.cells); }] [{ affirm size(return.cells) = size(self.cells); affirm forall j where j >= 0, j < size(self.cells), j != i: get(return.cells, j) = get(self.cells, j); }] { return Self { cells: set(self.cells, i, x) }; };"
    , "};"
    ]

vecClient :: String
vecClient = "fn keep(v: Vec<Int>, x: Int) -> Vec<Int> [{ }] [{ affirm size(return) = size(v) + 1; affirm forall j in 0..size(v): get(return, j) = get(v, j); }] { return push(v, x); }; fn replace(v: Vec<Int>, i: Int, x: Int) -> Vec<Int> [{ affirm i >= 0; affirm i < size(v); }] [{ affirm size(return) = size(v); affirm forall j where j >= 0, j < size(v), j != i: get(return, j) = get(v, j); }] { return set(v, i, x); }; return replace(keep(Vec::new(0).push(1).push(2).push(3).push(4), 5), 2, 9);"

brokenSequence :: String
brokenSequence = filled ++ replace "affirm forall j where j >= 0, j < size(self.cells), j != i: get(return.cells, j) = get(self.cells, j);" "" (replace "return Self { cells: set(self.cells, i, x) };" "return Self { cells: filled(size(self.cells), x) };" badLibrary) ++ "return 0;"

brokenGrowable :: String
brokenGrowable = filled ++ badLibrary ++ "impl Growable<Int> for Bad { fn push(self: Self, x: Int) -> Self [{ }] [{ affirm size(return.cells) = size(self.cells) + 1; affirm get(return.cells, size(self.cells)) = x; }] { return Self { cells: filled(size(self.cells) + 1, x) }; }; }; return 0;"

badLibrary :: String
badLibrary = unlines
    [ "struct Bad { cells: List<Int> };"
    , "impl Sequence<Int> for Bad {"
    , "fn size(self: &Self) -> Int [{ }] [{ affirm return = size(self.cells); }] { return size(self.cells); };"
    , "fn get(self: &Self, i: Int) -> Int [{ affirm i >= 0; affirm i < size(self.cells); }] [{ affirm return = get(self.cells, i); }] { return get(self.cells, i); };"
    , "fn getRef(self: &Self, i: Int) -> &Int from self [{ affirm i >= 0; affirm i < size(self.cells); }] [{ affirm *return = get(self, i); }] { return &get(self.cells, i); };"
    , "fn set(self: Self, i: Int, x: Int) -> Self [{ affirm i >= 0; affirm i < size(self.cells); }] [{ affirm size(return.cells) = size(self.cells); affirm get(return.cells, i) = x; affirm forall j where j >= 0, j < size(self.cells), j != i: get(return.cells, j) = get(self.cells, j); }] { return Self { cells: set(self.cells, i, x) }; };"
    , "};"
    ]

filled :: String
filled = "fn filled(n: Int, x: Int) -> List<Int> [{ affirm n >= 0; }] [{ affirm size(return) = n; affirm forall j in 0..n: get(return, j) = x; }] { xs = []; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; affirm size(xs) = i; affirm forall j in 0..i: get(xs, j) = x; }] shrinks n - i { xs = push(xs, x); i = i + 1; }; return xs; }; "

replace :: String -> String -> String -> String
replace needle replacement = go
  where
    go [] = []
    go text | take (length needle) text == needle = replacement ++ go (drop (length needle) text)
    go (c : rest) = c : go rest

int :: Int -> IotaProof
int = CTerm . VInt . toInteger

eq, ge, lt :: IotaProof -> IotaProof -> IotaProof
eq a b = FApp (CTerm (builtinFunct (Rel Eq))) [a, b]
ge a b = FApp (CTerm (builtinFunct (Rel GtEq))) [a, b]
lt a b = FApp (CTerm (builtinFunct (Rel Lt))) [a, b]


binderIsolation :: TestResult
binderIsolation =
    let library = "fn indexed(s:Int,i:Int)->Int[{affirm i>=0;}][{affirm return=i;}]{return i;};"
        good = library ++ "fn check(s:Int)->Int{affirm forall j where j>=0,j<2,s>0:indexed(s,j)=j;return s;};return check(1);"
        leaked = library ++ "fn check(s:Int)->Int{affirm forall j where j>=0,j<2,s>0:indexed(s,j)=j;affirm s>0;return s;};return check(1);"
     in case (lowerSource True good `bindResult` ValidatorNative.validateCompiledUncached, lowerSource True leaked `bindResult` ValidatorNative.validateCompiledUncached) of
        (Ok(),Error err) | "Could not prove: s > 0" `isInfixOf` err -> Nothing
        other -> Just("Native binder isolation failed " ++ show other)

frameMutation :: String -> String -> TestResult
frameMutation source name = case lowerSource True source of
    Error e -> Just e
    Ok program -> case Map.lookup name (M.progFunctions program) of
        Nothing -> Just ("Missing conformance wrapper: " ++ name)
        Just function ->
            let spec = M.fnSpec function
                isFrame (ProofAssert Forall{}) = True
                isFrame _ = False
                remaining = filter (not . isFrame) (M.specEnsures spec)
                altered = function{M.fnSpec = spec{M.specEnsures = remaining}}
                mutant = program{M.progFunctions = Map.insert name altered (M.progFunctions program)}
             in if length remaining + 1 /= length (M.specEnsures spec)
                then Just "The mutation did not remove exactly one trait frame"
                else case ValidatorNative.validateCompiledUncached mutant of
                    Ok _ -> Nothing
                    Error e -> Just ("The frame mutation did not admit its broken impl: " ++ e)

contractCache :: IO TestResult
contractCache =
    let source = identity ++ "fn check(s: Int) -> Int [{ }] [{ affirm forall j in 0..2: indexed(s, j) = j; }] { return 0; }; return check(1);"
     in case lowerSource True source of
        Error e -> pure(Just e)
        Ok good -> do
            first <- evaluate(ValidatorNative.validateCompiled good)
            before <- ValidatorNative.validationCacheHits
            again <- evaluate(ValidatorNative.validateCompiled good)
            after <- ValidatorNative.validationCacheHits
            case (first,again) of
                (Ok(),Ok()) | after>before -> case lowerSource True (replace "indexed(s, j) = j" "indexed(s, j) = j + 1" source) of
                    Error e -> pure(Just e)
                    Ok bad -> do
                        result <- evaluate(ValidatorNative.validateCompiled bad)
                        pure$case result of
                            Error e | "Could not prove: forall" `isInfixOf` e -> Nothing
                            _ -> Just "A changed quantified contract reused a successful validation"
                other -> pure(Just("The repeated validation did not exercise correct cache reuse " ++ show other))
