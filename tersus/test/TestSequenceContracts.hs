module TestSequenceContracts (testSequenceContracts) where

import Data.List (isInfixOf)
import qualified Data.Map as Map

import Cli (Command (..), runSource)
import Compile (lowerSource)
import qualified Ghost
import qualified Mir as M
import qualified MirValidate
import qualified ProofEngine as Engine
import ProofState
import ProofHelpers (proofIotas)
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
    , testCase "two checked accessor wrappers compose at the binder" (valid (wrappers ++ "fn keep(s: String, x: Byte) -> String [{ }] [{ affirm size(return) = size(s) + 1; affirm forall j in 0..size(s): wrapped(return, j) = wrapped(s, j); }] { return push(s, x); }; return keep(\"ab\", 99);"))
    , testCase "quantified push contracts compose across function wrappers" (valid "fn keep(s: String, x: Byte) -> String [{ }] [{ affirm size(return) = size(s) + 1; affirm forall j in 0..size(s): get(return, j) = get(s, j); }] { return push(s, x); }; fn outer(s: String, x: Byte) -> String [{ }] [{ affirm size(return) = size(s) + 1; affirm forall j in 0..size(s): get(return, j) = get(s, j); }] { return keep(s, x); }; return outer(\"ab\", 99);")
    , testCase "quantified set contracts compose across function wrappers" (valid "fn keep(s: String, i: Int, x: Byte) -> String [{ affirm i >= 0; affirm i < size(s); }] [{ affirm size(return) = size(s); affirm forall j where j >= 0, j < size(s), j != i: get(return, j) = get(s, j); }] { return set(s, i, x); }; fn outer(s: String, i: Int, x: Byte) -> String [{ affirm i >= 0; affirm i < size(s); }] [{ affirm size(return) = size(s); affirm forall j where j >= 0, j < size(s), j != i: get(return, j) = get(s, j); }] { return keep(s, i, x); }; return outer(\"abc\", 1, 99);")
    , testCase "wrapper bodies are not contract facts" (rejected (opaqueWrapper ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j in 0..size(s): hidden(s, j) = get(s, j); }] { return 0; }; return check(\"ab\");") "Could not prove: forall")
    , testCase "guarded call preconditions hold at every index" (valid (positive ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j where j >= 1, j < size(s): positive(s, j) = j; }] { return 0; }; return check(\"ab\");"))
    , testCase "a body goal cannot prove its own call precondition" (rejected (positive ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j in 0..size(s): positive(s, j) = j; }] { return 0; }; return check(\"ab\");") "i > 0")
    , testCase "a call-bearing guard cannot prove its own precondition" (rejected (positive ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j where j >= 0, j < size(s), positive(s, j) > 0: j >= 0; }] { return 0; }; return check(\"ab\");") "i > 0")
    , testCase "a call-bearing guard can use independent range guards" (valid (positive ++ "fn check(s: &String) -> Int [{ }] [{ affirm forall j where j >= 1, j < size(s), positive(s, j) > 0: j >= 0; }] { return 0; }; return check(\"ab\");"))
    , testCase "an accessor outside the guarded bounds is rejected" (rejected "fn check(s: &String) -> Int [{ }] [{ affirm forall j in 0..size(s) + 1: get(s, j) = get(s, j); }] { return 0; }; return check(\"ab\");" "i < size(self.bytes)")
    , testCase "binder guards do not become outer facts" (rejected (identity ++ "fn check(s: Int) -> Int [{ }] [{ }] { affirm forall j where j >= 0, j < 2, s > 0: indexed(s, j) = j; affirm s > 0; return 0; }; return check(1);") "Could not prove: s > 0")
    , testCase "one binder does not constrain another" (rejected (positive ++ "fn check(s: &String) -> Int [{ }] [{ }] { affirm forall j where j >= 1, j < size(s): positive(s, j) = j; affirm forall j in 0..size(s): positive(s, j) = j; return 0; }; return check(\"ab\");") "i > 0")
    , testCase "world-reading calls are rejected under a binder" (rejected "affirm forall j in 0..2: readByte() = readByte(); return 0;" "has no value in a proof")
    , testCase "world-reading wrappers are rejected under a binder" (rejected "fn read(s: Int, i: Int) -> Int { return readByte(); }; affirm forall j in 0..2: read(0, j) = read(0, j); return 0;" "reads the input")
    , testCase "world-reading calls are rejected in quantified premises" (rejected "fn check() -> Int [{ affirm forall j in 0..2: readByte() = readByte(); }] [{ }] { return 0; }; return 0;" "has no value in a proof")
    , testCase "diverging calls are rejected under a binder" (rejected "fn spin(s: Int, i: Int) -> Int ~ { return spin(s, i); }; affirm forall j in 0..2: spin(0, j) = spin(0, j); return 0;" "declared ~")
    , testCase "recursive calls do not saturate their own proof contract" (rejected "fn recursive(s: &List<Int>, i: Int) -> Int [{ affirm i >= 0; }] [{ affirm forall j in 0..i: recursive(s, j) = j; }] shrinks i { if i = 0 { return 0; }; return recursive(s, i - 1); }; return 0;" "from its own contract or body")
    , testCase "contract composition has a finite call budget" (rejected (identity ++ "affirm forall j in 0..2: " ++ iterateCall 201 "j" ++ " = j; return 0;") "budget exhausted")
    , testCase "sized accessor contracts compose" (valid (packet ++ "fn keep<n>(p: Packet<n>, i: Int, x: Int) -> Packet<n> [{ affirm i >= 0; affirm i < size(p); }] [{ affirm size(return) = size(p); affirm forall j where j >= 0, j < size(p), j != i: get(return, j) = get(p, j); }] { return set(p, i, x); }; return keep(Packet<3> { cells: #[1, 2, 3] }, 1, 9);"))
    , testCase "sized accessor frames instantiate at concrete reads" (valid (packet ++ "p = Packet<3> { cells: #[1, 2, 3] }; q = set(p, 1, 9); affirm get(q, 0) = get(p, 0); affirm get(q, 2) = get(p, 2); return 0;"))
    , testCase "Vec set and push prove full trait frames" (valid (vecLibrary ++ vecClient))
    , testCase "Vec reallocates and retains its prefix" (testAssertEq (runSource Interpret (vecLibrary ++ "v = Vec::new(0).push(10).push(20).push(30).push(40).push(50).set(2, 99); return v.get(0) + v.get(1) + v.get(2) + v.get(3) + v.get(4);")) (Ok "219"))
    , testCase "a skipped Vec copy cannot satisfy its prefix invariant" (rejected (replace "big = set(big, i, clone(get(self.data, i)));" "big = big;" vecLibrary) "Loop invariant is not preserved")
    , testCase "a Vec copy without its prefix invariant is insufficient" (rejected (replace "affirm forall j in 0..i: get(big, j) = get(self.data, j);" "" vecLibrary) "Could not prove: forall")
    , testCase "a wrong Vec copy cannot satisfy its prefix invariant" (rejected (replace "big = set(big, i, clone(get(self.data, i)));" "big = set(big, i, clone(x));" vecLibrary) "Loop invariant is not preserved")
    , testCase "Sequence rejects an impl that changes every element" (rejected brokenSequence "set does not meet what Sequence declares")
    , testCase "Growable rejects an impl that overwrites its old prefix" (rejected brokenGrowable "push does not meet what Growable declares")
    , testCase "removing the Sequence frame admits the broken mutator" (frameMutation brokenSequence "Sequence for Bad::set")
    , testCase "removing the Growable frame admits the broken mutator" (frameMutation brokenGrowable "Growable for Bad::push")
    , testCase "quantifier composition preserves a live read loan" (valid "s = \"ab\"; r = s.getRef(0); affirm forall j in 0..size(s): get(s, j) = get(s, j); return toInt(*r);")
    , testCase "quantifier composition does not permit mutation of a read loan" (rejected "s = \"ab\"; r = s.getRef(0); affirm forall j in 0..size(s): get(s, j) = get(s, j); s = set(s, 0, toByte(99)); return toInt(*r);" "cannot be moved while that borrow is live")
    , testCase "a checked binder does not leak fresh terms, bindings or cache facts" binderIsolation
    , testCase "quantified contract changes invalidate validation reuse" contractCache
    , testCase "a forall index cannot collide with a function symbol" (testAssertEq (Engine.entails (Forall "j" [ge (BVar "j") (int 0), lt (BVar "j") (int 2)] (eq (BVar "j") (int 0))) (Engine.proofContextFromFacts [eq (ATerm (Iota "$j")) (int 0), eq (ATerm (Iota "$forall j 0")) (int 0)])) False)
    , testCase "callee equivalence uses congruence, not explosion, with or without a cache" $
        let source = ATerm (Iota "callable")
            reader = ATerm (Iota "$reader")
            pureFunction = ATerm (Iota "$pure")
            facts = [eq source reader, eq (int 1) (int 2)]
            contexts = [Engine.proofContextFromFacts facts, Engine.proofContextFromCache (Just (Engine.factCacheAdd Engine.emptyFactCache facts)) facts]
         in testAssertEq [Engine.equivalentTerms source [reader, pureFunction] context | context <- contexts] [[True, False], [True, False]]
    , TestList "aliased proof calls"
        [ testCase "field alias checks quantified preconditions" (rejected (fieldAlias aliasPositive "positive" "affirm forall j in 0..2: g(0, j) = g(0, j);") "i > 0")
        , testCase "field alias checks scalar preconditions" (rejected (fieldAlias aliasPositive "positive" "affirm g(0, 0) = g(0, 0);") "i > 0")
        , testCase "field alias rejects a quantified reader" (rejected (fieldAlias aliasReader "reader" "affirm forall j in 0..2: g(0, j) = g(0, j);") "reads the input")
        , testCase "field alias rejects a scalar reader" (rejected (fieldAlias aliasReader "reader" "affirm g(0, 0) = g(0, 0);") "reads the input")
        , testCase "field alias rejects a quantified diverger" (rejected (fieldAlias aliasDiverger "spin" "affirm forall j in 0..2: g(0, j) = g(0, j);") "declared ~")
        , testCase "field alias rejects a scalar diverger" (rejected (fieldAlias aliasDiverger "spin" "affirm g(0, 0) = g(0, 0);") "declared ~")
        , testCase "valid field alias composes quantified contracts" (valid (fieldAlias aliasPositive "positive" "affirm forall j in 1..3: g(0, j) = j;"))
        , testCase "valid field alias composes scalar contracts" (valid (fieldAlias aliasPositive "positive" "affirm g(0, 1) = 1;"))
        , testCase "an unresolved quantified runtime callable fails closed" (rejected "fn check(g: fn(Int,Int)->Int) -> Int [{ }] [{ }] { affirm forall j in 0..2: g(0, j) = g(0, j); return 0; }; return 0;" "Function object not validated")
        , testCase "an unresolved scalar runtime callable fails closed" (rejected "fn check(g: fn(Int,Int)->Int) -> Int [{ }] [{ }] { affirm g(0, 0) = g(0, 0); return 0; }; return 0;" "Function object not validated")
        , testCase "a define alias from a field checks its preconditions" (rejected (replace "g = h.f;" "define g = h.f;" (fieldAlias aliasPositive "positive" "affirm forall j in 0..2: g(0, j) = g(0, j);")) "i > 0")
        , testCase "a valid define alias from a field composes contracts" (valid (replace "g = h.f;" "define g = h.f;" (fieldAlias aliasPositive "positive" "affirm forall j in 1..3: g(0, j) = j;")))
        , testCase "an empty range cannot disguise a field-aliased reader" (rejected (fieldAlias ("fn a(s: Int, i: Int) -> Int { return 0; }; " ++ aliasReader) "reader" "affirm forall j in 0..0: g(0, j) = g(0, j);") "reads the input")
        , testCase "contradiction cannot resolve a reader alias as a pure function" (rejected (fieldAlias ("fn a(s: Int, i: Int) -> Int { return 0; }; " ++ aliasReader) "reader" "assume 1 = 2; affirm g(0, 0) = g(0, 0);") "reads the input")
        , testCase "opaque rule-formal applications remain uninterpreted" (valid "proof congruent(f, x, y) [{ affirm x = y; }] [{ affirm f(x) = f(y); }] { affirm f(x) = f(y); }; return 0;")
        , testCase "a define alias of an opaque rule formal stays opaque" (valid "proof congruent(f, x, y) [{ affirm x = y; }] [{ affirm f(x) = f(y); }] { define g = f; affirm g(x) = f(y); }; return 0;")
        , testCase "reassigning a checked alias does not retain its call checks" (rejected (holder ++ aliasPositive ++ aliasReader ++ "h = H { f: positive }; g = h.f; affirm g(0, 1) = 1; other = H { f: reader }; g = other.f; affirm g(0, 1) = g(0, 1); return 0;") "reads the input")
        ]
    , TestList "proof-rule callable actuals"
        [ testCase "direct field actual checks scalar preconditions" (rejected (ruleField aliasPositive "positive" scalarRule "h.f 0 0") "i > 0")
        , testCase "direct field actual rejects scalar readers" (rejected (ruleField aliasReader "reader" scalarRule "h.f 0 0") "reads the input")
        , testCase "direct field actual rejects scalar divergers" (rejected (ruleField aliasDiverger "spin" scalarRule "h.f 0 0") "declared ~")
        , testCase "direct field actual checks quantified preconditions" (rejected (ruleField aliasPositive "positive" quantifiedRule "h.f") "i > 0")
        , testCase "direct field actual rejects quantified readers" (rejected (ruleField aliasReader "reader" quantifiedRule "h.f") "reads the input")
        , testCase "direct field actual rejects quantified divergers" (rejected (ruleField aliasDiverger "spin" quantifiedRule "h.f") "declared ~")
        , testCase "nested field actual cannot hide a reader" (rejected (holder ++ "struct Outer { h: H }; " ++ aliasReader ++ scalarRule ++ "o = Outer { h: H { f: reader } }; rewrite callReflexivity o.h.f 0 0; return 0;") "reads the input")
        , testCase "nested field actual checks preconditions" (rejected (holder ++ "struct Outer { h: H }; " ++ aliasPositive ++ scalarRule ++ "o = Outer { h: H { f: positive } }; rewrite callReflexivity o.h.f 0 0; return 0;") "i > 0")
        , testCase "dereferenced field actual cannot hide a reader" (rejected (holder ++ aliasReader ++ scalarRule ++ "h = H { f: reader }; r = &h; rewrite callReflexivity (*r).f 0 0; return 0;") "reads the input")
        , testCase "valid dereferenced field actual is checked" (valid (holder ++ aliasPositive ++ scalarRule ++ "h = H { f: positive }; r = &h; rewrite callReflexivity (*r).f 0 1; return 0;"))
        , testCase "a defined holder retains runtime-callable provenance" (rejected (holder ++ aliasReader ++ scalarRule ++ "define h = H { f: reader }; rewrite callReflexivity h.f 0 0; return 0;") "reads the input")
        , testCase "literal field actual retains runtime-callable provenance" (rejected (holder ++ aliasReader ++ scalarRule ++ "rewrite callReflexivity H { f: reader }.f 0 0; return 0;") "reads the input")
        , testCase "an unknown runtime field actual fails closed" (rejected (holder ++ scalarRule ++ "fn check(h: &H) -> Int { rewrite callReflexivity h.f 0 0; return 0; }; return 0;") "Function object not validated")
        , testCase "a holder constructed only from an opaque formal remains opaque" (valid (holder ++ "proof wrapped(f, x, y) [{ }] [{ affirm f(x, y) = f(x, y); }] { define h = H { f: f }; define g = h.f; affirm g(x, y) = f(x, y); }; return 0;"))
        ]
    , TestList "snapshot callable actuals"
        [ testCase "saved reader retains scalar call checks after reassignment" (rejected (snapshotField "reader" scalarRule "saved.f 0 0") "reads the input")
        , testCase "saved diverger retains scalar call checks after reassignment" (rejected (snapshotField "spin" scalarRule "saved.f 0 0") "declared ~")
        , testCase "saved function retains scalar preconditions after reassignment" (rejected (snapshotField "positive" scalarRule "saved.f 0 0") "i > 0")
        , testCase "saved reader retains quantified call checks after reassignment" (rejected (snapshotField "reader" quantifiedRule "saved.f") "reads the input")
        , testCase "saved diverger retains quantified call checks after reassignment" (rejected (snapshotField "spin" quantifiedRule "saved.f") "declared ~")
        , testCase "saved function retains quantified preconditions after reassignment" (rejected (snapshotField "positive" quantifiedRule "saved.f") "i > 0")
        , testCase "a valid saved function is unaffected by reassignment" (valid (snapshotField "positive" scalarRule "saved.f 0 1"))
        , testCase "an opaque saved holder remains opaque after rebinding" (valid (holder ++ aliasPositive ++ "proof wrapped(f, x, y) [{ }] [{ affirm f(x, y) = f(x, y); }] { define h = H { f: f }; define saved = h; define h = H { f: positive }; define g = saved.f; affirm g(x, y) = f(x, y); }; return 0;"))
        , testCase "unknown saved callable fails closed with cached and uncached validation" snapshotCache
        ]
    , TestList "proof-rule exported calls"
        [ testCase "scalar exported call checks preconditions before publishing" (rejected (aliasPositive ++ outputScalarRule ++ "rewrite outputCall positive 0 0; return 0;") "i > 0")
        , testCase "scalar exported call rejects readers" (rejected (aliasReader ++ outputScalarRule ++ "rewrite outputCall reader 0 0; return 0;") "reads the input")
        , testCase "scalar exported call rejects divergers" (rejected (aliasDiverger ++ outputScalarRule ++ "rewrite outputCall spin 0 0; return 0;") "declared ~")
        , testCase "scalar exported call rejects unknown runtime functions" (rejected (outputScalarRule ++ "fn check(g: fn(Int,Int)->Int) -> Int { rewrite outputCall g 0 0; return 0; }; return 0;") "Function object not validated")
        , testCase "quantified exported call checks preconditions before publishing" (rejected (aliasPositive ++ outputQuantifiedRule ++ "rewrite outputCall positive; return 0;") "i > 0")
        , testCase "quantified exported call rejects readers" (rejected (aliasReader ++ outputQuantifiedRule ++ "rewrite outputCall reader; return 0;") "reads the input")
        , testCase "quantified exported call rejects divergers" (rejected (aliasDiverger ++ outputQuantifiedRule ++ "rewrite outputCall spin; return 0;") "declared ~")
        , testCase "quantified exported call rejects unknown runtime functions" (rejected (outputQuantifiedRule ++ "fn check(g: fn(Int,Int)->Int) -> Int { rewrite outputCall g; return 0; }; return 0;") "Function object not validated")
        , testCase "legal scalar exported call is admitted" (valid (aliasPositive ++ outputScalarRule ++ "rewrite outputCall positive 0 1; return 0;"))
        , testCase "legal quantified exported call is admitted" (valid (identity ++ outputQuantifiedRule ++ "rewrite outputCall indexed; return 0;"))
        , testCase "opaque exported calls remain symbolic inside a proof rule" (valid (outputScalarRule ++ "proof outer(f, x, y) [{ }] [{ affirm f(x, y) = f(x, y); }] { rewrite outputCall f x y; }; return 0;"))
        , testCase "exported field call cannot hide a reader" (rejected (holder ++ aliasReader ++ outputScalarRule ++ "h = H { f: reader }; rewrite outputCall h.f 0 0; return 0;") "reads the input")
        , testCase "exported snapshot call cannot hide a reader" (rejected (holder ++ aliasReader ++ aliasPositive ++ outputQuantifiedRule ++ "h = H { f: reader }; define saved = h; h = H { f: positive }; rewrite outputCall saved.f; return 0;") "reads the input")
        ]
    , TestList "proof-definition calls"
        [ testCase "a diverging definition cannot manufacture a contradiction" (rejected "fn spin(i: Int) -> Int [{ }] [{ affirm 0 = 1; }] ~ { return spin(i); }; define ignored = spin(0); x = 1 / 0; return x;" "declared ~")
        , testCase "a proof definition cannot read the world" (rejected (aliasReader ++ "define value = reader(0, 0); return 0;") "reads the input")
        , testCase "a proof definition cannot invoke a field-aliased reader" (rejected (holder ++ aliasReader ++ "h = H { f: reader }; define g = h.f; define value = g(0, 0); return 0;") "reads the input")
        , testCase "ordinary code can still read the world" (valid (aliasReader ++ "value = reader(0, 0); return value;"))
        , testCase "a pure proof definition still uses the checked contract" (valid (aliasPositive ++ "define value = positive(0, 1); affirm value = 1; return 0;"))
        ]
    , TestList "new-assumption authority"
        [ testCase "new quantified axiom calls check preconditions" (rejected (aliasPositive ++ axiomQuantified ++ "rewrite ax positive; return 0;") "i > 0")
        , testCase "new quantified axiom calls accept guarded legal indexes" (valid (aliasPositive ++ replace "0..2" "1..3" axiomQuantified ++ "rewrite ax positive; return 0;"))
        , testCase "new quantified axiom calls reject readers" (rejected (aliasReader ++ axiomQuantified ++ "rewrite ax reader; return 0;") "reads the input")
        , testCase "new quantified axiom calls reject divergers" (rejected (aliasDiverger ++ axiomQuantified ++ "rewrite ax spin; return 0;") "declared ~")
        , testCase "an earlier axiom output cannot justify a later output call" (rejected (aliasPositive ++ "axiom ax(f, i) [{ }] [{ affirm i > 0; affirm f(0, i) = f(0, i); }]; rewrite ax positive 0; return 0;") "i > 0")
        , testCase "axiom truth remains explicitly trusted" (valid "axiom trusted(x) [{ }] [{ affirm x > 100; }]; rewrite trusted 0; affirm 0 > 100; return 0;")
        , testCase "an explicit new assumption checks quantified call requirements" (rejected (aliasPositive ++ "assume forall j in 0..2: positive(0, j) = positive(0, j); return 0;") "i > 0")
        , testCase "a guarded explicit assumption is admitted without proving its truth" (valid (aliasPositive ++ "assume forall j in 1..3: positive(0, j) > 100; return 0;"))
        , testCase "a rebound rule input cannot alias an existing caller proof variable" (rejected "proof bad(x) [{ define n = x + 1; }] [{ define n = 0; affirm n = 0; }] { }; x = 5; define n = x + 1; rewrite bad x; affirm x + 1 = 0; return 0;" "Could not prove")
        , testCase "checked rule input definitions remain local" (rejected "proof next(x) [{ define local = x + 1; affirm local > x; }] [{ affirm x + 1 > x; }] { }; rewrite next 5; affirm local = 6; return 0;" "Variable not found in proof map: local")
        ]
    , testCase "sized triggers retain the accessor, receiver and hidden sizes" sizedTriggers
    ]
  where
    valid source = case lowerSource True source `bindResult` MirValidate.validateProgram of
        Ok _ -> Nothing
        Error e -> Just e
    rejected source expected = case lowerSource True source `bindResult` MirValidate.validateProgram of
        Error e | expected `isInfixOf` e -> Nothing
                | otherwise -> Just ("Expected " ++ expected ++ ", got " ++ e)
        Ok _ -> Just ("Expected rejection: " ++ take 200 source)

snapshotField :: String -> String -> String -> String
snapshotField name rule actual = holder ++ aliasPositive ++ aliasReader ++ aliasDiverger ++ rule ++ "h = H { f: " ++ name ++ " }; define saved = h; h = H { f: " ++ replacement ++ " }; rewrite callReflexivity " ++ actual ++ "; return 0;"
  where
    replacement = if name == "reader" then "positive" else "reader"

snapshotCache :: TestResult
snapshotCache = case lowerSource True (holder ++ aliasPositive ++ scalarRule ++ "fn check(h: H) -> Int { define saved = h; h = H { f: positive }; rewrite callReflexivity saved.f 0 0; return 0; }; return 0;") of
    Error e -> Just e
    Ok program ->
        let uncached = mapResult (const ()) (MirValidate.validateProgramUncached program)
            cached = mapResult (const ()) (MirValidate.validateProgramWithCache emptyValidationCache program)
         in case (uncached, cached) of
            (Error e, Error e') | "Function object not validated" `isInfixOf` e && e == e' -> Nothing
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

sizedTriggers :: TestResult
sizedTriggers =
    let f = ATerm (Iota "$access")
        s = ATerm (Iota "source")
        readAt function receiver size index = FApp function [receiver, index, size]
        fact = Forall "j" [ge (BVar "j") (int 0), lt (BVar "j") (int 2)] (eq (readAt f s (int 3) (BVar "j")) (int 7))
        goals = [eq (readAt function receiver size (int i)) (int 7) | (function, receiver, size, i) <- [(f, s, int 3, 1), (f, s, int 4, 1), (ATerm (Iota "$other"), s, int 3, 1), (f, ATerm (Iota "other"), int 3, 1), (f, s, int 3, 2)]]
     in testAssertEq (Engine.entailsAll goals (Engine.proofContextFromFacts [fact])) [True, False, False, False, False]

binderIsolation :: TestResult
binderIsolation = case lowerSource True "return 0;" of
    Error e -> Just e
    Ok program ->
        let function = ATerm (Iota "$indexed")
            info = FnInfo ["s", "i"] [ProofAssert (geVar (ATerm "i") (CTerm (VInt 0)))] [FApp (CTerm (builtinFunct (Rel Eq))) [ATerm "return", ATerm "i"]] Nothing function True (KUser "indexed") False []
            st = (initialPState program){psFns = Map.singleton "indexed" info, psGlobals = Map.insert "indexed" (Iota "$indexed") (psGlobals (initialPState program))}
            goal = Forall "j" [geVar (BVar "j") (CTerm (VInt 0)), FApp (CTerm (builtinFunct (Rel Lt))) [BVar "j", CTerm (VInt 2)]] (FApp (CTerm (builtinFunct (Rel Eq))) [FApp (ATerm "indexed") [CTerm (VInt 0), BVar "j"], BVar "j"])
         in case runV (Ghost.runStatements st [ProofAssert goal]) of
            Error e -> Just e
            Ok checked -> testAssertEq (psVars checked == psVars st && psRuntimeProofValues checked == psRuntimeProofValues st && psView checked == psView st && psLocals checked == psLocals st && not (any (elem (iotaAt 0) . proofIotas) (allFacts checked)) && not (Engine.entails (ge (ATerm (iotaAt 0)) (int 0)) (proofContext checked))) True
  where
    geVar a b = FApp (CTerm (builtinFunct (Rel GtEq))) [a, b]

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
                else case MirValidate.validateProgramUncached mutant of
                    Ok _ -> Nothing
                    Error e -> Just ("The frame mutation did not admit its broken impl: " ++ e)

contractCache :: TestResult
contractCache =
    let source = identity ++ "fn check(s: Int) -> Int [{ }] [{ affirm forall j in 0..2: indexed(s, j) = j; }] { return 0; }; return check(1);"
     in case lowerSource True source of
        Error e -> Just e
        Ok good -> case MirValidate.validateProgramWithCache emptyValidationCache good of
            Error e -> Just e
            Ok (_, cache) -> case MirValidate.validateProgramWithCache cache good of
                Error e -> Just e
                Ok (_, warm) | validationCacheHits warm <= validationCacheHits cache -> Just "The repeated validation did not exercise cache reuse"
                Ok (_, warm) -> case lowerSource True (replace "indexed(s, j) = j" "indexed(s, j) = j + 1" source) of
                    Error e -> Just e
                    Ok bad -> case MirValidate.validateProgramWithCache warm bad of
                        Error e | "Could not prove: forall" `isInfixOf` e -> Nothing
                        _ -> Just "A changed quantified contract reused a successful validation"
