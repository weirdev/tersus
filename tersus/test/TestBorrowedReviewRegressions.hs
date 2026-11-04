module TestBorrowedReviewRegressions (testBorrowedReviewRegressions) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Parse
import TypeCheck (elaborate, elaborateWith, emptyImportEnv, Elaborated(..))
import qualified Mir as M
import qualified MirLower
import qualified SelfHostedMir
import qualified ValidatorNative
import qualified Interface
import Modules (ModuleId(..))
import Syntax
import Types
import Utils
import TestHarness

testBorrowedReviewRegressions :: Test
testBorrowedReviewRegressions = TestList "testBorrowedReviewRegressions"
    [ testCase "a forward source call reads through the actual pointer-returning target" $ mir forward `use` \program ->
        case Map.lookup "read" (M.progFunctions program) of
            Nothing -> Just "caller is missing"
            Just fn -> testAssertTrue (hasDeref fn && any (\block -> case M.blockTerminator block of
                M.Call (M.Const (M.CFn "field")) _ dest _ -> maybe False ((== TRef TInt) . M.localType) (Map.lookup dest (M.fnLocals fn))
                _ -> False) (Map.elems (M.fnBlocks fn)))
    , testCase "a callback parameter shadowing a global getter has ordinary result ABI" $ mir shadow `use` \program ->
        case Map.lookup "use" (M.progFunctions program) of
            Nothing -> Just "callback caller is missing"
            Just fn -> testAssertTrue (not (hasDeref fn) && any (\block -> case M.blockTerminator block of
                M.Call (M.Copy _) _ dest _ -> maybe False ((== TInt) . M.localType) (Map.lookup dest (M.fnLocals fn))
                _ -> False) (Map.elems (M.fnBlocks fn)))
    , testCase "a callback named like its enclosing borrowed function keeps ordinary ABI" $ mir selfShadow `use` \program ->
        case Map.lookup "view" (M.progFunctions program) of
            Nothing -> Just "enclosing function is missing"
            Just fn -> testAssertTrue (M.fnReturns fn == Just (TRef TInt) && not (hasDeref fn) && any (\block -> case M.blockTerminator block of
                M.Call (M.Copy _) _ dest _ -> maybe False ((== TInt) . M.localType) (Map.lookup dest (M.fnLocals fn))
                _ -> False) (Map.elems (M.fnBlocks fn)))
    , testCase "a nested borrowed function in an unused bounded template cannot vanish" $ rejected (mir nestedBorrowed) "Unmodeled: checked borrowed whole-value return places"
    , testCase "a nested borrowed function cannot be exported through its outer template" $ source nestedBorrowed `use` \original ->
        elaborateWith emptyImportEnv original `use` \(Elaborated checked _, state) ->
            rejected (Interface.extractLibInterface fixture original checked state) "Unmodeled: checked borrowed whole-value return places"
    , testCase "a nested ordinary function in an unused bounded template remains legal" $ source nestedOrdinary `use` \original ->
        elaborateWith emptyImportEnv original `use` \(typed@(Elaborated checked _), state) ->
            MirLower.lowerElaborated typed `use` \_ -> Interface.extractLibInterface fixture original checked state `use` \iface -> testAssertTrue (Map.member "helper" (Interface.ifTemplates iface))
    , testCase "an outer reference alias updated inside a block rejects its stale root" $ sourceReject (aliasPrefix ++ "fn choose(a: &Int, b: &Int) -> &Int from a { f = left; { f = right; }; return f(a, b); }; return 0;") "not a reference from a"
    , testCase "an outer reference alias updated inside a block keeps its actual root" $ sourceAccept (aliasPrefix ++ "fn choose(a: &Int, b: &Int) -> &Int from b { f = left; { f = right; }; return f(a, b); }; return 0;")
    , testCase "matching branch updates preserve a known outer reference alias" $ sourceAccept (aliasPrefix ++ "fn choose(a: &Int, b: &Int, flag: Bool) -> &Int from b { f = left; if flag { f = right; } else { f = right; }; return f(a, b); }; return 0;")
    , testCase "divergent branch updates cannot claim one reference origin" $ sourceReject (aliasPrefix ++ "fn choose(a: &Int, b: &Int, flag: Bool) -> &Int from a { f = left; if flag { f = right; }; return f(a, b); }; return 0;") "what the result is from is not known"
    , testCase "a fresh Let self-shadow keeps borrowed origins for function erasure rejection" $ rejected (freshSelf (getter ++ "fn fetch() -> fn(&G) -> Int { field = field; return field; }; return 0;") `bindResult` elaborate) "cannot be erased into a plain function value"
    , testCase "a fresh Let self-shadow call reads the actual pointer-returning ABI" $ (freshSelf (getter ++ "fn read(g: &G) -> Int { field = field; return field(g); }; return 0;") `bindResult` elaborate `bindResult` MirLower.lowerElaborated) `use` \program ->
        case Map.lookup "read" (M.progFunctions program) of
            Nothing -> Just "Let alias caller is missing"
            Just fn -> testAssertTrue (hasDeref fn && any (\block -> case M.blockTerminator block of
                M.Call (M.Copy _) _ dest _ -> maybe False ((== TRef TInt) . M.localType) (Map.lookup dest (M.fnLocals fn))
                _ -> False) (Map.elems (M.fnBlocks fn)))
    , testCase "a fresh Let self-shadow preserves legacy ReferenceOrigin forwarding" $ (freshSelf "fn carry(x: &Int) -> &Int from x { return &x; }; fn wrap(x: &Int) -> &Int from x { carry = carry; return carry(x); }; return 0;" `bindResult` elaborate) `use` \_ -> Nothing
    , testCase "a function-local scalar cannot erase a global getter's mode" $ sourceReject clobber "cannot be erased into a plain function value"
    , testCase "a function-local scalar cannot erase a legacy reference-carrier origin" $ sourceAccept legacy
    , testCase "a lexical block's local scalar cannot erase a global getter's mode" $ sourceReject blockClobber "cannot be erased into a plain function value"
    , testCase "forward borrowed function coercion fails before mode loss" $ sourceReject forwardErase "cannot be erased into a plain function value"
    , testCase "unused bounded borrowed declaration remains present until lowering rejects it" $ source bounded `use` \original ->
        elaborate original `use` \typed@(Elaborated statements _) ->
            testAssertTrue (any unsupportedTemplateDeclaration statements) <> rejected (MirLower.lowerElaborated typed) "Unmodeled: checked borrowed whole-value return places"
    , testCase "unused bounded borrowed mode cannot reach encoding or cached validation as success" $ rejected (mir bounded `bindResult` \program -> either Error (const (Ok ())) (SelfHostedMir.encode program)) "Unmodeled: checked borrowed whole-value return places"
    , testCase "unused bounded borrowed mode cannot reach uncached validation as success" $ rejected (mir bounded `bindResult` ValidatorNative.validateCompiledUncached) "Unmodeled: checked borrowed whole-value return places"
    , testCase "unsupported bounded borrowed declaration cannot be exported as a template" $ source bounded `use` \original ->
        elaborateWith emptyImportEnv original `use` \(Elaborated checked _, state) ->
            rejected (Interface.extractLibInterface fixture original checked state) "Unmodeled: checked borrowed whole-value return places"
    , testCase "unused bounded projection cannot vanish during elaboration/lowering" $ projected `use` \original ->
        elaborate original `use` \typed@(Elaborated statements _) -> testAssertTrue (hasValueProjection statements) <>
            rejected (MirLower.lowerElaborated typed) "Unmodeled: checked declaration-backed value projections"
    , testCase "unused bounded projection cannot be exported from deferred metadata" $ projected `use` \original ->
        elaborateWith emptyImportEnv original `use` \(Elaborated checked _, state) ->
            rejected (Interface.extractLibInterface fixture original checked state) "Unmodeled: checked declaration-backed value projections"
    , testCase "ordinary unused bounded functions remain legal templates" $ source ordinary `use` \original ->
        elaborateWith emptyImportEnv original `use` \(typed@(Elaborated checked _), state) ->
            MirLower.lowerElaborated typed `use` \_ -> Interface.extractLibInterface fixture original checked state `use` \iface ->
                testAssertTrue (Map.member "helper" (Interface.ifTemplates iface) && not (any unsupportedTemplateDeclaration checked))
    ]
  where
    fixture = ModuleId "tersuslib" (Just "fixture")
    getter = "struct G { n: Int }; fn field(g: &G) -> Int borrowed from g { return g.n; }; "
    forward = "struct G { n: Int }; fn read(g: &G) -> Int { return field(g); }; fn field(g: &G) -> Int borrowed from g { return g.n; }; return 0;"
    shadow = getter ++ "fn use(field: fn(&G) -> Int, g: &G) -> Int { return field(g); }; return 0;"
    selfShadow = "struct G { n: Int }; fn view(view: fn(&G) -> Int, g: &G) -> Int borrowed from g { n = view(g); return g.n; }; return 0;"
    nestedBorrowed = "trait Copy {}; fn helper<T: Copy>(x: T) -> Int { struct G { n: Int }; fn field(g: &G) -> Int borrowed from g { return g.n; }; return 0; }; return 0;"
    nestedOrdinary = "trait Copy {}; fn helper<T: Copy>(x: T) -> Int { struct G { n: Int }; fn field(g: &G) -> Int { return g.n; }; return 0; }; return 0;"
    aliasPrefix = "fn left(a: &Int, b: &Int) -> &Int from a { return &a; }; fn right(a: &Int, b: &Int) -> &Int from b { return &b; }; "
    clobber = getter ++ "fn shadow() -> Int { field = 1; return field; }; fn fetch() -> fn(&G) -> Int { return field; }; return 0;"
    blockClobber = getter ++ "fn fetch() -> fn(&G) -> Int { { field = 1; }; return field; }; return 0;"
    forwardErase = "struct G { n: Int }; fn fetch() -> fn(&G) -> Int { return field; }; fn field(g: &G) -> Int borrowed from g { return g.n; }; return 0;"
    legacy = "struct Held { r: &Int }; fn carry(x: &Int) -> Held from x { return Held { r: &x }; }; fn shadow() -> Int { carry = 1; return carry; }; fn wrap(x: &Int) -> Held from x { return carry(x); }; return 0;"
    bounded = "trait Copy {}; fn view<T: Copy>(x: &T) -> T borrowed from x { return x; }; return 0;"
    ordinary = "trait Copy {}; fn helper<T: Copy>(x: T) -> Int { return 0; }; return 0;"
    projected = source "trait Copy {}; fn helper<T: Copy>(x: T) -> Int { struct Local { n: Int }; return 0; }; return 0;" `bindResult` \body -> Ok (map attach body)
    attach (BoundedDef bounds (Assign name (Val (VFunct ps ins outs (NativeFunct sig term body) exports)))) =
        BoundedDef bounds (Assign name (Val (VFunct ps ins outs (NativeFunct sig term (map projection body)) exports)))
    attach other = other
    projection (StructDef name ps fields spec) = StructDef name ps fields spec{structProjection = Just (StoredPayload "n")}
    projection other = other
    freshSelf text = source text `bindResult` \body -> Ok (map fresh body)
    fresh (Assign name (Val (VFunct params ins outs (NativeFunct signature termination body) exports))) =
        Assign name (Val (VFunct params ins outs (NativeFunct signature termination (map fresh body)) exports))
    fresh (Assign name (Var rhs)) | name == rhs = Let name (Var rhs)
    fresh other = other
    source text = case Parse.parseStatementBlock text of Left err -> Error (show err); Right body -> Ok body
    mir text = source text `bindResult` elaborate `bindResult` MirLower.lowerElaborated
    use (Error err) _ = Just err
    use (Ok value) f = f value
    sourceAccept text = source text `bindResult` elaborate `use` \_ -> Nothing
    sourceReject text needle = rejected (source text `bindResult` elaborate) needle
    rejected (Error err) needle | needle `isInfixOf` err = Nothing
                              | otherwise = Just ("Expected " ++ needle ++ ", got " ++ err)
    rejected (Ok _) _ = Just "unsupported metadata was accepted"
    hasDeref fn = any (\statement -> case statement of M.Assign _ M.Deref{} -> True; _ -> False) [s | block <- Map.elems (M.fnBlocks fn), s <- M.blockStatements block]
