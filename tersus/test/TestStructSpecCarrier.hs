module TestStructSpecCarrier (testStructSpecCarrier) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified AstData as A
import qualified Compile
import qualified Interface as I
import qualified Link
import qualified Mir as M
import qualified MirData
import qualified MirHousekeeping as H
import qualified MirLower as L
import qualified Parse
import qualified SelfHostedMir as S
import qualified ValidatorNative as V
import Modules (ModuleId(..))
import Syntax
import Types
import TypeCheck (elaborate, elaborateWith, Elaborated(..), emptyImportEnv)
import TestHarness
import Utils

testStructSpecCarrier :: Test
testStructSpecCarrier = TestList "testStructSpecCarrier"
    [ testCase "ordinary invariant descriptors have no projection by default" $ lowered ordinary `use` \p -> case Map.lookup "Positive" (M.progInvariants p) of
        Just spec -> testAssertTrue (not (null (structInvariant spec)) && structProjection spec == Nothing)
        Nothing -> Just "ordinary invariant was lost"
    , testCase "ordinary field invariants validate with native cached and uncached validators" $ checked ordinary `use` \p -> validBoth p
    , testCase "invalid ordinary construction still fails its actual invariant" $ checked invalid `use` \p -> rejected (V.validateCompiledUncached p) "Could not prove"
    , testCase "top-level projected StructSpec reaches the original MIR map intact" $ projected `use` \ss -> lower ss `use` \p -> testAssertEq (Map.lookup "Payload" (M.progInvariants p)) (Just payloadSpec)
    , testCase "unused generic projected declaration retains its descriptor" $ projected `use` \ss -> lower ss `use` \p -> testAssertEq (Map.lookup "Prefix" (M.progInvariants p)) (Just prefixSpec)
    , testCase "projected declarations are transported through checked interfaces" $ projected `use` \ss -> elaborateWith emptyImportEnv ss `use` \(Elaborated typed _, state) ->
        I.extractLibInterface fixture ss typed state `use` \iface -> testAssertEq (Map.lookup "Payload" (I.ifInvariants iface), Map.lookup "Prefix" (I.ifInvariants iface)) (Just payloadSpec, Just prefixSpec)
    , testCase "an importing module preserves its imported generic descriptor" $ projected `use` \ss -> elaborateWith emptyImportEnv ss `use` \(Elaborated typed _, state) ->
        I.extractLibInterface fixture ss typed state `use` \iface -> source "return 0;" `use` \user ->
            elaborateWith (I.interfaceImportEnv iface) user `use` \(elab, _) -> L.lowerModuleWith (I.interfaceImportEnv iface) [iface] elab `use` \p ->
                testAssertEq (Map.lookup "Prefix" (M.progInvariants p)) (Just prefixSpec)
    , testCase "linking retains full descriptor identity" $ projected `use` \ss -> lower ss `use` \p ->
        Link.linkPrograms [(fixture, p)] `use` \linked -> testAssertEq (M.progInvariants linked) (M.progInvariants p)
    , testCase "native encoding refuses any projected descriptor before filtering" $ projected `use` \ss -> lower ss `use` \p -> rejected (either Error (const (Ok ())) (S.encode p)) "checked declaration-backed value projection"
    , testCase "native cached and uncached checks refuse unused projections" $ projected `use` \ss -> lower ss `use` \p -> unsupportedBoth p
    , testCase "obligation formatting does not erase an unsupported projection" $ projected `use` \ss -> lower ss `use` \p -> testAssertEq (S.obligationNote p "main" 0 0) Nothing
    , testCase "a modified canonical container descriptor is refused before sourceContainerView" $ Compile.lowerSource True "return 0;" `use` \p ->
        let decorated = p{M.progInvariants = Map.adjust (\spec -> spec{structProjection = Just (StoredPayload "blk")}) "Box" (M.progInvariants p)}
         in testAssertTrue (maybe False ((/= Nothing) . structProjection) (Map.lookup "Box" (M.progInvariants decorated))) <> unsupportedBoth decorated
    , testCase "native runtime wire does not grow a projection schema" $ projected `use` \ss -> lower ss `use` \p ->
        testAssertEq (MirData.writeProgram p) (MirData.writeProgram p{M.progInvariants = Map.map (\spec -> spec{structProjection = Nothing}) (M.progInvariants p)})
    , testCase "source AST2 remains the identical descriptor codec" $ projected `use` \ss -> A.writeParsed ss `use` \bytes -> A.readParsed bytes `use` \back -> testAssertEq back ss
    , testCase "typed field owner is carried for code and contract observations" $ source "struct Owner { n: Int }; fn read(p: &Owner) -> Int [{ }] [{ affirm return = p.n; }] { return p.n; }; return 0;" `use` \ss ->
        elaborate ss `use` \(Elaborated typed _) -> testAssertTrue (all (== Just "Owner") (fieldOwners typed) && length (fieldOwners typed) >= 2)
    , testCase "generic field owners name the actual declared instance" $ source "struct Wrap<T> { value: T }; fn read<T>(p: &Wrap<T>) -> T [{ }] [{ affirm return = p.value; }] { return p.value; }; return 0;" `use` \ss ->
        elaborate ss `use` \(Elaborated typed _) -> testAssertTrue (all (== Just "Wrap<'T>") (fieldOwners typed) && length (fieldOwners typed) >= 2)
    , testCase "a mismatched explicit owner is rejected by constructor typing" $ source "struct Owner { n: Int }; struct Other { n: Int }; p = Owner { n: 7 }; return p.n;" `use` \ss ->
        rejected (elaborate (map wrongOwner ss)) "base of an update of Other"
    , testCase "normal default library selection is not activated with projections" $ Compile.lowerSource True "return 7;" `use` \p -> testAssertTrue (all ((== Nothing) . structProjection) (Map.elems (M.progInvariants p))) <> validBoth p
    ]
  where
    ordinary = "struct Positive { n: Int } invariant [{ affirm n >= 0; }]; p = Positive { n: 7 }; affirm p.n = 7; return 0;"
    invalid = "struct Positive { n: Int } invariant [{ affirm n >= 0; }]; p = Positive { n: 0 - 1 }; return 0;"
    fixture = ModuleId "tersuslib" (Just "descriptor_fixture")
    payloadSpec = StructSpec [] (Just (StoredPayload "blk"))
    prefixSpec = StructSpec [] (Just (InitializedPrefix "blk" "len"))
    projected = source "struct Payload { ghost blk: Block<Int> }; struct Prefix<T> { ghost blk: Block<T>, len: Int }; return 0;" `bindResult` \ss -> Ok (map project ss)
    project (StructDef "Payload" ps fs _) = StructDef "Payload" ps fs payloadSpec
    project (StructDef "Prefix" ps fs _) = StructDef "Prefix" ps fs prefixSpec
    project other = other
    source text = case Parse.parseStatementBlock text of Left e -> Error (show e); Right ss -> Ok ss
    lower ss = elaborate ss `bindResult` L.lowerElaborated
    lowered text = source text `bindResult` lower
    checked text = lowered text `bindResult` \p -> H.verifyProgram p `bindResult` \_ -> Ok p
    validBoth p = rejectedSuccess (V.validateCompiled p) <> rejectedSuccess (V.validateCompiledUncached p)
    unsupportedBoth p = rejected (V.validateCompiled p) "checked declaration-backed value projection" <> rejected (V.validateCompiledUncached p) "checked declaration-backed value projection"
    rejectedSuccess (Error e) = Just e
    rejectedSuccess (Ok _) = Nothing
    rejected (Error e) needle | needle `isInfixOf` e = Nothing
                             | otherwise = Just ("Expected " ++ needle ++ ", got " ++ e)
    rejected (Ok _) _ = Just "expected refusal"
    use (Error e) _ = Just e
    use (Ok value) f = f value
    wrongOwner (Return (F (Val (VFunct ps ins outs (BuiltinFunct (Field _ field)) exports)) args)) = Return (F (Val (VFunct ps ins outs (BuiltinFunct (Field (Just "Other") field)) exports)) args)
    wrongOwner other = other
    fieldOwners = concatMap statementFields
    statementFields (Assign _ (Val (VFunct _ ins outs (NativeFunct _ _ body) _))) = concatMap validationFields (ins ++ outs) ++ fieldOwners body
    statementFields (Return expr) = exprFields expr
    statementFields _ = []
    validationFields (ProofAssert p) = proofFields p
    validationFields _ = []
    exprFields (F (Val (VFunct _ _ _ (BuiltinFunct (Field owner _)) _)) args) = owner : concatMap exprFields args
    exprFields (F f args) = concatMap exprFields (f : args)
    exprFields _ = []
    proofFields (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Field owner _)) _)) args) = owner : concatMap proofFields args
    proofFields (FApp f args) = concatMap proofFields (f : args)
    proofFields _ = []
