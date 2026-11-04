module TestCloneDropOrder (testCloneDropOrder, freshSource) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import Compile (lowerSource)
import qualified Mir as M
import qualified MirValidate
import ProofState (emptyValidationCache)
import TestHarness
import Utils


testCloneDropOrder :: Test
testCloneDropOrder = TestList "testCloneDropOrder"
    [ testCase "explicit allocating Clone before Drop validates" (accepted (freshSource False))
    , testCase "explicit allocating Clone after Drop validates" (accepted (freshSource True))
    , testCase "Clone before Drop uses the allocation and initialization path" (allocationPath (freshSource False))
    , testCase "Clone after Drop uses the allocation and initialization path" (allocationPath (freshSource True))
    , testCase "derived Clone after Drop still rejects copied permissions" (rejected (prefix ++ dropImpl ++ "impl Clone for Owned { }; return 0;") "permission")
    , testCase "derived Clone before Drop still rejects copied permissions" (rejected (prefix ++ "impl Clone for Owned { };" ++ dropImpl ++ "return 0;") "permission")
    , testCase "marker Clone after Drop remains forbidden" (rejected (markerPrefix ++ dropImpl ++ "impl Clone for Owned { }; return 0;") "has a drop")
    , testCase "marker Clone before Drop cannot copy a Block field" (rejected (markerPrefix ++ "impl Clone for Owned { };" ++ dropImpl ++ "return 0;") "which is not Clone")
    , testCase "Copy after Drop remains forbidden" (rejected (prefix ++ dropImpl ++ cloneImpl ++ "impl Copy for Owned { }; return 0;") "has a drop")
    , testCase "Copy before Drop cannot copy a Block field" (rejected (prefix ++ cloneImpl ++ "impl Copy for Owned { };" ++ dropImpl ++ "return 0;") "which is not Copy")
    , testCase "an explicit Clone cannot copy a linear value" (rejected (traits ++ "linear struct Ticket { value: Int }; impl Clone for Ticket { fn clone(self: &Self) -> Self { return Self { value: self.value }; }; }; return 0;") "is linear")
    , testCase "earlier valid Clone and Drop do not clear later linear guards" (rejected (prefix ++ dropImpl ++ cloneImpl ++ "linear struct Ticket { value: Int }; impl Clone for Ticket { fn clone(self: &Self) -> Self { return Self { value: self.value }; }; }; return 0;") "is linear")
    , testCase "Clone before Drop cannot duplicate a lent permission" (rejected (prefix ++ duplicateImpl ++ dropImpl ++ "return 0;") "permission in a value that is lent")
    , testCase "Clone after Drop cannot duplicate a lent permission" (rejected (prefix ++ dropImpl ++ duplicateImpl ++ "return 0;") "permission in a value that is lent")
    , testCase "Clone before Drop still proves its actual content contract" (rejected (prefix ++ wrongImpl ++ dropImpl ++ "return 0;") "Could not prove")
    , testCase "Clone after Drop still proves its actual content contract" (rejected (prefix ++ dropImpl ++ wrongImpl ++ "return 0;") "Could not prove")
    ]

accepted :: String -> TestResult
accepted source = checked source Nothing

rejected :: String -> String -> TestResult
rejected source expected = checked source (Just expected)

checked :: String -> Maybe String -> TestResult
checked source expected = case lowerSource True source of
    Error err -> if maybe False (`isInfixOf` err) expected then Nothing else Just err
    Ok program ->
        let results = [mapResult (const ()) (MirValidate.validateProgramUncached program), mapResult (const ()) (MirValidate.validateProgramWithCache emptyValidationCache program)]
            matches (Ok ()) = expected == Nothing
            matches (Error err) = maybe False (`isInfixOf` err) expected
         in if all matches results then Nothing else Just ("Expected " ++ show expected ++ ", got " ++ show results)

allocationPath :: String -> TestResult
allocationPath source = case lowerSource True source of
    Error err -> Just err
    Ok program -> case Map.lookup "<Owned as Clone>::clone" (M.progFunctions program) of
        Nothing -> Just "Missing actual custom Clone body"
        Just function ->
            let ops = [op | block <- Map.elems (M.fnBlocks function), M.Assign _ (M.ListOp op _) <- M.blockStatements block]
             in testAssertEq (length (filter (== M.AddrAlloc) ops), length (filter (== M.AddrWrite) ops), M.fnBorrowed function) (1, 1, [M.Local 1])

freshSource :: Bool -> String
freshSource dropFirst = prefix ++ (if dropFirst then dropImpl ++ cloneImpl else cloneImpl ++ dropImpl) ++ "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); original = Owned { addr: p, blk: b }; copy = clone(original); return Addr::get(copy.addr, 0, copy.blk);"

traits, prefix, markerPrefix, owned, dropImpl, cloneImpl, duplicateImpl, wrongImpl :: String
traits = "trait Clone { fn clone(self: &Self) -> Self [{ }] [{ }]; }; trait Copy { }; trait Drop { fn drop(self: Self) -> Int [{ }] [{ }]; }; "
owned = "struct Owned { addr: Addr<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 1; affirm filled(blk, 0); }]; "
prefix = traits ++ owned
markerPrefix = "trait Clone { }; trait Copy { }; trait Drop { fn drop(self: Self) -> Int [{ }] [{ }]; }; " ++ owned
dropImpl = "impl Drop for Owned { fn drop(self: Self) -> Int [{ }] [{ }] { return Addr::free(self.addr, Addr::dropValue(self.addr, 0, self.blk)); }; }; "
cloneImpl = "impl Clone for Owned { fn clone(self: &Self) -> Self [{ }] [{ affirm at(return.blk, 0) = at(self.blk, 0); }] { value = Addr::get(self.addr, 0, self.blk); (p, b) = Addr::alloc(1); b = Addr::write(p, 0, value, b); return Self { addr: p, blk: b }; }; }; "
duplicateImpl = "impl Clone for Owned { fn clone(self: &Self) -> Self [{ }] [{ }] { return Self { addr: self.addr, blk: self.blk }; }; }; "
wrongImpl = "impl Clone for Owned { fn clone(self: &Self) -> Self [{ }] [{ affirm at(return.blk, 0) = at(self.blk, 0) + 1; }] { value = Addr::get(self.addr, 0, self.blk); (p, b) = Addr::alloc(1); b = Addr::write(p, 0, value, b); return Self { addr: p, blk: b }; }; }; "
