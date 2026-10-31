module TestBuiltinRegistry (testBuiltinRegistry) where

import Data.List (sort)
import qualified Data.Map as Map

import BuiltinRegistry
import StdLib (builtinFunct, stdLibCtx)
import TersusTypes
import TestHarness

-- One representative of every BuiltinFunct constructor. A new constructor needs a representative
-- here, a BuiltinKind and exactly one registry entry, or these tests fail.
representatives :: [BuiltinFunct]
representatives =
    [ Size, First, Last, Get, Push, Pop, Set, Plus, Minus, Times, Div, Mod
    , NewArray, ArrayFrom, NewBoxedArray, NewEmptyArray
    , WriteByte, WriteError, ReadByte, ArgCount, ArgByte, PathByte, FileLoad, FileByte, StoreByte, FileStore
    , ToByte, FromByte, BytesFrom, Unsize, NewBox, UnBox, CloneOf
    , AddrNull, AddrOffset, AddrCast, AddrToInt, AddrFromInt, AddrAlloc, AddrGet, AddrWrite, AddrTake
    , AddrDropValue, AddrDropRange, AddrResize, AddrFree, AllocPair, TakePair, ResizePair, SplitPair
    , BlockNew, BlockTaken, BlockResized, BlockSplitLo, BlockSplitHi, BlockJoin, BlockAssume, BlockCast
    , BlockBase, BlockCap, BlockFilled, BlockContents, BlockOrigin, BlockStart, BlockExtent, BlockCount
    , UninitEmpty, UninitNew, UninitGet, UninitTake, UninitDiscard, UninitFilled, UninitAt
    , ToWord True 8, Replace, Rel Eq, And, Or, Not, Within
    , Ctor "Thing" [] ["x"], Field Nothing "x", Is "Thing", Project "Thing" "x", Cast "Thing"
    ]

testBuiltinRegistry :: Test
testBuiltinRegistry =
    TestList
        "testBuiltinRegistry"
        [ testCase "every constructor has exactly one registry entry" $
            testAssertEq (sort (map builtinKind representatives)) allBuiltinKinds
        , testCase "the registry has exactly one entry per kind" $
            testAssertEq (sort (map entryKind builtinRegistry)) allBuiltinKinds
        , testCase "every registry instance belongs to its entry" $
            testAssertTrue
                (all (\entry -> all (\b -> builtinKind b == entryKind entry) (entryInstances entry)) builtinRegistry)
        , testCase "every builtin value carries its own constructor" $
            testAssertTrue (all carries representatives)
        , testCase "parsed contracts give the registry parameter names" $
            testAssertTrue (all parsedParams representatives)
        , testCase "the standard context is the registry StdName bindings" $
            testAssertEq (Map.keys stdLibCtx) (sort (map fst stdBindings))
        , testCase "the standard context values are the registry builtins" $
            testAssertTrue (all (\(name, b) -> Map.lookup name stdLibCtx == Just (builtinFunct b)) stdBindings)
        , testCase "only the declaration-builtins have a dynamic signature" $
            testAssertEq
                (sort [builtinKind b | b <- representatives, signatureScheme b == SigDynamic])
                (sort [KCtor, KField, KIs, KProject, KCast])
        , testCase "readsWorld agrees with the registry" $
            testAssertTrue (all (\b -> readsWorld b == entryReadsWorld (entryFor b)) representatives)
        , testCase "ghostBuiltin agrees with the registry" $
            testAssertTrue (all (\b -> ghostBuiltin b == entryGhost (entryFor b)) representatives)
        ]
  where
    carries b = case builtinFunct b of
        VFunct _ _ _ (BuiltinFunct b') _ -> b' == b
        _ -> False
    parsedParams b = case contractSpec b of
        ParsedContract _ -> case builtinFunct b of
            VFunct paramNames _ _ _ _ -> paramNames == entryParams (entryFor b) b
            _ -> False
        _ -> True
