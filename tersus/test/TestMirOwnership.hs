{-# LANGUAGE PatternSynonyms #-}

module TestMirOwnership (testMirOwnership, testOwnershipMetadata, testOwnershipInterpreted) where

import Data.List (isInfixOf)

import qualified Data.Map.Strict as Map
import System.Exit (ExitCode (..))

import Compile (lowerSource)
import Mir
import MirData (forNative, readProgram, writeProgramWithGhosts)
import MirEval (MirValue (..), RunEnv (..), Outcome (..), runProgram, runProgramEnv)
import TestOwnership (runOwned, usesArrays)
import MirMono (monomorphize, monomorphizeForValidation)
import MirLists (lowerLists)
import MirHousekeeping (Tool (..), eraseGhosts, expandRefWrites, insertOwnership, nativeProgram, ownershipTool, toolProgram, emitterEntry, verifyProgram)
import MirOwnershipData (ownershipInput, restoreOwnership)
import Modules (LoadResult (..), loadFromFilesystem)
import Native (runWithInputFull)
import Syntax (Termination (..))
import qualified Syntax as S
import TestHarness
import TestNative (nativeExamples, nativeMirCase, unvalidatedPrograms, validatedPrograms)
import Pipeline (compileSource)
import Types (Arg (..), Size (..), Type (..), pattern TBox, pattern TList, instanceName)
import Utils

restoreRoundTrip :: Program -> Result Program String
restoreRoundTrip program = readProgram (writeProgramWithGhosts (ownershipInput program)) `bindResult` restoreOwnership program

testOwnershipMetadata :: Test
testOwnershipMetadata = TestList "testOwnershipMetadata"
    [ testCase "generic reference writes are instantiated by the host mono adapter" genericReferenceWrite
    , testCase "mutable named references instantiate declarations and field selectors" mutableNamedReference
    , testCase "mutable named references retain renamed list-lowering field selectors" mutableReferenceListNormalization
    , testCase "all structural types, sizes and function metadata survive transport" (testAssertEq (restoreRoundTrip metadataFixture) (Ok metadataFixture))
    , testCase "the runtime view still intentionally erases host metadata" (testAssertTrue (forNative metadataFixture /= metadataFixture))
    , testCase "repeated ghost payloads have separate identities" (testAssertEq (ghostIds (ownershipInput metadataFixture)) [0 .. length (ghostIds (ownershipInput metadataFixture)) - 1])
    , testCase "ghost payloads follow new blocks rather than old statement offsets" (testAssertEq (restoreOwnership metadataFixture splitFixture) (Ok restoredSplitFixture))
    , rejected "a dropped ghost is refused" "missing" (editMain (filter (not . isGhost)) numbered)
    , rejected "a repeated ghost ID is refused" "duplicated" (editMain (\stmts -> head stmts : stmts) numbered)
    , rejected "an unknown ghost ID is refused" "unrecognized" (editMain (\stmts -> Ghost Map.empty (GhostPosition (-1) 9999) : tail stmts) numbered)
    , rejected "an unnumbered ghost is refused" "unnumbered" (editMain (++ [Ghost Map.empty (GhostPosition 3 8)]) numbered)
    , rejected "ghost IDs may not migrate into another function" "unrecognized" crossFunctionFixture
    , rejected "a function removed by transport is refused" "function set" numbered{progFunctions = Map.empty}
    , rejected "changed structural type declarations are refused" "type declarations" numbered{progTypes = Map.empty}
    , rejected "changed borrowed parameters are refused" "header" numbered{progMain = (progMain numbered){fnBorrowed = [Local 1]}}
    , rejected "changed mutborrowed parameters are refused" "header" numbered{progMain = (progMain numbered){fnMutBorrowed = [Local 1]}}
    , rejected "changed from metadata is refused" "header" numbered{progMain = (progMain numbered){fnFrom = [Local 1]}}
    , rejected "changed source local names are refused" "local declaration" numbered{progMain = (progMain numbered){fnLocals = Map.map (\d -> d{localName = Nothing}) (fnLocals (progMain numbered))}}
    , rejected "original blocks referenced by proof metadata may not be removed" "original block" numbered{progMain = (progMain numbered){fnBlocks = Map.singleton (BlockId 9) (fnBlocks (progMain numbered) Map.! BlockId 0)}}
    , testCase "legacy ghosts remain readable" (testAssertEq (readProgram (ghostRecord "ghost")) (Ok (wireMain (Ghost Map.empty (GhostPosition (-1) (-1))))))
    , testCase "numbered ghosts remain readable" (testAssertEq (readProgram (ghostRecord "ghost 27")) (Ok (wireMain (Ghost Map.empty (GhostPosition (-1) 27)))))
    , testCase "explicit negative ghost IDs are refused" (testAssertErrorContains "nonnegative" (readProgram (ghostRecord "ghost -1")))
    , testCase "extra tokens after a ghost are refused" (testAssertErrorContains "more in it" (readProgram (ghostRecord "ghost 1 2")))
    , testCase "duplicate type records are refused" (testAssertErrorContains "duplicate type" (readProgram ("tersus-mir 2\nstruct \"T\" 0\nstruct \"T\" 0\n" ++ unlines (tail (lines (ghostRecord "ghost"))))))
    , testCase "duplicate local records are refused" (testAssertErrorContains "duplicate local" (readProgram (replaceLine "block 0" "local 0 none int\nlocal 0 none int\nblock 0" (ghostRecord "ghost"))))
    , testCase "duplicate block records are refused" (testAssertErrorContains "duplicate block" (readProgram (replaceLine "end" "block 0\nreturn\nend" (ghostRecord "ghost"))))
    ]
  where
    numbered = ownershipInput metadataFixture
    rejected name expected changed = testCase name (testAssertErrorContains expected (restoreOwnership metadataFixture changed))
    splitFixture = splitGhosts numbered
    restoredSplitFixture = splitGhosts metadataFixture
    crossFunctionFixture = numbered{progMain = (progMain numbered){fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Ghost Map.empty (GhostPosition (-1) 0)] Return)}}

testMirOwnership :: Test
testMirOwnership = TestList "testMirOwnership"
    [ TestList "examples own before list lowering" [TestCase path (do { text <- readFile path; compiled <- exampleProgram path; pure (ownedBeforeLowering text compiled) }) | path <- nativeExamples]
    , TestList "source corpus owns before list lowering" [testCase name (ownedBeforeLowering source (lowerSource True source)) | (name, source) <- validatedPrograms ++ unvalidatedPrograms]
    , testCase "nested sequence writes retain each intermediate element type" nestedSequenceWrite
    , testCase "enum field writes retain unwritten sibling fields" enumFieldWrite
    , testCase "pre-mono expansion of a program with no reference write leaves it whole" (testAssertEq (expandRefWrites metadataFixture) (Ok metadataFixture))
    , testCase "the mono fast path keeps specifications and ghost payloads" (case insertOwnership ownershipFixture of
        Error e -> Just e
        -- (main owns nothing and the drop does nothing, so both come back whole; the clone copies the `self` it is lent)
        Ok owned -> firstFailure
            [ testAssertEq (progTypes owned, progGenerics owned, progInvariants owned) (progTypes ownershipFixture, progGenerics ownershipFixture, progInvariants ownershipFixture)
            , testAssertEq (progMain owned) (progMain ownershipFixture)
            , testAssertEq (Map.lookup "<Plain as Drop>::drop" (progFunctions owned)) (Map.lookup "<Plain as Drop>::drop" (progFunctions ownershipFixture))
            , case (Map.lookup "<Plain as Clone>::clone" (progFunctions owned), Map.lookup "<Plain as Clone>::clone" (progFunctions ownershipFixture)) of
                (Just clone, Just original) -> firstFailure
                    [ testAssertEq (fnParams clone, fnBorrowed clone, fnReturns clone, fnSpec clone) (fnParams original, fnBorrowed original, fnReturns original, fnSpec original)
                    , testAssertTrue (fnLocals original `Map.isSubmapOf` fnLocals clone)
                    , testAssertEq (blockStatements <$> Map.lookup (BlockId 0) (fnBlocks clone)) (Just [Assign (Local 0) (CopyOf (Copy (Local 1)))])
                    ]
                _ -> Just "the clone is missing"
            ])
    , testCase "uncalled Drop and Clone implementations survive ownership" (case insertOwnership ownershipFixture of Error e -> Just e; Ok owned -> testAssertEq (Map.keys (progFunctions owned)) (Map.keys (progFunctions ownershipFixture)))
    , TestCase "the ownership tool is native after the cold boundary" nativeTool
    -- The fixtures of testOwnershipInterpreted, owned by the production tool and run natively (memory checks and valgrind)
    , TestList "native MIR fixtures" [TestCase label (nativeMirCase label program "1\n") | (label, program) <- nativeFixtures]
    -- Two of the patterns behind those fixtures are refused by the source checker now; the fixtures keep them covered
    , testCase "a view lent to a callee that writes its source is refused in source" (refusedInSource "fn f(t: &List<Int>, r: &mut List<List<Int>>) -> Int writes(r) { *r = [[9, 10]]; return size(t); }; xs = [[7]]; a = get(xs, 0); return f(&a, &mut xs) + size(get(xs, 0));")
    , testCase "a borrowed view whose source is replaced is refused in source" (refusedInSource "xs = [[7]]; a = get(xs, 0); t = &a; xs = set(xs, 0, [9, 10]); return size(*t) + size(get(xs, 0));")
    , TestCase "legacy list tokens and named lists own alike" (sameOwnedMain elementWriteLegacy elementWriteNamed)
    , TestCase "a legacy Box token and a declared named Box own alike" (sameOwnedMain boxedReferenceLegacy boxedReferenceNamed)
    , TestCase "unknown selectors are refused" (toolRefuses "pass unknown\ntersus-mir 2\n")
    , TestCase "malformed MIR is refused" (toolRefuses "pass ownership\ntersus-mir 2\nnot-mir\n")
    , TestCase "MIR version 1 is not ownership transport" (toolRefuses "pass expand\ntersus-mir 1\n")
    , TestCase "a jump to a block that is not there is refused" (toolRefuses ("pass ownership\n" ++ writeProgramWithGhosts (withMainBlocks (Map.map (\b -> b{blockTerminator = Goto (BlockId 77)})) (ownershipInput metadataFixture))))
    , TestCase "a function with no block 0 is refused" (toolRefuses ("pass ownership\n" ++ writeProgramWithGhosts (withMainBlocks (Map.mapKeys (\(BlockId n) -> BlockId (n + 5))) (ownershipInput metadataFixture))))
    ]
  where
    -- (here the passes run before list lowering, as on a generic body. A program with no reference write is left as it is by the
    -- expansion. A program with arrays or blocks, which the heap model cannot hold, has the well-formedness of its MIR checked
    -- after lowering and ownership in the order native code is made in. One that makes no reference is judged on the heap model
    -- by testOwnership, in that order; one with references is judged on the heap model against the executor here. testNative
    -- runs them all natively)
    ownedBeforeLowering text compiled = case compiled of
        Error e -> Just e
        Ok raw -> case expandRefWrites raw of
            Error e -> Just e
            Ok expanded | not (any writesReference (statementsOf raw)) && expanded /= raw -> Just "the expansion changed a program with no reference write"
            Ok expanded -> case insertOwnership expanded of
                Error e -> Just e
                Ok _ | usesArrays text || "Block" `isInfixOf` text -> case eraseGhosts raw `bindResult` nativeProgram `bindResult` insertOwnership `bindResult` verifyProgram of
                    Error e -> Just ("the lowered owned MIR is ill formed: " ++ e)
                    Ok () -> Nothing
                Ok _ | not (any makesReference (statementsOf raw)) -> Nothing
                Ok owned -> case (runOwned owned, runProgram raw) of
                    (Right a, Ok b) -> testAssertEq a b
                    (Left e, Error e') | e == e' -> Nothing
                    (Left e, _) -> Just ("the owned program fails on the heap model: " ++ e)
                    (Right a, Error e) -> Just ("the model returns " ++ show a ++ " where the executor stops with " ++ e)
    nativeTool = do
        tool <- ownershipTool
        pure $ case tool of
            ToolNative _ -> Nothing
            ToolFailed e -> Just e
            ToolInterpreted _ -> Just "a production caller received an interpreted ownership tool"
    refusedInSource source = case compileSource source of
        Error e | "Move error" `isInfixOf` e && "borrowed" `isInfixOf` e -> Nothing
        Error e -> Just ("refused at another stage: " ++ e)
        Ok _ -> Just "the source checker accepts the pattern"
    sameOwnedMain a b = do
        tool <- ownershipTool
        case tool of
            ToolNative exe -> do
                (_, outA, errA) <- runWithInputFull exe a
                (_, outB, errB) <- runWithInputFull exe b
                pure $ case (readProgram outA, readProgram outB) of
                    (Ok x, Ok y) -> firstFailure [testAssertEq (errA, errB) ("", ""), testAssertEq (fnBlocks (progMain x)) (fnBlocks (progMain y)), testAssertEq (fnLocals (progMain x)) (fnLocals (progMain y))]
                    (Error e, _) -> Just ("legacy: " ++ e ++ errA)
                    (_, Error e) -> Just ("named: " ++ e ++ errB)
            ToolFailed e -> pure (Just e)
            ToolInterpreted _ -> pure (Just "the paired control requires the production native tool")
    toolRefuses input = do
        tool <- ownershipTool
        case tool of
            ToolFailed e -> pure (Just e)
            ToolInterpreted _ -> pure (Just "refusal test requires the production native tool")
            ToolNative exe -> do
                (code, out, err) <- runWithInputFull exe input
                pure (testAssertTrue (code == ExitSuccess && out == "1\n" && not (null err)))

testOwnershipInterpreted :: Test
testOwnershipInterpreted = TestList "testOwnershipInterpreted"
    ([testCase label (sameAsNative program) | (label, program) <- smallOwnershipFixtures] ++
     [ testCase "a reference write releases the value it replaces" (model storedOwnerFixture)
     , testCase "a view of a replaced referent is a copy of its own" (model mutableViewFixture)
     , testCase "a field write through a reference releases the field it replaces" (model storedFieldFixture)
     , testCase "a view of a place written through a reborrow is a copy of its own" (firstFailure [model reborrowedWriteFixture, notPeeked (Local 4) reborrowedWriteFixture])
     , testCase "a view of a place written through a reference is a copy of its own" (firstFailure [model writtenSourceFixture, notPeeked (Local 2) writtenSourceFixture])
     , testCase "a view lent to a callee that writes its source is a copy of its own" (firstFailure [model calleeWriteFixture, notPeeked (Local 2) calleeWriteFixture])
     , testCase "a borrowed view outlives a replacement of its source as a copy" (firstFailure [model borrowedViewFixture, notPeeked (Local 2) borrowedViewFixture])
     -- Lowered programs name a list and a Box as their structs (`named "List" 1 type T`), and the Tersus passes must see
     -- through those names: to the references a list or a Box holds, and to the element an index of either reaches
     , testCase "a lowered list that holds a reference keeps a view of its referent a copy" (firstFailure [heapModel loweredListReferenceFixture, notPeeked (Local 5) loweredListReferenceFixture])
     , testCase "a lowered Box that holds a reference keeps a view of its referent a copy" (firstFailure [heapModel loweredBoxReferenceFixture, notPeeked (Local 5) loweredBoxReferenceFixture])
     , testCase "a write at an index of a lowered list through a reference releases the element" (heapModel loweredIndexWriteFixture)
     ])
  where
    -- (the interpreted emitter owns the program as the native tool does, and the owned program runs on the heap model to the executor's answer)
    sameAsNative program = case (interpretedOwnership program, insertOwnership program) of
        (Error e, _) -> Just e
        (_, Error e) -> Just ("native: " ++ e)
        (Ok owned, Ok native) -> firstFailure
            [ testAssertEq owned native
            , case (runOwned owned, runProgram program) of
                (Right a, Ok b) -> testAssertEq a b
                (Left e, _) -> Just ("the owned program fails on the heap model: " ++ e)
                (Right a, Error e) -> Just ("the model returns " ++ show a ++ " where the executor stops with " ++ e)
            ]
    model program = case interpretedOwnership program of
        Error e -> Just e
        Ok owned -> fmap (++ ("\n" ++ renderProgram owned)) (testAssertEq (runOwned owned) (Right (Just (MInt 1))))
    heapModel program = case interpretedOwnership program of
        Error e -> Just e
        Ok owned -> fmap (++ ("\n" ++ renderProgram owned)) (testAssertEq (runOwned owned) (Right (Just (MInt 1))))
    notPeeked local program = case interpretedOwnership program of
        Error e -> Just e
        Ok owned -> testAssertEq [() | BasicBlock stmts _ <- Map.elems (fnBlocks (progMain owned)), Peek d _ <- stmts, d == local] []
-- The emitter's program as the interpreter runs it, made once for every fixture
interpretedEmitter :: Result Program String
interpretedEmitter = mapResult monomorphizeForValidation (toolProgram emitterEntry)
{-# NOINLINE interpretedEmitter #-}

interpretedOwnership :: Program -> Result Program String
interpretedOwnership program = interpretedEmitter `bindResult` \tool ->
    runProgramEnv (RunEnv [] input (const Nothing)) tool `bindResult` \outcome ->
        if outValue outcome /= Nothing || not (null (outStderr outcome))
            then Error ("interpreted ownership failed: " ++ outStderr outcome)
            else readProgram (outStdout outcome) `bindResult` restoreOwnership program
  where
    input = "pass ownership\n" ++ writeProgramWithGhosts (ownershipInput program)

smallOwnershipFixtures :: [(String, Program)]
smallOwnershipFixtures = [("repeated consumes are owned as natively and run", plain), ("partial fields are owned as natively and run", fields), ("conditional drops are owned as natively and run", conditional)]
  where
    list = TList TInt
    decl n ty = (Local n, LocalDecl ty Nothing)
    base = wireEmpty{progMain = (progMain wireEmpty){fnReturns = Just TInt, fnLocals = Map.fromList [decl 0 TInt, decl 1 list, decl 2 list, decl 3 list, decl 4 TInt]}}
    assign n rv = Assign (Local n) rv
    make n = MakeList [Const (CInt n)]
    len n = ListOp Length [Copy (Local n)]
    plain = base{progMain = (progMain base){fnBlocks = Map.singleton (BlockId 0) (BasicBlock [assign 1 (make 7), assign 2 (Use (Copy (Local 1))), assign 3 (ListOp Push [Copy (Local 1), Const (CInt 9)]), assign 0 (len 2)] Return)}}
    fields = base{progTypes = Map.singleton "Holder" (StructDecl [("xs", list), ("ys", list)]), progMain = (progMain base){fnLocals = Map.insert (Local 4) (LocalDecl (TNamed "Holder" []) Nothing) (fnLocals (progMain base)), fnBlocks = Map.singleton (BlockId 0) (BasicBlock [assign 1 (make 7), assign 2 (make 9), assign 4 (MakeData "Holder" [("xs", Copy (Local 1)), ("ys", Copy (Local 2))]), assign 3 (ReadField (Copy (Local 4)) "Holder" "xs"), assign 0 (len 3)] Return)}}
    conditional = base{progMain = (progMain base){fnBlocks = Map.fromList [(BlockId 0, BasicBlock [assign 1 (make 7)] (SwitchBool (Const (CBool True)) (BlockId 1) (BlockId 2))), (BlockId 1, BasicBlock [Drop (Local 1)] (Goto (BlockId 3))), (BlockId 2, BasicBlock [] (Goto (BlockId 3))), (BlockId 3, BasicBlock [assign 0 (Use (Const (CInt 9)))] Return)]}}

storedOwnerFixture :: Program
storedOwnerFixture = wireEmpty{progFunctions = Map.singleton "store" store, progMain = entry}
  where
    list = TList TInt
    decl n ty = (Local n, LocalDecl ty Nothing)
    store = (progMain wireEmpty)
        { fnName = "store", fnParams = [Local 1, Local 2], fnReturns = Just TInt, fnBorrowed = [Local 1], fnMutBorrowed = [Local 1]
        , fnLocals = Map.fromList [decl 0 TInt, decl 1 (TMutRef list), decl 2 list]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [AssignRef (Local 1) [] (Use (Copy (Local 2))), Assign (Local 0) (Use (Const (CInt 0)))] Return)
        }
    entry = (progMain wireEmpty)
        { fnReturns = Just TInt, fnLocals = Map.fromList [decl 0 TInt, decl 1 list, decl 2 list, decl 3 (TMutRef list)]
        , fnBlocks = Map.fromList
            [(BlockId 0, BasicBlock [Assign (Local 1) (MakeList [Const (CInt 7)]), Assign (Local 2) (MakeList [Const (CInt 9)]), Assign (Local 3) (Borrow (Local 1) [] True)] (Call (Const (CFn "store")) [Copy (Local 3), Copy (Local 2)] (Local 0) (BlockId 1)))
            ,(BlockId 1, BasicBlock [Assign (Local 0) (ListOp Length [Copy (Local 1)])] Return)]
        }

storedFieldFixture :: Program
storedFieldFixture = wireEmpty{progTypes = Map.singleton "Holder" (StructDecl [("xs", list), ("n", TInt)]), progFunctions = Map.singleton "store" store, progMain = entry}
  where
    list = TList TInt
    holder = TNamed "Holder" []
    decl n ty = (Local n, LocalDecl ty Nothing)
    store = (progMain wireEmpty)
        { fnName = "store", fnParams = [Local 1, Local 2], fnReturns = Just TInt, fnBorrowed = [Local 1], fnMutBorrowed = [Local 1]
        , fnLocals = Map.fromList [decl 0 TInt, decl 1 (TMutRef holder), decl 2 list]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [AssignRef (Local 1) [RefField "Holder" "xs"] (Use (Copy (Local 2))), Assign (Local 0) (Use (Const (CInt 0)))] Return)
        }
    entry = (progMain wireEmpty)
        { fnReturns = Just TInt, fnLocals = Map.fromList [decl 0 TInt, decl 1 holder, decl 2 list, decl 3 (TMutRef holder), decl 4 list, decl 5 list]
        , fnBlocks = Map.fromList
            [(BlockId 0, BasicBlock [Assign (Local 4) (MakeList [Const (CInt 7)]), Assign (Local 1) (MakeData "Holder" [("xs", Copy (Local 4)), ("n", Const (CInt 3))]), Assign (Local 2) (MakeList [Const (CInt 9)]), Assign (Local 3) (Borrow (Local 1) [] True)] (Call (Const (CFn "store")) [Copy (Local 3), Copy (Local 2)] (Local 0) (BlockId 1)))
            ,(BlockId 1, BasicBlock [Assign (Local 5) (ReadField (Copy (Local 1)) "Holder" "xs"), Assign (Local 0) (ListOp Length [Copy (Local 5)])] Return)]
        }

-- xs = [[7]]; r1 = &mut xs; a = *r1; old = get(a, 0); n = size(old); r2 = &mut *r1; *r2 = [[9, 10]]; return size(old);
reborrowedWriteFixture :: Program
reborrowedWriteFixture = wireEmpty{progMain = entry}
  where
    list = TList TInt
    nested = TList list
    decl n ty = (Local n, LocalDecl ty Nothing)
    entry = (progMain wireEmpty)
        { fnReturns = Just TInt
        , fnLocals = Map.fromList [decl 0 TInt, decl 1 nested, decl 2 (TMutRef nested), decl 3 nested, decl 4 list, decl 5 TInt, decl 6 (TMutRef nested), decl 7 nested]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock
            [ Assign (Local 1) (Use (Const (CList [CList [CInt 7]])))
            , Assign (Local 2) (Borrow (Local 1) [] True)
            , Assign (Local 3) (Deref (Copy (Local 2)))
            , Assign (Local 4) (ListOp Get [Copy (Local 3), Const (CInt 0)])
            , Assign (Local 5) (ListOp Length [Copy (Local 4)])
            , Assign (Local 6) (Borrow (Local 2) [] True)
            , Assign (Local 7) (Use (Const (CList [CList [CInt 9, CInt 10]])))
            , AssignRef (Local 6) [] (Use (Copy (Local 7)))
            , Assign (Local 0) (ListOp Length [Copy (Local 4)])
            ] Return)
        }

-- xs = [[7]]; a = get(xs, 0); r = &mut xs; *r = [[9]]; return size(a);
writtenSourceFixture :: Program
writtenSourceFixture = wireEmpty{progMain = entry}
  where
    list = TList TInt
    nested = TList list
    decl n ty = (Local n, LocalDecl ty Nothing)
    entry = (progMain wireEmpty)
        { fnReturns = Just TInt
        , fnLocals = Map.fromList [decl 0 TInt, decl 1 nested, decl 2 list, decl 3 (TMutRef nested), decl 4 nested]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock
            [ Assign (Local 1) (Use (Const (CList [CList [CInt 7]])))
            , Assign (Local 2) (ListOp Get [Copy (Local 1), Const (CInt 0)])
            , Assign (Local 3) (Borrow (Local 1) [] True)
            , Assign (Local 4) (Use (Const (CList [CList [CInt 9]])))
            , AssignRef (Local 3) [] (Use (Copy (Local 4)))
            , Assign (Local 0) (ListOp Length [Copy (Local 2)])
            ] Return)
        }

-- fn f(t: &List<Int>, r: &mut List<List<Int>>) -> Int { *r = [[9]]; return size(*t); };
-- xs = [[7]]; a = get(xs, 0); return f(&a, &mut xs);
calleeWriteFixture :: Program
calleeWriteFixture = wireEmpty{progFunctions = Map.singleton "f" callee, progMain = entry}
  where
    list = TList TInt
    nested = TList list
    decl n ty = (Local n, LocalDecl ty Nothing)
    callee = (progMain wireEmpty)
        { fnName = "f", fnParams = [Local 1, Local 2], fnReturns = Just TInt, fnBorrowed = [Local 1, Local 2], fnMutBorrowed = [Local 2]
        , fnLocals = Map.fromList [decl 0 TInt, decl 1 (TRef list), decl 2 (TMutRef nested), decl 3 nested, decl 4 list]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock
            [ Assign (Local 3) (Use (Const (CList [CList [CInt 9]])))
            , AssignRef (Local 2) [] (Use (Copy (Local 3)))
            , Assign (Local 4) (Deref (Copy (Local 1)))
            , Assign (Local 0) (ListOp Length [Copy (Local 4)])
            ] Return)
        }
    entry = (progMain wireEmpty)
        { fnReturns = Just TInt
        , fnLocals = Map.fromList [decl 0 TInt, decl 1 nested, decl 2 list, decl 3 (TRef list), decl 4 (TMutRef nested)]
        , fnBlocks = Map.fromList
            [ (BlockId 0, BasicBlock
                [ Assign (Local 1) (Use (Const (CList [CList [CInt 7]])))
                , Assign (Local 2) (ListOp Get [Copy (Local 1), Const (CInt 0)])
                , Assign (Local 3) (Borrow (Local 2) [] False)
                , Assign (Local 4) (Borrow (Local 1) [] True)
                ] (Call (Const (CFn "f")) [Copy (Local 3), Copy (Local 4)] (Local 0) (BlockId 1)))
            , (BlockId 1, BasicBlock [] Return)
            ]
        }

-- An example as these checks read it: a package linked, a single file lowered
exampleProgram :: FilePath -> IO (Result Program String)
exampleProgram path = do
    loaded <- loadFromFilesystem path
    case loaded of
        Right (PackageResult _) -> linkedFromFile path
        _ -> lowerSource True <$> readFile path

-- The model fixtures, run natively; a lowered one without its list structs, which list lowering makes again
nativeFixtures :: [(String, Program)]
nativeFixtures =
    [ ("a reference write releases the value it replaces", referencesByValue storedOwnerFixture)
    , ("a view of a replaced referent is a copy of its own", referencesByValue mutableViewFixture)
    , ("a field write through a reference releases the field it replaces", referencesByValue storedFieldFixture)
    , ("a view of a place written through a reborrow is a copy of its own", referencesByValue reborrowedWriteFixture)
    , ("a view of a place written through a reference is a copy of its own", referencesByValue writtenSourceFixture)
    , ("a view lent to a callee that writes its source is a copy of its own", referencesByValue calleeWriteFixture)
    , ("a borrowed view outlives a replacement of its source as a copy", referencesByValue borrowedViewFixture)
    , ("a lowered list that holds a reference keeps a view of its referent a copy", withoutListStructs loweredListReferenceFixture)
    , ("a lowered Box that holds a reference keeps a view of its referent a copy", withoutListStructs loweredBoxReferenceFixture)
    , ("a write at an index of a lowered list through a reference releases the element", withoutListStructs loweredIndexWriteFixture)
    ]
  where
    withoutListStructs p = p{progTypes = Map.filterWithKey (\name _ -> take 5 name /= "List<" && take 4 name /= "Box<") (progTypes p)}
    -- (a parameter that is a reference is given by value, as the checker of native MIR wants it: a lent parameter has the
    -- type of what it is lent, which these fixtures write as the reference itself)
    referencesByValue p = p{progFunctions = Map.map byValue (progFunctions p)}
    byValue fn = fn{fnBorrowed = filter (not . reference fn) (fnBorrowed fn), fnMutBorrowed = filter (not . reference fn) (fnMutBorrowed fn)}
    reference fn l = case Map.lookup l (fnLocals fn) of
        Just (LocalDecl (TRef _) _) -> True
        Just (LocalDecl (TMutRef _) _) -> True
        _ -> False

-- One write at an index through a reference, as the ownership tool reads it: with the old `list` tokens, and with a list
-- named as its struct, as lowering writes it
elementWriteLegacy :: String
elementWriteLegacy = unlines
    [ "pass ownership", "tersus-mir 2"
    , "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
    , "local 0 none int", "local 1 some \"xs\" list list int", "local 2 none list int", "local 3 some \"r\" mutref list list int", "local 4 none list int"
    , "block 0", "assign 2 makelist 1 const int 7", "assign 1 makelist 1 copy 2", "assign 3 borrowmut 1 0"
    , "assign 4 makelist 2 const int 9 const int 10", "assignref 3 1 index const int 0 use copy 4", "assign 0 listop length 1 copy 1"
    , "return", "end"
    ]

-- A reference kept in a Box, read back and written through while a view of its place is live: with the old `box` and
-- `list` tokens, and named and declared as lowering writes them
boxedReferenceLegacy :: String
boxedReferenceLegacy = unlines $
    [ "pass ownership", "tersus-mir 2"
    , "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
    , "local 0 none int", "local 1 some \"xs\" list list int", "local 2 none list int", "local 3 some \"r\" mutref list list int"
    , "local 4 some \"b\" box mutref list list int", "local 5 some \"t\" list int", "local 6 some \"r2\" mutref list list int"
    , "local 7 none list list int", "local 8 none list int"
    ] ++ boxedReferenceBody

boxedReferenceNamed :: String
boxedReferenceNamed = unlines $
    [ "pass ownership" ] ++ loweredHeader ++
    [ "struct \"Box<&mut List<List<Int>>>\" 1 \"addr\" addr mutref named \"List\" 1 type named \"List\" 1 type int"
    , "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
    , "local 0 none int", "local 1 some \"xs\" named \"List\" 1 type named \"List\" 1 type int", "local 2 none named \"List\" 1 type int"
    , "local 3 some \"r\" mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 4 some \"b\" named \"Box\" 1 type mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 5 some \"t\" named \"List\" 1 type int", "local 6 some \"r2\" mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 7 none named \"List\" 1 type named \"List\" 1 type int", "local 8 none named \"List\" 1 type int"
    ] ++ boxedReferenceBody

boxedReferenceBody :: [String]
boxedReferenceBody =
    [ "block 0", "assign 2 makelist 1 const int 7", "assign 1 makelist 1 copy 2", "assign 3 borrowmut 1 0", "assign 4 makebox copy 3"
    , "assign 5 listop get 2 copy 1 const int 0", "assign 6 unbox copy 4", "assign 8 makelist 1 const int 9", "assign 7 makelist 1 copy 8"
    , "assignref 6 0 use copy 7", "assign 0 listop length 1 copy 5", "return", "end"
    ]

elementWriteNamed :: String
elementWriteNamed = unlines $
    [ "pass ownership" ] ++ loweredHeader ++
    [ "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
    , "local 0 none int", "local 1 some \"xs\" named \"List\" 1 type named \"List\" 1 type int", "local 2 none named \"List\" 1 type int"
    , "local 3 some \"r\" mutref named \"List\" 1 type named \"List\" 1 type int", "local 4 none named \"List\" 1 type int"
    , "block 0", "assign 2 makelist 1 const int 7", "assign 1 makelist 1 copy 2", "assign 3 borrowmut 1 0"
    , "assign 4 makelist 2 const int 9 const int 10", "assignref 3 1 index const int 0 use copy 4", "assign 0 listop length 1 copy 1"
    , "return", "end"
    ]

-- MIR as data written after list lowering
loweredFixture :: [String] -> Program
loweredFixture text = case readProgram (unlines text) of
    Ok program -> program
    Error e -> error ("a lowered fixture does not read: " ++ e)

loweredHeader :: [String]
loweredHeader =
    [ "tersus-mir 2"
    , "struct \"List<Int>\" 3 \"addr\" addr int \"len\" int \"cap\" int"
    , "struct \"List<List<Int>>\" 3 \"addr\" addr named \"List\" 1 type int \"len\" int \"cap\" int"
    ]

-- xs = [[7]]; r = &mut xs; rs = [r]; t = get(xs, 0); r2 = get(rs, 0); *r2 = [[9]]; return size(t);
loweredListReferenceFixture :: Program
loweredListReferenceFixture = loweredFixture $ loweredHeader ++
    [ "struct \"List<&mut List<List<Int>>>\" 3 \"addr\" addr mutref named \"List\" 1 type named \"List\" 1 type int \"len\" int \"cap\" int"
    , "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
    , "local 0 none int"
    , "local 1 some \"xs\" named \"List\" 1 type named \"List\" 1 type int"
    , "local 2 none named \"List\" 1 type int"
    , "local 3 some \"r\" mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 4 some \"rs\" named \"List\" 1 type mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 5 some \"t\" named \"List\" 1 type int"
    , "local 6 some \"r2\" mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 7 none named \"List\" 1 type named \"List\" 1 type int"
    , "local 8 none named \"List\" 1 type int"
    , "block 0"
    , "assign 2 makelist 1 const int 7"
    , "assign 1 makelist 1 copy 2"
    , "assign 3 borrowmut 1 0"
    , "assign 4 makelist 1 copy 3"
    , "assign 5 listop get 2 copy 1 const int 0"
    , "assign 6 listop get 2 copy 4 const int 0"
    , "assign 8 makelist 1 const int 9"
    , "assign 7 makelist 1 copy 8"
    , "assignref 6 0 use copy 7"
    , "assign 0 listop length 1 copy 5"
    , "return"
    , "end"
    ]

-- The same with the reference kept in a Box: b = Box::new(r); r2 = Box::unbox(b). Lowering declares the Box as its struct,
-- whose address hides what it holds
loweredBoxReferenceFixture :: Program
loweredBoxReferenceFixture = loweredFixture $ loweredHeader ++
    [ "struct \"Box<&mut List<List<Int>>>\" 1 \"addr\" addr mutref named \"List\" 1 type named \"List\" 1 type int"
    , "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
    , "local 0 none int"
    , "local 1 some \"xs\" named \"List\" 1 type named \"List\" 1 type int"
    , "local 2 none named \"List\" 1 type int"
    , "local 3 some \"r\" mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 4 some \"b\" named \"Box\" 1 type mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 5 some \"t\" named \"List\" 1 type int"
    , "local 6 some \"r2\" mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 7 none named \"List\" 1 type named \"List\" 1 type int"
    , "local 8 none named \"List\" 1 type int"
    , "block 0"
    , "assign 2 makelist 1 const int 7"
    , "assign 1 makelist 1 copy 2"
    , "assign 3 borrowmut 1 0"
    , "assign 4 makebox copy 3"
    , "assign 5 listop get 2 copy 1 const int 0"
    , "assign 6 unbox copy 4"
    , "assign 8 makelist 1 const int 9"
    , "assign 7 makelist 1 copy 8"
    , "assignref 6 0 use copy 7"
    , "assign 0 listop length 1 copy 5"
    , "return"
    , "end"
    ]

-- xs = [[7]]; r = &mut xs; (*r)[0] = [9, 10]; return size(xs);
loweredIndexWriteFixture :: Program
loweredIndexWriteFixture = loweredFixture $ loweredHeader ++
    [ "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
    , "local 0 none int"
    , "local 1 some \"xs\" named \"List\" 1 type named \"List\" 1 type int"
    , "local 2 none named \"List\" 1 type int"
    , "local 3 some \"r\" mutref named \"List\" 1 type named \"List\" 1 type int"
    , "local 4 none named \"List\" 1 type int"
    , "block 0"
    , "assign 2 makelist 1 const int 7"
    , "assign 1 makelist 1 copy 2"
    , "assign 3 borrowmut 1 0"
    , "assign 4 makelist 2 const int 9 const int 10"
    , "assignref 3 1 index const int 0 use copy 4"
    , "assign 0 listop length 1 copy 1"
    , "return"
    , "end"
    ]

-- xs = [[7]]; a = get(xs, 0); t = &a; xs = set(xs, 0, [9]); return size(*t);
borrowedViewFixture :: Program
borrowedViewFixture = wireEmpty{progMain = entry}
  where
    list = TList TInt
    nested = TList list
    decl n ty = (Local n, LocalDecl ty Nothing)
    entry = (progMain wireEmpty)
        { fnReturns = Just TInt
        , fnLocals = Map.fromList [decl 0 TInt, decl 1 nested, decl 2 list, decl 3 (TRef list), decl 4 list, decl 5 list]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock
            [ Assign (Local 1) (Use (Const (CList [CList [CInt 7]])))
            , Assign (Local 2) (ListOp Get [Copy (Local 1), Const (CInt 0)])
            , Assign (Local 3) (Borrow (Local 2) [] False)
            , Assign (Local 4) (Use (Const (CList [CInt 9])))
            , Assign (Local 1) (ListOp Set [Copy (Local 1), Const (CInt 0), Copy (Local 4)])
            , Assign (Local 5) (Deref (Copy (Local 3)))
            , Assign (Local 0) (ListOp Length [Copy (Local 5)])
            ] Return)
        }

mutableViewFixture :: Program
mutableViewFixture = wireEmpty{progFunctions = Map.singleton "view" view, progMain = entry}
  where
    list = TList TInt
    nested = TList list
    decl n ty = (Local n, LocalDecl ty Nothing)
    view = (progMain wireEmpty)
        { fnName = "view", fnParams = [Local 1], fnReturns = Just TInt, fnBorrowed = [Local 1], fnMutBorrowed = [Local 1]
        , fnLocals = Map.fromList [decl 0 TInt, decl 1 (TMutRef nested), decl 2 nested, decl 3 list, decl 4 TInt, decl 5 list, decl 6 nested]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock
            [Assign (Local 2) (Deref (Copy (Local 1)))
            ,Assign (Local 3) (ListOp Get [Copy (Local 2), Const (CInt 0)])
            ,Assign (Local 4) (ListOp Length [Copy (Local 3)])
            ,Assign (Local 5) (MakeList [Const (CInt 9), Const (CInt 10)])
            ,Assign (Local 6) (MakeList [Copy (Local 5)])
            ,AssignRef (Local 1) [] (Use (Copy (Local 6)))
            ,Assign (Local 0) (ListOp Length [Copy (Local 3)])] Return)
        }
    entry = (progMain wireEmpty)
        { fnReturns = Just TInt, fnLocals = Map.fromList [decl 0 TInt, decl 1 nested, decl 2 list, decl 3 (TMutRef nested)]
        , fnBlocks = Map.fromList
            [(BlockId 0, BasicBlock [Assign (Local 2) (MakeList [Const (CInt 7)]), Assign (Local 1) (MakeList [Copy (Local 2)]), Assign (Local 3) (Borrow (Local 1) [] True)] (Call (Const (CFn "view")) [Copy (Local 3)] (Local 0) (BlockId 1)))
            ,(BlockId 1, BasicBlock [] Return)]
        }

mutableNamedReference :: TestResult
mutableNamedReference = checkNamedReference "update<Int>" TInt (monomorphize (namedReferenceFixture (TParam "T") TInt ["T"]))

mutableReferenceListNormalization :: TestResult
mutableReferenceListNormalization = case lowerLists (Ok []) (namedReferenceFixture boxed boxed []) of
    Error e -> Just e
    Ok output -> checkNamedReference "update" (TList TInt) output
  where
    boxed = TBox (TArrayOf TInt SizeAny)

checkNamedReference :: String -> Type -> Program -> TestResult
checkNamedReference function element output = case Map.lookup function (progFunctions output) of
    Nothing -> Just ("the reference adapter did not keep " ++ function)
    Just fn -> firstFailure
        [ testAssertEq (localType <$> Map.lookup (Local 1) (fnLocals fn)) (Just (TMutRef holder))
        , testAssertEq (blockStatements (fnBlocks fn Map.! BlockId 0)) [AssignRef (Local 1) [RefField name "n"] (Use (Const (CInt 9)))]
        , testAssertEq (Map.lookup name (progTypes output)) (Just (StructDecl [("payload", element), ("n", TInt)]))
        , testAssertTrue (Map.notMember (instanceName "Holder" [ArgType (TParam "T")]) (progTypes output))
        ]
  where
    holder = TNamed "Holder" [ArgType element]
    name = instanceName "Holder" [ArgType element]

namedReferenceFixture :: Type -> Type -> [String] -> Program
namedReferenceFixture parameter actual typeParameters = wireEmpty
    { progTypes = Map.singleton name (StructDecl [("payload", parameter), ("n", TInt)])
    , progGenerics = Map.singleton "Holder" (["T"], [("payload", TParam "T"), ("n", TInt)])
    , progFunctions = Map.singleton "update" update
    , progMain = (progMain wireEmpty)
        { fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl (TMutRef (holder actual)) Nothing)]
        , fnBlocks = Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "update")) [Copy (Local 1)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]
        }
    }
  where
    holder element = TNamed "Holder" [ArgType element]
    name = instanceName "Holder" [ArgType parameter]
    update = (progMain wireEmpty)
        { fnName = "update", fnParams = [Local 1], fnTypeParams = typeParameters, fnBorrowed = [Local 1], fnMutBorrowed = [Local 1]
        , fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl (TMutRef (holder parameter)) Nothing)]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [AssignRef (Local 1) [RefField name "n"] (Use (Const (CInt 9)))] Return)
        }

genericReferenceWrite :: TestResult
genericReferenceWrite = case Map.lookup "update<Int, 2>" (progFunctions (monomorphize input)) of
    Nothing -> Just "the mono adapter did not instantiate a generic update"
    Just fn -> firstFailure
        [ testAssertEq (fnParams fn, fnBorrowed fn, fnMutBorrowed fn, fnFrom fn) ([Local 1], [Local 1], [Local 1], [Local 1])
        , testAssertEq (localType <$> Map.lookup (Local 1) (fnLocals fn)) (Just (TMutRef (TArrayOf TInt (SizeConst 2))))
        , testAssertEq (blockStatements (fnBlocks fn Map.! BlockId 0)) [AssignRef (Local 1) [RefIndex (Const (CInt 2))] (Use (Const (CInt 9))), Assign (Local 0) (Use (Const (CInt 0)))]
        ]
  where
    generic = (progMain wireEmpty)
        { fnName = "update", fnParams = [Local 1, Local 2], fnReturns = Just TInt, fnTypeParams = ["T"], fnSizeParams = ["n"]
        , fnBorrowed = [Local 1], fnMutBorrowed = [Local 1], fnFrom = [Local 1]
        , fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl (TMutRef (TArrayOf (TParam "T") (SizeParam "n"))) (Just "array")), (Local 2, LocalDecl TInt (Just "n"))]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [AssignRef (Local 1) [RefIndex (Copy (Local 2))] (Use (Const (CInt 9))), Assign (Local 0) (Use (Const (CInt 0)))] Return)
        }
    input = wireEmpty
        { progFunctions = Map.singleton "update" generic
        , progMain = (progMain wireEmpty)
            { fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl (TMutRef (TArrayOf TInt (SizeConst 2))) Nothing)]
            , fnBlocks = Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "update")) [Copy (Local 1), Const (CInt 2)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]
            }
        }

nestedSequenceWrite :: TestResult
nestedSequenceWrite = case expandRefWrites input of
    Error e -> Just e
    Ok output -> firstFailure
        [ testAssertEq (localType <$> Map.lookup (Local 3) locals) (Just (TList (TList TInt)))
        , testAssertEq (localType <$> Map.lookup (Local 4) locals) (Just (TList TInt))
        , testAssertEq (runProgram input) (runProgram output)
        ]
      where locals = fnLocals (progMain output)
  where
    list = TList TInt
    input = wireEmpty{progMain = (progMain wireEmpty)
        { fnReturns = Just (TList (TList list))
        , fnLocals = Map.fromList [(Local 0, LocalDecl (TList (TList list)) Nothing), (Local 1, LocalDecl (TList (TList list)) (Just "rows")), (Local 2, LocalDecl list (Just "replacement"))]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock
            [ Assign (Local 1) (Use (Const (CList [CList [CList [CInt 1]]])))
            , Assign (Local 2) (Use (Const (CList [CInt 2, CInt 3])))
            , AssignRef (Local 1) [RefIndex (Const (CInt 0)), RefIndex (Const (CInt 0))] (Use (Copy (Local 2)))
            , Assign (Local 0) (Use (Copy (Local 1)))
            ] Return)
        }}

enumFieldWrite :: TestResult
enumFieldWrite = case expandRefWrites input of
    Error e -> Just e
    Ok output -> firstFailure
        [ testAssertEq (localType <$> Map.lookup (Local 3) (fnLocals (progMain output))) (Just list)
        , testAssertEq [map fst fields | block <- Map.elems (fnBlocks (progMain output)), Assign (Local 1) (MakeData "E::Some" fields) <- blockStatements block] [["xs", "tag"]]
        , testAssertEq (runProgram input) (runProgram output)
        ]
  where
    list = TList TInt
    input = wireEmpty
        { progTypes = Map.singleton "E" (EnumDecl [("E::Some", [("xs", list), ("tag", TInt)]), ("E::None", [])])
        , progMain = (progMain wireEmpty)
            { fnReturns = Just (TNamed "E" [])
            , fnLocals = Map.fromList [(Local 0, LocalDecl (TNamed "E" []) Nothing), (Local 1, LocalDecl (TVariant "E::Some") (Just "value")), (Local 2, LocalDecl list (Just "replacement"))]
            , fnBlocks = Map.singleton (BlockId 0) (BasicBlock
                [ Assign (Local 1) (Use (Const (CData "E::Some" [("xs", CList [CInt 1]), ("tag", CInt 41)])))
                , Assign (Local 2) (Use (Const (CList [CInt 2, CInt 3])))
                , AssignRef (Local 1) [RefField "E::Some" "xs"] (Use (Copy (Local 2)))
                , Assign (Local 0) (Use (Copy (Local 1)))
                ] Return)
            }
        }

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [e | Just e <- results] of e : _ -> Just e; [] -> Nothing

metadataFixture :: Program
metadataFixture = Program
    { progTypes = Map.fromList [("Packet<n>", StructDecl [("items", TArrayOf (TParam "T") (SizeParam "n"))]), ("E", EnumDecl [("E::Some", [("value", TInt)]), ("E::None", [])])]
    , progGenerics = Map.singleton "Packet" (["T", "n"], [("items", TArrayOf (TParam "T") (SizeParam "n")), ("permission", TBlock (TParam "T"))])
    , progInvariants = Map.singleton "Packet" [S.AssignProofVar "invariant" (S.Val (S.VBool True))]
    , progFunctions = Map.singleton "symbolic" symbolic
    , progMain = mainFn
    }
  where
    symbolic = mainFn
        { fnName = "symbolic", fnParams = [Local 1, Local 2], fnSizeParams = ["n"], fnTypeParams = ["T"], fnBorrowed = [Local 1], fnMutBorrowed = [Local 2], fnFrom = [Local 1, Local 2]
        , fnReturns = Just (TRef (TParam "T"))
        , fnLocals = Map.fromList [(Local i, LocalDecl ty (Just ("local \"\\\955\128512 " ++ show i))) | (i, ty) <- zip [0 ..] structuralTypes]
        }
    mainFn = (progMain wireEmpty)
        { fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl TInt (Just "x"))]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Ghost env (GhostFunction "symbolic" "source name" True), Assign (Local 0) (Use (Const (CInt 7))), Ghost env (GhostPosition 4 9), Ghost env (GhostPosition 4 9), Ghost env (GhostDissolve (Local 1)), Ghost env (GhostValidation fact), Ghost env (GhostAxiom "law" ["x"] [fact] [fact]), Ghost env (GhostProof "lemma" ["x"] [fact] [fact] [fact])] Return)
        , fnSpec = emptySpec{specRequires = [fact], specEnsures = [fact], specTermination = Just MayDiverge, specEnv = env, specWrites = ["x.field"], specMutParams = ["x"], specFrom = ["x"], specLoops = Map.singleton (BlockId 0) (LoopSpec [fact] (Just MayDiverge) env (BlockId 0))}
        }
    fact = S.AssignProofVar "fact" (S.Val (S.VInt 7))
    env = Map.fromList [("x", Copy (Local 1)), ("symbolic", Const (CFn "symbolic"))]

structuralTypes :: [Type]
structuralTypes =
    [ TInt, TByte, TBool, TWord True 8, TWord True 16, TWord True 32, TWord False 16, TWord False 32
    , TList (TParam "T"), TBox (TArrayOf TInt SizeAny), TAddr (TParam "T"), TBlock TInt, TUninit (TParam "T")
    , TFn [TRef TInt, TMutRef (TParam "T")] (TParam "T"), TForall ["n"] ["T"] (TArrayOf (TParam "T") (SizeParam "n"))
    , TNamed "Packet" [ArgType (TList (TParam "T")), ArgSize (SizeParam "n"), ArgSize (SizeVar 23)]
    , TVariant "E::Some", TVar 19, TParam "T", TRef TInt, TMutRef (TArrayOf TInt (SizeConst 3))
    , TArrayOf TInt (SizeConst 3), TArrayOf TInt SizeAny, TArrayOf (TParam "T") (SizeParam "n"), TArrayOf TInt (SizeVar 23)
    ]

ownershipFixture :: Program
ownershipFixture = metadataFixture
    { progTypes = Map.singleton "Plain" (StructDecl [("n", TInt)])
    , progFunctions = Map.fromList [(fnName dropFn, dropFn), (fnName cloneFn, cloneFn)]
    }
  where
    dropFn = (progMain wireEmpty){fnName = "<Plain as Drop>::drop", fnParams = [Local 1], fnBorrowed = [Local 1], fnLocals = Map.singleton (Local 1) (LocalDecl (TNamed "Plain" []) (Just "self"))}
    cloneFn = dropFn{fnName = "<Plain as Clone>::clone", fnReturns = Just (TNamed "Plain" []), fnLocals = Map.insert (Local 0) (LocalDecl (TNamed "Plain" []) Nothing) (fnLocals dropFn), fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (Use (Copy (Local 1)))] Return)}

wireEmpty :: Program
wireEmpty = Program Map.empty Map.empty (Function "main" [] Nothing Map.empty (Map.singleton (BlockId 0) (BasicBlock [] Return)) [] [] [] [] [] emptySpec) Map.empty Map.empty

wireMain :: Statement -> Program
wireMain statement = wireEmpty{progMain = (progMain wireEmpty){fnBlocks = Map.singleton (BlockId 0) (BasicBlock [statement] Return)}}

ghostRecord :: String -> String
ghostRecord statement = unlines ["tersus-mir 2", "main \"main\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0", "block 0", statement, "return", "end"]

ghostIds :: Program -> [Int]
ghostIds program = [ident | fn <- Map.elems (progFunctions program) ++ [progMain program], block <- Map.elems (fnBlocks fn), Ghost _ (GhostPosition (-1) ident) <- blockStatements block]

statementsOf :: Program -> [Statement]
statementsOf program = [st | fn <- progMain program : Map.elems (progFunctions program), block <- Map.elems (fnBlocks fn), st <- blockStatements block]

writesReference :: Statement -> Bool
writesReference AssignRef{} = True
writesReference _ = False

makesReference :: Statement -> Bool
makesReference (Assign _ Borrow{}) = True
makesReference st = writesReference st

isGhost :: Statement -> Bool
isGhost Ghost{} = True
isGhost _ = False

withMainBlocks :: (Map.Map BlockId BasicBlock -> Map.Map BlockId BasicBlock) -> Program -> Program
withMainBlocks f program = program{progMain = (progMain program){fnBlocks = f (fnBlocks (progMain program))}}

editMain :: ([Statement] -> [Statement]) -> Program -> Program
editMain f program = program{progMain = (progMain program){fnBlocks = Map.map (\b -> b{blockStatements = f (blockStatements b)}) (fnBlocks (progMain program))}}

splitGhosts :: Program -> Program
splitGhosts program = program{progMain = (progMain program){fnBlocks = Map.fromList [(BlockId 0, BasicBlock (take 2 stmts) (Goto (BlockId 9))), (BlockId 9, BasicBlock (drop 2 stmts) Return)]}}
  where stmts = blockStatements (fnBlocks (progMain program) Map.! BlockId 0)

replaceLine :: String -> String -> String -> String
replaceLine old new = unlines . map (\line -> if line == old then new else line) . lines
