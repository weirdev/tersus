{-# LANGUAGE PatternSynonyms #-}
module TestMirMono (testMirMono, testMirMonoUsing, monoFixtures, metadataProgram, genericProgram, legacyPackInput, currentLoweredFixtures, testCurrentLoweredMetadataHost, testCurrentLoweredMetadataUsing) where

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (ExitCode (..))

import Compile (lowerSource)
import Mir
import MirData (readLowered, readProgram, writeProgramWithGhosts, writeLowered)
import MirOwnershipData (ownershipInput, restoreOwnership)
import MirHousekeeping (Tool (..), monomorphizeWith, ownershipTool, toolProgram, emitterEntry, eraseGhosts, nativeProgram, verifyCaptureEffects)
import MirMono (monomorphizeForValidation)
import qualified MirMonoOracle as Oracle
import Native (runWithInputFull)
import PreludeSource (stdName)
import qualified Syntax as S
import TestHarness
import TestNative (nativeExamples, validatedPrograms, unvalidatedPrograms)
import Types (Arg (..), Size (..), Type (..), Signature (..), BuiltinFunct (..), instanceName)
import Utils
import ValidatorNative (validateCompiled)

unitOf :: Program -> Lowered
unitOf p = Lowered p Set.empty Set.empty Set.empty Set.empty Set.empty Set.empty []

monoDifference :: Program -> Program -> TestResult
monoDifference expected actual
    | expected /= actual = Just ("native mono differs:\n" ++ unlines
        [ "types expected: " ++ take 500 (show (progTypes expected))
        , "types actual: " ++ take 500 (show (progTypes actual))
        , "changed functions: " ++ show (take 6 [name | name <- Set.toList (Map.keysSet (progFunctions expected) `Set.union` Map.keysSet (progFunctions actual)), Map.lookup name (progFunctions expected) /= Map.lookup name (progFunctions actual)])
        , "main changed: " ++ show (progMain expected /= progMain actual)
        ])
    | show expected /= show actual = Just "native mono changed retained builtin metadata"
    | writeLowered (unitOf expected) /= writeLowered (unitOf actual) = Just "native mono reserializes differently"
    | otherwise = Nothing

-- (master's oracle specializes data without checked records: the program is compared as that data writes it)
compareWire :: Program -> IO TestResult
compareWire checked = case writeLowered (unitOf original) of
    Error e -> pure (Just e)
    Ok input -> compareInput original input
  where
    original = checked{progProtocols = Map.empty, progOwnership = Nothing}

compareInput :: Program -> String -> IO TestResult
compareInput original input = do
    tool <- ownershipTool
    case tool of
        ToolNative exe -> do
            (code, out, err) <- runWithInputFull exe ("pass mono\n" ++ input)
            pure $ case (code, err, readLowered out) of
                (ExitSuccess, "", Ok unit) ->
                    let expected = (Oracle.monomorphize original){progCaptureStorage = Map.empty}
                        semantic = monoDifference expected (lowProgram unit)
                        bytes = case writeLowered (unitOf expected) of
                            Error e -> Just e
                            Ok text -> if text == out then Nothing else Just "native MIR3 stdout differs from the canonical Haskell writer"
                     in semantic <> bytes
                _ -> Just ("native full-MIR mono failed: " ++ show code ++ " " ++ err ++ " " ++ take 200 out)
        ToolFailed e -> pure (Just e)
        ToolInterpreted _ -> pure (Just "the full-MIR comparison requires the native emitter")

sourceMono :: (Bool -> String -> Result Program String) -> String -> IO TestResult
sourceMono lower source = case lower True source of
    Error e -> pure (Just ("does not lower: " ++ e))
    Ok p -> do
        raw <- compareWire p
        case raw of
            Just e -> pure (Just ("raw MIR: " ++ e))
            Nothing -> case eraseGhosts p `bindResult` nativeProgram of
                Error e -> pure (Just ("pre-monomorphization native stage refused: " ++ e))
                Ok native -> fmap (fmap ("native-stage MIR: " ++)) (compareWire native)

sourceStorageProvenance :: (Bool -> String -> Result Program String) -> TestResult
sourceStorageProvenance lower = case lower True source of
    Error e -> Just e
    Ok raw ->
        let mono = monomorphizeForValidation raw
            decoded = writeLowered (unitOf raw) `bindResult` readLowered
         in testAssertTrue (Map.member (stdName "core/types" "List") (progCaptureStorage raw))
            <> testAssertTrue (any ("keep<" `isPrefixOf`) (Map.keys (progFunctions mono)))
            <> testAssertEq (progCaptureStorage mono) (progCaptureStorage raw)
            <> testAssertEq (validateCompiled raw) (Ok ())
            <> testAssertEq (mapResult (progCaptureStorage . lowProgram) decoded) (Ok Map.empty)
            <> testAssertErrorContains "a boxed closure capture cannot contain references or permissions"
                (decoded `bindResult` (verifyCaptureEffects . lowProgram))
  where
    source = "fn keep<T>(x: T) -> T { return x; }; xs = keep([1, 2]); let f: Closure<fn() -> Int> = move fn() -> Int => size(xs); return f();"

testMirMono :: Test
testMirMono = testMirMonoUsing lowerSource

testMirMonoUsing :: (Bool -> String -> Result Program String) -> Test
testMirMonoUsing lower = TestList "testMirMono"
    [ TestList "source corpus" [TestCase label (sourceMono lower source) | (label, source) <- validatedPrograms ++ unvalidatedPrograms]
    , TestList "examples" [TestCase path (readFile path >>= sourceMono lower) | path <- nativeExamples]
    , testCurrentLoweredMetadataHost
    , testCurrentLoweredMetadataUsing ownershipTool
    , TestList "complete metadata and substitution" [TestCase label (compareWire p) | (label, p) <- monoFixtures]
    , TestList "validation adapter retains contracts and ghosts"
        [ testCase label (monoDifference (Oracle.monomorphizeForValidation p) (monomorphizeForValidation p)) | (label, p) <- monoFixtures ]
    , TestCase "source storage provenance survives validation Mono but not MIR3" $ pure $ sourceStorageProvenance lower
    , TestCase "the no-generic fast path does not request a native tool" $ do
        actual <- monomorphizeWith (error "the fast path forced the tool") metadataProgram
        pure (testAssertEq actual (Ok metadataProgram))
    , testCase "the comparator catches return type mutation" $ testAssertTrue
        (monoDifference genericProgram genericProgram{progMain = (progMain genericProgram){fnReturns = Just TBool}} /= Nothing)
    , testCase "the comparator catches omitted proof metadata" $ testAssertTrue
        (monoDifference metadataProgram metadataProgram{progInvariants = Map.empty} /= Nothing)
    , testCase "the comparator catches builtin metadata hidden by Value equality" $
        let original = builtinMetadata metadataProgram
            changed = original{progInvariants = Map.singleton "Plain" [S.ProofAssert (S.CTerm (S.VFunct [] [] [] (S.BuiltinFunct Plus) []))]}
         in testAssertTrue (original == changed && monoDifference original changed /= Nothing)
    , testCase "the comparator catches omitted implicit drops" $ testAssertTrue
        (monoDifference dropped dropped{progFunctions = Map.filterWithKey (\n _ -> not (" as Drop>::drop" `isInfixOf` n)) (progFunctions dropped)} /= Nothing)
    , TestCase "a failed native tool is not replaced by Haskell" $ do
        actual <- monomorphizeWith (pure (ToolFailed "mono-failure-sentinel")) genericProgram
        pure (testAssertErrorContains "mono-failure-sentinel" actual)
    , TestCase "an interpreted tool is refused" $ do
        actual <- monomorphizeWith (pure (ToolInterpreted metadataProgram)) genericProgram
        pure (testAssertErrorContains "natively only" actual)
    , TestCase "the emitter's validated program contains the native mono functions" $ pure $ case toolProgram emitterEntry of
        Error e -> Just e
        Ok p -> testAssertTrue (any ("$mono$" `isInfixOf`) (Map.keys (progFunctions p)))
    , TestCase "actual emitter refuses a blank-line trailing suffix" $ case writeLowered (unitOf metadataProgram) of
        Error e -> pure (Just e)
        Ok text -> refuses ("pass mono\n" ++ text ++ "\nunknown-suffix\n")
    , TestCase "actual emitter rejects unescaped non-ASCII quoted names" $ case writeLowered (unitOf metadataProgram) of
        Error e -> pure (Just e)
        Ok text ->
            let prefix = "function \"plain\""
                broken = unlines [if prefix `isPrefixOf` line then "function \"plaín\"" ++ drop (length prefix) line else line | line <- lines text]
             in refuses ("pass mono\n" ++ broken)
    , TestCase "current PackLoop rejects a negative invariant reference" negativePackLoop
    , TestCase "legacy PackLoop metadata emits current canonical MIR3" legacyPackLoop
    , testCase "the comparator catches omitted pack-loop invariants" $ testAssertTrue
        (monoDifference (packLoopMetadata True metadataProgram) (packLoopMetadata False metadataProgram) /= Nothing)
    , TestList "malformed transport" [TestCase label (refuses input) | (label, input) <- refusalFixtures]
    ]
  where
    dropped = Oracle.monomorphize dropProgram

refuses :: String -> IO TestResult
refuses input = do
    tool <- ownershipTool
    case tool of
        ToolNative exe -> do
            (code, out, err) <- runWithInputFull exe input
            pure (testAssertTrue (code == ExitSuccess && out == "1\n" && not (null err)))
        ToolFailed e -> pure (Just e)
        ToolInterpreted _ -> pure (Just "the refusal control requires the native emitter")

refusalFixtures :: [(String, String)]
refusalFixtures =
    [ ("MIR 2 is not full monomorphization transport", "pass mono\ntersus-mir 2\n")
    , ("an incomplete MIR 3 is refused", "pass mono\ntersus-mir 3\nnot-mir\n")
    , ("a bad payload count is refused", "pass mono\ntersus-mir 3\ndata 1\n")
    ]

currentLoweredFixtures :: [(String, Lowered)]
currentLoweredFixtures =
    [ ("no generic keeps mixed ordered assumption payloads", lowered metadataProgram)
    , ("generic specialization retains mixed program payloads", lowered genericProgram)
    ]
  where
    lowered p = (unitOf (p{progInvariants = Map.singleton "Plain" [S.ProofAssert embedded]}))
        { lowCopies = Set.singleton "Plain", lowLinear = Set.singleton "linear-λ"
        , lowDrops = Set.singleton "Plain", lowDeclared = Set.fromList ["Plain", "declared-λ"]
        , lowNested = Set.singleton "nested-é"
        , lowAssumes =
            [Left (S.CTerm (S.VBool False)), Right trustedCall
            ,Left (S.CTerm (S.VInt (10 ^ (30 :: Int)))), Right (S.F (S.Var "otherTrustedCall") [S.Var "λ"])]
        }
    embedded = S.CTerm (S.VFunct [] [] [] (S.NativeFunct (Signature [] TInt [] [] [] []) Nothing [S.Return trustedCall]) [S.CTerm (S.VInt (10 ^ (30 :: Int)))])
    trustedCall = S.F (S.Var "Block::assume")
        [ S.IfExpr (S.Val (S.VBool True))
            (S.BlockExpr [S.Let "branch-λ" (S.Val (S.VInt (10 ^ (30 :: Int)))), S.Return (S.Val (S.VInt 7))]
                (S.Ascribed (S.Var "branch-λ") (TArrayOf (TNamed "Tuple2" [ArgType TInt, ArgType TBool]) (SizeConst 3))))
            (S.Val (S.VInt 4))
        , S.Ascribed (S.Val (S.VList [])) (TNamed "List" [ArgType TInt])
        ]

currentLoweredMutations :: String -> [(String, String)]
currentLoweredMutations input =
    [ ("an expression child cannot replace the Ascribed type child", change "Ascribed" (\_ xs -> [head xs, xs !! 1, xs !! 1]))
    , ("an AST expression cannot be a Block statement list", change "BlockExpr" (\_ xs -> [head xs, last xs, last xs]))
    , ("a forward expression reference is refused", change "IfExpr" (\index xs -> [head xs, show (index + 1), xs !! 2, xs !! 3]))
    , ("an expression child may be used only once", change "IfExpr" (\_ xs -> [head xs, xs !! 1, xs !! 1, xs !! 3]))
    , ("assumption payloads may be referred to only once", records "assumes" (\xs -> take 3 xs ++ [xs !! 2] ++ drop 4 xs))
    , ("an assumption cannot use a specification payload kind", records "assumes" (\xs -> take 2 xs ++ ["0"] ++ drop 3 xs))
    , ("the data count must consume exactly the payload block", records "data" (\xs -> [head xs, show ((read (xs !! 1) :: Integer) + 1)]))
    , ("negative expression references are refused", change "IfExpr" (\_ xs -> [head xs, "-1", xs !! 2, xs !! 3]))
    , ("a blank line does not hide trailing input", input ++ "\nunknown-suffix\n")
    ]
  where
    rows = lines input
    (prefix, payload) = break (== "tersus-ast 1 mir") rows
    change tag edit = case break ((== tag) . head . words) (drop 1 payload) of
        (before, row : after) -> unlines (prefix ++ [head payload] ++ before ++ unwords (edit (length before) (words row)) : after)
        _ -> input
    records tag edit = unlines [if take (length tag + 1) row == tag ++ " " then unwords (edit (words row)) else row | row <- rows]

loweredRoundTrip :: Lowered -> TestResult
loweredRoundTrip original = case writeLowered original of
    Error e -> Just e
    Ok wire -> case readLowered wire of
        Error e -> Just e
        Ok actual -> testAssertEq (show actual) (show original) <> testAssertEq (writeLowered actual) (Ok wire)

currentMutationResult :: String -> String -> TestResult
currentMutationResult original changed =
    testAssertTrue (changed /= original)
        <> testAssertTrue (case readLowered original of Ok _ -> True; _ -> False)
        <> testAssertTrue (case readLowered changed of Error _ -> True; _ -> False)

testCurrentLoweredMetadataHost :: Test
testCurrentLoweredMetadataHost = TestList "current full Lowered metadata host"
    [ TestList "canonical mixed payloads" [testCase label (loweredRoundTrip value) | (label,value) <- currentLoweredFixtures]
    , testCase "validation specialization preserves the new program payloads" $
        let original = lowProgram (snd (last currentLoweredFixtures))
         in testAssertEq (show (monomorphizeForValidation original)) (show (Oracle.monomorphizeForValidation original))
    , TestList "strict payload mutations" [testCase label (currentMutationResult wire changed)
        | Ok wire <- [writeLowered (snd (head currentLoweredFixtures))], (label,changed) <- currentLoweredMutations wire]
    ]

testCurrentLoweredMetadataUsing :: IO Tool -> Test
testCurrentLoweredMetadataUsing getTool = TestList "current full Lowered native metadata"
    [ TestList "native canonical mixed payloads" [TestCase label (compareLowered value) | (label,value) <- currentLoweredFixtures]
    , TestList "native strict payload mutations" [TestCase label (rejects wire changed)
        | Ok wire <- [writeLowered (snd (head currentLoweredFixtures))], (label,changed) <- currentLoweredMutations wire]
    ]
  where
    compareLowered original = case writeLowered original of
        Error e -> pure (Just e)
        Ok input -> do
            tool <- getTool
            case tool of
                ToolNative exe -> do
                    (code,out,err) <- runWithInputFull exe ("pass mono\n" ++ input)
                    let expected = original{lowProgram = Oracle.monomorphize (lowProgram original)}
                    case (code,err,readLowered out,writeLowered expected) of
                        (ExitSuccess,"",Ok actual,Ok canonical) -> do
                            owned@(ownCode,ownOut,ownErr) <- runWithInputFull exe ("pass ownership\n" ++ writeProgramWithGhosts (ownershipInput (lowProgram actual)))
                            fused <- runWithInputFull exe ("pass mono-ownership\n" ++ input)
                            pure (testAssertEq (show actual) (show expected) <> testAssertEq out canonical
                                <> testAssertEq fused (ownCode,out ++ ownOut,ownErr)
                                <> case (owned,readProgram ownOut) of
                                    ((ExitSuccess,"1\n",errors),_) | not (null errors) -> Just "valid mixed metadata ownership was refused"
                                    ((ExitSuccess,_,""),Ok runtime) -> case restoreOwnership (lowProgram expected) runtime of
                                        Ok _ -> Nothing
                                        Error e -> Just e
                                    _ -> Just ("mixed metadata ownership failed: " ++ show (ownCode,take 200 ownOut,ownErr)))
                        _ -> pure (Just ("current Lowered native transport failed: " ++ show (code,take 200 out,err)))
                ToolFailed e -> pure (Just e)
                _ -> pure (Just "current full metadata requires a native emitter")
    rejects original changed = case currentMutationResult original changed of
        Just e -> pure (Just e)
        Nothing -> do
            tool <- getTool
            case tool of
                ToolNative exe -> do
                    mono@(code,out,err) <- runWithInputFull exe ("pass mono\n" ++ changed)
                    fused <- runWithInputFull exe ("pass mono-ownership\n" ++ changed)
                    pure (testAssertTrue (code == ExitSuccess && out == "1\n" && not (null err)) <> testAssertEq fused mono)
                ToolFailed e -> pure (Just e)
                _ -> pure (Just "current mutation controls require a native emitter")

emptyFunction :: Function
emptyFunction = Function "main" [] (Just TInt) (Map.singleton (Local 0) (LocalDecl TInt Nothing)) (Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (Use (Const (CInt 1)))] Return)) [] [] [] [] [] emptySpec

metadataProgram :: Program
metadataProgram = Program
    (Map.singleton "Plain" (StructDecl [("value", TInt)]))
    (Map.singleton "plain" emptyFunction{fnName = "plain", fnSpec = metadataSpec})
    emptyFunction{fnSpec = metadataSpec, fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Ghost (Map.singleton "value" (Const (CInt 7))) (GhostValidation (S.ProofAssert (S.CTerm (S.VBool True)))), Assign (Local 0) (Use (Const (CInt 1)))] Return)}
    (Map.singleton "Unused" (["T"], [("ghost", TBlock (TParam "T"))]))
    (Map.singleton "Plain" [S.ProofAssert (S.CTerm (S.VBool True))])
    Map.empty Map.empty Map.empty Map.empty Nothing
  where
    metadataSpec = emptySpec{specEnv = Map.singleton "builtin" (Const (CFn "plain")), specWrites = ["x"], specMutParams = ["x"], specFrom = ["x"]}

identityFunction :: Function
identityFunction = emptyFunction
    { fnName = "identity", fnParams = [Local 1], fnTypeParams = ["T"], fnReturns = Just (TParam "T")
    , fnLocals = Map.fromList [(Local 0, LocalDecl (TParam "T") (Just "result")), (Local 1, LocalDecl (TRef (TParam "T")) (Just "value"))]
    , fnBorrowed = [Local 1]
    , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (Use (Copy (Local 1)))] Return)
    }

genericProgram :: Program
genericProgram = metadataProgram
    { progFunctions = Map.insert "identity" identityFunction (progFunctions metadataProgram)
    , progMain = emptyFunction{fnBlocks = Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "identity")) [Const (CInt 123)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]}
    }

sizeProgram :: Integer -> Program
sizeProgram n = genericProgram
    { progFunctions = Map.singleton "sized" sized, progMain = main
    , progGenerics = Map.singleton "Packet" (["T", "n"], [("data", TArrayOf (TParam "T") (SizeParam "n")), ("value", TParam "T"), ("ghost", TBlock (TParam "T"))])
    , progTypes = Map.singleton "Packet<Int, n>" (StructDecl [("data", TArrayOf TInt (SizeParam "n")), ("value", TInt), ("ghost", TBlock TInt)])
    }
  where
    packet s = TNamed "Packet" [ArgType TInt, ArgSize s]
    sized = emptyFunction
        { fnName = "sized", fnParams = [Local 1, Local 2], fnSizeParams = ["n"], fnReturns = Just (packet (SizeParam "n"))
        , fnBorrowed = [Local 1, Local 2], fnMutBorrowed = [Local 2], fnFrom = [Local 1, Local 2]
        , fnLocals = Map.fromList [(Local 0, LocalDecl (packet (SizeParam "n")) (Just "result")), (Local 1, LocalDecl (TMutRef (packet (SizeParam "n"))) (Just "self")), (Local 2, LocalDecl TInt (Just "n"))]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (MakeData "Packet<Int, n>" [("data", Const (CArray [])), ("value", Copy (Local 2))]), AssignRef (Local 1) [RefField "Packet<Int, n>" "value"] (Use (Move (Local 2)))] (SwitchBool (Copy (Local 2)) (BlockId 0) (BlockId 0)))
        }
    main = emptyFunction{fnLocals = Map.singleton (Local 0) (LocalDecl (packet (SizeConst n)) Nothing), fnBlocks = Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "sized")) [Const (CData "Packet<Int, n>" []), Const (CInt n)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]}

dropProgram :: Program
dropProgram = genericProgram
    { progGenerics = Map.singleton "Holder" (["T"], [("value", TParam "T"), ("permission", TBlock (TParam "T"))])
    , progTypes = Map.singleton "Holder<Int>" (StructDecl [("value", TInt), ("permission", TBlock TInt)])
    , progFunctions = Map.fromList [("identity", identityFunction), ("<Holder as Drop>::drop", dropFn)]
    , progMain = emptyFunction{fnLocals = Map.insert (Local 1) (LocalDecl (TNamed "Holder" [ArgType TInt]) Nothing) (fnLocals emptyFunction)}
    }
  where
    dropFn = identityFunction{fnName = "<Holder as Drop>::drop", fnReturns = Nothing, fnBorrowed = [], fnLocals = Map.singleton (Local 1) (LocalDecl (TNamed "Holder" [ArgType (TParam "T")]) (Just "self")), fnBlocks = Map.singleton (BlockId 0) (BasicBlock [] Return)}

plainDropWithGeneric :: Program
plainDropWithGeneric = metadataProgram
    { progFunctions = Map.fromList [(fnName dropFn, dropFn), (fnName identityFunction, identityFunction)] }
  where
    dropFn = emptyFunction
        { fnName = "<Plain as Drop>::drop", fnParams = [Local 1], fnReturns = Nothing
        , fnLocals = Map.singleton (Local 1) (LocalDecl (TNamed "Plain" []) (Just "self"))
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [] Return)
        }

unicodeParameterProgram :: Program
unicodeParameterProgram = genericProgram
    { progGenerics = Map.singleton "Holder" (["É"], [("value", TParam "É")])
    , progTypes = Map.empty
    , progFunctions = Map.singleton "makeHolder" makeHolder
    , progMain = emptyFunction
        { fnReturns = Just (holder TInt), fnLocals = Map.singleton (Local 0) (LocalDecl (holder TInt) Nothing)
        , fnBlocks = Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "makeHolder")) [Const (CInt 7)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]
        }
    }
  where
    holder t = TNamed "Holder" [ArgType t]
    makeHolder = emptyFunction
        { fnName = "makeHolder", fnParams = [Local 1], fnTypeParams = ["É"], fnReturns = Just (holder (TParam "É"))
        , fnLocals = Map.fromList [(Local 0, LocalDecl (holder (TParam "É")) Nothing), (Local 1, LocalDecl (TParam "É") Nothing)]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (MakeData (instanceName "Holder" [ArgType (TParam "É")]) [("value", Copy (Local 1))])] Return)
        }

unicodeArgumentProgram :: String -> Program
unicodeArgumentProgram name = genericProgram
    { progGenerics = Map.singleton "G" (["T"], [("value", TParam "T")])
    , progTypes = Map.fromList [(name, StructDecl []), (gName, StructDecl [("value", named)])]
    , progFunctions = Map.singleton "identity" ownedIdentity
    , progMain = emptyFunction
        { fnReturns = Just gType, fnLocals = Map.fromList [(Local 0, LocalDecl gType Nothing), (Local 1, LocalDecl gType Nothing)]
        , fnBlocks = Map.fromList [(BlockId 0, BasicBlock [Assign (Local 1) (MakeData gName [("value", Const (CData name []))])] (Call (Const (CFn "identity")) [Copy (Local 1)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]
        }
    }
  where
    named = TNamed name []
    gType = TNamed "G" [ArgType named]
    gName = instanceName "G" [ArgType named]
    ownedIdentity = identityFunction{fnBorrowed = [], fnLocals = Map.fromList [(Local 0, LocalDecl (TParam "T") Nothing), (Local 1, LocalDecl (TParam "T") Nothing)]}

listSelectorProgram :: Program
listSelectorProgram = genericProgram
    { progGenerics = Map.singleton "List" (["T"], [("addr", TAddr (TParam "T")), ("len", TInt), ("cap", TInt)])
    , progTypes = Map.fromList
        [ (instanceName "List" [ArgType (TParam "T")], StructDecl [("addr", TAddr (TParam "T")), ("len", TInt), ("cap", TInt)])
        , ("List<Int>", StructDecl [("addr", TAddr TInt), ("len", TInt), ("cap", TInt)])
        ]
    , progFunctions = Map.singleton "<List as Drop>::drop" dropFn
    , progMain = emptyFunction{fnLocals = Map.insert (Local 1) (LocalDecl (TNamed "List" [ArgType TInt]) Nothing) (fnLocals emptyFunction)}
    }
  where
    symbolic = TNamed "List" [ArgType (TParam "T")]
    dropFn = emptyFunction
        { fnName = "<List as Drop>::drop", fnParams = [Local 1], fnTypeParams = ["T"], fnReturns = Nothing
        , fnLocals = Map.fromList [(Local 1, LocalDecl symbolic (Just "self")), (Local 2, LocalDecl (TAddr (TParam "T")) Nothing)]
        , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 2) (ReadField (Copy (Local 1)) (instanceName "List" [ArgType (TParam "T")]) "addr")] Return)
        }

nestedGenericArgument :: Type -> Program
nestedGenericArgument argument = genericProgram
    { progFunctions = Map.singleton "g" identityFunction
        { fnName = "g", fnBorrowed = []
        , fnLocals = Map.fromList [(Local 0, LocalDecl (TParam "T") Nothing), (Local 1, LocalDecl (TParam "T") Nothing)]
        }
    , progMain = emptyFunction
        { fnReturns = Just argument
        , fnLocals = Map.fromList [(Local 0, LocalDecl argument Nothing), (Local 1, LocalDecl argument Nothing)]
        , fnBlocks = Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "g")) [Copy (Local 1)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]
        }
    }

collidingTypeVariables :: Program
collidingTypeVariables = genericProgram
    { progFunctions = Map.singleton "g" ownedIdentity{fnName = "g"}
    , progMain = emptyFunction
        { fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl (TVar 0) Nothing), (Local 2, LocalDecl (TVar 1) Nothing), (Local 3, LocalDecl (TVar 1) Nothing), (Local 4, LocalDecl (TVar 0) Nothing)]
        , fnBlocks = Map.fromList
            [ (BlockId 0, BasicBlock [] (Call (Const (CFn "g")) [Copy (Local 2)] (Local 3) (BlockId 1)))
            , (BlockId 1, BasicBlock [] (Call (Const (CFn "g")) [Copy (Local 1)] (Local 4) (BlockId 2)))
            , (BlockId 2, BasicBlock [Assign (Local 0) (Use (Const (CInt 1)))] Return)
            ]
        }
    }
  where
    ownedIdentity = identityFunction{fnBorrowed = [], fnLocals = Map.fromList [(Local 0, LocalDecl (TParam "T") Nothing), (Local 1, LocalDecl (TParam "T") Nothing)]}

builtinMetadata :: Program -> Program
builtinMetadata p = p{progInvariants = Map.singleton "Plain" [S.ProofAssert payload]}
  where
    payload = S.CTerm (S.VFunct ["x"] [S.ProofAssert (S.CTerm (S.VBool True))] [S.ProofAssert (S.CTerm (S.VBool False))] (S.BuiltinFunct Plus) [S.CTerm (S.VInt (10 ^ (30 :: Int)))])

packLoopMetadata :: Bool -> Program -> Program
packLoopMetadata invariant program = program{progInvariants = Map.singleton "Plain" [S.ProofAssert payload]}
  where
    checks = if invariant then [S.ProofAssert (S.CTerm (S.VBool True))] else []
    loop = S.PackLoop "i" "a" "args" (S.Val (S.VInt 0)) (S.Val (S.VInt 2)) False checks [S.Return (S.Val (S.VInt 0))]
    payload = S.CTerm (S.VFunct [] [] [] (S.NativeFunct (Signature [] TInt [] [] [] []) Nothing [loop]) [])

legacyPackLoop :: IO TestResult
legacyPackLoop = case readLowered legacyPackInput of
    Error e -> pure (Just ("the current host rejected the legacy PackLoop record: " ++ e))
    Ok unit -> compareInput (lowProgram unit) legacyPackInput

-- Generated by the pre-invariant writer at 0496c37; removing a current reference leaves an orphan node.
legacyPackInput :: String
legacyPackInput = unlines
    [ "tersus-mir 3"
    , "struct \"Plain\" 0"
    , "invariant \"Plain\" 0"
    , "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
    , "spec requires 1 ensures 2 termination none writes 0 mutparams 0 from 0"
    , "env none 0"
    , "local 0 none int"
    , "block 0"
    , "assign 0 use const int 1"
    , "return"
    , "end"
    , "copies 0"
    , "linear 0"
    , "drops 0"
    , "stubs 0"
    , "declared 0"
    , "nested 0"
    , "assumes 0"
    , "data 54"
    , "tersus-ast 1 mir"
    , "StatementsEnd"
    , "StatementsEnd"
    , "Block 1"
    , "StatementsCons 2 0"
    , "StatementsEnd"
    , "Block 4"
    , "StatementsCons 5 3"
    , "StatementsEnd"
    , "NamesEnd"
    , "ValidationsEnd"
    , "ValidationsEnd"
    , "TypesEnd"
    , "Type int"
    , "NamesEnd"
    , "NamesEnd"
    , "NamesEnd"
    , "NamesEnd"
    , "Signature 11 12 13 14 15 16"
    , "NoTermination"
    , "StatementsEnd"
    , "NameEnd"
    , "NamePart \"i\" 20"
    , "NameEnd"
    , "NamePart \"a\" 22"
    , "NameEnd"
    , "NamePart \"args\" 24"
    , "NameEnd"
    , "NamePart \"0\" 26"
    , "VInt 27"
    , "Val 28"
    , "NameEnd"
    , "NamePart \"2\" 30"
    , "VInt 31"
    , "Val 32"
    , "StatementsEnd"
    , "NameEnd"
    , "NamePart \"0\" 35"
    , "VInt 36"
    , "Val 37"
    , "Return 38"
    , "StatementsCons 39 34"
    , "PackLoop 21 23 25 29 33 false 40"
    , "StatementsCons 41 19"
    , "NativeFunct 17 18 42"
    , "ProofsEnd"
    , "VFunct 8 9 10 43 44"
    , "CTerm 45"
    , "ProofAssert 46"
    , "ValidationStatement 47"
    , "StatementsCons 48 7"
    , "Block 49"
    , "StatementsCons 50 6"
    , "root 51"
    ]

negativePackLoop :: IO TestResult
negativePackLoop = case writeLowered (unitOf (packLoopMetadata False metadataProgram)) of
    Error e -> pure (Just e)
    Ok original ->
        let isLoop fields = length fields == 9 && head fields == "PackLoop"
            rows = [(isLoop (words line), line) | line <- lines original]
            broken = unlines [if changed then unwords (take 7 (words line) ++ ["-1"] ++ drop 8 (words line)) else line | (changed, line) <- rows]
         in if length (filter fst rows) /= 1 || broken == original
            then pure (Just "the negative PackLoop control did not change exactly one invariant reference")
            else case readLowered broken of
                Ok _ -> pure (Just "the current host admitted a negative PackLoop invariant reference")
                Error _ -> refuses ("pass mono\n" ++ broken)

monoFixtures :: [(String, Program)]
monoFixtures =
    [ ("no generic retains complete metadata", metadataProgram)
    , ("no generic retains pack-loop invariant metadata", packLoopMetadata True metadataProgram)
    , ("generic retains pack-loop invariant metadata", packLoopMetadata True genericProgram)
    , ("no generic retains empty pack-loop invariant metadata", packLoopMetadata False metadataProgram)
    , ("monomorphic Drop is deduplicated with an unrelated generic", plainDropWithGeneric)
    , ("Unicode uppercase type parameters complete declarations", unicodeParameterProgram)
    , ("nested Unicode lowercase types keep canonical backticks", unicodeArgumentProgram "α")
    , ("native list helper keeps canonical symbolic declaration and selector keys", listSelectorProgram)
    , ("named List renders an unresolved type as Pretty does", nestedGenericArgument (TNamed "List" [ArgType (TVar 1)]))
    , ("named Box renders an unresolved type as Pretty does", nestedGenericArgument (TNamed "Box" [ArgType (TVar 1)]))
    , ("named List renders a parameter without instance quoting", nestedGenericArgument (TNamed "List" [ArgType (TParam "B")]))
    , ("named Box retains nested forall in ordinary rendering", nestedGenericArgument (TNamed "Box" [ArgType (TForall [] ["B"] TInt)]))
    , ("structural instance keys win despite reverse discovery order", collidingTypeVariables)
    , ("nested Unicode alphanumeric types keep canonical backticks", unicodeArgumentProgram "α1")
    , ("generic type call strips only function proof metadata", genericProgram)
    , ("arbitrary precision proof values and builtin metadata survive fast path", builtinMetadata metadataProgram)
    , ("arbitrary precision proof values and builtin metadata survive instantiation", builtinMetadata genericProgram)
    , ("sizes substitute locals, operand constants, field selectors and provenance", sizeProgram 3)
    , ("arbitrary precision sizes and constants survive", sizeProgram (10 ^ (30 :: Int)))
    , ("implicit generic Drop and erased permission fields", dropProgram)
    , ("unknown type arguments default to Int", genericProgram{progMain = emptyFunction{fnReturns = Nothing, fnLocals = Map.empty, fnBlocks = Map.singleton (BlockId 0) (BasicBlock [] (Call (Const (CFn "identity")) [Const (CList [])] (Local 0) (BlockId 0)))}})
    , ("self-recursive reachable instances are deduplicated", genericProgram{progFunctions = Map.singleton "identity" identityFunction{fnBorrowed = [], fnLocals = Map.fromList [(Local 0, LocalDecl (TParam "T") Nothing), (Local 1, LocalDecl (TParam "T") Nothing)], fnBlocks = Map.singleton (BlockId 0) (BasicBlock [] (Call (Const (CFn "identity")) [Copy (Local 1)] (Local 0) (BlockId 0)))}})
    , ("unreachable generic functions are absent", genericProgram{progMain = emptyFunction})
    , ("a dynamic size argument leaves the call unchanged", (sizeProgram 3){progMain = (progMain (sizeProgram 3)){fnLocals = Map.insert (Local 2) (LocalDecl TInt Nothing) (fnLocals (progMain (sizeProgram 3))), fnBlocks = Map.singleton (BlockId 0) (BasicBlock [] (Call (Const (CFn "sized")) [Const (CData "Packet<Int, n>" []), Copy (Local 2)] (Local 0) (BlockId 0)))}})
    ]
