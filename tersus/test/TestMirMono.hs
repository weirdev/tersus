{-# LANGUAGE PatternSynonyms #-}
module TestMirMono (testMirMono, testMirMonoUsing) where

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (ExitCode (..))

import Compile (lowerSource)
import Mir
import MirData (readLowered, writeLowered)
import MirHousekeeping (Tool (..), monomorphizeWith, ownershipTool, toolProgram, emitterEntry, eraseGhosts, nativeProgram)
import MirMono (monomorphizeForValidation)
import qualified MirMonoOracle as Oracle
import Native (runWithInputFull)
import qualified Syntax as S
import TestHarness
import TestNative (nativeExamples, validatedPrograms, unvalidatedPrograms)
import Types (Arg (..), Size (..), Type (..), BuiltinFunct (..), instanceName)
import Utils

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

compareWire :: Program -> IO TestResult
compareWire original = case writeLowered (unitOf original) of
    Error e -> pure (Just e)
    Ok input -> do
        tool <- ownershipTool
        case tool of
            ToolNative exe -> do
                (code, out, err) <- runWithInputFull exe ("pass mono\n" ++ input)
                pure $ case (code, err, readLowered out) of
                    (ExitSuccess, "", Ok unit) ->
                        let expected = Oracle.monomorphize original
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

testMirMono :: Test
testMirMono = testMirMonoUsing lowerSource

testMirMonoUsing :: (Bool -> String -> Result Program String) -> Test
testMirMonoUsing lower = TestList "testMirMono"
    [ TestList "source corpus" [TestCase label (sourceMono lower source) | (label, source) <- validatedPrograms ++ unvalidatedPrograms]
    , TestList "examples" [TestCase path (readFile path >>= sourceMono lower) | path <- nativeExamples]
    , TestList "complete metadata and substitution" [TestCase label (compareWire p) | (label, p) <- monoFixtures]
    , TestList "validation adapter retains contracts and ghosts"
        [ testCase label (monoDifference (Oracle.monomorphizeForValidation p) (monomorphizeForValidation p)) | (label, p) <- monoFixtures ]
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
    , TestList "malformed transport" [TestCase label (refuses input) | (label, input) <- refusalFixtures]
    ]
  where
    dropped = Oracle.monomorphize dropProgram
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

emptyFunction :: Function
emptyFunction = Function "main" [] (Just TInt) (Map.singleton (Local 0) (LocalDecl TInt Nothing)) (Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (Use (Const (CInt 1)))] Return)) [] [] [] [] [] emptySpec

metadataProgram :: Program
metadataProgram = Program
    (Map.singleton "Plain" (StructDecl [("value", TInt)]))
    (Map.singleton "plain" emptyFunction{fnName = "plain", fnSpec = metadataSpec})
    emptyFunction{fnSpec = metadataSpec, fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Ghost (Map.singleton "value" (Const (CInt 7))) (GhostValidation (S.ProofAssert (S.CTerm (S.VBool True)))), Assign (Local 0) (Use (Const (CInt 1)))] Return)}
    (Map.singleton "Unused" (["T"], [("ghost", TBlock (TParam "T"))]))
    (Map.singleton "Plain" [S.ProofAssert (S.CTerm (S.VBool True))])
    Map.empty Map.empty
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

monoFixtures :: [(String, Program)]
monoFixtures =
    [ ("no generic retains complete metadata", metadataProgram)
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
