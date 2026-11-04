{-# LANGUAGE PatternSynonyms #-}

module TestMirEmit (testMirEmit, testMirEmitPrograms) where

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import System.Exit (ExitCode (..))

import Cli (World (..), noWorld, runProgramIn)
import Compile (lowerSource)
import MirOwnership (insertOwnership)
import qualified MirEval as Eval
import Types (Type (..), pattern TList, pattern TBox)
import Mir
import MirData (readProgram, writeProgram)
import TestHarness
import TestMirReader (withProgram)
import TestNative (nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The lowering to LLVM IR written in Tersus (examples/mir/emit/emit.tersus, step 31 of the roadmap and STEP31.md) is the compiler's emitter. It is given the MIR as data,
-- and writes all of the IR with no argument, the declarations, the descriptors of the types and the entry point for `outline`, and the code of each function for
-- `bodies`. What it writes has to build and run as the program does, which TestNative checks for every example and program by building the IR; here every mode
-- is run on every one of them, and the data of a program and the data of the program read back from it have to make the same IR. A smaller input is run by the
-- interpreter.
-- The emitter is built once (it needs clang, and the tests pass without it).
testMirEmit :: Test
testMirEmit =
    TestList
        "testMirEmit"
        [ TestCase "the four programs share the reader module of the mir package" sharedReader
        , TestCase "field offsets borrow the type table instead of cloning it" borrowedTypeTable
        , TestCase "hot emitter operations move Gen instead of cloning its history" threadedGen
        , TestCase "type closure preserves ordered duplicate and dependency traversal" orderedTypeClosure
        , TestCase "the IR of a loop, interpreted" (readFile "examples/loops.tersus" >>= interpretedIr)
        , TestParallel
            "every example, natively"
            [TestCase path (readFile path >>= nativeCheck path) | path <- nativeExamples]
        , TestCase "what is not the MIR is refused" refusal
        ]

-- The validated programs of the sweep as a group of their own, so the suite's group processes balance: this sweep
-- and testMirVerify's were the longest groups, and a group is a process.
testMirEmitPrograms :: Test
testMirEmitPrograms =
    TestParallel
        "testMirEmitPrograms"
        [TestCase name (nativeCheck name source) | (name, source) <- validatedPrograms]

sharedReader :: IO TestResult
sharedReader = do
    codec <- readFile "examples/data/codec/codec.tersus"
    reader <- readFile "examples/mir/reader/reader.tersus"
    programs <- mapM readFile ["examples/mir/mir_reader/mir_reader.tersus", "examples/mir/emit/emit.tersus", "examples/mir/mir_verify/mir_verify.tersus", "examples/mir/mir_erase/mir_erase.tersus"]
    pure $
        if "struct Token" `isInfixOf` codec
            && "struct Field" `isInfixOf` reader
            && all ("import data::codec::codec" `isInfixOf`) (reader : programs)
            && all ("import mir::reader::reader" `isInfixOf`) programs
            && not (any ("struct Token" `isInfixOf`) (reader : programs))
            then Nothing
            else Just "a MIR program does not use the shared reader and codec, or contains its own Token declaration"

-- The emitter of examples/mir/emit/emit.tersus, compiled once: the three interpreted cases each run it for a part of the IR, and its
-- validation is the most expensive thing in this group.
emitterProgram :: IO (Result Program String)
emitterProgram = programFromFile "examples/mir/emit/emit.tersus"

runEmitter :: World -> Result Program String -> Result ((String, String), [(FilePath, String)]) String
runEmitter world compiled = case compiled of
    Error e -> Error e
    Ok program -> runProgramIn world program

borrowedTypeTable :: IO TestResult
borrowedTypeTable = do
    loaded <- validatedFromFile "examples/mir/emit/emit.tersus"
    pure $ case loaded of
        Error e -> Just e
        Ok program -> case Map.lookup "fieldOffset" (progFunctions (insertOwnership program)) of
            Nothing -> Just "the emitter has no fieldOffset function"
            Just fn ->
                let table = TList (TNamed "mir$reader$reader$TypeDecl" [])
                    copied = [dest | block <- Map.elems (fnBlocks fn), Assign dest (ReadField _ "Ctx" "types") <- blockStatements block, Just decl <- [Map.lookup dest (fnLocals fn)], localType decl == table]
                 in if null copied then Nothing else Just ("fieldOffset clones the type table into " ++ show copied)

threadedGen :: IO TestResult
threadedGen = do
    loaded <- validatedFromFile "examples/mir/emit/emit.tersus"
    pure $ case loaded of
        Error e -> Just e
        Ok program ->
            let owned = insertOwnership program
                functions = [fn | (name, fn) <- Map.toList (progFunctions owned), fnReturns fn == Just (TNamed "Gen" []), name `notElem` ["<Gen as Clone>::clone", "Clone for Gen::clone"]]
                snapshots = [fnName fn | fn <- functions, block <- Map.elems (fnBlocks fn), Call (Const (CFn "<Gen as Clone>::clone")) _ _ _ <- [blockTerminator block]]
                copies = [fnName fn | fn <- functions, block <- Map.elems (fnBlocks fn), Assign dest CopyOf{} <- blockStatements block, Just decl <- [Map.lookup dest (fnLocals fn)], localType decl == TNamed "Gen" []]
             in if null functions then Just "the emitter has no Gen operations" else
                if null snapshots && null copies then Nothing else Just ("hot emitter operations clone Gen: " ++ show (snapshots ++ copies))

orderedTypeClosure :: IO TestResult
orderedTypeClosure = do
    loaded <- validatedFromFile "examples/mir/emit/emit.tersus"
    pure $ case loaded of
        Error e -> Just e
        Ok program -> firstFailure
            [ testAssertEq (Eval.runNamedFunction program "closeTypes" [Eval.MList declarations, Eval.MList roots]) (Ok (Just (Eval.MList expected)))
            | (declarations, roots, expected) <- cases
            ]
  where
    text s = Eval.MData "String" [("bytes", Eval.MList [Eval.MInt (toInteger (fromEnum c)) | c <- s])]
    named n = Eval.MData "data$codec$codec$Type::TNamed" [("name", text n), ("base", text n), ("argc", Eval.MInt 0), ("argTokens", Eval.MList [])]
    int = Eval.MData "data$codec$codec$Type::TInt" []
    byte = Eval.MData "data$codec$codec$Type::TByte" []
    bool = Eval.MData "data$codec$codec$Type::TBool" []
    field t = Eval.MData "mir$reader$reader$Field" [("name", text "value"), ("ty", t)]
    struct n t = Eval.MData "mir$reader$reader$TypeDecl::DStruct" [("name", text n), ("fields", Eval.MList [field t])]
    variant = Eval.MData "data$codec$codec$Type::TVariant" [("name", text "E::V")]
    enum = Eval.MData "mir$reader$reader$TypeDecl::DEnum" [("name", text "E"), ("variants", Eval.MList [Eval.MData "mir$reader$reader$Variant" [("name", text "E::V"), ("fields", Eval.MList [field bool])]])]
    node = named "Node"
    addr = Eval.MData "data$codec$codec$Type::TAddr" [("inner", node)]
    cases =
        [ ([], [bool, int, bool, int], [bool, int])
        , ([struct "A" int, struct "B" byte], [named "A", named "B", named "A"], [named "A", int, named "B", byte])
        , ([struct "A" int, struct "B" byte], [named "A", int, named "B", int], [named "A", int, named "B", byte])
        , ([enum], [variant, named "E", int, variant], [named "E", bool, int])
        , ([struct "Node" addr], [node, addr, node], [node, addr])
        ]
    firstFailure results = case [message | Just message <- results] of
        message : _ -> Just message
        [] -> Nothing

interpretedIr :: String -> IO TestResult
interpretedIr source = do
    emitter <- emitterProgram
    ownedResult <- ownedOnce source
    pure $ case ownedResult of
        Error e -> Just e
        Ok owned -> case mapResult fst (runEmitter noWorld{worldInput = writeProgram owned} emitter) of
            Error e -> Just e
            Ok (output, errors)
                | not (null errors) -> Just ("reported: " ++ errors)
                | "@tersus_main" `isInfixOf` output && "define" `isInfixOf` output -> Nothing
                | otherwise -> Just ("wrote\n" ++ take 2000 output)



-- Every mode writes the IR of a program, and the data of the program read back from the data makes the same IR
-- as the data. One case per program, so the sweep runs at the harness's parallelism instead of one program
-- after another inside a single case (withProgram builds the emitter executable once for the process). The data
-- comes from the harness's shared cache (mirDataOf): the groups between them compile these programs once.
nativeCheck :: String -> String -> IO TestResult
nativeCheck name source = withProgram "examples/mir/emit/emit.tersus" "emit" $ \exe -> do
    bad <- check exe (name, source)
    pure $ case bad of
        [] -> Nothing
        problems -> Just (unlines problems)
  where
    check exe (name, source) = do
        dataOf <- if "examples/mir/" `isPrefixOf` name then mirDataFromFile name else mirDataOf source
        case dataOf of
            Error e -> pure [name ++ ": " ++ e]
            Ok dataText -> do
                outline <- runExecutableBytes exe ["outline"] dataText
                bodies <- runExecutableBytes exe ["bodies"] dataText
                everything <- runExecutableBytes exe [] dataText
                roundTrip <- case readProgram dataText of
                    Error e -> pure ["the data does not read back: " ++ e]
                    Ok back -> do
                        again <- runExecutableBytes exe [] (writeProgram back)
                        pure $ case (everything, again) of
                            ((ExitSuccess, output, ""), (ExitSuccess, output', "")) | output == output' -> []
                            ((ExitSuccess, _, ""), (code, _, errors)) -> ["the IR of the program read back: exit " ++ show code ++ ", " ++ take 200 errors]
                            _ -> []
                let modeProblems =
                        [ name ++ ": the " ++ mode ++ ": exit " ++ show code ++ ", " ++ take 200 errors
                        | (mode, (code, _, errors)) <- [("outline", outline), ("bodies", bodies), ("IR", everything)]
                        , code /= ExitSuccess || not (null errors)
                        ]
                        ++ [name ++ ": the IR has no entry point" | (code, output, _) <- [everything], code == ExitSuccess, not ("@tersus_main" `isInfixOf` output)]
                pure (modeProblems ++ roundTrip)

refusal :: IO TestResult
refusal = withProgram "examples/mir/emit/emit.tersus" "emit" $ \exe -> do
    (_, output, errors) <- runExecutableBytes exe ["outline"] "return 1;\n"
    (_, output', errors') <- runExecutableBytes exe ["nonsense"] "tersus-mir 1\n"
    pure $
        if output == "1\n" && not (null errors) && output' == "1\n" && not (null errors')
            then Nothing
            else Just ("read as " ++ show output ++ " with " ++ show errors ++ ", and " ++ show output' ++ " with " ++ show errors')
