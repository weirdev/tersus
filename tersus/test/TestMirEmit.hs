{-# LANGUAGE PatternSynonyms #-}

module TestMirEmit (testMirEmit, testMirEmitPrograms) where

import Control.Concurrent.MVar (MVar, newMVar)
import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.IO.Unsafe (unsafePerformIO)

import Bootstrap (compilerSnapshotHash, llvmOfOwned)
import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import qualified Modules
import Native (buildExecutable, cachedProgram)
import qualified TersusParser

import Cli (World (..), noWorld, runProgramIn)
import Compile (lowerSource)
import MirHousekeeping (insertOwnership)
import qualified MirEval as Eval
import Types (Type (..), pattern TList, pattern TBox)
import Mir
import MirData (readProgram, writeProgram)
import TestHarness
import TestMirReader (programExecutable)
import TestNative (clangAvailable, nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The lowering to LLVM IR written in Tersus (examples/mir/emit/emit.tersus, step 31 of the roadmap and STEP31.md) is the compiler's emitter. It is given the MIR as data,
-- and writes all of the IR with no argument, the declarations, the descriptors of the types and the entry point for `outline`, and the code of each function for
-- `bodies`. What it writes has to build and run as the program does, which TestNative checks for every example and program by building the IR; here the full
-- mode is run on every one of them (outline/bodies only on a representative subset), and the data of a program and the data of the program read back from it have to make the same IR. A smaller input is run by the
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
        , TestCase "only outline invokes outline, once, without changing mode outputs" outlineDispatch
        , TestCase "mode errors preserve parse-first diagnostics and returned values" refusal
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
    writer <- readFile "examples/mir/writer/writer.tersus"
    programs <- mapM readFile ["examples/mir/mir_reader/mir_reader.tersus", "examples/mir/emit/emit.tersus", "examples/mir/mir_verify/mir_verify.tersus", "examples/mir/mir_erase/mir_erase.tersus", "examples/mir/ownership/ownership.tersus"]
    pure $
        if "struct Token" `isInfixOf` codec
            && "struct Field" `isInfixOf` reader
            && "import data::codec::codec" `isInfixOf` reader
            && "import data::codec::codec" `isInfixOf` writer
            && all ("import mir::reader::reader" `isInfixOf`) programs
            && not (any ("struct Token" `isInfixOf`) (reader : writer : programs))
            then Nothing
            else Just "a MIR program does not use the shared reader and codec, or contains its own Token declaration"

-- The emitter of examples/mir/emit/emit.tersus, compiled once: the three interpreted cases each run it for a part of the IR, and its
-- validation is the most expensive thing in this group.
emitterProgram :: IO (Result Program String)
emitterProgram = bootstrapFromFile "examples/mir/emit/emit.tersus"

runEmitter :: World -> Result Program String -> Result ((String, String), [(FilePath, String)]) String
runEmitter world compiled = case compiled of
    Error e -> Error e
    Ok program -> runProgramIn world program

-- The emitter linked and owned, made once in a process for the cases that look at its owned MIR
{-# NOINLINE ownedEmitter #-}
ownedEmitter :: Result Program String
ownedEmitter = unsafePerformIO (linkedFromFile "examples/mir/emit/emit.tersus") `bindResult` insertOwnership

-- The emitter executable (TestMirReader.programExecutable, kept on disk for the run), looked up once in a process: the
-- cases of a sweep would otherwise each hash its package again (TestHarness.memoizedTestExecutable keeps no failed build
-- and rebuilds an executable that is gone)
{-# NOINLINE emitterExecutable #-}
emitterExecutable :: MVar (Maybe FilePath)
emitterExecutable = unsafePerformIO (newMVar Nothing)

withEmitter :: (FilePath -> IO TestResult) -> IO TestResult
withEmitter use = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else do
            built <- memoizedTestExecutable emitterExecutable (programExecutable "examples/mir/emit/emit.tersus" "emit")
            case built of
                Error e -> pure (Just e)
                Ok exe -> use exe

borrowedTypeTable :: IO TestResult
borrowedTypeTable = do
    pure $ case ownedEmitter of
        Error e -> Just e
        Ok program -> case Map.lookup "fieldOffset" (progFunctions program) of
            Nothing -> Just "the emitter has no fieldOffset function"
            Just fn ->
                let table = TList (TNamed "mir$reader$reader$TypeDecl" [])
                    copied = [dest | block <- Map.elems (fnBlocks fn), Assign dest (ReadField _ "Ctx" "types") <- blockStatements block, Just decl <- [Map.lookup dest (fnLocals fn)], localType decl == table]
                 in if null copied then Nothing else Just ("fieldOffset clones the type table into " ++ show copied)

threadedGen :: IO TestResult
threadedGen = do
    pure $ case ownedEmitter of
        Error e -> Just e
        Ok owned ->
            let functions = [fn | (name, fn) <- Map.toList (progFunctions owned), fnReturns fn == Just (TNamed "Gen" []), name `notElem` ["<Gen as Clone>::clone", "Clone for Gen::clone"]]
                snapshots = [fnName fn | fn <- functions, block <- Map.elems (fnBlocks fn), Call (Const (CFn "<Gen as Clone>::clone")) _ _ _ <- [blockTerminator block]]
                copies = [fnName fn | fn <- functions, block <- Map.elems (fnBlocks fn), Assign dest CopyOf{} <- blockStatements block, Just decl <- [Map.lookup dest (fnLocals fn)], localType decl == TNamed "Gen" []]
             in if null functions then Just "the emitter has no Gen operations" else
                if null snapshots && null copies then Nothing else Just ("hot emitter operations clone Gen: " ++ show (snapshots ++ copies))

orderedTypeClosure :: IO TestResult
orderedTypeClosure = do
    loaded <- linkedFromFile "examples/mir/emit/emit.tersus"
    pure $ case loaded of
        Error e -> Just e
        Ok program -> firstTypeClosureProblem
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
    firstTypeClosureProblem results = case [message | Just message <- results] of
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



-- The full mode writes the IR of a program, and the data of the program read back from the data makes the same IR
-- as the data. One case per program, so the sweep runs at the harness's parallelism instead of one program
-- after another inside a single case (withProgram builds the emitter executable once for the process). The data
-- comes from the harness's shared cache (mirDataOf): the groups between them compile these programs once.
-- The outline/bodies modes are run only on a small representative subset: bodies is a distinct lenient path
-- in emit.tersus, so it still needs coverage, but running every mode on every program multiplies the sweep cost.
emitModeSubset :: [String]
emitModeSubset = ["examples/arithmetic.tersus", "examples/loops.tersus", "expression"]

nativeCheck :: String -> String -> IO TestResult
nativeCheck name source = withEmitter $ \exe -> do
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
                (outline, bodies) <-
                    if name `elem` emitModeSubset
                        then do
                            o <- runExecutableBytes exe ["outline"] dataText
                            b <- runExecutableBytes exe ["bodies"] dataText
                            pure (o, b)
                        else pure ((ExitSuccess, "", ""), (ExitSuccess, "", ""))
                everything <- runExecutableBytes exe [] dataText
                explicit <- if name `elem` emitModeSubset
                    then runExecutableBytes exe ["ir"] dataText
                    else pure everything
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
                pure (modeProblems ++ roundTrip ++ [name ++ ": default and explicit ir differ" | everything /= explicit])

outlineDispatch :: IO TestResult
outlineDispatch = withEmitter $ \exe -> do
    files <- Modules.snapshotFromFilesystem path
    loaded <- ownedFromFiles path files
    input <- mirDataOf "fn double(n: Int) -> Int { return n + n; }; return double(3);"
    backend <- lookupEnv "TERSUS_PARSER"
    parser <- TersusParser.parserKey
    case (loaded, input, parser) of
        (Error e, _, _) -> pure (Just e)
        (_, Error e, _) -> pure (Just e)
        (_, _, Error e) -> pure (Just e)
        (Ok program, Ok text, Ok identity) -> case Map.lookup "outline" (progFunctions program) of
            Nothing -> pure (Just "the emitter has no outline function")
            Just fn -> case Map.lookup (BlockId 0) (fnBlocks fn) of
                Nothing -> pure (Just "outline has no entry block")
                Just entry -> do
                    let marker = Local (1 + maximum [n | Local n <- Map.keys (fnLocals fn)])
                        marked = fn
                            { fnLocals = Map.insert marker (LocalDecl TInt Nothing) (fnLocals fn)
                            , fnBlocks = Map.insert (BlockId 0)
                                entry{blockStatements = Assign marker (ListOp WriteByte [Const (CInt 33)]) : blockStatements entry}
                                (fnBlocks fn)
                            }
                        instrumented = program{progFunctions = Map.insert "outline" marked (progFunctions program)}
                        key = fingerprint [packageCacheInput path files, writeProgram instrumented, show backend, compilerSnapshotHash, identity, runtimeSource]
                        build output = do
                            ir <- llvmOfOwned instrumented
                            case ir of
                                Error e -> pure (Error e)
                                Ok outlineProbeIr -> buildExecutable output outlineProbeIr
                    built <- cachedProgram "test-emit-outline-call" key "the outline call fixture" build
                    case built of
                        Error e -> pure (Just e)
                        Ok markedExe -> do
                            failures <- mapM (checkMode exe markedExe text) [[], ["ir"], ["outline"], ["bodies"]]
                            pure (firstFailure failures)
  where
    path = "examples/mir/emit/emit.tersus"
    checkMode exe markedExe text args = do
        original@(code, output, errors) <- runExecutableBytes exe args text
        observed <- runExecutableBytes markedExe args text
        let prefix = if args == ["outline"] then "!" else ""
            full = null args || args == ["ir"]
            shape = if args == ["bodies"]
                then "; function 0\n" `isPrefixOf` output && not ("define i32 @main" `isInfixOf` output)
                else "define i32 @main" `isInfixOf` output
                    && ("define internal i64 @\"fn.double\"" `isInfixOf` output) == full
                    && ("define internal { i64, i1 } @tersus_main" `isInfixOf` output) == full
        pure $ firstFailure
            [ if code == ExitSuccess && null errors && shape then Nothing else Just ("wrong " ++ show args ++ " output: " ++ show original)
            , if observed == (ExitSuccess, prefix ++ output, "") then Nothing
                else Just ("outline calls in " ++ show args ++ ": " ++ show (fmapOutput observed))
            ]
    fmapOutput (code, output, errors) = (code, take 300 output, errors)

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [message | Just message <- results] of
    message : _ -> Just message
    [] -> Nothing

refusal :: IO TestResult
refusal = withEmitter $ \exe -> do
    owned <- ownedOnce "return 1;"
    case owned of
        Error e -> pure (Just e)
        Ok program -> do
            let valid = writeProgram program
                main = progMain program
                unsupported = writeProgram program{progMain = main
                    { fnReturns = Just (TParam "T")
                    , fnLocals = Map.adjust (\decl -> decl{localType = TParam "T"}) (Local 0) (fnLocals main)
                    }}
                modes = [[], ["ir"], ["outline"], ["bodies"], ["nonsense"]]
                cases = [(args, text, message) | args <- modes, (text, message) <-
                    [("return 1;\n", "the input is not the MIR as data\n")
                    , ("tersus-mir 1\n", "the input is not the MIR as data\n")
                    , ("tersus-mir 1\nstruct \"P 0\n", "the input is not the MIR as data: a bad name\n")]]
            invalidMode <- runExecutableBytes exe ["nonsense"] valid
            parseFailures <- mapM (\(args, text, message) -> do
                actual <- runExecutableBytes exe args text
                pure (testAssertEq actual (ExitSuccess, "1\n", message))) cases
            defaultError <- runExecutableBytes exe [] unsupported
            irError <- runExecutableBytes exe ["ir"] unsupported
            outlineError <- runExecutableBytes exe ["outline"] unsupported
            pure $ firstFailure
                ( [ testAssertEq invalidMode (ExitSuccess, "1\n", "the first argument is ir, outline or bodies\n")
                  , testAssertEq defaultError irError
                  , testAssertEq defaultError (ExitSuccess, "1\n", "In " ++ fnName main ++ ": Native code does not support T yet\n")
                  , testAssertEq outlineError (ExitSuccess, "1\n", "Native code does not support T yet\n")
                  ] ++ parseFailures )
