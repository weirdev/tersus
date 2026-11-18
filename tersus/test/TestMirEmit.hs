{-# LANGUAGE PatternSynonyms #-}

module TestMirEmit (testMirEmit, testMirEmitPrograms, testMirEmitRecords) where

import Control.Concurrent.MVar (MVar, newMVar)
import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.IO.Unsafe (unsafePerformIO)

import Bootstrap (compilerSnapshotHash, emitWith, llvmOfOwned)
import LlvmRuntime (runtimeSource)
import qualified Modules
import Native (buildExecutable, cachedProgram)
import qualified TersusParser

import Cli (World (..), noWorld, runProgramIn)
import Compile (lowerSource)
import MirHousekeeping (insertOwnership)
import qualified MirEval as Eval
import Types (OwnershipFacts (..), Type (..))
import TestStorage (pattern TList, pattern TBox)
import Mir
import MirData (readProgram, writeOwnedProgram, writeProgram)
import MirMono (monomorphize)
import TestHarness
import TestMirReader (programExecutable)
import TestNative (clangAvailable, nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The lowering to LLVM IR written in Tersus (lib/mir/emit/emit.tersus, step 31 of the roadmap and STEP31.md) is the compiler's emitter. It is given the MIR as data,
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
        , TestCase "an emitter that refuses gives its reason, not IR" refusedEmit
        , TestCase "llvm, build and run fail with the emitter's reason" refusedIr
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
    codec <- readFile "lib/data/codec/codec.tersus"
    reader <- readFile "lib/mir/reader/reader.tersus"
    writer <- readFile "lib/mir/writer/writer.tersus"
    programs <- mapM readFile ["lib/mir/mir_reader/mir_reader.tersus", "lib/mir/emit/emit.tersus", "lib/mir/mir_verify/mir_verify.tersus", "lib/mir/mir_erase/mir_erase.tersus", "lib/mir/ownership/ownership.tersus"]
    pure $
        if "struct Token" `isInfixOf` codec
            && "struct Field" `isInfixOf` reader
            && "import data::codec::codec" `isInfixOf` reader
            && "import data::codec::codec" `isInfixOf` writer
            && all ("import mir::reader::reader" `isInfixOf`) programs
            && not (any ("struct Token" `isInfixOf`) (reader : writer : programs))
            then Nothing
            else Just "a MIR program does not use the shared reader and codec, or contains its own Token declaration"

-- The emitter of lib/mir/emit/emit.tersus, compiled once: the three interpreted cases each run it for a part of the IR, and its
-- validation is the most expensive thing in this group.
emitterProgram :: IO (Result Program String)
emitterProgram = bootstrapFromFile "lib/mir/emit/emit.tersus"

runEmitter :: World -> Result Program String -> Result ((String, String), [(FilePath, String)]) String
runEmitter world compiled = case compiled of
    Error e -> Error e
    Ok program -> runProgramIn world program

-- The emitter linked and owned, made once in a process for the cases that look at its owned MIR
{-# NOINLINE ownedEmitter #-}
ownedEmitter :: Result Program String
ownedEmitter = unsafePerformIO (linkedFromFile "lib/mir/emit/emit.tersus") `bindResult` insertOwnership

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
            built <- memoizedTestExecutable emitterExecutable (programExecutable "lib/mir/emit/emit.tersus" "emit")
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
    loaded <- linkedFromFile "lib/mir/emit/emit.tersus"
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

testMirEmitRecords :: Test
testMirEmitRecords = TestList "testMirEmitRecords" checkedRecords

-- The MIR the host gives the emitter may say each type's checked ownership facts and which declarations native storage
-- is (MIR.md, "Ownership and storage"); then the facts, not the spelling of a function, say what drops a value
checkedRecords :: [Test]
checkedRecords =
    [ TestCase "the checked facts give the IR the canonical drop the program records" $ withRecordData $ \exe text -> do
        checked <- runExecutableBytes exe [] (withRecords (rows text) text)
        pure (emitted checked <> testAssertTrue (defines "<V as std$core$ownership$Drop>::drop" checked) <> testAssertTrue (calls "<V as std$core$ownership$Drop>::drop" checked))
    , TestCase "the checked drop function is called whatever its name" $ withRecordData $ \exe text -> do
        let renamed = replace "\"<V as std$core$ownership$Drop>::drop\"" "\"app$V$release\"" text
        checked <- runExecutableBytes exe [] (withRecords (rows renamed) renamed)
        unchecked <- runExecutableBytes exe [] renamed
        pure (emitted checked <> testAssertTrue (calls "app$V$release" checked) <> testAssertTrue (not (calls "app$V$release" unchecked)))
    , TestCase "a checked program without a type's row is refused" $ withRecordData $ \exe text -> do
        refused <- runExecutableBytes exe [] (withRecords [row | row <- rows text, not ("owned \"V\"" `isPrefixOf` row)] text)
        pure (testAssertEq refused (ExitSuccess, "1\n", "the input is not the MIR as data\n"))
    , TestCase "a checked drop that names no function of the program is refused" $ withRecordData $ \exe text -> do
        refused <- runExecutableBytes exe [] (withRecords (rows (replace "\"<V as std$core$ownership$Drop>::drop\"" "\"absent\"" text)) text)
        pure (testAssertEq refused (ExitSuccess, "1\n", "the input is not the MIR as data\n"))
    , TestCase "storage declarations are those the storage record names" $ withEmitter $ \exe -> do
        dataOf <- mirDataOf "xs = [1, 2]; ys = push(xs, 3); return size(ys);"
        case dataOf of
            Error e -> pure (Just e)
            Ok text -> do
                given <- runExecutableBytes exe [] text
                let renamed = replace stdList "app$Seq" text
                checked <- runExecutableBytes exe [] renamed
                unnamed <- runExecutableBytes exe [] (withoutStorage renamed)
                let back (code, out, err) = (code, replace "app$Seq" stdList out, err)
                pure (testAssertTrue (("storage " ++ quoted stdList) `isInfixOf` text) <> emitted given <> testAssertEq (back checked) given <> testAssertTrue (back unnamed /= given))
    , TestCase "an instance without facts whose declaration is only Copy is refused before the ownership pass" $ withFacts $ \program facts ->
        let changed = program{progOwnership = Just (Map.delete "W<Int>" (Map.insert "W" (OwnershipFacts (Just "std$core$ownership$Copy") Nothing Nothing Nothing) facts))}
         in testAssertEq (uncoveredInstances (monomorphize changed)) ["W<Int>"]
                <> refusedWith "Type error: W<Int> has no checked ownership facts, and its declaration's facts may not apply to it" (insertOwnership changed)
    , TestCase "a declared type without facts is refused by the owned MIR's writer" $ withFacts $ \program facts ->
        let changed = program{progOwnership = Just (Map.delete "P" facts)}
         in refusedWith "Type error: P has no checked ownership facts" (writeOwnedProgram (monomorphize changed))
                <> refusedWith "Type error: P has no checked ownership facts" (insertOwnership changed)
    , TestCase "a checked Clone whose function the program does not have is refused, not written as none" $ withFacts $ \program facts ->
        let changed = program{progOwnership = Just (Map.adjust (\f -> f{ownershipClone = Just ("std$core$ownership$Clone", "absent")}) "P" facts)}
         in refusedWith "Type error: the checked Clone of P is absent, which the program does not have" (writeOwnedProgram (monomorphize changed))
                <> refusedWith "Type error: the checked Clone of P is absent, which the program does not have" (insertOwnership changed)
    , TestCase "a storage list of one address field is refused as it is read" $ storageRefusal
        (replace "struct \"app$Seq<Int>\" 3 \"addr\" addr int \"len\" int \"cap\" int" "struct \"app$Seq<Int>\" 1 \"addr\" addr int")
    , TestCase "a storage list whose length is not an Int is refused as it is read" $ storageRefusal
        (replace "\"len\" int \"cap\" int" "\"len\" byte \"cap\" int")
    , TestCase "a storage list without its room, which a clone writes, is refused as it is read" $ storageRefusal
        (replace "struct \"app$Seq<Int>\" 3 \"addr\" addr int \"len\" int \"cap\" int" "struct \"app$Seq<Int>\" 2 \"addr\" addr int \"len\" int")
    ]
  where
    source = "struct V { addr: Addr<Int>, n: Int, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = n; affirm count(blk) = 0; affirm n >= 0; }]; impl V { fn new(n: Int) -> Self [{ affirm n >= 0; }] [{ }] { (a, b) = Addr::alloc(n); return Self { addr: a, n: n, blk: b }; }; }; impl Drop for V { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; v = V::new(3); return v.n;"
    -- (a validated program whose declared P has a checked Clone and whose W<Int> is an instance, and its facts)
    withFacts use = do
        validated <- validatedOnce "struct P { a: Int };\nimpl Clone for P { };\nstruct W<T> { v: T };\np = P { a: 1 };\nq = clone(p);\nw = W<Int> { v: q.a };\nreturn w.v;"
        pure $ case validated of
            Error e -> Just e
            Ok program -> case progOwnership program of
                Just facts | Map.member "P" facts && Map.member "W<Int>" facts -> use program facts
                other -> Just ("the program does not have the facts of P and W<Int>: " ++ take 300 (show other))
    refusedWith needle result = case result of
        Error e | needle `isInfixOf` e -> Nothing
        Error e -> Just ("refused without " ++ needle ++ ": " ++ take 300 e)
        Ok _ -> Just ("not refused: " ++ needle)
    withRecordData use = withEmitter $ \exe -> do
        dataOf <- mirDataOf source
        case dataOf of
            Error e -> pure (Just e)
            Ok text -> use exe (withoutStorage text)
    -- (the data of a program with a list, its List renamed and given as storage, then the declaration made wrong)
    storageRefusal broken = withEmitter $ \exe -> do
        dataOf <- mirDataOf "xs = [1, 2]; ys = push(xs, 3); return size(ys);"
        case dataOf of
            Error e -> pure (Just e)
            Ok text -> do
                let renamed = replace stdList "app$Seq" text
                    bad = broken renamed
                refused <- runExecutableBytes exe [] bad
                pure (testAssertTrue (bad /= renamed)
                    <> testAssertEq refused (ExitSuccess, "1\n", "the input is not the MIR as data: the storage list app$Seq<Int> does not have its length and room as Ints after its address\n"))
    emitted (code, out, err) = testAssertEq (code, err) (ExitSuccess, "") <> testAssertTrue ("@tersus_main" `isInfixOf` out)
    -- (the drop function of a type calls the type's drop on the value it frees)
    calls name (_, out, _) = ("call i64 @\"fn." ++ name ++ "\"(ptr %slot)") `isInfixOf` out
    defines name (_, out, _) = any (\l -> "define " `isPrefixOf` l && ("@\"fn." ++ name ++ "\"(") `isInfixOf` l) (lines out)
    -- (a row for each declared type: its drop and its clone when the program has the conventional functions of them)
    rows text =
        [ unwords (["owned", quoted name] ++ map quoted ([""] ++ pair dropRole "drop" name ++ pair "std$core$ownership$Clone" "clone" name ++ ["", ""]))
        | line <- lines text, Just name <- [declared line] ]
      where
        pair trait function name
            | quoted ("<" ++ name ++ " as " ++ trait ++ ">::" ++ function) `isInfixOf` text = [trait, "<" ++ name ++ " as " ++ trait ++ ">::" ++ function]
            | name == "V" && trait == dropRole && "\"app$V$release\"" `isInfixOf` text = [trait, "app$V$release"]
            | name == "V" && trait == dropRole && "\"absent\"" `isInfixOf` text = [trait, "absent"]
            | otherwise = ["", ""]
    declared :: String -> Maybe String
    declared line = case break (== ' ') line of
        (keyword, ' ' : rest) | keyword `elem` ["struct", "enum"], [(name, _)] <- reads rest -> Just name
        _ -> Nothing
    quoted name = show name
    withRecords records text = insertAfterTypes (("ownership " ++ show (length records)) : records) text
    stdList = "std$core$types$List"
    dropRole = "std$core$ownership$Drop"
    withoutStorage text = unlines [l | l <- lines text, not ("storage " `isPrefixOf` l)]
    insertAfterTypes extra text =
        let (header : rest) = lines text
            (types, others) = span (\l -> declared l /= Nothing) rest
         in unlines (header : types ++ extra ++ others)
    replace from to text = case text of
        [] -> []
        _ | from `isPrefixOf` text -> to ++ replace from to (drop (length from) text)
        c : more -> c : replace from to more

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
        dataOf <- if embeddedToolFile name then mirDataFromFile name else mirDataOf source
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
    snapshot <- Modules.captureFilesystemInput Modules.defaultLoadOptions path Nothing
    loaded <- case snapshot of
        Left err -> pure (Error err)
        Right captured -> cachedFilesystemSnapshot "owned" captured
    input <- mirDataOf "fn double(n: Int) -> Int { return n + n; }; return double(3);"
    backend <- lookupEnv "TERSUS_PARSER"
    parser <- TersusParser.parserKey
    case (loaded, input, parser, snapshot) of
        (Error e, _, _, _) -> pure (Just e)
        (_, Error e, _, _) -> pure (Just e)
        (_, _, Error e, _) -> pure (Just e)
        (_, _, _, Left e) -> pure (Just e)
        (Ok program, Ok text, Ok identity, Right (_, _, snapshotInput)) -> case Map.lookup "outline" (progFunctions program) of
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
                        inputs = [snapshotInput, writeProgram instrumented, show backend, compilerSnapshotHash, identity, runtimeSource]
                        build output = do
                            ir <- llvmOfOwned instrumented
                            case ir of
                                Error e -> pure (Error e)
                                Ok outlineProbeIr -> buildExecutable output outlineProbeIr
                    key <- nativeCacheKey inputs
                    built <- case key of
                        Error err -> pure (Error err)
                        Ok completeKey -> cachedProgram "test-emit-outline-call" completeKey "the outline call fixture" build
                    case built of
                        Error e -> pure (Just e)
                        Ok markedExe -> do
                            failures <- mapM (checkMode exe markedExe text) [[], ["ir"], ["outline"], ["bodies"]]
                            pure (firstFailure failures)
  where
    path = "lib/mir/emit/emit.tersus"
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
                unsupported = writeProgram (unsupportedMain program)
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

unsupportedMain :: Program -> Program
unsupportedMain program = program{progMain = main
    { fnReturns = Just (TParam "T")
    , fnLocals = Map.adjust (\decl -> decl{localType = TParam "T"}) (Local 0) (fnLocals main)
    }}
  where
    main = progMain program

refusedEmit :: IO TestResult
refusedEmit = withEmitter $ \exe -> do
    owned <- ownedOnce "return 1;"
    case owned of
        Error e -> pure (Just e)
        Ok program -> do
            ir <- emitWith exe (writeProgram (unsupportedMain program))
            pure (testAssertEq ir (Error ("In " ++ fnName (progMain program) ++ ": Native code does not support T yet")))

-- (llvm, build and run all write the IR with llvmOfOwned)
refusedIr :: IO TestResult
refusedIr = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else do
            owned <- ownedOnce "return 1;"
            case owned of
                Error e -> pure (Just e)
                Ok program -> do
                    ir <- llvmOfOwned (unsupportedMain program)
                    pure (testAssertEq ir (Error ("Native code failed: In " ++ fnName (progMain program) ++ ": Native code does not support T yet")))
