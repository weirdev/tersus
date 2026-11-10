module TestPipeline
    ( testExamples
    , testHostValidation
    , testCli
    , testMir
    , testMirSelfHosted
    , selfHostedFamilyManifest
    , testIntRange
    , testPipeline
    , ExampleExpectation (..)
    , exampleExpectations
    ) where

import Control.Exception (bracket, evaluate, finally)
import Data.List (isInfixOf, nub, sort, subsequences)
import GHC.IO.Encoding (char8, getLocaleEncoding, setLocaleEncoding)
import System.Directory (createDirectory, createDirectoryIfMissing, doesFileExist, findExecutable, getTemporaryDirectory, removeDirectoryRecursive, removeFile)
import System.Environment (getExecutablePath, lookupEnv)
import System.FilePath ((</>), takeDirectory)
import System.Exit (ExitCode (..))
import System.Process (CreateProcess (..), proc)
import Native (readProcessOutput)
import CacheLock (openTempFileCloexec)
import System.IO
import qualified Data.Map as Map
import Cli
import Modules (LoadResult (..))
import qualified Modules
import PreludeSource (parserPackageFiles)
import qualified Mir as M
import MirEval
import MirLower
import MirHousekeeping (verifyProgram, validationEntry)
import Pipeline
import SelfHostedMir (encode, validateMirSubset, verdictProved)
import ValidatorNative (prepareTexts)
import TestParserFragments
import StdLib
import StdLibDefs (stdLibCtx, stdlibBuiltin)
import TypeCheck (Elaborated (..), elaborate)
import Types
import Syntax
import Utils
import TestHarness

-- Example program tests
-- Programs in examples/ must keep behaving as documented in examples/README.md.
-- Paths are relative to the package root, which is where `stack test` runs.
data ExampleExpectation
    = -- Validates, evaluates, and returns this value
      ExpectReturn Value
    | -- Validates and evaluates without a return value
      ExpectValid
    | -- Validation fails with an error containing this text
      ExpectRejected String

testExampleFile :: FilePath -> ExampleExpectation -> Test
testExampleFile path expectation = TestCase path $ do
    root <- Modules.findPackageRootIO path
    lowered <- case root of
        Nothing -> compileSource <$> readFile path
        Just _ -> do
            loaded <- if path == "lib/parser/parser.tersus"
                then pure (Modules.loadFromEntry (Modules.resolverFromFiles parserPackageFiles) path)
                else loadFromFilesystem path
            case loaded of
                Left err -> pure (Error err)
                Right (PackageResult pkg) -> pure (compileModulesToProgram pkg)
                Right (StandaloneResult _ _) -> compileSource <$> readFile path
    pure $ case lowered of
        Error err -> case expectation of
            ExpectRejected expectedError -> testAssertErrorContains expectedError (Error err :: Result () String)
            _ -> Just ("Example failed to compile: " ++ err)
        Ok program -> case expectation of
            ExpectRejected _ -> Just "expected rejection, but the example compiled"
            _ -> case runProgram program of
                Error err -> Just ("Evaluation failed with error: " ++ err)
                Ok result -> case expectation of
                    ExpectReturn expected -> testAssertEq (fmap fromMirValue result) (Just expected)
                    _ -> testAssertEq (fmap fromMirValue result) Nothing

-- The first failure of two checks
orElse :: TestResult -> TestResult -> TestResult
orElse Nothing other = other
orElse failure _ = failure

testModulesPackageExample :: Test
testModulesPackageExample = TestCase "examples/modules/app/main.tersus" $ do
    loaded <- loadFromFilesystem "examples/modules/app/main.tersus"
    pure $ case loaded of
        Left err -> Just ("modules example should load: " ++ err)
        Right (PackageResult pkg) -> case runPackageFiles noWorld Interpret pkg of
            Error err -> Just ("modules example should run: " ++ err)
            Ok ((output, _), _) -> testAssertEq output "64"
        Right other -> Just ("modules example should be a package, got: " ++ show other)

-- The compiler's own programs (the AST reader, and the MIR reader, checker and eraser and the
-- emitter of the mir package, under lib/) validated. They are large enough that validating them takes far longer than
-- the rest of the suite, so this group runs only when it is named (TestTersus.optInGroups); the
-- groups that run them build them unvalidated, as the host does.
testHostValidation :: Test
testHostValidation =
    TestList
        "testHostValidation"
        [ testExampleFile "lib/ast_reader/ast_reader.tersus" (ExpectReturn (VInt 1))
        , testExampleFile "lib/mir/mir_reader/mir_reader.tersus" (ExpectReturn (VInt 1))
        , testExampleFile "lib/mir/mir_verify/mir_verify.tersus" (ExpectReturn (VInt 1))
        , testExampleFile "lib/mir/mir_erase/mir_erase.tersus" (ExpectReturn (VInt 1))
        , testExampleFile "lib/mir/emit/emit.tersus" (ExpectReturn (VInt 1))
        ]

testExamples :: Test
testExamples =
    TestList
        "testExamples"
        (testModulesPackageExample : [testExampleFile path expectation | (path, expectation) <- exampleExpectations])

exampleExpectations :: [(FilePath, ExampleExpectation)]
exampleExpectations =
    [ ("examples/basics.tersus", ((ExpectReturn (VInt 6))))
    , ("examples/functions.tersus", ((ExpectReturn (VInt 21))))
    , ("examples/booleans.tersus", ((ExpectReturn (VBool True))))
    , ("examples/proofs.tersus", ExpectValid)
    , ("examples/rewrites.tersus", ExpectValid)
    , ("examples/safe_access.tersus", ((ExpectReturn (VInt 38))))
    , ("examples/contracts.tersus", ((ExpectReturn (VInt 8))))
    , ("examples/rules.tersus", ExpectValid)
    , ("examples/branching.tersus", ((ExpectReturn (VInt 106))))
    , ("examples/arithmetic.tersus", ((ExpectReturn (VInt 6))))
    , ("examples/types.tersus", ((ExpectReturn (VInt 6))))
    , ("examples/structs.tersus", ((ExpectReturn (VInt 11))))
    , ("examples/linked_list.tersus", ((ExpectReturn (VInt 9))))
    , ("examples/enums.tersus", ((ExpectReturn (VInt 27))))
    , ("examples/traits.tersus", ((ExpectReturn (VInt 55))))
    , ("examples/addresses.tersus", ((ExpectReturn (VInt 112))))
    , ("examples/drops.tersus", ((ExpectReturn (VInt 70))))
    , ("examples/rejected/trait_input_stronger.tersus", ((ExpectRejected "impl Step for Counter: advance does not meet what Step declares")))
    , ("examples/rejected/trait_output_weaker.tersus", ((ExpectRejected "impl Measure for Pair: measure does not meet what Measure declares")))
    , ("examples/rejected/body_not_exported.tersus", ((ExpectRejected "Could not prove: return = n")))
    , ("examples/rejected/trait_ambiguous_call.tersus", ((ExpectRejected "Counter::label is ambiguous")))
    , ("examples/rejected/trait_missing_function.tersus", ((ExpectRejected "impl Step for Counter lacks the function total")))
    , ("examples/arrays.tersus", ((ExpectReturn (VInt 42))))
    , ("examples/array_data.tersus", ((ExpectReturn (VInt 45))))
    , ("examples/rejected/array_size_mismatch.tersus", ((ExpectRejected "argument 2 of dot: expected Array<Int, 5>, got Array<Int, 4>")))
    , ("examples/rejected/array_runtime_size.tersus", ((ExpectRejected "the size of an array must be a constant")))
    , ("examples/rejected/array_unsized.tersus", ((ExpectRejected "an array with no size")))
    , ("examples/box_array.tersus", ((ExpectReturn (VInt 34))))
    , ("examples/array_sizes.tersus", ((ExpectReturn (VInt 42))))
    , ("examples/type_parameters.tersus", ((ExpectReturn (VInt 2045))))
    , ("examples/generic_structs.tersus", ((ExpectReturn (VInt 2224))))
    , ("examples/files.tersus", ((ExpectReturn (VInt (-1)))))
    , ("examples/args.tersus", ((ExpectReturn (VInt 0))))
    , ("examples/bytes.tersus", ((ExpectReturn (VInt 275020))))
    , ("examples/hello.tersus", ((ExpectReturn (VInt 14))))
    , ("examples/strings.tersus", ((ExpectReturn (VInt 980))))
    , ("examples/upper.tersus", ((ExpectReturn (VInt 0))))
    , ("examples/text.tersus", ((ExpectReturn (VInt 504))))
    , ("examples/vec.tersus", ((ExpectReturn (VInt 2491212381))))
    , ("examples/hashmap.tersus", ((ExpectReturn (VInt 218420))))
    , ("examples/spec_functions.tersus", ((ExpectReturn (VInt 25070))))
    , ("examples/list_methods.tersus", ((ExpectReturn (VInt 508221))))
    , ("examples/array_owners.tersus", ((ExpectReturn (VInt 207))))
    , ("examples/borrowing.tersus", ((ExpectReturn (VInt 138))))
    , ("examples/sized_structs.tersus", ((ExpectReturn (VInt 71))))
    , ("examples/rejected/sized_struct_mismatch.tersus", ((ExpectRejected "argument 1 of first: expected Packet<3>, got Packet<2>")))
    , ("examples/rejected/array_size_param_mismatch.tersus", ((ExpectRejected "argument 2 of dot: expected Array<Int, 2>, got Array<Int, 3>")))
    , ("examples/rejected/box_array_size.tersus", ((ExpectRejected "argument 1 of corner: expected Box<Array<Int, 3>>, got Box<Array<Int, ?>>")))
    , ("examples/rejected/array_push.tersus", ((ExpectRejected "argument 1 of push: expected List<?>, got Array<Int, 2>")))
    , ("examples/generic_lists.tersus", ((ExpectReturn (VList [VList [VInt 1, VInt 2], VList [VInt 3, VInt 4], VList [VInt 1, VInt 2]]))))
    , ("examples/helper_functions.tersus", ((ExpectReturn (VInt 11))))
    , ("examples/recursion.tersus", ((ExpectReturn (VInt 26))))
    , ("examples/termination.tersus", ((ExpectReturn (VInt 23))))
    , ("examples/for_loops.tersus", ((ExpectReturn (VInt 33))))
    , ("examples/linear.tersus", ((ExpectReturn (VInt 633))))
    , ("examples/packet_parser.tersus", ((ExpectReturn (VInt 711))))
    , ("examples/loops.tersus", ((ExpectReturn (VInt 30))))
    , ("examples/early_return.tersus", ((ExpectReturn (VInt 104))))
    , ("examples/loop_return.tersus", ((ExpectReturn (VInt 7))))
    , ("examples/parallel_sum.tersus", ((ExpectReturn (VList [VInt 11, VInt 22, VInt 33]))))
    , ("examples/build_list.tersus", ((ExpectReturn (VList [VInt 2, VInt 4, VInt 6]))))
    , ("examples/update_list.tersus", ((ExpectReturn (VList [VInt 101, VInt 102, VInt 103]))))
    , ("examples/element_facts.tersus", ((ExpectReturn (VInt 106))))
    , ("examples/frame_facts.tersus", ((ExpectReturn (VInt 149))))
    , ("examples/forall_facts.tersus", ((ExpectReturn (VInt 5))))
    , ("examples/rejected/forall_wrong_element.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/forall_invariant_gap.tersus", ((ExpectRejected "Loop invariant is not preserved")))
    , ("examples/rejected/forall_unproven.tersus", ((ExpectRejected "input validation failed")))
    , ("examples/rejected/frame_changed_index.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/get_out_of_range.tersus", ((ExpectRejected "Relation does not hold")))
    , ("examples/rejected/get_unproven_index.tersus", ((ExpectRejected "Relation lacks a proof")))
    , ("examples/rejected/parallel_length.tersus", ((ExpectRejected "Relation lacks a proof")))
    , ("examples/rejected/call_violates_contract.tersus", ((ExpectRejected "Could not prove: n > 0")))
    , ("examples/rejected/recursion_wrong_contract.tersus", ((ExpectRejected "Could not prove: return = 0")))
    , ("examples/rejected/recursion_input.tersus", ((ExpectRejected "Could not prove: n > 0")))
    , ("examples/rejected/type_return_mismatch.tersus", ((ExpectRejected "returned value: expected Int, got List<Int>")))
    , ("examples/rejected/type_argument_mismatch.tersus", ((ExpectRejected "argument 1 of size")))
    , ("examples/rejected/list_element_mismatch.tersus", ((ExpectRejected "argument 2 of push: expected Bool, got Int")))
    , ("examples/rejected/struct_update_frame.tersus", ((ExpectRejected "Could not prove: return.y = p.x")))
    , ("examples/rejected/struct_field_type.tersus", ((ExpectRejected "field value of Node: expected Int, got Bool")))
    , ("examples/rejected/enum_contract_unmet.tersus", ((ExpectRejected "Could not prove: s is Shape::Circle")))
    , ("examples/rejected/enum_wrong_variant.tersus", ((ExpectRejected "Could not prove: s is Shape::Rect")))
    , ("examples/rejected/linked_list_link_out_of_range.tersus", ((ExpectRejected "Could not prove: forall i in 0..size(return): get(return, i).next < size(return)")))
    , ("examples/rejected/linked_list_link_disagrees.tersus", ((ExpectRejected "Could not prove: forall i in 0..size(return): get(return, get(return, i).next).prev = i")))
    , ("examples/rejected/for_reads_past_end.tersus", ((ExpectRejected "Funct input validation failed")))
    , ("examples/rejected/division_not_below.tersus", ((ExpectRejected "Could not prove: return < n")))
    , ("examples/rejected/sum_bound_too_strong.tersus", ((ExpectRejected "Could not prove: return < 10")))
    , ("examples/rejected/loop_sum_not_kept.tersus", ((ExpectRejected "Could not prove: return = n")))
    , ("examples/rejected/packet_off_by_one.tersus", ((ExpectRejected "Funct input validation failed")))
    , ("examples/rejected/packet_negative_length.tersus", ((ExpectRejected "Funct input validation failed: Could not prove: lo <= hi")))
    , ("examples/rejected/packet_checksum_range.tersus", ((ExpectRejected "Could not prove: return < 255")))
    , ("examples/rejected/for_assigns_counter.tersus", ((ExpectRejected "The body of a for loop cannot assign its loop variable i")))
    , ("examples/rejected/loop_without_termination.tersus", ((ExpectRejected "Loop must say how it ends")))
    , ("examples/rejected/loop_variant_not_shrinking.tersus", ((ExpectRejected "Loop variant does not shrink: 3 - i")))
    , ("examples/rejected/loop_variant_unbounded.tersus", ((ExpectRejected "Loop variant is not bounded below: i")))
    , ("examples/rejected/recursion_without_variant.tersus", ((ExpectRejected "Not guaranteed to terminate: it calls itself")))
    , ("examples/rejected/recursion_variant_not_shrinking.tersus", ((ExpectRejected "Recursive call does not shrink the variant: n")))
    , ("examples/rejected/box_infinite_size.tersus", ((ExpectRejected "Chain holds itself, so it would have no size: hold the recursion in a Box, as in Box<Chain>")))
    , ("examples/rejected/recursion_shrinks_not_a_part.tersus", ((ExpectRejected "Recursive call does not shrink the variant: t")))
    , ("examples/rejected/diverging_call.tersus", ((ExpectRejected "it calls a function that is declared ~")))
    , ("examples/rejected/diverging_loop.tersus", ((ExpectRejected "a loop is declared ~")))
    , ("examples/rejected/linked_list_unchecked_walk.tersus", ((ExpectRejected "Loop invariant is not preserved")))
    , ("examples/call_forward.tersus", ((ExpectReturn (VInt 42))))
    , ("examples/mutual_recursion.tersus", ((ExpectReturn (VInt 2))))
    , ("examples/rejected/call_undefined.tersus", ((ExpectRejected "Undefined variable: nowhere")))
    , ("examples/rejected/mutual_without_variant.tersus", ((ExpectRejected "Mutually recursive functions must say what shrinks")))
    , ("examples/rejected/mutual_variant_not_shrinking.tersus", ((ExpectRejected "does not shrink the variant")))
    , ("examples/rejected/mutual_diverging_peer.tersus", ((ExpectRejected "declared ~")))
    , ("examples/rejected/division_by_zero.tersus", ((ExpectRejected "Relation lacks a proof")))
    , ("examples/rejected/push_size.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/set_out_of_range.tersus", ((ExpectRejected "Relation does not hold")))
    , ("examples/rejected/set_size.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/element_wrong.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/invariant_entry.tersus", ((ExpectRejected "Loop invariant does not hold on entry")))
    , ("examples/rejected/invariant_preserved.tersus", ((ExpectRejected "Loop invariant is not preserved")))
    , ("examples/rejected/loop_stale_fact.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/loop_return_invariant.tersus", ((ExpectRejected "Loop invariant is not preserved")))
    , ("examples/rejected/loop_missing_return.tersus", ((ExpectRejected "Return value not found")))
    , ("examples/rejected/unguarded_access.tersus", ((ExpectRejected "Could not prove: size(list) > 0")))
    , ("examples/rejected/branch_fact.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/guard_condition.tersus", ((ExpectRejected "Could not prove: size(list) > 0")))
    , ("examples/rejected/missing_return.tersus", ((ExpectRejected "Return value not found")))
    , ("examples/rejected/affirm.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/first_of_empty.tersus", ((ExpectRejected "Could not prove: size(list) > 0")))
    , ("examples/rejected/unmet_contract.tersus", ((ExpectRejected "is not greater than 0")))
    , ("examples/rejected/missing_contract.tersus", ((ExpectRejected "Could not prove: size(list) > 0")))
    , ("examples/rejected/output_contract.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/bad_proof_rule.tersus", ((ExpectRejected "Could not prove")))
    , ("examples/rejected/axiom_input.tersus", ((ExpectRejected "is not greater than 0")))
    , ("examples/rejected/unknown_rule.tersus", ((ExpectRejected "Unknown rewrite rule")))
    ]

-- CLI tests
testCliParseCommandLine :: TestResult
testCliParseCommandLine =
    testAssertEq
        (map parseCommandLine [["check", "a.tersus"], ["run", "-"], ["run"], ["frob", "a.tersus"], []])
        [Just (Check, "a.tersus"), Just (Run, "-"), Nothing, Nothing, Nothing]
        `orElse` testAssertEq (parseCommandLine ["mir", "a.tersus"]) (Just (Mir, "a.tersus"))
        `orElse` testAssertEq (parseCommandLine ["eval", "a.tersus"]) (Just (Interpret, "a.tersus"))

testCliRenderValue :: TestResult
testCliRenderValue =
    testAssertEq
        (map renderValue [VInt 5, VList [], VList [VInt 1, VInt 2], VBool True, VBool False])
        ["5", "[]", "[1, 2]", "true", "false"]

testCliRun :: TestResult
testCliRun =
    testAssertEq
        (map (runSource Interpret) ["x = [1, 2]; return size(x);", "return [3, 4];", "return 1 < 2;", "x = 5; affirm x = 5;", ""])
        [Ok "2", Ok "[3, 4]", Ok "true", Ok "", Ok ""]

testCliCheck :: TestResult
testCliCheck = testAssertEq (runSource Check "x = 5; affirm x = 5; return x;") (Ok "OK")

-- A program with a letter that is not ASCII loads under a locale that is not UTF-8
testCliReadsUtf8 :: Test
testCliReadsUtf8 = TestCase "utf8 source" $ do
    tmp <- getTemporaryDirectory
    (path, handle) <- openTempFileCloexec tmp "tersus_utf8.tersus"
    hSetEncoding handle utf8
    hPutStr handle "\233t\233 = 6; return \233t\233 * 7; // caf\233\n"
    hClose handle
    saved <- getLocaleEncoding
    (do setLocaleEncoding char8
        source <- readSourceFile path
        -- (the whole text, so that the handle has reached its end before the file is removed: Windows will not remove a file that is open)
        _ <- evaluate (length source)
        return (if runSource Interpret source == Ok "42" then Nothing else Just ("got " ++ show (runSource Interpret source))))
        `finally` (setLocaleEncoding saved >> removeFile path)

cliExecutable :: IO (Maybe FilePath)
cliExecutable = do
    supplied <- lookupEnv "TERSUS_TEST_CLI"
    self <- getExecutablePath
    adjacent <- doesFileExist (takeDirectory self </> "tersus-exe")
    case supplied of
        Just path -> pure (Just path)
        Nothing | adjacent -> pure (Just (takeDirectory self </> "tersus-exe"))
        Nothing -> do
            stack <- findExecutable "stack"
            case stack of
                Nothing -> pure Nothing
                Just command -> do
                    (code, output, _) <- readProcessOutput (proc command ["path", "--local-install-root"]) ""
                    let path = takeWhile (/= '\n') output </> "bin/tersus-exe"
                    present <- doesFileExist path
                    pure (if code == ExitSuccess && present then Just path else Nothing)

testCliConfiguredSources :: Test
testCliConfiguredSources = TestCase "real CLI isolates standalone/stdin roots and validates no-prelude IR" $ do
    executable <- cliExecutable
    case executable of
        Nothing -> pure (Just "tersus-exe is required for CLI regression; build it or supply TERSUS_TEST_CLI")
        Just cli -> bracket create removeDirectoryRecursive $ \root -> do
            let proj = root </> "proj"
                vendor = root </> "vendor"
                cwdRoot = root </> "X"
                standalone = proj </> "source.tersus"
                source = "import vendor::api { answer }; return answer();"
                config = ["--package-root", "vendor=" ++ vendor, "--no-prelude"]
                write path text = createDirectoryIfMissing True (takeDirectory path) >> writeFile path text
                run args input = readProcessOutput (proc cli args){cwd = Just (if ("X=" ++ cwdRoot) `elem` args then cwdRoot else proj)} input
                cases =
                    [ (config ++ ["eval", standalone], "", ExitSuccess, "42", "")
                    , (config ++ ["eval", "-"], source, ExitSuccess, "42", "")
                    , (config ++ ["check", "-"], "import foo::api; return 0;", ExitFailure 1, "", "not configured for standalone source")
                    , (config ++ ["check", "-"], "import main; return 0;", ExitFailure 1, "", "not configured for standalone source")
                    , (["--package-root", "X=" ++ cwdRoot, "--no-prelude", "eval", "-"], "import X::provider { answer }; return answer();", ExitSuccess, "42", "")
                    , (["--no-prelude", "llvm", "-"], "affirm 1 = 2; return 42;", ExitFailure 1, "", "Could not prove:")
                    , (["--package-root", "vendor=a", "--package-root", "vendor=b", "check", "-"], "return 0;", ExitFailure 2, "", "Usage:")
                    ]
            write (vendor </> "package.tersus") "noPrelude = true;"
            write (vendor </> "api/api.tersus") "fn answer() -> Int { return 42; };"
            write (root </> "foo/package.tersus") "noPrelude = true;"
            write (root </> "foo/api/api.tersus") "fn answer() -> Int { return 99; };"
            write standalone source
            initial <- run (config ++ ["eval", standalone]) ""
            write (cwdRoot </> "package.tersus") "noPrelude = true;"
            write (cwdRoot </> "provider.tersus") "fn answer() -> Int { return 42; };"
            results <- mapM (\(args, input, expectedCode, expectedOutput, expectedError) -> do
                (code, output, errors) <- run args input
                pure (testAssertEq code expectedCode <> testAssertEq (trim output) expectedOutput
                    <> if expectedError `isInfixOf` errors then Nothing else Just ("wrong CLI diagnostic: " ++ errors))) cases
            (irCode, ir, irErrors) <- run ["--no-prelude", "llvm", "-"] "return 42;"
            pure (testAssertEq initial (ExitSuccess, "42\n", "")
                <> foldr (<>) Nothing results
                <> testAssertEq irCode ExitSuccess
                <> testAssertTrue ("define" `isInfixOf` ir && null irErrors))
  where
    trim = reverse . dropWhile (`elem` "\r\n") . reverse
    create = do
        tmp <- getTemporaryDirectory
        (path, handle) <- openTempFileCloexec tmp "tersus-phase1-cli"
        hClose handle
        removeFile path
        createDirectory path
        pure path

testCli :: Test
testCli = TestList "testCli" [testCliReadsUtf8, testCliConfiguredSources, testCliCases]

-- Every entry point must refuse a program that does not validate, before it
-- is evaluated or lowered: (mode, runner for that mode, source, expected error).
-- The "return first([]);" row is the one that would be evaluated if validation
-- did not reject it first.
validationFailureCases :: [(String, String -> Result String String, String, String)]
validationFailureCases =
    [ ("Interpret", runSource Interpret, "x = 5; affirm x < 4;", "Validation failed")
    , ("Check", runSource Check, "x = 5; affirm x < 4;", "Validation failed")
    , ("Interpret", runSource Interpret, "return first([]);", "Validation failed")
    , ("Mir", runSource Mir, "x = 1; affirm x = 2;", "Validation failed")
    , ("compileSource", \source -> mapResult (const "") (compileSource source), "x = 1; affirm x = 2;", "Validation failed: Could not prove")
    ]

validationFailuresFor :: [String] -> [TestResult]
validationFailuresFor modes =
    [ testAssertErrorContains expected (run source)
    | (mode, run, source, expected) <- validationFailureCases
    , mode `elem` modes
    ]

validationFailureFor :: String -> TestResult
validationFailureFor mode = foldr orElse Nothing (validationFailuresFor [mode])

testCliCases :: Test
testCliCases =
    testCaseSeq
        "testCliCases"
        ([ testCliParseCommandLine
         , testCliRenderValue
         , testCliRun
         , testCliCheck
         , testAssertErrorContains "Parse error" (runSource Interpret "x = ;")
         ]
            ++ validationFailuresFor ["Interpret", "Check"])

-- MIR tests
-- Programs are lowered without being validated here (the examples are validated by testExamples), so a program may
-- do what validation would refuse.
lowerSource :: String -> Either String M.Program
lowerSource source = case parseStatementBlock source of
    Left err -> Left ("Parse failed: " ++ show err)
    Right stmts -> case lowerProgram stmts of
        Error e -> Left e
        Ok program -> Right program

withMir :: String -> (M.Program -> TestResult) -> TestResult
withMir source check = either Just check (lowerSource source)

-- What the program returns, run on the MIR
runMir :: String -> Result (Maybe String) String
runMir source = case lowerSource source of
    Left e -> Error e
    Right program -> mapResult (fmap renderMirValue) (runProgram program)

safeHead :: [a] -> Maybe a
safeHead (x : _) = Just x
safeHead [] = Nothing

blocksOf :: M.Function -> [(M.BlockId, M.BasicBlock)]
blocksOf = Map.toList . M.fnBlocks

mainFunction :: M.Program -> M.Function
mainFunction = M.progMain

-- The local with this source name (every one, as a variable can have several in different scopes)
localsNamed :: String -> M.Function -> [M.Local]
localsNamed name fn = [l | (l, d) <- Map.toList (M.fnLocals fn), M.localName d == Just name]

testMirStructure :: Test
testMirStructure =
    testCaseSeq
        "testMirStructure"
        [ -- A loop is a header that the end of the body jumps back to, and the header is the loop's
          withMir "i = 0; while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { i = i + 1; }; return i;" $ \p ->
            let fn = mainFunction p
                headers = Map.keys (M.specLoops (M.fnSpec fn))
                backEdges = [(from, to) | (from, M.BasicBlock _ (M.Goto to)) <- blocksOf fn, to <= from]
             in testAssertEq (length headers, map snd backEdges) (1, headers)
        , -- An if is a switch whose two branches meet at one block
          withMir "x = 1; if x < 2 { x = 5; } else { x = 6; }; return x;" $ \p ->
            let fn = mainFunction p
                gotos = [to | (_, M.BasicBlock _ (M.Goto to)) <- blocksOf fn]
             in testAssertEq (length (blocksOf fn), length gotos, length (filter (== head gotos) gotos)) (4, 2, 2)
        , -- With a return in both branches nothing is left to join
          withMir "x = 1; if x < 2 { return 5; } else { return 6; };" $ \p ->
            let fn = mainFunction p
             in testAssertEq (length (blocksOf fn), length [t | (_, M.BasicBlock _ t) <- blocksOf fn, isReturn t]) (3, 2)
        , -- A statement after a return is not lowered
          withMir "return 1; x = 2; return x;" $ \p ->
            testAssertEq (length (blocksOf (mainFunction p)), Map.size (M.fnLocals (mainFunction p))) (1, 1)
        , -- An assignment through a reference after a return is not lowered either
          withMir "x = 0; r = &mut x; return 0; *r = 1;" $ \p ->
            testAssertEq (length (blocksOf (mainFunction p))) 1
        , -- A function in a function is lifted to the top, and a function at the top keeps its name
          withMir "fn outer(n: Int) -> Int { fn inner(m: Int) -> Int { return m + 1; }; return inner(n); }; return outer(1);" $ \p ->
            testAssertEq (Map.keys (M.progFunctions p)) ["outer", "outer::inner"]
        , -- A variable made in a block is a local of its own: the two y are not the same, the x is one
          withMir "x = 1; { x = 2; y = 3; }; { y = 4; }; return x;" $ \p ->
            let fn = mainFunction p
             in testAssertEq (length (localsNamed "x" fn), length (localsNamed "y" fn)) (1, 2)
        , -- A shadowing let is another local too
          withMir "fn f(a: Int) -> Int { return a; }; x = 1; return f(x) + x;" $ \p ->
            testAssertEq (length (localsNamed "x" (mainFunction p))) 1
        , -- A function passed as a value is a constant function
          withMir "fn apply(g: fn(Int) -> Int, n: Int) -> Int { return g(g(n)); }; fn inc(n: Int) -> Int { return n + 1; }; return apply(inc, 1);" $ \p ->
            testAssertTrue ("const fn inc" `isInfixOf` M.renderProgram p)
        , -- The element type of an empty list is the one a later push decides, and every local has a type
          withMir "x = []; x = push(x, 1); return x;" $ \p ->
            testAssertEq [M.localType d | d <- Map.elems (M.fnLocals (mainFunction p)), M.localName d == Just "x"] [TList TInt]
        , -- A list that is never used still has a type
          withMir "x = [];" $ \p ->
            testAssertEq [M.localType d | d <- Map.elems (M.fnLocals (mainFunction p)), M.localName d == Just "x"] [TList TInt]
        , -- Types come out right for structs and enums
          withMir "struct P { x: Int, y: Bool }; p = P { x: 1, y: true }; q = p.y; r = p.x; return r;" $ \p ->
            testAssertEq [M.localType d | d <- Map.elems (M.fnLocals (mainFunction p)), M.localName d == Just "q"] [TBool]
        , -- The contracts, the loop and the proofs are kept, and the types are declared
          withMir "struct P { x: Int }; fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { affirm n > 0; return n; }; return f(1);" $ \p ->
            case Map.lookup "f" (M.progFunctions p) of
                Nothing -> Just "f is not in the program"
                Just fn ->
                    testAssertEq
                        (length (M.specRequires (M.fnSpec fn)), length (M.specEnsures (M.fnSpec fn)), length [() | (_, M.BasicBlock stmts _) <- blocksOf fn, M.Ghost{} <- stmts], Map.keys (M.progTypes p))
                        (1, 1, 1, ["P"])
        , -- A ghost statement carries what its names stand for where it is: the local, or the function
          withMir "fn f(n: Int) -> Int { return n; }; x = 1; { x = 2; y = 3; affirm y = 3; }; return f(x);" $ \p ->
            let envs = [env | (_, M.BasicBlock stmts _) <- blocksOf (mainFunction p), M.Ghost env (M.GhostValidation _) <- stmts]
                fn = mainFunction p
             in testAssertEq
                    (map (Map.lookup "f") envs, [Map.lookup "x" env == fmap M.Copy (safeHead (localsNamed "x" fn)) | env <- envs], [Map.member "y" env | env <- envs])
                    ([Just (M.Const (M.CFn "f"))], [True], [True])
        , -- Where a function is defined is marked, and the specification of the function names its parameters
          withMir "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ }] { return n; }; return f(1);" $ \p ->
            testAssertEq
                ([g | (_, M.BasicBlock stmts _) <- blocksOf (mainFunction p), M.Ghost _ g@M.GhostFunction{} <- stmts], fmap (M.specEnv . M.fnSpec) (Map.lookup "f" (M.progFunctions p)))
                ([M.GhostFunction "f" "f" True], Just (Map.fromList [("f", M.Const (M.CFn "f")), ("n", M.Copy (M.Local 1))]))
        , -- A builtin used as a value is a function of the program
          case lowerProgram [Assign "f" (Val (builtinFunct Plus)), Assign "r" (F (Var "f") [Val (VInt 1), Val (VInt 2)]), Return (Var "r")] of
            Error e -> Just e
            Ok p -> testAssertEq (Map.keys (M.progFunctions p), mapResult (fmap renderMirValue) (runProgram p)) (["builtin::add"], Ok (Just "3"))
        , -- A call ends the block it is in
          withMir "fn f(n: Int) -> Int { return n; }; a = f(1); b = f(a); return b;" $ \p ->
            testAssertEq (length [() | (_, M.BasicBlock _ M.Call{}) <- blocksOf (mainFunction p)]) 2
        , -- A cast is an operation of the MIR that gives the value the variant's type
          withMir "enum S { A { r: Int }, B }; s = S::A { r: 1 }; a = s as S::A; return a.r;" $ \p ->
            testAssertEq ([M.localType d | d <- Map.elems (M.fnLocals (mainFunction p)), M.localName d == Just "a"], "_1 as S::A" `isInfixOf` M.renderProgram p) ([TVariant "S::A"], True)
        , -- A function whose name is assigned is a local that holds it; one that is not is called by name
          withMir "fn f(n: Int) -> Int { return n; }; fn g(n: Int) -> Int { return n; }; h = f; h = g; return f(1) + h(2);" $ \p ->
            let fn = mainFunction p
             in testAssertEq (length (localsNamed "h" fn), length (localsNamed "f" fn), length (localsNamed "g" fn)) (1, 0, 0)
        , withMir "fn f(l: &List<Int>) -> Int { return 0; }; { f = size; }; return f([1, 2]);" $ \p ->
            testAssertEq (length (localsNamed "f" (mainFunction p)), runProgram p) (1, Ok (Just (MInt 2)))
        , -- Every program lowers to a well formed MIR
          withMir "fn f(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); }] [{ }] { return get(l, i); }; s = 0; for x in [1, 2, 3] { s = s + x; }; l = push([], s); return f(l, 0);" $ \p ->
            testAssertEq (verifyProgram p) (Ok ())
        ]
  where
    isReturn M.Return = True
    isReturn _ = False

-- A malformed program is refused by the check that every lowering goes through
testMirWellFormed :: Test
testMirWellFormed =
    testCaseSeq
        "testMirWellFormed"
        [ withMir "return 1;" $ \p ->
            let fn = mainFunction p
                broken = p{M.progMain = fn{M.fnBlocks = Map.map (\b -> b{M.blockTerminator = M.Goto (M.BlockId 7)}) (M.fnBlocks fn)}}
             in testAssertErrorContains "bb7" (verifyProgram broken)
        , withMir "x = 1; return x;" $ \p ->
            let fn = mainFunction p
                broken = p{M.progMain = fn{M.fnLocals = Map.delete (M.Local 1) (M.fnLocals fn)}}
             in testAssertErrorContains "undeclared" (verifyProgram broken)
        , withMir "x = 1; return x;" $ \p ->
            let fn = mainFunction p
                broken = p{M.progMain = fn{M.fnLocals = Map.map (\d -> d{M.localType = TVar 3}) (M.fnLocals fn)}}
             in testAssertErrorContains "no known type" (verifyProgram broken)
        ]

-- The verifier checks the types of the operations, not only the shape
testMirTypes :: Test
testMirTypes =
    testCaseSeq
        "testMirTypes"
        [ -- the type of the local that receives an operation
          broken "x = 1 + 2; return x;" (setLocalType (M.Local 1) TBool) "ill typed"
        , broken "l = [1]; l = push(l, 2); return size(l);" (setLocalType (M.Local 1) (TList TBool)) "ill typed"
        , broken "struct P { x: Int, y: Bool }; p = P { x: 1, y: true }; q = p.y; return q;" (setLocalType (M.Local 2) TInt) "the field is Bool, not Int"
        , -- operands of the wrong type
          broken "x = 1; if x < 2 { return 1; }; return 2;" (mapTerminators (\t -> case t of M.SwitchBool _ a b -> M.SwitchBool (M.Const (M.CInt 1)) a b; _ -> t)) "the test is not a Bool"
        , broken "x = 1 + 2; return x;" (mapStatements (\st -> case st of M.Assign d (M.BinaryOp op a _) -> M.Assign d (M.BinaryOp op a (M.Const (M.CBool True))); _ -> st)) "ill typed"
        , broken "l = [1, 2]; return get(l, 0);" (mapStatements (\st -> case st of M.Assign d (M.ListOp M.Get [l, _]) -> M.Assign d (M.ListOp M.Get [l, l]); _ -> st)) "ill typed"
        , -- calls: the callee, the arity, the arguments, the result
          broken "fn f(n: Int) -> Int { return n; }; return f(1);" (mapTerminators (\t -> case t of M.Call c _ d n -> M.Call c [] d n; _ -> t)) "takes 1 arguments, got 0"
        , broken "fn f(n: Int) -> Int { return n; }; return f(1);" (mapTerminators (\t -> case t of M.Call c _ d n -> M.Call c [M.Const (M.CBool True)] d n; _ -> t)) "argument 1 is not Int"
        , broken "fn f(n: Int) -> Int { return n; }; return f(1);" (mapTerminators (\t -> case t of M.Call _ a d n -> M.Call (M.Const (M.CInt 3)) a d n; _ -> t)) "not a function"
        , broken "fn f(n: Int) -> Int { return n; }; return f(1);" (mapTerminators (\t -> case t of M.Call _ a d n -> M.Call (M.Const (M.CFn "nope")) a d n; _ -> t)) "names the function nope"
        , broken "fn f(n: Int) -> Int { return n; }; return f(1);" (setLocalType (M.Local 0) TBool) "the function returns"
        , -- a comparison of two types
          broken "return 1 = 2;" (mapStatements (\st -> case st of M.Assign d (M.BinaryOp op a _) -> M.Assign d (M.BinaryOp op a (M.Const (M.CBool True))); _ -> st)) "the operands are"
        , -- a cast: of a value of the enum, giving the variant
          broken "enum S { A { r: Int }, B }; s = S::A { r: 1 }; a = s as S::A; return a.r;" (setLocalType (M.Local 2) TInt) "the result is Int, not S::A"
        , broken "enum S { A { r: Int }, B }; s = S::A { r: 1 }; a = s as S::A; return a.r;" (mapStatements (\st -> case st of M.Assign d (M.AsVariant _ n) -> M.Assign d (M.AsVariant (M.Const (M.CInt 1)) n); _ -> st)) "is not a S"
        , -- a variant is a value of its enum, and not the other way
          withMir "enum S { A { r: Int }, B }; fn f(s: S) -> Int [{ affirm s is S::A; }] [{ }] { return (s as S::A).r; }; return f(S::A { r: 1 });" $ \p ->
            testAssertEq (verifyProgram p) (Ok ())
        ]
  where
    broken source change expected =
        withMir source $ \p -> testAssertErrorContains expected (verifyProgram (onEvery change p))
    onEvery f p = p{M.progMain = f (M.progMain p), M.progFunctions = Map.map f (M.progFunctions p)}
    setLocalType l ty fn = fn{M.fnLocals = Map.adjust (\d -> d{M.localType = ty}) l (M.fnLocals fn)}
    mapBlocks f fn = fn{M.fnBlocks = Map.map f (M.fnBlocks fn)}
    mapTerminators f = mapBlocks (\b -> b{M.blockTerminator = f (M.blockTerminator b)})
    mapStatements f = mapBlocks (\b -> b{M.blockStatements = map f (M.blockStatements b)})

-- Programs run on the MIR, with what they give
testMirRun :: Test
testMirRun =
    testCaseSeq
        "testMirRun"
        [ testAssertEq (runMir source) expected
        | (source, expected) <-
                [ ("return 1 + 2 * 3;", Ok (Just "7"))
                , ("x = 7; y = x % 3; z = x / 2; return y * 10 + z;", Ok (Just "13"))
                , ("return -7 / 2 + -7 % 3;", Ok (Just "-2"))
                , ("l = [1, 2, 3]; l = push(l, 4); l = set(l, 0, 9); return l;", Ok (Just "[9, 2, 3, 4]"))
                , ("l = [1, 2, 3]; return get(l, 1) + first(l) + last(l) + size(l);", Ok (Just "9"))
                , ("x = 0; i = 0; while i < 10 [{ affirm i <= 10; }] shrinks 10 - i { if i % 2 = 0 { x = x + i; }; i = i + 1; }; return x;", Ok (Just "20"))
                , ("fn fact(n: Int) -> Int [{ affirm n >= 0; }] [{ }] shrinks n { if n = 0 { return 1; } else { return n * fact(n - 1); }; }; return fact(10);", Ok (Just "3628800"))
                , ("fn first2(l: List<Int>) -> Int [{ affirm size(l) > 1; }] [{ }] { return get(l, 1); }; return first2([4, 5, 6]);", Ok (Just "5"))
                , ("fn apply(g: fn(Int) -> Int, n: Int) -> Int { return g(g(n)); }; fn inc(n: Int) -> Int { return n + 1; }; return apply(inc, 1);", Ok (Just "3"))
                , ("fn outer(n: Int) -> Int { fn inner(m: Int) -> Int { return m * 2; }; return inner(n) + inner(1); }; return outer(5);", Ok (Just "12"))
                , ("struct P { x: Int, y: Int }; p = P { x: 1, y: 2 }; q = P { y: 5, ..p }; return q.x + q.y;", Ok (Just "6"))
                , ("enum S { A { r: Int }, B, C { w: Int, h: Int } }; fn area(s: S) -> Int { return match s { S::A { r: r } => r * 3, S::B => 0, S::C { w: w, h: h } => w * h }; }; return area(S::A { r: 2 }) + area(S::B) + area(S::C { w: 3, h: 4 });", Ok (Just "18"))
                , ("s = 0; for i in 0..5 { s = s + i; }; for x in [10, 20] { s = s + x; }; return s;", Ok (Just "40"))
                , ("x = 1; if x = 1 { y = 2; x = x + y; }; return x;", Ok (Just "3"))
                , ("x = 5; { x = 6; y = 1; }; return x;", Ok (Just "6"))
                , ("a = true; b = false; return a = b;", Ok (Just "false"))
                , ("x = 1; affirm x = 1; return x;", Ok (Just "1"))
                , ("x = 1;", Ok (Nothing))
                , ("enum S { A { r: Int }, B }; s = S::A { r: 1 }; a = s as S::A; return a.r;", Ok (Just "1"))
                , ("enum S { A { r: Int }, B }; s = S::A { r: 1 }; a = s as S::A; s = a; return (s as S::A).r;", Ok (Just "1"))
                , ("enum S { A { r: Int }, B }; s = S::A { r: 1 }; return s as S::A;", Ok (Just "S::A { r: 1 }"))
                , ("enum S { A { r: Int }, B }; fn r(c: S::A) -> Int { return c.r; }; s = S::A { r: 4 }; return r(s as S::A);", Ok (Just "4"))
                , ("enum S { A { r: Int }, B }; s = S::B; a = s as S::A; return 1;", Ok (Just "1"))
                , ("fn f(l: &List<Int>) -> Int { return 0; }; { f = size; }; return f([1, 2]);", Ok (Just "2"))
                , ("fn outer(n: Int) -> Int { fn g(m: Int) -> Int { return m; }; fn h(m: Int) -> Int { return m * 10; }; { g = h; }; return g(n); }; return outer(2);", Ok (Just "20"))
                , ("fn a(n: Int) -> Int { return n + 1; }; fn b(n: Int) -> Int { return n + 2; }; f = a; { f = b; }; return f(1) + a(1);", Ok (Just "5"))
                , ("fn a(n: Int) -> Int { return n + 1; }; fn use(n: Int) -> Int { return a(n); }; { a = use; }; return use(1) + a(1);", Ok (Just "4"))
                , ("return [];", Ok (Just "[]"))
                , ("return 1 / 0;", Error "Division by zero")
                , ("return get([1], 3);", Error "Get index out of range")
                , ("fn f(n: Int) -> Int { if n > 0 { return 1; }; }; return f(0);", Error "Function did not return a value")
                , ("return 5 + 6;", Ok (Just "11"))
                ]
        ]

testMir :: Test
testMir =
    TestList
        "testMir"
        [ testMirStructure
        , testMirWellFormed
        , testMirTypes
        , testMirRun
        , testStdlibInTersus
        , testCaseSeq
            "testMirCli"
            ([ -- `mir` prints the blocks
              testAssertEq (runSource Mir "x = 1 + 2; return x;") (Ok (unlines ["fn main() -> Int {", "    let _0: Int;", "    let _1: Int; // x", "    bb0: {", "        _1 = Add(const 1, const 2);", "        _0 = _1;", "        return;", "    }", "}"]))
            ]
                ++ validationFailuresFor ["Mir"])
        ]

-- The standard library is written in Tersus (lib/stdlib.tersus): the contracts the validator is
-- given for a builtin come from that text, and the names a program calls it by are all there.
testStdlibInTersus :: Test
testStdlibInTersus =
    TestCase "the standard library is written in Tersus" $
        pure $
            testAssertTrue
                ( (case stdlibBuiltin Get of
                    VFunct params inputs _ _ exported -> (params, length inputs, exported)
                    _ -> ([], 0, []))
                    == (["list", "index"], 4, [relProof Eq (ATerm "return") (FApp (CTerm (builtinFunct Get)) [ATerm "list", ATerm "index"])])
                    && Map.size stdLibCtx == 31
                    && Map.member "get" stdLibCtx
                    && Map.member "push" stdLibCtx
                )

testMirSelfHosted :: Test
testMirSelfHosted = TestList "testMirSelfHosted"
    [ TestList name
        [ TestCase (show queryIndex) $ do
            compiled <- bootstrapFromFile validationEntry
            pure $ case compiled of
                Error e -> Just ("Could not compile the Tersus validator: " ++ e)
                Ok program -> snd (selfHostedQueryFamilies program !! familyIndex) !! queryIndex
        | queryIndex <- [0 .. count - 1]
        ]
    | (familyIndex, (name, count)) <- zip [0 ..] selfHostedFamilyManifest
    ]

selfHostedFamilyManifest :: [(String, Int)]
selfHostedFamilyManifest =
    [(name, length queries) | (name, queries) <- selfHostedQueryFamilies (error "query metadata forced the validator")]

selfHostedQueryFamilies :: M.Program -> [(String, [TestResult])]
selfHostedQueryFamilies program =
            let fact (a, b) = MData "EqualityFact" [("left", MInt a), ("right", MInt b)]
                terms = [(12, 2, 10, 2), (13, 2, 11, 2), (10, 1, 0, 2), (11, 1, 1, 2), (14, 3, 1, 2)] :: [(Integer, Integer, Integer, Integer)]
                term (i, op, a, b) = MData "BinaryTerm" [("id", MInt i), ("op", MInt op), ("left", MInt a), ("right", MInt b)]
                mixed = [(3, 4, False), (2, 3, True), (1, 2, False)] :: [(Integer, Integer, Bool)]
                mixedFact (a, b, s) = MData "OrderFact" [("smaller", MInt a), ("greater", MInt b), ("strict", MBool s)]
                apps = [(10,20,[0,2]), (11,21,[1,2]), (12,20,[0]), (13,20,[]), (14,21,[])] :: [(Integer,Integer,[Integer])]
                app (i, f, args) = MData "ApplicationTerm" [("id", MInt i), ("function", MInt f), ("arguments", MList (map MInt args))]
                differentFact (a, b) = MData "DisequalityFact" [("left", MInt a), ("right", MInt b)]
                diffFact (a, b, k) = MData "DifferenceFact" [("left", MInt a), ("right", MInt b), ("bound", MInt k)]
                differenceEdges = [(1,2,0),(2,3,-1),(3,4,0)] :: [(Integer,Integer,Integer)]
                overflowEdges = [(1,0,-9223372036854775808),(2,1,-1)] :: [(Integer,Integer,Integer)]
                checkDifferenceOverflow = testAssertEq (runNamedFunction program "hasDifference" [MList [], MList (map diffFact overflowEdges), MInt 2, MInt 0, MInt (-9223372036854775808)]) (Ok (Just (MBool False)))
                checkDifferenceContradiction facts expected = testAssertEq (runNamedFunction program "contradictoryDifferences" [localsValue [], MList (map diffFact facts)]) (Ok (Just (MBool expected)))
                checkProduct a b result = testAssertEq (runNamedFunction program "safeProduct" [MInt a, MInt b]) (Ok (Just result))
                productValues = [-9223372036854775808, -9223372036854775807, -4611686018427387904, -3074457345618258603, -3, -2, -1, 0, 1, 2, 3, 3074457345618258602, 4611686018427387903, 9223372036854775806, 9223372036854775807]
                productResult a b = let n = a * b in if n < -9223372036854775808 || n > 9223372036854775807 then MData "SumResult::Overflow" [] else MData "SumResult::Sum" [("value", MInt n)]
                constants = [(30,0,3),(31,0,3),(32,0,5),(33,0,0),(34,1,0)] :: [(Integer,Integer,Integer)]
                constant (i, k, v) = MData "ConstantTerm" [("id", MInt i), ("kind", MInt k), ("value", MInt v)]
                validatorContext = MData "ValidatorContext" [("equalities", MList [fact (0,1)]), ("applications", MList []), ("constants", MList []), ("orders", MList (map mixedFact mixed)), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                goal name a b = MData ("ValidatorGoal::" ++ name) [("left", MInt a), ("right", MInt b)]
                checkContext name a b expected = testAssertEq (runNamedFunction program "entailsGoal" [validatorContext, goal name a b]) (Ok (Just (MBool expected)))
                boundContext = MData "ValidatorContext" [("equalities", MList []), ("applications", MList (map app [(10,20,[0]),(11,20,[1])])), ("constants", MList []), ("orders", MList (map mixedFact [(0,1,False),(1,0,False)])), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                checkBoundCongruence = testAssertEq (runNamedFunction program "entailsGoal" [boundContext, goal "Equal" 10 11]) (Ok (Just (MBool True)))
                emptyContext = MData "ValidatorContext" [("equalities", MList []), ("applications", MList []), ("constants", MList []), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                checkUnknownGoal = testAssertEq (runNamedFunction program "entailsGoal" [emptyContext, MData "ValidatorGoal::Unknown" []]) (Ok (Just (MBool False)))
                localsValue bindings = MData "HashMap" [("buckets", MList [MList [MData "Entry" [("key", MInt k), ("value", MInt v)] | (k, v) <- bindings]]), ("count", MInt (toInteger (length bindings)))]
                initialExecution = MData "ExecutionState" [("context", emptyContext), ("locals", localsValue []), ("templates", MList [])]
                termRef i = MData "ValueRef::Term" [("term", MInt i)]
                localRef i = MData "ValueRef::Local" [("local", MInt i)]
                assignLocal i ref = MData "ExecutionStep::Assign" [("local", MInt i), ("value", ref)]
                applyLocal local result = MData "ExecutionStep::Apply" [("local", MInt local), ("result", MInt result), ("function", MInt 10), ("arguments", MList [localRef 0])]
                checkLocals = MData "ExecutionStep::Check" [("relation", MInt 0), ("left", localRef 1), ("right", localRef 2)]
                executionSteps = [assignLocal 0 (termRef 1), applyLocal 1 2, applyLocal 2 3, checkLocals]
                checkExecution steps status step = case runNamedFunction program "executeSteps" [initialExecution, MList steps] of
                    Ok (Just (MData "ExecutionResult" fields)) -> testAssertEq (lookup "status" fields, lookup "failedAt" fields) (Just (MInt status), Just (MInt step))
                    result -> Just ("Unexpected execution result: " ++ show result)
                checkTerms relation a b = MData "ExecutionStep::Check" [("relation", MInt relation), ("left", termRef a), ("right", termRef b)]
                assumeTerms a b = MData "ExecutionStep::Assume" [("relation", MInt 0), ("left", termRef a), ("right", termRef b)]
                scoped steps = MData "ExecutionStep::Scoped" [("steps", MList steps)]
                nestScoped n = iterate (\inner -> scoped [inner]) (scoped []) !! (n - 1)
                driverBytes text = MList [MInt (toInteger (fromEnum c)) | c <- text]
                dInt n = MData "DriverValue::DriverInt" [("value", MInt n)]
                dBool b = MData "DriverValue::DriverBool" [("value", MBool b)]
                dList items = MData "DriverValue::DriverList" [("items", MList items)]
                dData name fields = MData "DriverValue::DriverData" [("name", driverBytes name), ("fields", MList fields)]
                dTerm i = dData "ValueRef::Term" [dInt i]
                dLocal i = dData "ValueRef::Local" [dInt i]
                dStep name fields = dData ("ExecutionStep::" ++ name) fields
                dCheck left right = dStep "Check" [dInt 0, left, right]
                dDone = dData "ExecutionEnd::Done" []
                dBlockAt i steps end = dData "ExecutionBlock" [dInt i, steps, end]
                dBlock = dBlockAt 0
                toDriver value = case value of
                    MInt n -> dInt n
                    MBool b -> dBool b
                    MList items -> dList (map toDriver items)
                    MData name fields -> dData name (map (toDriver . snd) fields)
                    other -> other
                driven blocks entry state = case runNamedFunction program "driverValidate" [blocks, MInt entry, toDriver state] of
                    Ok (Just (MData "ExecutionFlowResult" fields)) -> Right (lookup "status" fields)
                    result -> Left ("Unexpected driven validation result: " ++ show result)
                checkDrivenIn state blocks expected = either Just (`testAssertEq` Just (MInt expected)) (driven blocks 0 state)
                checkDriven blocks = checkDrivenIn initialExecution (dList blocks)
                checkDrivenSteps steps = checkDriven [dBlock (dList steps) dDone]
                dNestScoped n = iterate (\inner -> dStep "Scoped" [dList [inner]]) (dStep "Scoped" [dList []]) !! (n - 1)
                checkDrivenDepth n expected = testAssertEq (runNamedFunction program "driverSteps" [dList [dNestScoped n]]) (Ok (Just (MList [expected])))
                onLoop change value = case value of
                    MData "ExecutionEnd::Loop" fields -> MData "ExecutionEnd::Loop" (change fields)
                    MData name fields -> MData name [(key, onLoop change field) | (key, field) <- fields]
                    MList items -> MList (map (onLoop change) items)
                    other -> other
                checkDrivenLoop source change expected = case parseSource source `bindResult` elaborate `bindResult` lowerElaborated of
                    Error e -> Just ("Could not lower test program: " ++ e)
                    Ok mir -> case fmap (lookup "f") (encode mir) of
                        Right (Just (blocks, initial, entry)) -> either Just (`testAssertEq` Just (MInt expected)) (driven (toDriver (onLoop change blocks)) entry initial)
                        other -> Just ("Could not encode test program: " ++ show (fmap (fmap (const ())) other))
                loopSource after = "fn f(n: Int) -> Int { x = 0; i = 0; while i < n [{ affirm i >= 0; }] shrinks n - i { x = 1; i = i + 1; }; " ++ after ++ " return x; }; return 0;"
                setLoopField key value fields = [(k, if k == key then value else v) | (k, v) <- fields]
                appendLoopField key extra fields = [(k, case v of MList items | k == key -> MList (items ++ [extra]); _ -> v) | (k, v) <- fields]
                parsedValue text = case runNamedFunction program "driverParseValue" [driverBytes text, MInt 0] of
                    Ok (Just (MData "DriverParsed" fields)) -> lookup "value" fields
                    _ -> Nothing
                malformed = Just (MData "DriverValue::DriverMalformed" [])
                drivenTexts = parseSource "fn f(x: Int) -> Int { return x; }; return 0;" `bindResult` elaborate `bindResult` lowerElaborated `bindResult` prepareTexts False
                checkDrivenInput edit expected = case drivenTexts of
                    Error e -> Just ("Could not prepare test program: " ++ e)
                    Ok texts -> case runProgramWith (edit (show (length texts) ++ "\n") (concatMap snd texts)) program of
                        Ok (out, _) -> testAssertEq out expected
                        Error e -> Just ("The driver did not run: " ++ e)
                drivenProved = "0 -1 -1 -1\n"
                drivenRefused = "2 -1 -1 0\n"
                drivenContext constantTerms = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [app (10, -8, [0,1])]), ("constants", MList constantTerms), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                drivenState constantTerms = MData "ExecutionState" [("context", drivenContext constantTerms), ("locals", localsValue []), ("templates", MList [])]
                dBooleanBranch value = dData "ExecutionEnd::BooleanBranch" [dInt 1, dInt 2, dInt (-1), value, dTerm 20, dTerm 21]
                checkDrivenBoolean value = checkDrivenIn (drivenState boolConstants) (dList [dBlock (dList []) (dBooleanBranch value), dBlockAt 1 (dList []) dDone, dBlockAt 2 (dList []) dDone])
                checkDrivenConstant zero = checkDrivenIn (drivenState [constant (2, 0, 0), zero]) (dList [dBlock (dList [dCheck (dTerm 1) (dTerm 2)]) dDone])
                dTemplate fields = dStep "AssumeForall" [dData "ForallTemplate" fields]
                dRelation = dData "TemplateRelation" [dInt 0, dInt 0, dInt 0]
                checkSavedComparison function truth relation left right =
                    let comparison = app (10, function, [0,1])
                        bool = constant (20, 1, if truth then 1 else 0)
                        context = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [comparison]), ("constants", MList [bool]), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                        initial = MData "ExecutionState" [("context", context), ("locals", localsValue []), ("templates", MList [])]
                        assume = MData "ExecutionStep::Assume" [("relation", MInt 0), ("left", termRef 10), ("right", termRef 20)]
                        obligation = MData "ExecutionStep::Check" [("relation", MInt relation), ("left", termRef left), ("right", termRef right)]
                     in case runNamedFunction program "executeSteps" [initial, MList [assume, obligation]] of
                            Ok (Just (MData "ExecutionResult" fields)) -> testAssertEq (lookup "status" fields) (Just (MInt 0))
                            result -> Just ("Unexpected saved-comparison result: " ++ show result)
                -- Term 3 is push(1, 2), term 4 is size(1), term 6 is a get of the
                -- old list at term 5 (an index below size(1) with no lower bound),
                -- and term 40 is the same read of the pushed list. Tracing 40 back
                -- to the old list would recover the element fact a push refuses to
                -- carry, so it must happen only with the index proved in range.
                readThroughPushContext extraConstants extraOrders = MData "ValidatorContext" [("equalities", MList []), ("applications", MList (map app [(3, -16, [1, 2]), (4, -13, [1]), (6, -14, [1, 5]), (40, -14, [3, 5])])), ("constants", MList (map constant ((7, 0, 0) : extraConstants))), ("orders", MList (map mixedFact extraOrders)), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [diffFact (5, 4, -1)])]
                checkReadThroughPush extraConstants extraOrders expected =
                    case runNamedFunction program "readThroughSequence" [readThroughPushContext extraConstants extraOrders, MInt 40, MInt 3, MInt 5] of
                        Ok (Just (MData "ValidatorContext" fields)) -> case lookup "applications" fields of
                            Just (MList traced) -> testAssertEq (app (40, -14, [1, 5]) `elem` traced) expected
                            other -> Just ("Unexpected traced applications: " ++ show other)
                        result -> Just ("Unexpected read-through result: " ++ show result)
                execEndDone = MData "ExecutionEnd::Done" []
                execJump i = MData "ExecutionEnd::Jump" [("target", MInt i)]
                execBranch = MData "ExecutionEnd::Branch" [("yes", MInt 1), ("no", MInt 2), ("yesSteps", MList []), ("noSteps", MList [])]
                execBlock i steps end = MData "ExecutionBlock" [("id", MInt i), ("steps", MList steps), ("end", end)]
                joinCheck = MData "ExecutionStep::Check" [("relation", MInt 0), ("left", localRef 1), ("right", localRef 0)]
                execBlocks branchValue = [execBlock 0 [assignLocal 0 (termRef 1)] execBranch, execBlock 1 [assignLocal 1 (termRef 1)] (execJump 3), execBlock 2 [assignLocal 1 (termRef branchValue)] (execJump 3), execBlock 3 [joinCheck] execEndDone]
                execBranchTo yes no = MData "ExecutionEnd::Branch" [("yes", MInt yes), ("no", MInt no), ("yesSteps", MList []), ("noSteps", MList [])]
                -- (variant mode 2 asks nothing at the back edge, and term 5 is the zero)
                execLoopEnd exitBlock bodyBlock regionBlocks = MData "ExecutionEnd::Loop"
                    [ ("exit", MInt exitBlock), ("body", MInt bodyBlock), ("region", MList (map MInt regionBlocks))
                    , ("checks", MList []), ("assumptions", MList []), ("havoc", MList [])
                    , ("relation", MInt 2), ("left", termRef 1), ("right", termRef 2)
                    , ("variant", termRef 1), ("variantMode", MInt 2), ("variantOther", termRef 1)
                    , ("zero", termRef 5), ("variantObject", termRef 1), ("variantFamily", MInt (-1))
                    , ("variantConstructor", MInt (-1)), ("orTests", MList [])
                    ]
                -- A graph the sweep cannot order is refused, never swept in part: a cycle no
                -- loop accounts for, an edge into a loop region past its header, an edge to a
                -- block that is not there, and nested regions the bridge could not have made
                -- (one without its header, one naming a missing block). Containment in the
                -- enclosing region is not checked: a region is the blocks that reach its header.
                unorderedCycleBlocks = [execBlock 0 [] (execJump 1), execBlock 1 [] (execJump 2), execBlock 2 [] (execJump 1)]
                regionEntryBlocks = [execBlock 0 [] execBranch, execBlock 1 [] (execLoopEnd 4 3 [1, 3]), execBlock 2 [] (execJump 3), execBlock 3 [] (execJump 1), execBlock 4 [] execEndDone]
                missingTargetBlocks = [execBlock 0 [] (execJump 9)]
                headerlessRegionBlocks = [execBlock 0 [] (execLoopEnd 2 1 [1]), execBlock 1 [] (execJump 0), execBlock 2 [] execEndDone]
                strayRegionBlocks = [execBlock 0 [] (execLoopEnd 2 1 [0, 1, 9]), execBlock 1 [] (execJump 0), execBlock 2 [] execEndDone]
                -- A loop body of n sequential diamonds (each arm assigns, each join is the
                -- next diamond's branch), then a latch. N = 3n blocks run once, so at most
                -- 2N + 1 arrivals in the round; a walk per path would reach the latch 2^n times.
                diamondLoopBlocks n =
                    execBlock 0 [] (execLoopEnd 90 1 [0 .. 3 * n + 1])
                        : concat [ [ execBlock (3 * k + 1) [] (execBranchTo (3 * k + 2) (3 * k + 3))
                                   , execBlock (3 * k + 2) [assignLocal 1 (termRef 1)] (execJump (3 * k + 4))
                                   , execBlock (3 * k + 3) [assignLocal 1 (termRef 2)] (execJump (3 * k + 4)) ]
                                 | k <- [0 .. n - 1] ]
                        ++ [execBlock (3 * n + 1) [assignLocal 2 (termRef 1)] (execJump 0), execBlock 90 [] execEndDone]
                -- Nested ifs whose joins (6, 7) and one arm (5) are empty jumps: they forward each
                -- arrival to the latch as it is, so nothing in the round is merged.
                forwardedLoopBlocks =
                    [ execBlock 0 [] (execLoopEnd 90 1 [0 .. 8]), execBlock 1 [] (execBranchTo 2 3)
                    , execBlock 2 [assignLocal 1 (termRef 1)] (execBranchTo 4 5), execBlock 3 [assignLocal 1 (termRef 2)] (execJump 7)
                    , execBlock 4 [assignLocal 1 (termRef 2)] (execJump 6), execBlock 5 [] (execJump 6), execBlock 6 [] (execJump 7)
                    , execBlock 7 [] (execJump 8), execBlock 8 [assignLocal 2 (termRef 1)] (execJump 0), execBlock 90 [] execEndDone ]
                loopInitial = MData "ExecutionState" [("context", mergeContext [constant (5, 0, 0)] []), ("locals", localsValue []), ("templates", MList [])]
                -- (the test is term 5 < term 6, which always holds, so a loop is left only
                -- through a later conjunct's edge to its exit)
                execGuardedLoopEnd exitBlock bodyBlock regionBlocks checks assumptions havoc = MData "ExecutionEnd::Loop"
                    [ ("exit", MInt exitBlock), ("body", MInt bodyBlock), ("region", MList (map MInt regionBlocks))
                    , ("checks", MList checks), ("assumptions", MList assumptions), ("havoc", MList (map MInt havoc))
                    , ("relation", MInt 2), ("left", termRef 5), ("right", termRef 6)
                    , ("variant", termRef 1), ("variantMode", MInt 2), ("variantOther", termRef 1)
                    , ("zero", termRef 5), ("variantObject", termRef 1), ("variantFamily", MInt (-1))
                    , ("variantConstructor", MInt (-1)), ("orTests", MList [])
                    ]
                xIsZeroCheck = MData "ExecutionStep::Check" [("relation", MInt 0), ("left", localRef 1), ("right", termRef 5)]
                xIsZeroAssume = MData "ExecutionStep::Assume" [("relation", MInt 0), ("left", localRef 1), ("right", termRef 5)]
                xIsZeroLoop exitBlock bodyBlock regionBlocks = execGuardedLoopEnd exitBlock bodyBlock regionBlocks [xIsZeroCheck] [xIsZeroAssume] [1]
                -- A body that sets x to 7 and leaves through its own exit, where x = 0 is checked:
                -- after the loop, or at the outer loop's back edge when the exit is its latch.
                -- The control leaves with x = 0.
                bodyExitBlocks exitValue = [execBlock 1 [assignLocal 1 (termRef exitValue)] (execBranchTo 2 3), execBlock 2 [assignLocal 1 (termRef 5)] (execJump 0)]
                bodyExitTopBlocks = execBlock 9 [assignLocal 1 (termRef 5)] (execJump 0) : execBlock 0 [] (xIsZeroLoop 3 1 [0, 1, 2]) : bodyExitBlocks 1 ++ [execBlock 3 [xIsZeroCheck] execEndDone]
                bodyExitLatchBlocks exitValue =
                    [ execBlock 9 [assignLocal 1 (termRef 5)] (execJump 10), execBlock 10 [] (xIsZeroLoop 11 0 [10, 0, 1, 2, 3])
                    , execBlock 0 [] (xIsZeroLoop 3 1 [0, 1, 2]) ] ++ bodyExitBlocks exitValue ++ [execBlock 3 [] (execJump 10), execBlock 11 [] execEndDone]
                -- Edges out of a loop that are not its own exit are still refused: to another block
                -- of the outer region, to a missing exit, with the exit the header, or inside the region.
                plainExitLoop exitBlock bodyBlock regionBlocks = execGuardedLoopEnd exitBlock bodyBlock regionBlocks [] [] []
                strayExitBlocks =
                    [ [ execBlock 9 [] (execJump 10), execBlock 10 [] (plainExitLoop 11 0 [10, 0, 1, 2, 3, 4]), execBlock 0 [] (plainExitLoop 3 1 [0, 1, 2])
                      , execBlock 1 [] (execBranchTo 2 4), execBlock 2 [] (execJump 0), execBlock 3 [] (execJump 10)
                      , execBlock 4 [assignLocal 1 (termRef 1)] (execJump 10), execBlock 11 [] execEndDone ]
                    , [execBlock 9 [] (execJump 0), execBlock 0 [] (plainExitLoop 77 1 [0, 1, 2]), execBlock 1 [] (execBranchTo 2 77), execBlock 2 [] (execJump 0)]
                    , [execBlock 9 [] (execJump 0), execBlock 0 [] (plainExitLoop 0 1 [0, 1, 2]), execBlock 1 [] (execBranchTo 2 3), execBlock 2 [] (execJump 0), execBlock 3 [] execEndDone]
                    , [execBlock 9 [] (execJump 0), execBlock 0 [] (plainExitLoop 2 1 [0, 1, 2]), execBlock 1 [] (execBranchTo 2 4), execBlock 2 [] (execJump 0), execBlock 4 [] execEndDone]
                    ]
                exitInitial = MData "ExecutionState" [("context", mergeContext [constant (1, 0, 7), constant (2, 0, 8), constant (5, 0, 0), constant (6, 0, 1)] []), ("locals", localsValue []), ("templates", MList [])]
                checkFlowFrom entry blocks state status = case runNamedFunction program "validateExecution" [MList blocks, MInt entry, state] of
                    Ok (Just (MData "ExecutionFlowResult" fields)) -> testAssertEq (lookup "status" fields) (Just (MInt status))
                    result -> Just ("Unexpected execution flow result: " ++ show result)
                -- Loops left by later conjuncts: three extra conjuncts at the top level, the same
                -- loop as the last statement of an outer loop, k such loops in sequence, and three
                -- nested loops each left straight to the enclosing latch.
                conjunctLoopBlocks = [execBlock 0 [] (execLoopEnd 90 1 [0, 1, 2, 3, 4]), execBlock 1 [] (execBranchTo 2 90), execBlock 2 [] (execBranchTo 3 90), execBlock 3 [] (execBranchTo 4 90), execBlock 4 [assignLocal 2 (termRef 1)] (execJump 0), execBlock 90 [] execEndDone]
                conjunctInOuterBlocks =
                    [ execBlock 10 [] (execLoopEnd 96 0 [10, 0, 1, 2, 3, 4, 95]), execBlock 0 [] (execLoopEnd 95 1 [0, 1, 2, 3, 4]), execBlock 1 [] (execBranchTo 2 95), execBlock 2 [] (execBranchTo 3 95)
                    , execBlock 3 [] (execBranchTo 4 95), execBlock 4 [assignLocal 2 (termRef 1)] (execJump 0), execBlock 95 [assignLocal 3 (termRef 1)] (execJump 10), execBlock 96 [] execEndDone ]
                sequentialConjunctLoops n =
                    concat [ [ execBlock (10 * k) [] (execLoopEnd (10 * k + 9) (10 * k + 1) [10 * k, 10 * k + 1, 10 * k + 2])
                             , execBlock (10 * k + 1) [] (execBranchTo (10 * k + 2) (10 * k + 9))
                             , execBlock (10 * k + 2) [assignLocal 2 (termRef 1)] (execJump (10 * k))
                             , execBlock (10 * k + 9) [assignLocal 3 (termRef 1)] (execJump (if k == n - 1 then 999 else 10 * k + 10)) ]
                           | k <- [0 .. n - 1] ] ++ [execBlock 999 [] execEndDone]
                nestedConjunctLoops =
                    [ execBlock 10 [] (execLoopEnd 99 20 [10, 20, 21, 22, 30, 31, 32, 15, 25]), execBlock 20 [] (execLoopEnd 15 21 [20, 21, 22, 30, 31, 32, 25])
                    , execBlock 21 [] (execBranchTo 22 15), execBlock 22 [] (execJump 30), execBlock 30 [] (execLoopEnd 25 31 [30, 31, 32])
                    , execBlock 31 [] (execBranchTo 32 25), execBlock 32 [assignLocal 2 (termRef 1)] (execJump 30)
                    , execBlock 25 [] (execJump 20), execBlock 15 [] (execJump 10), execBlock 99 [] execEndDone ]
                checkSweepCounts = checkSweepCountsFrom 0
                checkSweepCountsFrom entry blocks expected = case runNamedFunction program "sweepExecution" [MList blocks, MInt entry, loopInitial] of
                    Ok (Just (MData "SweepResult" fields)) -> case lookup "result" fields of
                        Just (MData "ExecutionFlowResult" result) -> testAssertEq (lookup "status" result, lookup "block" result, lookup "arrivals" fields, lookup "merges" fields) expected
                        other -> Just ("Sweep result without a flow result: " ++ show other)
                    result -> Just ("Unexpected sweep result: " ++ show result)
                checkExecutionFlow blocks status blockId = case runNamedFunction program "validateExecution" [MList blocks, MInt 0, initialExecution] of
                    Ok (Just (MData "ExecutionFlowResult" fields)) -> testAssertEq (lookup "status" fields, lookup "block" fields) (Just (MInt status), Just (MInt blockId))
                    result -> Just ("Unexpected execution flow result: " ++ show result)
                checkBooleanBranch constantTerms destinations blocks expected =
                    let context = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [app (10, -8, [0,1])]), ("constants", MList constantTerms), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                        initial = MData "ExecutionState" [("context", context), ("locals", localsValue []), ("templates", MList [])]
                        end = MData "ExecutionEnd::BooleanBranch" [("yes", MInt (fst destinations)), ("no", MInt (snd destinations)), ("join", MInt (-1)), ("value", termRef 10), ("trueValue", termRef 20), ("falseValue", termRef 21)]
                     in case runNamedFunction program "validateExecution" [MList (execBlock 0 [] end : blocks), MInt 0, initial] of
                            Ok (Just (MData "ExecutionFlowResult" fields)) -> testAssertEq (lookup "status" fields) (Just (MInt expected))
                            result -> Just ("Unexpected boolean branch result: " ++ show result)
                checkBooleanJoin rightValue expected =
                    let joinConstants = boolConstants ++ [constant (30, 0, 3), constant (31, 0, rightValue), constant (32, 0, 3)]
                        context = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [app (10, -8, [0,1])]), ("constants", MList joinConstants), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                        initial = MData "ExecutionState" [("context", context), ("locals", localsValue []), ("templates", MList [])]
                        end = MData "ExecutionEnd::BooleanBranch" [("yes", MInt 1), ("no", MInt 2), ("join", MInt 3), ("value", termRef 10), ("trueValue", termRef 20), ("falseValue", termRef 21)]
                        blocks = [execBlock 0 [] end, execBlock 1 [assignLocal 1 (termRef 30)] (execJump 3), execBlock 2 [assignLocal 1 (termRef 31)] (execJump 3), execBlock 3 [MData "ExecutionStep::Check" [("relation", MInt 0), ("left", localRef 1), ("right", termRef 32)]] execEndDone]
                     in case runNamedFunction program "validateExecution" [MList blocks, MInt 0, initial] of
                            Ok (Just (MData "ExecutionFlowResult" fields)) -> testAssertEq (lookup "status" fields) (Just (MInt expected))
                            result -> Just ("Unexpected joined boolean branch result: " ++ show result)
                checkBooleanJoinKnown expected =
                    let joinConstants = boolConstants ++ [constant (0, 0, 1), constant (1, 0, 2), constant (30, 0, 3), constant (31, 0, 4), constant (32, 0, 3)]
                        context = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [app (10, -8, [0,1])]), ("constants", MList joinConstants), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                        initial = MData "ExecutionState" [("context", context), ("locals", localsValue []), ("templates", MList [])]
                        end = MData "ExecutionEnd::BooleanBranch" [("yes", MInt 1), ("no", MInt 2), ("join", MInt 3), ("value", termRef 10), ("trueValue", termRef 20), ("falseValue", termRef 21)]
                        blocks = [execBlock 0 [] end, execBlock 1 [assignLocal 1 (termRef 30)] (execJump 3), execBlock 2 [assignLocal 1 (termRef 31)] (execJump 3), execBlock 3 [MData "ExecutionStep::Check" [("relation", MInt 0), ("left", localRef 1), ("right", termRef 32)]] execEndDone]
                     in case runNamedFunction program "validateExecution" [MList blocks, MInt 0, initial] of
                            Ok (Just (MData "ExecutionFlowResult" fields)) -> testAssertEq (lookup "status" fields) (Just (MInt expected))
                            result -> Just ("Unexpected known boolean join result: " ++ show result)
                boolConstants = [constant (20, 1, 1), constant (21, 1, 0)]
                checkMirSubset input expected =
                    let lowered = parseSource input `bindResult` elaborate `bindResult` lowerElaborated
                     in case lowered of
                            Error e -> Just ("Could not lower test program: " ++ e)
                            Ok mir ->
                                let result = mapResult verdictProved (validateMirSubset program mir)
                                 in case testAssertEq result (Ok expected) of
                                        Just failure -> Just (input ++ ": " ++ failure)
                                        Nothing -> Nothing
                checkMalformedArrayLength =
                    let input = "fn f<n>(a: Array<Int, n>, m: Int) -> Int { b = array(n, 0); return size(b); }; return 0;"
                        lowered = parseSource input `bindResult` elaborate `bindResult` lowerElaborated
                     in case lowered of
                            Error e -> Just ("Could not lower malformed-MIR fixture: " ++ e)
                            Ok mir -> case Map.lookup "f" (M.progFunctions mir) of
                                Nothing -> Just "Fixture has no f function"
                                Just fn -> case [local | (local, decl) <- Map.toList (M.fnLocals fn), M.localName decl == Just "m"] of
                                    [wrong] ->
                                        let alter (M.Assign dest (M.ListOp M.NewArray [_, fill])) = M.Assign dest (M.ListOp M.NewArray [M.Copy wrong, fill])
                                            alter other = other
                                            replace block' = block'{M.blockStatements = map alter (M.blockStatements block')}
                                            broken = fn{M.fnBlocks = Map.map replace (M.fnBlocks fn)}
                                            program' = mir{M.progFunctions = Map.insert "f" broken (M.progFunctions mir)}
                                         in testAssertEq (verifyProgram program') (Ok ()) `orElse` testAssertEq (mapResult verdictProved (validateMirSubset program program')) (Ok Nothing)
                                    _ -> Just "Fixture has no unique m parameter"
                variantFact (object, family, constructor, matches) = MData "VariantFact" [("object", MInt object), ("family", MInt family), ("constructor", MInt constructor), ("matches", MBool matches)]
                variantContext = MData "ValidatorContext" [("equalities", MList []), ("applications", MList []), ("constants", MList []), ("orders", MList []), ("different", MList []), ("variants", MList [variantFact (0, 10, 20, True), variantFact (1, 10, 21, True)]), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                checkVariantGoal name a b expected = testAssertEq (runNamedFunction program "entailsGoal" [variantContext, goal name a b]) (Ok (Just (MBool expected)))
                constructorField = MData "ConstructorField" [("constructor", MInt 100), ("field", MInt 200), ("index", MInt 1)]
                constructorContext = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [app (10, 100, [0, 1]), app (11, 200, [10])]), ("constants", MList []), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList [MInt 200]), ("constructorFunctions", MList [MInt 100]), ("constructorFields", MList [constructorField]), ("differences", MList [])]
                checkConstructorGoal name a b expected = testAssertEq (runNamedFunction program "entailsGoal" [constructorContext, goal name a b]) (Ok (Just (MBool expected)))
                withinGoal a b = MData "ValidatorGoal::Within" [("inner", MInt a), ("outer", MInt b)]
                withinContext = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [app (11, 200, [10]), app (12, 201, [11])]), ("constants", MList []), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList [MInt 200, MInt 201]), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                checkWithin a b expected = testAssertEq (runNamedFunction program "entailsGoal" [withinContext, withinGoal a b]) (Ok (Just (MBool expected)))
                mergeContext constants equalities = MData "ValidatorContext" [("equalities", MList equalities), ("applications", MList []), ("constants", MList constants), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                mergeLeftState = MData "ExecutionState" [("context", mergeContext [constant (10, 0, 3)] [fact (10, 10)]), ("locals", localsValue [(1, 10)]), ("templates", MList [])]
                mergeRightState = MData "ExecutionState" [("context", mergeContext [constant (11, 0, 3)] [fact (11, 11)]), ("locals", localsValue [(1, 11)]), ("templates", MList [])]
                checkCommonContext =
                    let left = mergeContext [] [fact (0, 1), fact (2, 3)]
                        right = mergeContext [] [fact (1, 0), fact (2, 4)]
                        expected = mergeContext [] [fact (0, 1)]
                     in testAssertEq (runNamedFunction program "commonContext" [left, right]) (Ok (Just expected))
                -- (both sides hold 3 in local 1: the merged context says the merged local is 3)
                checkMergeStates = case runNamedFunction program "mergeStates" [mergeLeftState, mergeRightState] of
                    Ok (Just (MData "StateMergeLookup::Found" [("state", MData "ExecutionState" [("context", context), ("locals", mergedLocals), ("templates", _)])])) ->
                        case runNamedFunction program "lookupLocal" [mergedLocals, MInt 1] of
                            Ok (Just (MData "ValueLookup::Found" [("term", MInt found)])) ->
                                testAssertEq (runNamedFunction program "entailsGoal" [context, goal "Equal" found 10]) (Ok (Just (MBool True)))
                            other -> Just ("Merged state malformed: " ++ show other)
                    result -> Just ("Unexpected mergeStates result: " ++ show result)
                -- Structural twins of the merge model's contest cases: a local both sides bind to one
                -- minted id keeps it, and is bounded only when its definition reaches a dropped one, its
                -- own (T1) or through unnamed intermediates (A1, A1b). Their source rows in testIfJoin
                -- do not isolate this: each arm's Add steps state relations of their own.
                contestState = contestStateWith []
                contestStateWith equalities contestApps constantTerms orders bindings = MData "ExecutionState" [("context", MData "ValidatorContext" [("equalities", MList (map fact equalities)), ("applications", MList (map app contestApps)), ("constants", MList (map constant constantTerms)), ("orders", MList (map mixedFact orders)), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]), ("locals", localsValue bindings), ("templates", MList [])]
                checkMergedGoal name leftApps rightApps constantTerms orders bindings goalName a b =
                    case runNamedFunction program "mergeStates" [contestState leftApps constantTerms orders bindings, contestState rightApps constantTerms orders bindings] of
                        Ok (Just (MData "StateMergeLookup::Found" [("state", MData "ExecutionState" (("context", context) : _))])) ->
                            fmap ((name ++ ": ") ++) (testAssertEq (runNamedFunction program "entailsGoal" [context, goal goalName a b]) (Ok (Just (MBool True))))
                        result -> Just (name ++ ": unexpected mergeStates result: " ++ show result)
                -- x = old + 1 / old + 2, t = old + 3 kept, old held by no local: x < t
                checkContestT1 = checkMergedGoal "T1" [(-31, -1, [-30, 10]), (-32, -1, [-30, 12])] [(-31, -1, [-30, 11]), (-32, -1, [-30, 12])] [(10, 0, 1), (11, 0, 2), (12, 0, 3)] [] [(1, 1), (2, -31), (3, -32)] "Less" (-31) (-32)
                -- x = (y + a) + 1 / (y + b) + 1 with a, b >= 0: y < x
                checkContestA1 = checkMergedGoal "A1" [(-30, -1, [1, 2]), (-31, -1, [-30, 10])] [(-30, -1, [1, 3]), (-31, -1, [-30, 10])] [(10, 0, 1), (13, 0, 0)] [(13, 2, False), (13, 3, False)] [(1, 1), (2, 2), (3, 3), (4, -31)] "Less" 1 (-31)
                checkContestA1b = checkMergedGoal "A1b" [(-30, -1, [1, 2]), (-31, -1, [-30, 10]), (-32, -1, [-31, 10])] [(-30, -1, [1, 3]), (-31, -1, [-30, 10]), (-32, -1, [-31, 10])] [(10, 0, 1), (13, 0, 0)] [(13, 2, False), (13, 3, False)] [(1, 1), (2, 2), (3, 3), (4, -32)] "Less" 1 (-32)
                -- T1 with its branch condition -5 kept by local 5: true on the left, false on the right
                conditionConstants = [(8, 1, 1), (9, 1, 0)]
                checkContestT1WithCondition =
                    case runNamedFunction program "mergeStates"
                            [ contestStateWith [(-5, 8)] [(-31, -1, [-30, 10]), (-32, -1, [-30, 12])] ([(10, 0, 1), (11, 0, 2), (12, 0, 3)] ++ conditionConstants) [] [(1, 1), (2, -31), (3, -32), (5, -5)]
                            , contestStateWith [(-5, 9)] [(-31, -1, [-30, 11]), (-32, -1, [-30, 12])] ([(10, 0, 1), (11, 0, 2), (12, 0, 3)] ++ conditionConstants) [] [(1, 1), (2, -31), (3, -32), (5, -5)] ] of
                        Ok (Just (MData "StateMergeLookup::Found" [("state", MData "ExecutionState" (("context", context) : _))])) ->
                            testAssertEq (runNamedFunction program "entailsGoal" [context, goal "Less" (-31) (-32)]) (Ok (Just (MBool True)))
                        result -> Just ("T1 with condition: unexpected mergeStates result: " ++ show result)
                -- x keeps one id, the integer 0 on the left and 1 on the right, beside the condition and
                -- boolean constants of the same values. Only a dropped definition selects a self-pair, and
                -- x's only dropped fact is an equality, so the merge bounds it neither way
                checkIntegerSelfPair goalName a b expected =
                    case runNamedFunction program "mergeStates"
                            [ contestStateWith [(-31, 20), (-5, 8)] [] ((20, 0, 0) : (21, 0, 1) : conditionConstants) [] [(1, -31), (5, -5)]
                            , contestStateWith [(-31, 21), (-5, 9)] [] ((20, 0, 0) : (21, 0, 1) : conditionConstants) [] [(1, -31), (5, -5)] ] of
                        Ok (Just (MData "StateMergeLookup::Found" [("state", MData "ExecutionState" (("context", context) : _))])) ->
                            fmap (("integer self-pair " ++ goalName ++ ": ") ++) (testAssertEq (runNamedFunction program "entailsGoal" [context, goal goalName a b]) (Ok (Just (MBool expected))))
                        result -> Just ("integer self-pair: unexpected mergeStates result: " ++ show result)
                -- Merges read off each side's facts with no solver (addDifferenceHull). Ids follow the
                -- encoder: parameters and literal constants are non-negative, minted terms negative,
                -- and the two arms mint from one state, so one negative id can mean two values. Each
                -- goal names the joined local's term on one side and a merged local or a term on the
                -- other; NEG goals are false on some path of the two sides and must stay unproved.
                hullSide = contestStateWith
                hullMerged (leftSide, rightSide) = case runNamedFunction program "mergeStates" [leftSide, rightSide] of
                    Ok (Just (MData "StateMergeLookup::Found" [("state", MData "ExecutionState" fields)])) -> Right fields
                    other -> Left ("unexpected mergeStates result: " ++ show other)
                hullLocal fields key = case lookup "locals" fields of
                    Just merged -> case runNamedFunction program "lookupLocal" [merged, MInt key] of
                        Ok (Just (MData "ValueLookup::Found" [("term", MInt bound)])) -> Just bound
                        _ -> Nothing
                    Nothing -> Nothing
                checkHull name sides pairKey goals = case hullMerged sides of
                    Left e -> Just (name ++ ": " ++ e)
                    Right fields -> case (lookup "context" fields, hullLocal fields pairKey) of
                        (Just context, Just joined) ->
                            let ask (shape, joinedLeft, other, expected) = case either (hullLocal fields) Just other of
                                    Nothing -> Just (name ++ ": no merged local " ++ show other)
                                    Just otherTerm -> fmap ((name ++ " " ++ shape ++ " " ++ show (joinedLeft, other) ++ ": ") ++)
                                        (testAssertEq (runNamedFunction program "entailsGoal" [context, if joinedLeft then goal shape joined otherTerm else goal shape otherTerm joined]) (Ok (Just (MBool expected))))
                             in foldr (orElse . ask) Nothing goals
                        _ -> Just (name ++ ": the merged state has no context or no joined local")
                hullFacts sides = case hullMerged sides of
                    Right fields | Just (MData _ context) <- lookup "context" fields ->
                        let count listName = case lookup listName context of
                                Just (MList items) -> length items
                                _ -> -1
                         in Just (count "orders", count "differences", count "constants")
                    _ -> Nothing
                quadSides k = ( hullSide [] [] [(-50 - i, 0, i) | i <- [1 .. k]] [] [(i, -50 - i) | i <- [1 .. k]]
                              , hullSide [] [] [(-1000 - i, 0, 1000 + i) | i <- [1 .. k]] [] [(i, -1000 - i) | i <- [1 .. k]] )
                hubSides k = ( hullSide [] [(-50, -1, [1, 31])] [(31, 0, 1), (32, 0, 2)] [(-50, 100 + i, True) | i <- [0 .. k - 1]] ([(1, 1), (4, -50)] ++ [(100 + i, 100 + i) | i <- [0 .. k - 1]])
                             , hullSide [] [(-60, -1, [1, 32])] [(31, 0, 1), (32, 0, 2)] [(-60, 100 + i, True) | i <- [0 .. k - 1]] ([(1, 1), (4, -60)] ++ [(100 + i, 100 + i) | i <- [0 .. k - 1]]) )
                freeLocals = [(71, 71), (72, 72), (73, 73)]
                -- Both arms mint -1000 and -1001 from one state; -1001 is w on the left and v on the
                -- right, and drops out of the merged state. A bound term minted at -1001 would read the
                -- root edge x <= -1001 as x <= 7 or 9.
                freshCollide renamed = ( hullSide [] [(-1000, -1, [1, 31]), (-1001, -1, [-1000, 33])] [(31, 0, 1), (32, 0, 2), (33, 0, 3), (35, 0, 5), (37, 0, 7), (39, 0, 9)] [(35, 1, False), (-1000, -1001, True)] [(1, 1), (4, -1000), (7, -1001)]
                                       , hullSide [] [(right, -1, [1, 32]), (-1001, -1, [right, 39])] [(31, 0, 1), (32, 0, 2), (33, 0, 3), (35, 0, 5), (37, 0, 7), (39, 0, 9)] [(35, 1, False), (right, -1001, False)] [(1, 1), (4, right), (8, -1001)] )
                    where right = if renamed then -1002 else -1000
                freshGoals = [("AtMost", True, Right 37, False), ("AtMost", True, Right 39, False), ("Less", False, Left 1, True)]
                -- A loop candidate is replayed in a state built from the loop's initial state, so
                -- every term id it names has to be one of that state's: an id inference minted
                -- while building the candidate denotes something else, or nothing, where the
                -- candidate is replayed. The pair helpers take the initial context as a parameter,
                -- and these calls give them a work context disjoint from it -- which a real work
                -- context, the initial one plus the scratch terms, never is. That is deliberate:
                -- it is what makes the parameter, rather than st.work.context, the thing the
                -- assertion pins.
                inferContextOf constantTerms = MData "ValidatorContext" [("equalities", MList []), ("applications", MList []), ("constants", MList constantTerms), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                inferSubject local subjectTerm = MData "InferSubject" [("local", MInt local), ("isSize", MBool False), ("temp", MInt 0), ("term", MInt subjectTerm)]
                scratchInferState constantTerms = MData "InferState" [("work", MData "ExecutionState" [("context", inferContextOf constantTerms), ("locals", localsValue [(20, 20), (21, 21)]), ("templates", MList [])]), ("index", MInt 0), ("candIndex", MInt 0), ("assigned", MList []), ("anchors", MList []), ("goals", MList [])]
                replayedTerms value = case value of
                    MData "ValueRef::Term" fields -> [named | Just (MInt named) <- [lookup "term" fields]]
                    MData _ fields -> concatMap (replayedTerms . snd) fields
                    MList items -> concatMap replayedTerms items
                    _ -> []
                inferredGoals result = case result of
                    Ok (Just (MData "InferState" fields)) -> case lookup "goals" fields of
                        Just (MList goals) -> Right (length goals, sort (nub (concatMap replayedTerms goals)))
                        other -> Left ("Inference state without goals: " ++ show other)
                    _ -> Left ("Unexpected inference result: " ++ show result)
                checkPairProvenance name workConstants initialConstants expected =
                    testAssertEq
                        (inferredGoals (runNamedFunction program name [scratchInferState (map constant workConstants), inferContextOf (map constant initialConstants), inferSubject 20 20, inferSubject 21 21, MInt 7, MInt 4]))
                        (Right expected)
                inferredEntryState = MData "ExecutionState" [("context", MData "ValidatorContext" [("equalities", MList []), ("applications", MList []), ("constants", MList (map constant [(1, 0, 0), (2, 0, 1), (3, 0, 3), (4, 0, -1)])), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]), ("locals", localsValue [(1, 3), (2, 4)]), ("templates", MList [])]
                -- The scans inside the phases are reached through no parameter, so the whole
                -- inference is run over an entry state of its own: it has to keep candidates,
                -- and every term they replay has to be one the entry state names. The two
                -- subjects are 4 apart with no constant of 4 to name the distance, so the sum
                -- of ones inference builds for it folds to 2 and records a constant of 2 in the
                -- work state that the entry state does not have; the pair totals 2, which is
                -- the value the last phase then looks a constant up by. A scan reading the work
                -- state finds that minted constant and leaves its id in a candidate, which is
                -- the id this assertion does not allow.
                inferredEntryTerms = case inferredEntryState of
                    MData _ stateFields -> case lookup "context" stateFields of
                        Just (MData _ contextFields) -> case lookup "constants" contextFields of
                            Just (MList entryConstants) -> sort [i | MData "ConstantTerm" fields <- entryConstants, Just (MInt i) <- [lookup "id" fields]]
                            _ -> []
                        _ -> []
                    _ -> []
                checkInferenceProvenance = case runNamedFunction program "inferLoopCandidateGoals" [inferredEntryState, MList [MInt 1, MInt 2], MData "HashSet" [("map", MData "HashMap" [("buckets", MList [MList []]), ("count", MInt 0)])]] of
                    Ok (Just (MList goals)) ->
                        let outside = [replayed | replayed <- sort (nub (concatMap replayedTerms goals)), replayed `notElem` inferredEntryTerms]
                         in (if null goals then Just "Inference kept no loop candidate" else Nothing)
                                `orElse` (if null outside then Nothing else Just ("Candidates replay terms the entry state does not name: " ++ show outside ++ ", named: " ++ show inferredEntryTerms))
                    other -> Just ("Unexpected candidate result: " ++ show other)
                -- A cache threaded through the goals answers each as a fresh cache does, and
                -- the classes it keeps are its own context's, made on the first ask.
                cacheContext equalities = MData "ValidatorContext" [("equalities", MList (map fact equalities)), ("applications", MList (map app [(10,20,[0]),(11,20,[1])])), ("constants", MList (map constant [(30,0,3),(31,0,3),(32,0,5)])), ("orders", MList (map mixedFact [(1,5,True),(2,3,False),(6,4,False)])), ("different", MList [differentFact (3,4)]), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
                aliasedGoals =
                    [ (goal "Equal" 0 1, True), (goal "Equal" 10 11, True), (goal "Less" 7 32, True), (goal "AtMost" 7 31, True)
                    , (goal "Less" 32 7, False), (goal "Less" 0 5, True), (goal "Less" 5 0, False), (goal "Less" 3 4, True)
                    , (goal "Equal" 0 2, False), (goal "Equal" 30 31, True), (goal "Equal" 0 1, True), (goal "Less" 7 32, True) ]
                unaliasedGoals =
                    [ (goal "Equal" 0 1, False), (goal "Equal" 10 11, False), (goal "Less" 7 32, False), (goal "Less" 30 32, True)
                    , (goal "Equal" 30 31, True), (goal "Less" 32 30, False), (goal "Equal" 0 1, False) ]
                cacheField name (MData _ fields) = lookup name fields
                cacheField _ _ = Nothing
                ownClasses context = case (cacheField "equalities" context, cacheField "applications" context, cacheField "constants" context) of
                    (Just equalities, Just applications, Just known) -> case runNamedFunction program "semanticFacts" [equalities, applications, known] of
                        Ok (Just facts) -> case runNamedFunction program "leastClasses" [facts] of
                            Ok (Just classes) -> Just classes
                            _ -> Nothing
                        _ -> Nothing
                    _ -> Nothing
                threadCache cache [] = Right (cache, [])
                threadCache cache ((asked, _) : rest) = case runNamedFunction program "entailsGoalCached" [cache, asked] of
                    Ok (Just answer@(MData "CachedAnswer" _)) -> case (cacheField "holds" answer, cacheField "cache" answer) of
                        (Just (MBool holds), Just next) -> fmap (\(final, answers) -> (final, holds : answers)) (threadCache next rest)
                        other -> Left ("Unexpected cached answer: " ++ show other)
                    other -> Left ("Unexpected cached answer: " ++ show other)
                checkCacheThreaded context expected = case runNamedFunction program "entailmentCache" [context] of
                    Ok (Just start) -> case threadCache start expected of
                        Left e -> Just e
                        Right (final, threaded) ->
                            testAssertEq threaded (map snd expected)
                                `orElse` testAssertEq [runNamedFunction program "entailsGoal" [context, asked] | (asked, _) <- expected] [Ok (Just (MBool holds)) | (_, holds) <- expected]
                                `orElse` testAssertEq (cacheField "plainClassesMade" start, cacheField "plainClassesMade" final) (Just (MBool False), Just (MBool True))
                                `orElse` testAssertEq (fmap Just (cacheField "plainClasses" final)) (Just (ownClasses context))
                    other -> Just ("Unexpected entailment cache: " ++ show other)
             in [ ("products", [checkProduct a b (productResult a b) | a <- productValues, b <- productValues])
                , ("relations",
                      [ checkDifferenceOverflow
                      , checkDifferenceContradiction [(1,2,2),(2,1,-3)] True
                      , checkDifferenceContradiction [(1,2,2),(2,1,-2)] False
                      , checkDifferenceContradiction [(1,2,0),(2,1,0)] False
                      , checkProduct 3 (-4) (MData "SumResult::Sum" [("value", MInt (-12))])
                      , checkProduct (-9223372036854775808) (-1) (MData "SumResult::Overflow" [])
                      , checkProduct 9223372036854775807 2 (MData "SumResult::Overflow" [])
                      , checkProduct (-9223372036854775808) 1 (MData "SumResult::Sum" [("value", MInt (-9223372036854775808))])
                      , checkProduct 3 (-3074457345618258603) (MData "SumResult::Overflow" [])
                      , checkProduct (-3074457345618258603) 3 (MData "SumResult::Overflow" [])
                      , checkProduct (-4611686018427387904) (-2) (MData "SumResult::Overflow" [])
                      , checkProduct (-4611686018427387903) (-2) (MData "SumResult::Sum" [("value", MInt 9223372036854775806)])
                      , checkContext "Equal" 0 1 True, checkContext "Less" 0 4 True, checkContext "AtMost" 0 2 True
                      , checkContext "Different" 0 4 True, checkContext "Less" 4 0 False
                      , checkBoundCongruence
                      , checkUnknownGoal
                      ])
                , ("entailment cache",
                      [ checkCacheThreaded (cacheContext [(0,1),(3,6),(7,30)]) aliasedGoals
                      , checkCacheThreaded (cacheContext []) unaliasedGoals
                      ])
                , ("execution",
                      [ checkExecution executionSteps 0 (-1), checkExecution [assignLocal 0 (localRef 99)] 2 0
                      , checkSavedComparison (-6) True 0 0 1, checkSavedComparison (-6) False 1 0 1
                      , checkSavedComparison (-7) True 1 0 1, checkSavedComparison (-7) False 0 0 1
                      , checkSavedComparison (-8) True 2 0 1, checkSavedComparison (-8) False 3 1 0
                      , checkSavedComparison (-9) True 3 0 1, checkSavedComparison (-9) False 2 1 0
                      , checkSavedComparison (-10) True 2 1 0, checkSavedComparison (-10) False 3 0 1
                      , checkSavedComparison (-11) True 3 1 0, checkSavedComparison (-11) False 2 0 1
                      , checkExecution (executionSteps ++ [applyLocal 3 2]) 2 4
                      , checkExecutionFlow (execBlocks 1) 0 3, checkExecutionFlow (execBlocks 2) 1 3
                      , checkBooleanBranch (boolConstants ++ [constant (0,0,1), constant (1,0,2)]) (1,99) [execBlock 1 [] execEndDone] 0
                      , checkBooleanBranch (boolConstants ++ [constant (0,0,2), constant (1,0,1)]) (99,1) [execBlock 1 [] execEndDone] 0
                      , checkBooleanBranch (boolConstants ++ [constant (0,0,1), constant (1,0,2)]) (99,1) [execBlock 1 [] execEndDone] 3
                      , checkBooleanBranch boolConstants (1,99) [execBlock 1 [] execEndDone] 3
                      , checkExecutionFlow unorderedCycleBlocks 3 0, checkExecutionFlow regionEntryBlocks 3 0
                      , checkExecutionFlow missingTargetBlocks 3 0, checkExecutionFlow headerlessRegionBlocks 3 0
                      , checkExecutionFlow strayRegionBlocks 3 0
                      , checkSweepCounts (diamondLoopBlocks 8) (Just (MInt 0), Just (MInt 90), Just (MInt 35), Just (MInt 7))
                      , checkSweepCounts (diamondLoopBlocks 16) (Just (MInt 0), Just (MInt 90), Just (MInt 67), Just (MInt 15))
                      , checkSweepCounts forwardedLoopBlocks (Just (MInt 0), Just (MInt 90), Just (MInt 9), Just (MInt 0))
                      , checkFlowFrom 9 bodyExitTopBlocks exitInitial 1, checkFlowFrom 9 (bodyExitLatchBlocks 1) exitInitial 1
                      , checkFlowFrom 9 (bodyExitLatchBlocks 5) exitInitial 0
                      ] ++ [checkFlowFrom 9 blocks exitInitial 3 | blocks <- strayExitBlocks] ++
                      [ checkSweepCounts conjunctLoopBlocks (Just (MInt 0), Just (MInt 90), Just (MInt 9), Just (MInt 0))
                      , checkSweepCountsFrom 10 conjunctInOuterBlocks (Just (MInt 0), Just (MInt 96), Just (MInt 10), Just (MInt 0))
                      , checkSweepCounts (sequentialConjunctLoops 4) (Just (MInt 0), Just (MInt 999), Just (MInt 21), Just (MInt 4))
                      , checkSweepCounts (sequentialConjunctLoops 8) (Just (MInt 0), Just (MInt 999), Just (MInt 41), Just (MInt 8))
                      , checkSweepCountsFrom 10 nestedConjunctLoops (Just (MInt 0), Just (MInt 99), Just (MInt 9), Just (MInt 0))
                      , checkBooleanBranch boolConstants (1,2) [execBlock 1 [] execEndDone, execBlock 2 [joinCheck] execEndDone] 2
                      , checkBooleanJoin 3 0, checkBooleanJoin 4 1, checkBooleanJoinKnown 0
                      , checkExecution [scoped [assumeTerms 1 2, checkTerms 0 1 2]] 0 (-1)
                      , checkExecution [assignLocal 0 (termRef 1), scoped [checkTerms 0 1 2]] 1 1
                      , checkExecution [scoped [assumeTerms 1 2], checkTerms 0 1 2] 1 1
                      , checkExecution [assignLocal 0 (termRef 1), scoped [assignLocal 1 (localRef 99)]] 2 1
                      , checkExecution [nestScoped 16] 0 (-1), checkExecution [nestScoped 17] 2 0
                      , checkReadThroughPush [] [] False
                      , checkReadThroughPush [] [(7, 5, False)] True
                      , checkReadThroughPush [(5, 0, -1), (4, 0, 2)] [] False
                      , checkExecution [MData "ExecutionStep::Unsupported" []] 2 0
                      ])
                , ("driver",
                      [ checkDrivenSteps [dStep "Assign" [dInt 0, dTerm 1], dCheck (dLocal 0) (dTerm 1)] 0
                      , checkDrivenSteps [dStep "Frobnicate" [dInt 0]] 2
                      , checkDrivenSteps [dStep "Havoc" [dInt 5, dInt 6]] 2
                      , checkDrivenSteps [dStep "Havoc" []] 2
                      , checkDrivenSteps [dStep "Assign" [dInt 0, dData "ValueRef::Frobnicate" [dInt 1]]] 2
                      , checkDrivenSteps [dStep "Assign" [dInt 0, dData "ValueRef::Term" []]] 2
                      , checkDriven [dBlock (dList []) (dData "ExecutionEnd::Frobnicate" [])] 2
                      , checkDriven [dBlock (dList []) (dData "ExecutionEnd::Jump" [])] 2
                      , checkDriven [dBlock (dInt 0) dDone] 2
                      , checkDriven [dData "ExecutionBlock" [dInt 0, dList [], dDone, dInt 0]] 2
                      , checkDrivenSteps [dStep "Scoped" [dList [dCheck (dTerm 1) (dTerm 1)]]] 0
                      , checkDrivenSteps [dStep "Scoped" [dList [dStep "Assume" [dInt 0, dTerm 1, dTerm 2]]], dCheck (dTerm 1) (dTerm 2)] 1
                      , checkDrivenLoop (loopSource "") id 0, checkDrivenLoop (loopSource "affirm x = 0;") id 1
                      , checkDrivenLoop (loopSource "") (++ [("extra", MInt 0)]) 2
                      , checkDrivenLoop (loopSource "affirm x = 0;") (setLoopField "havoc" (MInt 0)) 2
                      , checkDrivenSteps [dTemplate [dInt 0, dList [], dList [], dRelation]] 0
                      , checkDrivenSteps [dTemplate [dInt 0, dList [], dList []]] 2
                      , checkDrivenSteps [dStep "ApplyFresh" [dInt 0, dInt 7, dList [dTerm 1, dTerm 2]]] 0
                      , checkDrivenSteps [dStep "ApplyFresh" [dInt 0, dInt 7, dList [dTerm 1, dInt 2]]] 2
                      , checkDrivenBoolean (dTerm 10) 0, checkDrivenBoolean (dData "ValueRef::Term" [dInt 10, dInt 11]) 2
                      , checkDrivenConstant (constant (1, 0, 0)) 0
                      , checkDrivenConstant (MData "ConstantTerm" [("id", MInt 1), ("kind", MInt 0)]) 2
                      , checkDrivenConstant (MData "ConstantTerm" [("id", MInt 1), ("kind", MInt 0), ("value", MBool False)]) 2
                      , checkDrivenSteps [dStep "Assume" [dInt 0, dTerm 1, dTerm 2], dCheck (dTerm 1) (dTerm 2)] 0
                      , checkDrivenSteps [dStep "Assume" [dBool False, dTerm 1, dTerm 2], dCheck (dTerm 1) (dTerm 2)] 2
                      , checkDrivenSteps [dStep "Havoc" [dInt 0]] 0
                      , checkDrivenSteps [dStep "Havoc" [dBool False]] 2
                      , checkDrivenLoop (loopSource "") (appendLoopField "havoc" (MInt 0)) 0
                      , checkDrivenLoop (loopSource "") (appendLoopField "havoc" (MBool False)) 2
                      , testAssertEq (parsedValue "i 7") (Just (dInt 7))
                      , testAssertEq (parsedValue "i x") (Just (MData "DriverValue::DriverMalformed" []))
                      , testAssertEq (parsedValue "") (Just (MData "DriverValue::DriverMalformed" []))
                      , testAssertEq (parsedValue "l 1 i 7") (Just (dList [dInt 7]))
                      , testAssertEq (parsedValue "l x") malformed
                      , testAssertEq (parsedValue "d n 1 a 0") (Just (dData "a" []))
                      , testAssertEq (parsedValue "d n - 0") malformed
                      , testAssertEq (parsedValue "d n 1 a x") malformed
                      , checkDrivenInput (++) drivenProved
                      , checkDrivenInput (\count body -> count ++ body ++ "\n \n") drivenProved
                      , checkDrivenInput (\count body -> count ++ body ++ "i 0 ") drivenRefused
                      , checkDrivenInput (\_ _ -> "") drivenRefused
                      , checkDrivenInput (\count body -> count ++ dropWhile (/= '\n') body) drivenRefused
                      , checkDrivenDepth 16 (nestScoped 16)
                      , checkDrivenDepth 17 (iterate (\inner -> scoped [inner]) (MData "ExecutionStep::Unsupported" []) !! 16)
                      ])
                , ("MIR contracts",
                      [ checkMirSubset "x = 1; y = x; affirm y = 1; return y;" (Just True)
                      , checkMirSubset "x = 1; affirm x = 2; return x;" (Just False)
                      , checkMirSubset "x = 5; below = x < 6; affirm below = true; return 0;" (Just True)
                      , checkMirSubset "x = 5; below = x < 6; affirm below = false; return 0;" (Just False)
                      , checkMirSubset "x = 5; below = x < 6; affirm below != false; return 0;" (Just True)
                      , checkMirSubset "x = 5; below = x < 6; affirm below != true; return 0;" (Just False)
                      , checkMirSubset "x = 5; below = x > 6; affirm below != true; return 0;" (Just True)
                      , checkMirSubset "x = 5; below = x > 6; affirm below != false; return 0;" (Just False)
                      , checkMirSubset "flag = false; affirm flag != true; return 0;" (Just True)
                      , checkMirSubset "flag = true; affirm flag != true; return 0;" (Just False)
                      , checkMirSubset "affirm true != false; return 0;" (Just True)
                      , checkMirSubset "affirm false != false; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int { affirm x = x; return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int { affirm x = 0; return x; }; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int { return 1 / x; }; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int, y: Int) -> Int { if x < y { affirm x < y; } else { affirm y <= x; }; return 0; }; return 0;" (Just True)
                      , checkMirSubset "fn f(flag: Bool) -> Int { y = 0; if flag { y = 1; } else { y = 2; }; affirm y > 0; return y; }; return f(true);" (Just True)
                      , checkMirSubset "fn f(flag: Bool) -> Int { y = 0; if flag { y = 1; } else { y = 2; }; affirm y > 1; return y; }; return f(true);" (Just False)
                      , checkMirSubset "fn f(x: Int, y: Int) -> Int { if x < y { return 0; } else { affirm x < y; }; return 0; }; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x >= 0; }] { return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return >= 0; }] { return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return > 0; }] { return x; }; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return + 1 > 0; }] { return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x + 1 > 0; }] [{ affirm return = x + 1; }] { return x + 1; }; return f(1);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x / 1 > 0; }] { return x; }; return f(1);" (Just True)
                      , checkMirSubset "fn f(x: Int, y: Int) -> Int [{ affirm x / y > 0; }] { return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(xs: List<Int>) -> Int [{ affirm size(xs) > 0; }] [{ affirm return = get(xs, 0); }] { return get(xs, 0); }; return f([5]);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int shrinks x { return x; }; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int { return x; }; return f(1);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int { return x; }; a = f(1); b = f(1); affirm a = b; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int { return x; }; a = f(1); b = f(2); affirm a = b; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int { return x; }; fn g(x: Int) -> Int { return x; }; a = f(1); b = g(1); affirm a = b; return 0;" (Just False)
                      , checkMirSubset "fn f() -> Int { return readByte(); }; a = f(); b = f(); affirm a = b; return 0;" (Just False)
                      , checkMirSubset "fn f() -> Int { return fileStore(); }; a = f(); b = f(); affirm a = b; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Byte) -> Int { return storeByte(x); }; a = f(toByte(65)); b = f(toByte(65)); affirm a = b; return 0;" (Just False)
                      -- (a proof cannot name a function whose result the world gives, so
                      -- it cannot make two of its calls one value either)
                      , checkMirSubset "fn f() -> Int { return fileStore(); }; affirm f() = f(); return 0;" Nothing
                      , checkMirSubset "fn f(x: Byte) -> Int { return storeByte(x); }; affirm f(toByte(65)) = f(toByte(65)); return 0;" Nothing
                      -- (naming it through a local is naming it: the set grows over every
                      -- function a body names, not only over the callees of its calls)
                      , checkMirSubset "fn f() -> Int { return fileStore(); }; fn g() -> Int { h = f; return h(); }; affirm g() = g(); return 0;" Nothing
                      , checkMirSubset "fn f() -> Int { return readByte(); }; fn g() -> Int { h = f; return h(); }; affirm g() = g(); return 0;" Nothing
                      , checkMirSubset "fn f(x: Byte) -> Int { return storeByte(x); }; fn g(x: Byte) -> Int { h = f; return h(x); }; affirm g(toByte(65)) = g(toByte(65)); return 0;" Nothing
                      , checkMirSubset "fn f() -> Int { return fileStore(); }; fn g() -> Int { h = f; return h(); }; fn k() -> Int { return g(); }; affirm k() = k(); return 0;" Nothing
                      -- (a wrapper that names only a pure function still has one value per argument)
                      , checkMirSubset "fn f(x: Int) -> Int { return x + 1; }; fn g(x: Int) -> Int { h = f; return h(x); }; affirm g(3) = g(3); return 0;" (Just True)
                      , checkMirSubset "a = fileStore(); b = fileStore(); affirm a = b; return 0;" (Just False)
                      , checkMirSubset "a = fileStore(); affirm a >= 0 - 1; affirm a <= 0; return 0;" (Just True)
                      , checkMirSubset "a = pathByte(toByte(65)); b = pathByte(toByte(65)); affirm a = b; return 0;" (Just False)
                      -- (a byte added to a path or to a file gives the length so far, not the byte)
                      , checkMirSubset "a = pathByte(toByte(65)); affirm a = 65; return 0;" (Just False)
                      , checkMirSubset "a = pathByte(toByte(65)); affirm a >= 0; return 0;" (Just True)
                      , checkMirSubset "a = storeByte(toByte(65)); b = storeByte(toByte(65)); affirm a = b; return 0;" (Just False)
                      , checkMirSubset "a = storeByte(toByte(65)); affirm a = 65; return 0;" (Just False)
                      , checkMirSubset "a = storeByte(toByte(65)); affirm a >= 0; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > 0; }] { return x; }; return f(1);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > 0; }] { return x; }; return f(0);" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int [{ }] [{ affirm return = x; }] { return x; }; x = 3; x = f(x); affirm x = 3; return x;" (Just True)
                      -- (a reassigned parameter is its entry value in the output contract: refused, return is 2 and x was 1)
                      , checkMirSubset "fn f(x: Int) -> Int [{ }] [{ affirm return = x; }] { x = 2; return x; }; return f(1);" (Just False)
                      , checkMirSubset "fn g() -> Int [{ }] [{ affirm return = 2; }] { return 2; }; fn f(x: Int) -> Int [{ }] [{ affirm return = x; }] { x = g(); return x; }; return f(1);" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int [{ }] [{ affirm return > 0; }] { return x; }; return f(1);" (Just False)
                      , checkMirSubset "fn yes() -> Bool [{ }] [{ affirm return = true; }] { return true; }; flag = yes(); if flag { return 1; } else { affirm 0 = 1; return 0; };" (Just True)
                      , checkMirSubset "fn g(x: Int) -> Int [{ }] [{ affirm return = x; }] { return x; }; fn f(x: Int) -> Int [{ }] [{ affirm return = x; }] { return g(x); }; return f(2);" (Just True)
                      , checkMirSubset "fn g(x: Int) -> Int [{ affirm x > 0; }] { return x; }; fn f(x: Int) -> Int { return g(x); }; return f(1);" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int { return f(x); }; return f(1);" (Just False)
                      ])
                , ("MIR arithmetic",
                      [ checkMirSubset "return 7 / 1;" (Just True)
                      , checkMirSubset "return 7 / 0;" (Just False)
                      , checkMirSubset "x = 1; y = x + 1; affirm y = 2; return y;" (Just True)
                      , checkMirSubset "x = 1; y = x + 1; affirm y = 3; return y;" (Just False)
                      , checkMirSubset "x = 3; y = x - 1; affirm y = 2; return y;" (Just True)
                      , checkMirSubset "x = 1; affirm x + 1 = 2; return x;" (Just True)
                      , checkMirSubset "x = 1; affirm x + 1 = 3; return x;" (Just False)
                      , checkMirSubset "b = Box::new(3); x = Box::unbox(b); affirm x = 3; return x;" (Just True)
                      , checkMirSubset "b = Box::new(3); x = Box::unbox(b); affirm x = 4; return x;" (Just False)
                      , checkMirSubset "b = Box::new(Box::new(3)); x = Box::unbox(Box::unbox(b)); affirm x = 3; return x;" (Just True)
                      , checkMirSubset "x = 5; y = x * 1; affirm y = 5; return y;" (Just True)
                      , checkMirSubset "x = 5; y = 1 * x; affirm y = 5; return y;" (Just True)
                      , checkMirSubset "x = 5; y = x * 0; affirm y = 0; return y;" (Just True)
                      , checkMirSubset "x = 5; y = 0 * x; affirm y = 1; return y;" (Just False)
                      , checkMirSubset "x = 5; y = x / 1; affirm y = 5; return y;" (Just True)
                      , checkMirSubset "x = -7; y = x / 3; affirm y = -3; return y;" (Just True)
                      , checkMirSubset "x = -7; y = x % 3; affirm y = 2; return y;" (Just True)
                      , checkMirSubset "x = 7; y = x / -3; affirm y = -3; return y;" (Just True)
                      , checkMirSubset "x = 7; y = x % -3; affirm y = -2; return y;" (Just True)
                      , checkMirSubset "x = 3; y = x * 4; affirm y = 12; return y;" (Just True)
                      , checkMirSubset "x = 3; y = x * 4; affirm y = 13; return y;" (Just False)
                      , checkMirSubset "x = -3; y = x * 4; affirm y = -12; return y;" (Just True)
                      ])
                , ("MIR sequences",
                      [ checkMirSubset "xs = [1, 2]; affirm size(xs) = 2; return size(xs);" (Just True)
                      , checkMirSubset "xs = [1, 2]; affirm size(xs) = 3; return size(xs);" (Just False)
                      , checkMirSubset "xs = []; affirm size(xs) = 0; return 0;" (Just True)
                      , checkMirSubset "xs = [[1], [2, 3]]; affirm size(xs) = 2; return size(xs);" (Just True)
                      , checkMirSubset "xs = [4, 5]; x = get(xs, 1); affirm x = 5; return x;" (Just True)
                      , checkMirSubset "xs = [4, 5]; affirm get(xs, 0) = 4; return 0;" (Just True)
                      , checkMirSubset "xs = [4, 5]; affirm get(xs, 0) = 5; return 0;" (Just False)
                      , checkMirSubset "xs = [4, 5]; return get(xs, 2);" (Just False)
                      , checkMirSubset "xs = [4, 5]; return get(xs, -1);" (Just False)
                      , checkMirSubset "xs = #[4, 5]; affirm size(xs) = 2; affirm get(xs, 1) = 5; return 0;" (Just True)
                      , checkMirSubset "xs = #[4, 5]; return get(xs, 2);" (Just False)
                      , checkMirSubset "xs = Box::new(#[4, 5]); affirm get(xs, 0) = 4; return size(xs);" (Just True)
                      , checkMirSubset "a = array(3, 7); affirm size(a) = 3; affirm get(a, 1) = 7; return get(a, 2);" (Just True)
                      , checkMirSubset "a = array(3, 7); affirm last(a) = 7; return 0;" (Just True)
                      , checkMirSubset "a = array(3, 7); affirm last(a) = 8; return 0;" (Just False)
                      , checkMirSubset "a = array(3, 7); a = set(a, 0, 9); affirm last(a) = 7; return 0;" (Just True)
                      , checkMirSubset "a = array(3, 7); a = set(a, 2, 9); affirm last(a) = 9; return 0;" (Just True)
                      , checkMirSubset "a = array(3, 7); affirm get(a, 1) = 8; return 0;" (Just False)
                      , checkMirSubset "a = array(0, 7); return get(a, 0);" (Just False)
                      , checkMirSubset "a = Array::boxed(2, 7); affirm get(a, 1) = 7; return size(a);" (Just True)
                      , checkMirSubset "a = array(3, 7); a = set(a, 0, 9); affirm get(a, 1) = 7; return get(a, 0);" (Just True)
                      , checkMirSubset "a = array(3, 7); a = set(a, 0, 9); affirm get(a, 1) = 9; return 0;" (Just False)
                      , checkMirSubset "a = array(3, 7); a = set(a, 0, 9); a = set(a, 2, 8); affirm get(a, 0) = 9; affirm get(a, 1) = 7; affirm get(a, 2) = 8; return 0;" (Just True)
                      , checkMirSubset "n = -1; a = Array::boxed(n, 7); return 0;" (Just False)
                      , checkMirSubset "a = Array::empty(); affirm size(a) = 0; return size(a);" (Just True)
                      , checkMirSubset "a = Array::empty(); return get(a, 0);" (Just False)
                      , checkMirSubset "affirm get(array(2, 7), 0) = 7; return 0;" (Just True)
                      , checkMirSubset "xs = [4, 5]; affirm first(xs) = 4; return first(xs);" (Just True)
                      , checkMirSubset "xs = []; return first(xs);" (Just False)
                      , checkMirSubset "xs = [4, 5]; affirm last(xs) = 5; return last(xs);" (Just True)
                      , checkMirSubset "xs = [4, 5]; affirm last(xs) = 4; return 0;" (Just False)
                      , checkMirSubset "xs = []; return last(xs);" (Just False)
                      ])
                , ("MIR data",
                      [ checkMirSubset "struct P { x: Int }; p = P { x: 4 }; affirm p.x = 4; return p.x;" (Just True)
                      , checkMirSubset "struct P { x: Int }; p = P { x: 4 }; affirm p.x = 5; return p.x;" (Just False)
                      , checkMirSubset "struct P { x: Int }; p = P { x: 4 }; b = Box::new(p); affirm b.x = 4; return b.x;" (Just True)
                      , checkMirSubset "struct P { x: Int }; p = P { x: 4 }; p = P { x: p.x + 1 }; affirm p.x = 5; return p.x;" (Just True)
                      , checkMirSubset "struct P { x: Int }; p = P { x: 4 }; q = p; p = P { x: 5 }; affirm q.x = 4; return q.x;" (Just True)
                      , checkMirSubset "struct P { x: Int }; p = P { x: 4 }; q = P { x: 4 }; affirm p = q; return 0;" (Just True)
                      , checkMirSubset "struct P { x: Int } invariant [{ affirm x >= 0; }]; p = P { x: 4 }; return p.x;" (Just True)
                      , checkMirSubset "struct P { x: Int } invariant [{ affirm x >= 0; }]; p = P { x: -1 }; return p.x;" (Just False)
                      , checkMirSubset "struct P { x: Int, y: Int } invariant [{ affirm x <= y; }]; p = P { x: 2, y: 3 }; return p.x;" (Just True)
                      , checkMirSubset "struct P { x: Int, y: Int } invariant [{ affirm x <= y; }]; p = P { x: 3, y: 2 }; return p.x;" (Just False)
                      , checkMirSubset "struct P { x: Int } invariant [{ affirm x >= 0; }]; fn f(p: P) -> Int [{ }] [{ affirm return >= 0; }] { return p.x; }; p = P { x: 4 }; return f(p);" (Just True)
                      , checkMirSubset "struct P { x: Int } invariant [{ affirm x >= 0; }]; fn f(p: P) -> Int { affirm p.x < 0; return 0; }; return 0;" (Just False)
                      , checkMirSubset "fn f(a: Array<Int, 2>) -> Int { affirm size(a) = 2; return get(a, 1); }; return 0;" (Just True)
                      , checkMirSubset "fn f<n>(a: Array<Int, n>) -> Int { affirm size(a) = n; return n; }; return f(#[1, 2]);" (Just True)
                      , checkMirSubset "fn f<n>(a: Array<Int, n>) -> Int [{ affirm n > 0; }] { return get(a, 0); }; return f(#[1]);" (Just True)
                      , checkMirSubset "fn f<n>(a: Array<Int, n>) -> Int [{ affirm n > 0; }] { return get(a, 0); }; return f(#[]);" (Just False)
                      , checkMalformedArrayLength
                      , checkMirSubset "enum E { A, B }; return E::A;" (Just True)
                      , checkMirSubset "extern fn labs(x: Int) -> Int [{ }] [{ affirm return >= 0; }]; a = labs(0 - 3); affirm a >= 0; return a;" (Just True)
                      , checkMirSubset "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); x = Addr::get(p, 0, b); return x + Addr::free(p, b);" (Just False)
                      , checkMirSubset "x = I32::from(3); return toInt(x);" (Just True)
                      ])
                , ("MIR list updates",
                      [ checkMirSubset "xs = [4]; xs = push(xs, 5); affirm size(xs) = 2; affirm get(xs, 1) = 5; return 0;" (Just True)
                      , checkMirSubset "xs = [4]; xs = push(xs, 5); affirm get(xs, 1) = 4; return 0;" (Just False)
                      , checkMirSubset "xs = []; xs = push(xs, 5); affirm size(xs) = 1; return get(xs, 0);" (Just True)
                      , checkMirSubset "xs = [4]; xs = push(xs, 5); affirm get(xs, 0) = 4; return 0;" (Just True)
                      , checkMirSubset "xs = [4]; xs = push(push(xs, 5), 6); affirm get(xs, 0) = 4; affirm get(xs, 1) = 5; return 0;" (Just True)
                      , checkMirSubset "xs = [4]; affirm size(push(xs, 5)) = 2; affirm get(push(xs, 5), 1) = 5; return 0;" (Just True)
                      , checkMirSubset "xs = [4]; xs = push(xs, 5); affirm last(xs) = 5; return 0;" (Just True)
                      , checkMirSubset "xs = [4, 5]; xs = pop(xs); affirm size(xs) = 1; affirm get(xs, 0) = 4; return 0;" (Just True)
                      , checkMirSubset "xs = [4, 5]; xs = pop(xs); affirm get(xs, 0) = 5; return 0;" (Just False)
                      , checkMirSubset "xs = [4, 5]; xs = pop(xs); return get(xs, 1);" (Just False)
                      , checkMirSubset "xs = []; xs = pop(xs); return 0;" (Just False)
                      , checkMirSubset "xs = [4, 5]; affirm size(pop(xs)) = 1; return get(pop(xs), 0);" (Just True)
                      , checkMirSubset "xs = [4]; xs = push(xs, 5); xs = pop(xs); affirm size(xs) = 1; affirm get(xs, 0) = 4; return 0;" (Just True)
                      , checkMirSubset "xs = [4, 5]; xs = set(xs, 1, 9); affirm size(xs) = 2; affirm get(xs, 0) = 4; affirm get(xs, 1) = 9; return 0;" (Just True)
                      , checkMirSubset "xs = [4, 5]; xs = set(xs, 1, 9); affirm get(xs, 1) = 5; return 0;" (Just False)
                      , checkMirSubset "xs = [4, 5]; xs = set(xs, 2, 9); return 0;" (Just False)
                      , checkMirSubset "xs = #[4, 5]; xs = set(xs, 0, 9); affirm get(xs, 1) = 5; return get(xs, 0);" (Just True)
                      , checkMirSubset "xs = [4, 5]; affirm get(set(xs, 1, 9), 1) = 9; return 0;" (Just True)
                      , checkMirSubset "affirm 1 / 0 = 1; return 0;" (Just False)
                      ])
                , ("MIR branches",
                      [ checkMirSubset "x = 1; if x = 1 { return 1; } else { return 2; };" (Just True)
                      , checkMirSubset ("x = 1; " ++ concat (replicate 8 "if x = 1 { x = 1; } else { x = 1; }; ") ++ "affirm x = 1; return x;") (Just True)
                      , checkMirSubset "x = 1; if x = 1 { affirm x = 2; } else { return 0; }; return 1;" (Just False)
                      , checkMirSubset "flag = true; if flag { return 1; } else { affirm 0 = 1; return 0; };" (Just True)
                      , checkMirSubset "flag = false; if flag { affirm 0 = 1; return 0; } else { return 1; };" (Just True)
                      , checkMirSubset "flag = true; if flag { affirm 0 = 1; }; return 0;" (Just False)
                      , checkMirSubset "x = 1; flag = x < 2; if flag { affirm flag = true; } else { affirm flag = false; }; return 0;" (Just True)
                      , checkMirSubset "a = 1; b = 2; flag = a < b; if true { a = 1; } else { a = 1; }; if flag { affirm a < b; }; return 0;" (Just True)
                      , checkMirSubset "a = 1; b = 2; flag = a < b; if true { a = 3; } else { a = 3; }; if flag { affirm a < b; }; return 0;" (Just False)
                      , checkMirSubset "x = 1; y = 2; flag = x < y; x = 3; if flag { affirm x < y; }; return 0;" (Just False)
                      , checkMirSubset "x = 1; if x != 0 { return 3 / x; } else { return 0; };" (Just True)
                      , checkMirSubset "x = 0; if x != 0 { return 3 / x; } else { return 0; };" (Just True)
                      , checkMirSubset "x = 1; flag = x != 0; x = 0; if flag { return 3 / x; } else { return 0; };" (Just False)
                      , checkMirSubset "x = 1; y = 2; if x < y { x = 3; } else { x = 3; }; affirm x = 3; return x;" (Just True)
                      ])
                , ("MIR loops",
                      [ checkMirSubset "i = 2; while i > 0 [{ affirm i >= 0; }] shrinks i { i = i - 1; }; affirm i = 0; return i;" (Just True)
                      , checkMirSubset "i = 2; while i > 0 [{ }] shrinks i { i = i - 1; }; return i;" (Just True)
                      , checkMirSubset "fn scale(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > 0; }] { return 2 * x; }; return scale(3);" (Just True)
                      , checkMirSubset "fn scale(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] { return 2 * x; }; return scale(3);" (Just True)
                      , checkMirSubset "i = 2; while i > 0 [{ affirm i >= 1; }] shrinks i { i = i - 1; }; return i;" (Just False)
                      , checkMirSubset "i = 2; while i > 0 shrinks i { i = i + 1; }; return i;" (Just False)
                      , checkMirSubset "i = 0; while i < 2 shrinks 2 - i { i = i + 1; }; return i;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 [{ affirm i + 1 <= 3; }] shrinks 2 - i { i = i + 1; }; return i;" (Just True)
                      , checkMirSubset "s = 0; for i in 0..3 { s = s + 1; }; return s;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 shrinks 2 - i { i = i - 1; }; return i;" (Just False)
                      , checkMirSubset "n = 2; i = 0; while i < n shrinks n - i { i = i + 1; n = n + 1; }; return i;" (Just False)
                      , checkMirSubset "xs = [1]; for i in 0..size(xs) { if get(xs, i) > 0 { return 1; }; }; return 0;" (Just True)
                      , -- (the loop returns on its first pass, so what follows it is never reached)
                        checkMirSubset "xs = [1]; for i in 0..size(xs) { if get(xs, i) > 0 { return 1; }; }; affirm 0 = 1; return 0;" (Just True)
                      , checkMirSubset "xs = [0]; for i in 0..size(xs) { if get(xs, i) > 0 { return 1; }; }; affirm 0 = 1; return 0;" (Just False)
                      , checkMirSubset "s = 0; for i in 0..1 { for j in 0..1 { s = s + 1; }; }; return s;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { if i < 2 { i = i + 1; } else { i = i + 0; }; }; return i;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { if i < 2 { i = i + 1; } else { i = i + 0; }; }; affirm i = 2; return i;" (Just True)
                      , checkMirSubset "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { i = i + 1; }; return i; }; return f(3);" (Just True)
                      , checkMirSubset "xs = [1]; for i in 0..size(xs) { affirm i >= 0; affirm i < size(xs); }; return 0;" (Just True)
                      , checkMirSubset "xs = [1]; for i in 0..size(xs) { if i > 0 { affirm i >= 1; }; }; return 0;" (Just True)
                      , checkMirSubset "fn f(xs: List<Int>) -> Int { affirm size(xs) >= 0; return 0; }; return f([]);" (Just True)
                      , checkMirSubset "fn f(xs: List<Int>) -> Int { affirm size(xs) >= 1; return 0; }; return f([]);" (Just False)
                      ])
                , ("bridges",
                      [ checkVariantGoal "Different" 0 1 True, checkVariantGoal "Equal" 0 1 False
                      , checkConstructorGoal "Equal" 11 1 True, checkConstructorGoal "Equal" 11 0 False
                      , checkWithin 12 10 True, checkWithin 10 12 False, checkWithin 10 10 False
                      , checkCommonContext, checkMergeStates, checkContestT1, checkContestA1, checkContestA1b
                      , checkContestT1WithCondition
                      , checkIntegerSelfPair "AtMost" 20 (-31) False, checkIntegerSelfPair "AtMost" (-31) 21 False, checkIntegerSelfPair "Less" 20 (-31) False
                      , testAssertErrorContains "Function does not exist" (runNamedFunction program "missing" [])
                      , testAssertErrorContains "expected 3 arguments" (runNamedFunction program "hasEquality" [])
                      ])
                , ("join hull",
                      [ checkHull "FreshCollide" (freshCollide False) 4 freshGoals
                      , checkHull "FreshControl" (freshCollide True) 4 freshGoals
                        -- (no root edge: the order w <= x reaches x's class on each side only through the opaque call)
                      , checkHull "A3Affirm"
                            ( hullSide [] [(-30, -1, [1, 32]), (-31, 7, [-30]), (20, -1, [1, 33])] [(32, 0, 2), (33, 0, 3)] [(-31, -30, False), (-31, 20, False)] [(1, 1), (2, 20), (4, -31)]
                            , hullSide [] [(-60, -1, [1, 33]), (-61, 7, [-60]), (20, -1, [1, 33])] [(32, 0, 2), (33, 0, 3)] [(-61, -60, False), (-61, 20, False)] [(1, 1), (2, 20), (4, -61)] )
                            4 [("AtMost", True, Left 2, True), ("Less", False, Left 2, False)]
                        -- y changes on the left only; x > y holds on each side only as a root edge
                      , checkHull "AffirmOneSided"
                            ( hullSide [] [(-50, -1, [1, 31]), (-51, -1, [1, 32])] [(31, 0, 1), (32, 0, 2), (33, 0, 3)] [(-50, -51, True)] [(1, -50), (4, -51)]
                            , hullSide [] [(-60, -1, [1, 33])] [(31, 0, 1), (32, 0, 2), (33, 0, 3)] [(1, -60, True)] [(1, 1), (4, -60)] )
                            4 [("Less", False, Left 1, True), ("AtMost", True, Left 1, False)]
                      , checkHull "GuideAffirm"
                            ( hullSide [] [(-50, -1, [1, 2])] [(31, 0, 1)] [(3, 2, False), (31, 3, False), (1, -50, True)] [(1, 1), (2, 2), (3, 3), (4, -50)]
                            , hullSide [] [(-60, -1, [1, 3])] [(31, 0, 1)] [(3, 2, False), (31, 3, False), (1, -60, True)] [(1, 1), (2, 2), (3, 3), (4, -60)] )
                            4 [("Less", False, Left 1, True)]
                      , checkHull "Range"
                            (hullSide [] [] [(33, 0, 3), (39, 0, 9), (38, 0, 8), (-50, 0, 3)] [] [(4, -50)], hullSide [] [] [(33, 0, 3), (39, 0, 9), (38, 0, 8), (-60, 0, 9)] [] [(4, -60)])
                            4 [("AtMost", False, Right 33, True), ("AtMost", True, Right 39, True), ("AtMost", True, Right 38, False)]
                      , checkHull "StrictEdge"
                            (hullSide [] [(-50, -1, [1, 30])] [(30, 0, 0), (31, 0, 1)] [] [(1, 1), (4, -50)], hullSide [] [(-60, -1, [1, 31])] [(30, 0, 0), (31, 0, 1)] [] [(1, 1), (4, -60)])
                            4 [("AtMost", False, Left 1, True), ("Less", False, Left 1, False)]
                      , checkHull "FalseClaim"
                            (hullSide [] [(-50, -1, [1, 31])] [(31, 0, 1)] [] [(1, 1), (4, -50)], hullSide [] [(-60, -2, [1, 31])] [(31, 0, 1)] [] [(1, 1), (4, -60)])
                            4 [("Less", False, Left 1, False), ("Less", True, Left 1, False)]
                        -- raw -40 is p2 + 1 on the left and the constant 100 on the right
                      , checkHull "RawMeaning"
                            (hullSide [] [(-40, -1, [2, 31]), (-41, -1, [-40, 31])] [(31, 0, 1)] [] [(1, -41), (9, -40)], hullSide [] [] [(31, 0, 1), (-40, 0, 100), (-60, 0, 0)] [] [(1, -60)])
                            1 [("Less", False, Right (-40), False), ("Less", True, Right (-40), False), ("AtMost", True, Right (-40), False)]
                      , checkHull "SubSign"
                            ( hullSide [] [(-50, -2, [1, 33]), (20, -2, [1, 32])] [(31, 0, 1), (32, 0, 2), (33, 0, 3)] [] [(1, 1), (3, 20), (4, -50)]
                            , hullSide [] [(-60, -2, [1, 31]), (20, -2, [1, 32])] [(31, 0, 1), (32, 0, 2), (33, 0, 3)] [] [(1, 1), (3, 20), (4, -60)] )
                            4 [("Less", True, Left 1, True), ("AtMost", True, Left 3, False), ("AtMost", False, Left 1, False)]
                        -- the classes -49 and -4294967295 pack to the key of (-50, 1) unless the ids are kept within 2^31
                      , checkHull "BigIdCollide"
                            (hullSide [] [] [(31, 0, 1)] [(-49, -4294967295, False)] [(1, 1), (4, -50)], hullSide [] [] [(31, 0, 1)] [(-60, 1, False)] [(1, 1), (4, -60)])
                            4 [("AtMost", True, Left 1, False)]
                      , checkHull "BigValue"
                            (hullSide [] [] [(30, 0, 0), (-50, 0, 1125899906842624)] [] [(4, -50)], hullSide [] [] [(30, 0, 0), (-60, 0, 1125899906842625)] [] [(4, -60)])
                            4 [("AtMost", True, Right 30, False)]
                      , checkHull "FiniteBigValue"
                            (hullSide [] [] [(30, 0, 0), (-50, 0, 1099511627777)] [] [(4, -50)], hullSide [] [] [(30, 0, 0), (-60, 0, 5)] [] [(4, -60)])
                            4 [("AtMost", True, Right 30, False)]
                        -- with the least id below -2^62 nothing is minted, so no range fact needs a new term
                      , let sides = (hullSide [] [] [(31, 0, 1), (-50, 0, 3)] [(-4611686018427387905, 1, False)] [(1, 1), (4, -50)], hullSide [] [] [(31, 0, 1), (-60, 0, 4)] [] [(1, 1), (4, -60)])
                         in checkHull "MinBoundary" sides 4 [("AtMost", True, Left 1, False), ("Less", True, Left 1, False)]
                                `orElse` testAssertEq (hullFacts sides) (Just (0, 0, 1))
                      , checkHull "Bool"
                            (hullSide [] [] [(30, 0, 0), (31, 0, 1), (-50, 1, 1)] [] [(4, -50)], hullSide [] [] [(30, 0, 0), (31, 0, 1), (-60, 1, 0)] [] [(4, -60)])
                            4 [("AtMost", True, Right 30, False), ("AtMost", False, Right 31, False)]
                      , checkHull "CycleContra"
                            (hullSide [] [(-50, -1, [-50, 31])] [(31, 0, 1)] [] [(1, 1), (4, -50)], hullSide [] [(-60, -1, [1, 31])] [(31, 0, 1)] [] [(1, 1), (4, -60)])
                            4 [("Less", True, Left 1, False), ("AtMost", True, Left 1, False)]
                      , checkHull "CycleOk"
                            ( hullSide [] [(-50, -1, [-51, 31]), (-51, -2, [-50, 31])] [(31, 0, 1), (32, 0, 2), (35, 0, 5), (37, 0, 7)] [(32, -51, False)] [(4, -50)]
                            , hullSide [] [] [(31, 0, 1), (32, 0, 2), (35, 0, 5), (37, 0, 7), (-60, 0, 5)] [] [(4, -60)] )
                            4 [("AtMost", True, Right 32, False), ("Less", False, Right 35, False)]
                      , checkHull "Ambiguous" (hullSide [] [] [(-50, 0, 5)] [] [(1, -50), (2, -50)], hullSide [] [] [(-60, 0, 1), (-61, 0, 9)] [] [(1, -60), (2, -61)])
                            1 [("Less", True, Left 2, False), ("Less", False, Left 2, False)]
                      , checkHull "ManyLeaf"
                            ( hullSide [] [(-41, -1, [1, 2]), (-42, -1, [-41, 3]), (-43, -1, [-42, 4]), (-44, -1, [-43, 5]), (-45, -1, [-44, 6]), (-50, -1, [-45, 31])] [(30, 0, 0), (31, 0, 1), (32, 0, 2)] [(30, i, False) | i <- [1 .. 6]] ([(i, i) | i <- [1 .. 6]] ++ [(9, -50)])
                            , hullSide [] [(-41, -1, [1, 2]), (-42, -1, [-41, 3]), (-43, -1, [-42, 4]), (-44, -1, [-43, 5]), (-45, -1, [-44, 6]), (-60, -1, [-45, 32])] [(30, 0, 0), (31, 0, 1), (32, 0, 2)] [(30, i, False) | i <- [1 .. 6]] ([(i, i) | i <- [1 .. 6]] ++ [(9, -60)]) )
                            9 [("Less", False, Left 3, True), ("AtMost", True, Left 3, False), ("Less", False, Right 30, True)]
                        -- b shares a root class with the earlier pair a on the left; its root edge is a's there
                      , checkHull "AliasOpaque"
                            (hullSide [] [(-50, 7, [1])] [] [(1, -50, True)] [(1, 1), (2, -50), (3, -50)], hullSide [] [(-61, 7, [1]), (-62, 8, [1])] [] [(1, -62, True)] [(1, 1), (2, -61), (3, -62)])
                            3 [("Less", False, Left 1, True), ("AtMost", True, Left 1, False)]
                      , checkHull "AliasedRootFirstOwner"
                            (hullSide [] [] [] [(1, -50, True), (-50, 9, True)] [(1, 1), (2, -50), (3, -50), (9, 9)], hullSide [] [] [] [(1, -61, True), (-61, 9, True), (1, -62, True)] [(1, 1), (2, -61), (3, -62), (9, 9)])
                            3 [("AtMost", True, Left 1, False), ("AtMost", False, Left 9, False)]
                        -- output is two facts a pair however many pairs, plus one per hub edge
                      , testAssertEq [hullFacts (quadSides k) | k <- [4, 8, 16, 32]] [Just (2 * k, 0, 2 * k) | k <- [4, 8, 16, 32]]
                      , testAssertEq (map (fmap (\(orders, differences, _) -> (orders, differences)) . hullFacts . hubSides) [16, 64]) [Just (33, 1), Just (129, 1)]
                        -- the F fixtures with their minted terms negative; parameters and literals keep their ids
                      , checkHull "F01neg" (hullSide [] [] [(30, 0, 5), (-50, 0, 7)] [] [(1, 30), (2, -50)], hullSide [] [] [(30, 0, 5), (-60, 0, 6)] [] [(1, 30), (2, -60)])
                            2 [("AtMost", False, Left 1, True), ("Less", False, Left 1, True), ("Less", True, Left 1, False)]
                      , checkHull "F02neg"
                            ( hullSide [] [(-40, -13, [41])] [(33, 0, 0), (-50, 0, 0)] [(33, 3, False)] ([(1, -40), (2, 41), (3, 3), (4, -50)] ++ freeLocals)
                            , hullSide [] [(-40, -13, [41]), (-60, -2, [33, 3])] [(33, 0, 0)] [(33, 3, False)] ([(1, -40), (2, 41), (3, 3), (4, -60)] ++ freeLocals) )
                            4 [("AtMost", True, Left 3, True), ("Less", True, Left 1, False), ("Less", False, Left 3, False)]
                      , checkHull "F03alias" (hullSide [(1, 2), (-50, 1)] [] [] [] [(1, 1), (2, 2), (3, -50)], hullSide [(1, 2), (-60, 2)] [] [] [] [(1, 1), (2, 2), (3, -60)])
                            3 [("AtMost", True, Left 1, True), ("AtMost", False, Left 1, True)]
                      , checkHull "F03neg" (hullSide [(1, 2)] [] [] [] [(1, 1), (2, 2), (3, -50)], hullSide [(1, 2)] [] [] [] [(1, 1), (2, 2), (3, -60)])
                            3 [("AtMost", True, Left 1, False)]
                      , checkHull "F04neg"
                            ( hullSide [] [] [(33, 0, 0), (31, 0, 1), (-50, 0, 1)] [(33, 3, False), (3, 33, True)] ([(1, 3), (2, 4), (5, -50)] ++ freeLocals)
                            , hullSide [] [(-60, -1, [4, 31])] [(33, 0, 0), (31, 0, 1)] [(33, 3, False)] ([(1, 3), (2, 4), (5, -60)] ++ freeLocals) )
                            5 [("Less", True, Left 2, False)]
                      , checkHull "F05neg"
                            ( hullSide [] [(-50, -1, [1, 2])] [(31, 0, 1)] [(31, 1, False), (31, 2, False), (-50, 31, False)] ([(1, 1), (2, 2), (3, 4), (5, -50)] ++ freeLocals)
                            , hullSide [] [(-60, -1, [4, 31])] [(31, 0, 1)] [(31, 1, False), (31, 2, False)] ([(1, 1), (2, 2), (3, 4), (5, -60)] ++ freeLocals) )
                            5 [("Less", True, Left 3, False)]
                      , checkHull "F06neg"
                            ( hullSide [] [(-20, -1, [1, 2]), (-21, 20, [3, 2]), (-22, 20, [3, -20])] [(33, 0, 0)] [(33, 1, False), (-20, 2, False)] ([(1, 1), (2, 2), (3, 3), (4, -21), (5, -22)] ++ freeLocals)
                            , hullSide [] [(-20, -1, [1, 2]), (-21, 20, [3, 2]), (-22, 20, [3, -20])] [(33, 0, 0)] [(33, 1, False), (-20, 2, False)] ([(1, 1), (2, 2), (3, 3), (4, -21), (5, -21)] ++ freeLocals) )
                            5 [("Less", True, Left 4, False), ("Less", False, Left 4, False)]
                      , checkHull "F07neg"
                            ( hullSide [] [(-52, -1, [1, 2]), (-50, -1, [-52, 31])] [(33, 0, 0), (31, 0, 1), (32, 0, 2)] [(33, 1, False), (33, 2, False)] [(1, 1), (2, 2), (5, -50)]
                            , hullSide [] [(-62, -1, [1, 2]), (-60, -1, [-62, 32])] [(33, 0, 0), (31, 0, 1), (32, 0, 2)] [(33, 1, False), (33, 2, False)] [(1, 1), (2, 2), (5, -60)] )
                            5 [("Less", False, Left 1, True), ("Less", False, Left 2, True), ("Less", True, Left 1, False)]
                      , checkHull "F08neg"
                            (hullSide [] [] [(-50, 0, 1)] [] [(5, -50), (71, 71), (72, 72), (73, 73), (74, 74), (75, 75)], hullSide [] [] [(-60, 0, 2)] [] [(5, -60), (71, 71), (72, 72), (73, 73), (74, 74), (75, 75)])
                            5 [("AtMost", False, Left 71, False), ("AtMost", True, Left 71, False)]
                        -- a Boolean constant is no number: true is not 1
                      , checkHull "F09neg"
                            ( hullSide [] [] [(33, 0, 0), (31, 0, 1), (34, 1, 1), (-50, 0, 1)] [] ([(1, 33), (2, 31), (3, 34), (5, -50)] ++ freeLocals)
                            , hullSide [] [] [(33, 0, 0), (31, 0, 1), (34, 1, 1), (-60, 0, 2)] [] ([(1, 33), (2, 31), (3, 34), (5, -60)] ++ freeLocals) )
                            5 [("Less", False, Left 1, True), ("AtMost", False, Left 2, True), ("Less", False, Left 2, False), ("AtMost", False, Left 3, False), ("AtMost", True, Left 3, False)]
                      , checkHull "F11neg"
                            ( hullSide [] [(-21, 20, [3, 1]), (-22, 20, [3, 2])] [] [(1, 2, False), (2, 1, False), (-22, -50, True)] ([(1, 1), (2, 2), (3, 3), (4, -21), (5, -50), (6, -22)] ++ freeLocals)
                            , hullSide [] [(-21, 20, [3, 1]), (-22, 20, [3, 2])] [] [(1, 2, False), (2, 1, False), (-22, -60, True)] ([(1, 1), (2, 2), (3, 3), (4, -21), (5, -60), (6, -22)] ++ freeLocals) )
                            5 [("Less", False, Left 6, True), ("AtMost", True, Left 6, False)]
                      , checkHull "F12neg"
                            (hullSide [(-24, -28)] [] [] [(-28, -50, True)] ([(1, -24), (2, -28), (5, -50)] ++ freeLocals), hullSide [(-24, -28)] [] [] [(-28, -60, True)] ([(1, -24), (2, -28), (5, -60)] ++ freeLocals))
                            5 [("Less", False, Left 1, True), ("Less", False, Left 2, True), ("AtMost", True, Left 2, False)]
                      ])
                , ("loop candidate provenance",
                      [ checkPairProvenance "inferPairGoal" [(900, 0, 7), (901, 0, 4)] [(10, 0, 7), (11, 0, 4)] (1, [10, 11])
                      , checkPairProvenance "inferPairByConstants" [(900, 0, 7), (901, 0, 4)] [(10, 0, 7), (11, 0, 4)] (1, [10, 11])
                      , checkPairProvenance "inferPairGoal" [(900, 0, 7), (901, 0, 4), (902, 0, 3)] [(10, 0, 7), (11, 0, 4), (12, 0, 3)] (1, [12])
                      , checkPairProvenance "inferPairGoal" [(900, 0, 7), (901, 0, 4), (903, 0, 1)] [(10, 0, 7), (11, 0, 4), (13, 0, 1)] (1, [13])
                      -- (the work state alone can name the distance: with none in the initial
                      -- state there is no candidate, rather than one naming the work state's)
                      , checkPairProvenance "inferPairGoal" [(900, 0, 7), (901, 0, 4)] [(11, 0, 4)] (0, [])
                      , checkInferenceProvenance
                      ])
                ]

-- Int is 64 bits: literals must fit, and arithmetic that leaves the range stops the program
testIntRange :: Test
testIntRange =
    testCaseSeq
        "testIntRange"
        ( [ testAssertTrue (either (const False) (const True) (parseStatementBlock src)) | src <- ["x = 9223372036854775807;", "x = -9223372036854775808;", "return [9223372036854775807, -9223372036854775808];"]]
            ++ [ either (\e -> testAssertTrue ("out of range" `isInfixOf` show e)) (const (Just "should not parse")) (parseStatementBlock src)
               | src <- ["x = 9223372036854775808;", "x = -9223372036854775809;", "return [99999999999999999999];"]
               ]
            ++ [ testAssertEq (runMir src) (Error "Integer overflow")
               | src <-
                    [ "return 9223372036854775807 + 1;"
                    , "return -9223372036854775808 - 1;"
                    , "x = 4611686018427387904; return x * 2;"
                    , "return -9223372036854775808 / -1;"
                    , "l = [9223372036854775807, 1]; return get(l, 0) + get(l, 1);"
                    , "fn double(n: Int) -> Int { return n + n; }; return double(9223372036854775807);"
                    ]
               ]
            ++ [ testAssertEq (runMir src) (Ok (Just expected))
               | (src, expected) <-
                    [ ("return 9223372036854775807 + 0;", "9223372036854775807")
                    , ("return -9223372036854775808 + 9223372036854775807;", "-1")
                    , ("return 9223372036854775807 - 9223372036854775807;", "0")
                    , ("return -9223372036854775808 / 1;", "-9223372036854775808")
                    , ("return -9223372036854775808 % -1;", "0")
                    , ("return 3037000499 * 3037000499;", "9223372030926249001")
                    , ("return 0 - 9223372036854775807;", "-9223372036854775807")
                    ]
               ]
            ++ [testAssertEq (runMir "x = 2; return x * 4611686018427387904;") (Error "Integer overflow")]
            ++ [ testAssertErrorContains "Integer overflow" (runSource Interpret "return 9223372036854775807 + 1;")
               , -- (validation reasons about unbounded integers, so a property it proves holds for the runs that do not stop)
                 testAssertEq (runSource Check "x = 9223372036854775807; y = x + 1; affirm y = x + 1;") (Ok "OK")
               ]
        )

-- The trait of this name that a reading of a program has, and the fields of the struct of this name
traitCount :: String -> [Statement] -> Int
traitCount name stmts = length [() | TraitDef n _ _ <- stmts, n == name]

structFields :: String -> [Statement] -> [[String]]
structFields name stmts = [map fst fields | StructDef n _ fields _ <- stmts, n == name]

-- The stages of a program, and what each one hands to the next
testPipeline :: Test
testPipeline =
    testCaseSeq
        "testPipeline"
        [ case compileSource "return parserUnicodeLetter(233);" of
            Ok _ -> Just "ordinary source received private parser helpers"
            Error err | "Parser tool failure:" `isInfixOf` err -> Just err
            Error err -> testAssertTrue ("parserUnicodeLetter" `isInfixOf` err)
        , testAssertErrorContains "frontend sentinel" (validatedSourceWith (\_ _ -> Error "frontend sentinel") "return 1;")
        , testAssertErrorContains "frontend sentinel" (compileSourceWith (\_ _ -> Error "frontend sentinel") "return 1;")
        , case compileSourceWith (\_ _ -> Ok ([], [], [Return (Val (VInt 7))])) "return 1;" of
            Error err -> Just err
            Ok program -> testAssertEq (mapResult (fmap renderMirValue) (runProgram program)) (Ok (Just "7"))
        , case validatedSourceWith (\_ _ -> Ok ([], [], [Return (Val (VInt 7))])) "return 1;" of
            Error err -> Just err
            Ok program -> testAssertEq (mapResult (fmap renderMirValue) (runProgram program)) (Ok (Just "7"))
        , -- Each stage names itself in its error
          testAssertErrorContains "Parse error" (parseSource "x = ;")
        , validationFailureFor "compileSource"
        , testAssertErrorContains "Validation failed: Type error" (compileSource "x = 1; y = x(2);")
        , -- The checked program has each `shrinks` clause resolved, and is the one that gets lowered
          case parseSource "i = 0; while i < 3 shrinks 3 - i { i = i + 1; };" `bindResult` elaborate of
            Ok (Elaborated stmts _) -> testAssertTrue (not (null [() | While _ _ (Just (Counting _)) _ <- stmts]))
            Error e -> Just e
        , case compileSource "i = 0; while i < 3 shrinks 3 - i { i = i + 1; }; return i;" of
            Ok program -> testAssertEq (mapResult (fmap renderMirValue) (runProgram program), Map.size (M.fnBlocks (M.progMain program))) (Ok (Just "3"), 4)
            Error e -> Just e
        , -- The MIR of a program is verified: a program with no return type to agree on never gets that far
          testAssertErrorContains "Validation failed: Type error" (compileSource "if true { return 1; } else { return false; };")
        , testAssertEq (mapResult (const ()) (compileSource "")) (Ok ())
        , -- The libraries in front of a program are decided from the program as it was read, not from its text
          case parseSource "trait Sequence { fn size(self: Self) -> Int; }; struct Box1 { n: Int }; impl Sequence for Box1 { fn size(self: Self) -> Int { return self.n; }; }; return Box1 { n: 3 }.size();" of
            Ok stmts -> testAssertEq (traitCount "Sequence" stmts) 1
            Error e -> Just e
        , case parseSource "struct String { x: Int }; return String { x: 3 }.x;" of
            Ok stmts -> testAssertEq (structFields "String" stmts) [["x"]]
            Error e -> Just e
        , case parseSource "// Sequence String Clone\nreturn 4;" of
            Ok stmts -> testAssertEq (traitCount "Sequence" stmts, structFields "String" stmts) (0, [])
            Error e -> Just e
        , case parseSource "struct String { bytes: List<Byte> }; s = \"trait Sequence\"; return size(s.bytes);" of
            Ok stmts -> testAssertEq (traitCount "Sequence" stmts, structFields "String" stmts) (0, [["bytes"]])
            Error e -> Just e
        , case parseSource "return \"a\";" of
            Ok stmts -> testAssertEq (structFields "String" stmts) [["bytes"]]
            Error e -> Just e
        , case parseSource "fn f<S: Sequence<Int>>(s: &S) -> Int { return size(s); }; return f([1, 2]);" of
            Ok stmts -> testAssertEq (traitCount "Sequence" stmts) 1
            Error e -> Just e
        , testAssertErrorContains "Parse error" (parseSource "trait Sequence { fn size(self: Self) -> Int; }; s = \"a\";")
        , testAssertErrorContains "Parse error" (parseSource "x = \"a\"; y = ;")
        , -- A program that declares its own enum or trait named String is read without the string library
          testAssertEq (mapResult (const ()) (compileSource "enum String { Empty }; String = true; if String { return 1; } else { return 2; };")) (Ok ())
        , testAssertEq (mapResult (const ()) (compileSource "trait String { fn size(self: Self) -> Int; }; String = true; if String { return 1; } else { return 2; };")) (Ok ())
        , -- A program that declares its own prelude trait is read without the prelude or the libraries that need it, so String is not a struct there
          testAssertEq (mapResult (const ()) (compileSource "trait Sequence { }; String = true; if String { return 1; } else { return 2; };")) (Ok ())
        , testAssertEq (mapResult (const ()) (compileSource "trait String { }; String = true; if String { return 1; } else { return 2; };")) (Ok ())
        , -- The names native code makes a list and a Box of are reserved from what a program declares, not from its text
          testAssertErrorContains "listPush is reserved" (parseSource "fn listPush(x: Int) -> Int { return x; }; return 1;")
        , case parseSource "// fn listPush\nreturn 1;" of
            Ok _ -> Nothing
            Error e -> Just e
        ]
