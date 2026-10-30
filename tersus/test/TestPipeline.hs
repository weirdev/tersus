module TestPipeline
    ( testExamples
    , testCli
    , testMir
    , testIntRange
    , testPipeline
    ) where

import Control.Exception (evaluate, finally)
import Control.Monad (when)
import Data.List (isInfixOf)
import GHC.IO.Encoding (char8, getLocaleEncoding, setLocaleEncoding)
import System.Directory (getTemporaryDirectory, removeFile)
import System.IO
import qualified Data.Map as Map
import qualified Data.Set as Set
import Cli
import qualified Mir as M
import MirEval
import MirLower
import MirOwnership (insertOwnership)
import MirVerify
import Pipeline
import qualified ProofEngine as Engine
import SelfHostedProof (querySelfHosted)
import SelfHostedMir (checkerProgram, validateMir, validateMirSubset)
import Parse
import StdLib
import TypeCheck (elaborate)
import TersusTypes
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
    source <- readFile path
    -- (as the command line reads a program, so an example that uses the prelude has it)
    pure $ case parseSource source of
        Error err -> case expectation of
            ExpectRejected expectedError -> testAssertErrorContains expectedError (Error err :: Result () String)
            _ -> Just $ "Parse failed: " ++ err
        Ok stmts -> checkExample stmts expectation

checkExample :: [Statement] -> ExampleExpectation -> TestResult
checkExample stmts (ExpectRejected expectedError) =
    testAssertErrorContains expectedError (validateStatements stmts)
checkExample stmts expectation =
    case validateStatements stmts of
        Error e -> Just $ "Validation failed with error: " ++ e
        Ok _ -> case runStatements stmts of
            Error e -> Just $ "Evaluation failed with error: " ++ e
            Ok result -> case expectation of
                ExpectReturn expected -> testAssertEq (fmap fromMirValue result) (Just expected)
                _ -> testAssertEq (fmap fromMirValue result) Nothing

-- The first failure of two checks
orElse :: TestResult -> TestResult -> TestResult
orElse Nothing other = other
orElse failure _ = failure

testExamples :: Test
testExamples =
    TestList
        "testExamples"
        [ testExampleFile "examples/basics.tersus" (ExpectReturn (VInt 6))
        , testExampleFile "examples/functions.tersus" (ExpectReturn (VInt 21))
        , testExampleFile "examples/booleans.tersus" (ExpectReturn (VBool True))
        , testExampleFile "examples/proofs.tersus" ExpectValid
        , testExampleFile "examples/rewrites.tersus" ExpectValid
        , testExampleFile "examples/safe_access.tersus" (ExpectReturn (VInt 38))
        , testExampleFile "examples/contracts.tersus" (ExpectReturn (VInt 8))
        , testExampleFile "examples/rules.tersus" ExpectValid
        , testExampleFile "examples/branching.tersus" (ExpectReturn (VInt 106))
        , testExampleFile "examples/arithmetic.tersus" (ExpectReturn (VInt 6))
        , testExampleFile "examples/types.tersus" (ExpectReturn (VInt 6))
        , testExampleFile "examples/structs.tersus" (ExpectReturn (VInt 11))
        , testExampleFile "examples/linked_list.tersus" (ExpectReturn (VInt 9))
        , testExampleFile "examples/enums.tersus" (ExpectReturn (VInt 27))
        , testExampleFile "examples/traits.tersus" (ExpectReturn (VInt 55))
        , testExampleFile "examples/rejected/trait_input_stronger.tersus" (ExpectRejected "impl Step for Counter: advance does not meet what Step declares")
        , testExampleFile "examples/rejected/trait_output_weaker.tersus" (ExpectRejected "impl Measure for Pair: measure does not meet what Measure declares")
        , testExampleFile "examples/rejected/body_not_exported.tersus" (ExpectRejected "Could not prove: return = n")
        , testExampleFile "examples/rejected/trait_ambiguous_call.tersus" (ExpectRejected "Counter::label is ambiguous")
        , testExampleFile "examples/rejected/trait_missing_function.tersus" (ExpectRejected "impl Step for Counter lacks the function total")
        , testExampleFile "examples/arrays.tersus" (ExpectReturn (VInt 42))
        , testExampleFile "examples/array_data.tersus" (ExpectReturn (VInt 45))
        , testExampleFile "examples/rejected/array_size_mismatch.tersus" (ExpectRejected "argument 2 of dot: expected Array<Int, 5>, got Array<Int, 4>")
        , testExampleFile "examples/rejected/array_runtime_size.tersus" (ExpectRejected "the size of an array must be a constant")
        , testExampleFile "examples/rejected/array_unsized.tersus" (ExpectRejected "an array with no size")
        , testExampleFile "examples/box_array.tersus" (ExpectReturn (VInt 34))
        , testExampleFile "examples/array_sizes.tersus" (ExpectReturn (VInt 42))
        , testExampleFile "examples/type_parameters.tersus" (ExpectReturn (VInt 2045))
        , testExampleFile "examples/generic_structs.tersus" (ExpectReturn (VInt 2224))
        , testExampleFile "examples/files.tersus" (ExpectReturn (VInt (-1)))
        , testExampleFile "examples/args.tersus" (ExpectReturn (VInt 0))
        , testExampleFile "examples/bytes.tersus" (ExpectReturn (VInt 275020))
        , testExampleFile "examples/hello.tersus" (ExpectReturn (VInt 14))
        , testExampleFile "examples/strings.tersus" (ExpectReturn (VInt 980))
        , testExampleFile "examples/upper.tersus" (ExpectReturn (VInt 0))
        , testExampleFile "examples/text.tersus" (ExpectReturn (VInt 504))
        , testExampleFile "examples/mir_reader.tersus" (ExpectReturn (VInt 1))
        , testExampleFile "examples/emit.tersus" (ExpectReturn (VInt 1))
        , testExampleFile "examples/vec.tersus" (ExpectReturn (VInt 2491212381))
        , testExampleFile "examples/spec_functions.tersus" (ExpectReturn (VInt 25070))
        , testExampleFile "examples/list_methods.tersus" (ExpectReturn (VInt 508221))
        , testExampleFile "examples/array_owners.tersus" (ExpectReturn (VInt 207))
        , testExampleFile "examples/borrowing.tersus" (ExpectReturn (VInt 138))
        , testExampleFile "examples/sized_structs.tersus" (ExpectReturn (VInt 71))
        , testExampleFile "examples/rejected/sized_struct_mismatch.tersus" (ExpectRejected "argument 1 of first: expected Packet<3>, got Packet<2>")
        , testExampleFile "examples/rejected/array_size_param_mismatch.tersus" (ExpectRejected "argument 2 of dot: expected Array<Int, 2>, got Array<Int, 3>")
        , testExampleFile "examples/rejected/box_array_size.tersus" (ExpectRejected "argument 1 of corner: expected Box<Array<Int, 3>>, got Box<Array<Int, ?>>")
        , testExampleFile "examples/rejected/array_push.tersus" (ExpectRejected "argument 1 of push: expected List<?>, got Array<Int, 2>")
        , testExampleFile "examples/generic_lists.tersus" (ExpectReturn (VList [VList [VInt 1, VInt 2], VList [VInt 3, VInt 4], VList [VInt 1, VInt 2]]))
        , testExampleFile "examples/helper_functions.tersus" (ExpectReturn (VInt 11))
        , testExampleFile "examples/recursion.tersus" (ExpectReturn (VInt 26))
        , testExampleFile "examples/termination.tersus" (ExpectReturn (VInt 23))
        , testExampleFile "examples/for_loops.tersus" (ExpectReturn (VInt 33))
        , testExampleFile "examples/linear.tersus" (ExpectReturn (VInt 633))
        , testExampleFile "examples/packet_parser.tersus" (ExpectReturn (VInt 711))
        , testExampleFile "examples/loops.tersus" (ExpectReturn (VInt 30))
        , testExampleFile "examples/early_return.tersus" (ExpectReturn (VInt 104))
        , testExampleFile "examples/loop_return.tersus" (ExpectReturn (VInt 7))
        , testExampleFile "examples/parallel_sum.tersus" (ExpectReturn (VList [VInt 11, VInt 22, VInt 33]))
        , testExampleFile "examples/build_list.tersus" (ExpectReturn (VList [VInt 2, VInt 4, VInt 6]))
        , testExampleFile "examples/update_list.tersus" (ExpectReturn (VList [VInt 101, VInt 102, VInt 103]))
        , testExampleFile "examples/element_facts.tersus" (ExpectReturn (VInt 106))
        , testExampleFile "examples/frame_facts.tersus" (ExpectReturn (VInt 149))
        , testExampleFile "examples/forall_facts.tersus" (ExpectReturn (VInt 5))
        , testExampleFile "examples/rejected/forall_wrong_element.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/forall_invariant_gap.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/forall_unproven.tersus" (ExpectRejected "input validation failed")
        , testExampleFile "examples/rejected/frame_changed_index.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/get_out_of_range.tersus" (ExpectRejected "Relation does not hold")
        , testExampleFile "examples/rejected/get_unproven_index.tersus" (ExpectRejected "Relation lacks a proof")
        , testExampleFile "examples/rejected/parallel_length.tersus" (ExpectRejected "Relation lacks a proof")
        , testExampleFile "examples/rejected/call_violates_contract.tersus" (ExpectRejected "Could not prove: n > 0")
        , testExampleFile "examples/rejected/recursion_wrong_contract.tersus" (ExpectRejected "Could not prove: return = 0")
        , testExampleFile "examples/rejected/recursion_input.tersus" (ExpectRejected "Could not prove: n > 0")
        , testExampleFile "examples/rejected/type_return_mismatch.tersus" (ExpectRejected "returned value: expected Int, got List<Int>")
        , testExampleFile "examples/rejected/type_argument_mismatch.tersus" (ExpectRejected "argument 1 of size")
        , testExampleFile "examples/rejected/list_element_mismatch.tersus" (ExpectRejected "argument 2 of push: expected Bool, got Int")
        , testExampleFile "examples/rejected/struct_update_frame.tersus" (ExpectRejected "Could not prove: return.y = p.x")
        , testExampleFile "examples/rejected/struct_field_type.tersus" (ExpectRejected "field value of Node: expected Int, got Bool")
        , testExampleFile "examples/rejected/enum_contract_unmet.tersus" (ExpectRejected "Could not prove: s is Shape::Circle")
        , testExampleFile "examples/rejected/enum_wrong_variant.tersus" (ExpectRejected "Could not prove: s is Shape::Rect")
        , testExampleFile "examples/rejected/linked_list_link_out_of_range.tersus" (ExpectRejected "Could not prove: forall i in 0..size(return): get(return, i).next < size(return)")
        , testExampleFile "examples/rejected/linked_list_link_disagrees.tersus" (ExpectRejected "Could not prove: forall i in 0..size(return): get(return, get(return, i).next).prev = i")
        , testExampleFile "examples/rejected/for_reads_past_end.tersus" (ExpectRejected "Funct input validation failed")
        , testExampleFile "examples/rejected/division_not_below.tersus" (ExpectRejected "Could not prove: return < n")
        , testExampleFile "examples/rejected/sum_bound_too_strong.tersus" (ExpectRejected "Could not prove: return < 10")
        , testExampleFile "examples/rejected/loop_sum_not_kept.tersus" (ExpectRejected "Could not prove: return = n")
        , testExampleFile "examples/rejected/packet_off_by_one.tersus" (ExpectRejected "Funct input validation failed")
        , testExampleFile "examples/rejected/packet_negative_length.tersus" (ExpectRejected "Could not prove: lo <= hi")
        , testExampleFile "examples/rejected/packet_checksum_range.tersus" (ExpectRejected "Could not prove: return < 255")
        , testExampleFile "examples/rejected/for_assigns_counter.tersus" (ExpectRejected "The body of a for loop cannot assign its loop variable i")
        , testExampleFile "examples/rejected/loop_without_termination.tersus" (ExpectRejected "Loop must say how it ends")
        , testExampleFile "examples/rejected/loop_variant_not_shrinking.tersus" (ExpectRejected "Loop variant does not shrink: 3 - i")
        , testExampleFile "examples/rejected/loop_variant_unbounded.tersus" (ExpectRejected "Loop variant is not bounded below: i")
        , testExampleFile "examples/rejected/recursion_without_variant.tersus" (ExpectRejected "Not guaranteed to terminate: it calls itself")
        , testExampleFile "examples/rejected/recursion_variant_not_shrinking.tersus" (ExpectRejected "Recursive call does not shrink the variant: n")
        , testExampleFile "examples/rejected/box_infinite_size.tersus" (ExpectRejected "Chain holds itself, so it would have no size: hold the recursion in a Box, as in Box<Chain>")
        , testExampleFile "examples/rejected/recursion_shrinks_not_a_part.tersus" (ExpectRejected "Recursive call does not shrink the variant: t")
        , testExampleFile "examples/rejected/diverging_call.tersus" (ExpectRejected "it calls a function that is declared ~")
        , testExampleFile "examples/rejected/diverging_loop.tersus" (ExpectRejected "a loop is declared ~")
        , testExampleFile "examples/rejected/linked_list_unchecked_walk.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/call_before_definition.tersus" (ExpectRejected "Undefined variable: later")
        , testExampleFile "examples/rejected/division_by_zero.tersus" (ExpectRejected "Relation lacks a proof")
        , testExampleFile "examples/rejected/push_size.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/set_out_of_range.tersus" (ExpectRejected "Relation does not hold")
        , testExampleFile "examples/rejected/set_size.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/element_wrong.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/invariant_entry.tersus" (ExpectRejected "Loop invariant does not hold on entry")
        , testExampleFile "examples/rejected/invariant_preserved.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/loop_stale_fact.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/loop_return_invariant.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/loop_missing_return.tersus" (ExpectRejected "Return value not found")
        , testExampleFile "examples/rejected/unguarded_access.tersus" (ExpectRejected "Could not prove: size(list) > 0")
        , testExampleFile "examples/rejected/branch_fact.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/guard_condition.tersus" (ExpectRejected "Could not prove: size(list) > 0")
        , testExampleFile "examples/rejected/missing_return.tersus" (ExpectRejected "Return value not found")
        , testExampleFile "examples/rejected/affirm.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/first_of_empty.tersus" (ExpectRejected "Could not prove: size(list) > 0")
        , testExampleFile "examples/rejected/unmet_contract.tersus" (ExpectRejected "is not greater than 0")
        , testExampleFile "examples/rejected/missing_contract.tersus" (ExpectRejected "Could not prove: size(list) > 0")
        , testExampleFile "examples/rejected/output_contract.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/bad_proof_rule.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/axiom_input.tersus" (ExpectRejected "is not greater than 0")
        , testExampleFile "examples/rejected/unknown_rule.tersus" (ExpectRejected "Unknown rewrite rule")
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
    (path, handle) <- openTempFile tmp "tersus_utf8.tersus"
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

testCli :: Test
testCli = TestList "testCli" [testCliReadsUtf8, testCliCases]

testCliCases :: Test
testCliCases =
    testCaseSeq
        "testCliCases"
        [ testCliParseCommandLine
        , testCliRenderValue
        , testCliRun
        , testCliCheck
        , testAssertErrorContains "Parse error" (runSource Interpret "x = ;")
        , testAssertErrorContains "Validation failed" (runSource Interpret "x = 5; affirm x < 4;")
        , testAssertErrorContains "Validation failed" (runSource Check "x = 5; affirm x < 4;")
        , -- Validation must reject the program before it is evaluated
          testAssertErrorContains "Validation failed" (runSource Interpret "return first([]);")
        ]

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
        , withMir "fn f(l: List<Int>) -> Int { return 0; }; { f = size; }; return f([1, 2]);" $ \p ->
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
                , ("fn f(l: List<Int>) -> Int { return 0; }; { f = size; }; return f([1, 2]);", Ok (Just "2"))
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
        , testSelfHostedEquality
        , testCaseSeq
            "testMirCli"
            [ -- `mir` prints the blocks
              testAssertEq (runSource Mir "x = 1 + 2; return x;") (Ok (unlines ["fn main() -> Int {", "    let _0: Int;", "    let _1: Int; // x", "    bb0: {", "        _1 = Add(const 1, const 2);", "        _0 = _1;", "        return;", "    }", "}"]))
            , testAssertErrorContains "Validation failed" (runSource Mir "x = 1; affirm x = 2;")
            , -- A run reports the errors that validation would have prevented
              testAssertEq (runMir "return 1 / 0;") (Error "Division by zero")
            ]
        ]

-- Compare the Tersus equality closure with the reference solver over graph
-- shapes covering disconnected vertices, chains, cycles, duplicates and loops.
testSelfHostedEquality :: Test
testSelfHostedEquality = TestCase "self-hosted equality query" $ do
    putStrLn "Running self-hosted validator differential checks"
    case checkerProgram of
        Error e -> pure (Just ("Could not validate the Tersus validator: " ++ e))
        Ok program ->
            let fact (a, b) = MData "EqualityFact" [("left", MInt a), ("right", MInt b)]
                eq :: Integer -> Integer -> IotaProof
                eq a b = FApp eqProof [ATerm (Iota (show a)), ATerm (Iota (show b))]
                check pairs a b =
                    let context = Engine.proofContextFromFacts [eq x y | (x, y) <- pairs]
                        expected = Engine.entails (eq a b) context
                        result = runNamedFunction program "hasEquality" [MList (map fact pairs), MInt a, MInt b]
                     in case testAssertEq result (Ok (Just (MBool expected))) of
                            Nothing -> Nothing
                            Just e -> Just ("facts " ++ show pairs ++ ", query " ++ show (a, b) ++ ": " ++ e)
                expectedGraph pairs =
                    let starts = [0..3]
                        context = Engine.proofContextFromFacts [eq a b | (a, b) <- pairs]
                     in [ Set.fromList [right | right <- starts, Engine.entails (eq left right) context]
                        | left <- starts
                        ]
                checkGraphBatch =
                    let starts = [0..3]
                        expected = map expectedGraph graphs
                        result = runNamedFunction program "equalityReachabilityBatch"
                            [MList [MList (map fact pairs) | pairs <- graphs], MList (map MInt starts)]
                        decodeGraph (MList rows) = mapM reachableSet rows
                        decodeGraph _ = Nothing
                     in case result of
                            Ok (Just (MList rows)) -> case mapM decodeGraph rows of
                                Just actual -> testAssertEq actual expected
                                Nothing -> Just ("Batched equality closure returned malformed rows: " ++ show result)
                            _ -> Just ("Unexpected batched equality closure result: " ++ show result)
                reachableSet (MList values) = Set.fromList <$> mapM integerValue values
                reachableSet _ = Nothing
                integerValue (MInt integer) = Just integer
                integerValue _ = Nothing
                edges = [(a, b) | a <- [0..3], b <- [a + 1..3]] :: [(Integer, Integer)]
                graphs =
                    [ []
                    , [(0, 1)]
                    , [(0, 1), (2, 3)]
                    , [(1, 2), (0, 1)]
                    , [(2, 3), (1, 2), (0, 1)]
                    , [(0, 1), (0, 2), (0, 3)]
                    , [(0, 1), (1, 2), (2, 0)]
                    , [(0, 1), (0, 1), (1, 1)]
                    , edges
                    ]
                terms = [(12, 2, 10, 2), (13, 2, 11, 2), (10, 1, 0, 2), (11, 1, 1, 2), (14, 3, 1, 2)] :: [(Integer, Integer, Integer, Integer)]
                term (i, op, a, b) = MData "BinaryTerm" [("id", MInt i), ("op", MInt op), ("left", MInt a), ("right", MInt b)]
                expr i = case [(op, a, b) | (j, op, a, b) <- terms, i == j] of
                    (op, a, b) : _ -> FApp (ATerm (Iota ("op" ++ show op))) [expr a, expr b]
                    [] -> ATerm (Iota (show i))
                congruenceContext = Engine.proofContextFromFacts [eq 0 1]
                checkCongruence a b =
                    let expected = Engine.entails (FApp eqProof [expr a, expr b]) congruenceContext
                        actual = runNamedFunction program "hasCongruence" [MList [fact (0, 1)], MList (map term terms), MInt a, MInt b]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                lt :: Integer -> Integer -> IotaProof
                lt a b = FApp (CTerm (builtinFunct (Rel Lt))) [ATerm (Iota (show a)), ATerm (Iota (show b))]
                orders = [(3, 4), (2, 3), (1, 2)] :: [(Integer, Integer)]
                orderFact (a, b) = MData "StrictOrderFact" [("smaller", MInt a), ("greater", MInt b)]
                orderContext = Engine.proofContextFromFacts (eq 0 1 : [lt a b | (a, b) <- orders])
                checkOrder a b =
                    let expected = Engine.entails (lt a b) orderContext
                        actual = runNamedFunction program "hasStrictOrder" [MList [fact (0, 1)], MList (map orderFact orders), MInt a, MInt b]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                le :: Integer -> Integer -> IotaProof
                le a b = FApp (CTerm (builtinFunct (Rel LtEq))) [ATerm (Iota (show a)), ATerm (Iota (show b))]
                mixed = [(3, 4, False), (2, 3, True), (1, 2, False)] :: [(Integer, Integer, Bool)]
                mixedFact (a, b, s) = MData "OrderFact" [("smaller", MInt a), ("greater", MInt b), ("strict", MBool s)]
                mixedContext = Engine.proofContextFromFacts (eq 0 1 : [if s then lt a b else le a b | (a, b, s) <- mixed])
                checkMixed a b s =
                    let expected = Engine.entails (if s then lt a b else le a b) mixedContext
                        actual = runNamedFunction program "hasOrder" [MList [fact (0, 1)], MList (map mixedFact mixed), MInt a, MInt b, MBool s]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                termOrderContext = Engine.proofContextFromFacts [eq 0 1, FApp (CTerm (builtinFunct (Rel Lt))) [expr 10, expr 5]]
                checkTermOrder a b =
                    let expected = Engine.entails (FApp (CTerm (builtinFunct (Rel Lt))) [expr a, expr b]) termOrderContext
                        actual = runNamedFunction program "hasOrderWithTerms" [MList [fact (0, 1)], MList (map term terms), MList [mixedFact (10, 5, True)], MInt a, MInt b, MBool True]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                apps = [(10,20,[0,2]), (11,21,[1,2]), (12,20,[0]), (13,20,[]), (14,21,[])] :: [(Integer,Integer,[Integer])]
                app (i, f, args) = MData "ApplicationTerm" [("id", MInt i), ("function", MInt f), ("arguments", MList (map MInt args))]
                appExpr i = case [(f, args) | (j, f, args) <- apps, i == j] of
                    (f, args) : _ -> FApp (ATerm (Iota (show f))) (map appExpr args)
                    [] -> ATerm (Iota (show i))
                appContext = Engine.proofContextFromFacts [eq 0 1, eq 20 21]
                checkApp a b =
                    let expected = Engine.entails (FApp eqProof [appExpr a, appExpr b]) appContext
                        actual = runNamedFunction program "hasApplicationEquality" [MList (map fact [(0,1),(20,21)]), MList (map app apps), MInt a, MInt b]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                appOrderContext = Engine.proofContextFromFacts [eq 0 1, eq 20 21, FApp (CTerm (builtinFunct (Rel Lt))) [appExpr 10, appExpr 5]]
                checkAppOrder a b =
                    let expected = Engine.entails (FApp (CTerm (builtinFunct (Rel Lt))) [appExpr a, appExpr b]) appOrderContext
                        actual = runNamedFunction program "hasApplicationOrder" [MList (map fact [(0,1),(20,21)]), MList (map app apps), MList [mixedFact (10,5,True)], MInt a, MInt b, MBool True]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                impossible = [(1,2,True),(2,1,False)] :: [(Integer,Integer,Bool)]
                impossibleContext = Engine.proofContextFromFacts [lt 1 2, le 2 1]
                checkImpossible =
                    let expected = Engine.entails (lt 7 8) impossibleContext
                        actual = runNamedFunction program "entailsApplicationOrder" [MList [], MList [], MList (map mixedFact impossible), MInt 7, MInt 8, MBool True]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                ne :: Integer -> Integer -> IotaProof
                ne a b = FApp (CTerm (builtinFunct (Rel NotEq))) [ATerm (Iota (show a)), ATerm (Iota (show b))]
                differentFact (a, b) = MData "DisequalityFact" [("left", MInt a), ("right", MInt b)]
                checkDifferent a b =
                    let context = Engine.proofContextFromFacts [eq 0 1, ne 1 2, lt 2 3]
                        expected = Engine.entails (ne a b) context
                        actual = runNamedFunction program "entailsApplicationDisequality" [MList [fact (0,1)], MList [], MList [mixedFact (2,3,True)], MList [differentFact (1,2)], MInt a, MInt b]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                diffFact (a, b, k) = MData "DifferenceFact" [("left", MInt a), ("right", MInt b), ("bound", MInt k)]
                differenceEdges = [(1,2,0),(2,3,-1),(3,4,0)] :: [(Integer,Integer,Integer)]
                checkDifference a b s =
                    let expected = Engine.entails (if s then lt a b else le a b) mixedContext
                        actual = runNamedFunction program "hasDifference" [MList [fact (0,1)], MList (map diffFact differenceEdges), MInt a, MInt b, MInt (if s then -1 else 0)]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                overflowEdges = [(1,0,-9223372036854775808),(2,1,-1)] :: [(Integer,Integer,Integer)]
                checkDifferenceOverflow = testAssertEq (runNamedFunction program "hasDifference" [MList [], MList (map diffFact overflowEdges), MInt 2, MInt 0, MInt (-9223372036854775808)]) (Ok (Just (MBool False)))
                checkDifferenceContradiction facts expected = testAssertEq (runNamedFunction program "contradictoryDifferences" [MList [], MList (map diffFact facts)]) (Ok (Just (MBool expected)))
                checkProduct a b result =
                    case testAssertEq (runNamedFunction program "safeProduct" [MInt a, MInt b]) (Ok (Just result)) of
                        Nothing -> Nothing
                        Just failure -> Just ("safeProduct " ++ show (a, b) ++ ": " ++ failure)
                productValues = [-9223372036854775808, -3, -1, 0, 1, 3, 9223372036854775807]
                productResult a b = let n = a * b in if n < -9223372036854775808 || n > 9223372036854775807 then MData "SumResult::Overflow" [] else MData "SumResult::Sum" [("value", MInt n)]
                refinedContext = Engine.proofContextFromFacts [eq 0 1, le 1 2, le 2 3, ne 0 3]
                checkRefined a b =
                    let expected = Engine.entails (lt a b) refinedContext
                        actual = runNamedFunction program "entailsRefinedOrder" [MList [fact (0,1)], MList [], MList (map mixedFact [(1,2,False),(2,3,False)]), MList [differentFact (0,3)], MInt a, MInt b, MBool True]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                constants = [(30,0,3),(31,0,3),(32,0,5),(33,0,0),(34,1,0)] :: [(Integer,Integer,Integer)]
                constant (i, k, v) = MData "ConstantTerm" [("id", MInt i), ("kind", MInt k), ("value", MInt v)]
                constantExpr i = case i of
                    30 -> CTerm (VInt 3)
                    31 -> CTerm (VInt 3)
                    32 -> CTerm (VInt 5)
                    33 -> CTerm (VInt 0)
                    34 -> CTerm (VBool False)
                    _ -> ATerm (Iota (show i))
                checkConstantEquality a b =
                    let expected = Engine.entails (FApp eqProof [constantExpr a, constantExpr b]) Engine.emptyProofContext
                        actual = runNamedFunction program "entailsSemanticEquality" [MList [], MList [], MList (map constant constants), MInt a, MInt b]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                checkConstantOrder a b =
                    let expected = Engine.entails (FApp (CTerm (builtinFunct (Rel Lt))) [constantExpr a, constantExpr b]) Engine.emptyProofContext
                        actual = runNamedFunction program "entailsSemanticOrder" [MList [], MList [], MList (map constant constants), MList [], MList [], MInt a, MInt b, MBool True]
                     in testAssertEq actual (Ok (Just (MBool expected)))
                validatorContext = MData "ValidatorContext" [("equalities", MList [fact (0,1)]), ("applications", MList []), ("constants", MList []), ("orders", MList (map mixedFact mixed)), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList []), ("universals", MList [])]
                goal name a b = MData ("ValidatorGoal::" ++ name) [("left", MInt a), ("right", MInt b)]
                checkContext name a b expected = testAssertEq (runNamedFunction program "entailsGoal" [validatorContext, goal name a b]) (Ok (Just (MBool expected)))
                boundContext = MData "ValidatorContext" [("equalities", MList []), ("applications", MList (map app [(10,20,[0]),(11,20,[1])])), ("constants", MList []), ("orders", MList (map mixedFact [(0,1,False),(1,0,False)])), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList []), ("universals", MList [])]
                checkBoundCongruence = testAssertEq (runNamedFunction program "entailsGoal" [boundContext, goal "Equal" 10 11]) (Ok (Just (MBool True)))
                emptyContext = MData "ValidatorContext" [("equalities", MList []), ("applications", MList []), ("constants", MList []), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList []), ("universals", MList [])]
                knownOrder = MData "ProofStep::KnownOrder" [("left", MInt 1), ("right", MInt 2), ("strict", MBool True)]
                checkStep = MData "ProofStep::Check" [("goal", goal "Less" 1 2)]
                proofResult ok index = Ok (Just (MData "ProofResult" [("valid", MBool ok), ("failedAt", MInt index)]))
                checkProofSteps = testAssertEq (runNamedFunction program "validateProofSteps" [emptyContext, MList [knownOrder, checkStep]]) (proofResult True (-1))
                checkProofOrder = testAssertEq (runNamedFunction program "validateProofSteps" [emptyContext, MList [checkStep, knownOrder]]) (proofResult False 0)
                checkUnknownStep = testAssertEq (runNamedFunction program "validateProofSteps" [emptyContext, MList [MData "ProofStep::Unknown" []]]) (proofResult False 0)
                checkUnknownGoal = testAssertEq (runNamedFunction program "entailsGoal" [emptyContext, MData "ValidatorGoal::Unknown" []]) (Ok (Just (MBool False)))
                block i steps end = MData "FlowBlock" [("id", MInt i), ("steps", MList steps), ("end", end)]
                done = MData "FlowEnd::Done" []
                jump i = MData "FlowEnd::Jump" [("target", MInt i)]
                branch = MData "FlowEnd::Branch" [("yes", MInt 1), ("no", MInt 2), ("yesFacts", MList [knownOrder]), ("noFacts", MList [])]
                flowResult status b step = Ok (Just (MData "FlowResult" [("status", MInt status), ("block", MInt b), ("step", MInt step)]))
                runFlow blocks = runNamedFunction program "validateFlow" [MList blocks, MInt 0, emptyContext]
                checkFlow = testAssertEq (runFlow [block 0 [] branch, block 1 [checkStep] done, block 2 [] done]) (flowResult 0 2 (-1))
                checkFlowBadBranch = testAssertEq (runFlow [block 0 [] branch, block 1 [checkStep] done, block 2 [checkStep] done]) (flowResult 1 2 0)
                checkFlowCycle = testAssertEq (runFlow [block 0 [] (jump 0)]) (flowResult 4 0 (-1))
                checkFlowMissing = testAssertEq (runFlow [block 0 [] (jump 2)]) (flowResult 3 2 (-1))
                checkFlowDuplicate = testAssertEq (runFlow [block 0 [] done, block 0 [] done]) (flowResult 3 0 (-1))
                checkFlowUnsupported = testAssertEq (runFlow [block 0 [] (MData "FlowEnd::Unsupported" [])]) (flowResult 2 0 (-1))
                initialExecution = MData "ExecutionState" [("context", emptyContext), ("locals", MList [])]
                termRef i = MData "ValueRef::Term" [("term", MInt i)]
                localRef i = MData "ValueRef::Local" [("local", MInt i)]
                assignLocal i ref = MData "ExecutionStep::Assign" [("local", MInt i), ("value", ref)]
                applyLocal local result = MData "ExecutionStep::Apply" [("local", MInt local), ("result", MInt result), ("function", MInt 10), ("arguments", MList [localRef 0])]
                checkLocals = MData "ExecutionStep::Check" [("relation", MInt 0), ("left", localRef 1), ("right", localRef 2)]
                executionSteps = [assignLocal 0 (termRef 1), applyLocal 1 2, applyLocal 2 3, checkLocals]
                checkExecution steps status step = case runNamedFunction program "executeSteps" [initialExecution, MList steps] of
                    Ok (Just (MData "ExecutionResult" fields)) -> testAssertEq (lookup "status" fields, lookup "failedAt" fields) (Just (MInt status), Just (MInt step))
                    result -> Just ("Unexpected execution result: " ++ show result)
                checkSavedComparison function truth relation left right =
                    let comparison = app (10, function, [0,1])
                        bool = constant (20, 1, if truth then 1 else 0)
                        context = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [comparison]), ("constants", MList [bool]), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList []), ("universals", MList [])]
                        initial = MData "ExecutionState" [("context", context), ("locals", MList [])]
                        assume = MData "ExecutionStep::Assume" [("relation", MInt 0), ("left", termRef 10), ("right", termRef 20)]
                        obligation = MData "ExecutionStep::Check" [("relation", MInt relation), ("left", termRef left), ("right", termRef right)]
                     in case runNamedFunction program "executeSteps" [initial, MList [assume, obligation]] of
                            Ok (Just (MData "ExecutionResult" fields)) -> testAssertEq (lookup "status" fields) (Just (MInt 0))
                            result -> Just ("Unexpected saved-comparison result: " ++ show result)
                execEndDone = MData "ExecutionEnd::Done" []
                execJump i = MData "ExecutionEnd::Jump" [("target", MInt i)]
                execBranch = MData "ExecutionEnd::Branch" [("yes", MInt 1), ("no", MInt 2), ("yesSteps", MList []), ("noSteps", MList [])]
                execBlock i steps end = MData "ExecutionBlock" [("id", MInt i), ("steps", MList steps), ("end", end)]
                joinCheck = MData "ExecutionStep::Check" [("relation", MInt 0), ("left", localRef 1), ("right", localRef 0)]
                execBlocks branchValue = [execBlock 0 [assignLocal 0 (termRef 1)] execBranch, execBlock 1 [assignLocal 1 (termRef 1)] (execJump 3), execBlock 2 [assignLocal 1 (termRef branchValue)] (execJump 3), execBlock 3 [joinCheck] execEndDone]
                checkExecutionFlow blocks status blockId = case runNamedFunction program "validateExecution" [MList blocks, MInt 0, initialExecution] of
                    Ok (Just (MData "ExecutionFlowResult" fields)) -> testAssertEq (lookup "status" fields, lookup "block" fields) (Just (MInt status), Just (MInt blockId))
                    result -> Just ("Unexpected execution flow result: " ++ show result)
                checkBooleanBranch constantTerms destinations blocks expected =
                    let context = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [app (10, -8, [0,1])]), ("constants", MList constantTerms), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList []), ("universals", MList [])]
                        initial = MData "ExecutionState" [("context", context), ("locals", MList [])]
                        end = MData "ExecutionEnd::BooleanBranch" [("yes", MInt (fst destinations)), ("no", MInt (snd destinations)), ("join", MInt (-1)), ("value", termRef 10), ("trueValue", termRef 20), ("falseValue", termRef 21)]
                     in case runNamedFunction program "validateExecution" [MList (execBlock 0 [] end : blocks), MInt 0, initial] of
                            Ok (Just (MData "ExecutionFlowResult" fields)) -> testAssertEq (lookup "status" fields) (Just (MInt expected))
                            result -> Just ("Unexpected boolean branch result: " ++ show result)
                checkBooleanJoin rightValue expected =
                    let joinConstants = boolConstants ++ [constant (30, 0, 3), constant (31, 0, rightValue), constant (32, 0, 3)]
                        context = MData "ValidatorContext" [("equalities", MList []), ("applications", MList [app (10, -8, [0,1])]), ("constants", MList joinConstants), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList []), ("universals", MList [])]
                        initial = MData "ExecutionState" [("context", context), ("locals", MList [])]
                        end = MData "ExecutionEnd::BooleanBranch" [("yes", MInt 1), ("no", MInt 2), ("join", MInt 3), ("value", termRef 10), ("trueValue", termRef 20), ("falseValue", termRef 21)]
                        blocks = [execBlock 0 [] end, execBlock 1 [assignLocal 1 (termRef 30)] (execJump 3), execBlock 2 [assignLocal 1 (termRef 31)] (execJump 3), execBlock 3 [MData "ExecutionStep::Check" [("relation", MInt 0), ("left", localRef 1), ("right", termRef 32)]] execEndDone]
                     in case runNamedFunction program "validateExecution" [MList blocks, MInt 0, initial] of
                            Ok (Just (MData "ExecutionFlowResult" fields)) -> testAssertEq (lookup "status" fields) (Just (MInt expected))
                            result -> Just ("Unexpected joined boolean branch result: " ++ show result)
                boolConstants = [constant (20, 1, 1), constant (21, 1, 0)]
                checkMirSubset input expected =
                    let lowered = parseSource input `bindResult` elaborate `bindResult` lowerElaborated
                     in case lowered of
                            Error e -> Just (input ++ ": could not lower test program: " ++ e)
                            Ok mir ->
                                let result = validateMirSubset program mir
                                 in case testAssertEq result (Ok expected) of
                                        Just failure -> Just (input ++ ": " ++ failure ++ "; self-hosted=" ++ show result ++ "\n" ++ M.renderProgram mir)
                                        Nothing -> Nothing
                checkMirSubsetOnly input expected =
                    let lowered = parseSource input `bindResult` elaborate `bindResult` lowerElaborated
                     in case lowered of
                            Error e -> Just (input ++ ": could not lower test program: " ++ e)
                            Ok mir -> case testAssertEq (validateMirSubset program mir) (Ok expected) of
                                Nothing -> Nothing
                                Just failure -> Just (input ++ ": " ++ failure ++ "; self-hosted subset rejected MIR:\n" ++ M.renderProgram mir)
                checkOwnedMirSubset input expected =
                    let lowered = parseSource input `bindResult` elaborate `bindResult` lowerElaborated
                     in case lowered of
                            Error e -> Just (input ++ ": could not lower test program: " ++ e)
                            Ok mir ->
                                let owned = insertOwnership (nativeProgram mir)
                                 in case testAssertEq (validateMirSubset program owned) (Ok expected) of
                                        Nothing -> Nothing
                                        Just failure -> Just (input ++ ": " ++ failure ++ "\n" ++ M.renderProgram owned)
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
                                         in testAssertEq (verifyProgram program') (Ok ()) `orElse` testAssertEq (validateMirSubset program program') (Ok Nothing)
                                    _ -> Just "Fixture has no unique m parameter"
                bridgeFacts = [eq 0 1, lt 1 2, le 2 3]
                checkBridge query = testAssertEq (querySelfHosted program bridgeFacts query) (Ok (Just (Engine.entails query (Engine.proofContextFromFacts bridgeFacts))))
                variantNone = CTerm (VData "Option::None" [])
                variantSome = CTerm (VData "Option::Some" [])
                variantDisequality = FApp (CTerm (builtinFunct (Rel NotEq))) [variantNone, variantSome]
                variantEquality = FApp (CTerm (builtinFunct (Rel Eq))) [variantNone, variantSome]
                ctorNone = FApp (CTerm (builtinFunct (Ctor "Option::None" []))) []
                ctorSome = FApp (CTerm (builtinFunct (Ctor "Option::Some" []))) []
                ctorDisequality = FApp (CTerm (builtinFunct (Rel NotEq))) [ctorNone, ctorSome]
                leftValue = ATerm (Iota "left value")
                symbolicRight = ATerm (Iota "right value")
                leftIsNone = FApp (CTerm (builtinFunct (Is "Option::None"))) [leftValue]
                rightIsSome = FApp (CTerm (builtinFunct (Is "Option::Some"))) [symbolicRight]
                symbolicDisequality = FApp (CTerm (builtinFunct (Rel NotEq))) [leftValue, symbolicRight]
                someOne = CTerm (VData "Option::Some" [("value", VInt 1)])
                someTwo = CTerm (VData "Option::Some" [("value", VInt 2)])
                fieldDisequality = FApp (CTerm (builtinFunct (Rel NotEq))) [someOne, someTwo]
                unrelatedEquality = FApp (CTerm (builtinFunct (Rel Eq))) [CTerm (VInt 0), CTerm (VInt 1)]
             in runSelfHostedChecks
                     ( [ checkOwnedMirSubset "struct Pair { left: Int, right: Int }; fn left(p: Pair) -> Int { return p.left; }; return left(Pair { left: 3, right: 4 });" (Just True)
                          , checkMirSubsetOnly "fn sumFirstLast(lst: List<Int>) -> Int [{ define s = size(lst); rewrite eqToGtZero s; affirm s > 0; }] { return first(lst) + last(lst); }; return sumFirstLast([3, 6]);" (Just True)
                          , checkMirSubsetOnly "fn successor(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { return n + 1; }; fn compose(n: Int) -> Int [{ }] [{ affirm return = successor(successor(n)); }] { return n + 2; }; return compose(3);" (Just True)
                          , checkMirSubsetOnly "fn positiveSuccessor(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n + 1; }] { return n + 1; }; fn compose(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = positiveSuccessor(positiveSuccessor(n)); }] { return n + 2; }; return compose(3);" (Just True)
                          , checkGraphBatch
                          , checkMirSubsetOnly "fn guardedSuccessor(n: Int) -> Int [{ define saved = n; affirm saved >= 0; }] [{ affirm return = saved + 1; }] { return n + 1; }; fn compose(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = guardedSuccessor(n); }] { return n + 1; }; return compose(3);" (Just True)
                          , checkMirSubsetOnly "fn step(n: Int) -> Int [{ define before = n; }] [{ affirm return = before + 1; affirm n = return; }] { n = n + 1; return n; }; fn compose(n: Int) -> Int [{ }] [{ affirm return = step(n); }] { return n + 1; }; return compose(3);" (Just True)
                          , checkMirSubsetOnly "fn generic<n>(a: Array<Int, n>) -> Int [{ }] [{ affirm return = n; }] { return n; }; fn wrap<n>(a: Array<Int, n>) -> Int [{ }] [{ affirm return = generic(a); }] { return n; }; return 0;" (Just True)
                          , checkMirSubsetOnly "fn identity<n>(a: Array<Int, n>) -> Array<Int, n> [{ }] [{ }] { return a; }; fn sizeAfter<n>(a: Array<Int, n>) -> Int [{ }] [{ affirm size(identity(a)) = n; }] { return n; }; return sizeAfter(#[1, 2]);" (Just True)
                          , checkMirSubsetOnly "fn byteValue<n>(a: Array<Int, n>) -> Byte [{ }] [{ }] { return toByte(1); }; fn wrap<n>(a: Array<Int, n>) -> Int [{ }] [{ affirm toInt(byteValue(a)) >= 0; }] { return 0; }; return 0;" (Just True)
                          , checkMirSubsetOnly "fn successor(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { return n + 1; }; fn throughAlias(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { f = successor; g = f; affirm g(n) = n + 1; return n + 1; }; return throughAlias(3);" (Just True)
                          , checkMirSubsetOnly "fn up1(n: Int) -> Int [{ }] [{ affirm return > n; }] { return n + 1; }; fn up2(n: Int) -> Int [{ }] [{ affirm return > n; }] { return n + 2; }; fn throughJoin(choose: Bool, n: Int) -> Int [{ }] [{ affirm return > n; }] { f = up1; if choose { f = up2; }; affirm f(n) > n; return n + 1; }; return throughJoin(true, 3);" (Just True)
                          , checkMirSubsetOnly "fn up(n: Int) -> Int [{ }] [{ affirm return > n; }] { return n + 1; }; fn same(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; }; fn throughJoin(choose: Bool, n: Int) -> Int [{ }] [{ }] { f = up; if choose { f = same; }; affirm f(n) > n; return n + 1; }; return throughJoin(true, 3);" (Just False)
                      , checkMirSubsetOnly "fn positiveSuccessor(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n + 1; }] { return n + 1; }; fn compose(n: Int) -> Int [{ }] [{ affirm return = positiveSuccessor(n); }] { return n + 1; }; return compose(3);" (Just False)
                          , checkMirSubsetOnly "fn add1(i: Int) -> Int { return i + 1; }; fn addThree(a: Int, b: Int, c: Int) -> Int { return a + b + c; }; fn sumFirstLast(lst: List<Int>) -> Int [{ define s = size(lst); rewrite eqToGtZero s; affirm s > 0; }] { return first(lst) + last(lst); }; x = add1(4); y = sumFirstLast([3, 6, 9, 12]); return addThree(x, y, 1);" (Just True)
                          , checkMirSubsetOnly "fn firstWithSize(xs: List<Int>) -> Int [{ define s = size(xs); rewrite eqToGtZero s; affirm s > 0; }] [{ affirm s > 0; affirm return = first(xs); }] { return first(xs); }; x = firstWithSize([3, 6, 9, 12]); affirm x = 3; return x;" (Just True)
                          , checkMirSubsetOnly "fn inc(n: Int) -> Int { return n + 1; }; fn dec(n: Int) -> Int { return n - 1; }; fn apply(choose: Bool, n: Int) -> Int { f = inc; if choose { f = dec; }; return f(n); }; return apply(true, 5);" (Just True)
                          , checkMirSubsetOnly "fn inc(n: Int) -> Int [{ affirm n >= 0; }] { return n + 1; }; fn dec(n: Int) -> Int [{ affirm n >= 0; }] { return n - 1; }; fn apply(choose: Bool, n: Int) -> Int [{ affirm n >= 0; }] { f = inc; if choose { f = dec; }; return f(n); }; return apply(true, 5);" (Just True)
                          , checkMirSubsetOnly "fn apply(f: fn() -> Int) -> Int { return f(); }; fn answer() -> Int { return 42; }; return apply(answer);" (Just True)
                          , checkMirSubsetOnly "fn inc(n: Int) -> Int [{ affirm n >= 0; }] { return n + 1; }; fn dec(n: Int) -> Int { return n - 1; }; fn apply(choose: Bool, n: Int) -> Int { f = inc; if choose { f = dec; }; return f(n); }; return apply(true, 5);" (Just False)
                          , checkMirSubsetOnly "fn base(n: Int) -> Int { return n; }; fn count(n: Int) -> Int [{ affirm n >= 0; }] [{ }] shrinks n { f = count; if n = 1 { f = base; }; if n = 0 { return 0; } else { return f(n - 1); }; }; return count(3);" (Just True)
                          , checkMirSubsetOnly "fn base(n: Int) -> Int { return n; }; fn count(n: Int) -> Int [{ affirm n >= 0; }] [{ }] shrinks n { f = count; if n = 1 { f = base; }; if n = 0 { return 0; } else { return f(n); }; }; return count(3);" (Just False)
                          , checkMirSubsetOnly "fn up1(n: Int) -> Int [{ }] [{ affirm return > n; }] { return n + 1; }; fn up2(n: Int) -> Int [{ }] [{ affirm return > n; }] { return n + 2; }; fn apply(choose: Bool, n: Int) -> Int { f = up1; if choose { f = up2; }; r = f(n); affirm r > n; return r; }; return apply(true, 5);" (Just True)
                          , checkMirSubsetOnly "fn up1(n: Int) -> Int [{ }] [{ define saved = return; affirm saved > n; }] { return n + 1; }; fn up2(n: Int) -> Int [{ }] [{ define result = return; affirm result > n; }] { return n + 2; }; fn apply(choose: Bool, n: Int) -> Int { f = up1; if choose { f = up2; }; r = f(n); affirm r > n; return r; }; return apply(true, 5);" (Just True)
                      , checkMirSubsetOnly "fn up1(n: Int, floor: Int) -> Int [{ }] [{ affirm return = n; affirm return > floor; }] { n = floor + 1; return n; }; fn up2(value: Int, floor: Int) -> Int [{ }] [{ affirm return = value; affirm return > floor; }] { value = floor + 2; return value; }; fn apply(choose: Bool, n: Int, floor: Int) -> Int [{ affirm n = floor; }] { f = up1; if choose { f = up2; }; r = f(n, floor); affirm r > floor; affirm r != n; return r; }; return apply(true, 5, 5);" (Just True)
                      , checkMirSubsetOnly "fn up1(value: Byte, floor: Int) -> Int [{ affirm floor >= 0; affirm floor < 255; }] [{ affirm return = toInt(value); }] { value = toByte(floor + 1); return toInt(value); }; fn up2(byte: Byte, floor: Int) -> Int [{ affirm floor >= 0; affirm floor < 254; }] [{ affirm return = toInt(byte); }] { byte = toByte(floor + 2); return toInt(byte); }; fn apply(choose: Bool, floor: Int) -> Int [{ affirm floor >= 0; affirm floor < 254; }] { f = up1; if choose { f = up2; }; r = f(toByte(floor), floor); affirm r >= 0; affirm r < 256; return r; }; return apply(true, 5);" (Just True)
                          , checkMirSubsetOnly "fn up1(n: Int, floor: Int) -> Int [{ }] [{ affirm return > floor; }] { n = floor + 1; return n; }; fn same(n: Int, floor: Int) -> Int [{ }] [{ affirm return >= floor; }] { n = floor; return n; }; fn apply(choose: Bool, n: Int, floor: Int) -> Int { f = up1; if choose { f = same; }; r = f(n, floor); affirm r > floor; return r; }; return apply(true, 5, 5);" (Just False)
                          , checkMirSubsetOnly "fn up(n: Int) -> Int [{ }] [{ affirm return > n; }] { return n + 1; }; fn same(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; }; fn apply(choose: Bool, n: Int) -> Int { f = up; if choose { f = same; }; r = f(n); affirm r > n; return r; }; return apply(true, 5);" (Just False)
                          , checkMirSubsetOnly "affirm size(Array::boxed(3, 9)) = 3; return 0;" (Just True)
                          , checkMirSubsetOnly "affirm get(Array::boxed(2, 7), 1) = 7; return 0;" (Just True)
                          , checkMirSubsetOnly "affirm size(Array::empty()) = 0; return 0;" (Just True)
                          , checkMirSubsetOnly "enum Choice { Left, Right }; value = Choice::Left; affirm value is Choice::Left; return 0;" (Just True)
                          , checkMirSubsetOnly "enum Choice { Left, Right }; value = Choice::Left; affirm value is Choice::Right; return 0;" (Just False)
                          , checkMirSubsetOnly "enum Choice { Left, Right }; fn acceptsLeft(value: Choice) -> Bool [{ affirm value is Choice::Left; }] [{ affirm return = true; }] { return true; }; return acceptsLeft(Choice::Left);" (Just True)
                          , checkMirSubsetOnly "enum Choice { Left { n: Int }, Right }; fn leftNumber(value: Choice) -> Int [{ affirm value is Choice::Left; }] [{ affirm return = (value as Choice::Left).n; }] { return (value as Choice::Left).n; }; return leftNumber(Choice::Left { n: 5 });" (Just True)
                          , checkMirSubsetOnly "affirm Box::unbox(Box::new(3)) = 3; affirm clone([1, 2]) = [1, 2]; return 0;" (Just True)
                          , checkMirSubsetOnly "enum Choice { Left, Right }; fn acceptsNotLeft(value: Choice) -> Int { if !(value is Choice::Left) { return 0; } else { affirm value is Choice::Left; return 1; }; }; return acceptsNotLeft(Choice::Right);" (Just True)
                          , checkMirSubset "enum Tree { Leaf, Node { left: Box<Tree> } }; fn depth(t: Box<Tree>) -> Int { d = 0; while t is Tree::Node shrinks t { t = (t as Tree::Node).left; d = d + 1; }; return d; }; return depth(Box::new(Tree::Node { left: Box::new(Tree::Leaf) }));" (Just True)
                          ]
                       ++ [ check [] 0 0, check [] 0 1
                      , check [(0,1),(2,3)] 1 0, check [(0,1),(2,3)] 0 3
                      , check [(2,3),(1,2),(0,1)] 0 3, check [(0,1),(0,1),(1,1)] 1 0
                      ] ++
                      [checkProduct a b (productResult a b) | a <- productValues, b <- productValues] ++
                      [ checkCongruence 10 11, checkCongruence 12 13, checkCongruence 10 14
                      , checkOrder 0 4, checkOrder 1 3, checkOrder 4 0, checkOrder 0 0
                      , checkMixed 0 4 True, checkMixed 0 4 False, checkMixed 0 2 True, checkMixed 0 2 False
                      , checkMixed 4 0 False, checkMixed 0 0 False, checkMixed 0 0 True
                      , checkTermOrder 11 5, checkTermOrder 5 11
                      , checkApp 10 11, checkApp 10 12, checkApp 13 14, checkApp 12 10
                      , checkAppOrder 11 5, checkAppOrder 5 11
                      , checkImpossible
                      , checkDifferent 0 2, checkDifferent 2 0, checkDifferent 2 3, checkDifferent 0 3, checkDifferent 0 0
                      , checkDifference 0 4 True, checkDifference 0 2 True, checkDifference 0 2 False, checkDifference 4 0 False
                      , checkDifferenceOverflow
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
                      , checkRefined 1 3, checkRefined 1 2, checkRefined 3 1
                      , checkConstantEquality 30 31, checkConstantEquality 30 32, checkConstantEquality 33 34
                      , checkConstantOrder 30 32, checkConstantOrder 32 30
                      , checkContext "Equal" 0 1 True, checkContext "Less" 0 4 True, checkContext "AtMost" 0 2 True
                      , checkContext "Different" 0 4 True, checkContext "Less" 4 0 False
                      , checkBoundCongruence
                      , checkProofSteps, checkProofOrder, checkUnknownStep, checkUnknownGoal
                      , checkFlow, checkFlowBadBranch, checkFlowCycle, checkFlowMissing, checkFlowDuplicate, checkFlowUnsupported
                      , checkExecution executionSteps 0 (-1), checkExecution [assignLocal 0 (localRef 99)] 2 0
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
                      , checkBooleanBranch boolConstants (1,2) [execBlock 1 [] execEndDone, execBlock 2 [joinCheck] execEndDone] 2
                      , checkBooleanJoin 3 0, checkBooleanJoin 4 1
                      , checkMirSubset "fn f(x: Int) -> Int { if x >= x { return 1; }; }; return f(0);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int { if x > 0 { return 1; }; }; return f(1);" (Just False)
                      , checkMirSubset "x = 1; y = x; affirm y = 1; return y;" (Just True)
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
                      , checkMirSubset "fn f(x: Int, y: Int) -> Int { if x < y { return 0; } else { affirm x < y; }; return 0; }; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x >= 0; }] { return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return >= 0; }] { return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return > 0; }] { return x; }; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return + 1 > 0; }] { return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x + 1 > 0; }] [{ affirm return = x + 1; }] { return x + 1; }; return f(1);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x / 1 > 0; }] { return x; }; return f(1);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x / -1 > 0; }] { return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int, y: Int) -> Int [{ affirm x / y > 0; }] { return x; }; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int, y: Int) -> Int [{ affirm x / y > 0; }] { return x; }; return f(6, 2);" (Just True)
                      , checkMirSubset "fn f(x: Int, y: Int) -> Int [{ affirm x / y > 0; }] { return x; }; return f(1, 0);" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x / -1 > 0; }] { return x; }; return f(-4);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x / -1 > 0; }] { return x; }; min = -9223372036854775807 - 1; return f(min);" (Just False)
                      , checkMirSubset "fn f(xs: List<Int>) -> Int [{ affirm size(xs) > 0; }] [{ affirm return = get(xs, 0); }] { return get(xs, 0); }; return f([5]);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int shrinks x { return x; }; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int { return x; }; return f(1);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int { return x; }; a = f(1); b = f(1); affirm a = b; return 0;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int { return x; }; a = f(1); b = f(2); affirm a = b; return 0;" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int { return x; }; fn g(x: Int) -> Int { return x; }; a = f(1); b = g(1); affirm a = b; return 0;" (Just False)
                      , checkMirSubset "b = readByte(); affirm b >= -1; affirm b < 256; return b;" (Just True)
                      , checkMirSubset "b = readByte(); affirm b = 0; return b;" (Just False)
                      , checkMirSubset "fn f() -> Int { return readByte(); }; a = f(); b = f(); affirm a = b; return 0;" (Just False)
                      , checkMirSubset "b = toByte(255); affirm toInt(b) = 255; return toInt(b);" (Just True)
                      , checkMirSubset "b = toByte(256); return toInt(b);" (Just False)
                      , checkMirSubset "b = writeByte(65); affirm toInt(b) = 65; return toInt(b);" (Just True)
                      , checkMirSubset "b = writeError(65); affirm toInt(b) = 65; return toInt(b);" (Just True)
                      , checkMirSubset "x = 1; y = 2; rewrite checkRel x < y; affirm x < y; return 0;" (Just True)
                      , checkMirSubset "x = 2; y = 1; rewrite checkRel x < y; return 0;" (Just False)
                      , checkMirSubset "x = 5; rewrite checkGtZero x; affirm x > 0; return x;" (Just True)
                      , checkMirSubset "x = 0; rewrite checkGtZero x; return x;" (Just False)
                      , checkMirSubset "x = 2; define saved = x; x = 1; affirm saved = 2; return x;" (Just True)
                      , checkMirSubset "x = 2; define saved = x; x = 1; affirm saved = 1; return x;" (Just False)
                      , checkMirSubset "x = 2; define x = 1; affirm x = 1; x = 3; affirm x = 3; return x;" (Just True)
                      , checkMirSubset "x = 2; define saved = x; if true { affirm saved = 2; }; return x;" (Just True)
                      , checkMirSubset "x = 2; if true { define saved = x; }; affirm saved = 2; return x;" (Just True)
                      , checkMirSubset "x = 2; if false { define saved = x; }; affirm saved = 2; return x;" (Just False)
                      , checkMirSubset "x = 2; flag = true; if flag { define saved = x; }; affirm saved = 2; return x;" (Just True)
                      , checkMirSubset "x = 2; flag = false; if flag { define saved = x; }; affirm saved = 2; return x;" (Just False)
                      , checkMirSubset "x = 2; if x = 2 { define saved = x; }; affirm saved = 2; return x;" (Just True)
                      , checkMirSubset "x = 2; if x != 2 { define saved = x; }; affirm saved = 2; return x;" (Just False)
                      , checkMirSubset "x = 1; if x + 1 = 2 { define saved = x; }; affirm saved = 1; return x;" (Just True)
                      , checkMirSubset "x = 1; if x + 1 = 3 { define saved = x; }; affirm saved = 1; return x;" (Just False)
                      , checkMirSubset "enum Shade { Red, Blue }; shade = Shade::Red; if shade is Shade::Red { define saved = 1; }; affirm saved = 1; return 0;" (Just True)
                      , checkMirSubset "enum Shade { Red, Blue }; shade = Shade::Red; if shade is Shade::Blue { define saved = 1; }; affirm saved = 1; return 0;" (Just False)
                      , checkMirSubset "fn successor(x: Int) -> Int [{ }] [{ define next = x + 1; affirm return = next; }] { return x + 1; }; return successor(4);" (Just True)
                      , checkMirSubset "fn successor(x: Int) -> Int [{ }] [{ define next = x + 1; affirm return = next; }] { return x; }; return successor(4);" (Just False)
                      , checkMirSubset "x = 5; rewrite eqToGtZero x; affirm x > 0; return x;" (Just True)
                      , checkMirSubset "x = 0; rewrite eqToGtZero x; return x;" (Just False)
                      , checkMirSubset "x = 5; rewrite eqToLtPlus1 x; affirm x < x + 1; return x;" (Just True)
                      , checkMirSubset "x = 5; copy = x; rewrite refl x = 5; affirm copy = 5; return 0;" (Just True)
                      , checkMirSubset "zs = [1, 2, 3]; count = size(zs); rewrite evalAll; affirm count = 3; return count;" (Just True)
                      , checkMirSubset "flag = true; affirm flag; return 0;" (Just True)
                      , checkMirSubset "flag = false; affirm flag; return 0;" (Just False)
                      , checkMirSubset "affirm [1, 2] = [1, 2]; return 0;" (Just True)
                      , checkMirSubset "affirm [1, 2] = [1, 3]; return 0;" (Just False)
                      , checkMirSubset "struct Pair { x: Int }; affirm Pair { x: 1 } = Pair { x: 1 }; return 0;" (Just True)
                      , checkMirSubset "struct Pair { x: Int }; affirm Pair { x: 1 } = Pair { x: 2 }; return 0;" (Just False)
                      , checkMirSubset "enum Shade { Red { n: Int }, Blue }; affirm Shade::Red { n: 1 } = Shade::Red { n: 1 }; return 0;" (Just True)
                      , checkMirSubset "enum Shade { Red { n: Int }, Blue }; affirm Shade::Red { n: 1 } = Shade::Blue; return 0;" (Just False)
                      , checkMirSubset "axiom positiveMeansOne(x) [{ affirm x > 0; }] [{ affirm x = 1; }]; x = 5; rewrite positiveMeansOne x; affirm x = 1; return x;" (Just True)
                      , checkMirSubset "axiom positiveMeansOne(x) [{ affirm x > 0; }] [{ affirm x = 1; }]; x = 0; rewrite positiveMeansOne x; return x;" (Just False)
                      , checkMirSubset "axiom positiveMeansOne(x) [{ affirm x > 0; }] [{ affirm x = 1; }]; fn prove(x: Int) -> Int [{ affirm x > 0; }] [{ }] { rewrite positiveMeansOne x; affirm x = 1; return x; }; return prove(5);" (Just True)
                      , checkMirSubset "proof keepPositive(x) [{ affirm x > 0; }] [{ affirm x > 0; }] { affirm x > 0; }; x = 5; rewrite keepPositive x; affirm x > 0; return x;" (Just True)
                      , checkMirSubsetOnly "enum Choice { Left, Right }; proof keepLeft(value) [{ affirm value is Choice::Left; }] [{ affirm value is Choice::Left; }] { affirm value is Choice::Left; }; choice = Choice::Left; rewrite keepLeft choice; affirm choice is Choice::Left; return 0;" (Just True)
                      , checkMirSubsetOnly "enum E { A { x: Int }, B }; fn value(e: E) -> Int [{ affirm e is E::A; }] [{ affirm return = (e as E::A).x; }] { return (e as E::A).x; }; return value(E::A { x: 4 });" (Just True)
                      , checkMirSubset "proof keepPositive(x) [{ affirm x > 0; }] [{ affirm x > 1; }] { affirm x > 1; }; x = 5; rewrite keepPositive x; return x;" (Just False)
                      , checkMirSubset "proof keepPositive(x) [{ affirm x > 0; }] [{ affirm x > 0; }] { affirm x > 0; }; fn prove(x: Int) -> Int [{ affirm x > 0; }] [{ }] { rewrite keepPositive x; affirm x > 0; return x; }; return prove(5);" (Just True)
                      , checkMirSubset "x = 5; proof fixed(x) [{ }] [{ affirm x = 5; }] { affirm x = 5; }; return x;" (Just False)
                      , checkMirSubset "proof positive(x) [{ affirm x > 0; }] [{ affirm x > 1; }] { affirm x > 0; }; x = 5; rewrite positive x; return x;" (Just False)
                      , checkMirSubset "proof increment(x) [{ }] [{ affirm x + 1 > x; }] { affirm x + 1 > x; }; x = 5; rewrite increment x; affirm x + 1 > x; return 0;" (Just True)
                      , checkMirSubset "proof increment(x) [{ }] [{ affirm x + 1 > x; }] { affirm x + 1 > x + 1; }; return 0;" (Just False)
                      , checkMirSubset "proof allBelow(n, m) [{ }] [{ }] { affirm forall j where j >= 0, j < n, n <= m: j < m; }; return 0;" (Just True)
                      , checkMirSubset "proof allAbove(n, m) [{ }] [{ }] { affirm forall j where j >= 0, j < n, n <= m: j > m; }; return 0;" (Just False)
                      , checkMirSubset "proof definedPositive(x) [{ affirm x + 1 > x; }] [{ affirm x + 1 > x; }] { define next = x + 1; affirm next > x; }; x = 5; rewrite definedPositive x; affirm x + 1 > x; return 0;" (Just True)
                      , checkMirSubset "axiom definedPositive(x) [{ define next = x + 1; affirm next > x; }] [{ affirm x + 1 > x; }]; x = 5; rewrite definedPositive x; affirm x + 1 > x; return 0;" (Just True)
                      , checkMirSubset "proof definedPositive(x) [{ define next = x + 1; affirm next > x; }] [{ affirm next > x; }] { affirm next > x; }; x = 5; rewrite definedPositive x; return 0;" (Just True)
                      , checkMirSubset "fn successor(x: Int) -> Int [{ define next = x + 1; affirm next > x; }] [{ affirm return = next; }] { return x + 1; }; return successor(5);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > 0; }] { return x; }; return f(1);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > 0; }] { return x; }; return f(0);" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int [{ }] [{ affirm return = x; }] { return x; }; x = 3; x = f(x); affirm x = 3; return x;" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ }] [{ affirm return = x; }] { x = 2; return x; }; return f(1);" (Just True)
                      , checkMirSubset "fn g() -> Int [{ }] [{ affirm return = 2; }] { return 2; }; fn f(x: Int) -> Int [{ }] [{ affirm return = x; }] { x = g(); return x; }; return f(1);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ }] [{ affirm x > 0; affirm return = x; }] { x = 2; return x; }; y = f(1); affirm y > 0; return 0;" (Just True)
                      , checkMirSubset "fn setFlag(flag: Bool) -> Int [{ }] [{ affirm flag = true; }] { flag = true; return 0; }; return setFlag(false);" (Just True)
                      , checkMirSubset "fn setList(xs: List<Int>) -> Int [{ }] [{ affirm xs = [2]; }] { xs = [2]; return 0; }; return setList([1]);" (Just True)
                      , checkMirSubset "fn f(x: Int) -> Int [{ }] [{ affirm return > 0; }] { return x; }; return f(1);" (Just False)
                      , checkMirSubset "fn yes() -> Bool [{ }] [{ affirm return = true; }] { return true; }; flag = yes(); if flag { return 1; } else { affirm 0 = 1; return 0; };" (Just True)
                      , checkMirSubset "fn g(x: Int) -> Int [{ }] [{ affirm return = x; }] { return x; }; fn f(x: Int) -> Int [{ }] [{ affirm return = x; }] { return g(x); }; return f(2);" (Just True)
                      , checkMirSubset "fn g(x: Int) -> Int [{ affirm x > 0; }] { return x; }; fn f(x: Int) -> Int { return g(x); }; return f(1);" (Just False)
                      , checkMirSubset "fn identity(x: Int) -> Int [{ }] [{ affirm return = x; }] { return x; }; f = identity; return f(4);" (Just True)
                      , checkMirSubset "fn identity(x: Int) -> Int [{ }] [{ affirm return = x; }] { return x; }; f = identity; g = f; return g(4);" (Just True)
                      , checkMirSubset "fn identity(x: Int) -> Int [{ }] [{ affirm return = x; }] { return x; }; f = identity; if true { n = 1; } else { n = 2; }; return f(4);" (Just True)
                      , checkMirSubset "fn positive(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > 0; }] { return x; }; f = positive; return f(0);" (Just False)
                      , checkMirSubset "fn f(x: Int) -> Int { return f(x); }; return f(1);" (Just False)
                      , checkMirSubset "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] shrinks n { if n = 0 { return 0; } else { return f(n - 1); }; }; return f(3);" (Just True)
                      , checkMirSubset "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] shrinks n { if n = 0 { return 0; } else { return f(n); }; }; return f(1);" (Just False)
                      , checkMirSubset "enum Tree { Leaf, Branch { left: Box<Tree> } }; fn count(t: Box<Tree>) -> Int shrinks t { return match t { Tree::Leaf => 0, Tree::Branch { left: left } => count(left) }; }; return count(Box::new(Tree::Leaf));" (Just True)
                      , checkMirSubset "enum Tree { Leaf, Branch { left: Box<Tree> } }; fn loop(t: Box<Tree>) -> Int shrinks t { return loop(t); }; return 0;" (Just False)
                      , checkMirSubset "return 7 / 1;" (Just True)
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
                      , checkMirSubset "xs = [1, 2]; affirm size(xs) = 2; return size(xs);" (Just True)
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
                      , checkMirSubset "struct P { x: Int }; p = P { x: 4 }; affirm p.x = 4; return p.x;" (Just True)
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
                      , checkMirSubset "xs = [4]; xs = push(xs, 5); affirm size(xs) = 2; affirm get(xs, 1) = 5; return 0;" (Just True)
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
                      , checkMirSubset "x = 1; if x = 1 { return 1; } else { return 2; };" (Just True)
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
                      , checkMirSubset "i = 2; while i > 0 [{ affirm i >= 0; }] shrinks i { i = i - 1; }; affirm i = 0; return i;" (Just True)
                      , checkMirSubset "i = 2; while i > 0 [{ }] shrinks i { i = i - 1; }; return i;" (Just True)
                      , checkMirSubset "i = 2; while i > 0 [{ affirm i >= 1; }] shrinks i { i = i - 1; }; return i;" (Just False)
                      , checkMirSubset "i = 2; while i > 0 shrinks i { i = i + 1; }; return i;" (Just False)
                      , checkMirSubset "i = 0; while i < 2 shrinks 2 - i { i = i + 1; }; return i;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 [{ }] shrinks 2 - i { affirm i >= 0; i = i + 1; }; return i;" (Just True)
                      , checkMirSubset "out = []; i = 0; while i < 3 [{ }] shrinks 3 - i { out = push(out, i); i = i + 1; }; affirm size(out) = i; return i;" (Just True)
                      , checkMirSubset "out = []; i = 0; while i < 3 [{ }] shrinks 3 - i { out = push(out, i); i = i + 1; }; affirm size(out) = i + 1; return i;" (Just False)
                      -- The entry and back-edge checks prove this inferred bound even though the reference validator declines it.
                      , checkMirSubsetOnly "n = 2; i = 0; while i < n [{ }] shrinks n - i { i = i + 1; }; affirm i = n; return i;" (Just True)
                      , checkMirSubsetOnly "i = 0; j = 2; while i < 3 [{ }] shrinks 3 - i { i = i + 1; j = j + 1; }; affirm j = i + 2; return j;" (Just True)
                      , checkMirSubsetOnly "i = 3; j = 1; while i > 0 [{ }] shrinks i { i = i - 1; j = j - 1; }; affirm j = i - 2; return j;" (Just True)
                      , checkMirSubsetOnly "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = 0; while i < n [{ }] shrinks n - i { i = i + 1; }; affirm i = n; return i; }; return f(2);" (Just True)
                      , checkMirSubsetOnly "xs = [4, 5]; i = 0; while i < size(xs) [{ }] shrinks 2 - i { i = i + 1; }; affirm i = 2; return i;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 [{ affirm i + 1 <= 3; }] shrinks 2 - i { i = i + 1; }; return i;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 [{ define next = i + 1; affirm next > i; }] shrinks 2 - i { i = i + 1; }; return i;" (Just True)
                      , checkMirSubset "affirm forall j in 0..3: j >= 0; return 0;" (Just True)
                      , checkMirSubset "affirm forall j in 0..3: j < 2; return 0;" (Just False)
                      , checkMirSubset "n = 3; affirm forall j in 0..n: j < n; return 0;" (Just True)
                      , checkMirSubset "n = 3; affirm forall j in 0..n: j < 2; return 0;" (Just False)
                      , checkMirSubset "fn f(n: Int) -> Int { affirm forall j in 0..n: j < n; return 0; }; return f(3);" (Just True)
                      , checkMirSubset "fn f(n: Int) -> Int { affirm forall j in 0..n: j <= n; return 0; }; return f(3);" (Just True)
                      , checkMirSubset "fn f(n: Int) -> Int { affirm forall j in 0..n: j >= 0; return 0; }; return f(3);" (Just True)
                      , checkMirSubset "fn f(n: Int) -> Int { affirm forall j in 0..n: j >= 0; affirm forall j in 0..n: j <= n; return 0; }; return f(3);" (Just True)
                      , checkMirSubset "fn f(n: Int) -> Int { affirm forall j in 0..n: j > 0; return 0; }; return f(3);" (Just False)
                      , checkMirSubset "fn f(n: Int, x: Int) -> Int [{ affirm n > 0; affirm forall i in 0..n: x > 0; }] { affirm x > 0; return x; }; return f(2, 1);" (Just True)
                      , checkMirSubset "fn f(n: Int, x: Int) -> Int [{ affirm forall i in 0..n: x > 0; }] { affirm x > 0; return x; }; return f(2, 1);" (Just False)
                      , checkMirSubset "fn f(n: Int, x: Int) -> Int [{ affirm n <= 0; affirm forall i in 0..n: x > 0; }] { affirm x > 0; return x; }; return f(0, 1);" (Just False)
                      , checkMirSubsetOnly "fn ready(n: Int, flag: Bool) -> Bool [{ affirm n > 0; affirm forall i in 0..n: flag; }] { affirm flag; return flag; }; return ready(1, true);" (Just True)
                      , checkMirSubsetOnly "fn notReady(n: Int, flag: Bool) -> Bool [{ affirm n > 0; affirm forall i in 0..n: !flag; }] { affirm !flag; return flag; }; return notReady(1, false);" (Just True)
                      , checkMirSubsetOnly "fn onePositive(n: Int, x: Int, y: Int) -> Bool [{ affirm n > 0; affirm forall i in 0..n: x > 0 || y > 0; }] { affirm x > 0 || y > 0; return true; }; return onePositive(1, 1, 0);" (Just True)
                      , checkMirSubsetOnly "fn nonnegativeWitness(n: Int, x: Int) -> Int [{ affirm n > 0; affirm forall i in 0..n: i <= x; }] { affirm 0 <= x; return x; }; return nonnegativeWitness(2, 2);" (Just True)
                      , checkMirSubsetOnly "fn boundedUniversal(n: Int, j: Int, x: Int) -> Int [{ affirm j >= 0; affirm j < n; affirm forall i in 0..n: i <= x; }] { affirm j <= x; return x; }; return boundedUniversal(3, 1, 2);" (Just True)
                      , checkMirSubsetOnly "fn strictUniversal(n: Int, j: Int, x: Int) -> Int [{ affirm j >= 0; affirm j < n; affirm forall i in 0..n: i < x; }] { affirm j <= x; return x; }; return strictUniversal(3, 1, 4);" (Just True)
                      , checkMirSubsetOnly "fn symmetricUniversal(n: Int, j: Int, x: Int) -> Int [{ affirm j >= 0; affirm j < n; affirm forall i in 0..n: x != i; }] { affirm j != x; return x; }; return symmetricUniversal(3, 1, 4);" (Just True)
                      , checkMirSubsetOnly "fn joinedUniversal(n: Int, j: Int, x: Int, flag: Bool) -> Int [{ affirm j >= 0; affirm j < n; affirm forall i in 0..n: i <= x; }] { if flag { affirm true; } else { affirm true; }; affirm j <= x; return x; }; return joinedUniversal(3, 1, 2, true);" (Just True)
                      , checkMirSubsetOnly "fn branchUniversal(n: Int, j: Int, x: Int, flag: Bool) -> Int [{ affirm j >= 0; affirm j < n; }] { if flag { a = n + 1; affirm forall i in 0..n: i <= x; } else { a = n + 1; b = n + 2; affirm forall i in 0..n: i <= x; }; affirm j <= x; return x; }; return branchUniversal(3, 1, 2, true);" (Just True)
                      , checkMirSubsetOnly "fn joinCompare(x: Int, y: Int) -> Int { if x < y { x = y; } else { y = x; }; affirm x = y; return x; }; return joinCompare(1, 2);" (Just True)
                      , checkMirSubsetOnly "enum E { A, B }; affirm E::A != E::B; return 0;" (Just True)
                      , checkMirSubsetOnly "enum E { A, B }; affirm E::A = E::B; return 0;" (Just False)
                      , checkMirSubsetOnly "enum E { A, B }; fn distinct() -> Bool { a = E::A; b = E::B; affirm a != b; return true; }; affirm distinct(); return 0;" (Just True)
                      , checkMirSubsetOnly "enum E { A, B }; fn equal(a: E, b: E) -> Bool { affirm a = b; return true; }; x = E::A; y = E::B; affirm equal(x, y); return 0;" (Just False)
                      , checkMirSubsetOnly "enum E { A, B, C }; fn distinct(a: E, b: E) -> Bool { if a is E::A { if b is E::B { affirm a != b; }; }; return true; }; return distinct(E::A, E::B);" (Just True)
                      , checkMirSubsetOnly "enum E { A, B }; fn distinct(a: E, b: E) -> Bool { if a is E::A { } else { if b is E::A { affirm a != b; }; }; return true; }; return distinct(E::B, E::A);" (Just True)
                      , checkMirSubsetOnly "enum E { A, B }; fn distinct(a: E, b: E) -> Bool { flag = a is E::A; alias = flag; if alias { if b is E::B { affirm a != b; }; }; return true; }; return distinct(E::A, E::B);" (Just True)
                      , checkMirSubsetOnly "enum E { A, B }; fn impossible(e: E) -> Int { if e is E::A { if e is E::B { affirm 1 = 2; }; }; return 0; }; return impossible(E::A);" (Just True)
                      , checkMirSubsetOnly "enum E { A, B }; fn stale(e: E) -> Bool { flag = e is E::A; e = E::B; if flag { affirm e is E::A; }; return true; }; return stale(E::A);" (Just False)
                      , checkMirSubsetOnly "fn unboundedUniversal(n: Int, j: Int, x: Int) -> Int [{ affirm j >= 0; affirm j < n; }] { affirm j <= x; return x; }; return unboundedUniversal(3, 1, 2);" (Just False)
                      , checkMirSubsetOnly "fn outsideUniversal(n: Int, j: Int, x: Int) -> Int [{ affirm j = n; affirm forall i in 0..n: i <= x; }] { affirm j <= x; return x; }; return outsideUniversal(3, 3, 4);" (Just False)
                      , checkMirSubsetOnly "fn guarded(n: Int, m: Int, x: Int) -> Int [{ affirm n > 1; affirm n <= m; affirm forall i where i >= 1, i < n, n <= m: x > 0; }] { affirm x > 0; return x; }; return guarded(2, 3, 1);" (Just True)
                      , checkMirSubsetOnly "fn witnessed(n: Int, x: Int) -> Int [{ affirm n > 1; affirm forall i where i >= 0, i < n, i = 1: x > 0; }] { affirm x > 0; return x; }; return witnessed(2, 1);" (Just True)
                      , checkMirSubsetOnly "fn emptyWitness(n: Int, x: Int) -> Int [{ affirm n > 2; affirm forall i where i >= 2, i < n, i = 1: x > 0; }] { affirm x > 0; return x; }; return emptyWitness(3, 1);" (Just False)
                      , checkMirSubsetOnly "proof nonemptyPositive(n: Int, x: Int) [{ affirm n > 0; affirm forall i in 0..n: x > 0; }] [{ affirm x > 0; }]; n = 2; x = 1; rewrite nonemptyPositive(n, x); affirm x > 0; return 0;" (Just True)
                      , checkMirSubsetOnly "fn f(n: Int) -> Int [{ affirm forall j in 0..3: j < n; }] { affirm 2 < n; return 0; }; return f(3);" (Just True)
                      , checkMirSubsetOnly "fn f(n: Int) -> Int [{ affirm forall j in 0..3: j < n; }] { affirm 2 < n; return 0; }; return f(2);" (Just False)
                      , checkMirSubsetOnly "fn f(n: Int) -> Int [{ }] [{ affirm forall j in 0..3: j < return; }] { return n; }; r = f(3); affirm 2 < r; return 0;" (Just True)
                      , checkMirSubset "n = 4; affirm forall j in 0..n - 1: j < n; return 0;" (Just True)
                      , checkMirSubset "n = 4; affirm forall j in 0..n - 1: j < 2; return 0;" (Just False)
                      , checkMirSubset "lo = 1; hi = 4; affirm forall j in lo..hi: j >= 1; return 0;" (Just True)
                      , checkMirSubset "n = 0; affirm forall j in 0..n: j = 100; return 0;" (Just True)
                      , checkMirSubset "fn f(n: Int, m: Int) -> Int { affirm forall j where j >= 0, j < n, n <= m: j < m; return 0; }; return f(3, 4);" (Just True)
                      , checkMirSubset "fn f(n: Int, m: Int) -> Int { affirm forall j where j >= 0, j < n, n <= m: j > m; return 0; }; return f(3, 4);" (Just False)
                      , checkMirSubset "axiom below(n) [{ }] [{ affirm forall i in 0..n: i < n; }]; n = 3; rewrite below n; affirm forall j in 0..n: j < n; return 0;" (Just True)
                      , checkMirSubset "fn f(n: Int) -> Int { affirm forall i in 0..n: i < n; return 0; }; return f(3);" (Just True)
                      , checkMirSubset "fn f(n: Int) -> Int { affirm forall i in 0..n: i < 2; return 0; }; return f(3);" (Just False)
                      , checkMirSubset "affirm true && true; return 0;" (Just True)
                      , checkMirSubset "affirm true && false; return 0;" (Just False)
                      , checkMirSubset "affirm false = false; return 0;" (Just True)
                      , checkMirSubset "affirm 1 >= 2; return 0;" (Just False)
                      , testAssertErrorContains "a proof is not made" (parseSource "affirm true || false; return 0;")
                      , testAssertErrorContains "a proof is not made" (parseSource "x = 3; affirm x < 2 || x > 4; return 0;")
                      , checkMirSubset "fn scale(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > 0; }] { return 2 * x; }; return scale(3);" (Just True)
                      , checkMirSubset "fn scale(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] { return 2 * x; }; return scale(3);" (Just True)
                      , checkMirSubset "fn scale(x: Int) -> Int [{ affirm x < 0; }] [{ affirm return < x; }] { return 2 * x; }; return scale(-3);" (Just True)
                      , checkMirSubset "fn scale(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return < x; }] { return -2 * x; }; return scale(3);" (Just True)
                      , checkMirSubset "fn scale(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > 0; }] { return -2 * x; }; return scale(3);" (Just False)
                      , checkMirSubset "fn rem(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return >= 0; affirm return < 3; }] { return x % 3; }; return rem(10);" (Just True)
                      , checkMirSubset "fn rem(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return <= 0; affirm return > -3; }] { return x % -3; }; return rem(10);" (Just True)
                      , checkMirSubset "fn rem(x: Int, d: Int) -> Int [{ affirm d > 0; }] [{ affirm return >= 0; affirm return < d; }] { return x % d; }; return rem(10, 3);" (Just True)
                      , checkMirSubset "fn rem(x: Int, d: Int) -> Int [{ affirm d < 0; }] [{ affirm return <= 0; affirm return > d; }] { return x % d; }; return rem(10, -3);" (Just True)
                      , checkMirSubset "fn quot(x: Int, d: Int) -> Int [{ affirm d > 0; affirm x >= 0; }] [{ affirm return >= 0; affirm return <= x; }] { return x / d; }; return quot(10, 3);" (Just True)
                      , checkMirSubset "fn quot(x: Int, d: Int) -> Int [{ affirm d < 0; affirm x >= 0; }] [{ affirm return <= 0; }] { return x / d; }; return quot(10, -3);" (Just True)
                      , checkMirSubset "s = 0; for i in 0..3 { s = s + 1; }; return s;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 shrinks 2 - i { i = i - 1; }; return i;" (Just False)
                      , checkMirSubset "n = 2; i = 0; while i < n shrinks n - i { i = i + 1; n = n + 1; }; return i;" (Just False)
                      , checkMirSubset "n = 2; i = 0; while i < n shrinks n - i { i = i + 1; n = n + 0; }; return i;" (Just True)
                      , checkMirSubset "enum Tree { Leaf, Node { left: Box<Tree> } }; t = Box::new(Tree::Node { left: Box::new(Tree::Leaf) }); d = 0; while t is Tree::Node shrinks t { if d = 0 { child = (t as Tree::Node).left; t = child; d = 1; } else { return d; }; }; return d;" (Just True)
                      , checkMirSubset "xs = [1]; for i in 0..size(xs) { if get(xs, i) > 0 { return 1; }; }; return 0;" (Just True)
                      , checkMirSubset "xs = [1]; for i in 0..size(xs) { if get(xs, i) > 0 { return 1; }; }; affirm 0 = 1; return 0;" (Just False)
                      , checkMirSubset "s = 0; for i in 0..1 { for j in 0..1 { s = s + 1; }; }; return s;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { if i < 2 { i = i + 1; } else { i = i + 0; }; }; return i;" (Just True)
                      , checkMirSubset "i = 0; while i < 2 [{ affirm i >= 0; affirm i <= 2; }] shrinks 2 - i { if i < 2 { i = i + 1; } else { i = i + 0; }; }; affirm i = 2; return i;" (Just True)
                      , checkMirSubset "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { i = i + 1; }; return i; }; return f(3);" (Just True)
                      , checkMirSubset "xs = [1]; for i in 0..size(xs) { affirm i >= 0; affirm i < size(xs); }; return 0;" (Just True)
                      , checkMirSubset "xs = [1]; for i in 0..size(xs) { if i > 0 { affirm i >= 1; }; }; return 0;" (Just True)
                      , checkMirSubset "fn f(xs: List<Int>) -> Int { affirm size(xs) >= 0; return 0; }; return f([]);" (Just True)
                      , checkMirSubset "fn f(xs: List<Int>) -> Int { affirm size(xs) >= 1; return 0; }; return f([]);" (Just False)
                      , checkMirSubset "fn spin(x: Int) -> Int ~ { return x; }; fn relay(x: Int) -> Int ~ { return spin(x); }; return 0;" (Just True)
                      , checkMirSubset "fn replace(n: Int) -> Int [{ affirm n = 1; }] [{ affirm return = 4; }] { n = 2; return 4; }; return replace(1);" (Just True)
                      , checkMirSubset "fn bump(n: Int) -> Int [{ }] [{ affirm return = n; }] { n = n + 1; return n; }; return bump(1);" (Just True)
                      , checkMirSubset "enum E { A { n: Int }, B }; e = E::A { n: 5 }; return (e as E::A).n;" (Just True)
                      , checkMirSubset "enum E { A { n: Int }, B }; fn extract(e: E) -> Int { return match e { E::A { n: n } => n, E::B => 0 }; }; return extract(E::A { n: 5 });" (Just True)
                      , checkMirSubset "enum E { A, B }; e = E::A; if e is E::A { affirm 1 = 1; } else { affirm 1 = 2; }; return 0;" (Just True)
                      , checkMirSubset "enum E { A, B }; e = E::A; if e is E::B { affirm 1 = 2; } else { affirm 1 = 1; }; return 0;" (Just True)
                      , checkMirSubset "enum E { A, B }; e = E::A; if e is E::A { affirm 1 = 1; } else { affirm 1 = 2; }; return 0;" (Just True)
                      , checkMirSubset "struct Boxed<T> { value: T, n: Int } invariant [{ affirm n >= 0; }]; fn number<T>(b: Boxed<T>) -> Int [{ }] [{ affirm return >= 0; }] { return b.n; }; return number(Boxed<Int> { value: 1, n: 3 });" (Just True)
                      , checkMirSubset "struct Boxed<T> { value: T, n: Int } invariant [{ affirm n >= 0; }]; return Boxed<Int> { value: 1, n: 3 }.n;" (Just True)
                      , checkMirSubset "struct Boxed<T> { value: T, n: Int } invariant [{ affirm n >= 0; }]; return Boxed<Int> { value: 1, n: -1 }.n;" (Just False)
                      , checkMirSubset "x = 1; y = 2; xs = push(push([], x), y); affirm size(xs) = 2; affirm get(xs, 1) = 2; return 0;" (Just True)
                      , checkMirSubset "x = 1; y = 2; xs = push(push([], x), y); affirm get(xs, 1) = 1; return 0;" (Just False)
                      , checkBridge (lt 0 3), checkBridge (lt 3 0), checkBridge (ne 0 3), checkBridge (eq 0 1)
                      , testAssertEq (querySelfHosted program [] variantDisequality) (Ok (Just True))
                      , testAssertEq (querySelfHosted program [] ctorDisequality) (Ok (Just True))
                      , testAssertEq (querySelfHosted program [] fieldDisequality) (Ok (Just True))
                      , testAssertEq (querySelfHosted program [variantEquality] unrelatedEquality) (Ok (Just True))
                      , testAssertEq (querySelfHosted program [leftIsNone, rightIsSome] symbolicDisequality) (Ok (Just True))
                      , testAssertEq (querySelfHosted program [leftIsNone, FApp (CTerm (builtinFunct (Is "Option::Some"))) [leftValue]] unrelatedEquality) (Ok (Just True))
                      , testAssertEq (querySelfHosted program [] (BVar "i")) (Ok Nothing)
                      , testAssertErrorContains "Function does not exist" (runNamedFunction program "missing" [])
                      , testAssertErrorContains "expected 3 arguments" (runNamedFunction program "hasEquality" [])
                      ] )

-- The differential matrix executes the checker many times in one process.
-- Force each result sequentially and print progress checkpoints.
runSelfHostedChecks :: [TestResult] -> IO TestResult
runSelfHostedChecks = go (0 :: Int)
  where
    go _ [] = pure Nothing
    go count (result : rest) = do
        let count' = count + 1
        when (count' <= 4 || count' `mod` 64 == 0) $
            putStrLn ("Checked " ++ show count' ++ " self-hosted validator cases")
        case result of
            Just failure -> pure (Just failure)
            Nothing -> go count' rest

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

-- The stages of a program, and what each one hands to the next
testPipeline :: Test
testPipeline =
    testCaseSeq
        "testPipeline"
        [ -- Each stage names itself in its error
          testAssertErrorContains "Parse error" (parseSource "x = ;")
        , testAssertErrorContains "Validation failed: Could not prove" (compileSource "x = 1; affirm x = 2;")
        , testAssertErrorContains "Validation failed: Type error" (compileSource "x = 1; y = x(2);")
        , -- A program that does not validate is not lowered
          testAssertErrorContains "Validation failed" (compileSource "x = 1; affirm x = 2;")
        , -- The checked program has each `shrinks` clause resolved, and is the one that gets lowered
          case parseSource "i = 0; while i < 3 shrinks 3 - i { i = i + 1; };" `bindResult` elaborate of
            Ok stmts -> testAssertTrue (not (null [() | While _ _ (Just (Counting _)) _ <- stmts]))
            Error e -> Just e
        , case compileSource "i = 0; while i < 3 shrinks 3 - i { i = i + 1; }; return i;" of
            Ok program -> testAssertEq (mapResult (fmap renderMirValue) (runProgram program), Map.size (M.fnBlocks (M.progMain program))) (Ok (Just "3"), 4)
            Error e -> Just e
        , -- The MIR of a program is verified: a program with no return type to agree on never gets that far
          testAssertErrorContains "Validation failed: Type error" (compileSource "if true { return 1; } else { return false; };")
        , testAssertEq (mapResult (const ()) (compileSource "")) (Ok ())
        , case parseSource "x = 1; affirm x = 1; return x;" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> testAssertEq (validateMir program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "fn f(xs: List<Int>) -> Int [{ affirm size(xs) > 1; define item = get(xs, 1); affirm item = item; }] [{ }] { return 0; }; return f([10, 20]);" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> testAssertEq (validateMir program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "fn f(x: Int) -> Int { if x >= x { return 1; }; }; return f(0);" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> testAssertEq (validateMir program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "fn f(x: Int) -> Int [{ affirm x / 1 > 0; }] { return x; }; return 0;" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program ->
                testAssertEq (validateMir program) (Ok (Just True))
                    `orElse` testAssertEq (mapResult (const ()) (compileSource "fn f(x: Int) -> Int [{ affirm x / 1 > 0; }] { return x; }; return 0;")) (Ok ())
            Error e -> Just e
        , case parseSource "fn add1(i: Int) -> Int { return i + 1; }; fn addThree(a: Int, b: Int, c: Int) -> Int { return a + b + c; }; fn sumFirstLast(lst: List<Int>) -> Int [{ define s = size(lst); rewrite eqToGtZero s; affirm s > 0; }] { return first(lst) + last(lst); }; x = add1(4); y = sumFirstLast([3, 6, 9, 12]); return addThree(x, y, 1);" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> testAssertEq (validateMir program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "fn apply(f: fn(Int) -> Int, n: Int) -> Int { return f(n); }; fn up(n: Int) -> Int { return n + 1; }; fn down(n: Int) -> Int { return n - 1; }; f = up; return apply(up, 2) + apply(f, 2);" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "fn apply(f: fn(Int) -> Int, n: Int) -> Int { return f(n); }; fn needsPositive(n: Int) -> Int [{ affirm n > 0; }] { return n; }; return apply(needsPositive, 0);" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just False))
            Error e -> Just e
        , case parseSource "struct Target { value: Int }; fn apply(f: fn(Target) -> Int, x: Target) -> Int { affirm f(x) = f(x); return 0; }; fn answer(x: Target) -> Int [{ }] [{ affirm return = 42; }] { return 42; }; fn anotherAnswer(x: Target) -> Int [{ }] [{ affirm return = 42; }] { return 42; }; return apply(answer, Target { value: 0 });" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "struct Target { value: Int }; fn apply(f: fn(Target) -> Int, x: Target) -> Int { affirm f(x) = f(x); return 0; }; fn answer(x: Target) -> Int [{ }] [{ affirm return = 42; }] { return 42; }; fn needsPositive(x: Target) -> Int [{ affirm x.value > 0; }] [{ affirm return = 42; }] { return 42; }; return apply(answer, Target { value: 0 });" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just False))
            Error e -> Just e
        , case parseSource "struct Target { value: Int }; fn apply(f: fn(Target) -> Int, x: Target) -> Int { affirm f(x) >= 0; return 0; }; fn answer(x: Target) -> Int [{ }] [{ affirm return >= 0; affirm return <= 10; }] { return 1; }; fn anotherAnswer(x: Target) -> Int [{ }] [{ affirm return >= 0; affirm return <= 100; }] { return 2; }; return apply(answer, Target { value: 0 });" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "enum Tree { Leaf, Branch { left: Box<Tree>, value: Int, right: Box<Tree> } }; fn sum(t: Box<Tree>) -> Int shrinks Box::unbox(t) { return match t { Tree::Leaf => 0, Tree::Branch { left: l, value: v, right: r } => v + sum(l) + sum(r) }; }; return sum(Box::new(Tree::Branch { left: Box::new(Tree::Leaf), value: 2, right: Box::new(Tree::Leaf) }));" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "enum Tree { Leaf, Node { left: Box<Tree> } }; fn depth(t: Box<Tree>) -> Int { d = 0; while t is Tree::Node shrinks Box::unbox(t) { t = (t as Tree::Node).left; d = d + 1; }; return d; }; return depth(Box::new(Tree::Node { left: Box::new(Tree::Leaf) }));" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "enum Tree { Leaf, Node { left: Box<Tree> } }; fn depth(t: Box<Tree>) -> Int shrinks t { if t is Tree::Node { t = (t as Tree::Node).left; return depth(t); } else { return 0; }; }; return depth(Box::new(Tree::Node { left: Box::new(Tree::Leaf) }));" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "enum Tree { Leaf, Node { left: Box<Tree> } }; fn depth(t: Box<Tree>) -> Int shrinks t { t = Box::new(Tree::Leaf); return depth(t); }; return depth(Box::new(Tree::Node { left: Box::new(Tree::Leaf) }));" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok Nothing)
            Error e -> Just e
        , case parseSource "fn maybe(flag: Bool) -> Int [{ affirm flag = true; }] ~ { while flag [{ affirm flag = true; }] ~ { flag = true; }; return 0; }; return 0;" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "fn maybe(flag: Bool) -> Int [{ affirm flag = true; }] ~ { while flag [{ affirm flag = true; }] ~ { flag = false; }; return 0; }; return 0;" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just False))
            Error e -> Just e
        , case parseSource "xs = [10, 20]; i = 0; while i < size(xs) [{ affirm i >= 0; affirm i <= size(xs); }] shrinks size(xs) - i { i = i + 1; }; affirm i = size(xs); return i;" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just True))
            Error e -> Just e
        , case parseSource "fn maybe(flag: Bool) -> Int { while flag ~ { flag = false; }; return 0; }; return 0;" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok Nothing)
            Error e -> Just e
        , case parseSource "axiom successorPositive(n) [{ affirm n >= 0; }] [{ affirm n + 1 > 0; }]; proof establishSuccessorPositive(n) [{ affirm n >= 0; }] [{ affirm n + 1 > 0; }] { rewrite successorPositive n; }; fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm n + 1 > 0; }] { rewrite establishSuccessorPositive n; return n; }; return f(0);" `bindResult` elaborate `bindResult` lowerElaborated of
            Ok program -> case checkerProgram of
                Error e -> Just e
                Ok checker -> testAssertEq (validateMirSubset checker program) (Ok (Just True))
            Error e -> Just e
        ]
