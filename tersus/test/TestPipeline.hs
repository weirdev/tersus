module TestPipeline
    ( testExamples
    , testCli
    , testMir
    , testIntRange
    , testPipeline
    ) where

import Control.Exception (finally)
import Data.List (isInfixOf)
import GHC.IO.Encoding (char8, getLocaleEncoding, setLocaleEncoding)
import System.Directory (getTemporaryDirectory, removeFile)
import System.IO
import qualified Data.Map as Map
import Cli
import qualified Mir as M
import MirEval
import MirLower
import MirVerify
import Pipeline
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
        , testExampleFile "examples/rejected/packet_negative_length.tersus" (ExpectRejected "Funct input validation failed: Could not prove: lo <= hi")
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
        , testCaseSeq
            "testMirCli"
            [ -- `mir` prints the blocks
              testAssertEq (runSource Mir "x = 1 + 2; return x;") (Ok (unlines ["fn main() -> Int {", "    let _0: Int;", "    let _1: Int; // x", "    bb0: {", "        _1 = Add(const 1, const 2);", "        _0 = _1;", "        return;", "    }", "}"]))
            , testAssertErrorContains "Validation failed" (runSource Mir "x = 1; affirm x = 2;")
            , -- A run reports the errors that validation would have prevented
              testAssertEq (runMir "return 1 / 0;") (Error "Division by zero")
            ]
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
        ]
