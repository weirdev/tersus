{-# LANGUAGE PatternSynonyms #-}

module TestMirEval (testMirEvalLists) where

import Control.Exception (evaluate)
import GHC.Conc (getAllocationCounter)
import qualified Data.Map.Strict as Map

import Compile (lowerSource)
import qualified Mir as M
import qualified MirEval as Eval
import Syntax (Value (..))
import Types (Type (..), pattern TList, pattern TBox)
import TestHarness
import Utils

testMirEvalLists :: Test
testMirEvalLists = TestList "testMirEvalLists" $
    [ testCase "host list construction, matching, equality and Show" hostLists
    , runs "append, endpoints and pop" "xs = push([1, 2], 3); a = first(xs); b = last(xs); xs = pop(xs); return a * 100 + b * 10 + size(xs);" (Eval.MInt 132)
    , runs "an indexed update does not change its snapshot" "xs = [1, 2, 3]; ys = set(clone(xs), 1, 9); return get(xs, 1) * 10 + get(ys, 1);" (Eval.MInt 29)
    , runs "nested indexed update through a reference" "xs = [[1, 2], [3, 4]]; r = &mut get(get(xs, 1), 0); *r = 9; return get(get(xs, 1), 0);" (Eval.MInt 9)
    , runs "references stored in a list survive a call" "fn read(rs: &List<&Int>) -> Int { r = get(rs, 0); return *r; }; xs = [7]; rs = push([], &get(xs, 0)); return read(rs);" (Eval.MInt 7)
    , testCase "distinct references returned through nested calls keep their order" returnedReferences
    , runs "concrete generic fields keep reference roots across a call" "struct Wrap<T> { value: T }; fn read(w: &Wrap<&Int>) -> Int { r = w.value; return *r; }; x = 21; w = Wrap<&Int> { value: &x }; return read(w);" (Eval.MInt 21)
    , runs "a recursive enum still finds references after its recursive edge" "enum Node { Next { child: Box<Node> }, Ref { value: &Int } }; fn read(node: Node) -> Int { if node is Node::Ref { r = (node as Node::Ref).value; return *r; }; return 0; }; x = 31; node = Node::Ref { value: &x }; return read(node);" (Eval.MInt 31)
    , runs "repeated array elements have independent updates" "xs = array(3, [1, 2]); ys = set(xs, 1, [9]); return size(get(ys, 0)) * 100 + first(get(ys, 1)) * 10 + size(get(ys, 2));" (Eval.MInt 292)
    ]
    ++ [ fails name source expected
       | (name, source, expected) <-
           [ ("negative index", "return get([1], -1);", "Get index out of range")
           , ("past-end index", "return get([1], 1);", "Get index out of range")
           , ("negative update index", "return set([1], -1, 2);", "Set index out of range")
           , ("past-end update index", "return set([1], 1, 2);", "Set index out of range")
           , ("first of an empty list", "xs = []; return first(xs);", "First requires a non-empty list")
           , ("last of an empty list", "xs = []; return last(xs);", "Last requires a non-empty list")
           , ("pop of an empty list", "xs = []; return pop(xs);", "Pop requires a non-empty list")
           ]
       ]
    ++ [ TestCase "growing and indexing a large list has bounded allocation" boundedGrowth ]

hostLists :: TestResult
hostLists =
    let value = Eval.MList [Eval.MInt 1, Eval.MData "Cell" [("n", Eval.MInt 2)]]
        expected = VList [VInt 1, VData "Cell" [("n", VInt 2)]]
     in case value of
        Eval.MList values -> firstFailure
            [ testAssertEq values [Eval.MInt 1, Eval.MData "Cell" [("n", Eval.MInt 2)]]
            , testAssertEq (Eval.toMirValue expected) (Just value)
            , testAssertEq (Eval.fromMirValue value) expected
            , testAssertEq (show value) "MList [MInt 1,MData \"Cell\" [(\"n\",MInt 2)]]"
            ]
        _ -> Just "host list did not match MList"

-- The frontend cannot return an assembled reference list yet; reshape a type-checked reference pair to exercise MIR sequence returns.
returnedReferences :: TestResult
returnedReferences = case lowerSource True source of
    Error e -> Just e
    Ok program -> testAssertEq (Eval.runProgram (program{M.progMain = reshape (M.progMain program), M.progFunctions = Map.map reshape (M.progFunctions program)})) (Ok (Just (Eval.MInt 79)))
  where
    source = "struct PairRefs { a: &Int, b: &Int }; fn ends(xs: &List<Int>) -> PairRefs from xs { return PairRefs { a: &get(xs, 0), b: &get(xs, 2) }; }; fn again(prefix: Int, xs: &List<Int>) -> PairRefs from xs { return ends(xs); }; padding = 123; xs = [7, 8, 9]; p = again(padding, xs); a = p.a; b = p.b; return *a * 10 + *b;"
    shape (TNamed "PairRefs" []) = TList (TRef TInt)
    shape ty = ty
    reshape fn = fn
        { M.fnReturns = fmap shape (M.fnReturns fn)
        , M.fnLocals = Map.map (\decl -> decl{M.localType = shape (M.localType decl)}) (M.fnLocals fn)
        , M.fnBlocks = Map.map (\block -> block{M.blockStatements = map statement (M.blockStatements block)}) (M.fnBlocks fn)
        }
    statement (M.Assign dest rv) = M.Assign dest (rvalue rv)
    statement other = other
    rvalue (M.MakeData "PairRefs" fields) = M.MakeList (map snd fields)
    rvalue (M.ReadField value "PairRefs" "a") = M.ListOp M.Get [value, M.Const (M.CInt 0)]
    rvalue (M.ReadField value "PairRefs" "b") = M.ListOp M.Get [value, M.Const (M.CInt 1)]
    rvalue other = other

runs :: String -> String -> Eval.MirValue -> Test
runs name source expected = testCase name (testAssertEq (lowerSource True source `bindResult` Eval.runProgram) (Ok (Just expected)))

fails :: String -> String -> String -> Test
fails name source expected = testCase name (testAssertErrorContains expected (lowerSource True source `bindResult` Eval.runProgram))

boundedGrowth :: IO TestResult
boundedGrowth = case lowerSource True "fn listItem(xs: &List<Int>, i: Int) -> Int { return get(xs, i); }; xs = []; for i in 0..16000 { xs = push(xs, i); }; for i in 0..4000 { xs = set(xs, i * 3, 0); }; total = 0; for i in 0..16000 { total = total + get(xs, i); }; for i in 0..512 { total = total + listItem(xs, i * 23); }; return total + size(xs) + first(xs) + last(xs);" of
    Error e -> pure (Just e)
    Ok program -> do
        _ <- evaluate (length (show program))
        before <- getAllocationCounter
        let correct = testAssertEq (Eval.runProgram program) (Ok (Just (Eval.MInt 106035852)))
        _ <- evaluate (forceTestResult correct)
        after <- getAllocationCounter
        pure $ firstFailure
            [ correct
            , if before - after < 256 * 1024 * 1024 then Nothing else Just ("list growth allocated " ++ show (before - after) ++ " bytes; expected less than 256 MiB")
            ]

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [message | Just message <- results] of
    message : _ -> Just message
    [] -> Nothing
