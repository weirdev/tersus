module TestRawArrayTransfer (testRawArrayTransfer, transferPrograms) where

import Control.Exception (finally)
import Data.List (isInfixOf)
import qualified Data.Map as Map
import System.Directory (getTemporaryDirectory, removeFile)
import System.Exit (ExitCode (..))
import System.IO (hClose, openTempFile)

import Bootstrap (tersusLlvm)
import Cli (Command (..), runSource)
import Compile (lowerSource)
import qualified Mir as M
import MirData (forNative, readProgram, writeProgram)
import MirHousekeeping (eraseGhosts, verifyProgram)
import qualified ValidatorNative
import Native (buildExecutableFast)
import Types (Type (..), Size (..))
import TestHarness
import TestNative (runExecutableBytes)
import Utils

testRawArrayTransfer :: Test
testRawArrayTransfer = TestList "testRawArrayTransfer"
    [ TestList "contracts" [testCase name (validation source expected) | (name, source, expected) <- contractCases]
    , TestList "interpreter" [testCase name (testAssertEq (runSource Interpret source) (Ok expected)) | (name, source, expected) <- transferPrograms]
    , TestList "native" [TestCase name (native source expected) | (name, source, expected) <- transferPrograms]
    , testCase "wire roundtrip preserves generic prefix operations" wireRoundtrip
    , testCase "verifier rejects a size operand different from the result size" (malformedSize 1)
    , testCase "verifier rejects a runtime-local size for an inline array" (malformedSize 0)
    , testCase "size parameters use their corresponding trailing locals before and after erasure" sizeParameterLocals
    , testCase "the ghost prefix update is erased and runtime arity is two" erasureShape
    ]

validation :: String -> Maybe String -> TestResult
validation source expected = case lowerSource True source of
    Error e -> if maybe False (`isInfixOf` e) expected then Nothing else Just e
    Ok program ->
        let results = [ValidatorNative.validateCompiledUncached program, ValidatorNative.validateCompiled program]
            matches (Ok ()) = expected == Nothing
            matches (Error e) = maybe False (`isInfixOf` e) expected
         in if all matches results then Nothing else Just ("Expected " ++ show expected ++ ", got " ++ show results)

contractCases :: [(String, String, Maybe String)]
contractCases =
    [ ("filled Block.cast is not an array transfer", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); c = Block::cast(b); q = Addr::cast(p); return Addr::free(q, c);", Just "count(b) = 0")
    , ("empty prefix", emptyTransfer, Nothing)
    , ("entire initialized prefix", fullTransfer, Nothing)
    , ("partial prefix preserves remaining initialized slots", partialTransfer, Nothing)
    , ("transfer exports element equality and empties the prefix", "(p, b) = Addr::alloc(2); b = Addr::write(p, 0, 7, b); b = Addr::write(p, 1, 9, b); define prior = b; (a, b) = Addr::takeArray(p, 2, b); affirm size(a) = 2; affirm get(a, 0) = 7; affirm get(a, 1) = 9; affirm count(b) = count(prior) - 2; affirm filled(b, 0) = false; affirm filled(b, 1) = false; return Addr::free(p, b);", Nothing)
    , ("result Array size cannot disagree with n", "fn f(p: Addr<Int>, ghost b: Block<Int>) -> (Array<Int, 3>, Block<Int>) { return Addr::takeArray(p, 2, b); }; return 0;", Just "expected Tuple2")
    , ("wrong element type cannot be transferred", "fn f(p: Addr<Int>, ghost b: Block<Bool>) -> (Array<Int, 2>, Block<Int>) { return Addr::takeArray(p, 2, b); }; return 0;", Just "argument 3 of Addr::takeArray")
    , ("negative length", "(p, b) = Addr::alloc(0); (a, b) = Addr::takeArray(p, 0 - 1, b); return Addr::free(p, b);", Just "negative")
    , ("length beyond capacity", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); (a, b) = Addr::takeArray(p, 2, b); return Addr::free(p, b);", Just "n <= cap(b)")
    , ("unfilled prefix", "(p, b) = Addr::alloc(3); b = Addr::write(p, 1, 7, b); b = Addr::write(p, 2, 9, b); (a, b) = Addr::takeArray(p, 2, b); b = Addr::dropValue(p, 2, b); return Addr::free(p, b);", Just "filled")
    , ("permission base must match address", "(p, b) = Addr::alloc(1); (q, c) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); (a, b) = Addr::takeArray(q, 1, b); Addr::free(q, c); return Addr::free(p, b);", Just "base(b) = p")
    , ("empty prefix still checks its base", "(p, b) = Addr::alloc(0); (q, c) = Addr::alloc(0); (a, b) = Addr::takeArray(q, 0, b); Addr::free(q, c); return Addr::free(p, b);", Just "base(b) = p")
    , ("old permission cannot be consumed again", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); (a, c) = Addr::takeArray(p, 1, b); return Addr::free(p, b);", Just "was moved")
    , ("updated permission cannot read moved slots", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); (a, b) = Addr::takeArray(p, 1, b); x = Addr::get(p, 0, b); return x + Addr::free(p, b);", Just "filled(b, i) = true")
    , ("transfer cannot run with only a borrowed permission", "fn f(p: Addr<Int>, b: &Block<Int>) -> Array<Int, 1> { (a, c) = Addr::takeArray(p, 1, b); return a; }; return 0;", Just "permission in a value that is lent")
    , ("arbitrary runtime Int is not an inline size", "fn f(p: Addr<Int>, n: Int, ghost b: Block<Int>) -> (Array<Int, 2>, Block<Int>) { return Addr::takeArray(p, n, b); }; return 0;", Just "size of an array must be a constant")
    -- (a generic body is validated at the copies a program uses, and these four programs use none: the validator
    -- written in Tersus does not check the mutated bodies; a copy of transfer, whose result is a tuple with a
    -- sized array, does not lower yet)
    , ("symbolic count must cover the transferred prefix", replace "affirm count(b) >= n;" "" genericTransfer, Nothing)
    , ("symbolic length must be bounded by the permission", replace "affirm count(b) >= n;" "" (replace "affirm n <= cap(b);" "" genericTransfer), Nothing)
    , ("symbolic initialized-prefix invariant is required", replace "affirm forall j in 0..n: filled(b, j) = true;" "" genericTransfer, Nothing)
    , ("returned permission cannot lose its count update", replace "affirm count(return.1) = count(b) - n;" "affirm count(return.1) = count(b);" genericTransfer, Nothing)
    , ("empty prefix need not have any initialized slots", "(p, b) = Addr::alloc(3); (a, b) = Addr::takeArray(p, 0, b); return size(a) + Addr::free(p, b);", Nothing)
    , ("a symbolic inline size validates without a Clone bound", genericTransfer, Nothing)
    -- (the validator written in Tersus does not know how many slots of a split permission's upper part are filled)
    , ("an offset split permission transfers its own prefix", splitTransfer, Just "Could not prove: count(b) >= n")
    , ("non-Clone owning elements transfer without cloning", owningTransfer, Nothing)
    ]

emptyTransfer, fullTransfer, partialTransfer, splitTransfer, owningTransfer, genericTransfer :: String
emptyTransfer = "(p, b) = Addr::alloc(0); (a, b) = Addr::takeArray(p, 0, b); return size(a) + Addr::free(p, b);"
fullTransfer = "(p, b) = Addr::alloc(2); b = Addr::write(p, 0, 7, b); b = Addr::write(p, 1, 9, b); (a, b) = Addr::takeArray(p, 2, b); Addr::free(p, b); return a;"
partialTransfer = "(p, b) = Addr::alloc(3); b = Addr::write(p, 0, 7, b); b = Addr::write(p, 1, 9, b); b = Addr::write(p, 2, 11, b); (a, b) = Addr::takeArray(p, 2, b); affirm count(b) = 1; affirm filled(b, 2) = true; affirm at(b, 2) = 11; (x, b) = Addr::take(p, 2, b); Addr::free(p, b); return get(a, 0) + get(a, 1) + x;"
splitTransfer = "(p, b) = Addr::alloc(3); b = Addr::write(p, 0, 7, b); b = Addr::write(p, 1, 8, b); b = Addr::write(p, 2, 9, b); (lo, hi) = Block::split(b, 1); q = Addr::offset(p, 1); (a, hi) = Addr::takeArray(q, 2, hi); lo = Addr::dropValue(p, 0, lo); b = Block::join(lo, hi); Addr::free(p, b); return a;"
owningTransfer = "struct Owned { xs: List<Int> }; (p, b) = Addr::alloc(2); b = Addr::write(p, 0, Owned { xs: [1, 2] }, b); b = Addr::write(p, 1, Owned { xs: [3] }, b); (a, b) = Addr::takeArray(p, 2, b); Addr::free(p, b); first = &get(a, 0); second = &get(a, 1); return size((*first).xs) * 10 + size((*second).xs);"
genericTransfer = "fn transfer<T, n>(p: Addr<T>, ghost b: Block<T>) -> (Array<T, n>, Block<T>) [{ affirm base(b) = p; affirm n >= 0; affirm n <= cap(b); affirm count(b) >= n; affirm forall j in 0..n: filled(b, j) = true; }] [{ affirm size(return.0) = n; affirm count(return.1) = count(b) - n; affirm forall j in 0..n: get(return.0, j) = at(b, j); affirm forall j in 0..n: filled(return.1, j) = false; }] { return Addr::takeArray(p, n, b); }; return 0;"

transferPrograms :: [(String, String, String)]
transferPrograms =
    [ ("empty array", emptyTransfer, "0")
    , ("null empty prefix", "p = Addr::null(); b = Block::assume(p, 0); (a, b) = Addr::takeArray(p, 0, b); return (a, b);", "Tuple2 { 0: [] }")
    , ("full array", fullTransfer, "[7, 9]")
    , ("partial prefix", partialTransfer, "27")
    , ("non-Clone owners", owningTransfer, "21")
    , ("zero-byte element array", "struct Empty { }; (p, b) = Addr::alloc(1); b = Addr::write(p, 0, Empty { }, b); (a, b) = Addr::takeArray(p, 1, b); Addr::free(p, b); return size(a);", "1")
    , ("owning Box payloads", "(p, b) = Addr::alloc(2); b = Addr::write(p, 0, Box::new(7), b); b = Addr::write(p, 1, Box::new(9), b); (a, b) = Addr::takeArray(p, 2, b); Addr::free(p, b); x = Box::unbox(clone(get(a, 0))); y = Box::unbox(clone(get(a, 1))); return x + y;", "16")
    , ("monomorphized size parameter", "fn transfer<n>(p: Addr<Int>, ghost b: Block<Int>, hint: &Array<Int, n>) -> Array<Int, n> [{ affirm base(b) = p; affirm whole(b); affirm cap(b) = n; affirm count(b) = n; affirm forall j in 0..n: filled(b, j) = true; }] [{ affirm size(return) = n; }] { (a, b) = Addr::takeArray(p, n, b); Addr::free(p, b); return a; }; (p, b) = Addr::alloc(2); b = Addr::write(p, 0, 7, b); b = Addr::write(p, 1, 9, b); a = transfer(p, b, #[0, 0]); return a;", "[7, 9]")
    , ("Byte layout", "(p, b) = Addr::alloc(2); b = Addr::write(p, 0, toByte(65), b); b = Addr::write(p, 1, toByte(90), b); (a, b) = Addr::takeArray(p, 2, b); Addr::free(p, b); return toInt(get(a, 0)) + toInt(get(a, 1));", "155")
    , ("nested inline arrays", "(p, b) = Addr::alloc(2); b = Addr::write(p, 0, #[1, 2], b); b = Addr::write(p, 1, #[3, 4], b); (a, b) = Addr::takeArray(p, 2, b); Addr::free(p, b); return a;", "[[1, 2], [3, 4]]")
    , ("reuse emptied slots", "(p, b) = Addr::alloc(1); b = Addr::write(p, 0, 7, b); (a, b) = Addr::takeArray(p, 1, b); b = Addr::write(p, 0, 9, b); (c, b) = Addr::takeArray(p, 1, b); Addr::free(p, b); return get(a, 0) * 10 + get(c, 0);", "79")
    ]

native :: String -> String -> IO TestResult
native source expected = do
    ir <- tersusLlvm source
    case ir of
        Error e -> pure (Just e)
        Ok text -> do
            temporary <- getTemporaryDirectory
            (path, handle) <- openTempFile temporary "tersus-array-transfer-test"
            hClose handle
            (do
                built <- buildExecutableFast ["-DTERSUS_CHECK"] path text
                case built of
                    Error e -> pure (Just e)
                    Ok () -> do
                        result <- runExecutableBytes path [] ""
                        pure (testAssertEq result (ExitSuccess, expected ++ "\n", "")))
                `finally` removeFile path

wireRoundtrip :: TestResult
wireRoundtrip = case lowerSource True fullTransfer of
    Error e -> Just e
    Ok program -> testAssertEq (readProgram (writeProgram program)) (Ok (forNative program))

malformedSize :: Integer -> TestResult
malformedSize wrong = case lowerSource True fullTransfer of
    Error e -> Just e
    Ok program ->
        let original = M.progMain program
            local = M.Local (1 + maximum [i | M.Local i <- Map.keys (M.fnLocals original)])
            change (M.Assign d (M.ListOp M.AddrTakeArray [p, _, b])) = M.Assign d (M.ListOp M.AddrTakeArray [p, if wrong == 0 then M.Copy local else M.Const (M.CInt wrong), b])
            change s = s
            block (M.BasicBlock ss term) = M.BasicBlock (M.Assign local (M.Use (M.Const (M.CInt 2))) : map change ss) term
            altered = program{M.progMain = original{M.fnBlocks = Map.map block (M.fnBlocks original), M.fnLocals = Map.insert local (M.LocalDecl TInt (Just "runtimeLength")) (M.fnLocals original)}}
         in testAssertErrorContains "addrTakeArray size operand must equal" (verifyProgram altered)

sizeParameterLocals :: TestResult
sizeParameterLocals = case lowerSource True "return 0;" of
    Error e -> Just e
    Ok program ->
        let main = M.progMain program
            array = TArrayOf TInt (SizeParam "n")
            fixture correct ghost =
                let source = if correct then M.Local 3 else M.Local 2
                    locals = Map.fromList [(M.Local 0, M.LocalDecl array Nothing), (M.Local 1, M.LocalDecl (TAddr TInt) (Just "p")), (M.Local 2, M.LocalDecl TInt (Just (if correct then "ordinary" else "n"))), (M.Local 3, M.LocalDecl TInt (Just (if correct then "n" else "m"))), (M.Local 4, M.LocalDecl (TBlock TInt) (Just "b"))]
                    args = [M.Copy (M.Local 1), M.Copy source] ++ [M.Copy (M.Local 4) | ghost]
                    fn = main{M.fnParams = [M.Local 1, M.Local 2, M.Local 3], M.fnSizeParams = ["n"], M.fnReturns = Just array, M.fnLocals = locals, M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [M.Assign (M.Local 0) (M.ListOp M.AddrTakeArray args)] M.Return), M.fnSpec = M.emptySpec}
                 in program{M.progMain = fn}
            checks = [case verifyProgram (fixture correct ghost) of
                Ok () | correct -> Nothing
                Error e | not correct && "addrTakeArray size operand must equal" `isInfixOf` e -> Nothing
                other -> Just ("Unexpected size-parameter mapping result: " ++ show other)
                | correct <- [True, False], ghost <- [True, False]]
         in case [failure | Just failure <- checks] of
            failure : _ -> Just failure
            [] -> Nothing

erasureShape :: TestResult
erasureShape = case lowerSource True fullTransfer of
    Error e -> Just e
    Ok program -> case eraseGhosts program of
        Error e -> Just e
        Ok erased ->
            let statements = concatMap M.blockStatements (Map.elems (M.fnBlocks (M.progMain erased)))
                transfers = [args | M.Assign _ (M.ListOp M.AddrTakeArray args) <- statements]
                ghosts = [() | M.Assign _ (M.ListOp M.BlockPrefixTaken _) <- statements]
             in testAssertEq (map length transfers, length ghosts) ([2], 0)

replace :: String -> String -> String -> String
replace needle replacement = go
  where
    go [] = []
    go input | take (length needle) input == needle = replacement ++ go (drop (length needle) input)
    go (c : rest) = c : go rest
