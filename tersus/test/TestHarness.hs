module TestHarness
    ( TestResult
    , Test (..)
    , TestSummary (..)
    , testSummary
    , combineSummaries
    , testCase
    , testCaseSeq
    , forceTestResult
    , runTest
    , testAssertTrue
    , testAssertEq
    , testAssertErrorContains
    , parseValFailStmtHelper
    , parseEvalProgramHelper
    , parseEvalProgramFailHelper
    , parseValidProgramHelper
    , parseValidateFailProgramHelper
    , nativeInts
    , vecLibrary
    , compileOnce
    , mirDataOf
    ) where

import qualified Control.Exception as Exception
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.MVar (MVar, modifyMVar, newEmptyMVar, newMVar, putMVar, takeMVar)
import Control.Concurrent.QSem (QSem, newQSem, signalQSem, waitQSem)
import Control.Exception (IOException, SomeException, bracket_, displayException, finally, mask, throwIO, try)
import Control.Monad (forM)
import GHC.Conc (getNumCapabilities)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import System.Directory (createDirectory, createDirectoryIfMissing, doesFileExist, getFileSize, getModificationTime, removeDirectory, removeFile, renameFile)
import System.Environment (getExecutablePath)
import System.FilePath ((</>))
import System.IO (hClose, openTempFile)
import System.IO.Unsafe (unsafePerformIO)

import Hash (fingerprint)
import Mir (Program)
import MirData (writeProgram)
import MirEval (fromMirValue)
import Native (cacheDirectory)
import Parse
import Pipeline (compileSource, ownedSource, parseWithEquality, runStatements, validateStatements)
import Types
import Syntax
import Solver
import Utils

type TestResult = Maybe String

data Test = TestCase String (IO TestResult) | TestList String [Test] | TestParallel String [Test]

data TestSummary = TestSummary
    { summaryPassed :: Int
    , summaryFailed :: Int
    }

testSummary :: Int -> Int -> TestSummary
testSummary = TestSummary

combineSummaries :: TestSummary -> TestSummary -> TestSummary
combineSummaries
    (TestSummary passedA failedA)
    (TestSummary passedB failedB) =
        TestSummary (passedA + passedB) (failedA + failedB)

testCase :: String -> TestResult -> Test
testCase name result = TestCase name (pure result)

testCaseSeq :: String -> [TestResult] -> Test
testCaseSeq name results =
    TestList
        name
        (zipWith (\i result -> testCase (show i) result) [0 :: Integer ..] results)

forceTestResult :: TestResult -> ()
forceTestResult Nothing = ()
forceTestResult (Just message) = forceString message
  where
    forceString [] = ()
    forceString (c : cs) = c `seq` forceString cs

-- The cases that run at once, in every parallel group at every depth between them: a parallel group inside another does
-- not multiply the number, so the whole process stays within its capabilities (the child processes of TestTersus are given
-- their share of the processors as theirs).
{-# NOINLINE caseSlots #-}
caseSlots :: QSem
caseSlots = unsafePerformIO (getNumCapabilities >>= newQSem . max 1)

runTest :: [String] -> Test -> IO TestSummary
runTest prefixes (TestCase name resultIO) = bracket_ (waitQSem caseSlots) (signalQSem caseSlots) $ do
    let fullName = unwords (prefixes ++ [name])
    resultOrCrash <- try (resultIO >>= \result -> Exception.evaluate (forceTestResult result) >> pure result) :: IO (Either SomeException TestResult)
    case resultOrCrash of
        Right Nothing -> do
            putStrLn $ "[PASS] " ++ fullName
            pure (testSummary 1 0)
        Right (Just err) -> do
            putStrLn $ "[FAIL] " ++ fullName
            putStrLn err
            pure (testSummary 0 1)
        Left ex -> do
            putStrLn $ "[CRASH] " ++ fullName
            putStrLn (displayException ex)
            pure (testSummary 0 1)
runTest prefixes (TestList name tests) = do
    putStrLn $ "Running " ++ unwords (prefixes ++ [name])
    summaries <- mapM (runTest (prefixes ++ [name])) tests
    putStrLn ""
    pure (foldr combineSummaries (testSummary 0 0) summaries)
runTest prefixes (TestParallel name tests) = do
    putStrLn $ "Running " ++ unwords (prefixes ++ [name])
    vars <- forM tests $ \test -> do
        var <- newEmptyMVar
        _ <- forkIO (mask (\restore -> (try (restore (runTest (prefixes ++ [name]) test)) >>= \r -> putMVar var r)))
        pure var
    summaries <- forM vars (\var -> takeMVar var >>= either (\e -> throwIO (e :: SomeException)) pure)
    putStrLn ""
    pure (foldr combineSummaries (testSummary 0 0) summaries)

testAssertTrue :: Bool -> TestResult
testAssertTrue True = Nothing
testAssertTrue False = Just "Expected True, got False"

testAssertEq :: (Show a, Eq a) => a -> a -> TestResult
testAssertEq actual expected =
    if actual == expected
        then Nothing
        else Just $ "Expected: " ++ show expected ++ "\nGot: " ++ show actual

testAssertErrorContains :: String -> Result a String -> TestResult
testAssertErrorContains expectedSubstring result =
    case result of
        Ok _ -> Just $ "Expected failure containing: " ++ show expectedSubstring
        Error err ->
            if expectedSubstring `isInfixOf` err
                then Nothing
                else
                    Just $
                        "Expected failure containing: "
                            ++ show expectedSubstring
                            ++ "\nGot: "
                            ++ show err

parseValFailStmtHelper :: String -> TestResult
parseValFailStmtHelper stmtStr =
    let parseOutput = parseStatement stmtStr
     in case parseOutput of
            Left err -> Just $ "Parse failed: " ++ show err
            Right (Block stmts) -> case validateStatements stmts of
                Ok _ -> Just "Validation succeeded expected failure"
                Error _ -> Nothing
            Right _ -> Just "Not a block statement"

-- Control flow tests. A program runs on the MIR once it type checks; nothing here validates it.
parseEvalProgramHelper :: String -> Maybe Value -> TestResult
parseEvalProgramHelper source expected = withProgram source $
    case parseWithEquality source of
        Left err -> Just $ "Parse failed: " ++ err
        Right stmts -> case runStatements stmts of
            Ok result -> testAssertEq (fmap fromMirValue result) expected
            Error e -> Just $ "Evaluation failed with error: " ++ e

parseEvalProgramFailHelper :: String -> String -> TestResult
parseEvalProgramFailHelper source expectedError = withProgram source $
    case parseWithEquality source of
        Left err -> Just $ "Parse failed: " ++ err
        Right stmts -> testAssertErrorContains expectedError (runStatements stmts)

parseValidProgramHelper :: String -> TestResult
parseValidProgramHelper source = withProgram source $
    case parseWithEquality source of
        Left err -> Just $ "Parse failed: " ++ err
        Right stmts -> case validateStatements stmts of
            Ok _ -> Nothing
            Error e -> Just $ "Validation failed with error: " ++ e

parseValidateFailProgramHelper :: String -> String -> TestResult
parseValidateFailProgramHelper source expectedError = withProgram source $
    case parseWithEquality source of
        Left err -> Just $ "Parse failed: " ++ err
        Right stmts -> testAssertErrorContains expectedError (validateStatements stmts)

-- A failure says which program it was about (the start of it)
withProgram :: String -> TestResult -> TestResult
withProgram source = fmap (\message -> message ++ "\nProgram: " ++ take 500 source)

-- The compilation of a program, remembered for the process: cases that all use the same big program (the emitter of
-- examples/emit.tersus) validate it once instead of once per case. Compilation is pure, so a result stays valid.
compileOnce :: String -> IO (Result Program String)
compileOnce source = modifyMVar compiledSources $ \cache ->
    case Map.lookup source cache of
        Just result -> pure (cache, result)
        Nothing -> do
            let result = compileSource source
            _ <- Exception.evaluate result
            pure (Map.insert source result cache, result)

{-# NOINLINE compiledSources #-}
compiledSources :: MVar (Map.Map String (Result Program String))
compiledSources = unsafePerformIO (newMVar Map.empty)

-- The MIR of a program as data (what MirData writes of Pipeline.ownedSource), shared between the groups that check
-- the same programs (TestMirData, TestMirReader, TestMirEmit, TestMirVerify): each group runs in a process of its
-- own, so without this every one of them pays the full type check and validation of every example and program again.
-- An entry is the data a validated compile wrote, kept in the cache directory under a name made of the source and of
-- the test binary as built (its size and modification time): a rebuild that changes the compiler or the harness
-- misses the cache and validates afresh, so an entry is only ever used by the binary whose validation produced its
-- kind. A source that does not compile is not remembered, so the case that asked reports why. Without a cache
-- directory the data is simply computed.
mirDataOf :: String -> IO (Result String String)
mirDataOf source = do
    cache <- cacheDirectory
    case cache of
        Error _ -> pure compute
        Ok dir -> do
            built <- binaryIdentity
            let dataDir = dir </> "mir-data"
                file = dataDir </> fingerprint [source, built]
            present <- doesFileExist file
            if present
                then do
                    cached <- try (readFile file >>= \text -> Exception.evaluate (length text) >> pure text) :: IO (Either IOException String)
                    pure $ case cached of
                        Right text -> Ok text
                        Left _ -> compute
                else do
                    made <- try (createDirectoryIfMissing True dataDir) :: IO (Either IOException ())
                    case made of
                        Left _ -> pure compute
                        Right () -> do
                            -- (one process compiles an entry while the others wait for it: on a cold cache the group
                            -- processes would otherwise each validate the same program at the same time. The lock is a
                            -- directory made for the entry, which only one process can make)
                            let lock = file ++ ".lock"
                                produce = do
                                    let result = compute
                                    case result of
                                        Error _ -> pure result
                                        Ok text -> do
                                            (staging, handle) <- openTempFile dataDir "mir-data.tmp"
                                            hClose handle
                                            removeFile staging
                                            writeFile staging text
                                            renameFile staging file
                                            pure result
                            acquired <- try (createDirectory lock) :: IO (Either IOException ())
                            case acquired of
                                Right () -> produce `finally` removeDirectory lock
                                Left _ -> do
                                    waited <- waitForEntry file (120 :: Int)
                                    case waited of
                                        Just text -> pure (Ok text)
                                        -- (the holder may be gone, or slower than the wait: computing again is
                                        -- always safe, the entry written is the same)
                                        Nothing -> produce
  where
    waitForEntry file tries
        | tries <= 0 = pure Nothing
        | otherwise = do
            present <- doesFileExist file
            if present
                then do
                    cached <- try (readFile file >>= \text -> Exception.evaluate (length text) >> pure text) :: IO (Either IOException String)
                    pure $ case cached of
                        Right text -> Just text
                        Left _ -> Nothing
                else threadDelay 500000 >> waitForEntry file (tries - 1)
    compute = case ownedSource source of
        Error e -> Error e
        Ok program -> Ok (writeProgram program)

-- What identifies the test binary that is running: a compiler or harness change rebuilds it, which changes at
-- least one of these, so cached MIR data made by another build is not used.
{-# NOINLINE binaryIdentity #-}
binaryIdentity :: IO String
binaryIdentity = unsafePerformIO $ do
    cache <- newMVar Nothing
    pure $ modifyMVar cache $ \known -> case known of
        Just identity -> pure (known, identity)
        Nothing -> do
            identity <- try identify :: IO (Either IOException String)
            let text = case identity of
                    Right value -> value
                    Left _ -> ""
            pure (Just text, text)
  where
    identify :: IO String
    identify = do
        exe <- getExecutablePath
        size <- getFileSize exe
        modified <- getModificationTime exe
        pure (show size ++ " " ++ show modified)

-- Run tests
-- A function over integers only
nativeInts :: Int -> [Statement] -> FunctBody
nativeInts n = NativeFunct (Signature (replicate n TInt) TInt [] [] [] []) Nothing


-- The growable list of `examples/vec.tersus` (without the comments), which the tests build programs on
vecLibrary :: String
vecLibrary =
    unlines
        [ "trait Sequence<E> {"
        , "    fn size(self: &Self) -> Int [{ }] [{ affirm return >= 0; }];"
        , "    fn get(self: &Self, i: Int) -> E [{ affirm i >= 0; affirm i < size(self); }] [{ }];"
        , "    fn set(self: Self, i: Int, x: E) -> Self [{ affirm i >= 0; affirm i < size(self); }] [{ affirm size(return) = size(self); affirm get(return, i) = x; }];"
        , "};"
        , "trait Growable<E> {"
        , "    fn push(self: Self, x: E) -> Self [{ }] [{ affirm size(return) = size(self) + 1; affirm get(return, size(self)) = x; }];"
        , "};"
        , "struct Vec<T> {"
        , "    data: Box<Array<T>>,"
        , "    len: Int,"
        , "} invariant [{ affirm len >= 0; affirm len <= size(data); affirm size(data) >= 1; }];"
        , "impl<T> Clone for Vec<T> { };"
        , "impl<T> Vec<T> {"
        , "    fn new(filler: T) -> Self [{ }] [{ affirm return.len = 0; }] {"
        , "        return Self { data: Array::boxed(4, filler), len: 0 };"
        , "    };"
        , "    fn pop(self: Self) -> Self [{ affirm self.len >= 1; }] [{ affirm return.len = self.len - 1; }] {"
        , "        return Self { data: self.data, len: self.len - 1 };"
        , "    };"
        , "};"
        , "impl<T> Sequence<T> for Vec<T> {"
        , "    fn size(self: &Self) -> Int [{ }] [{ affirm return = self.len; }] {"
        , "        return self.len;"
        , "    };"
        , "    fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return = get(self.data, i); }] {"
        , "        return clone(get(self.data, i));"
        , "    };"
        , "    fn set(self: Self, i: Int, x: T) -> Self [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return.len = self.len; affirm get(return.data, i) = x; }] {"
        , "        return Self { data: set(self.data, i, x), len: self.len };"
        , "    };"
        , "};"
        , "impl<T> Growable<T> for Vec<T> {"
        , "    fn push(self: Self, x: T) -> Self [{ }] [{ affirm return.len = self.len + 1; affirm get(return.data, self.len) = x; }] {"
        , "        if self.len < size(self.data) {"
        , "            return Self { data: set(self.data, self.len, x), len: self.len + 1 };"
        , "        };"
        , "        big = Array::boxed(size(self.data) * 2, clone(x));"
        , "        i = 0;"
        , "        while i < self.len [{ affirm i >= 0; affirm i <= self.len; affirm size(big) = size(self.data) * 2; }] shrinks self.len - i {"
        , "            big = set(big, i, clone(get(self.data, i)));"
        , "            i = i + 1;"
        , "        };"
        , "        return Self { data: set(big, self.len, x), len: self.len + 1 };"
        , "    };"
        , "};"
        ]
