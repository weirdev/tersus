{-# LANGUAGE CPP #-}

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
    , ownedOnce
    , validatedOnce
    , mirDataOf
    , encodeProgram
    , decodeProgram
    , sharedProgramCacheFile
    , openEntryLockFile
    ) where

import qualified Control.Exception as Exception
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.MVar (MVar, modifyMVar, newEmptyMVar, newMVar, putMVar, takeMVar, withMVar)
import Control.Concurrent.QSem (QSem, newQSem, signalQSem, waitQSem)
import Control.Exception (IOException, SomeException, bracket, bracket_, displayException, finally, mask, onException, throwIO, try)
import Control.Monad (forM, when)
import GHC.Conc (getNumCapabilities)
import Data.Char (isSpace)
import Data.List (isInfixOf, stripPrefix)
import qualified Data.Map.Strict as Map
import System.Directory (createDirectory, createDirectoryIfMissing, doesDirectoryExist, doesFileExist, getFileSize, getModificationTime, removeDirectory, removeDirectoryRecursive, removeFile, renameFile)
import System.Environment (getExecutablePath)
import System.FilePath ((</>))
import System.IO (SeekMode (AbsoluteSeek), hClose, hPutStr, openTempFile)
import System.IO.Unsafe (unsafePerformIO)
import System.Posix.IO (FileLock, LockRequest (WriteLock), OpenMode (WriteOnly), closeFd, defaultFileFlags, openFd, waitToSetLock)
import System.Posix.Types (Fd)

import Hash (fingerprint)
import Mir (Program)
import MirData (writeProgram)
import MirEval (fromMirValue)
import Native (cacheDirectory)
import Parse
import Pipeline (compileSource, ownedSource, parseWithEquality, runStatements, validateStatements, validatedSource)
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

-- Lossless codec for a compiled program. MirData.writeProgram is lossy by design, so the shared
-- cache uses derived Show/Read, which keep specs, invariants, generics and ghost contents.
programCodecHeader :: String
programCodecHeader = "tersus-test-program 1\n"

encodeProgram :: Program -> String
encodeProgram program = programCodecHeader ++ show program ++ "\n"

decodeProgram :: String -> Result Program String
decodeProgram text = case stripPrefix programCodecHeader text of
    Nothing -> Error "not a tersus-test-program 1 entry"
    Just body -> case reads body of
        [(program, rest)] | all isSpace rest -> Ok program
        _ -> Error "malformed tersus-test-program entry"

-- The compilation of a program, remembered for the process and, when it succeeded, on disk:
-- test groups run in processes of their own, so without the disk entry every group would
-- validate the same big programs again. Only successful compilations are written; an error
-- is remembered in this process (as compileOnce always did) and recomputed by others.
compileOnce :: String -> IO (Result Program String)
compileOnce source = sharedProgram "compile" source (compileSource source)

ownedOnce :: String -> IO (Result Program String)
ownedOnce source = sharedProgram "owned" source (ownedSource source)

validatedOnce :: String -> IO (Result Program String)
validatedOnce source = sharedProgram "validated" source (validatedSource source)

sharedProgram :: String -> String -> Result Program String -> IO (Result Program String)
sharedProgram stage source compute = do
    known <- lookupCached
    case known of
        Just result -> pure result
        Nothing -> withEntryThreadLock (stage, source) $ do
            again <- lookupCached
            case again of
                Just result -> pure result
                Nothing -> do
                    result <- sharedOnDisk stage source compute
                    modifyMVar compiledSources $ \cache -> pure (Map.insert (stage, source) result cache, result)
  where
    lookupCached = modifyMVar compiledSources $ \cache -> pure (cache, Map.lookup (stage, source) cache)

{-# NOINLINE compiledSources #-}
compiledSources :: MVar (Map.Map (String, String) (Result Program String))
compiledSources = unsafePerformIO (newMVar Map.empty)

-- Kernel locks are per process, so threads of one process take a per-entry MVar first; the
-- map holds one lock per stage and source ever shared here, as compiledSources itself does.
{-# NOINLINE entryLocks #-}
entryLocks :: MVar (Map.Map (String, String) (MVar ()))
entryLocks = unsafePerformIO (newMVar Map.empty)

withEntryThreadLock :: (String, String) -> IO (Result Program String) -> IO (Result Program String)
withEntryThreadLock key action = do
    lock <- modifyMVar entryLocks $ \locks -> case Map.lookup key locks of
        Just existing -> pure (locks, existing)
        Nothing -> do
            fresh <- newMVar ()
            pure (Map.insert key fresh locks, fresh)
    withMVar lock (\_ -> action)

sharedOnDisk :: String -> String -> Result Program String -> IO (Result Program String)
sharedOnDisk stage source compute = do
    cache <- cacheDirectory
    case cache of
        Error _ -> pure compute
        Ok dir -> do
            built <- binaryIdentity
            let entryKey = fingerprint [stage, source, built, programCodecHeader]
                dataDir = dir </> "test-programs"
                file = dataDir </> entryKey
            made <- try (createDirectoryIfMissing True dataDir) :: IO (Either IOException ())
            case made of
                Left _ -> pure compute
                Right () -> do
                    existing <- readEntry file
                    case existing of
                        Just program -> pure (Ok program)
                        Nothing -> do
                            let produce = do
                                    -- another process may have written it while this one waited for the lock
                                    waited <- readEntry file
                                    case waited of
                                        Just program -> pure (Ok program)
                                        Nothing -> case compute of
                                            Error e -> pure (Error e)
                                            Ok program -> do
                                                written <- try (writeEntryAtomically dataDir file (encodeEntry entryKey program)) :: IO (Either IOException ())
                                                case written of
                                                    Right () -> pure (Ok program)
                                                    Left _ -> pure (Ok program)
                            locked <- withKernelLock file produce
                            case locked of
                                Just result -> pure result
                                -- the entry cannot be locked (an unwritable directory, a full
                                -- disk): computing without the cache is always safe
                                Nothing -> pure compute
  where
    readEntry file = do
        present <- doesFileExist file
        if not present
            then pure Nothing
            else do
                built <- binaryIdentity
                let entryKey = fingerprint [stage, source, built, programCodecHeader]
                cached <- try (readFile file >>= \text -> Exception.evaluate (length text) >> pure text) :: IO (Either IOException String)
                pure $ case cached of
                    Right text -> case decodeEntry entryKey text of
                        Ok program -> Just program
                        Error _ -> Nothing
                    Left _ -> Nothing

-- An entry carries the key it was filed under, so a well-formed program filed for another
-- source, stage or build is a miss, not an answer.
decodeEntry :: String -> String -> Result Program String
decodeEntry key text = case stripPrefix (programCodecHeader ++ key ++ "\n") text of
    Nothing -> Error "entry key mismatch"
    Just body -> case reads body of
        [(program, rest)] | all isSpace rest -> Ok program
        _ -> Error "malformed tersus-test-program entry"

encodeEntry :: String -> Program -> String
encodeEntry key program = programCodecHeader ++ key ++ "\n" ++ show program ++ "\n"

writeEntryAtomically :: FilePath -> FilePath -> String -> IO ()
writeEntryAtomically dir file text = do
    (staging, handle) <- openTempFile dir "entry.tmp"
    hPutStr handle text
    hClose handle
    renameFile staging file

-- The one place the unix openFd version difference lives: unix before 2.8 takes the creation
-- mode as its own argument, and from 2.8 on it is the creat field of the flags. Without the
-- Cabal version macros (a direct ghc build of the tests on the older toolchain) the older
-- call is used.
openEntryLockFile :: FilePath -> IO Fd
#ifdef MIN_VERSION_unix
# if MIN_VERSION_unix(2,8,0)
openEntryLockFile path = openFd path WriteOnly defaultFileFlags{creat = Just 0o644}
# else
openEntryLockFile path = openFd path WriteOnly (Just 0o644) defaultFileFlags
# endif
#else
openEntryLockFile path = openFd path WriteOnly (Just 0o644) defaultFileFlags
#endif

-- One process compiles an entry while the others wait in the kernel for its lock: a file
-- lock on the entry's lock file, held from before the entry is re-read until after it is
-- written, and released by closing the descriptor -- by the bracket below, or by the kernel
-- when the process dies, however it dies. Nothing about who holds it is kept on disk, so
-- there is no stale state to reclaim and no wait after which a waiter duplicates work.
-- Returns Nothing when the lock file cannot be opened or locked at all.
withKernelLock :: FilePath -> IO (Result Program String) -> IO (Maybe (Result Program String))
withKernelLock file produce = do
    outcome <- try acquireUse :: IO (Either IOException (Result Program String))
    pure $ case outcome of
        Right result -> Just result
        Left _ -> Nothing
  where
    acquireUse = bracket acquire closeFd (\_ -> produce)
    acquire = do
        fd <- openEntryLockFile (file ++ ".lock")
        waitToSetLock fd lockRequest `onException` closeFd fd
        pure fd
    lockRequest :: FileLock
    lockRequest = (WriteLock, AbsoluteSeek, 0, 0)

-- The cache file a stage and source use, when there is a cache directory (for cache tests).
sharedProgramCacheFile :: String -> String -> IO (Maybe FilePath)
sharedProgramCacheFile stage source = do
    cache <- cacheDirectory
    case cache of
        Error _ -> pure Nothing
        Ok dir -> do
            built <- binaryIdentity
            pure (Just (dir </> "test-programs" </> fingerprint [stage, source, built, programCodecHeader]))

-- The MIR of a program as data (what MirData writes of Pipeline.ownedSource), shared between
-- the groups that check the same programs: the owned program itself comes from the shared
-- cache above, so the lossy data is written from the same validated program in every group.
mirDataOf :: String -> IO (Result String String)
mirDataOf source = do
    owned <- ownedOnce source
    pure $ case owned of
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
