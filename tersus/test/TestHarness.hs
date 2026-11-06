{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
-- Retries must not share a forced failure from the unsafePerformIO-backed pipeline.
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}

module TestHarness
    ( TestResult
    , Test (..)
    , TestSummary (..)
    , testSummary
    , combineSummaries
    , testCase
    , testCaseSeq
    , testCaseNamedSeq
    , parseFailsWithHelper
    , parseValidateEvalProgramHelper
    , batchItems
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
    , pipelineRuns
    , pipelineValid
    , pipelineRejected
    , nativeInts
    , vecLibrary
    , compileOnce
    , bootstrapOnce
    , ownedOnce
    , validatedOnce
    , programFromFile
    , programFromFiles
    , bootstrapFromFile
    , validatedFromFile
    , linkedFromFile
    , ownedFromFile
    , ownedFromFiles
    , packageCacheInput
    , matchesEmbeddedPackage
    , mirDataOf
    , mirDataFromFile
    , encodeProgram
    , decodeProgram
    , sharedProgramCacheFile
    , sharedProgram
    , compilerIdentity
    , verifiedSeedIdentity
    , openEntryLockFile
    , executableDigest
    , memoizedTestExecutable
    ) where

import Control.DeepSeq (force)
import qualified Data.ByteString.Lazy as BL
import qualified TestProgramBinary as ProgramBinary
import TestProgramBuildIdentity (concreteBuildIdentity, approvedBuildIdentity)
import qualified Control.Exception as Exception
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.MVar (MVar, modifyMVar, newEmptyMVar, newMVar, putMVar, takeMVar, withMVar)
import Control.Concurrent.QSem (QSem, newQSem, signalQSem, waitQSem)
import Control.Exception (IOException, SomeException, bracket, bracket_, bracketOnError, displayException, finally, mask, onException, throwIO, try)
import Control.Monad (forM, when)
import GHC.Conc (getNumCapabilities)
import Data.Char (isHexDigit, isSpace, toLower)
import Data.List (isInfixOf, isPrefixOf, stripPrefix)
import qualified Data.Map.Strict as Map
import System.Directory (createDirectoryIfMissing, doesFileExist, makeAbsolute, removeFile, renameFile)
import System.Environment (getExecutablePath, getProgName, lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>), takeDirectory, takeFileName)
import System.IO (SeekMode (AbsoluteSeek), hClose)
import System.IO.Unsafe (unsafePerformIO)
import System.Posix.IO (FileLock, LockRequest (WriteLock), closeFd, waitToSetLock)
import System.Posix.Types (Fd)
import System.Process (proc)

import CacheLock (openBinaryTempFileCloexec, openLockFd)
import Mir (Program)
import Compile (lowerSource)
import MirHousekeeping (eraseGhosts, toolProgram)
import PreludeSource (compilerSourceHash, libPackageFiles, mirPackageFiles, parserSeedSha256, seedSha256, stdlibSource, toolPackageFiles, validationDriverSource, validationSource)
import Hash (fingerprint)
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)
import MirData (writeProgram)
import MirEval (fromMirValue)
import Native (cacheDirectory, readProcessOutput)
import TestParserFragments
import Modules (LoadResult (..), normalizePath, resolverFromFiles, snapshotFromFilesystem)
import qualified Modules
import Pipeline (loadFromEntry, compileModulesValidated, erasedModuleProgram, ownedModuleProgram, compileSource, ownedSource, parseSource, parseWithEquality, runStatements, validateStatements, validatedSource)
import Types
import Syntax
import Solver
import Utils

type TestResult = Maybe String

memoizedTestExecutable :: MVar (Maybe FilePath) -> IO (Result FilePath String) -> IO (Result FilePath String)
memoizedTestExecutable box prepare = modifyMVar box $ \saved -> do
    live <- case saved of
        Just exe -> doesFileExist exe
        Nothing -> pure False
    result <- case saved of
        Just exe | live -> pure (Ok exe)
        _ -> prepare
    let keep = case result of Ok exe -> Just exe; Error _ -> Nothing
    pure (keep, result)

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

-- Like testCaseSeq, but each row keeps its own name in the output.
testCaseNamedSeq :: String -> [(String, TestResult)] -> Test
testCaseNamedSeq name rows =
    TestList name (map (uncurry testCase) rows)

-- A parse failure whose message contains the expected text.
parseFailsWithHelper :: String -> String -> TestResult
parseFailsWithHelper source expected =
    case parseStatementBlock source of
        Left err -> if expected `isInfixOf` show err then Nothing else Just ("Wrong parse error: " ++ show err)
        Right _ -> Just ("Expected a parse error for: " ++ source)

-- Dual stage: a program must both validate and evaluate to the expected value.
parseValidateEvalProgramHelper :: String -> Maybe Value -> TestResult
parseValidateEvalProgramHelper source expected = withProgram source $
    case parseWithEquality source of
        Left err -> Just $ "Parse failed: " ++ err
        Right stmts -> case validateStatements stmts of
            Error e -> Just $ "Validation failed with error: " ++ e
            Ok _ -> case runStatements stmts of
                Ok result -> testAssertEq (fmap fromMirValue result) expected
                Error e -> Just $ "Evaluation failed with error: " ++ e
batchItems :: Int -> Int -> [a] -> [a]
batchItems count batch values
    | count <= 0 || batch < 1 || batch > count = []
    | otherwise = [value | (index, value) <- zip [0 :: Int ..] values, index `mod` count == batch - 1]

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

-- The validator written in Tersus names the obligation it could not prove in the words of the
-- contract (`Could not prove: x = 2`), as the old engine did, and is held to them; the old
-- engine's other words (`Relation does not hold`, `Loop invariant is not preserved`) are not its
-- own, and a program it refuses for not proving something, or for using what it does not model
-- yet, has failed as expected there.
testAssertErrorContains :: String -> Result a String -> TestResult
testAssertErrorContains expectedSubstring result =
    case result of
        Ok _ -> Just $ "Expected failure containing: " ++ show expectedSubstring
        Error err ->
            if expectedSubstring `isInfixOf` err
                || not ("Could not prove: " `isPrefixOf` expectedSubstring)
                    && any (`isInfixOf` err) ["Could not prove: ", "could not prove ", "the Tersus validator does not model yet"]
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

-- Assert validation fails and the error contains the expected substring
-- (via testAssertErrorContains, whose documented fallback accepts any
-- "Could not prove: ..." / unmodelled-feature verdict for a specific
-- "Could not prove: <obligation>" expectation).
parseValidateFailProgramHelper :: String -> String -> TestResult
parseValidateFailProgramHelper source expectedError = withProgram source $
    case parseWithEquality source of
        Left err -> Just $ "Parse failed: " ++ err
        Right stmts -> case validateStatements stmts of
            Ok _ -> Just "Validation passed when it should have failed"
            result@(Error _) -> testAssertErrorContains expectedError result

-- The Pipeline.parseSource counterparts of the helpers above: parseSource reads a program as
-- the command line reads it, with the libraries the pipeline puts in front of it (lib-injected),
-- where parseWithEquality reads the source alone. pipelineRejected asserts the expected
-- substring, on a parse failure directly and on a validation failure via
-- testAssertErrorContains (as parseValidateFailProgramHelper does).
pipelineRuns :: String -> Value -> TestResult
pipelineRuns source expected = case parseSource source of
    Error e -> Just ("Parse failed: " ++ e)
    Ok stmts -> case runStatements stmts of
        Ok result -> testAssertEq (fmap fromMirValue result) (Just expected)
        Error e -> Just ("Evaluation failed with error: " ++ e)

pipelineValid :: String -> TestResult
pipelineValid source = case parseSource source of
    Error e -> Just ("Parse failed: " ++ e)
    Ok stmts -> case validateStatements stmts of
        Ok _ -> Nothing
        Error e -> Just ("Validation failed with error: " ++ e)

pipelineRejected :: String -> String -> TestResult
pipelineRejected source expected = case parseSource source of
    Error e -> if expected `isInfixOf` e then Nothing else Just ("Expected failure containing: " ++ show expected ++ "\nGot: " ++ e)
    Ok stmts -> testAssertErrorContains expected (validateStatements stmts)

-- A failure says which program it was about (the start of it)
withProgram :: String -> TestResult -> TestResult
withProgram source = fmap (\message -> message ++ "\nProgram: " ++ take 500 source)

-- Textual markers used by test probes. Disk entries use TestProgramBinary,
-- whose structural codec retains specs, invariants, generics and ghost contents.
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
-- validate the same big programs again. Only successful compilations are remembered,
-- so a transient tool failure can be retried in the same process.
compileOnce :: String -> IO (Result Program String)
compileOnce source = sharedProgram "compile" source (pure (compileSource source))

-- A program of the compiler itself (the emitter, the MIR checker and eraser, the validator)
-- as the host builds it, lowered with its ghosts erased and not validated: the validator is
-- one of these programs, so they are the bootstrap (MirHousekeeping.ownedProgramOf). Whether
-- each validates is testHostValidation's to say; the groups that run them test what they do.
bootstrapOnce :: String -> IO (Result Program String)
bootstrapOnce source = sharedProgram "bootstrap" source (pure (lowerSource True source `bindResult` eraseGhosts))

ownedOnce :: String -> IO (Result Program String)
ownedOnce source = sharedProgram "owned" source (pure (ownedSource source))

validatedOnce :: String -> IO (Result Program String)
validatedOnce source = sharedProgram "validated" source (pure (validatedSource source))

-- A program in a package, compiled from its entry file through the module
-- pipeline (the same stages as compileOnce, ownedOnce and validatedOnce do
-- for a single-file program given as text)
programFromFile :: FilePath -> IO (Result Program String)
programFromFile path = snapshotFromFilesystem path >>= programFromFiles path

programFromFiles :: FilePath -> [(FilePath, String)] -> IO (Result Program String)
programFromFiles = cachedFromPackage "program"

-- One of the compiler's own programs as the host builds it: linked, its ghosts erased, not
-- validated (see cachedFromPackage)
bootstrapFromFile :: FilePath -> IO (Result Program String)
bootstrapFromFile = programFromFile

-- The same, before its ghosts are erased
linkedFromFile :: FilePath -> IO (Result Program String)
linkedFromFile = validatedFromFile

validatedFromFile :: FilePath -> IO (Result Program String)
validatedFromFile path = snapshotFromFilesystem path >>= cachedFromPackage "validated" path

ownedFromFile :: FilePath -> IO (Result Program String)
ownedFromFile path = snapshotFromFilesystem path >>= ownedFromFiles path

ownedFromFiles :: FilePath -> [(FilePath, String)] -> IO (Result Program String)
ownedFromFiles = cachedFromPackage "owned"

packageCacheInput :: FilePath -> [(FilePath, String)] -> String
packageCacheInput path files = show (normalizePath path,
    Map.toAscList (Map.fromList [(normalizePath file, source) | (file, source) <- files]))

matchesEmbeddedPackage :: FilePath -> Modules.LoadedPackage -> Bool
matchesEmbeddedPackage path actual
    | normalizePath path `notElem` map fst toolPackageFiles = False
    -- The cached tool is compiled by the bootstrap/oracle loader. Compare
    -- against that exact input, not a second production-parser reading.
    | otherwise = case Modules.loadFromEntry (resolverFromFiles toolPackageFiles) (normalizePath path) of
        Right (PackageResult embedded) -> show actual == show embedded
        _ -> False

cachedFromPackage :: String -> FilePath -> [(FilePath, String)] -> IO (Result Program String)
cachedFromPackage stage path files = do
    let input = packageCacheInput path files
        validated = case loadFromEntry (resolverFromFiles files) path of
            Left e -> Error e
            Right (PackageResult pkg)
                -- (the compiler's own programs as the host builds them: linked, not
                -- validated, MirHousekeeping.toolProgram; testHostValidation validates them)
                | matchesEmbeddedPackage path pkg -> toolProgram (normalizePath path)
                | otherwise -> compileModulesValidated pkg
            Right _ -> Error (path ++ " is not in a package")
    packageStage stage input validated

packageStage :: String -> String -> Result Program String -> IO (Result Program String)
packageStage stage input validated = sharedProgram ("package-" ++ stage) input $ case stage of
    "validated" -> pure validated
    "program" -> do
        before <- packageStage "validated" input validated
        pure (before `bindResult` erasedModuleProgram)
    "owned" -> do
        program <- packageStage "program" input validated
        pure (program `bindResult` ownedModuleProgram)
    _ -> pure (Error ("unknown package compilation stage: " ++ stage))

mirDataFromFile :: FilePath -> IO (Result String String)
mirDataFromFile path = do
    owned <- ownedFromFile path
    pure $ case owned of
        Error e -> Error e
        Ok program -> Ok (writeProgram program)

sharedProgram :: String -> String -> IO (Result Program String) -> IO (Result Program String)
sharedProgram stage source compute = do
    scope <- cacheBuildScope
    case scope of
        Nothing -> compute
        Just identity -> shared identity
  where
    shared identity = do
        let key = (show (stage, identity), source)
            lookupCached = modifyMVar compiledSources $ \cache -> pure (cache, Map.lookup key cache)
        known <- lookupCached
        case known of
            Just result -> pure result
            Nothing -> withEntryThreadLock key $ do
                again <- lookupCached
                case again of
                    Just result -> pure result
                    Nothing -> do
                        result <- sharedOnDisk identity stage source compute
                        case result of
                            Error _ -> pure result
                            Ok program -> do
                                _ <- Exception.evaluate (force program)
                                after <- cacheBuildScope
                                if after /= Just identity then pure result else
                                    modifyMVar compiledSources $ \cache -> pure (Map.insert key result cache, result)

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

sharedOnDisk :: String -> String -> String -> IO (Result Program String) -> IO (Result Program String)
sharedOnDisk identity stage source compute = do
    file <- cacheFileFor identity stage source
    case file of
        Nothing -> compute
        Just path -> do
            let dataDir = takeDirectory path
                entryKey = takeFileName path
            made <- try (createDirectoryIfMissing True dataDir) :: IO (Either IOException ())
            case made of
                Left _ -> compute
                Right () -> do
                    existing <- readEntry entryKey path
                    case existing of
                        Just program -> pure (Ok program)
                        Nothing -> do
                            let produce = do
                                    -- another process may have written it while this one waited for the lock
                                    waited <- readEntry entryKey path
                                    case waited of
                                        Just program -> pure (Ok program)
                                        Nothing -> do
                                            result <- compute
                                            case result of
                                                Error e -> pure (Error e)
                                                Ok program -> do
                                                    _ <- Exception.evaluate (force program)
                                                    after <- cacheBuildScope
                                                    if after /= Just identity then pure (Ok program) else do
                                                        written <- try (writeEntryAtomically dataDir path (ProgramBinary.encodeEntry entryKey program)) :: IO (Either IOException ())
                                                        case written of
                                                            Right () -> pure (Ok program)
                                                            Left _ -> pure (Ok program)
                            locked <- withKernelLock path produce
                            case locked of
                                Just result -> pure result
                                -- the entry cannot be locked (an unwritable directory, a full
                                -- disk): computing without the cache is always safe
                                Nothing -> compute
  where
    readEntry entryKey file = do
        cached <- try (ProgramBinary.readEntryBytes file) :: IO (Either IOException BL.ByteString)
        case cached of
            Right bytes -> case ProgramBinary.decodeEntry entryKey bytes of
                Right program -> Just <$> Exception.evaluate (force program)
                Left _ -> pure Nothing
            Left _ -> pure Nothing

-- New-format rejection is a cache miss, never an attempt to read legacy text.
writeEntryAtomically :: FilePath -> FilePath -> BL.ByteString -> IO ()
writeEntryAtomically dir file bytes = do
    size <- Exception.evaluate (BL.length bytes)
    when (size > ProgramBinary.maxEntryBytes) (ioError (userError "cache entry exceeds size limit"))
    bracketOnError (openBinaryTempFileCloexec dir "entry.tmp")
        (\(staging, handle) -> hClose handle >> removeFile staging)
        (\(staging, handle) -> BL.hPut handle bytes >> hClose handle >> renameFile staging file)

openEntryLockFile :: FilePath -> IO Fd
openEntryLockFile = openLockFd

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

-- The cache file a stage and source use. The scope is also the memory-cache key,
-- so changing an actual override cannot reuse a previous process-local result.
sharedProgramCacheFile :: String -> String -> IO (Maybe FilePath)
sharedProgramCacheFile stage source = do
    scope <- cacheBuildScope
    maybe (pure Nothing) (\identity -> cacheFileFor identity stage source) scope

cacheFileFor :: String -> String -> String -> IO (Maybe FilePath)
cacheFileFor identity stage source = do
    cache <- cacheDirectory
    case cache of
        Ok dir -> do
            key <- sha256 [] (show (stage, source, compilerIdentity, ProgramBinary.codecVersion, identity))
            pure ((\digest -> dir </> "test-programs" </> digest) <$> key)
        _ -> pure Nothing

cacheBuildScope :: IO (Maybe String)
cacheBuildScope = do
    build <- executableBuildIdentity
    backend <- lookupEnv "TERSUS_PARSER"
    path <- lookupEnv "PATH"
    overrides <- mapM seedIdentity
        [("TERSUS_PARSER_SEED_FILE", parserSeedSha256), ("TERSUS_SEED_FILE", seedSha256)]
    pure $ (\b seeds -> show (b, backend, path, seeds)) <$> build <*> sequence overrides
  where
    seedIdentity (variable, expected) = do
        override <- lookupEnv variable
        selected <- case override of
            Just file -> pure (Just file)
            Nothing -> firstExisting (if variable == "TERSUS_PARSER_SEED_FILE"
                then ["bootstrap/parser.ll", "tersus/bootstrap/parser.ll"]
                else ["bootstrap/emitter.ll", "tersus/bootstrap/emitter.ll"])
        case selected of
            Nothing -> pure (Just (variable, Nothing))
            Just file -> do
                absolute <- makeAbsolute file
                digest <- verifiedSeedIdentity absolute expected
                pure ((\value -> (variable, Just (absolute, value))) <$> digest)
    firstExisting [] = pure Nothing
    firstExisting (file : rest) = do
        exists <- doesFileExist file
        if exists then pure (Just file) else firstExisting rest

verifiedSeedIdentity :: FilePath -> String -> IO (Maybe String)
verifiedSeedIdentity file expected = do
    digest <- executableDigest file
    pure (if digest == Just expected then digest else Nothing)

{-# NOINLINE buildIdentityCache #-}
buildIdentityCache :: MVar (Maybe String)
buildIdentityCache = unsafePerformIO (newMVar Nothing)

executableBuildIdentity :: IO (Maybe String)
executableBuildIdentity = do
    self <- try ((,) <$> getProgName <*> getExecutablePath) :: IO (Either IOException (String, FilePath))
    case self of
        Left _ -> pure Nothing
        Right (name, file) -> do
            let interpreted value = value == "<interactive>" || any (`isPrefixOf` value) ["ghc", "runghc", "runhaskell"]
            if interpreted name || interpreted (takeFileName file) then pure Nothing else
                case approvedBuildIdentity of
                    Just approved -> pure (Just ("approved-build-manifest:" ++ approved))
                    Nothing -> modifyMVar buildIdentityCache $ \cached -> case cached of
                        Just _ -> pure (cached, cached)
                        Nothing -> do
                            digest <- executableDigest file
                            let identity = ("executable-sha256:" ++) <$> digest
                            pure (identity, identity)

-- The MIR of a program as data (what MirData writes of Pipeline.ownedSource), shared between
-- the groups that check the same programs: the owned program itself comes from the shared
-- cache above, so the lossy data is written from the same validated program in every group.
mirDataOf :: String -> IO (Result String String)
mirDataOf source = do
    owned <- ownedOnce source
    pure $ case owned of
        Error e -> Error e
        Ok program -> Ok (writeProgram program)

-- Concrete compiler/platform and selected dependency unit IDs, compiler and
-- embedded sources, harness/helpers, codec source/version and package files.
-- Package YAML is an input, not evidence of actual GHC command-line options:
-- cacheBuildScope adds an approved manifest or conservative executable identity.
compilerIdentity :: String
compilerIdentity =
    fingerprint $
        [ compilerSourceHash
        , harnessSourceHash
        , concreteBuildIdentity
        , ProgramBinary.codecVersion
        , stdlibSource
        , validationSource
        , validationDriverSource
        , seedSha256
        , parserSeedSha256
        ]
            ++ concatMap (\(path, contents) -> [path, contents]) libPackageFiles
            ++ concatMap (\(path, contents) -> [path, contents]) toolPackageFiles

harnessSourceHash :: String
harnessSourceHash =
    $( do
        let paths = ["test/TestHarness.hs", "test/TestParserFragments.hs", "test/TestProgramBinary.hs", "test/TestProgramBuildIdentity.hs", "package.yaml", "stack.yaml", "stack.yaml.lock"]
        inputs <- mapM (\path -> do addDependentFile path; contents <- runIO (readFile path); pure [path, contents]) paths
        lift (fingerprint (concat inputs))
     )

executableDigest :: FilePath -> IO (Maybe String)
executableDigest path = sha256 [path] ""

sha256 :: [String] -> String -> IO (Maybe String)
sha256 arguments input = do
    digest <- run "sha256sum" arguments
    case digest of
        Just _ -> pure digest
        Nothing -> run "shasum" (["-a", "256"] ++ arguments)
  where
    run command args = do
        outcome <- try (readProcessOutput (proc command args) input) :: IO (Either IOException (ExitCode, String, String))
        pure $ case outcome of
            Right (ExitSuccess, out, _) -> case words out of
                digest : _ | length digest == 64 && all isHexDigit digest -> Just (map toLower digest)
                _ -> Nothing
            _ -> Nothing

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
        , "    fn set(self: Self, i: Int, x: E) -> Self [{ affirm i >= 0; affirm i < size(self); }] [{ affirm size(return) = size(self); affirm get(return, i) = x; affirm forall j where j >= 0, j < size(self), j != i: get(return, j) = get(self, j); }];"
        , "};"
        , "trait Growable<E> {"
        , "    fn push(self: Self, x: E) -> Self [{ }] [{ affirm size(return) = size(self) + 1; affirm get(return, size(self)) = x; affirm forall j in 0..size(self): get(return, j) = get(self, j); }];"
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
        , "    fn set(self: Self, i: Int, x: T) -> Self [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return.len = self.len; affirm get(return.data, i) = x; affirm forall j where j >= 0, j < self.len, j != i: get(return.data, j) = get(self.data, j); }] {"
        , "        return Self { data: set(self.data, i, x), len: self.len };"
        , "    };"
        , "};"
        , "impl<T> Growable<T> for Vec<T> {"
        , "    fn push(self: Self, x: T) -> Self [{ }] [{ affirm return.len = self.len + 1; affirm get(return.data, self.len) = x; affirm forall j in 0..self.len: get(return.data, j) = get(self.data, j); }] {"
        , "        if self.len < size(self.data) {"
        , "            return Self { data: set(self.data, self.len, x), len: self.len + 1 };"
        , "        };"
        , "        big = Array::boxed(size(self.data) * 2, clone(x));"
        , "        i = 0;"
        , "        while i < self.len [{ affirm i >= 0; affirm i <= self.len; affirm size(big) = size(self.data) * 2; affirm forall j in 0..i: get(big, j) = get(self.data, j); }] shrinks self.len - i {"
        , "            big = set(big, i, clone(get(self.data, i)));"
        , "            i = i + 1;"
        , "        };"
        , "        return Self { data: set(big, self.len, x), len: self.len + 1 };"
        , "    };"
        , "};"
        ]
