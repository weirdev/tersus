module TestTersus (main, allGroups) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar, threadDelay)
import Control.Concurrent.MVar (modifyMVar, modifyMVar_, newMVar)
import Control.Exception (SomeException, displayException, mask, try)
import Control.Monad (forM, forM_, unless, when)
import Data.List (foldl', isPrefixOf)
import GHC.Clock (getMonotonicTime)
import Native (availableProcessors, readProcessOutput)
import System.Environment (getArgs, getEnvironment, getExecutablePath, lookupEnv)
import System.Exit (ExitCode (..), exitFailure)
import System.IO (BufferMode (LineBuffering), hPutStr, hSetBuffering, stderr, stdout)
import System.Process (CreateProcess (..), proc)
import System.Posix.Process (getParentProcessID, getProcessID)

import TestHarness
import TestBasics
import TestValidation
import TestProofs
import TestControl
import TestData
import TestPipeline
import TestNative
import TestOwnership
import TestTraits
import TestArrays
import TestBorrow
import TestCopies
import TestGenerics
import TestBox
import TestDeref
import TestPointers
import TestSequence
import TestStrings
import TestBytes
import TestConnectives
import TestMirData
import TestMirDifferential
import TestMirOwnership
import TestMirEval
import TestMirReader
import TestMirVerify
import TestMirErase
import TestMirCopies
import TestMirEmit
import TestMirSupport
import TestBootstrap
import TestEq
import TestHashMap
import TestHashSet
import TestBuiltinRegistry
import TestSharedCache
import TestScheduling
import TestAstData
import TestDifferential
import TestElaborate
import TestFrontendBootstrap
import TestDataCodec
import TestModules
import TestParity
import TestParser
import TestParserBootstrap
import TestParserUnicode
import TestLibModules

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    args <- getArgs
    case parseArguments args >>= select of
        Left message -> do
            hPutStr stderr (message ++ "\n")
            hPutStr stderr "Usage: tersus-test [-j <n>] [--shard k/n] [group...]\n"
            exitFailure
        Right (arguments, names) -> do
            let selected = [g | g <- allGroups, groupName g `elem` names]
            forM_ (argumentShard arguments) $ \(index, count) -> do
                putStrLn ("[SHARD] " ++ show index ++ "/" ++ show count ++ " " ++ show (length names) ++ "/" ++ show (length allGroups) ++ " groups")
                putStrLn ("[GROUPS] " ++ unwords names)
            jobs <- case argumentJobs arguments of
                Just n -> pure n
                Nothing -> min (length names) <$> availableProcessors
            isolated <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_ISOLATED"
            parent <- getParentProcessID
            processors <- availableProcessors
            let overlap = bootstrapOverlapAllowed (argumentChild arguments) jobs processors names (isolated == Just (show parent))
            (summary, reported) <-
                if useWorkerProcesses arguments jobs (length names)
                    then runInParallel jobs names
                    else runInProcess overlap selected
            unless (argumentChild arguments) $ do
                putStrLn $
                    "Summary: "
                        ++ show (summaryPassed summary)
                        ++ " passed, "
                        ++ show (summaryFailed summary)
                        ++ " failed"
            when (summaryFailed summary > 0 || not reported) exitFailure
  where
    select arguments = (,) arguments <$> selectGroupNames arguments (map groupName allGroups)

allGroups :: [Test]
allGroups = concatMap registered originalGroups
  where
    registered original
        | groupName original == "testParserBootstrap" = parserBootstrapGroups
        | groupName original == "testHostValidation" = hostValidationGroups
        | otherwise = case lookup (groupName original) [(groupName tree, split) | (tree, split) <- batchedGroups] of
            Just split -> split
            Nothing -> [original]

batchedGroups :: [(Test, [Test])]
batchedGroups = [(original, splitTestGroups 4 original) | original <- [testNative, testMirEmit, testMirVerify, testMirSelfHosted, testAstData, testParser, testAstReader]]

originalGroups :: [Test]
originalGroups =
    [ testParse
    , testParseEval
    , testValidateWithExpectedMatch
    , testValidateWithExpectedMismatch
    , testValidationFail
    , testValidationCache
    , testHaskellParity
    , testUserRewriteValidation
    , testParseVal
    , testParseValFail
    , testCrashRegression
    , testExamples
    , testHostValidation
    , testElaborateMutant
    , testFrontendBootstrap
    , testCli
    , testMir
    , testMirSelfHosted
    , testIntRange
    , testPipeline
    , testControlFlow
    , testLists
    , testForallSyntax
    , testForallInstantiation
    , testForallProof
    , testGoalSlices
    , testForallLoops
    , testPrettyProofs
    , testMulDivNegative
    , testCrlf
    , testEnumCast
    , testListProofs
    , testEqualityByParts
    , testEnums
    , testStructs
    , testGenericLists
    , testTypeCheck
    , testRecursion
    , testSolverCache
    , testTermination
    , testRefinedArithmetic
    , testLinearArithmetic
    , testIfJoin
    , testModulo
    , testCallsAndReturnJoin
    , testForLoops
    , testInferredInvariants
    , testCfgValidation
    , testPrecedence
    , testFirstLast
    , testFunctionCalls
    , testCallsUseContracts
    , testNative
    , testOwnership
    , testTraits
    , testArrays
    , testBox
    , testDeref
    , testPointers
    , testBorrow
    , testCopies
    , testGenerics
    , testSequence
    , testStrings
    , testBytes
    , testConnectives
    , testMirData
    , testMirLowered
    , testMirDifferential
    , testMirOwnership
    , testOwnershipMetadata
    , testOwnershipInterpreted
    , testMirEvalLists
    , testMirReader
    , testMirVerify
    , testMirErase
    , testMirCopies
    , testMirVerifyPrograms
    , testMirEmit
    , testMirEmitPrograms
    , testBootstrap
    , testEq
    , testHashMap
    , testHashSet
    , testModules
    , testPhase1Packages
    , testPhase2Packages
    , testBuiltinRegistry
    , testSharedCache
    , testPhase1Cache
    , testVerdictLocks
    , testSharedCacheProbe
    , testScheduling (map groupName allGroups) batchedGroups
    , testAstData
    , testDataCodec
    , testParser
    , testParserBootstrap
    , testParserUnicode
    , testAstReader
    , testDifferential
    , testParity
    , testLibModules
    , testNativeStorageModules
    , testMirSupport
    ]

runInProcess :: Bool -> [Test] -> IO (TestSummary, Bool)
runInProcess overlap selected = do
    summary <- foldr combineSummaries (testSummary 0 0) <$> mapM runGroup selected
    pure (summary, True)
  where
    runGroup group
        | "testParserBootstrap:" `isPrefixOf` groupName group = withParserBootstrapFixture (groupName group) overlap (runTest [] group)
        | otherwise = runTest [] group

-- Each group runs in a process of its own, so that a group's temporary files, locale and environment are its own, and
-- several groups make progress at once. A child is given one group, so it runs in its process and prints no summary;
-- its [PASS]/[FAIL]/[CRASH] lines are the counts here, and its exit status says whether it failed.
-- The groups with the most memory-weighted work start first: a group is a process and the run is over when the last
-- of them ends, so the ones that take minutes are started first and the seconds-long ones fill in around them, instead of
-- the longest only starting once everything before it in the list has had a process. The results are still taken
-- in the order of the list of groups, so the output is unchanged.
runInParallel :: Int -> [String] -> IO (TestSummary, Bool)
runInParallel jobs names = do
    self <- getExecutablePath
    statistics <- lookupEnv "TERSUS_TEST_RTS_STATS"
    inherited <- getEnvironment
    processors <- availableProcessors
    parent <- getProcessID
    let isolated = if bootstrapOverlapAllowed False jobs processors names False then show parent else ""
        environment = ("TERSUS_PARSER_BOOTSTRAP_ISOLATED", isolated) : [(key, value) | (key, value) <- inherited, key /= "TERSUS_PARSER_BOOTSTRAP_ISOLATED"]
        rtsOptions = ["-s" | statistics == Just "1"]
    putStrLn ("Running " ++ show (length names) ++ " test groups in " ++ show jobs ++ " processes")
    slots <- forM names $ \name -> do
        done <- newEmptyMVar
        pure (name, done)
    queue <- newMVar (launchOrder fst slots, 0 :: Int)
    let release name = modifyMVar_ queue (\(remaining, used) -> pure (remaining, used - estimatedPeakMiB name))
        worker = mask $ \restore -> do
            next <- modifyMVar queue $ \(remaining, used) -> case admitGroup memoryBudgetMiB (estimatedPeakMiB . fst) used remaining of
                Nothing -> pure ((remaining, used), if null remaining then Nothing else Just Nothing)
                Just (slot@(name, _), rest) -> pure ((rest, used + estimatedPeakMiB name), Just (Just slot))
            case next of
                Nothing -> pure ()
                Just Nothing -> threadDelay 200000 >> restore worker
                Just (Just (name, done)) -> do
                    result <- try $ restore $ do
                        started <- getMonotonicTime
                        putStrLn ("[START] " ++ name)
                        let arguments = [name, "--child", "+RTS", "-N1"] ++ rtsOptions ++ ["-RTS"]
                        outcome <- try (readProcessOutput (proc self arguments){env = Just environment} "")
                        finished <- getMonotonicTime
                        putStrLn ("[DONE] " ++ name ++ " " ++ elapsedText (finished - started))
                        pure (name, finished - started, outcome)
                    release name
                    putMVar done $ case result of
                        Left e -> (name, 0, Left (e :: SomeException))
                        Right outcome -> outcome
                    restore worker
    forM_ [1 .. min jobs (length names)] $ \_ -> forkIO worker
    -- (the results are taken in the order of the list, so the output has the order it has without the processes)
    outcomes <- forM slots $ \(_, done) -> takeMVar done >>= printOutcome
    pure (foldr combineSummaries (testSummary 0 0) (map fst outcomes), all snd outcomes)

printOutcome :: (String, Double, Either SomeException (ExitCode, String, String)) -> IO (TestSummary, Bool)
printOutcome (name, seconds, outcome) = do
    let (exitCode, out, err) = case outcome of
            Right (status, stdoutText, stderrText) -> (status, stdoutText, stderrText)
            Left e -> (ExitFailure 1, "", displayException e)
    putStr out
    hPutStr stderr err
    putStrLn ("[TIME] " ++ name ++ " " ++ elapsedText seconds)
    let summary = countResults out
        missing = exitCode /= ExitSuccess && summaryFailed summary == 0
    when missing $
        putStrLn ("[CRASH] " ++ name ++ " (the process of the group failed before it reported a result)")
    pure
        ( if missing
            then testSummary (summaryPassed summary) (summaryFailed summary + 1)
            else summary
        , exitCode == ExitSuccess
        )

elapsedText :: Double -> String
elapsedText seconds =
    let tenths = round (seconds * 10) :: Int
     in show (tenths `div` 10) ++ "." ++ show (tenths `mod` 10) ++ "s"

-- The [PASS]/[FAIL]/[CRASH] lines of a group, which is what the summary of the whole run adds up
countResults :: String -> TestSummary
countResults = foldl' count (testSummary 0 0) . lines
  where
    count summary line
        | "[PASS]" `isPrefixOf` line = testSummary (summaryPassed summary + 1) (summaryFailed summary)
        | "[FAIL]" `isPrefixOf` line || "[CRASH]" `isPrefixOf` line = testSummary (summaryPassed summary) (summaryFailed summary + 1)
        | otherwise = summary
