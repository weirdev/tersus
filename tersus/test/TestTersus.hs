module TestTersus (main, allGroups) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar, threadDelay)
import Control.Concurrent.MVar (modifyMVar, modifyMVar_, newMVar)
import Control.Exception (SomeException, displayException, mask, try)
import Control.Monad (forM, forM_, unless, when)
import Data.List (foldl', isPrefixOf, sortBy)
import Data.Ord (comparing)
import GHC.Clock (getMonotonicTime)
import GHC.Conc (getNumProcessors)
import System.Environment (getArgs, getExecutablePath, lookupEnv)
import System.Exit (ExitCode (..), exitFailure)
import System.IO (BufferMode (LineBuffering), hPutStr, hSetBuffering, stderr, stdout)
import System.Process (proc, readCreateProcessWithExitCode)

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
import TestMirEval
import TestMirReader
import TestMirVerify
import TestMirErase
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
                Nothing -> min (length names) <$> getNumProcessors
            (summary, reported) <-
                if useWorkerProcesses arguments jobs (length names)
                    then runInParallel jobs names
                    else runInProcess selected
            unless (argumentChild arguments) $ do
                putStrLn $
                    "Summary: "
                        ++ show (summaryPassed summary)
                        ++ " passed, "
                        ++ show (summaryFailed summary)
                        ++ " failed"
            when (summaryFailed summary > 0 || not reported) exitFailure
  where
    select arguments = (,) arguments . withoutOptIn arguments <$> selectGroupNames arguments (map groupName allGroups)
    withoutOptIn arguments names
        | null (argumentGroups arguments) = filter (`notElem` optInGroups) names
        | otherwise = names

-- Groups that run only when they are named: too slow for every run of the suite
optInGroups :: [String]
optInGroups = ["testHostValidation"]

allGroups :: [Test]
allGroups = concatMap registered originalGroups
  where
    registered original = case lookup (groupName original) [(groupName tree, split) | (tree, split) <- batchedGroups] of
        Just split -> split
        Nothing -> [original]

batchedGroups :: [(Test, [Test])]
batchedGroups = [(original, splitTestGroups 4 original) | original <- [testNative, testMirEmit, testMirVerify, testMirSelfHosted]]

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
    , testMirEvalLists
    , testMirReader
    , testMirVerify
    , testMirErase
    , testMirVerifyPrograms
    , testMirEmit
    , testMirEmitPrograms
    , testBootstrap
    , testEq
    , testHashMap
    , testHashSet
    , testModules
    , testBuiltinRegistry
    , testSharedCache
    , testVerdictLocks
    , testSharedCacheProbe
    , testScheduling (map groupName allGroups) batchedGroups
    , testAstData
    , testParser
    , testParserBootstrap
    , testParserUnicode
    , testAstReader
    , testParity
    , testLibModules
    , testNativeStorageModules
    , testMirSupport
    ]

runInProcess :: [Test] -> IO (TestSummary, Bool)
runInProcess selected = do
    summary <- foldr combineSummaries (testSummary 0 0) <$> mapM runGroup selected
    pure (summary, True)
  where
    runGroup group
        | groupName group == "testParserBootstrap" = withParserBootstrapFixture (runTest [] group)
        | otherwise = runTest [] group

-- Each group runs in a process of its own, so that a group's temporary files, locale and environment are its own, and
-- several groups make progress at once. A child is given one group, so it runs in its process and prints no summary;
-- its [PASS]/[FAIL]/[CRASH] lines are the counts here, and its exit status says whether it failed.
-- The groups that take the longest, longest first: a group is a process and the run is over when the last of them
-- ends, so the ones that take minutes are started first and the seconds-long ones fill in around them, instead of
-- the longest only starting once everything before it in the list has had a process. The results are still taken
-- in the order of the list of groups, so the output is unchanged.
runInParallel :: Int -> [String] -> IO (TestSummary, Bool)
runInParallel jobs names = do
    self <- getExecutablePath
    statistics <- lookupEnv "TERSUS_TEST_RTS_STATS"
    let rtsOptions = ["-s" | statistics == Just "1"]
    putStrLn ("Running " ++ show (length names) ++ " test groups in " ++ show jobs ++ " processes")
    slots <- forM names $ \name -> do
        done <- newEmptyMVar
        pure (name, done)
    -- (a self-hosted group holds the compiled validator as Haskell data, about 2 GB, and peaks at 5 to 7 GB: at most
    -- two run at once, so that a runner of 16 GB is not exhausted; the next group that may run is taken instead)
    queue <- newMVar (sortBy (comparing (negate . groupWeight . fst)) slots, 0 :: Int)
    let allowed heavy (name, _) = not (isSelfHosted name) || heavy < 2
        release name = when (isSelfHosted name) $ modifyMVar_ queue (\(remaining, heavy) -> pure (remaining, heavy - 1))
        worker = mask $ \restore -> do
            next <- modifyMVar queue $ \(remaining, heavy) -> case break (allowed heavy) remaining of
                (_, []) -> pure ((remaining, heavy), if null remaining then Nothing else Just Nothing)
                (before, slot@(name, _) : after) -> pure ((before ++ after, heavy + fromEnum (isSelfHosted name)), Just (Just slot))
            case next of
                Nothing -> pure ()
                Just Nothing -> threadDelay 200000 >> restore worker
                Just (Just (name, done)) -> do
                    result <- try $ restore $ do
                        started <- getMonotonicTime
                        putStrLn ("[START] " ++ name)
                        let arguments = [name, "--child", "+RTS", "-N1"] ++ rtsOptions ++ ["-RTS"]
                        outcome <- try (readCreateProcessWithExitCode (proc self arguments) "")
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
