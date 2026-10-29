module TestTersus (main) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.QSem (newQSem, signalQSem, waitQSem)
import Control.Exception (SomeException, bracket_, displayException, try)
import Control.Monad (forM, unless, when)
import Data.List (foldl', isPrefixOf)
import GHC.Clock (getMonotonicTime)
import GHC.Conc (getNumProcessors)
import System.Environment (getArgs, getExecutablePath)
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
import TestSequence
import TestStrings
import TestBytes
import TestConnectives
import TestMirData
import TestMirReader
import TestMirEmit
import TestBootstrap

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    args <- getArgs
    case parseArguments args of
        Left message -> do
            hPutStr stderr (message ++ "\n")
            hPutStr stderr "Usage: tersus-test [-j <n>] [group...]\n"
            exitFailure
        Right arguments -> do
            -- (the names of groups on the command line run only those: `tests testBorrow testCopies`)
            let chosen = argumentGroups arguments
                selected = if null chosen then allGroups else [g | g <- allGroups, groupName g `elem` chosen]
                names = map groupName selected
            jobs <- case argumentJobs arguments of
                Just n -> pure n
                Nothing -> min (length names) <$> getNumProcessors
            (summary, reported) <-
                if jobs <= 1 || length names <= 1
                    then runInProcess selected
                    else runInParallel jobs names
            unless (argumentChild arguments) $ do
                putStrLn $
                    "Summary: "
                        ++ show (summaryPassed summary)
                        ++ " passed, "
                        ++ show (summaryFailed summary)
                        ++ " failed"
            when (summaryFailed summary > 0 || not reported) exitFailure

allGroups :: [Test]
allGroups =
    [ testParse
    , testParseEval
    , testValidateWithExpectedMatch
    , testValidateWithExpectedMismatch
    , testValidationFail
    , testUserRewriteValidation
    , testProofEngine
    , testParseVal
    , testParseValFail
    , testCrashRegression
    , testExamples
    , testCli
    , testMir
    , testIntRange
    , testPipeline
    , testControlFlow
    , testLists
    , testArithmetic
    , testForallSyntax
    , testForallInstantiation
    , testForallProof
    , testForallGrownList
    , testForallLoops
    , testPrettyProofs
    , testMulDivNegative
    , testCrlf
    , testEnumCast
    , testListProofs
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
    , testBorrow
    , testCopies
    , testGenerics
    , testSequence
    , testStrings
    , testBytes
    , testConnectives
    , testMirData
    , testMirReader
    , testMirEmit
    , testBootstrap
    ]

groupName :: Test -> String
groupName (TestList name _) = name
groupName (TestCase name _) = name

data Arguments = Arguments
    { argumentJobs :: Maybe Int
    , argumentGroups :: [String]
    , argumentChild :: Bool
    }

parseArguments :: [String] -> Either String Arguments
parseArguments = go (Arguments Nothing [] False)
  where
    go arguments [] = Right arguments
    go arguments ("--child" : rest) = go arguments{argumentChild = True} rest
    go arguments ("-j" : number : rest) = withJobs arguments number rest
    go arguments ("--jobs" : number : rest) = withJobs arguments number rest
    go _ ["-j"] = Left "-j needs a number of jobs"
    go _ ["--jobs"] = Left "--jobs needs a number of jobs"
    go arguments (argument : rest)
        | "--jobs=" `isPrefixOf` argument = withJobs arguments (drop (length "--jobs=") argument) rest
        | "-j" `isPrefixOf` argument && length argument > 2 = withJobs arguments (drop 2 argument) rest
        | "-" `isPrefixOf` argument = Left ("unknown option: " ++ argument)
        | otherwise = go arguments{argumentGroups = argumentGroups arguments ++ [argument]} rest
    withJobs arguments number rest = case reads number of
        [(jobs, "")] | jobs >= (1 :: Int) -> go arguments{argumentJobs = Just jobs} rest
        _ -> Left ("-j needs a number of jobs (at least 1), not " ++ show number)

runInProcess :: [Test] -> IO (TestSummary, Bool)
runInProcess selected = do
    summary <- foldr combineSummaries (testSummary 0 0) <$> mapM (runTest []) selected
    pure (summary, True)

-- Each group runs in a process of its own, so that a group's temporary files, locale and environment are its own, and
-- several groups make progress at once. A child is given one group, so it runs in its process and prints no summary;
-- its [PASS]/[FAIL]/[CRASH] lines are the counts here, and its exit status says whether it failed.
runInParallel :: Int -> [String] -> IO (TestSummary, Bool)
runInParallel jobs names = do
    self <- getExecutablePath
    putStrLn ("Running " ++ show (length names) ++ " test groups in " ++ show jobs ++ " processes")
    sem <- newQSem jobs
    slots <- forM names $ \name -> do
        done <- newEmptyMVar
        _ <- forkIO $
            bracket_ (waitQSem sem) (signalQSem sem) $ do
                started <- getMonotonicTime
                -- (a group runs in one thread, so one capability is all its process can use: left to the package's -with-rtsopts=-N, every
                -- child would take as many capabilities as the machine has processors, so N children would make N times N of them and their
                -- threads and parallel garbage collectors would compete for the same cores)
                let arguments = [name, "--child", "+RTS", "-N1", "-RTS"]
                outcome <- try (readCreateProcessWithExitCode (proc self arguments) "")
                finished <- getMonotonicTime
                putMVar done (name, finished - started, outcome)
        pure done
    -- (the results are taken in the order of the list, so the output has the order it has without the processes)
    outcomes <- forM slots $ \done -> takeMVar done >>= printOutcome
    pure (foldr combineSummaries (testSummary 0 0) (map fst outcomes), all snd outcomes)

printOutcome :: (String, Double, Either SomeException (ExitCode, String, String)) -> IO (TestSummary, Bool)
printOutcome (name, seconds, outcome) = do
    let (exitCode, out, err) = case outcome of
            Right (status, stdoutText, stderrText) -> (status, stdoutText, stderrText)
            Left e -> (ExitFailure 1, "", displayException e)
    putStr out
    hPutStr stderr err
    let tenths = round (seconds * 10) :: Int
    putStrLn ("[TIME] " ++ name ++ " " ++ show (tenths `div` 10) ++ "." ++ show (tenths `mod` 10) ++ "s")
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

-- The [PASS]/[FAIL]/[CRASH] lines of a group, which is what the summary of the whole run adds up
countResults :: String -> TestSummary
countResults = foldl' count (testSummary 0 0) . lines
  where
    count summary line
        | "[PASS]" `isPrefixOf` line = testSummary (summaryPassed summary + 1) (summaryFailed summary)
        | "[FAIL]" `isPrefixOf` line || "[CRASH]" `isPrefixOf` line = testSummary (summaryPassed summary) (summaryFailed summary + 1)
        | otherwise = summary
