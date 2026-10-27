module TestTersus (main) where

import Control.Monad (when)
import System.Exit (exitFailure)
import System.IO (BufferMode (LineBuffering), hSetBuffering, stdout)

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
    summary <-
        foldr combineSummaries (testSummary 0 0)
            <$> mapM
                (runTest [])
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
    putStrLn $
        "Summary: "
            ++ show (summaryPassed summary)
            ++ " passed, "
            ++ show (summaryFailed summary)
            ++ " failed"
    when (summaryFailed summary > 0) exitFailure
