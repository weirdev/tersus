module TestTersus (main) where

import Control.Monad (when)
import System.Exit (exitFailure)

import TestHarness
import TestBasics
import TestValidation
import TestProofs
import TestControl
import TestData
import TestPipeline

main :: IO ()
main = do
    summary <-
        foldr combineSummaries (testSummary 0 0)
            <$> mapM
                (runTest [])
                [ testParse
                , testEvaluateFullContext
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
                , testPrecedence
                , testFirstLast
                , testFunctionCalls
                , testValidationFuel
                ]
    putStrLn $
        "Summary: "
            ++ show (summaryPassed summary)
            ++ " passed, "
            ++ show (summaryFailed summary)
            ++ " failed"
    when (summaryFailed summary > 0) exitFailure
