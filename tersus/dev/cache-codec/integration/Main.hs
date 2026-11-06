module Main (main) where

import Control.Monad (when)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import TestHarness
import TestSharedCache (testSharedCacheCodec, testSharedCacheProbe)

main :: IO ()
main = do
    args <- getArgs
    summary <- runTest [] (if "testSharedCacheProbe" `elem` args then testSharedCacheProbe else testSharedCacheCodec)
    putStrLn ("Summary: " ++ show (summaryPassed summary) ++ " passed, " ++ show (summaryFailed summary) ++ " failed")
    when (summaryFailed summary /= 0) exitFailure
