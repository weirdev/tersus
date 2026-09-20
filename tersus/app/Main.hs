module Main (main) where

import Control.Monad (unless)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.IO (hPutStr, hPutStrLn, stderr)

import Cli
import Utils

main :: IO ()
main = do
    args <- getArgs
    case parseCommandLine args of
        Nothing -> hPutStr stderr usage >> exitWith (ExitFailure 2)
        Just (command, file) -> do
            source <- readSource file
            case runSource command source of
                Ok output -> unless (null output) (putStrLn output)
                Error e -> hPutStrLn stderr e >> exitWith (ExitFailure 1)

readSource :: FilePath -> IO String
readSource "-" = getContents
readSource file = readFile file
