module Main (main) where

import Control.Monad (unless)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.IO (hPutStr, hPutStrLn, stderr)

import Cli
import Native (buildExecutable, runExecutable)
import Utils

main :: IO ()
main = do
    useUtf8
    args <- getArgs
    case parseCommandLine args of
        Nothing -> hPutStr stderr usage >> exitWith (ExitFailure 2)
        Just (command, file) -> do
            source <- readSource file
            case runSource command source of
                Error e -> failWith e
                Ok output -> case command of
                    Build executable -> do
                        built <- buildExecutable executable output
                        case built of
                            Error e -> failWith e
                            Ok () -> return ()
                    Run -> do
                        ran <- runExecutable output
                        case ran of
                            Error e -> failWith e
                            Ok ExitSuccess -> return ()
                            Ok code -> exitWith code
                    _ -> unless (null output) (putStrLn output)

failWith :: String -> IO ()
failWith e = hPutStrLn stderr e >> exitWith (ExitFailure 1)

readSource :: FilePath -> IO String
readSource = readSourceFile
