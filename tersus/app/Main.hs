module Main (main) where

import Control.Monad (unless)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import GHC.IO.Encoding (char8, setFileSystemEncoding)
import System.IO (hPutStr, hPutStrLn, stderr)

import Bootstrap (tersusLlvm)
import Cli
import Native (buildExecutable, runExecutable)
import Utils

main :: IO ()
main = do
    useUtf8
    -- (the arguments are the bytes they were given as, whatever the locale is: they are the arguments of the program too)
    setFileSystemEncoding char8
    args <- getArgs
    case parseProgramArguments args of
        Nothing -> hPutStr stderr usage >> exitWith (ExitFailure 2)
        Just (command, file, programArgs) -> do
            source <- readSource file
            -- (a program that is read from the standard input has none left to read)
            input <- if command == Interpret && file /= "-" then readInputBytes else return ""
            -- (the IR is written by the emitter in Tersus)
            result <-
                if makesIr command
                    then mapResult (\ir -> ((ir, ""), [])) <$> tersusLlvm source
                    else pure (runSourceFiles (World input programArgs readWorldFile) command source)
            case result of
                Error e -> failWith e
                Ok ((output, errors), files) -> case command of
                    Build executable -> do
                        built <- buildExecutable executable output
                        case built of
                            Error e -> failWith e
                            Ok () -> return ()
                    Run -> do
                        ran <- runExecutable output programArgs
                        case ran of
                            Error e -> failWith e
                            Ok ExitSuccess -> return ()
                            Ok code -> exitWith code
                    _ -> do
                        -- (the files that the program wrote are written when it has run, whatever it printed)
                        failed <- writeWorldFiles files
                        mapM_ (\path -> hPutStrLn stderr ("could not write " ++ path)) failed
                        hPutStr stderr errors >> unless (null output) (putStrLn output)

failWith :: String -> IO ()
failWith e = hPutStrLn stderr e >> exitWith (ExitFailure 1)

readSource :: FilePath -> IO String
readSource = readSourceFile
