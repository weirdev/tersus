module Main (main) where

import Control.Monad (unless)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import GHC.IO.Encoding (char8, setFileSystemEncoding)
import System.IO (hPutStr, hPutStrLn, stderr)

import Bootstrap (llvmOfOwned, tersusLlvm)
import Cli
import qualified Modules
import Native (buildExecutable, runExecutable)
import Pipeline (compileModulesToOwned)
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
            package <- loadPackage file
            case package of
                Just (Left err) -> failWith err
                _ -> do
                    source <- case package of
                        Nothing -> readSource file
                        Just _ -> return ""
                    -- (a program that is read from the standard input has none left to read)
                    input <- if command == Interpret && file /= "-" then readInputBytes else return ""
                    -- (the IR is written by the emitter in Tersus)
                    result <- case package of
                        Just (Right pkg)
                            | makesIr command -> case compileModulesToOwned pkg of
                                Error err -> pure (Error err)
                                Ok owned -> mapResult (\ir -> ((ir, ""), [])) <$> llvmOfOwned owned
                            | otherwise -> pure (runPackageFiles (World input programArgs readWorldFile) command pkg)
                        _
                            | makesIr command -> mapResult (\ir -> ((ir, ""), [])) <$> tersusLlvm source
                            | otherwise -> pure (runSourceFiles (World input programArgs readWorldFile) command source)
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

loadPackage :: FilePath -> IO (Maybe (Either String Modules.LoadedPackage))
loadPackage "-" = return Nothing
loadPackage file = do
    root <- Modules.findPackageRootIO file
    case root of
        Nothing -> return Nothing
        Just _ -> do
            loaded <- Modules.loadFromFilesystem file
            return $ case loaded of
                Left err -> Just (Left err)
                Right (Modules.PackageResult pkg) -> Just (Right pkg)
                Right _ -> Nothing
