module Native
    ( buildExecutable
    , buildExecutableWith
    , runExecutable
    ) where

import Control.Exception (IOException, finally, try)
import System.Directory (getTemporaryDirectory, removeFile)
import System.Exit (ExitCode (..))
import System.IO (hClose, hPutStr, openTempFile)
import System.Process (readProcessWithExitCode, rawSystem)

import LlvmRuntime (runtimeSource)
import Utils

-- Compiles LLVM IR (see LlvmEmit) and the runtime to an executable with clang. The two sources are written to files with
-- names no other program has, in the temporary directory, and only those files are removed afterwards.
buildExecutable :: FilePath -> String -> IO (Result () String)
buildExecutable = buildExecutableWith []

-- With more flags for clang (the tests build with -DTERSUS_CHECK, which makes the runtime check its use of memory)
buildExecutableWith :: [String] -> FilePath -> String -> IO (Result () String)
buildExecutableWith flags output ir = do
    tmp <- getTemporaryDirectory
    irFile <- writeTemporary tmp "tersus.ll" ir
    runtimeFile <- writeTemporary tmp "tersus_rt.c" runtimeSource
    (do
        outcome <- try (readProcessWithExitCode "clang" (["-O2", "-Wno-override-module"] ++ flags ++ ["-o", output, irFile, runtimeFile]) "")
        return $ case outcome of
            Left e -> Error ("Could not run clang: " ++ show (e :: IOException))
            Right (ExitSuccess, _, _) -> Ok ()
            Right (ExitFailure _, out, err) -> Error ("clang failed:\n" ++ out ++ err))
        `finally` (removeFile irFile >> removeFile runtimeFile)

-- Compiles the IR to an executable in the temporary directory, runs it with the input and output of this process, and removes it.
-- Ok holds the exit status of the program, and Error says that it could not be built.
runExecutable :: String -> IO (Result ExitCode String)
runExecutable ir = do
    tmp <- getTemporaryDirectory
    exe <- writeTemporary tmp "tersus_run" ""
    -- (the file only names a place: the linker makes the executable there)
    removeFile exe
    (do
        built <- buildExecutable exe ir
        case built of
            Error e -> return (Error e)
            Ok () -> Ok <$> rawSystem exe [])
        `finally` (try (removeFile exe) :: IO (Either IOException ()))

-- A new file named after the template, with its extension kept, that holds the text
writeTemporary :: FilePath -> String -> String -> IO FilePath
writeTemporary dir template text = do
    (path, handle) <- openTempFile dir template
    hPutStr handle text
    hClose handle
    return path
