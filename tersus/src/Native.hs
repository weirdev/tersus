module Native
    ( buildExecutable
    ) where

import Control.Exception (IOException, finally, try)
import System.Directory (getTemporaryDirectory, removeFile)
import System.Exit (ExitCode (..))
import System.IO (hClose, hPutStr, openTempFile)
import System.Process (readProcessWithExitCode)

import LlvmRuntime (runtimeSource)
import Utils

-- Compiles LLVM IR (see LlvmEmit) and the runtime to an executable with clang. The two sources are written to files with
-- names no other program has, in the temporary directory, and only those files are removed afterwards.
buildExecutable :: FilePath -> String -> IO (Result () String)
buildExecutable output ir = do
    tmp <- getTemporaryDirectory
    irFile <- writeTemporary tmp "tersus.ll" ir
    runtimeFile <- writeTemporary tmp "tersus_rt.c" runtimeSource
    (do
        outcome <- try (readProcessWithExitCode "clang" ["-O2", "-Wno-override-module", "-o", output, irFile, runtimeFile] "")
        return $ case outcome of
            Left e -> Error ("Could not run clang: " ++ show (e :: IOException))
            Right (ExitSuccess, _, _) -> Ok ()
            Right (ExitFailure _, out, err) -> Error ("clang failed:\n" ++ out ++ err))
        `finally` (removeFile irFile >> removeFile runtimeFile)

-- A new file named after the template, with its extension kept, that holds the text
writeTemporary :: FilePath -> String -> String -> IO FilePath
writeTemporary dir template text = do
    (path, handle) <- openTempFile dir template
    hPutStr handle text
    hClose handle
    return path
