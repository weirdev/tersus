module Native
    ( buildExecutable
    ) where

import Control.Exception (IOException, finally, try)
import System.Directory (createDirectoryIfMissing, removeDirectoryRecursive)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import LlvmRuntime (runtimeSource)
import Utils

-- Compiles LLVM IR (see LlvmEmit) and the runtime to an executable with clang. The two sources are written to a directory
-- beside the output, which is removed afterwards.
buildExecutable :: FilePath -> String -> IO (Result () String)
buildExecutable output ir = do
    let dir = output ++ ".build"
        irFile = dir </> "program.ll"
        runtimeFile = dir </> "runtime.c"
    createDirectoryIfMissing True dir
    (do
        writeFile irFile ir
        writeFile runtimeFile runtimeSource
        outcome <- try (readProcessWithExitCode "clang" ["-O2", "-Wno-override-module", "-o", output, irFile, runtimeFile] "")
        return $ case outcome of
            Left e -> Error ("Could not run clang: " ++ show (e :: IOException))
            Right (ExitSuccess, _, _) -> Ok ()
            Right (ExitFailure _, out, err) -> Error ("clang failed:\n" ++ out ++ err))
        `finally` removeDirectoryRecursive dir
