module Native
    ( buildExecutable
    , buildExecutableWith
    , buildExecutableFast
    , runExecutable
    ) where

import Control.Exception (IOException, finally, try)
import System.Directory (doesFileExist, getTemporaryDirectory, removeFile, renameFile)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (hClose, hPutStr, openTempFile)
import System.Process (readProcessWithExitCode, rawSystem)

import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import Utils

-- Compiles LLVM IR (written by the emitter in Tersus, see Bootstrap) and the runtime to an executable with clang. The two sources are written to files with
-- names no other program has, in the temporary directory, and only those files are removed afterwards.
buildExecutable :: FilePath -> String -> IO (Result () String)
buildExecutable = buildExecutableWith []

-- With more flags for clang (the tests build with -DTERSUS_CHECK, which makes the runtime check its use of memory)
buildExecutableWith :: [String] -> FilePath -> String -> IO (Result () String)
buildExecutableWith = buildWith "-O2"

-- The same without optimizing: an executable that is built to be run once (a test) is made sooner, and does what it does as
-- slowly as it does; what the language defines (the overflow checks of the IR, the checks of the runtime) is the same.
buildExecutableFast :: [String] -> FilePath -> String -> IO (Result () String)
buildExecutableFast = buildWith "-O0"

buildWith :: String -> [String] -> FilePath -> String -> IO (Result () String)
buildWith opt flags output ir = do
    tmp <- getTemporaryDirectory
    irFile <- writeTemporary tmp "tersus.ll" ir
    (do
        runtime <- runtimeObject tmp flags
        case runtime of
            Error e -> return (Error e)
            Ok object -> do
                outcome <- try (readProcessWithExitCode "clang" ([opt, "-Wno-override-module"] ++ flags ++ ["-o", output, irFile, object]) "")
                return $ case outcome of
                    Left e -> Error ("Could not run clang: " ++ show (e :: IOException))
                    Right (ExitSuccess, _, _) -> Ok ()
                    Right (ExitFailure _, out, err) -> Error ("clang failed:\n" ++ out ++ err))
        `finally` removeFile irFile

-- The runtime compiled once for a set of flags, kept in the temporary directory under a name made of what it is made of: a
-- build that is cut short leaves it under another name, and one that is there is used as it is.
runtimeObject :: FilePath -> [String] -> IO (Result FilePath String)
runtimeObject tmp flags = do
    let object = tmp </> ("tersus_rt_" ++ fingerprint (runtimeSource : flags) ++ ".o")
    present <- doesFileExist object
    if present
        then return (Ok object)
        else do
            runtimeFile <- writeTemporary tmp "tersus_rt.c" runtimeSource
            (partial, handle) <- openTempFile tmp "tersus_rt.tmp"
            hClose handle
            removeFile partial
            outcome <- try (readProcessWithExitCode "clang" (["-O2", "-Wno-override-module"] ++ flags ++ ["-c", "-o", partial, runtimeFile]) "") `finally` removeFile runtimeFile
            case outcome of
                Left e -> return (Error ("Could not run clang: " ++ show (e :: IOException)))
                Right (ExitSuccess, _, _) -> renameFile partial object >> return (Ok object)
                Right (ExitFailure _, out, err) -> removeFile partial >> return (Error ("clang failed:\n" ++ out ++ err))

-- Compiles the IR to an executable in the temporary directory, runs it with the input and output of this process, and removes it.
-- Ok holds the exit status of the program, and Error says that it could not be built.
runExecutable :: String -> [String] -> IO (Result ExitCode String)
runExecutable ir args = do
    tmp <- getTemporaryDirectory
    exe <- writeTemporary tmp "tersus_run" ""
    -- (the file only names a place: the linker makes the executable there)
    removeFile exe
    (do
        built <- buildExecutable exe ir
        case built of
            Error e -> return (Error e)
            Ok () -> Ok <$> rawSystem exe args)
        `finally` (try (removeFile exe) :: IO (Either IOException ()))

-- A new file named after the template, with its extension kept, that holds the text
writeTemporary :: FilePath -> String -> String -> IO FilePath
writeTemporary dir template text = do
    (path, handle) <- openTempFile dir template
    hPutStr handle text
    hClose handle
    return path
