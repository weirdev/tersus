module Native
    ( cacheDirectory
    , buildExecutable
    , buildExecutableWith
    , buildExecutableFast
    , runExecutable
    ) where

import Control.Exception (IOException, finally, try)
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, doesFileExist, getTemporaryDirectory, getXdgDirectory, removeFile, renameFile)
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
        runtime <- runtimeObject flags
        case runtime of
            Error e -> return (Error e)
            Ok object -> do
                outcome <- try (readProcessWithExitCode "clang" ([opt, "-Wno-override-module"] ++ flags ++ ["-o", output, irFile, object]) "")
                return $ case outcome of
                    Left e -> Error ("Could not run clang: " ++ show (e :: IOException))
                    Right (ExitSuccess, _, _) -> Ok ()
                    Right (ExitFailure _, out, err) -> Error ("clang failed:\n" ++ out ++ err))
        `finally` removeFile irFile

-- The runtime compiled once for a set of flags, kept in the cache directory of the user under a name made of what it is made
-- of: the temporary directory is shared, and another user could put an object of their own at a name that can be worked out
-- from the runtime and the flags, which would then be linked into a program and run. A build that is cut short leaves its
-- object under another name, and one that is there is used as it is.
runtimeObject :: [String] -> IO (Result FilePath String)
runtimeObject flags = do
    cache <- cacheDirectory
    case cache of
        Error e -> return (Error e)
        Ok dir -> do
            let object = dir </> ("tersus_rt_" ++ fingerprint (runtimeSource : flags) ++ ".o")
            present <- doesFileExist object
            if present
                then return (Ok object)
                else do
                    tmp <- getTemporaryDirectory
                    runtimeFile <- writeTemporary tmp "tersus_rt.c" runtimeSource
                    (partial, handle) <- openTempFile dir "tersus_rt.tmp"
                    hClose handle
                    removeFile partial
                    outcome <- try (readProcessWithExitCode "clang" (["-O2", "-Wno-override-module"] ++ flags ++ ["-c", "-o", partial, runtimeFile]) "") `finally` removeFile runtimeFile
                    case outcome of
                        Left e -> removeIfExists partial >> return (Error ("Could not run clang: " ++ show (e :: IOException)))
                        Right (ExitSuccess, _, _) -> renameFile partial object >> return (Ok object)
                        Right (ExitFailure _, out, err) -> removeIfExists partial >> return (Error ("clang failed:\n" ++ out ++ err))

-- Where the runtime objects are kept: the cache directory of the user, as for the emitter (see Bootstrap). There is no
-- fallback to a shared directory such as /tmp, where another user could have put an object of their own under the name of
-- one of these, which would be linked into a program and run as this user.
cacheDirectory :: IO (Result FilePath String)
cacheDirectory = do
    cache <- getXdgDirectory XdgCache "tersus"
    made <- try (createDirectoryIfMissing True cache)
    pure $ case made of
        Right () -> Ok cache
        Left e -> Error ("Could not make the cache directory " ++ cache ++ " for the runtime: " ++ show (e :: IOException))

-- Removes a file that may not be there (a compiler that failed before it made its output)
removeIfExists :: FilePath -> IO ()
removeIfExists path = do
    _ <- try (removeFile path) :: IO (Either IOException ())
    return ()

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
