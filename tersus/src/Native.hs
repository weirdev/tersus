module Native
    ( cacheDirectory
    , cachedProgram
    , buildExecutable
    , buildExecutableWith
    , buildExecutableFast
    , runExecutable
    , runWithInput
    , runWithInputFull
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar, withMVar)
import Control.Exception (IOException, evaluate, finally, try)
import GHC.IO.Encoding (char8)
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, doesFileExist, getTemporaryDirectory, getXdgDirectory, removeFile, renameFile)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (IOMode (..), hClose, hGetContents, hPutStr, hPutStrLn, hSetEncoding, openFile, openTempFile, stderr)
import System.IO.Unsafe (unsafePerformIO)

import qualified Data.Map.Strict as Map
import System.Process (CreateProcess (..), StdStream (..), createProcess, proc, readProcessWithExitCode, rawSystem, waitForProcess)

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

-- What the executable at the path writes for the input: its output, or its reason (on the standard error) for refusing it. The bytes are read as they are.
-- The input and the output go through files, not pipes: with the non-threaded runtime a thread that feeds a pipe is never run while the process is
-- waited on, so a program fed through pipes stops both ways (a thread per pipe does not help there, and callers may run programs at the same time either way).
runWithInput :: FilePath -> String -> IO (Result String String)
runWithInput exe input = do
    (code, out, err) <- runWithInputFull exe input
    pure $ case code of
        ExitSuccess -> Ok out
        ExitFailure _ -> Error (dropWhileEnd' (== '\n') (decodeUtf8 err))
  where
    dropWhileEnd' p = reverse . dropWhile p . reverse

-- The same with everything the executable did: its exit status, what it wrote, and what it wrote to the standard error. A program
-- written in Tersus says it refuses its input on the standard error and gives 1 as its value, which the runtime writes and still
-- exits with success, so a caller that has to tell a refusal from an answer reads those, not the status.
runWithInputFull :: FilePath -> String -> IO (ExitCode, String, String)
runWithInputFull exe input = do
    outcome <- try run :: IO (Either IOException (ExitCode, String, String))
    pure $ case outcome of
        Left e -> (ExitFailure 1, "", "Could not run " ++ exe ++ ": " ++ show e)
        Right done -> done
  where
    run = do
        (inPath, inHandle) <- openTempFileAt "tersus-run-in.tmp"
        (outPath, outHandle) <- openTempFileAt "tersus-run-out.tmp"
        (errPath, errHandle) <- openTempFileAt "tersus-run-err.tmp"
        finally
            ( do
                hSetEncoding inHandle char8
                hPutStr inHandle input
                hClose inHandle
                hSetEncoding outHandle char8
                hSetEncoding errHandle char8
                readHandle <- openFile inPath ReadMode
                hSetEncoding readHandle char8
                (_, _, _, process) <- createProcess (proc exe []){std_in = UseHandle readHandle, std_out = UseHandle outHandle, std_err = UseHandle errHandle}
                code <- waitForProcess process
                hClose readHandle
                hClose outHandle
                hClose errHandle
                out <- readBytes outPath
                err <- readBytes errPath
                pure (code, out, err)
            )
            (mapM_ removeFile [inPath, outPath, errPath])
    openTempFileAt name = getTemporaryDirectory >>= \dir -> openTempFile dir name
    readBytes path = do
        handle <- openFile path ReadMode
        hSetEncoding handle char8
        contents <- hGetContents handle
        _ <- evaluate (length contents)
        hClose handle
        pure contents

-- A new file named after the template, with its extension kept, that holds the text
writeTemporary :: FilePath -> String -> String -> IO FilePath
writeTemporary dir template text = do
    (path, handle) <- openTempFile dir template
    hPutStr handle text
    hClose handle
    return path

-- A program in the cache, named for what it is made of: made by the action if it is not there. It is made under another name and moved, so that a build that is cut
-- short leaves nothing that looks like the program.
-- One build of a cached program at a time in this process: callers that reach a cold cache together (the cases of a
-- parallel test group) would otherwise each build it. A lock for each of them, since building one of them builds the
-- other first (the emitter is made by the seed).
{-# NOINLINE cacheLocks #-}
cacheLocks :: MVar (Map.Map String (MVar ()))
cacheLocks = unsafePerformIO (newMVar Map.empty)

cacheLock :: String -> IO (MVar ())
cacheLock key = modifyMVar cacheLocks $ \locks -> case Map.lookup key locks of
    Just lock -> pure (locks, lock)
    Nothing -> do
        lock <- newMVar ()
        pure (Map.insert key lock locks, lock)

cachedProgram :: String -> String -> String -> (FilePath -> IO (Result () String)) -> IO (Result FilePath String)
cachedProgram kind hash what build = do
    lock <- cacheLock (kind ++ hash)
    withMVar lock $ \_ -> do
        cache <- cacheDirectory
        case cache of
            Error e -> pure (Error e)
            Ok dir -> do
                let exe = dir </> (kind ++ "-" ++ hash)
                present <- doesFileExist exe
                if present
                    then pure (Ok exe)
                    else do
                        hPutStrLn stderr ("Building " ++ what ++ " (once, it is kept in the cache)...")
                        (partial, handle) <- openTempFile dir (kind ++ ".tmp")
                        hClose handle
                        removeFile partial
                        built <- build partial
                        case built of
                            Error e -> pure (Error e)
                            Ok () -> renameFile partial exe >> pure (Ok exe)
