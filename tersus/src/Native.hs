module Native
    ( cacheDirectory
    , cacheLock
    , cachedProgram
    , parallelBuilds
    , availableProcessors
    , buildExecutable
    , buildExecutableWith
    , buildExecutableFast
    , runExecutable
    , runWithInput
    , runWithInputFull
    , runCommandWithInputFull
    ) where

import Control.Concurrent (forkIOWithUnmask, killThread)
import Control.Concurrent.Chan (newChan, readChan, writeChan)
import Control.Concurrent.MVar (MVar, modifyMVar, newEmptyMVar, newMVar, putMVar, readMVar, withMVar)
import Control.Exception (IOException, SomeException, bracket, bracketOnError, evaluate, finally, mask, onException, throwIO, try)
import Control.Monad (forM)
import GHC.Conc (getNumCapabilities, getNumProcessors, setNumCapabilities)
import GHC.IO.Encoding (char8)
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, doesFileExist, getTemporaryDirectory, getXdgDirectory, removeFile, renameFile)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (Handle, IOMode (..), hClose, hGetContents, hIsTerminalDevice, hPutStr, hPutStrLn, hSetEncoding, openFile, openTempFile, stderr, stdin)
import System.IO.Error (isDoesNotExistError)
import System.Environment (getEnvironment)
import System.Posix.Signals (sigKILL, signalProcessGroup)
import System.Posix.Types (ProcessID)
import GHC.IO.Handle.Lock (LockMode (..), hLock)
import System.IO.Unsafe (unsafePerformIO)
import System.Info (os)

import qualified Data.Map.Strict as Map
import System.Process (CreateProcess (..), ProcessHandle, StdStream (..), getPid, proc, readCreateProcessWithExitCode, terminateProcess, waitForProcess, withCreateProcess)

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
                (code, out, err) <- runCommandWithInputFull "clang" ([opt, "-Wno-override-module"] ++ flags ++ ["-o", output, irFile, object]) ""
                return $ case code of
                    ExitSuccess -> Ok ()
                    ExitFailure _ -> Error ("clang failed:\n" ++ out ++ err))
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
                    (code, out, err) <- runCommandWithInputFull "clang" (["-O2", "-Wno-override-module"] ++ flags ++ ["-c", "-o", partial, runtimeFile]) "" `finally` removeFile runtimeFile
                    case code of
                        ExitSuccess -> renameFile partial object >> return (Ok object)
                        ExitFailure _ -> removeIfExists partial >> return (Error ("clang failed:\n" ++ out ++ err))

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
            Ok () -> do
                terminal <- hIsTerminalDevice stdin
                Ok <$> waitOwnedProcess (proc exe args){create_group = not terminal, delegate_ctlc = terminal})
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
runWithInputFull exe = runCommandWithInputFull exe []

-- The same for an executable given arguments
runCommandWithInputFull :: FilePath -> [String] -> String -> IO (ExitCode, String, String)
runCommandWithInputFull exe args = runProcessWithInputFull exe (proc exe args)

runProcessWithInputFull :: String -> CreateProcess -> String -> IO (ExitCode, String, String)
runProcessWithInputFull exe command input = do
    outcome <- try run :: IO (Either IOException (ExitCode, String, String))
    pure $ case outcome of
        Left e -> (ExitFailure 1, "", "Could not run " ++ exe ++ ": " ++ show e)
        Right done -> done
  where
    run = withTemporary "tersus-run-in.tmp" $ \(inPath, inHandle) ->
        withTemporary "tersus-run-out.tmp" $ \(outPath, outHandle) ->
            withTemporary "tersus-run-err.tmp" $ \(errPath, errHandle) -> do
                hSetEncoding inHandle char8
                hPutStr inHandle input
                hClose inHandle
                hSetEncoding outHandle char8
                hSetEncoding errHandle char8
                code <- bracket (openFile inPath ReadMode) hClose $ \readHandle -> do
                    hSetEncoding readHandle char8
                    waitOwnedProcess command{std_in = UseHandle readHandle, std_out = UseHandle outHandle,
                        std_err = UseHandle errHandle, create_group = True}
                hClose outHandle
                hClose errHandle
                out <- readBytes outPath
                err <- readBytes errPath
                pure (code, out, err)
    withTemporary name = bracket (getTemporaryDirectory >>= \dir -> openTempFile dir name) cleanupTemporary
    readBytes path = bracket (openFile path ReadMode) hClose $ \handle -> do
        hSetEncoding handle char8
        contents <- hGetContents handle
        _ <- evaluate (length contents)
        pure contents

waitOwnedProcess :: CreateProcess -> IO ExitCode
waitOwnedProcess command = mask $ \restore ->
    withCreateProcess command{close_fds = True} $ \_ _ _ process -> do
        pid <- getPid process
        restore (waitForProcess process) `onException` case pid of
            Just group | create_group command -> stopProcessGroup group process
            _ -> terminateProcess process >> waitForProcess process >> pure ()

stopProcessGroup :: ProcessID -> ProcessHandle -> IO ()
stopProcessGroup group process = do
    sent <- try (signalProcessGroup sigKILL group) :: IO (Either IOException ())
    case sent of
        Left e | not (isDoesNotExistError e) -> throwIO e
        _ -> pure ()
    _ <- waitForProcess process
    pure ()

cleanupTemporary :: (FilePath, Handle) -> IO ()
cleanupTemporary (path, handle) = do
    _ <- try (hClose handle) :: IO (Either IOException ())
    removeIfExists path

-- A new file named after the template, with its extension kept, that holds the text
writeTemporary :: FilePath -> String -> String -> IO FilePath
writeTemporary dir template text = bracketOnError (openTempFile dir template) cleanupTemporary $ \(path, handle) -> do
    hPutStr handle text
    hClose handle
    return path

-- Older GHCs count the machine's CPUs rather than the process's Linux affinity.
availableProcessors :: IO Int
availableProcessors
    | os /= "linux" = getNumProcessors
    | otherwise = do
        environment <- getEnvironment
        let clean = filter (\(name, _) -> name `notElem` ["OMP_NUM_THREADS", "OMP_THREAD_LIMIT"]) environment
        counted <- try (readCreateProcessWithExitCode (proc "nproc" []){env = Just clean, close_fds = True} "") :: IO (Either IOException (ExitCode, String, String))
        case counted of
            Right (ExitSuccess, output, _) -> case reads output of
                [(count, rest)] | count > 0 && all (`elem` " \t\r\n") rest -> pure count
                _ -> getNumProcessors
            _ -> getNumProcessors

{-# NOINLINE buildCapabilities #-}
buildCapabilities :: MVar (Int, Int)
buildCapabilities = unsafePerformIO (newMVar (0, 0))

acquireBuildCapabilities :: IO ()
acquireBuildCapabilities = modifyMVar buildCapabilities $ \(users, original) ->
    if users > 0 then pure ((users + 1, original), ()) else do
        previous <- getNumCapabilities
        processors <- availableProcessors
        setNumCapabilities processors
        pure ((1, previous), ())

releaseBuildCapabilities :: () -> IO ()
releaseBuildCapabilities _ = modifyMVar buildCapabilities $ \(users, original) ->
    if users > 1 then pure ((users - 1, original), ()) else do
        setNumCapabilities original
        pure ((0, 0), ())

-- Use the allowed CPUs until the last nested or overlapping build region exits.
parallelBuilds :: [IO a] -> IO [a]
parallelBuilds actions = bracket acquireBuildCapabilities releaseBuildCapabilities $ \_ -> do
    completed <- newChan
    let start [] = pure []
        start ((index, action) : rest) = do
            slot <- newEmptyMVar
            thread <- forkIOWithUnmask $ \unmask -> do
                result <- try (unmask action)
                putMVar slot result
                writeChan completed (index, result)
            others <- start rest `onException` stop [(thread, slot)]
            pure ((thread, slot) : others)
        stop running = do
            mapM_ (killThread . fst) running
            mapM_ (readMVar . snd) running
    bracket (start (zip [0 :: Int ..] actions)) stop $ \running -> do
        results <- forM running $ \_ -> do
            (index, result) <- readChan completed
            value <- either (\e -> throwIO (e :: SomeException)) pure result
            pure (index, value)
        pure (Map.elems (Map.fromList results))

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
                -- Keep the lock file: unlinking it could give waiters different inodes.
                -- Handle locks belong to open descriptions, not the process: independent
                -- build threads must not trigger fcntl's process-level deadlock detection.
                bracket (openFile (exe ++ ".lock") ReadWriteMode) hClose $ \handle -> do
                    hLock handle ExclusiveLock
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
