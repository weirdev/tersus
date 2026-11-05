module CacheLock
    ( openLockFd
    , openLockHandle
    , openTempFileCloexec
    , openBinaryTempFileCloexec
    , withExecutableTempFile
    , copyFileCloexec
    , withSpawnShared
    , withExecutableWrite
    ) where

#include <fcntl.h>

import Control.Concurrent.MVar (MVar, newMVar, putMVar, takeMVar)
import Control.Exception (IOException, SomeException, bracket, bracketOnError, finally, mask, mask_, onException, throwIO, try)
import Data.Bits ((.&.))
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.Word (Word8)
import Foreign.C.Error (eEXIST, eINTR, errnoToIOError, getErrno, throwErrnoIfMinus1Retry)
import Foreign.C.Types (CInt)
import Foreign.Marshal.Alloc (allocaBytes)
import Foreign.Ptr (Ptr, plusPtr)
import System.Directory (removeFile, renameFile)
import System.FilePath ((</>), takeDirectory)
import System.IO (Handle, hClose, hSetBinaryMode)
import System.IO.Unsafe (unsafePerformIO)
import System.Posix.Files (fileMode, getFdStatus, setFdMode)
import System.Posix.Internals (c_open, withFilePath)
import System.Posix.IO (closeFd, fdReadBuf, fdToHandle, fdWriteBuf)
import System.Posix.Process (getProcessID)
import System.Posix.Types (ByteCount, Fd (..))

writeFlags :: CInt
writeFlags = #{const O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC}

readFlags :: CInt
readFlags = #{const O_RDONLY | O_CLOEXEC}

openLockFd :: FilePath -> IO Fd
openLockFd path = withFilePath path $ \name ->
    Fd <$> throwErrnoIfMinus1Retry "open cache lock"
        (c_open name #{const O_RDWR | O_CREAT | O_CLOEXEC} 0o600)

openLockHandle :: FilePath -> IO Handle
openLockHandle path = bracketOnError (openLockFd path) closeFd fdToHandle

-- CLOEXEC only closes inherited writable descriptors at exec. Exclude the
-- clone-to-exec window too: spawns share this lock only during creation,
-- executable writers hold it through close. No holder may acquire the other
-- side recursively; child waits and output draining must happen after release.
{-# NOINLINE spawnEntry #-}
spawnEntry :: MVar ()
spawnEntry = unsafePerformIO (newMVar ())

{-# NOINLINE spawnReaders #-}
spawnReaders :: MVar Int
spawnReaders = unsafePerformIO (newMVar 0)

{-# NOINLINE spawnResource #-}
spawnResource :: MVar ()
spawnResource = unsafePerformIO (newMVar ())

withSpawnShared :: IO a -> IO a
withSpawnShared action = mask $ \restore -> do
    acquireShared
    outcome <- tried (restore action)
    releaseShared
    either throwIO pure outcome

-- A waiting writer holds the turnstile, so readers that arrive after it queue
-- behind it rather than starving it.
withExecutableWrite :: IO a -> IO a
withExecutableWrite action = mask $ \restore -> do
    takeMVar spawnEntry
    takeMVar spawnResource `onException` putMVar spawnEntry ()
    outcome <- tried (restore action)
    putMVar spawnResource ()
    putMVar spawnEntry ()
    either throwIO pure outcome

tried :: IO a -> IO (Either SomeException a)
tried = try

acquireShared :: IO ()
acquireShared = mask_ $ do
    takeMVar spawnEntry
    outcome <- tried (do
        held <- takeMVar spawnReaders
        (if held == 0 then takeMVar spawnResource else pure ())
            `onException` putMVar spawnReaders held
        putMVar spawnReaders (held + 1))
    putMVar spawnEntry ()
    either throwIO pure outcome

releaseShared :: IO ()
releaseShared = mask_ $ do
    held <- takeMVar spawnReaders
    (if held == 1 then putMVar spawnResource () else pure ())
        `onException` putMVar spawnReaders held
    putMVar spawnReaders (held - 1)

openTempFileCloexec :: FilePath -> String -> IO (FilePath, Handle)
openTempFileCloexec = newTempFile False

openBinaryTempFileCloexec :: FilePath -> String -> IO (FilePath, Handle)
openBinaryTempFileCloexec = newTempFile True

newTempFile :: Bool -> FilePath -> String -> IO (FilePath, Handle)
newTempFile binary dir template = mask $ \restore -> do
    (path, fd) <- newTempFd dir template
    handle <- fdToHandle fd `onException` (closeFd fd >> removeQuietly path)
    restore (if binary then hSetBinaryMode handle True else pure ())
        `onException` (hClose handle >> removeQuietly path)
    pure (path, handle)

{-# NOINLINE tempNames #-}
tempNames :: IORef Int
tempNames = unsafePerformIO (newIORef 0)

newTempFd :: FilePath -> String -> IO (FilePath, Fd)
newTempFd dir template = getProcessID >>= attempt (0 :: Int)
  where
    (prefix, suffix) = templateParts template
    attempt tries pid
        | tries >= 4096 = ioError (userError ("could not make a new temporary file in " ++ dir))
        | otherwise = do
            unique <- atomicModifyIORef' tempNames (\n -> (n + 1, n))
            let path = dir </> (prefix ++ show pid ++ "-" ++ show unique ++ suffix)
            opened <- withFilePath path (\name -> c_open name writeFlags 0o600)
            if opened >= 0 then pure (path, Fd opened) else do
                errno <- getErrno
                if errno == eEXIST || errno == eINTR
                    then attempt (tries + 1) pid
                    else ioError (errnoToIOError "openTempFileCloexec" errno Nothing (Just path))

-- The unique part goes before the extension, not after it, so a caller that
-- asks for "entry.tmp" or "tersus_rt.c" keeps that extension.
templateParts :: String -> (String, String)
templateParts template = case break (== '.') (reverse template) of
    (reversedSuffix, "") -> (reverse reversedSuffix, "")
    (reversedSuffix, _ : rest) -> (reverse rest, '.' : reverse reversedSuffix)

withExecutableTempFile :: FilePath -> String -> ((FilePath, Handle) -> IO a) -> IO a
withExecutableTempFile dir template use =
    withExecutableWrite (bracketOnError (newTempFile False dir template) discardTemporary use)

discardTemporary :: (FilePath, Handle) -> IO ()
discardTemporary (path, handle) = do
    _ <- try (hClose handle) :: IO (Either IOException ())
    removeQuietly path

copyFileCloexec :: FilePath -> FilePath -> IO ()
copyFileCloexec source target = withExecutableWrite $
    bracket (openReadFd source) closeFd $ \input -> do
        mode <- (.&. 0o7777) . fileMode <$> getFdStatus input
        mask $ \restore -> do
            (staging, output) <- newTempFd (takeDirectory target) "copy.tmp"
            (restore (copyBytes input output >> setFdMode output mode) `finally` closeFd output)
                `onException` removeQuietly staging
            restore (renameFile staging target) `onException` removeQuietly staging

removeQuietly :: FilePath -> IO ()
removeQuietly path = do
    _ <- try (removeFile path) :: IO (Either IOException ())
    pure ()

openReadFd :: FilePath -> IO Fd
openReadFd path = withFilePath path $ \name ->
    Fd <$> throwErrnoIfMinus1Retry ("copyFileCloexec " ++ path) (c_open name readFlags 0)

copyBytes :: Fd -> Fd -> IO ()
copyBytes input output = allocaBytes chunk next
  where
    chunk = 65536
    next :: Ptr Word8 -> IO ()
    next buffer = do
        got <- fdReadBuf input buffer (fromIntegral chunk)
        if got == 0 then pure () else put buffer got >> next buffer
    put :: Ptr Word8 -> ByteCount -> IO ()
    put buffer remaining
        | remaining == 0 = pure ()
        | otherwise = do
            written <- fdWriteBuf output buffer remaining
            put (buffer `plusPtr` fromIntegral written) (remaining - written)
