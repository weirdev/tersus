module CacheLock (openLockFd, openLockHandle) where

#include <fcntl.h>

import Control.Exception (bracketOnError)
import Foreign.C.Error (throwErrnoIfMinus1Retry)
import System.IO (Handle)
import System.Posix.Internals (c_open, withFilePath)
import System.Posix.IO (closeFd, fdToHandle)
import System.Posix.Types (Fd (..))

openLockFd :: FilePath -> IO Fd
openLockFd path = withFilePath path $ \name ->
    Fd <$> throwErrnoIfMinus1Retry "open cache lock"
        (c_open name #{const O_RDWR | O_CREAT | O_CLOEXEC} 0o600)

openLockHandle :: FilePath -> IO Handle
openLockHandle path = bracketOnError (openLockFd path) closeFd fdToHandle
