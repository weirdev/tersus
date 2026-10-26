module Bootstrap
    ( emitterHash
    , stageZero
    , stageOne
    , cachedEmitter
    , tersusLlvm
    , emitWith
    ) where

import Control.Exception (IOException, finally, try)
import Data.Bits (xor)
import Data.Char (ord)
import Data.List (foldl')
import Data.Word (Word64)
import GHC.IO.Encoding (char8, getFileSystemEncoding, getLocaleEncoding, setFileSystemEncoding, setLocaleEncoding)
import Numeric (showHex)
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, doesFileExist, getXdgDirectory, removeFile, renameFile)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (hClose, hPutStrLn, openTempFile, stderr)
import System.Process (readProcessWithExitCode)

import LlvmRuntime (runtimeSource)
import MirData (writeProgram)
import Native (buildExecutable)
import Pipeline (llvmSource, ownedSource)
import PreludeSource (emitterSource, listsSource, preludeSource, stringSource)
import Utils

-- The lowering to LLVM IR that is written in Tersus (examples/emit.tersus, step 31 and STEP31.md) as the compiler's own emitter. An executable of it reads the MIR of a
-- program as data (MirData) and writes its LLVM IR, which is what `tersus --tersus-emitter` uses instead of LlvmEmit. It is made in two stages:
-- - stage 0 is the emitter built from the IR that LlvmEmit (Haskell) writes for it. It is built when it is first used, and kept in the cache under a hash of the
--   sources it is made of (`cachedEmitter`), so that building this package needs no clang;
-- - stage 1 is the emitter built from the IR that stage 0 writes for the emitter's own source (`stageOne`). The IR has to be the same text as stage 0 was built from,
--   and then stage 1 is stage 0 again; the tests check that, for the emitter and for every program.

-- A hash (FNV-1a, 64 bits, as 16 hexadecimal digits) of the text that stage 0 is made of: the emitter, the runtime it is linked with, and the library every program
-- has. What LlvmEmit writes for them is not part of it.
emitterHash :: String
emitterHash = let digits = showHex (foldl' step 14695981039346656037 (concatMap (++ "\0") parts)) "" in replicate (16 - length digits) '0' ++ digits
  where
    parts = [emitterSource, runtimeSource, preludeSource, listsSource, stringSource]
    step :: Word64 -> Char -> Word64
    step h c = (h `xor` fromIntegral (ord c)) * 1099511628211

-- Stage 0: the emitter built, at the path, from the IR of LlvmEmit
stageZero :: FilePath -> IO (Result () String)
stageZero output = case llvmSource emitterSource of
    Error e -> pure (Error e)
    Ok ir -> buildExecutable output ir

-- Stage 1: the emitter built, at the path, from the IR that the emitter at the first path writes for it
stageOne :: FilePath -> FilePath -> IO (Result () String)
stageOne compiler output = case ownedSource emitterSource of
    Error e -> pure (Error e)
    Ok owned -> do
        ir <- emitWith compiler (writeProgram owned)
        case ir of
            Error e -> pure (Error e)
            Ok text -> buildExecutable output text

-- What the emitter at the path writes for the MIR as data: its IR, or its reason (on the standard error) for refusing the program. The bytes are read as they are.
emitWith :: FilePath -> String -> IO (Result String String)
emitWith exe input = do
    saved <- getLocaleEncoding
    savedFs <- getFileSystemEncoding
    setLocaleEncoding char8
    setFileSystemEncoding char8
    outcome <- try (readProcessWithExitCode exe [] input) `finally` (setLocaleEncoding saved >> setFileSystemEncoding savedFs)
    pure $ case outcome of
        Left e -> Error ("Could not run the emitter: " ++ show (e :: IOException))
        Right (ExitSuccess, out, _) -> Ok out
        Right (ExitFailure _, _, err) -> Error (dropWhileEnd' (== '\n') (decodeUtf8 err))
  where
    dropWhileEnd' p = reverse . dropWhile p . reverse

-- Stage 0 in the cache, built if it is not there yet
cachedEmitter :: IO (Result FilePath String)
cachedEmitter = do
    cache <- cacheDirectory
    case cache of
        Error e -> pure (Error e)
        Ok dir -> do
            let exe = dir </> ("emitter-" ++ emitterHash)
            present <- doesFileExist exe
            if present then pure (Ok exe) else build dir exe
  where
    build dir exe = do
        hPutStrLn stderr "Building the emitter written in Tersus (once, it is kept in the cache)..."
        -- (built where nothing else will be, and moved: a build that is cut short leaves nothing that looks like the emitter)
        (partial, handle) <- openTempFile dir "emitter.tmp"
        hClose handle
        removeFile partial
        built <- stageZero partial
        case built of
            Error e -> pure (Error e)
            Ok () -> renameFile partial exe >> pure (Ok exe)

-- Where the emitter is kept: the cache directory of the user. There is no fallback to a shared directory such as /tmp, where another user could have put a program
-- of their own under the name of the emitter, which would be run as this user.
cacheDirectory :: IO (Result FilePath String)
cacheDirectory = do
    cache <- getXdgDirectory XdgCache "tersus"
    made <- try (createDirectoryIfMissing True cache)
    pure $ case made of
        Right () -> Ok cache
        Left e -> Error ("Could not make the cache directory " ++ cache ++ " for the emitter: " ++ show (e :: IOException))

-- The LLVM IR of a program, by the emitter in Tersus
tersusLlvm :: String -> IO (Result String String)
tersusLlvm source = case ownedSource source of
    Error e -> pure (Error e)
    Ok owned -> do
        exe <- cachedEmitter
        case exe of
            Error e -> pure (Error e)
            Ok path -> do
                ir <- emitWith path (writeProgram owned)
                pure (either' ir)
  where
    either' (Error e) = Error ("Native code failed: " ++ e)
    either' ok = ok
