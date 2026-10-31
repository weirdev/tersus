module Bootstrap
    ( seedHash
    , seedSha256
    , seedUrl
    , emitterHash
    , stageZero
    , stageOne
    , cachedSeed
    , cachedEmitter
    , tersusLlvm
    , llvmOfOwned
    , emitWith
    ) where

import Control.Exception (IOException, evaluate, finally, try)
import Data.Char (isHexDigit)
import GHC.IO.Encoding (char8)
import System.Directory (XdgDirectory (..), createDirectoryIfMissing, doesFileExist, getTemporaryDirectory, getXdgDirectory, removeFile, renameFile)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import Control.Concurrent.MVar (MVar, modifyMVar, newMVar, withMVar)
import System.IO (IOMode (..), hClose, hGetContents, hPutStr, hPutStrLn, hSetEncoding, openFile, openTempFile, stderr)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (CreateProcess (..), StdStream (..), createProcess, proc, readProcessWithExitCode, waitForProcess)

import qualified Data.Map.Strict as Map

import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import qualified Mir as M
import MirData (writeProgram)
import Native (buildExecutable)
import Pipeline (ownedSource)
import PreludeSource (emitterSource, listsSource, preludeSource, seedSha256, stringSource)
import Utils

-- The lowering to LLVM IR that is written in Tersus (examples/emit.tersus, step 31 and STEP31.md) is the compiler's only emitter. An executable of it reads the MIR of a
-- program as data (MirData) and writes its LLVM IR; `tersus build`, `llvm` and `run` use it. It is a
-- program of the language that needs a compiler, so it is made in stages from a seed:
-- - the seed is the IR of an emitter. It is the IR that the emitter wrote for its own source when the seed was made, and
--   it does not have to be the latest: it only has to be able to compile the emitter as it is now, which it can as long as the data it reads and the runtime it calls
--   are the same. The seed itself is not kept in the repository: it is a GitHub release asset (`seedUrl`), and the repository keeps only its SHA-256
--   (bootstrap/emitter.sha256, embedded by `PreludeSource` as `seedSha256`). It is fetched once, verified against that pin, and kept in the cache
--   directory of the user. A seed at $TERSUS_SEED_FILE, or a bootstrap/emitter.ll in the working tree, is used instead when present (and also verified),
--   which is how a machine with no network keeps working;
-- - stage 0 is the seed built with clang (`stageZero`);
-- - stage 1 is the emitter as it is now, built from the IR that stage 0 writes for its source (`stageOne`). This is the one that compiles programs;
-- - and the fixpoint is that stage 1 writes for the emitter the same IR as stage 0 did, so that stage 2 would be stage 1 again (the tests check it). Making a new seed is
--   `tersus llvm examples/emit.tersus > emitter.ll.new`, then `sha256sum emitter.ll.new`, upload it as the asset `emitter.ll` of a new release tagged
--   `bootstrap-<first 12 digits of that digest>`, and put the digest in bootstrap/emitter.sha256. Never redirect straight into a seed file that the
--   running compiler is using: the shell truncates it before the compiler runs.
-- Both are built when they are first needed and kept in the cache directory of the user, so that building this package needs no clang and no network.

-- The release the seed is fetched from: one release per seed, tagged for the seed it holds, so a release is never reused for a different seed
seedUrl :: String
seedUrl = "https://github.com/weirdev/tersus/releases/download/bootstrap-" ++ take 12 seedSha256 ++ "/emitter.ll"

-- What stage 0 is made of: the seed and the runtime it is linked with
seedHash :: String
seedHash = fingerprint [seedSha256, runtimeSource]

-- What stage 1 is made of: stage 0, the emitter, and the library every program has
emitterHash :: String
emitterHash = fingerprint [seedHash, emitterSource, preludeSource, listsSource, stringSource]

-- Stage 0: the seed built, at the path
stageZero :: FilePath -> IO (Result () String)
stageZero output = do
    seed <- seedText
    case seed of
        Error e -> pure (Error e)
        Ok text -> buildExecutable output text

seedText :: IO (Result String String)
seedText = do
    override <- lookupEnv "TERSUS_SEED_FILE"
    case override of
        Just path -> verifiedText path
        Nothing -> do
            local <- firstExisting ["bootstrap" </> "emitter.ll", "tersus" </> "bootstrap" </> "emitter.ll"]
            case local of
                Just path -> verifiedText path
                Nothing -> cachedText
  where
    firstExisting [] = pure Nothing
    firstExisting (path : rest) = do
        present <- doesFileExist path
        if present then pure (Just path) else firstExisting rest
    cachedText = do
        cache <- cacheDirectory
        case cache of
            Error e -> pure (Error e)
            Ok dir -> do
                let path = dir </> ("seed-" ++ seedHash ++ ".ll")
                present <- doesFileExist path
                if present
                    then verifiedText path
                    else do
                        fetched <- downloadSeed dir path
                        case fetched of
                            Error e -> pure (Error e)
                            Ok () -> verifiedText path

downloadSeed :: FilePath -> FilePath -> IO (Result () String)
downloadSeed dir path = do
    (partial, handle) <- openTempFile dir "seed.ll.tmp"
    hClose handle
    outcome <- try (readProcessWithExitCode "curl" ["-fsSL", "-o", partial, seedUrl] "") :: IO (Either IOException (ExitCode, String, String))
    case outcome of
        Left e -> removeQuietly partial >> pure (Error ("Could not run curl to fetch the bootstrap seed from " ++ seedUrl ++ ": " ++ show e ++ ". Install curl, or set TERSUS_SEED_FILE to a seed file."))
        Right (ExitFailure _, _, err) -> removeQuietly partial >> pure (Error ("Could not fetch the bootstrap seed from " ++ seedUrl ++ ": " ++ err ++ "Set TERSUS_SEED_FILE to a seed file to work without a network."))
        Right (ExitSuccess, _, _) -> do
            verified <- verifyFile partial
            case verified of
                Error e -> removeQuietly partial >> pure (Error e)
                Ok () -> renameFile partial path >> pure (Ok ())

verifiedText :: FilePath -> IO (Result String String)
verifiedText path = do
    verified <- verifyFile path
    case verified of
        Error e -> pure (Error e)
        Ok () -> do
            read' <- try (readBytes path) :: IO (Either IOException String)
            pure $ case read' of
                Left e -> Error ("Could not read the bootstrap seed " ++ path ++ ": " ++ show e)
                Right text -> Ok text
  where
    readBytes p = do
        handle <- openFile p ReadMode
        hSetEncoding handle char8
        contents <- hGetContents handle
        _ <- evaluate (length contents)
        hClose handle
        pure contents

verifyFile :: FilePath -> IO (Result () String)
verifyFile path = do
    outcome <- try (readProcessWithExitCode "sha256sum" [path] "") :: IO (Either IOException (ExitCode, String, String))
    bySum <- case outcome of
        Right (ExitSuccess, out, _) -> pure (Just out)
        _ -> do
            fallback <- try (readProcessWithExitCode "shasum" ["-a", "256", path] "") :: IO (Either IOException (ExitCode, String, String))
            pure $ case fallback of
                Right (ExitSuccess, out, _) -> Just out
                _ -> Nothing
    pure $ case bySum of
        Nothing -> Error ("Could not run sha256sum or shasum to verify the bootstrap seed " ++ path ++ ".")
        Just out
            | takeWhile (/= ' ') out == seedSha256 && length seedSha256 == 64 && all isHexDigit seedSha256 -> Ok ()
            | otherwise -> Error ("The bootstrap seed " ++ path ++ " does not match bootstrap/emitter.sha256 (" ++ seedSha256 ++ "): got " ++ takeWhile (/= ' ') out ++ ". Refusing to build it.")

removeQuietly :: FilePath -> IO ()
removeQuietly path = do
    _ <- try (removeFile path) :: IO (Either IOException ())
    pure ()

-- Stage 1: the emitter as it is now, built at the path from the IR that the emitter at the first path writes for it
stageOne :: FilePath -> FilePath -> IO (Result () String)
stageOne compiler output = case ownedSource emitterSource of
    Error e -> pure (Error e)
    Ok owned -> do
        ir <- emitWith compiler (writeProgram owned)
        case ir of
            Error e -> pure (Error e)
            Ok text -> buildExecutable output text

-- What the emitter at the path writes for the MIR as data: its IR, or its reason (on the standard error) for refusing the program. The bytes are read as they are.
-- The MIR goes in and the IR comes out through files, not pipes: with the non-threaded runtime a thread that feeds a pipe is never run while the process is
-- waited on, so a program fed through pipes stops both ways (a thread per pipe does not help there, and callers may run emitters at the same time either way).
emitWith :: FilePath -> String -> IO (Result String String)
emitWith exe input = do
    outcome <- try run :: IO (Either IOException (ExitCode, String, String))
    pure $ case outcome of
        Left e -> Error ("Could not run the emitter: " ++ show e)
        Right (ExitSuccess, out, _) -> Ok out
        Right (ExitFailure _, _, err) -> Error (dropWhileEnd' (== '\n') (decodeUtf8 err))
  where
    dropWhileEnd' p = reverse . dropWhile p . reverse
    run = do
        (inPath, inHandle) <- openTempFileAt "tersus-emit-in.tmp"
        (outPath, outHandle) <- openTempFileAt "tersus-emit-out.tmp"
        (errPath, errHandle) <- openTempFileAt "tersus-emit-err.tmp"
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

-- Stage 0 in the cache, built if it is not there yet
cachedSeed :: IO (Result FilePath String)
cachedSeed = cached "seed" seedHash "the seed of the emitter written in Tersus" stageZero

-- Stage 1 in the cache, built (from stage 0, which is built too if it is not there) if it is not there yet
cachedEmitter :: IO (Result FilePath String)
cachedEmitter = cached "emitter" emitterHash "the emitter written in Tersus" $ \output -> do
    zero <- cachedSeed
    case zero of
        Error e -> pure (Error e)
        Ok compiler -> stageOne compiler output

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

cached :: String -> String -> String -> (FilePath -> IO (Result () String)) -> IO (Result FilePath String)
cached kind hash what build = do
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
    Ok owned -> llvmOfOwned owned

-- The LLVM IR of a program that who owns each value has been made explicit in (the owned MIR of Pipeline), by the emitter in
-- Tersus: what `tersusLlvm` does with what `ownedSource` gives, for a caller that has the program already.
llvmOfOwned :: M.Program -> IO (Result String String)
llvmOfOwned owned = do
    exe <- cachedEmitter
    case exe of
        Error e -> pure (Error e)
        Ok path -> do
            ir <- emitWith path (writeProgram owned)
            pure (either' ir)
  where
    either' (Error e) = Error ("Native code failed: " ++ e)
    either' ok = ok
