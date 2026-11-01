-- The validator written in Tersus (lib/validation.tersus), compiled to
-- native code and run as a program: this is how every program is
-- validated. The bridge (SelfHostedMir.encode) makes the data the
-- validator checks; this module writes it in the text the validator's
-- driver (lib/validation_driver.tersus) reads, runs the compiled
-- validator on it, and reads its verdict back. The validator is compiled
-- once and kept in the cache directory under a name made of everything
-- it is made of. It is built without being validated: it is the
-- bootstrap, and its own regression test validates it like any other
-- program. The interpreted validator (SelfHostedMir.validateMirSubset)
-- remains for that test; nothing else runs it.
module ValidatorNative (validateCompiled) where

import Control.Exception (IOException, evaluate, finally, try)
import GHC.IO.Encoding (char8)
import System.Directory (doesFileExist, getTemporaryDirectory, removeFile, renameFile)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (IOMode (..), hClose, hGetContents, hPutStr, hSetEncoding, openFile, openTempFile)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (CreateProcess (..), StdStream (..), createProcess, proc, readProcessWithExitCode, waitForProcess)

import qualified Mir as M
import Hash (fingerprint)
import Libraries (parseSourceWith)
import LlvmRuntime (runtimeSource)
import MirData (writeProgram)
import MirEval (MirValue (..))
import MirGhost (eraseGhosts, withoutUninit)
import MirLists (lowerLists)
import MirLower (lowerElaborated, lowerLibrary)
import MirOwnership (expandRefWrites, insertOwnership)
import MirVerify (verifyProgram)
import Native (buildExecutable, cacheDirectory)
import PreludeSource (boxSource, emitterSource, listsSource, seedSha256, validationDriverSource, validationSource)
import SelfHostedMir (encode)
import TypeCheck (elaborate)
import Utils (Result (..), bindResult)

-- Validate a program with the compiled Tersus validator. A program the
-- bridge does not model is refused, not waved through: there is no other
-- validator to fall back to. The messages are the ones the interpreted
-- validator gives (see SelfHostedMir.validateByTersus).
validateCompiled :: M.Program -> Result () String
validateCompiled program = verifyProgram program `bindResult` \_ -> case encode program of
    Left what -> Error (unmodeledMessage what)
    Right functions -> case unsafePerformIO (runValidator functions) of
        Error e -> Error e
        Ok (0, _, _, _) -> Ok ()
        Ok (1, block, step, index) -> Error ("Could not prove: an obligation could not be proved by the Tersus validator (in " ++ functionName functions index ++ ", block " ++ show block ++ ", step " ++ show step ++ ")")
        Ok (2, block, _, index) -> Error (unmodeledMessage ("an operation in " ++ functionName functions index ++ ", block " ++ show block))
        Ok (3, _, _, index) -> Error (unmodeledMessage ("the control flow of " ++ functionName functions index))
        Ok (_, block, _, index) -> Error (unmodeledMessage ("a loop of " ++ functionName functions index ++ " at block " ++ show block))
  where
    unmodeledMessage what = "the program uses a feature the Tersus validator does not model yet: " ++ what
    functionName functions index
        | index >= 0 && index < length functions = fst (functions !! index)
        | otherwise = "the program"

-- The verdict of the compiled validator over every function the bridge
-- encoded, as (status, block, step, function index)
runValidator :: [(String, (MirValue, MirValue, Integer))] -> IO (Result (Int, Int, Int, Int) String)
runValidator functions = case serializeFunctions functions of
    Left e -> pure (Error e)
    Right input -> do
        exe <- validatorExecutable
        case exe of
            Error e -> pure (Error e)
            Ok path -> do
                outcome <- runWithFiles path input
                pure $ case outcome of
                    Error e -> Error e
                    Ok (code, out, err) -> case (code, map readInt (words (firstLine out))) of
                        (ExitSuccess, [Just status, Just block, Just step, Just index]) -> Ok (status, block, step, index)
                        _ -> Error ("the compiled validator did not answer (exit " ++ show code ++ ", output: " ++ take 200 out ++ ", error: " ++ take 200 err ++ ")")
  where
    firstLine = takeWhile (/= '\n')
    readInt text = case reads text of
        [(n, "")] -> Just n
        _ -> Nothing

-- The text the driver reads: a count, then per function the entry block,
-- the entry state and the blocks (see lib/validation_driver.tersus)
serializeFunctions :: [(String, (MirValue, MirValue, Integer))] -> Either String String
serializeFunctions functions = do
    parts <- mapM serializeFunction functions
    pure (show (length functions) ++ "\n" ++ concat parts)
  where
    serializeFunction (_, (blocks, initial, entry)) = do
        stateText <- serializeValue initial
        blocksText <- serializeValue blocks
        pure (show entry ++ "\n" ++ stateText ++ blocksText)

serializeValue :: MirValue -> Either String String
serializeValue value = case value of
    MInt n -> Right ("i " ++ show n ++ " ")
    MBool b -> Right ("b " ++ (if b then "1 " else "0 "))
    MList values -> do
        parts <- mapM serializeValue values
        Right ("l " ++ show (length values) ++ " " ++ concat parts)
    MData name fields -> do
        parts <- mapM (serializeValue . snd) fields
        Right ("d n " ++ show (length name) ++ " " ++ name ++ " " ++ show (length fields) ++ " " ++ concat parts)
    MFn name -> Left ("a function value (" ++ name ++ ") in the data for the validator")
    MEmpty -> Left "an empty value in the data for the validator"
    MRef _ _ -> Left "a reference value in the data for the validator"

-- The compiled validator, built once and kept in the cache
validatorExecutable :: IO (Result FilePath String)
validatorExecutable = cachedExecutable "validator" validatorHash buildValidator
  where
    validatorHash = fingerprint [validationSource, validationDriverSource, listsSource, boxSource, emitterSource, seedSha256, runtimeSource]

buildValidator :: FilePath -> IO (Result () String)
buildValidator output = case ownedUnvalidated (validationSource ++ "\n" ++ validationDriverSource) of
    Error e -> pure (Error ("Could not build the validator written in Tersus: " ++ e))
    Ok owned -> do
        emitter <- emitterExecutable
        case emitter of
            Error e -> pure (Error e)
            Ok exe -> do
                ir <- emitWith exe (writeProgram owned)
                case ir of
                    Error e -> pure (Error e)
                    Ok text -> buildExecutable output text

-- The emitter written in Tersus, compiled for the validator's build. It
-- is made the same way as the validator (lowered without being
-- validated): Bootstrap's emitter is made through the production
-- pipeline, which is the thing being replaced here.
emitterExecutable :: IO (Result FilePath String)
emitterExecutable = cachedExecutable "validator-emitter" hash buildEmitter
  where
    hash = fingerprint [seedSha256, emitterSource, listsSource, boxSource, runtimeSource]
    buildEmitter output = case ownedUnvalidated emitterSource of
        Error e -> pure (Error ("Could not build the emitter for the validator: " ++ e))
        Ok owned -> do
            seed <- seedExecutable
            case seed of
                Error e -> pure (Error e)
                Ok exe -> do
                    ir <- emitWith exe (writeProgram owned)
                    case ir of
                        Error e -> pure (Error e)
                        Ok text -> buildExecutable output text

-- Stage 0: the seed of the emitter, compiled
seedExecutable :: IO (Result FilePath String)
seedExecutable = cachedExecutable "validator-seed" hash buildSeed
  where
    hash = fingerprint [seedSha256, runtimeSource]
    buildSeed output = do
        seed <- seedText
        case seed of
            Error e -> pure (Error e)
            Ok text -> buildExecutable output text

-- A program in the cache, named for what it is made of, made by the
-- action if it is not there (as Bootstrap.cached does for the emitter)
cachedExecutable :: String -> String -> (FilePath -> IO (Result () String)) -> IO (Result FilePath String)
cachedExecutable kind hash build = do
    cache <- cacheDirectory
    case cache of
        Error e -> pure (Error e)
        Ok dir -> do
            let exe = dir </> (kind ++ "-" ++ hash)
            present <- doesFileExist exe
            if present
                then pure (Ok exe)
                else do
                    (partial, handle) <- openTempFile dir (kind ++ ".tmp")
                    hClose handle
                    removeFile partial
                    built <- build partial
                    case built of
                        Error e -> pure (Error e)
                        Ok () -> renameFile partial exe >> pure (Ok exe)

-- The MIR of a program with who owns each value made explicit, without
-- validating it: the stage the bootstrap programs (the validator, the
-- emitter for its build) are compiled from
ownedUnvalidated :: String -> Result M.Program String
ownedUnvalidated source =
    parseSourceWith True source `bindResult` \stmts ->
        elaborate stmts `bindResult` \elaborated ->
            lowerElaborated elaborated `bindResult` \program ->
                eraseGhosts program `bindResult` \erased ->
                    let owned = insertOwnership (lowerLists listLibrary (withoutUninit (expandRefWrites erased)))
                     in verifyProgram owned `bindResult` \_ -> Ok owned

-- The library of lists and Boxes, lowered without being validated, as
-- Pipeline.listLibrary is from the validated lowering
listLibrary :: M.Program
listLibrary = case parseSourceWith False (listsSource ++ "\n" ++ boxSource) `bindResult` \stmts ->
    elaborate stmts `bindResult` \elaborated ->
        lowerLibrary elaborated `bindResult` eraseGhosts of
    Ok program -> program
    Error e -> error ("lib/lists.tersus and lib/box.tersus do not lower: " ++ e)

-- The seed of the emitter: $TERSUS_SEED_FILE, a bootstrap/emitter.ll in
-- the working tree, the cache, or fetched from its release (as
-- Bootstrap.seedText finds it), verified against the pinned digest
seedText :: IO (Result String String)
seedText = do
    override <- lookupEnv "TERSUS_SEED_FILE"
    case override of
        Just path -> verifiedText path
        Nothing -> do
            local <- firstExisting ["bootstrap" </> "emitter.ll", "tersus" </> "bootstrap" </> "emitter.ll"]
            case local of
                Just path -> verifiedText path
                Nothing -> cachedSeedText
  where
    firstExisting [] = pure Nothing
    firstExisting (path : rest) = do
        present <- doesFileExist path
        if present then pure (Just path) else firstExisting rest
    cachedSeedText = do
        cache <- cacheDirectory
        case cache of
            Error e -> pure (Error e)
            Ok dir -> do
                let path = dir </> ("seed-" ++ fingerprint [seedSha256, runtimeSource] ++ ".ll")
                present <- doesFileExist path
                if present
                    then verifiedText path
                    else do
                        fetched <- downloadSeed dir path
                        case fetched of
                            Error e -> pure (Error e)
                            Ok () -> verifiedText path

seedUrl :: String
seedUrl = "https://github.com/weirdev/tersus/releases/download/bootstrap-" ++ take 12 seedSha256 ++ "/emitter.ll"

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
    pure $ case outcome of
        Left e -> Error ("Could not run sha256sum to verify the bootstrap seed: " ++ show e)
        Right (ExitFailure _, _, err) -> Error ("Could not verify the bootstrap seed " ++ path ++ ": " ++ err)
        Right (ExitSuccess, out, _) -> case words out of
            (digest : _) | digest == seedSha256 -> Ok ()
            _ -> Error ("The bootstrap seed " ++ path ++ " does not match the digest pinned in bootstrap/emitter.sha256")

removeQuietly :: FilePath -> IO ()
removeQuietly path = do
    _ <- try (removeFile path) :: IO (Either IOException ())
    pure ()

-- Run a program with the input and output through files (as
-- Bootstrap.emitWith does: a thread feeding a pipe is never run while
-- the process is waited on with the non-threaded runtime)
runWithFiles :: FilePath -> String -> IO (Result (ExitCode, String, String) String)
runWithFiles exe input = do
    outcome <- try run :: IO (Either IOException (ExitCode, String, String))
    pure $ case outcome of
        Left e -> Error ("Could not run the compiled validator: " ++ show e)
        Right ok -> Ok ok
  where
    run = do
        tmp <- getTemporaryDirectory
        (inPath, inHandle) <- openTempFile tmp "tersus-validator-in.tmp"
        (outPath, outHandle) <- openTempFile tmp "tersus-validator-out.tmp"
        (errPath, errHandle) <- openTempFile tmp "tersus-validator-err.tmp"
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
    readBytes path = do
        handle <- openFile path ReadMode
        hSetEncoding handle char8
        contents <- hGetContents handle
        _ <- length contents `seq` pure ()
        hClose handle
        pure contents

-- What the emitter at the path writes for the MIR as data (as
-- Bootstrap.emitWith)
emitWith :: FilePath -> String -> IO (Result String String)
emitWith exe input = do
    outcome <- try run :: IO (Either IOException (ExitCode, String, String))
    pure $ case outcome of
        Left e -> Error ("Could not run the emitter: " ++ show e)
        Right (ExitSuccess, out, _) -> Ok out
        Right (ExitFailure _, _, err) -> Error ("the emitter refused the program: " ++ dropWhileEnd (== '\n') err)
  where
    dropWhileEnd p = reverse . dropWhile p . reverse
    run = do
        tmp <- getTemporaryDirectory
        (inPath, inHandle) <- openTempFile tmp "tersus-emit-in.tmp"
        (outPath, outHandle) <- openTempFile tmp "tersus-emit-out.tmp"
        (errPath, errHandle) <- openTempFile tmp "tersus-emit-err.tmp"
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
    readBytes path = do
        handle <- openFile path ReadMode
        hSetEncoding handle char8
        contents <- hGetContents handle
        _ <- length contents `seq` pure ()
        hClose handle
        pure contents
