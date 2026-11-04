-- The validator written in Tersus (lib/validation.tersus), compiled to
-- native code and run as a program: this is how every program is
-- validated. The bridge (SelfHostedMir.encode) makes the data the
-- validator checks; this module writes it in the text the validator's
-- driver (lib/validation_driver.tersus) reads, runs the compiled
-- validator on it, and reads its verdict back. The validator is built as
-- MirHousekeeping builds the checker and the eraser (by the emitter in the
-- cache) and kept in the cache under a name made of everything it is made
-- of. It is built without being validated: it is the bootstrap, and its
-- own regression test validates it like any other program. The
-- interpreted validator (SelfHostedMir.validateMirSubset) remains for
-- that test; nothing else runs it.
module ValidatorNative (validateCompiled, validateCompiledUncached, validateLibrary, validationCacheHits, withVerdictLock) where

import Control.Concurrent.MVar (withMVar)
import Control.Exception (IOException, bracket, try)
import Control.Monad (when)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import System.Directory (copyFile, createDirectoryIfMissing, doesFileExist, renameFile)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import GHC.IO.Handle.Lock (LockMode (..), hLock)
import System.IO (IOMode (..), hClose, hPutStr, openFile, openTempFile)
import System.IO.Unsafe (unsafePerformIO)

import qualified Mir as M
import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import MirData (writeProgram)
import MirEval (MirValue (..))
import MirHousekeeping (cachedEmitter, nativeStorage, ownedProgramOf)
import Native (buildExecutable, cacheDirectory, cacheLock, cachedProgram, runCommandWithInputFull, runWithInput)
import PreludeSource (boxSource, listsSource, validationDriverSource, validationSource)
import Seed (emitterHash)
import SelfHostedMir (encode, encodeLibrary, obligationNote)
import Syntax (parseImplCheckName)
import Utils (Result (..))

-- Validate a program (one the MIR checker has accepted) with the compiled
-- Tersus validator. A program the bridge does not model is refused, not
-- waved through: there is no other validator to fall back to. The
-- messages are the ones the interpreted validator gives (see
-- SelfHostedMir.validateByTersus).
--
-- The verdict on a function is a function of the data the bridge makes
-- of it alone (that data holds the contracts of what it calls, the
-- invariants of the types it makes and the rules it uses), so a verdict
-- is kept for the rest of the process under that data, and a function
-- met again (a library's, in the next program) is not checked again.
validateCompiled :: M.Program -> Result () String
validateCompiled = validateWith False True

-- The same, with every function checked, for the tests of the cache
validateCompiledUncached :: M.Program -> Result () String
validateCompiledUncached = validateWith False False

-- The native storage library (lib/lists.tersus and lib/box.tersus, linked),
-- with a List and a Box as the structs they are (SelfHostedMir.encodeLibrary)
validateLibrary :: M.Program -> Result () String
validateLibrary = validateWith True True

validateWith :: Bool -> Bool -> M.Program -> Result () String
validateWith physical caching program = unsafePerformIO (validateWithExe validatorExecutable physical caching program)

-- The same, run by the validator the first argument gives
validateWithExe :: IO (Result FilePath String) -> Bool -> Bool -> M.Program -> IO (Result () String)
validateWithExe exe physical caching program = case (if physical then encodeLibrary else encode) program of
    Left what -> pure (Error (unmodeledMessage what))
    Right functions -> case mapM (\(name, f) -> fmap (\text -> (name, text)) (serializeFunction f)) functions of
        Left e -> pure (Error e)
        Right texts -> do
            checked <- verdicts exe caching (map snd texts)
            pure $ case checked of
                Error e -> Error e
                Ok results -> case [(index, verdict) | (index, Just verdict@(status, _, _)) <- zip [0 ..] results, status /= 0] of
                    [] -> Ok ()
                    (index, (status, block, step)) : _ -> Error (message (fst (texts !! index)) status block step)
  where
    unmodeledMessage what = "the program uses a feature the Tersus validator does not model yet: " ++ what
    message name status block step = case status of
        1 -> case (obligationNote physical program name block step, parseImplCheckName name) of
            (Just note, Just (trait, owner, function)) -> "impl " ++ trait ++ " for " ++ owner ++ ": " ++ function ++ " does not meet what " ++ trait ++ " declares: could not prove " ++ note
            (Just note, Nothing) -> "Could not prove: " ++ note ++ " (in " ++ name ++ ")"
            _ -> "Could not prove: an obligation could not be proved by the Tersus validator (in " ++ name ++ ", block " ++ show block ++ ", step " ++ show step ++ ")"
        2 -> unmodeledMessage ("an operation in " ++ name ++ ", block " ++ show block)
        3 -> unmodeledMessage ("the control flow of " ++ name)
        _ -> unmodeledMessage ("a loop of " ++ name ++ " at block " ++ show block)

-- The verdicts already known, by the text of a function's data, and how
-- many times one has been used
{-# NOINLINE verdictCache #-}
verdictCache :: IORef (Map.Map String (Int, Int, Int))
verdictCache = unsafePerformIO (newIORef Map.empty)

{-# NOINLINE cacheHitCount #-}
cacheHitCount :: IORef Int
cacheHitCount = unsafePerformIO (newIORef 0)

validationCacheHits :: IO Int
validationCacheHits = readIORef cacheHitCount

-- The verdict on each function, in order, as far as the first that fails:
-- the validator checks the functions in order and stops at the first it
-- refuses, so a function after it has none (Nothing), and is never
-- reached when the verdicts are read in order
verdicts :: IO (Result FilePath String) -> Bool -> [String] -> IO (Result [Maybe (Int, Int, Int)] String)
verdicts exe caching texts = do
    inMemory <- if caching then readIORef verdictCache else pure Map.empty
    onDisk <- if caching then fmap (Map.fromList . concat) (mapM (\text -> maybe [] (\v -> [(text, v)]) <$> diskVerdict text) [text | text <- nub texts, Map.notMember text inMemory]) else pure Map.empty
    _ <- atomicModifyIORef' verdictCache (\cache -> (Map.union cache onDisk, ()))
    let known = Map.union inMemory onDisk
        missing = [(index, text) | (index, text) <- zip [0 :: Int ..] texts, Map.notMember text known]
        hits = length texts - length missing
    _ <- atomicModifyIORef' cacheHitCount (\n -> (n + hits, ()))
    checked <- if null missing then pure (Ok Map.empty) else if caching then oneAtATime exe (map snd missing) Map.empty else runValidator exe (map snd missing)
    case checked of
        Error e -> pure (Error e)
        Ok found -> do
            let fresh = Map.fromList [(index, verdict) | (position, (index, _)) <- zip [0 ..] missing, Just verdict <- [Map.lookup position found]]
            _ <- atomicModifyIORef' verdictCache (\cache -> (Map.union cache (Map.fromList [(texts !! index, verdict) | (index, verdict) <- Map.toList fresh]), ()))
            when caching $ mapM_ (\(index, verdict) -> storeVerdict (texts !! index) verdict) (Map.toList fresh)
            pure (Ok [if Map.member text known then Map.lookup text known else Map.lookup index fresh | (index, text) <- zip [0 ..] texts])

-- The functions not known yet, checked one at a time in order, as far as
-- the first refused, each under a lock of its own: a process that asks for
-- a function another process is checking waits for that verdict instead of
-- checking it too (the groups of the tests start together, and share most
-- of the libraries' functions)
oneAtATime :: IO (Result FilePath String) -> [String] -> Map.Map Int (Int, Int, Int) -> IO (Result (Map.Map Int (Int, Int, Int)) String)
oneAtATime _ [] found = pure (Ok found)
oneAtATime exe (text : rest) found = do
    verdict <- withVerdictLock text $ do
        stored <- diskVerdict text
        case stored of
            Just v -> pure (Ok v)
            Nothing -> do
                checked <- runValidator exe [text]
                case checked of
                    Error e -> pure (Error e)
                    Ok answers -> do
                        let v = Map.findWithDefault (0, -1, -1) 0 answers
                        storeVerdict text v
                        pure (Ok v)
    case verdict of
        Error e -> pure (Error e)
        Ok v@(status, _, _) ->
            let found' = Map.insert (Map.size found) v found
             in if status /= 0 then pure (Ok found') else oneAtATime exe rest found'

withVerdictLock :: String -> IO a -> IO a
withVerdictLock text action = do
    file <- verdictFile text
    case file of
        Nothing -> action
        Just path -> do
            createDirectoryIfMissing True (takeDirectory path)
            -- (the threads of one process take turns first: a process may not open one file for writing twice, and
            -- the second open fails instead of waiting)
            lock <- cacheLock ("verdict " ++ path)
            withMVar lock $ \_ ->
                bracket (openFile (path ++ ".lock") ReadWriteMode) hClose (\handle -> hLock handle ExclusiveLock >> action)

-- The compiled validator's verdicts over the functions given: each one up
-- to the first refused is proved, the refused one has its own
runValidator :: IO (Result FilePath String) -> [String] -> IO (Result (Map.Map Int (Int, Int, Int)) String)
runValidator validator texts = do
    exe <- validator
    case exe of
        Error e -> pure (Error e)
        Ok path -> do
            -- (the checker recurses over the facts it holds, deeper than a default
            -- stack of 8 MB for a large function, so the limit is raised first)
            (code, out, err) <- runCommandWithInputFull "/bin/sh" ["-c", raiseStack, path] (show (length texts) ++ "\n" ++ concat texts)
            pure $ case (code, map readInt (words (takeWhile (/= '\n') out))) of
                (ExitSuccess, [Just 0, _, _, _]) -> Ok (Map.fromList [(i, (0, -1, -1)) | i <- [0 .. length texts - 1]])
                (ExitSuccess, [Just status, Just block, Just step, Just index]) ->
                    Ok (Map.fromList ([(i, (0, -1, -1)) | i <- [0 .. index - 1]] ++ [(index, (status, block, step))]))
                _ -> Error ("the compiled validator did not answer (exit " ++ show code ++ ", output: " ++ take 200 out ++ ", error: " ++ take 200 err ++ ")")
  where
    readInt text = case reads text of
        [(n, "")] -> Just n
        _ -> Nothing

-- The text the driver reads of one function: its entry block, its entry
-- state and its blocks; the driver reads a count of them first (see
-- lib/validation_driver.tersus)
serializeFunction :: (MirValue, MirValue, Integer) -> Either String String
serializeFunction (blocks, initial, entry) = do
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

-- The compiled validator in the cache. It is built from its source without
-- being validated (no validator is there yet: uncheckedValidator), and then
-- it validates what it is made of, the native storage library its lists and
-- Boxes are built with; only a validator that has done so is used.
validatorExecutable :: IO (Result FilePath String)
validatorExecutable = cachedProgram "validator" validatorHash "the validator written in Tersus, checked" $ \output -> do
    unchecked <- uncheckedValidator
    case unchecked of
        Error e -> pure (Error e)
        Ok exe -> do
            checked <- selfCheck (pure (Ok exe))
            case checked of
                Error e -> pure (Error ("the validator written in Tersus does not validate " ++ e))
                Ok () -> copyFile exe output >> pure (Ok ())

-- What the validator validates of itself, run by the validator given
selfCheck :: IO (Result FilePath String) -> IO (Result () String)
selfCheck exe = case nativeStorage of
    Error e -> pure (Error ("the native storage library: " ++ e))
    Ok (_, library) -> do
        -- (not through the shared verdicts: a process that holds the lock of a
        -- function waits for this validator, so this build must not wait for it)
        checked <- validateWithExe exe True False library
        pure (either (\e -> Error ("the native storage library: " ++ e)) Ok (resultEither checked))
  where
    resultEither (Ok a) = Right a
    resultEither (Error e) = Left e

-- The validator built by the emitter in the cache from the validator and its
-- driver, not yet validated
uncheckedValidator :: IO (Result FilePath String)
uncheckedValidator = cachedProgram "validator-unchecked" validatorHash "the validator written in Tersus" $ \output -> do
    emitter <- cachedEmitter
    case emitter of
        Error e -> pure (Error e)
        Ok exe -> case ownedProgramOf (validationSource ++ "\n" ++ validationDriverSource) of
            Error e -> pure (Error ("the validator written in Tersus does not compile: " ++ e))
            Ok program -> do
                ir <- runWithInput exe (writeProgram program)
                case ir of
                    Error e -> pure (Error e)
                    Ok text -> buildExecutable output text

validatorHash :: String
validatorHash = fingerprint [emitterHash, validationSource, validationDriverSource, listsSource, boxSource, runtimeSource]

-- Run $0 with the largest stack the system allows (macOS caps it at 64 MB)
raiseStack :: String
raiseStack = "ulimit -s unlimited 2>/dev/null || ulimit -s 65532 2>/dev/null; exec \"$0\""

-- The verdicts are kept on disk too, so that each function is validated once
-- for a build of the validator however many processes ask: a file per
-- function under the validator's hash, named by a fingerprint of the
-- function's data and holding that data in full, so a verdict is used only
-- for the very data it was given (a fingerprint that collides is a miss).
verdictFile :: String -> IO (Maybe FilePath)
verdictFile text = do
    cache <- cacheDirectory
    pure $ case cache of
        Ok dir -> Just (dir </> ("verdicts-" ++ validatorHash) </> fingerprint [text])
        Error _ -> Nothing

diskVerdict :: String -> IO (Maybe (Int, Int, Int))
diskVerdict text = do
    file <- verdictFile text
    case file of
        Nothing -> pure Nothing
        Just path -> do
            present <- doesFileExist path
            if not present
                then pure Nothing
                else do
                    contents <- try (readFileStrict path) :: IO (Either IOException String)
                    pure $ case contents of
                        Right body -> case break (== '\n') body of
                            (header, '\n' : stored) | stored == text -> case map reads (words header) of
                                [[(status, "")], [(block, "")], [(step, "")]] -> Just (status, block, step)
                                _ -> Nothing
                            _ -> Nothing
                        Left _ -> Nothing
  where
    readFileStrict path = do
        body <- readFile path
        length body `seq` pure body

storeVerdict :: String -> (Int, Int, Int) -> IO ()
storeVerdict text (status, block, step) = do
    file <- verdictFile text
    case file of
        Nothing -> pure ()
        Just path -> do
            let dir = takeDirectory path
            outcome <- try (do
                createDirectoryIfMissing True dir
                (temporary, handle) <- openTempFile dir "verdict.tmp"
                hPutStr handle (unwords (map show [status, block, step]) ++ "\n" ++ text)
                hClose handle
                renameFile temporary path) :: IO (Either IOException ())
            pure (either (const ()) id outcome)
