-- The validator written in Tersus (lib/validation/validation.tersus), compiled to
-- native code and run as a program: this is how every program is
-- validated. The bridge (SelfHostedMir.encode) makes the data the
-- validator checks; this module writes it in the text the validator's
-- driver (lib/validation/driver.tersus) reads, runs the compiled
-- validator on it, and reads its verdict back. The validator is built as
-- MirHousekeeping builds the checker and the eraser (by the emitter in the
-- cache) and kept in the cache under a name made of everything it is made
-- of. It is built without being validated: it is the bootstrap, and it is
-- used only once it has validated its own source and the native storage
-- library it is built with. The
-- interpreted validator (SelfHostedMir.validateMirSubset) remains for
-- that test; nothing else runs it.
module ValidatorNative (validateCompiled, validateCompiledUncached, validationRefusals, validateLibrary, validationCacheHits, withVerdictLock, cachedBootstrapEmitter, validatorKey, certificateKey, prepareTexts, raiseStack) where

import Control.Concurrent.MVar (MVar, modifyMVar, modifyMVar_, newMVar, takeMVar, withMVar)
import Data.List (sortOn)
import Data.Char (isSpace)
import Data.Ord (Down (..))
import Control.Exception (IOException, bracket, evaluate, try)
import Control.Monad (when)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
import System.Directory (createDirectoryIfMissing, doesFileExist, renameFile)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import GHC.IO.Handle.Lock (LockMode (..), hLock)
import System.IO (hClose, hPutStr)
import System.IO.Unsafe (unsafePerformIO)

import qualified Mir as M
import CacheLock (copyFileCloexec, openLockHandle, openTempFileCloexec)
import Hash (fingerprint)
import MirEval (MirValue (..))
import MirHousekeeping (cachedEmitter, cachedUncheckedValidator, nativeStorage, prepareBootstrap, prepareValidator, cachedPreparedInput, cachedContentKey, emitterEntry)
import Native (cacheDirectory, cacheLock, cachedProgram, cachedProgramIfPresent, availableProcessors, parallelBuilds, runCommandWithInputFull, raiseStack)
import SelfHostedMir (encode, encodeLibrary, obligationNote)
import Syntax (parseImplCheckName)
import Utils (Result (..), mapResult)

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
prepareTexts :: Bool -> M.Program -> Result [(String, String)] String
prepareTexts physical program = case (if physical then encodeLibrary else encode) program of
    Left what -> Error ("the program uses a feature the Tersus validator does not model yet: " ++ what)
    Right functions -> case mapM (\(name, f) -> fmap (\text -> (name, text)) (serializeFunction f)) functions of
        Left e -> Error e
        Right texts -> Ok texts

validateWithExe :: IO (Result FilePath String) -> Bool -> Bool -> M.Program -> IO (Result () String)
validateWithExe exe physical caching program = case prepareTexts physical program of
    Error e -> pure (Error e)
    Ok texts -> validateTexts exe physical caching program texts

validateTexts :: IO (Result FilePath String) -> Bool -> Bool -> M.Program -> [(String, String)] -> IO (Result () String)
validateTexts exe physical caching program texts = do
    checked <- verdicts exe caching (map snd texts)
    pure $ case checked of
        Error e -> Error e
        Ok results -> case [(index, verdict) | (index, Just verdict@(status, _, _)) <- zip [0 ..] results, status /= 0] of
            [] -> Ok ()
            (index, verdict) : _ -> Error (refusalMessage physical program (fst (texts !! index)) verdict)

refusalMessage :: Bool -> M.Program -> String -> (Int, Int, Int) -> String
refusalMessage physical program name (status, block, step) = case status of
    1 -> case (obligationNote physical program name block step, parseImplCheckName name) of
        (Just note, Just (trait, owner, function)) -> "impl " ++ trait ++ " for " ++ owner ++ ": " ++ function ++ " does not meet what " ++ trait ++ " declares: could not prove " ++ note
        (Just note, Nothing) -> "Could not prove: " ++ note ++ " (in " ++ name ++ ")"
        _ -> "Could not prove: an obligation could not be proved by the Tersus validator (in " ++ name ++ ", block " ++ show block ++ ", step " ++ show step ++ ")"
    2 -> unmodeledMessage ("an operation in " ++ name ++ ", block " ++ show block)
    3 -> unmodeledMessage ("the control flow of " ++ name)
    _ -> unmodeledMessage ("a loop of " ++ name ++ " at block " ++ show block)
  where
    unmodeledMessage what = "the program uses a feature the Tersus validator does not model yet: " ++ what

-- Every function of a program checked, not only those before the first refused (as validateCompiled checks them),
-- with the verdicts validateCompiled keeps on disk: what each function refused, or that the validator could not
-- check it, in the program's order
validationRefusals :: M.Program -> IO (Result [String] String)
validationRefusals program = case prepareTexts False program of
    Error e -> pure (Error e)
    Ok texts -> do
        namespace <- validatorKey
        built <- validatorExecutable
        case (namespace, built) of
            (Error e, _) -> pure (Error e)
            (_, Error e) -> pure (Error e)
            (Ok key, Ok exe) -> do
                let distinct = Map.keys (Map.fromList [(text, ()) | (_, text) <- texts])
                checked <- inParallel (storedOrChecked key (pure (Ok exe))) distinct
                let byText = Map.fromList (zip distinct checked)
                pure (Ok [message | (name, text) <- texts, Just outcome <- [Map.lookup text byText], Just message <- [failure name outcome]])
  where
    failure name (Error e) = Just ("the compiled validator could not check " ++ name ++ ": " ++ e)
    failure name (Ok verdict@(status, _, _))
        | status /= 0 = Just (refusalMessage False program name verdict)
        | otherwise = Nothing

-- The verdicts already known, by the text of a function's data, and how
-- many times one has been used
{-# NOINLINE verdictCache #-}
verdictCache :: IORef (Map.Map String (Map.Map String (Int, Int, Int)))
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
verdicts exe False texts = do
    checked <- inParallel (checkOne exe) texts
    pure $ case [e | Error e <- checked] of
        e : _ -> Error e
        [] -> Ok [Just verdict | Ok verdict <- checked]
verdicts exe True texts = do
    namespace <- validatorKey
    case namespace of
        Error e -> pure (Error e)
        Ok key -> cachedVerdicts key exe texts

cachedVerdicts :: String -> IO (Result FilePath String) -> [String] -> IO (Result [Maybe (Int, Int, Int)] String)
cachedVerdicts namespace exe texts = do
    allKnown <- readIORef verdictCache
    let inMemory = Map.findWithDefault Map.empty namespace allKnown
        textByIndex = Map.fromList (zip [0 :: Int ..] texts)
        unknownTexts = Map.fromList [(text, ()) | text <- texts, Map.notMember text inMemory]
    onDisk <- fmap (Map.fromList . concat) (mapM (\text -> maybe [] (\v -> [(text, v)]) <$> diskVerdict namespace text) (Map.keys unknownTexts))
    _ <- atomicModifyIORef' verdictCache (\cache -> (Map.insertWith Map.union namespace onDisk cache, ()))
    let known = Map.union inMemory onDisk
        missing = [(index, text) | (index, text) <- zip [0 :: Int ..] texts, Map.notMember text known]
        hits = length texts - length missing
    _ <- atomicModifyIORef' cacheHitCount (\n -> (n + hits, ()))
    checked <- if null missing then pure (Ok Map.empty) else oneAtATime namespace exe (map snd missing) Map.empty
    case checked of
        Error e -> pure (Error e)
        Ok found -> do
            let fresh = Map.fromList [(index, verdict) | (position, (index, _)) <- zip [0 ..] missing, Just verdict <- [Map.lookup position found]]
                freshByText = Map.foldlWithKey' (\byText index verdict -> Map.insertWith (\_new existing -> existing) (textByIndex Map.! index) verdict byText) Map.empty fresh
            _ <- atomicModifyIORef' verdictCache (\cache -> (Map.insertWith Map.union namespace freshByText cache, ()))
            mapM_ (\(text, verdict) -> storeVerdict namespace text verdict) (Map.toList freshByText)
            pure (Ok [if Map.member text known then Map.lookup text known else Map.lookup index fresh | (index, text) <- zip [0 ..] texts])

-- The functions not known yet, checked one at a time in order, as far as
-- the first refused, each under a lock of its own: a process that asks for
-- a function another process is checking waits for that verdict instead of
-- checking it too (the groups of the tests start together, and share most
-- of the libraries' functions)
oneAtATime :: String -> IO (Result FilePath String) -> [String] -> Map.Map Int (Int, Int, Int) -> IO (Result (Map.Map Int (Int, Int, Int)) String)
oneAtATime _ _ [] found = pure (Ok found)
oneAtATime namespace exe (text : rest) found = do
    verdict <- storedOrChecked namespace exe text
    case verdict of
        Error e -> pure (Error e)
        Ok v@(status, _, _) ->
            let found' = Map.insert (Map.size found) v found
             in if status /= 0 then pure (Ok found') else oneAtATime namespace exe rest found'

storedOrChecked :: String -> IO (Result FilePath String) -> String -> IO (Result (Int, Int, Int) String)
storedOrChecked namespace exe text = withVerdictLock namespace text $ do
    stored <- diskVerdict namespace text
    case stored of
        Just v -> pure (Ok v)
        Nothing -> do
            checked <- checkOne exe text
            case checked of
                Error e -> pure (Error e)
                Ok v -> storeVerdict namespace text v >> pure (Ok v)

withVerdictLock :: String -> String -> IO a -> IO a
withVerdictLock namespace text action = do
    file <- verdictFile namespace text
    case file of
        Nothing -> action
        Just path -> do
            createDirectoryIfMissing True (takeDirectory path)
            -- (the threads of one process take turns first: a process may not open one file for writing twice, and
            -- the second open fails instead of waiting)
            lock <- cacheLock ("verdict " ++ path)
            withMVar lock $ \_ ->
                bracket (openLockHandle (path ++ ".lock")) hClose (\handle -> hLock handle ExclusiveLock >> action)

-- Each text checked, as many at once as the machine has processors, the longest first
inParallel :: (String -> IO (Result a String)) -> [String] -> IO [Result a String]
inParallel check texts = do
    workers <- availableProcessors
    queue <- newMVar (sortOn (Down . length . snd) (zip [0 :: Int ..] texts))
    found <- newMVar Map.empty
    let next = modifyMVar queue (\pending -> pure (drop 1 pending, take 1 pending))
        worker = do
            item <- next
            case item of
                [] -> pure ()
                (index, text) : _ -> do
                    checked <- check text
                    modifyMVar_ found (pure . Map.insert index checked)
                    worker
    _ <- parallelBuilds (replicate (max 1 workers) worker)
    Map.elems <$> takeMVar found

checkOne :: IO (Result FilePath String) -> String -> IO (Result (Int, Int, Int) String)
checkOne exe text = do
    checked <- runValidator exe [text]
    pure $ case checked of
        Error e -> Error e
        Ok answers -> maybe (Error "the compiled validator gave no verdict") Ok (Map.lookup 0 answers)

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
                (ExitSuccess, [Just status, Just block, Just step, Just index]) | index >= 0 && index < length texts ->
                    Ok (Map.fromList ([(i, (0, -1, -1)) | i <- [0 .. index - 1]] ++ [(index, (status, block, step))]))
                _ -> Error ("the compiled validator did not answer (exit " ++ show code ++ ", output: " ++ take 200 out ++ ", error: " ++ take 200 err ++ ")")
  where
    readInt text = case reads text of
        [(n, "")] -> Just n
        _ -> Nothing

-- The text the driver reads of one function: its entry block, its entry
-- state and its blocks; the driver reads a count of them first (see
-- lib/validation/driver.tersus)
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

-- Overlap full validator self-validation with the other post-E1 tool builds.
cachedBootstrapEmitter :: IO (Result FilePath String)
cachedBootstrapEmitter = do
    prepared <- prepareBootstrap
    case prepared of
        Error e -> pure (Error e)
        Ok () -> do
            results <- parallelBuilds [cachedEmitter, validatorExecutable]
            pure $ case results of
                [Ok emitter, Ok _] -> Ok emitter
                [Error e, _] -> Error e
                [_, Error e] -> Error e
                _ -> Error "incomplete checked bootstrap"

-- The compiled validator in the cache. It is built from its source without
-- being validated (no validator is there yet: uncheckedValidator), and then
-- it validates what it is made of: the native storage library its lists and
-- Boxes are built with, and its own source; only a validator that has done
-- so is used.
type PreparedCertificate = (String, M.Program, [(String, String)], M.Program, [(String, String)])

{-# NOINLINE certificateCache #-}
certificateCache :: MVar (Maybe PreparedCertificate)
certificateCache = unsafePerformIO (newMVar Nothing)

certificateKey :: String -> [String] -> [String] -> String
certificateKey unchecked library own = fingerprint [show
    (unchecked, map ("1\n" ++) library, map ("1\n" ++) own)]

prepareCertificate :: IO (Result PreparedCertificate String)
prepareCertificate = do
    prepared <- prepareValidator
    case prepared of
        Error e -> pure (Error e)
        Ok (unchecked, own, _) -> modifyMVar certificateCache $ \made -> case made of
            Just ready -> pure (made, Ok ready)
            Nothing -> do
                stored <- cachedPreparedInput "validator-selfcheck" [] validChecks $ pure $ case nativeStorage of
                    Error e -> Error ("the native storage library: " ++ e)
                    Ok (_, library) -> case (prepareTexts True library, prepareTexts False own) of
                        (Error e, _) -> Error ("the native storage library: " ++ e)
                        (_, Error e) -> Error ("its own source: " ++ e)
                        (Ok a, Ok b) -> Ok (show (a, b))
                case stored of
                    Error e -> pure (Nothing, Error e)
                    Ok text -> case readChecks text of
                        Nothing -> pure (Nothing, Error "invalid prepared self-check transport")
                        Just (libraryTexts, ownTexts) -> do
                            let library = case nativeStorage of Ok (_, value) -> value; Error e -> error e
                                key = certificateKey unchecked (map snd libraryTexts) (map snd ownTexts)
                                ready = (key, library, libraryTexts, own, ownTexts)
                            _ <- evaluate (length key)
                            pure (Just ready, Ok ready)
  where
    readChecks text = case reads text of
        [(inputs, rest)] | all isSpace rest -> Just inputs
        _ -> Nothing
    validChecks text = case readChecks text :: Maybe ([(String, String)], [(String, String)]) of
        Just _ -> True
        Nothing -> False

validatorKey :: IO (Result String String)
validatorKey = do
    ready <- prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok () -> cachedContentKey "validator-checked" ["-O2"]
            [(emitterEntry, []), ("validator", []), ("validator-selfcheck", [])] $
                fmap (mapResult (\(key, _, _, _, _) -> key)) prepareCertificate

validatorExecutable :: IO (Result FilePath String)
validatorExecutable = do
    key <- validatorKey
    case key of
        Error e -> pure (Error e)
        Ok identity -> do
            existing <- cachedProgramIfPresent "validator" identity
            case existing of
                Error e -> pure (Error e)
                Ok (Just exe) -> pure (Ok exe)
                Ok Nothing -> buildCheckedValidator

buildCheckedValidator :: IO (Result FilePath String)
buildCheckedValidator = do
    prepared <- prepareCertificate
    case prepared of
        Error e -> pure (Error e)
        Ok (key, library, libraryTexts, own, ownTexts) ->
            cachedProgram "validator" key "the validator written in Tersus, checked" $ \output -> do
                unchecked <- uncheckedValidator
                case unchecked of
                    Error e -> pure (Error e)
                    Ok exe -> do
                        storage <- validateTexts (pure (Ok exe)) True False library libraryTexts
                        checked <- case storage of
                            Error e -> pure (Error ("the native storage library: " ++ e))
                            Ok () -> do
                                result <- validateTexts (pure (Ok exe)) False False own ownTexts
                                pure $ case result of
                                    Error e -> Error ("its own source: " ++ e)
                                    Ok () -> Ok ()
                        case checked of
                            Error e -> pure (Error ("the validator written in Tersus does not validate " ++ e))
                            Ok () -> copyFileCloexec exe output >> pure (Ok ())

-- The validator built by the emitter in the cache from the validator and its
-- driver, not yet validated
uncheckedValidator :: IO (Result FilePath String)
uncheckedValidator = cachedUncheckedValidator

-- The verdicts are kept on disk too, so that each function is validated once
-- for a build of the validator however many processes ask: a file per
-- function under the validator's hash, named by a fingerprint of the
-- function's data and holding that data in full, so a verdict is used only
-- for the very data it was given (a fingerprint that collides is a miss).
verdictFile :: String -> String -> IO (Maybe FilePath)
verdictFile namespace text = do
    cache <- cacheDirectory
    pure $ case cache of
        Ok dir -> Just (dir </> ("verdicts-" ++ namespace) </> fingerprint [text])
        Error _ -> Nothing

diskVerdict :: String -> String -> IO (Maybe (Int, Int, Int))
diskVerdict namespace text = do
    file <- verdictFile namespace text
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

storeVerdict :: String -> String -> (Int, Int, Int) -> IO ()
storeVerdict namespace text (status, block, step) = do
    file <- verdictFile namespace text
    case file of
        Nothing -> pure ()
        Just path -> do
            let dir = takeDirectory path
            outcome <- try (do
                createDirectoryIfMissing True dir
                (temporary, handle) <- openTempFileCloexec dir "verdict.tmp"
                hPutStr handle (unwords (map show [status, block, step]) ++ "\n" ++ text)
                hClose handle
                renameFile temporary path) :: IO (Either IOException ())
            pure (either (const ()) id outcome)
