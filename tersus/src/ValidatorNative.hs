-- The validator written in Tersus (lib/validation/), compiled to
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
module ValidatorNative (withValidatorOperation, validateCompiled, validateCompiledUncached, validationRefusals, inBatches, validateLibrary, validationCacheHits, withVerdictLock, inParallel, cachedBootstrapEmitter, cachedBootstrapSourceEmitter, validatorKey, certificateKey, prepareTexts, prepareEncodedTexts, raiseStack) where

import Control.Concurrent.MVar (MVar, modifyMVar, modifyMVar_, newMVar, takeMVar, withMVar)
import Data.List (foldl', isSuffixOf, sortOn)
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
import MirHousekeeping (cachedEmitter, cachedSourceEmitter, cachedUncheckedValidatorFrom,
    emitterIdentity, guardEmitterDirectory, cachedEmitterContentKeyFor, prepareValidatorFor, nativeStorage, prepareBootstrap,
    cachedPreparedInput)
import EmitterProvenance (emitterSourcesMatch)
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
prepareTexts physical program = prepareEncodedTexts ((if physical then encodeLibrary else encode) program)

prepareEncodedTexts :: Either String [(String, (MirValue, MirValue, Integer))] -> Result [(String, String)] String
prepareEncodedTexts encoded = case encoded of
    Left what -> Error (unmodeledFeature what)
    Right functions -> case mapM (\(name, f) -> fmap (\text -> (name, text)) (serializeFunction f)) functions of
        Left e -> Error e
        Right texts -> Ok texts

unmodeledFeature :: String -> String
unmodeledFeature what = "the program uses a feature the Tersus validator does not model yet: " ++ what

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
        (Just note, Nothing) -> "Could not prove: " ++ note ++ " (in " ++ shown ++ ")"
        _ -> "Could not prove: an obligation could not be proved by the Tersus validator (in " ++ shown ++ ", block " ++ show block ++ ", step " ++ show step ++ ")"
    2 -> unmodeledMessage ("an operation in " ++ name ++ ", block " ++ show block)
    3 -> unmodeledMessage ("the control flow of " ++ name)
    _ -> unmodeledMessage ("a loop of " ++ name ++ " at block " ++ show block)
  where
    unmodeledMessage what = "the program uses a feature the Tersus validator does not model yet: " ++ what
    -- (MirCopies.packContracts: the reads of the pack in a variadic function's contracts)
    shown
        | "$contract" `isSuffixOf` name = "the contracts of " ++ take (length name - length "$contract") name
        | otherwise = name

-- Every function of a program checked, not only those before the first refused (as validateCompiled checks them),
-- with the verdicts validateCompiled keeps on disk: what each function refused, or that the validator could not
-- check it, in the program's order.
--
-- Each worker serializes and releases its function's proof text; keeping every text exhausted the Host runner.
validationRefusals :: M.Program -> IO (Result [String] String)
validationRefusals program = case encode program of
    Left what -> pure (Error (unmodeledFeature what))
    Right functions -> do
        sized <- evaluate (forcedSizes [(name, function, functionSize function) | (name, function) <- functions])
        namespace <- validatorKey
        built <- validatorExecutable
        case (namespace, built) of
            (Error e, _) -> pure (Error e)
            (_, Error e) -> pure (Error e)
            (Ok key, Ok exe) -> do
                _ <- evaluate (fullyEvaluated key `seq` fullyEvaluated exe)
                let check (_, function, _) = case serializeFunction function of
                        Left e -> pure (Left e)
                        Right text -> Right <$> storedOrChecked key (pure (Ok exe)) text
                checked <- inParallelBy (\(_, _, size) -> size) check sized
                pure $ case [e | Left e <- checked] of
                    e : _ -> Error e
                    [] -> Ok [message | ((name, _, _), Right outcome) <- zip sized checked, Just message <- [failure name outcome]]
  where
    forcedSizes items = foldr (\(_, _, size) rest -> size `seq` rest) () items `seq` items
    failure name (Error e) = Just ("the compiled validator could not check " ++ name ++ ": " ++ e)
    failure name (Ok verdict@(status, _, _))
        | status /= 0 = Just (refusalMessage False program name verdict)
        | otherwise = Nothing

inBatches :: Int -> ([a] -> IO (Result [String] String)) -> [a] -> IO (Result [String] String)
inBatches size work items = go items []
  where
    go [] done = pure (Ok (concat (reverse done)))
    go remaining done = case splitAt (max 1 size) remaining of
        (taken, rest) -> do
            answered <- work taken
            case answered of
                Error e -> pure (Error e)
                Ok found -> do
                    _ <- evaluate (foldr (seq . fullyEvaluated) () found)
                    go rest (found : done)

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
verdicts _ True texts = do
    selected <- emitterIdentity
    case selected of
        Error e -> pure (Error e)
        Ok producer -> do
            namespace <- validatorKeyFor producer
            case namespace of
                Error e -> pure (Error e)
                Ok key -> withValidatorOperation producer key (\exe -> cachedVerdicts key exe texts)

-- Keep misses on one certified namespace; source drift must refuse, not mix producers.
withValidatorOperation :: (Bool, String, FilePath) -> String -> (IO (Result FilePath String) -> IO (Result a String)) -> IO (Result a String)
withValidatorOperation producer key use = guardEmitterDirectory producer $ do
    saved <- newMVar Nothing
    let current = do
            let (pinned, _, _) = producer
            same <- if pinned then emitterSourcesMatch else pure True
            selected <- if same then emitterIdentity else pure (Error "validator source changed during validation")
            case selected of
                Error e -> pure (Error e)
                Ok actual | actual /= producer -> pure (Error "validator producer changed during validation")
                Ok _ -> do
                    namespace <- validatorKeyFor producer
                    pure $ case namespace of
                        Ok actual | actual == key -> Ok ()
                        Error e -> Error e
                        _ -> Error "validator certificate changed during validation"
        acquire = guardEmitterDirectory producer $ modifyMVar saved $ \previous -> do
            present <- case previous of
                Just exe -> doesFileExist exe
                Nothing -> pure False
            result <- case previous of
                Just exe | present -> pure (Ok exe)
                _ -> do
                    fresh <- current
                    case fresh of
                        Error e -> pure (Error e)
                        Ok () -> validatorExecutableFor producer
            let keep = case result of Ok exe -> Just exe; Error _ -> Nothing
            pure (keep, result)
    result <- use acquire
    case result of
        Error e -> pure (Error e)
        Ok answer -> do
            fresh <- current
            pure $ case fresh of Error e -> Error e; Ok () -> Ok answer

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
    _ <- evaluate (foldr (seq . fullyEvaluated) () texts)
    inParallelBy length check texts

-- The same for any items, the largest by the given size first. GHC 9.6's runtime can lose the wakeup of a thread
-- blocked on a thunk that other threads force too (GHC #26324), so the items must have nothing left to evaluate.
inParallelBy :: (t -> Int) -> (t -> IO b) -> [t] -> IO [b]
inParallelBy size check items = do
    workers <- availableProcessors
    pending <- evaluate (forcedQueue (sortOn (Down . fst) [(size item, (index, item)) | (index, item) <- zip [0 :: Int ..] items]))
    queue <- newMVar (map snd pending)
    found <- newMVar Map.empty
    let next = modifyMVar queue $ \queued -> pure $ case queued of
            [] -> ([], Nothing)
            item : rest -> (rest, Just item)
        worker = do
            item <- next
            case item of
                Nothing -> pure ()
                Just (index, value) -> do
                    checked <- check value
                    modifyMVar_ found (pure . Map.insert index checked)
                    worker
    _ <- parallelBuilds (replicate (max 1 workers) worker)
    Map.elems <$> takeMVar found
  where
    forcedQueue queued = foldr (\(itemSize, (index, _)) rest -> itemSize `seq` index `seq` rest) () queued `seq` queued

fullyEvaluated :: String -> ()
fullyEvaluated = foldr seq ()

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

-- How large the text of a function is, roughly, for the order the functions are checked in; it evaluates everything
-- serializeFunction reads
functionSize :: (MirValue, MirValue, Integer) -> Int
functionSize (blocks, initial, entry) = entry `seq` valueSize blocks + valueSize initial

valueSize :: MirValue -> Int
valueSize value = case value of
    MInt n -> n `seq` 1
    MBool b -> b `seq` 1
    MList values -> foldl' (\total v -> total + valueSize v) 1 values
    MData name fields -> fullyEvaluated name `seq` foldl' (\total (_, v) -> total + valueSize v) (length name) fields
    _ -> 1

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

cachedBootstrapSourceEmitter :: IO (Result FilePath String)
cachedBootstrapSourceEmitter = do
    results <- parallelBuilds [cachedSourceEmitter, validatorExecutable]
    pure $ case results of
        [Ok emitter, Ok _] -> Ok emitter
        [Error e, _] -> Error e
        [_, Error e] -> Error e
        _ -> Error "incomplete checked source bootstrap"

-- The compiled validator in the cache. It is built from its source without
-- being validated (no validator is there yet: uncheckedValidator), and then
-- it validates what it is made of: the native storage library its lists and
-- Boxes are built with, and its own source; only a validator that has done
-- so is used.
type PreparedCertificate = (String, String, FilePath, FilePath, M.Program, [(String, String)], M.Program, [(String, String)])

{-# NOINLINE certificateCache #-}
certificateCache :: MVar (Map.Map (FilePath, String) PreparedCertificate)
certificateCache = unsafePerformIO (newMVar Map.empty)

certificateKey :: String -> [String] -> [String] -> String
certificateKey unchecked library own = fingerprint [show
    (unchecked, map ("1\n" ++) library, map ("1\n" ++) own)]

prepareCertificateFor :: (Bool, String, FilePath) -> IO (Result PreparedCertificate String)
prepareCertificateFor producer@(_, _, directory) = guardEmitterDirectory producer $ do
    prepared <- prepareValidatorFor producer
    case prepared of
        Error e -> pure (Error e)
        Ok (unchecked, own, input) -> do
            executable <- cachedUncheckedValidatorFrom producer unchecked input
            case executable of
                Error e -> pure (Error e)
                Ok exe -> modifyMVar certificateCache $ \made -> case Map.lookup (directory, unchecked) made of
                    Just ready@(_, _, _, previousExe, _, _, _, _) | previousExe == exe -> pure (made, Ok ready)
                    _ -> do
                        stored <- cachedPreparedInput "validator-selfcheck" [] validChecks $ pure $ case nativeStorage of
                            Error e -> Error ("the native storage library: " ++ e)
                            Ok (_, library) -> case (prepareTexts True library, prepareTexts False own) of
                                (Error e, _) -> Error ("the native storage library: " ++ e)
                                (_, Error e) -> Error ("its own source: " ++ e)
                                (Ok a, Ok b) -> Ok (show (a, b))
                        case stored of
                            Error e -> pure (made, Error e)
                            Ok text -> case readChecks text of
                                Nothing -> pure (made, Error "invalid prepared self-check transport")
                                Just (libraryTexts, ownTexts) -> do
                                    let library = case nativeStorage of Ok (_, value) -> value; Error e -> error e
                                        key = certificateKey unchecked (map snd libraryTexts) (map snd ownTexts)
                                        ready = (key, unchecked, directory, exe, library, libraryTexts, own, ownTexts)
                                    _ <- evaluate (length key)
                                    pure (Map.insert (directory, unchecked) ready made, Ok ready)
  where
    readChecks text = case reads text of
        [(inputs, rest)] | all isSpace rest -> Just inputs
        _ -> Nothing
    validChecks text = case readChecks text :: Maybe ([(String, String)], [(String, String)]) of
        Just _ -> True
        Nothing -> False

validatorKey :: IO (Result String String)
validatorKey = do
    selected <- emitterIdentity
    case selected of
        Error e -> pure (Error e)
        Ok producer -> validatorKeyFor producer

validatorKeyFor :: (Bool, String, FilePath) -> IO (Result String String)
validatorKeyFor producer = cachedEmitterContentKeyFor producer "validator-checked" ["-O2"]
    [("validator", []), ("validator-selfcheck", [])] $
        fmap (mapResult (\(key, _, _, _, _, _, _, _) -> key)) (prepareCertificateFor producer)

validatorExecutable :: IO (Result FilePath String)
validatorExecutable = do
    selected <- emitterIdentity
    case selected of
        Error e -> pure (Error e)
        Ok producer -> validatorExecutableFor producer

validatorExecutableFor :: (Bool, String, FilePath) -> IO (Result FilePath String)
validatorExecutableFor producer = guardEmitterDirectory producer $ do
    key <- validatorKeyFor producer
    case key of
        Error e -> pure (Error e)
        Ok identity -> do
            existing <- cachedProgramIfPresent "validator" identity
            case existing of
                Error e -> pure (Error e)
                Ok (Just exe) -> pure (Ok exe)
                Ok Nothing -> buildCheckedValidatorFor producer

buildCheckedValidatorFor :: (Bool, String, FilePath) -> IO (Result FilePath String)
buildCheckedValidatorFor producer = guardEmitterDirectory producer $ do
    prepared <- prepareCertificateFor producer
    case prepared of
        Error e -> pure (Error e)
        Ok (key, unchecked, directory, exe, library, libraryTexts, own, ownTexts) ->
            cachedProgram "validator" key "the validator written in Tersus, checked" $ \output -> do
                current <- cacheDirectory
                if current /= Ok directory || certificateKey unchecked (map snd libraryTexts) (map snd ownTexts) /= key
                    then pure (Error "validator certificate producer changed before validation")
                    else do
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
                            Ok () -> do
                                still <- cacheDirectory
                                if still /= Ok directory then pure (Error "validator cache directory changed before publication")
                                    else copyFileCloexec exe output >> pure (Ok ())

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
