module TestParserBootstrap (testParserBootstrap, withParserBootstrapFixture, bootstrapOverlapAllowed) where

import Control.Concurrent (MVar, forkFinally, killThread, myThreadId, newEmptyMVar, newMVar, putMVar, readMVar, takeMVar, threadDelay)
import Control.Concurrent.MVar (modifyMVar, swapMVar, tryPutMVar, tryReadMVar)
import Control.Exception (AsyncException (ThreadKilled), IOException, SomeAsyncException, SomeException, bracket, bracket_, displayException, evaluate, finally, fromException, mask, onException, throwIO, try)
import Control.Monad (forM, when)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, sort)
import GHC.Clock (getMonotonicTime)
import System.Directory (copyFile, createDirectory, createDirectoryIfMissing, createFileLink, doesFileExist, findExecutable, getTemporaryDirectory, getModificationTime, listDirectory, removeDirectoryRecursive, removeFile, renameFile)
import System.Environment (getEnvironment, getExecutablePath, lookupEnv, setEnv, unsetEnv)
import System.Exit (ExitCode (..))
import System.Process (CreateProcess (..), StdStream (..), getPid, proc, waitForProcess, withCreateProcess)
import System.IO (hClose, hGetContents, openTempFile)
import System.IO.Error (isDoesNotExistError)
import System.FilePath ((</>), takeDirectory)
import System.IO.Unsafe (unsafePerformIO)
import System.Posix.Signals (nullSignal, sigKILL, sigTERM, signalProcessGroup)
import System.Timeout (timeout)

import qualified AstData
import qualified Bootstrap
import qualified Compile
import qualified FileParserProtocol as File
import MirData (writeProgram)
import MirEval (runProgram, MirValue (..))
import Modules (LoadResult (..), resolverFromFiles)
import qualified Modules
import qualified PackageCompile
import MirHousekeeping (listLibrary)
import qualified MirHousekeeping as Housekeeping
import MirLists (lowerLists)
import MirOwnership (expandRefWrites, insertOwnership)
import Native (buildExecutable, cacheDirectory)
import Syntax (Expression (..), Statement (..), Value (..))
import ParsedFile
import qualified ParserSeed
import qualified Pipeline
import PreludeSource (compilerSourceHash, libPackageFiles, stdlibSource, toolPackageFiles, mirPackageFiles)
import Hash (fingerprint)
import Seed (cachedParserSeed, parserSeedHash, seedHash, emitterHash)
import qualified SourceParse
import qualified TersusParser
import TestHarness
import Utils

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [err | Just err <- results] of
    err : _ -> Just err
    [] -> Nothing

withDirectory :: (FilePath -> IO a) -> IO a
withDirectory use = bracket make removeDirectoryRecursive use
  where
    make = do
        tmp <- getTemporaryDirectory
        (home, handle) <- openTempFile tmp "tersus-parser-bootstrap-test"
        hClose handle
        removeFile home
        createDirectory home
        pure home

data BootstrapFixture = BootstrapFixture
    { fixtureDirectory :: FilePath
    , phasePairResults :: Maybe (MVar (Maybe (TestResult, TestResult)))
    }

{-# NOINLINE fixtureHome #-}
fixtureHome :: MVar (Maybe BootstrapFixture)
fixtureHome = unsafePerformIO (newMVar Nothing)

-- An isolated group may use two N1 phase workers; a group sharing the runner stays serial.
bootstrapOverlapAllowed :: Bool -> Int -> Int -> [String] -> Bool -> Bool
bootstrapOverlapAllowed child jobs processors names parentDispatch =
    processors >= 2 && names == ["testParserBootstrap"]
        && (if child then parentDispatch else jobs >= 2)

withParserBootstrapFixture :: Bool -> IO a -> IO a
withParserBootstrapFixture overlap action = do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just name | name `elem` ["emitter-corrupt", "parser-corrupt", "parser-missing", "interpreted-corrupt",
            "clang-missing", "haskell-refused", "cold", "concurrent", "reuse", "repair", "emitter-repair", "fixpoint"] -> action
        Just name -> fail ("unknown parser bootstrap worker: " ++ name)
        Nothing -> withDirectory $ \home -> do
            results <- if overlap then Just <$> newMVar Nothing else pure Nothing
            bracket (swapMVar fixtureHome (Just (BootstrapFixture home results))) restoreHome $ \_ ->
                bracket (swapMVar coldReuseResults Nothing) restoreResults (const action)
  where
    restoreHome previous = swapMVar fixtureHome previous >> pure ()
    restoreResults previous = swapMVar coldReuseResults previous >> pure ()

coldCacheHome :: IO FilePath
coldCacheHome = readMVar fixtureHome >>= maybe (fail "parser bootstrap group fixture is missing") (pure . fixtureDirectory)

worker :: String -> FilePath -> [(String, String)] -> IO (ExitCode, String, String)
worker mode home overrides = timed ("worker " ++ mode) $ do
    self <- getExecutablePath
    inherited <- getEnvironment
    let changed = ("TERSUS_PARSER_BOOTSTRAP_WORKER", mode) : ("XDG_CACHE_HOME", home) : overrides
        environment = changed ++ [(key, value) | (key, value) <- inherited, key `notElem` map fst changed, key /= "TERSUS_PARSER"]
        command = (proc self ["testParserBootstrap", "--child", "+RTS", "-N1", "-RTS"])
            {env = Just environment, create_group = True, std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe}
    withCreateProcess command $ \input output errors process -> mask $ \restore -> do
        pid <- getPid process >>= maybe (fail "bootstrap worker has no process group") pure
        let signal sig = do
                sent <- try (signalProcessGroup sig pid) :: IO (Either IOException ())
                case sent of
                    Left e | not (isDoesNotExistError e) -> throwIO e
                    _ -> pure ()
            gone = do
                present <- try (signalProcessGroup nullSignal pid) :: IO (Either IOException ())
                case present of
                    Left e | isDoesNotExistError e -> pure ()
                           | otherwise -> throwIO e
                    Right () -> threadDelay 10000 >> gone
            stop = do
                signal sigTERM
                _ <- timeout 5000000 (waitForProcess process)
                signal sigKILL
                _ <- waitForProcess process
                ended <- timeout 5000000 gone
                case ended of
                    Just () -> pure ()
                    Nothing -> fail "bootstrap worker descendants did not exit"
            readAll handle = do
                text <- hGetContents handle
                _ <- evaluate (length text)
                pure text
        restore (do
            mapM_ hClose input
            case (output, errors) of
                (Just out, Just err) -> paired (readAll out) (readAll err) $ \readOut readErr -> do
                    status <- waitForProcess process
                    stdoutText <- readOut
                    stderrText <- readErr
                    pure (status, stdoutText, stderrText)
                _ -> fail "bootstrap worker output pipes are missing") `finally` stop

reportWorkerTimings :: String -> IO ()
reportWorkerTimings output = mapM_ putStrLn
    [line | line <- lines output, any (`isPrefixOf` line)
        ["[BOOT] P0 ", "[BOOT] E1+checker+eraser+ListBox ", "[BOOT] P1 ", "[BOOT] source ", "[BOOT] user package "]]

paired :: IO a -> IO b -> (IO a -> IO b -> IO c) -> IO c
paired first second use = pairedResults first second $ \firstResult secondResult _ ->
    use (result firstResult) (result secondResult)
  where
    result slot = readMVar slot >>= either throwIO pure

-- forkFinally publishes each terminal outcome under its mask. Each result slot
-- has one writer and starts empty; the wake notification is nonblocking/coalesced.
pairedResults :: IO a -> IO b -> (MVar (Either SomeException a) -> MVar (Either SomeException b) -> MVar () -> IO c) -> IO c
pairedResults first second use = do
    firstResult <- newEmptyMVar
    secondResult <- newEmptyMVar
    completed <- newEmptyMVar
    let publish slot answer = do
            putMVar slot answer
            _ <- tryPutMVar completed ()
            pure ()
        start = do
            one <- forkFinally first (publish firstResult)
            two <- forkFinally second (publish secondResult)
                `onException` (killThread one >> readMVar firstResult >> pure ())
            pure (one, two)
        stop (one, two) = do
            killThread one
            killThread two
            _ <- readMVar firstResult
            _ <- readMVar secondResult
            pure ()
    bracket start stop $ \_ -> use firstResult secondResult completed

inFreshWorker :: String -> (FilePath -> IO [(String, String)]) -> IO TestResult -> IO TestResult
inFreshWorker mode setup action = do
    selected <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case selected of
        Just active | active == mode -> action
                    | otherwise -> pure Nothing
        Nothing -> withDirectory $ \home -> do
            overrides <- setup home
            (status, out, err) <- worker mode home overrides
            pure $ case status of
                ExitSuccess -> Nothing
                _ -> Just ("fresh " ++ mode ++ " worker: " ++ out ++ err)

inPrimedWorker :: String -> [String] -> IO TestResult -> IO TestResult
inPrimedWorker mode evicted action = do
    selected <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case selected of
        Just active | active == mode -> action
                    | otherwise -> pure Nothing
        Nothing -> do
            (cold, _, _) <- coldAndReuse
            case cold of
                Just e -> pure (Just ("priming requires a successful cold worker: " ++ e))
                Nothing -> coldCacheHome >>= \source -> primedWorker source mode evicted

primedWorker :: FilePath -> String -> [String] -> IO TestResult
primedWorker source mode evicted = withDirectory $ \home -> do
    let target = home </> "tersus"
    copyBootstrapTools (source </> "tersus") target
    names <- listDirectory target
    mapM_ (removeFile . (target </>))
        [name | name <- names, '.' `notElem` name, any (`isPrefixOf` name) evicted]
    (status, out, err) <- worker mode home []
    pure $ case status of
        ExitSuccess -> Nothing
        _ -> Just ("primed " ++ mode ++ " worker: " ++ out ++ err)

copyBootstrapTools :: FilePath -> FilePath -> IO ()
copyBootstrapTools source target = do
    createDirectoryIfMissing True target
    names <- listDirectory source
    mapM_ (\name -> do
        regular <- doesFileExist (source </> name)
        when (regular && not (".lock" `isSuffixOf` name))
            (copyFile (source </> name) (target </> name)))
        [name | name <- names, any (`isPrefixOf` name)
            ["parser-seed-", "tersus-parser-", "seed-", "emitter-", "mir-verify-", "mir-erase-", "validator-", "tersus_rt_"]]

wrongSeed :: String -> FilePath -> IO [(String, String)]
wrongSeed variable home = do
    let path = home </> "wrong-seed.ll"
    writeFile path "not a pinned seed\n"
    pure [(variable, path)]

failureCase :: String -> String -> IO TestResult
failureCase mode expected = inFreshWorker mode setup $ do
    result <- evaluate (Pipeline.compileSource "return 17;")
    pure $ case result of
        Error err -> firstFailure
            [ testAssertErrorContains expected (Error err :: Result () String)
            , testAssertTrue ("Parser tool failure:" `isPrefixOf` err || "Unknown TERSUS_PARSER" `isPrefixOf` err)
            ]
        Ok _ -> Just "a failed bootstrap was hidden by another parser"
  where
    setup home = case mode of
        "emitter-corrupt" -> wrongSeed "TERSUS_SEED_FILE" home
        "parser-corrupt" -> wrongSeed "TERSUS_PARSER_SEED_FILE" home
        "parser-missing" -> pure [("TERSUS_PARSER_SEED_FILE", home </> "missing.ll")]
        "interpreted-corrupt" -> (++ [("TERSUS_PARSER", "interpreted")]) <$> wrongSeed "TERSUS_PARSER_SEED_FILE" home
        "haskell-refused" -> pure [("TERSUS_PARSER", "haskell")]
        "clang-missing" -> do
            let bin = home </> "bin"
            createDirectory bin
            mapM_ (\name -> do
                path <- findExecutable name
                case path of
                    Just executable -> createFileLink executable (bin </> name)
                    Nothing -> pure ()) ["sha256sum", "shasum", "curl"]
            pure [("PATH", bin)]
        _ -> fail ("unknown bootstrap control: " ++ mode)

withSetting :: String -> Maybe String -> IO a -> IO a
withSetting name value action = bracket (lookupEnv name) restore $ \_ -> do
    restore value
    action >>= evaluate
  where
    restore Nothing = unsetEnv name
    restore (Just text) = setEnv name text

retryStages :: IO TestResult
retryStages = sharedPhase fst retryStagesRecipe

sharedPhase :: ((TestResult, TestResult) -> TestResult) -> IO TestResult -> IO TestResult
sharedPhase select serial = do
    role <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    fixture <- readMVar fixtureHome
    case (role, fixture >>= phasePairResults) of
        (Nothing, Just slot) -> do
            outcome <- modifyMVar slot (\saved -> case saved of
                Just results -> pure (saved, Right results)
                Nothing -> do
                    (cold, _, _) <- coldAndReuse
                    answer <- try $ case cold of
                        Just e -> pure (Just ("priming requires a successful cold worker: " ++ e), Just ("priming requires a successful cold worker: " ++ e))
                        Nothing -> collectPhases retryStagesRecipe parserFixpointRecipe
                    let results = case answer of
                            Right values -> values
                            Left ex -> let cancelled = Just ("repair/fixpoint pair interrupted: " ++ displayException (ex :: SomeException)) in (cancelled, cancelled)
                    pure (Just results, answer))
            either throwIO (pure . select) outcome
        _ -> serial

-- Observe the guaranteed terminal outcomes, including cancellation after an
-- action finishes; no completion message is sent from inside a phase action.
collectPhases :: IO TestResult -> IO TestResult -> IO (TestResult, TestResult)
collectPhases first second = pairedResults checkedFirst checkedSecond $ \a b completed ->
    let next = do
            firstAnswer <- tryReadMVar a
            secondAnswer <- tryReadMVar b
            firstValue <- traverse verdict firstAnswer
            secondValue <- traverse verdict secondAnswer
            case (firstValue, secondValue) of
                (Just x, Just y) -> pure (x, y)
                _ -> takeMVar completed >> next
     in next
  where
    checkedFirst = first >>= \result -> evaluate (forceTestResult result) >> pure result
    checkedSecond = second >>= \result -> evaluate (forceTestResult result) >> pure result
    verdict (Right result) = pure result
    verdict (Left ex) = case fromException ex :: Maybe SomeAsyncException of
        Just _ -> throwIO ex
        Nothing -> pure (Just (displayException ex))

retryStagesRecipe :: IO TestResult
retryStagesRecipe = inPrimedWorker "repair" ["parser-seed-", "tersus-parser-", "seed-"] $ do
    directory <- cacheDirectory
    case directory of
        Error e -> pure (Just e)
        Ok cache -> withDirectory $ \home -> do
            let missing = home </> "missing-parser.ll"
                bin = home </> "bin"
                sourceValue answer = case answer of
                    Left e -> Just e
                    Right wire -> case AstData.readParsed wire of
                        Error e -> Just e
                        Ok body -> testAssertTrue (not (null body)) <> testAssertEq (last body) (Return (Val (VInt 43)))
                refused label answer = case answer of
                    Left e -> testAssertTrue (ParserSeed.toolFailure e)
                    Right _ -> Just (label ++ ": transient bootstrap error was not refused")
                parsed answer = testAssertEq (fmap fst answer) (Right (ParsedFile [] [Return (Val (VInt 42))]))
            createDirectory bin
            mapM_ (\name -> do
                found <- findExecutable name
                case found of
                    Nothing -> pure ()
                    Just path -> createFileLink path (bin </> name)) ["sha256sum", "shasum"]
            sourceFailed <- withSetting "TERSUS_PARSER_SEED_FILE" (Just missing) (TersusParser.toolParseSource "return 41;")
            nativeFailed <- withSetting "TERSUS_PARSER_SEED_FILE" (Just missing) (TersusParser.parseFileNative emptyDecls "return 42;")
            clangFailed <- withSetting "PATH" (Just bin) (TersusParser.parseFileNative emptyDecls "return 42;")
            emitterFailed <- withSetting "TERSUS_SEED_FILE" (Just (home </> "missing-emitter.ll")) (TersusParser.parseFileNative emptyDecls "return 42;")
            nativeReady <- TersusParser.parseFileNative emptyDecls "return 42;"
            sourceReady <- TersusParser.toolParseSource "return 43;"
            case firstFailure [refused "source P0" sourceFailed, refused "native P0" nativeFailed, refused "clang" clangFailed, refused "emitter E0" emitterFailed, parsed nativeReady, sourceValue sourceReady] of
                Just e -> pure (Just e)
                Nothing -> do
                    executable <- TersusParser.parserExecutable
                    case executable of
                        Error e -> pure (Just e)
                        Ok path -> do
                            removeFile path
                            rebuilt <- TersusParser.parseFileNative emptyDecls "return 42;"
                            present <- doesFileExist path
                            let p0 = cache </> ("parser-seed-" ++ parserSeedHash)
                            interpretedFailed <- bracket (renameFile p0 (p0 ++ ".held"))
                                (\_ -> renameFile (p0 ++ ".held") p0)
                                (\_ -> withSetting "TERSUS_PARSER_SEED_FILE" (Just missing) (TersusParser.parseFileInterpreted emptyDecls "return 42;"))
                            interpretedReady <- TersusParser.parseFileInterpreted emptyDecls "return 42;"
                            pure (firstFailure [parsed rebuilt, testAssertTrue present, refused "interpreted P0" interpretedFailed, parsed interpretedReady])

emitterRetryStages :: IO TestResult
emitterRetryStages = inPrimedWorker "emitter-repair" ["parser-seed-", "seed-"] $ withDirectory $ \home -> do
    let bin = home </> "bin"
        refused label result = case result of
            Error _ -> Nothing
            Ok _ -> Just (label ++ ": direct emitter bootstrap error was not refused")
    createDirectory bin
    mapM_ (\name -> do
        found <- findExecutable name
        case found of
            Nothing -> pure ()
            Just path -> createFileLink path (bin </> name)) ["sha256sum", "shasum"]
    parserFailed <- withSetting "TERSUS_PARSER_SEED_FILE" (Just (home </> "missing-parser.ll")) Bootstrap.cachedEmitter
    clangFailed <- withSetting "PATH" (Just bin) Bootstrap.cachedEmitter
    emitterFailed <- withSetting "TERSUS_SEED_FILE" (Just (home </> "missing-emitter.ll")) Bootstrap.cachedEmitter
    ready <- Bootstrap.cachedEmitter
    case firstFailure [refused "P0" parserFailed, refused "clang" clangFailed, refused "E0" emitterFailed] of
        Just e -> pure (Just e)
        Nothing -> case ready of
            Error e -> pure (Just e)
            Ok _ -> do
                let checked = Compile.lowerSource True "return 42;" `bindResult` \program ->
                        Housekeeping.verifyProgram program `bindResult` \_ -> Housekeeping.eraseGhosts program
                case checked of
                    Error e -> pure (Just e)
                    Ok program -> do
                        _ <- evaluate listLibrary
                        pure (testAssertEq (runProgram program) (Ok (Just (MInt 42))))

bootstrapLibraryHash :: IO TestResult
bootstrapLibraryHash = pure $ testAssertEq emitterHash
    (fingerprint ([seedHash, parserSeedHash] ++ concatMap (\(path, text) -> [path, text]) (mirPackageFiles ++ libPackageFiles)
        ++ [stdlibSource, compilerSourceHash]))

timed :: String -> IO a -> IO a
timed name action = do
    start <- getMonotonicTime
    value <- action
    end <- getMonotonicTime
    putStrLn ("[BOOT] " ++ name ++ " " ++ show (end - start) ++ "s")
    pure value

waitForColdPeer :: FilePath -> IO ()
waitForColdPeer cache = do
    participant <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_PARTICIPANT"
    (own, peer) <- case participant of
        Just "A" -> pure ("A", "B")
        Just "B" -> pure ("B", "A")
        _ -> fail "cold bootstrap participant is missing"
    let root = takeDirectory cache
        ready name = root </> ("ready-" ++ name)
        wait = do
            present <- doesFileExist (ready peer)
            if present then pure () else threadDelay 10000 >> wait
    writeFile (ready own) "ready\n"
    complete <- timeout 30000000 wait
    case complete of
        Just () -> pure ()
        Nothing -> fail "cold bootstrap peer did not observe the empty cache"

coldStages :: IO TestResult
coldStages = do
    directory <- cacheDirectory
    case directory of
        Error e -> pure (Just e)
        Ok home -> do
            before <- listDirectory home
            waitForColdPeer home
            seed <- timed "P0" cachedParserSeed
            case ParserSeed.parseImportPrefix userMain of
                Right [Import ["bootstrapprobe", "math"] Nothing (Just ["twice"]) 1 1] -> pure ()
                Left e -> fail e
                Right imports -> fail ("unexpected user-package import metadata: " ++ show imports)
            emitter <- timed "E1+checker+eraser+ListBox" Bootstrap.cachedEmitter
            parser <- timed "P1" (TersusParser.parseFileNative emptyDecls "return 42;")
            source <- timed "source" (evaluate (Pipeline.compileSource "return 42;"))
            package <- timed "user package" $ evaluate $ case Pipeline.loadFromEntry (resolver userPackage) "bootstrapprobe/main.tersus" of
                Left e -> Error e
                Right (PackageResult pkg) -> Pipeline.compileModulesValidated pkg
                Right _ -> Error "the importing user program is not a package"
            entries <- listDirectory home
            pure $ firstFailure
                [ if null before then Nothing else Just ("cold worker started with " ++ show before)
                , case seed of Error e -> Just e; Ok _ -> Nothing
                , case emitter of Error e -> Just e; Ok _ -> Nothing
                , case parser of Left e -> Just e; Right (parsed, _) -> testAssertEq (fileBody parsed) [Return (Val (VInt 42))]
                , case source `bindResult` runProgram of Error e -> Just e; Ok answer -> testAssertEq answer (Just (MInt 42))
                , case package `bindResult` runProgram of Error e -> Just e; Ok answer -> testAssertEq answer (Just (MInt 42))
                , testAssertTrue (all (`elem` entries) ["parser-seed-" ++ parserSeedHash, "seed-" ++ seedHash, "emitter-" ++ emitterHash, "tersus-parser-" ++ TersusParser.parserHash])
                , testAssertTrue (all (\prefix -> any (prefix `isPrefixOf`) entries) ["mir-verify-", "mir-erase-", "tersus_rt_"])
                ]
  where
    resolver = resolverFromFiles
    userMain = "import bootstrapprobe::math { twice }; return twice(21);"
    userPackage =
        [ ("bootstrapprobe/package.tersus", "")
        , ("bootstrapprobe/main.tersus", userMain)
        , ("bootstrapprobe/math/math.tersus", "fn twice(x: Int) -> Int ~ { return x + x; };")
        ]

warmStages :: IO TestResult
warmStages = do
    answer <- TersusParser.parseFileNative emptyDecls "return 42;"
    ir <- Bootstrap.tersusLlvm "return 42;"
    pure $ firstFailure [either Just (const Nothing) answer, case ir of Error e -> Just e; Ok _ -> Nothing]

{-# NOINLINE coldReuseResults #-}
coldReuseResults :: MVar (Maybe (TestResult, TestResult, TestResult))
coldReuseResults = unsafePerformIO (newMVar Nothing)

coldAndReuse :: IO (TestResult, TestResult, TestResult)
coldAndReuse = modifyMVar coldReuseResults $ \saved -> case saved of
    Just results -> pure (saved, results)
    Nothing -> do
        home <- coldCacheHome
        results <- paired
            (worker "cold" home [("TERSUS_PARSER_BOOTSTRAP_PARTICIPANT", "A")])
            (worker "concurrent" home [("TERSUS_PARSER_BOOTSTRAP_PARTICIPANT", "B")]) $ \readFirst readSecond -> do
                first <- try readFirst :: IO (Either SomeException (ExitCode, String, String))
                cold <- workerResult "cold A" first
                second <- try readSecond :: IO (Either SomeException (ExitCode, String, String))
                peer <- workerResult "cold B" second
                names <- listDirectory (home </> "tersus")
                let concurrent = firstFailure [cold, peer,
                        testAssertTrue (all (`elem` names) ["parser-seed-" ++ parserSeedHash,
                            "emitter-" ++ emitterHash, "tersus-parser-" ++ TersusParser.parserHash])]
                reused <- case cold of
                    Just e -> pure (Just ("cache reuse requires a successful cold worker: " ++ e))
                    Nothing -> do
                        outcome <- try (reuse home) :: IO (Either SomeException TestResult)
                        either synchronousFailure pure outcome
                pure (cold, reused, concurrent)
        pure (Just results, results)
  where
    workerResult label result = case result of
        Left ex -> synchronousFailure ex
        Right (ExitSuccess, out, _) -> reportWorkerTimings out >> pure Nothing
        Right (_, out, err) -> pure (Just (label ++ ": " ++ out ++ err))
    reuse home = do
        let cache = home </> "tersus"
        names <- sort <$> listDirectory cache
        before <- mapM (getModificationTime . (cache </>)) names
        second <- worker "reuse" home []
        afterNames <- sort <$> listDirectory cache
        after <- mapM (getModificationTime . (cache </>)) names
        pure $ case second of
            (ExitSuccess, _, _) -> testAssertEq (afterNames, after) (names, before)
            (_, out, err) -> Just (out ++ err)
    synchronousFailure ex = case fromException ex :: Maybe SomeAsyncException of
        Just _ -> throwIO ex
        Nothing -> pure (Just (displayException ex))

coldWorkerStages :: IO TestResult
coldWorkerStages = do
    result <- coldStages
    case result of
        Just e -> pure (Just e)
        Nothing -> warmStages

coldProcess :: IO TestResult
coldProcess = do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just "cold" -> coldWorkerStages
        Just _ -> pure Nothing
        Nothing -> do
            (cold, _, _) <- coldAndReuse
            pure cold

cacheReuse :: IO TestResult
cacheReuse = do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just "reuse" -> warmStages
        Just _ -> pure Nothing
        Nothing -> do
            (_, reused, _) <- coldAndReuse
            pure reused

concurrentCold :: IO TestResult
concurrentCold = do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just "concurrent" -> coldWorkerStages
        Just _ -> pure Nothing
        Nothing -> do
            (_, _, concurrent) <- coldAndReuse
            pure concurrent

parserFixpoint :: IO TestResult
parserFixpoint = sharedPhase snd parserFixpointRecipe

parserFixpointRecipe :: IO TestResult
parserFixpointRecipe = inPrimedWorker "fixpoint" [] $ do
    emitter <- Bootstrap.cachedEmitter
    let zeroPackage = loadPackage ParserSeed.parseFileWith
        onePackage = loadPackage (checkedParser TersusParser.parseFileNative)
        zeroOwned = zeroPackage `bindResult` ownPackage
        oneOwned = onePackage `bindResult` ownPackage
    case (emitter, zeroPackage, onePackage, zeroOwned, oneOwned) of
        (Ok exe, Ok a, Ok b, Ok zero, Ok one)
            | show a /= show b -> pure (Just "P0/P1 prepared current PACKAGE AST/imports/Marks/identities differ")
            | writeProgram zero /= writeProgram one -> pure (Just "P0/P1 current checking/lowering/MIR differs")
            | otherwise -> do
                first <- Bootstrap.emitWith exe (writeProgram zero)
                second <- Bootstrap.emitWith exe (writeProgram one)
                case (first, second) of
                    (Ok ir0, Ok ir1) | ir0 == ir1 -> withDirectory $ \home -> do
                        let two = home </> "parser-two"
                        built <- buildExecutable two ir1
                        case built of
                            Error e -> pure (Just e)
                            Ok () -> do
                                let twoParser = ParserSeed.parseFileWithTool (pure (Ok two))
                                    twoPackage = loadPackage (checkedParser twoParser)
                                case twoPackage of
                                    Error e -> pure (Just e)
                                    Ok c | show b /= show c -> pure (Just "P1/P2 prepared current PACKAGE differs")
                                    Ok _ -> case SourceParse.probeDecls of
                                        Left e -> pure (Just e)
                                        Right decls -> do
                                            results <- forM ["return 42;", "s = \"λ🙂\"; return size(s.bytes);", "enum E { A, B }; enum E { C }; return E::C;", "import app::geo as g { Point }; return 0;"] $ \source -> do
                                                p0 <- ParserSeed.parseFileNative (locating decls) source
                                                p1 <- TersusParser.parseFileNative (locating decls) source
                                                p2 <- twoParser (locating decls) source
                                                pure (sameFile p0 p1 <> sameFile p1 p2)
                                            pure (firstFailure results)
                    (Error e, _) -> pure (Just e)
                    (_, Error e) -> pure (Just e)
                    _ -> pure (Just "regenerated current P1/P2 IR differs")
        (Error e, _, _, _, _) -> pure (Just e)
        (_, Error e, _, _, _) -> pure (Just e)
        (_, _, Error e, _, _) -> pure (Just e)
        (_, _, _, Error e, _) -> pure (Just e)
        (_, _, _, _, Error e) -> pure (Just e)
  where
    loadPackage parser = case Modules.loadFromEntryWith parser (resolverFromFiles toolPackageFiles) "examples/parser/parser.tersus" of
        Left e -> Error e
        Right (PackageResult pkg) -> Ok pkg
        Right _ -> Error "parser was not loaded as its current package"
    ownPackage pkg = PackageCompile.compileModulesLinked pkg `bindResult` \program ->
        mapResult insertOwnership (Housekeeping.nativeProgram program)
    checkedParser current decls source = unsafePerformIO $ do
        p0 <- ParserSeed.parseFileNative decls source
        pn <- current decls source
        pure $ case (p0, pn) of
            (Left e, Left _) | not (ParserSeed.toolFailure e) -> pn
            _ -> case sameFile p0 pn of
                Nothing -> pn
                Just e -> Left (ParserSeed.failure ("prepared package file parity: " ++ e))
    sameFile (Right (a, da)) (Right (b, db)) = testAssertEq a b <> testAssertEq (File.writeParsedFile a da) (File.writeParsedFile b db)
    sameFile (Left e) _ = Just e
    sameFile _ (Left e) = Just e

overlapControls :: IO TestResult
overlapControls = do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just _ -> pure Nothing
        Nothing -> do
            failures <- collectPhases (pure (Just "repair failure")) (ioError (userError "fixpoint failure"))
            firstHome <- newEmptyMVar
            secondHome <- newEmptyMVar
            let isolated own peer = withDirectory $ \home -> do
                    let marker = home </> "retained"
                    writeFile marker "kept"
                    putMVar own home
                    other <- readMVar peer
                    present <- doesFileExist marker
                    pure (firstFailure [testAssertTrue (home /= other), testAssertTrue present])
            isolation <- timeout 5000000 (collectPhases (isolated firstHome secondHome) (isolated secondHome firstHome))
            cancellation <- cancellationControl
            publication <- terminalPublicationControl
            pure $ firstFailure
                [ testAssertEq (fst failures) (Just "repair failure")
                , testAssertTrue (maybe False ("fixpoint failure" `isInfixOf`) (snd failures))
                , testAssertEq isolation (Just (Nothing, Nothing))
                , cancellation
                , publication
                , firstFailure [testAssertEq (bootstrapOverlapAllowed child jobs processors names marker) expected
                    | (child, jobs, processors, names, marker, expected) <-
                        [(False, 4, 4, ["testParserBootstrap"], False, True)
                        , (False, 1, 4, ["testParserBootstrap"], True, False)
                        , (False, 4, 1, ["testParserBootstrap"], False, False)
                        , (False, 4, 4, ["testParserBootstrap", "testParser"], True, False)
                        , (True, 4, 4, ["testParserBootstrap"], False, False)
                        , (True, 1, 4, ["testParserBootstrap"], True, True)
                        , (True, 1, 4, ["testParserBootstrap"], False, False)]]
                ]

-- Fill the coalescing wake slot before terminal publication: neither terminal
-- callback may block, and both guaranteed outcomes remain independently readable.
terminalPublicationControl :: IO TestResult
terminalPublicationControl = do
    release <- newEmptyMVar
    let action = readMVar release >> pure Nothing
    result <- timeout 5000000 $ pairedResults action action $ \a b wake -> do
        putMVar wake ()
        putMVar release ()
        first <- readMVar a
        second <- readMVar b
        pure (either (Just . displayException) id first, either (Just . displayException) id second)
    pure (testAssertEq result (Just (Nothing, Nothing)))

cancellationControl :: IO TestResult
cancellationControl = firstFailure <$> mapM cancellationCase ["parent", "first", "second", "external-first", "external-second"]

cancellationCase :: String -> IO TestResult
cancellationCase trigger = do
    firstStarted <- newEmptyMVar
    secondStarted <- newEmptyMVar
    firstStopped <- newEmptyMVar
    secondStopped <- newEmptyMVar
    block <- newEmptyMVar
    completed <- newEmptyMVar
    firstThread <- newEmptyMVar
    secondThread <- newEmptyMVar
    let held name threadSlot started peer stopped = bracket_ (do
            thread <- myThreadId
            putMVar threadSlot thread
            putMVar started ()) (putMVar stopped ()) $ do
            _ <- readMVar peer
            if trigger == name then throwIO ThreadKilled else takeMVar block
        run = collectPhases (held "first" firstThread firstStarted secondStarted firstStopped) (held "second" secondThread secondStarted firstStarted secondStopped)
    bracket (forkFinally run (putMVar completed)) killThread $ \thread -> do
        ready <- timeout 5000000 (readMVar firstStarted >> readMVar secondStarted)
        case ready of
            Nothing -> pure (Just "paired phases did not both start")
            Just () -> do
                when (trigger == "parent") (killThread thread)
                when (trigger == "external-first") (readMVar firstThread >>= killThread)
                when (trigger == "external-second") (readMVar secondThread >>= killThread)
                cleaned <- timeout 5000000 (readMVar completed >>= \answer -> readMVar firstStopped >> readMVar secondStopped >> pure answer)
                pure $ case cleaned of
                    Just (Left ex) | Just _ <- (fromException ex :: Maybe SomeAsyncException) -> Nothing
                    _ -> Just (trigger ++ ": paired cancellation did not propagate after both phase cleanups")

bootstrapCase :: String -> IO TestResult -> Test
bootstrapCase name action = TestCase name $ do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just _ -> action
        Nothing -> timed name $ do
            result <- action
            _ <- evaluate (forceTestResult result)
            pure result

testParserBootstrap :: Test
testParserBootstrap = TestList "testParserBootstrap"
    [ bootstrapCase "default whole Pipeline refuses failed native bootstrap" (failureCase "emitter-corrupt" "bootstrap/emitter.sha256")
    , bootstrapCase "corrupt parser seed is an explicit tool failure" (failureCase "parser-corrupt" "bootstrap/parser.sha256")
    , bootstrapCase "missing parser override is an explicit tool failure" (failureCase "parser-missing" "verify the parser bootstrap seed")
    , bootstrapCase "interpreted parser still requires verified native P0" (failureCase "interpreted-corrupt" "bootstrap/parser.sha256")
    , bootstrapCase "no clang is an explicit P0 tool failure" (failureCase "clang-missing" "Could not run clang")
    , bootstrapCase "retired haskell backend is refused" (failureCase "haskell-refused" "expected native or interpreted")
    , bootstrapCase "cold process reaches P0 E1 P1 source and package" coldProcess
    , bootstrapCase "fresh processes reuse every bootstrap cache entry without writes" cacheReuse
    , bootstrapCase "concurrent empty-cache processes converge" concurrentCold
    , bootstrapCase "same-process transient failures repair without stale library or executable caches" retryStages
    , bootstrapCase "public emitter bootstrap failures repair before tool and library CAF initialization" emitterRetryStages
    , bootstrapCase "bootstrap fingerprints cover the complete compiler library manifest" bootstrapLibraryHash
    , bootstrapCase "P0 P1 current-source fixpoint regenerates identical IR and P2 behavior" parserFixpoint
    , bootstrapCase "isolated phase overlap retains failure attribution, private homes and cancellation" overlapControls
    ]
