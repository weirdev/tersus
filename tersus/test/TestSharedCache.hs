module TestSharedCache (testSharedCache, testSharedCacheProbe) where

import Control.Concurrent (forkIO, killThread, newEmptyMVar, putMVar, takeMVar, threadDelay)
import Control.Exception (SomeException, bracket, finally, throwIO, try)
import Control.Monad (when)
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.List (isInfixOf, isPrefixOf, sort)
import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import PreludeSource (mirPackageFiles)
import Seed (emitterHash)
import qualified TersusParser
import qualified Modules
import qualified PackageCompile
import qualified MirHousekeeping
import qualified Data.Map.Strict as Map
import System.Directory (copyFile, createDirectoryIfMissing, doesDirectoryExist, doesFileExist, getModificationTime, getTemporaryDirectory, listDirectory, removeDirectoryRecursive, removeFile, renameFile, setModificationTime)
import System.Environment (getEnvironment, getExecutablePath, lookupEnv, setEnv, unsetEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>), takeDirectory, takeFileName)
import System.IO (IOMode (WriteMode), SeekMode (AbsoluteSeek), hClose, openTempFile, withFile)
import System.Posix.IO (LockRequest (WriteLock), closeFd, waitToSetLock)
import System.Posix.Process (exitImmediately, getProcessID)
import System.Posix.Signals (sigKILL, signalProcess)
import System.Process (CreateProcess (..), ProcessHandle, StdStream (UseHandle), createProcess, proc, readCreateProcessWithExitCode, terminateProcess, waitForProcess)
import System.Timeout (timeout)

import Modules (LoadResult (..), LoadedPackage (..), LoadedModule (..), LoadedFile (..), ModuleId (..), loadFromFilesystem, normalizePath, snapshotFromFilesystem)
import MirHousekeeping (emitterEntry)
import Mir (BasicBlock (..), BlockId (..), Function (..), FunctionSpec (..), LocalDecl (..), Program (..), Statement (..))
import qualified Mir as Mir
import MirHousekeeping (verifyProgram)
import Native (cacheDirectory, cachedProgram, runWithInputFull)
import MirData (forNative)
import TestHarness
import Types (Type (..))
import Utils

richSource :: String
richSource = "struct Packet<n> { body: Array<Int, n> }; struct S { n: Int } invariant [{ affirm n >= 0; }]; fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n; }; p = Packet<2> { body: #[1, 2] }; s = S { n: f(get(p.body, 0)) }; return s.n;"

probeSource :: String
probeSource = "return 987021;"

invalidProbeSource :: String
invalidProbeSource = "return missing_hash_probe_987099(;"

testSharedCache :: Test
testSharedCache =
    TestList
        "testSharedCache"
        (map requireParser
        [ TestCase "truncated named List declaration is refused natively" (rawNamedTruncation "List" "")
        , TestCase "truncated named Box element is refused natively" (rawNamedTruncation "Box" " type")
        , TestCase "frozen tool reuse keeps the full freshly validated program" toolValidationParity
        , TestCase "package snapshots invalidate on dependencies, entry, imports and file layout" packageSnapshots
        , TestCase "duplicate paths and normalized aliases use the resolver's snapshot" packageAliases
        , TestCase "independent processes reuse a package snapshot" packageProcesses
        , TestCase "failed native parsing is retried in the same process" parserRetry
        , TestCase "lossless roundtrip keeps contracts, invariants, generics and ghosts" roundtrip
        , TestCase "source change misses" sourceChange
        , TestCase "stage isolation" stageIsolation
        , TestCase "corrupt and truncated entries recompute" corruptRecomputes
        , TestCase "a well-formed entry for another source is not trusted" poisonedEntry
        , TestCase "failed compiles are not filed" failedNotFiled
        , TestCase "independent processes reuse an entry" independentProcesses
        , TestCase "concurrent processes share one entry" concurrentProcesses
        , TestCase "a killed lock owner releases the entry" killedOwnerReleases
        , TestCase "an unusable lock falls back without hanging" unusableLockFallsBack
        , TestCase "a mutated program is still verified" mutatedStillVerified
        , TestCase "executable digest ignores mtime and detects equal-size byte changes" digestIdentity
        , TestCase "an unreadable executable has no identity" unreadableIdentity
        , TestCase "full SHA256 keys isolate exact source and stage" exactKeys
        , TestCase "a restored entry survives touching the actual executable" touchedExecutable
        , TestCase "a stale build entry is rejected in a fresh process" staleBuildEntry
        , TestCase "missing hash tools compile without reading or writing disk entries" missingHashTools
        , TestCase "native concurrent processes build once and warm hits preserve the entry" (nativeProcesses False)
        , TestCase "native nested checker emitter seed locks do not deadlock" (nativeProcesses True)
        , TestCase "native failed builders release the lock for retry" (nativeRecovery "error")
        , TestCase "native exceptions release the lock for retry" (nativeRecovery "exception")
        , TestCase "native crashed builders release the lock for retry" (nativeRecovery "crash")
        , TestCase "native killed builders release the lock for retry" (nativeRecovery "hold")
        , TestCase "native threads still build once" nativeThreads
        , TestCase "package stages share lossless validated intermediates" packageStages
        , TestCase "package keys include dependency contents and module layout" packageInputs
        , TestCase "independent processes reuse package compilation" (ciPackageProcesses False)
        , TestCase "concurrent processes share package compilation" (ciPackageProcesses True)
        , TestCase "embedded reuse requires identical loaded compiler input" embeddedInputs
        , TestCase "package keys retain the resolver's duplicate precedence" packageDuplicateKeys
        , TestCase "changed embedded source still fails validation independently" embeddedChangedSource
        ])
  where
    requireParser (TestCase name action) = TestCase name $ do
        ready <- TersusParser.runParserTool False ["return 0;"]
        case ready of
            Left e -> pure (Just e)
            Right _ -> action
    requireParser test = test

rawNamedTruncation :: String -> String -> IO TestResult
rawNamedTruncation name suffix = do
    cache <- cacheDirectory
    case cache of
        Error e -> pure (Just e)
        Ok dir -> do
            let exe = dir </> ("tersus-parser-" ++ TersusParser.parserHash)
                request ty = unlines
                    [ "tersus-file-parse 1", "decls", "ctors 0", "types 0", "self none"
                    , "selfType some " ++ ty, "typeParams 0", "generics 0", "implParams 0"
                    , "ownClone false", "locate false", "fieldTypes 0", "endDecls", "source 0"
                    ]
                prefix = "named " ++ show name ++ " 1"
            (goodCode, goodOut, _) <- runWithInputFull exe (request (prefix ++ " type int"))
            (badCode, badOut, errors) <- runWithInputFull exe (request (prefix ++ suffix))
            pure $ firstFailure
                [ testAssertEq goodCode ExitSuccess
                , testAssertTrue ("tersus-file 1\n" `isPrefixOf` goodOut)
                , testAssertEq badCode ExitSuccess
                , testAssertEq badOut "1\n"
                , testAssertTrue (not (null errors))
                ]

testSharedCacheProbe :: Test
testSharedCacheProbe = TestList "testSharedCacheProbe" [TestCase "probe" probe]

probe :: IO TestResult
probe = do
    native <- lookupEnv "TERSUS_NATIVE_CACHE_PROBE"
    package <- lookupEnv "TERSUS_PACKAGE_CACHE_PROBE"
    case package of
        Just path -> do
            Just marker <- lookupEnv "TERSUS_SHARED_CACHE_PROBE"
            result <- validatedFromFile path
            case result of
                Error e -> pure (Just e)
                Ok program -> writeFile marker (encodeProgram program) >> pure Nothing
        Nothing -> maybe sharedProbe nativeProbe native

sharedProbe :: IO TestResult
sharedProbe = do
    retry <- lookupEnv "TERSUS_SHARED_CACHE_PARSER_RETRY"
    case retry of
        Just _ -> parserRetryProbe
        Nothing -> regularSharedProbe

regularSharedProbe :: IO TestResult
regularSharedProbe = do
    hold <- lookupEnv "TERSUS_SHARED_CACHE_PROBE_HOLD"
    case hold of
        Just lockPath -> do
            fd <- openEntryLockFile lockPath
            waitToSetLock fd (WriteLock, AbsoluteSeek, 0, 0)
            marker <- lookupEnv "TERSUS_SHARED_CACHE_PROBE"
            case marker of
                Just path -> writeFile (path ++ ".holding") ""
                Nothing -> pure ()
            threadDelay 600000000
            closeFd fd
            pure ()
        Nothing -> pure ()
    marker <- lookupEnv "TERSUS_SHARED_CACHE_PROBE"
    case marker of
        Nothing -> pure Nothing
        Just path -> do
            invalid <- lookupEnv "TERSUS_SHARED_CACHE_PROBE_INVALID"
            case invalid of
                Just _ -> do
                    result <- compileOnce invalidProbeSource
                    case result of
                        Error e -> writeFile path e >> pure Nothing
                        Ok _ -> pure (Just "invalid source reused a successful compilation")
                Nothing -> do
                    package <- lookupEnv "TERSUS_SHARED_CACHE_PACKAGE"
                    result <- maybe (compileOnce probeSource) programFromFile package
                    case result of
                        Error e -> pure (Just e)
                        Ok program -> do
                            writeFile path (encodeProgram program)
                            pure Nothing

withNativeHome :: (FilePath -> IO a) -> IO a
withNativeHome use = do
    tmp <- getTemporaryDirectory
    (home, handle) <- openTempFile tmp "tersus-native-cache-test"
    hClose handle
    removeFile home
    createDirectoryIfMissing True home
    use home `finally` removeDirectoryRecursive home

awaitNativeFile :: FilePath -> IO ()
awaitNativeFile path = do
    ready <- timeout 10000000 loop
    case ready of
        Just () -> pure ()
        Nothing -> ioError (userError ("native probe did not create " ++ path))
  where
    loop = do
        present <- doesFileExist path
        if present then pure () else threadDelay 10000 >> loop

nativeProbe :: String -> IO TestResult
nativeProbe mode = do
    Just home <- lookupEnv "XDG_CACHE_HOME"
    Just marker <- lookupEnv "TERSUS_SHARED_CACHE_PROBE"
    writeFile (marker ++ ".started") ""
    when (mode `elem` ["shared", "nested"]) (awaitNativeFile (home </> "go"))
    result <- make (if mode == "nested" then "checker" else "single")
    case result of
        Error e -> pure (if mode == "error" then Nothing else Just e)
        Ok path -> writeFile marker path >> pure Nothing
  where
    make kind = cachedProgram ("native-probe-" ++ kind) "key" "native cache probe" $ \output -> do
        Just home <- lookupEnv "XDG_CACHE_HOME"
        Just marker <- lookupEnv "TERSUS_SHARED_CACHE_PROBE"
        writeFile (marker ++ "." ++ kind ++ ".built") ""
        case mode of
            "error" -> pure (Error "intentional builder failure")
            "exception" -> throwIO (userError "intentional builder exception")
            "crash" -> exitImmediately (ExitFailure 23) >> pure (Error "crash returned")
            "hold" -> do
                pid <- getProcessID
                writeFile (marker ++ ".pid") (show pid)
                threadDelay 600000000
                pure (Error "holder was not killed")
            _ -> do
                when (mode == "shared" || (mode == "nested" && kind == "seed")) (awaitNativeFile (home </> "release"))
                dependency <- case kind of
                    "checker" -> make "emitter"
                    "emitter" -> make "seed"
                    _ -> pure (Ok "")
                case dependency of
                    Error e -> pure (Error e)
                    Ok _ -> writeFile output kind >> pure (Ok ())

withNativeChildren :: FilePath -> [(String, String)] -> ([ProcessHandle] -> IO a) -> IO a
withNativeChildren home children = bracket
    (mapM (\(marker, mode) -> spawnProbe home [("TERSUS_SHARED_CACHE_PROBE", home </> marker), ("TERSUS_NATIVE_CACHE_PROBE", mode)]) children)
    (mapM_ (\child -> terminateProcess child >> waitForProcess child >> pure ()))

nativeProcesses :: Bool -> IO TestResult
nativeProcesses nested = withNativeHome $ \home -> do
    let markers = ["child" ++ show i | i <- [1 .. 4 :: Int]]
        kinds = if nested then ["checker", "emitter", "seed"] else ["single"]
        mode = if nested then "nested" else "shared"
        entry kind = home </> "tersus" </> ("native-probe-" ++ kind ++ "-key")
        built marker kind = home </> (marker ++ "." ++ kind ++ ".built")
    withNativeChildren home [(marker, mode) | marker <- markers] $ \children -> do
        mapM_ (awaitNativeFile . (home </>) . (++ ".started")) markers
        writeFile (home </> "go") ""
        -- Leave the first builder blocked while the other processes reach the cold entry.
        threadDelay 500000
        writeFile (home </> "release") ""
        codes <- mapM (waitChild 15) children
        counts <- mapM (\kind -> length . filter id <$> mapM (\marker -> doesFileExist (built marker kind)) markers) kinds
        results <- mapM (readMarker . (home </>)) markers
        before <- mapM (getModificationTime . entry) kinds
        withNativeChildren home [("warm", mode)] $ \warm -> do
            warmCodes <- mapM (waitChild 15) warm
            warmBuilt <- mapM (doesFileExist . built "warm") kinds
            after <- mapM (getModificationTime . entry) kinds
            names <- listDirectory (home </> "tersus")
            let expected = concat [["native-probe-" ++ kind ++ "-key", "native-probe-" ++ kind ++ "-key.lock"] | kind <- kinds]
            pure $ firstFailure
                [ testAssertEq codes (replicate 4 (Just ExitSuccess))
                , testAssertEq counts (replicate (length kinds) 1)
                , testAssertEq results (replicate 4 (Right (entry (head kinds))))
                , testAssertEq warmCodes [Just ExitSuccess]
                , testAssertEq warmBuilt (replicate (length kinds) False)
                , testAssertEq after before
                , testAssertEq (sort names) (sort expected)
                ]

nativeRecovery :: String -> IO TestResult
nativeRecovery mode = withNativeHome $ \home ->
    withNativeChildren home [("owner", mode)] $ \owners -> do
        let entry = home </> "tersus" </> "native-probe-single-key"
        awaitNativeFile (home </> "owner.single.built")
        when (mode == "hold") $ do
            awaitNativeFile (home </> "owner.pid")
            pid <- read <$> readFile (home </> "owner.pid")
            signalProcess sigKILL pid
        ownerCodes <- mapM (waitChild 15) owners
        absent <- not <$> doesFileExist entry
        withNativeChildren home [("retry", "retry")] $ \children -> do
            codes <- mapM (waitChild 15) children
            rebuilt <- doesFileExist (home </> "retry.single.built")
            contents <- readMarker entry
            pure $ firstFailure
                [ testAssertTrue (all (/= Nothing) ownerCodes)
                , testAssertTrue absent
                , testAssertEq codes [Just ExitSuccess]
                , testAssertTrue rebuilt
                , testAssertEq contents (Right "single")
                ]

nativeThreads :: IO TestResult
nativeThreads = withNativeHome $ \home -> do
    saved <- lookupEnv "XDG_CACHE_HOME"
    let restore = maybe (unsetEnv "XDG_CACHE_HOME") (setEnv "XDG_CACHE_HOME") saved
    (do
        setEnv "XDG_CACHE_HOME" home
        count <- newIORef (0 :: Int)
        let build output = do
                atomicModifyIORef' count (\n -> (n + 1, ()))
                threadDelay 100000
                writeFile output "threads"
                pure (Ok ())
            start = do
                result <- newEmptyMVar
                tid <- forkIO $ do
                    outcome <- try (cachedProgram "native-probe-threads" "key" "thread probe" build) :: IO (Either SomeException (Result FilePath String))
                    putMVar result outcome
                pure (tid, result)
        bracket (mapM (const start) [1 .. 8 :: Int]) (mapM_ (killThread . fst)) $ \threads -> do
            outcomes <- timeout 15000000 (mapM (takeMVar . snd) threads)
            builders <- readIORef count
            pure $ firstFailure
                [ testAssertEq builders 1
                , case outcomes of
                    Just results -> testAssertTrue (all success results)
                    Nothing -> Just "native thread waiters hung"
                ]) `finally` restore
  where
    success (Right (Ok _)) = True
    success _ = False

digestIdentity :: IO TestResult
digestIdentity = do
    home <- freshHome "tersus-shared-cache-digest"
    ( do
        let path = home </> "binary"
            oldTime = read "2000-01-01 00:00:00 UTC"
        writeFile path "abc"
        before <- executableDigest path
        setModificationTime path oldTime
        touched <- executableDigest path
        writeFile path "abd"
        setModificationTime path oldTime
        changed <- executableDigest path
        pure $ firstFailure
            [ testAssertEq before (Just "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
            , testAssertEq touched before
            , testAssertTrue (changed /= Nothing && changed /= before)
            ]) `finally` removeDirectoryRecursive home

unreadableIdentity :: IO TestResult
unreadableIdentity = do
    home <- freshHome "tersus-shared-cache-unreadable"
    (testAssertEq <$> executableDigest (home </> "missing") <*> pure Nothing)
        `finally` removeDirectoryRecursive home

exactKeys :: IO TestResult
exactKeys = do
    files <- mapM (uncurry sharedProgramCacheFile)
        [("compile", "return 1;"), ("compile", "return 2;"), ("validated", "return 1;"), ("compile", "a\0b"), ("compile\0a", "b")]
    pure $ firstFailure
        [ testAssertTrue (all (maybe False ((== 64) . length . takeFileName)) files)
        , testAssertTrue (length (Map.fromList [(file, ()) | file <- files]) == length files)
        ]

touchedExecutable :: IO TestResult
touchedExecutable = do
    home <- freshHome "tersus-shared-cache-touched"
    ( do
        self <- getExecutablePath
        let copied = home </> "tersus-test"
            marker = home </> "marker"
        copyFile self copied
        env <- probeEnv home marker []
        let runChild = readCreateProcessWithExitCode
                (proc copied ["testSharedCacheProbe", "--child", "+RTS", "-N1", "-RTS"]){env = Just env} ""
        (code1, _, err1) <- runChild
        first <- readMarker marker
        entries <- entryFiles home
        case (code1, first, entries) of
            (ExitSuccess, Right original, [entry]) -> do
                before <- getModificationTime entry
                digest <- executableDigest copied
                setModificationTime copied (read "2000-01-01 00:00:00 UTC")
                afterDigest <- executableDigest copied
                (code2, _, err2) <- runChild
                second <- readMarker marker
                after <- getModificationTime entry
                afterEntries <- entryFiles home
                pure $ firstFailure
                    [ testAssertEq code2 ExitSuccess <? err2
                    , testAssertEq second (Right original)
                    , testAssertEq digest afterDigest
                    , testAssertEq after before
                    , testAssertEq afterEntries entries
                    ]
            _ -> pure (Just ("first copied executable failed: " ++ err1 ++ show entries))
        ) `finally` removeDirectoryRecursive home

staleBuildEntry :: IO TestResult
staleBuildEntry = do
    home <- freshHome "tersus-shared-cache-stale"
    ( do
        let marker = home </> "marker"
        firstChild <- spawnProbe home []
        firstCode <- waitChild 300 firstChild
        original <- readMarker marker
        entries <- entryFiles home
        case (firstCode, original, entries) of
            (Just ExitSuccess, Right expected, [entry]) -> do
                Right text <- readMarker entry
                let stale = unlines (head (lines text) : replicate 64 '0' : drop 2 (lines text))
                writeFile entry stale
                child <- spawnProbe home []
                code <- waitChild 300 child
                got <- readMarker marker
                repaired <- readMarker entry
                pure $ firstFailure
                    [ testAssertEq code (Just ExitSuccess)
                    , testAssertEq got (Right expected)
                    , testAssertEq repaired (Right text)
                    ]
            _ -> pure (Just ("could not seed stale entry: " ++ show firstCode ++ show entries))
        ) `finally` removeDirectoryRecursive home

missingHashTools :: IO TestResult
missingHashTools = do
    home <- freshHome "tersus-shared-cache-no-hash"
    ( do
        file <- sharedProgramCacheFile "compile" invalidProbeSource
        rejected <- compileOnce invalidProbeSource
        other <- compileOnce richSource
        case (file, rejected, other) of
            (Just path, Error expected, Ok wrong) -> do
                let marker = home </> "marker"
                    entry = home </> "tersus" </> "test-programs" </> takeFileName path
                    (header, body) = break (== '\n') (encodeProgram wrong)
                    poisoned = header ++ "\n" ++ takeFileName path ++ body
                createDirectoryIfMissing True (takeDirectory entry)
                writeFile entry poisoned
                child <- spawnProbe home [("PATH", home), ("TERSUS_SHARED_CACHE_PROBE_INVALID", "1")]
                code <- waitChild 10 child
                when (code == Nothing) (terminateProcess child >> waitForProcess child >> pure ())
                got <- readMarker marker
                after <- readMarker entry
                afterEntries <- entryFiles home
                pure $ firstFailure
                    [ testAssertEq code (Just ExitSuccess)
                    , testAssertEq got (Right expected)
                    , testAssertEq after (Right poisoned)
                    , testAssertEq afterEntries [entry]
                    ]
            _ -> pure (Just "could not seed a correctly keyed success for the invalid source")
        ) `finally` removeDirectoryRecursive home

roundtrip :: IO TestResult
roundtrip = do
    validated <- validatedOnce richSource
    compiled <- compileOnce richSource
    pure $ case (validated, compiled) of
        (Ok v, Ok _) ->
            firstFailure
                [ testAssertEq (decodeProgram (encodeProgram v)) (Ok v)
                , testAssertTrue (not (Map.null (progGenerics v))) <? "generics were lost"
                , testAssertTrue (not (Map.null (progInvariants v))) <? "invariants were lost"
                , testAssertTrue (hasSpec v) <? "contracts were lost"
                , testAssertTrue (hasGhost v) <? "ghosts were lost from the validated program"
                                ]
        (Error e, _) -> Just e
        (_, Error e) -> Just e
  where
    hasSpec program = any (\fn -> not (null (specRequires (fnSpec fn))) || not (null (specEnsures (fnSpec fn)))) (progMain program : Map.elems (progFunctions program))
    hasGhost program = any (any isGhost . blockStatements) (concatMap (Map.elems . fnBlocks) (progMain program : Map.elems (progFunctions program)))
    isGhost s = case s of
        Ghost _ _ -> True
        _ -> False

infixl 0 <?

(<?) :: TestResult -> String -> TestResult
Nothing <? _ = Nothing
(Just _) <? message = Just message

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [f | Just f <- results] of
    f : _ -> Just f
    [] -> Nothing

sourceChange :: IO TestResult
sourceChange = do
    a <- compileOnce "zx987a = 41; return zx987a + 1;"
    b <- compileOnce "zx987a = 41; return zx987a + 2;"
    pure $ case (a, b) of
        (Ok pa, Ok pb) -> if pa /= pb then Nothing else Just "different sources gave the same program"
        (Error e, _) -> Just e
        (_, Error e) -> Just e

stageIsolation :: IO TestResult
stageIsolation = do
    validated <- validatedOnce richSource
    compiled <- compileOnce richSource
    owned <- ownedOnce richSource
    files <- mapM (\stage -> sharedProgramCacheFile stage richSource) ["validated", "compile", "owned"]
    exist <- mapM (maybe (pure False) doesFileExist) files
    pure $ case (validated, compiled, owned) of
        (Ok v, Ok c, Ok _) ->
            firstFailure
                [ if v /= c then Nothing else Just "validated and compiled programs are the same"
                , if length (filter (maybe False (const True)) files) == 3 && files !! 0 /= files !! 1 && files !! 1 /= files !! 2 then Nothing else Just ("stage cache files are not distinct: " ++ show files)
                , if and exist then Nothing else Just "a stage did not file its entry"
                ]
        (Error e, _, _) -> Just e
        (_, Error e, _) -> Just e
        (_, _, Error e) -> Just e

corruptRecomputes :: IO TestResult
corruptRecomputes = do
    let source = "return 987001;"
    file <- sharedProgramCacheFile "compile" source
    case file of
        Nothing -> pure (Just "no cache directory")
        Just path -> do
            createDirectoryIfMissing True (takeDirectory path)
            writeFile path "garbage, not a program"
            result <- compileOnce source
            pure $ case result of
                Error e -> Just e
                Ok program ->
                    firstFailure
                        [ case decodeProgram (take 40 (encodeProgram program)) of
                            Error _ -> Nothing
                            Ok _ -> Just "a truncated entry decoded"
                        , case decodeProgram "not a program" of
                            Error _ -> Nothing
                            Ok _ -> Just "garbage decoded"
                        ]

poisonedEntry :: IO TestResult
poisonedEntry = do
    let source = "return 987011;"
    other <- compileOnce "return 987012;"
    file <- sharedProgramCacheFile "compile" source
    case (other, file) of
        (Ok program, Just path) -> do
            createDirectoryIfMissing True (takeDirectory path)
            writeFile path (encodeProgram program)
            result <- compileOnce source
            pure $ case result of
                Ok got -> if got /= program then Nothing else Just "a program filed for another source was trusted"
                Error e -> Just e
        (Error e, _) -> pure (Just e)
        (_, Nothing) -> pure (Just "no cache directory")

failedNotFiled :: IO TestResult
failedNotFiled = do
    let source = "zx987b = 1; affirm zx987b = 2; return zx987b;"
    a <- compileOnce source
    b <- compileOnce source
    file <- sharedProgramCacheFile "compile" source
    exists <- maybe (pure False) doesFileExist file
    pure $ case (a, b) of
        (Error _, Error _) -> if exists then Just "a failed compile was filed" else Nothing
        _ -> Just "a bad program compiled"

independentProcesses :: IO TestResult
independentProcesses = do
    home <- freshHome "tersus-shared-cache-test"
    let marker = home </> "marker"
    ( do
        self <- getExecutablePath
        env0 <- getEnvironment
        let childEnv = ("XDG_CACHE_HOME", home) : ("TERSUS_SHARED_CACHE_PROBE", marker) : [(k, v) | (k, v) <- env0, k /= "XDG_CACHE_HOME", k /= "TERSUS_SHARED_CACHE_PROBE"]
            runChild = readCreateProcessWithExitCode (proc self ["testSharedCacheProbe", "--child", "+RTS", "-N1", "-RTS"]){env = Just childEnv} ""
        (code1, _, err1) <- runChild
        first <- try (readFile marker >>= \t -> length t `seq` pure t) :: IO (Either IOError String)
        entries <- entryFiles home
        case (code1, first, entries) of
            (ExitSuccess, Right text1, [entry]) -> do
                before <- getModificationTime entry
                (code2, _, err2) <- runChild
                second <- try (readFile marker >>= \t -> length t `seq` pure t) :: IO (Either IOError String)
                after <- getModificationTime entry
                pure $ case (code2, second) of
                    (ExitSuccess, Right text2)
                        | text1 /= text2 -> Just "the second process wrote a different program"
                        | before /= after -> Just "the second process rewrote the cache entry instead of reusing it"
                        | otherwise -> Nothing
                    _ -> Just ("the second child failed: " ++ err2)
            _ -> pure (Just ("the first child failed: " ++ err1 ++ " entries " ++ show entries)))
        `finally` removeDirectoryRecursive home

concurrentProcesses :: IO TestResult
concurrentProcesses = do
    home <- freshHome "tersus-shared-cache-concurrent"
    ( do
        handles <- mapM (\i -> spawnProbe home [("TERSUS_SHARED_CACHE_PROBE", home </> ("marker" ++ show i))]) [1 .. 4 :: Int]
        codes <- mapM (waitChild 300) handles
        markers <- mapM (readMarker . \i -> home </> ("marker" ++ show i)) [1 .. 4 :: Int]
        entries <- entryFiles home
        pure $ case (codes, markers, entries) of
            ([Just ExitSuccess, Just ExitSuccess, Just ExitSuccess, Just ExitSuccess], [Right a, Right b, Right c, Right d], [_]) ->
                if a == b && b == c && c == d
                    then case decodeProgram a of
                        Ok _ -> Nothing
                        Error e -> Just e
                    else Just "concurrent processes wrote different programs"
            _ -> Just ("concurrent children failed: " ++ show codes))
        `finally` removeDirectoryRecursive home

killedOwnerReleases :: IO TestResult
killedOwnerReleases = do
    home <- freshHome "tersus-shared-cache-killed"
    ( do
        entryName <- maybe "" takeFileName <$> sharedProgramCacheFile "compile" probeSource
        let lockPath = home </> "tersus" </> "test-programs" </> (entryName ++ ".lock")
            holderMarker = home </> "holder-marker"
        createDirectoryIfMissing True (takeDirectory lockPath)
        holder <- spawnProbe home [("TERSUS_SHARED_CACHE_PROBE", holderMarker), ("TERSUS_SHARED_CACHE_PROBE_HOLD", lockPath)]
        holding <- waitForFile (holderMarker ++ ".holding") 100
        if not holding
            then do
                terminateProcess holder
                pure (Just "the holder never took the lock")
            else do
                waiter <- spawnProbe home [("TERSUS_SHARED_CACHE_PROBE", home </> "waiter-marker")]
                threadDelay 1000000
                terminateProcess holder
                code <- waitChild 300 waiter
                entries <- entryFiles home
                marker <- readMarker (home </> "waiter-marker")
                pure $ case (code, entries, marker) of
                    (Just ExitSuccess, [_], Right _) -> Nothing
                    _ -> Just ("the waiter did not finish after the owner was killed: " ++ show code ++ " entries " ++ show entries))
        `finally` removeDirectoryRecursive home
  where
    waitForFile path tries
        | tries <= 0 = pure False
        | otherwise = do
            present <- doesFileExist path
            if present then pure True else threadDelay 100000 >> waitForFile path (tries - 1)

unusableLockFallsBack :: IO TestResult
unusableLockFallsBack = do
    home <- freshHome "tersus-shared-cache-unusable"
    saved <- lookupEnv "XDG_CACHE_HOME"
    let restore = maybe (unsetEnv "XDG_CACHE_HOME") (setEnv "XDG_CACHE_HOME") saved
    let action = do
            setEnv "XDG_CACHE_HOME" home
            let source = "return 987031;"
            file <- sharedProgramCacheFile "compile" source
            case file of
                Nothing -> pure (Just "no cache directory")
                Just path -> do
                    -- a directory where the lock file belongs cannot be opened for locking
                    createDirectoryIfMissing True (path ++ ".lock")
                    result <- timeout 60000000 (compileOnce source)
                    exists <- doesFileExist path
                    pure $ case result of
                        Just (Ok _) -> if exists then Just "an entry was filed despite the unusable lock" else Nothing
                        Just (Error e) -> Just e
                        Nothing -> Just "computing with an unusable lock hung"
    (action `finally` restore) `finally` removeDirectoryRecursive home


seedHome :: FilePath -> IO ()
seedHome home = do
    seedFile <- sharedProgramCacheFile "compile" probeSource
    case seedFile of
        Just path -> do
            let realCache = takeDirectory (takeDirectory path)
            names <- listDirectory realCache
            createDirectoryIfMissing True (home </> "tersus")
            mapM_ (\name -> do
                let from = realCache </> name
                isFile <- doesFileExist from
                when isFile (copyFile from (home </> "tersus" </> name))) names
        Nothing -> pure ()

freshHome :: String -> IO FilePath
freshHome name = do
    tmp <- getTemporaryDirectory
    let home = tmp </> name
    exists <- doesDirectoryExist home
    when exists (removeDirectoryRecursive home)
    createDirectoryIfMissing True home
    seedHome home
    pure home

probeEnv :: FilePath -> FilePath -> [(String, String)] -> IO [(String, String)]
probeEnv home marker extra = do
    env0 <- getEnvironment
    pure (("XDG_CACHE_HOME", home) : ("TERSUS_SHARED_CACHE_PROBE", marker) : extra ++ [(k, v) | (k, v) <- env0, k /= "XDG_CACHE_HOME", k /= "TERSUS_SHARED_CACHE_PROBE", k `notElem` map fst extra])

spawnProbe :: FilePath -> [(String, String)] -> IO ProcessHandle
spawnProbe home extra = do
    self <- getExecutablePath
    let marker = case lookup "TERSUS_SHARED_CACHE_PROBE" extra of
            Just m -> m
            Nothing -> home </> "marker"
    env <- probeEnv home marker extra
    withFile "/dev/null" WriteMode $ \sink -> do
        (_, _, _, handle) <- createProcess (proc self ["testSharedCacheProbe", "--child", "+RTS", "-N1", "-RTS"]){env = Just env, std_out = UseHandle sink, std_err = UseHandle sink}
        pure handle

waitChild :: Int -> ProcessHandle -> IO (Maybe ExitCode)
waitChild seconds handle = timeout (seconds * 1000000) (waitForProcess handle)

entryFiles :: FilePath -> IO [FilePath]
entryFiles home = do
    let dir = home </> "tersus" </> "test-programs"
    exists <- doesDirectoryExist dir
    if not exists
        then pure []
        else map (dir </>) . filter (not . isSuffixOf' ".lock") <$> listDirectory dir
  where
    isSuffixOf' suffix name = reverse suffix == take (length suffix) (reverse name)

readMarker :: FilePath -> IO (Either IOError String)
readMarker path = try (readFile path >>= \text -> length text `seq` pure text)

toolValidationParity :: IO TestResult
toolValidationParity =
    let entry = MirHousekeeping.mirEraseEntry
        fresh = case Modules.loadFromEntry (Modules.resolverFromFiles mirPackageFiles) entry of
            Left e -> Error e
            Right (Modules.PackageResult pkg) -> PackageCompile.compileModulesLinked pkg
            Right _ -> Error "the frozen eraser is not a package"
     in pure (testAssertEq (MirHousekeeping.toolProgram entry) fresh)

-- The compiled tools of a cache (the validator, the emitter, the MIR checker
-- and eraser, the seed and the runtime), copied into another
copyCompiledTools :: FilePath -> FilePath -> IO ()
copyCompiledTools from to = do
    createDirectoryIfMissing True to
    names <- listDirectory from
    mapM_ (\name -> do
        regular <- doesFileExist (from </> name)
        when (regular && any (`isPrefixOf` name) ["validator-", "emitter-", "mir-verify-", "mir-erase-", "seed-", "tersus_rt_"] && not (".lock" `isInfixOf` name)) $
            copyFile (from </> name) (to </> name)) names

withCacheHome :: (FilePath -> IO a) -> IO a
withCacheHome use = withNativeHome $ \home -> do
    saved <- lookupEnv "XDG_CACHE_HOME"
    let restore = maybe (unsetEnv "XDG_CACHE_HOME") (setEnv "XDG_CACHE_HOME") saved
    (setEnv "XDG_CACHE_HOME" home >> use home) `finally` restore

packageFixture :: FilePath -> IO (FilePath, FilePath)
packageFixture home = do
    let root = home </> "app"
        entry = root </> "main.tersus"
        dependency = root </> "geo" </> "geo.tersus"
    createDirectoryIfMissing True (takeDirectory dependency)
    writeFile (root </> "package.tersus") ""
    writeFile entry "import app::geo; return geo::value();"
    writeFile dependency "fn value() -> Int { return 1; };"
    pure (entry, dependency)

packageSnapshots :: IO TestResult
packageSnapshots = do
    home <- freshHome "tersus-shared-package-snapshot"
    (do
        (entry, dependency) <- packageFixture home
        first <- validatedFromFile entry
        same <- validatedFromFile entry
        compiled <- programFromFile entry
        owned <- ownedFromFile entry
        writeFile dependency "fn value() -> Int { return 2; };"
        changed <- validatedFromFile entry
        writeFile dependency "fn value() -> Int [{ }] [{ affirm return = 3; }] { return 2; };"
        refused <- validatedFromFile entry
        writeFile dependency "fn value() -> Int { return 2; };"
        writeFile entry "import app::geo::geo::value; return value() + 1;"
        changedEntry <- validatedFromFile entry
        renameFile dependency (takeDirectory dependency </> "renamed.tersus")
        renamed <- validatedFromFile entry
        writeFile entry "import app::geo::renamed::value; return value() + 1;"
        repaired <- validatedFromFile entry
        pure $ case (first, same, compiled, owned, changed, refused, changedEntry, renamed, repaired) of
            (Ok a, Ok b, Ok _, Ok _, Ok c, Error _, Ok d, Error _, Ok _) -> firstFailure
                [testAssertEq a b, testAssertTrue (a /= c), testAssertTrue (c /= d)]
            _ -> Just "a changed dependency, contract, entry, import or filename reused the wrong package result")
        `finally` removeDirectoryRecursive home

packageAliases :: IO TestResult
packageAliases = do
    let marker = ("cache_alias/package.tersus", "")
        one = ("cache_alias/main.tersus", "return 1;")
        two = ("cache_alias/./main.tersus", "return 2;")
    first <- ownedFromFiles "cache_alias/main.tersus" [marker, one, two]
    second <- ownedFromFiles "cache_alias/main.tersus" [marker, two, one]
    alias <- ownedFromFiles "cache_alias/./main.tersus"
        [("cache_alias/./package.tersus", ""), ("cache_alias/main.tersus", "return 2;")]
    pure $ case (first, second, alias) of
        (Ok a, Ok b, Ok c) -> firstFailure [testAssertTrue (a /= b), testAssertEq a c]
        _ -> Just "duplicate or normalized paths selected the wrong package contents"

-- Exercise the complete snapshot through one validated cache entry; parser
-- bootstrap and native erasure are covered separately, not by these child deadlines.
packageProcesses :: IO TestResult
packageProcesses = do
    home <- freshHome "tersus-shared-package-processes"
    (do
        (entry, _) <- packageFixture home
        let run = do
                child <- spawnProbe home [("TERSUS_PACKAGE_CACHE_PROBE", entry), ("TERSUS_PARSER", "haskell")]
                code <- waitChild 300 child
                marker <- readMarker (home </> "marker")
                files <- entryFiles home
                times <- mapM getModificationTime files
                pure (code, marker, sort files, times)
        first <- run
        second <- run
        pure $ case (first, second) of
            ((Just ExitSuccess, Right a, files, times), (Just ExitSuccess, Right b, files', times')) ->
                firstFailure [testAssertEq a b, testAssertTrue (length files == 1), testAssertEq files files', testAssertEq times times']
            _ -> Just "package probes failed or did not reuse their cache entry")
        `finally` removeDirectoryRecursive home

parserRetry :: IO TestResult
parserRetry = do
    home <- freshHome "tersus-shared-parser-retry"
    (do
        child <- spawnProbe home [("TERSUS_SHARED_CACHE_PARSER_RETRY", "1")]
        code <- waitChild 300 child
        pure (testAssertEq code (Just ExitSuccess))) `finally` removeDirectoryRecursive home

parserRetryProbe :: IO TestResult
parserRetryProbe = do
    Just home <- lookupEnv "XDG_CACHE_HOME"
    primed <- TersusParser.runParserTool False ["return 0;"]
    case primed of
        Left e -> pure (Just e)
        Right _ -> do
            let parser = home </> "tersus" </> ("tersus-parser-" ++ TersusParser.parserHash)
                source = "return 987823;"
            before <- bracket (renameFile parser (parser ++ ".held"))
                (\_ -> renameFile (parser ++ ".held") parser)
                (\_ -> compileOnce source)
            after <- compileOnce source
            pure $ case (before, after) of
                (Error e, Ok _) | "Parser tool failure:" `isPrefixOf` e -> Nothing
                _ -> Just ("native parser retry: before=" ++ describe before ++ "; after=" ++ describe after)
  where
    describe (Error e) = e
    describe (Ok _) = "success"

ciPackageFixture :: FilePath -> IO (FilePath, FilePath)
ciPackageFixture home = do
    let root = home </> "pkg"
        entry = root </> "main.tersus"
        dependency = root </> "helper" </> "helper.tersus"
    createDirectoryIfMissing True (takeDirectory dependency)
    writeFile (root </> "package.tersus") ""
    writeFile entry "import pkg::helper::answer; return answer();"
    writeFile dependency "fn answer() -> Int [{ }] [{ }] { return 41; };"
    pure (entry, dependency)

packageStages :: IO TestResult
packageStages = withCacheHome $ \home -> do
    (entry, _) <- ciPackageFixture home
    owned <- ownedFromFile entry
    program <- programFromFile entry
    validated <- validatedFromFile entry
    sources <- Modules.snapshotFromFilesystem entry
    files <- mapM (\stage -> sharedProgramCacheFile ("package-" ++ stage)
        (packageCacheInput entry sources)) ["owned", "program", "validated"]
    present <- mapM (maybe (pure False) doesFileExist) files
    pure $ case (owned, program, validated) of
        (Ok _, Ok _, Ok original) -> firstFailure
            [ testAssertTrue (and present && length (Map.fromList [(file, ()) | Just file <- files]) == 3)
            , testAssertEq (decodeProgram (encodeProgram original)) (Ok original)
            ]
        other -> Just (show other)

packageInputs :: IO TestResult
packageInputs = withCacheHome $ \home -> do
    (entry, dependency) <- ciPackageFixture home
    original <- validatedFromFile entry
    writeFile dependency "fn answer() -> Int [{ }] [{ }] { return 42; };"
    changed <- validatedFromFile entry
    writeFile dependency "fn answer() -> Int [{ }] [{ }] { affirm 1 = 2; return 41; };"
    invalid <- validatedFromFile entry
    sources <- Modules.snapshotFromFilesystem entry
    invalidFile <- sharedProgramCacheFile "package-validated" (packageCacheInput entry sources)
    filed <- maybe (pure False) doesFileExist invalidFile
    writeFile dependency "fn answer() -> Int [{ }] [{ }] { return 41; };"
    writeFile (takeDirectory dependency </> "extra.tersus") "fn extra() -> Int { return 1; };"
    layoutChanged <- validatedFromFile entry
    removeFile (takeDirectory dependency </> "extra.tersus")
    restored <- validatedFromFile entry
    pure $ case (original, changed, invalid, layoutChanged, restored) of
        (Ok a, Ok b, Error _, Error _, Ok c) ->
            testAssertTrue (a /= b && a == c && not filed)
        other -> Just (show other)

ciPackageProcesses :: Bool -> IO TestResult
ciPackageProcesses concurrent = do
  -- (validation runs the validator written in Tersus, compiled once into the
  -- cache: the fresh cache homes of the probes are given the compiled tools,
  -- which are not what this test measures, so that each probe has 30 seconds
  -- for the package)
  warm <- compileOnce "return 0;"
  original <- cacheDirectory
  withCacheHome $ \home -> do
    case (warm, original) of
        (Ok _, Ok dir) -> copyCompiledTools dir (home </> "tersus")
        _ -> pure ()
    (entry, _) <- ciPackageFixture home
    let markers = if concurrent then ["first" ++ show i | i <- [1 .. 4 :: Int]] else ["first"]
        extra marker = [("TERSUS_PACKAGE_CACHE_PROBE", entry), ("TERSUS_SHARED_CACHE_PROBE", home </> marker), ("TERSUS_PARSER", "haskell")]
    bracket (mapM (spawnProbe home . extra) markers)
        (mapM_ (\child -> terminateProcess child >> waitForProcess child >> pure ())) $ \children -> do
        codes <- mapM (waitChild 30) children
        outputs <- mapM (readMarker . (home </>)) markers
        entries <- entryFiles home
        before <- mapM getModificationTime entries
        bracket (spawnProbe home (extra "warm"))
            (\child -> terminateProcess child >> waitForProcess child >> pure ()) $ \child -> do
            warmCode <- waitChild 30 child
            warmOutput <- readMarker (home </> "warm")
            after <- mapM getModificationTime entries
            pure $ firstFailure
                [ testAssertEq codes (replicate (length markers) (Just ExitSuccess))
                , testAssertEq warmCode (Just ExitSuccess)
                , testAssertTrue (length entries == 1 && all (== warmOutput) outputs)
                , testAssertEq after before
                ]

embeddedInputs :: IO TestResult
embeddedInputs = do
    loaded <- loadFromFilesystem emitterEntry
    pure $ case loaded of
        Left e -> Just e
        Right (StandaloneResult _ _) -> Just "the embedded emitter is not a package"
        Right (PackageResult pkg) ->
            let sourceChanged = pkg{packageModules = map changeModule (packageModules pkg)}
                changeModule modu = modu{loadedModuleFiles = map (\file -> file{loadedFileSource = loadedFileSource file ++ "\n"}) (loadedModuleFiles modu)}
                identityChanged = pkg{packageEntryModule = ModuleId "different" Nothing}
             in testAssertTrue (matchesEmbeddedPackage emitterEntry pkg
                && not (matchesEmbeddedPackage emitterEntry sourceChanged)
                && not (matchesEmbeddedPackage emitterEntry identityChanged))

packageDuplicateKeys :: IO TestResult
packageDuplicateKeys = pure $ testAssertTrue
    ( packageCacheInput "pkg/./main.tersus" [("pkg/./main.tersus", "old"), ("pkg/main.tersus", "new")]
        == packageCacheInput "pkg/main.tersus" [("pkg/main.tersus", "new")]
      && packageCacheInput "pkg/main.tersus" [("pkg/main.tersus", "old"), ("pkg/main.tersus", "new")]
        /= packageCacheInput "pkg/main.tersus" [("pkg/main.tersus", "new"), ("pkg/main.tersus", "old")])

embeddedChangedSource :: IO TestResult
embeddedChangedSource = withCacheHome $ \_ -> do
    let changed = [(path, if path == emitterEntry
            then "import mir::reader::reader; return missingEmbedProvider();" else source)
            | (path, source) <- mirPackageFiles]
    result <- ownedFromFiles emitterEntry changed
    file <- sharedProgramCacheFile "package-validated" (packageCacheInput emitterEntry changed)
    filed <- maybe (pure False) doesFileExist file
    pure (firstFailure [testAssertErrorContains "missingEmbedProvider" result,
        testAssertTrue (not filed)])

mutatedStillVerified :: IO TestResult
mutatedStillVerified = do
    owned <- ownedOnce "fn double987(n: Int) -> Int [{ }] [{ }] { return n + n; }; return double987(3);"
    pure $ case owned of
        Error e -> Just e
        Ok program ->
            let mutated = program{progMain = change (progMain program)}
                change fn = case Map.keys (fnLocals fn) of
                    [] -> fn
                    local : _ -> fn{fnLocals = Map.adjust (\decl -> decl{localType = TVar 0}) local (fnLocals fn)}
             in firstFailure
                    [ case verifyProgram (forNative program) of
                        Ok () -> Nothing
                        Error e -> Just ("the unmutated program was refused: " ++ e)
                    , case verifyProgram (forNative mutated) of
                        Ok () -> Just "the mutated program was accepted"
                        Error _ -> Nothing
                    ]
