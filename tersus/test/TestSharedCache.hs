module TestSharedCache (testSharedCache, testSharedCacheProbe) where

import Control.Concurrent (threadDelay)
import Control.Exception (finally, try)
import Control.Monad (when)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import System.Directory (copyFile, createDirectoryIfMissing, doesDirectoryExist, doesFileExist, getModificationTime, getTemporaryDirectory, listDirectory, removeDirectoryRecursive, removeFile, setModificationTime)
import System.Environment (getEnvironment, getExecutablePath, lookupEnv, setEnv, unsetEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>), takeDirectory, takeFileName)
import System.IO (SeekMode (AbsoluteSeek))
import System.Posix.IO (LockRequest (WriteLock), closeFd, waitToSetLock)
import System.Process (CreateProcess (..), ProcessHandle, createProcess, proc, readCreateProcessWithExitCode, terminateProcess, waitForProcess)
import System.Timeout (timeout)

import Mir (BasicBlock (..), BlockId (..), Function (..), FunctionSpec (..), LocalDecl (..), Program (..), Statement (..))
import qualified Mir as Mir
import MirHousekeeping (verifyProgram)
import MirData (forNative)
import TestHarness
import Types (Type (..))
import Utils

richSource :: String
richSource = "struct Packet<n> { body: Array<Int, n> }; struct S { n: Int } invariant [{ affirm n >= 0; }]; fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n; }; p = Packet<2> { body: #[1, 2] }; s = S { n: f(get(p.body, 0)) }; return s.n;"

probeSource :: String
probeSource = "return 987021;"

testSharedCache :: Test
testSharedCache =
    TestList
        "testSharedCache"
        [ TestCase "lossless roundtrip keeps contracts, invariants, generics and ghosts" roundtrip
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
        ]

testSharedCacheProbe :: Test
testSharedCacheProbe = TestList "testSharedCacheProbe" [TestCase "probe" probe]

probe :: IO TestResult
probe = do
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
            result <- compileOnce probeSource
            case result of
                Error e -> pure (Just e)
                Ok program -> do
                    writeFile path (encodeProgram program)
                    pure Nothing

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
        let marker = home </> "marker"
        firstChild <- spawnProbe home []
        firstCode <- waitChild 300 firstChild
        original <- readMarker marker
        entries <- entryFiles home
        other <- compileOnce "return 987099;"
        case (firstCode, original, entries, other) of
            (Just ExitSuccess, Right expected, [entry], Ok wrong) -> do
                Right text <- readMarker entry
                let poisoned = unlines (take 2 (lines text)) ++ show wrong ++ "\n"
                writeFile entry poisoned
                child <- spawnProbe home [("PATH", home)]
                code <- waitChild 300 child
                got <- readMarker marker
                after <- readMarker entry
                afterEntries <- entryFiles home
                pure $ firstFailure
                    [ testAssertEq code (Just ExitSuccess)
                    , testAssertEq got (Right expected)
                    , testAssertEq after (Right poisoned)
                    , testAssertEq afterEntries entries
                    ]
            _ -> pure (Just ("could not seed missing-hash test: " ++ show firstCode ++ show entries))
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
    (_, _, _, handle) <- createProcess (proc self ["testSharedCacheProbe", "--child", "+RTS", "-N1", "-RTS"]){env = Just env}
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
