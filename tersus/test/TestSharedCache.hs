-- Scoped retry actions must not share a forced unsafePerformIO pipeline failure.
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
module TestSharedCache (testSharedCache, testSharedCacheCodec, testSharedCacheProbe, testVerdictLocks, testPhase1Cache) where

import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as BC
import qualified TestProgramBinary as ProgramBinary
import TestProgramBinaryChecks (binaryChecks, richProgram)
import TestProgramBuildIdentity (concreteBuildIdentity)
import Control.DeepSeq (force)
import qualified Control.Exception as Exception
import Control.Concurrent (MVar, ThreadId, forkFinally, forkIOWithUnmask, forkIO, killThread, newEmptyMVar, newMVar, putMVar, takeMVar, threadDelay, tryPutMVar, yield)
import Control.Concurrent.MVar (modifyMVar, readMVar, tryReadMVar)
import Control.Exception (IOException, MaskingState (..), SomeException, bracket, bracketOnError, displayException, finally, getMaskingState, mask, mask_, throwIO, try)
import Control.Monad (forever, when, forM)
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.Maybe (isNothing)
import Data.Char (isSpace, ord)
import Numeric (showHex)
import GHC.IO.Handle (hDuplicate, hDuplicateTo)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, sort)
import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import PreludeSource (mirPackageFiles, listsSource, boxSource, validationPackageFiles)
import Seed (compilerSnapshotHash, parserSeedHash)
import qualified TestMirReader
import TestNative (runExecutableBytes)
import qualified Seed
import qualified TersusParser
import ElaboratorTool (sourceElaboratorExecutable)
import qualified Modules
import qualified Compile
import qualified Pipeline
import qualified Bootstrap
import GHC.Clock (getMonotonicTime)
import qualified PackageCompile
import qualified MirHousekeeping
import qualified Data.Map.Strict as Map
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist, findExecutable, getModificationTime, getPermissions, getTemporaryDirectory, listDirectory, removeDirectoryRecursive, removeFile, renameFile, setModificationTime, setPermissions, withCurrentDirectory)
import System.Environment (getEnvironment, getExecutablePath, lookupEnv, setEnv, unsetEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>), takeDirectory, takeFileName)
import System.IO (Handle, IOMode (ReadMode, WriteMode), SeekMode (AbsoluteSeek), hClose, hSetBinaryMode, stdin, withFile)
import CacheLock (copyFileCloexec, openTempFileCloexec, withExecutableTempFile, withExecutableWrite, withSpawnShared)
import System.Posix.Files (setFileMode)
import System.Posix.IO (LockRequest (WriteLock), closeFd, waitToSetLock)
import System.Posix.Process (exitImmediately, getProcessID)
import System.Posix.Types (ProcessID)
import System.Process (CreateProcess (..), ProcessHandle, StdStream (NoStream, UseHandle), getPid, getProcessExitCode, proc, waitForProcess)
import System.Timeout (timeout)

import GHC.Conc (getNumCapabilities, setNumCapabilities)
import Modules (LoadResult (..), LoadedPackage (..), LoadedModule (..), LoadedFile (..), ModuleId (..), loadFromFilesystem, normalizePath, snapshotFromFilesystem)
import MirHousekeeping (emitterEntry)
import Mir (BasicBlock (..), BlockId (..), Function (..), FunctionSpec (..), LocalDecl (..), Program (..), Statement (..))
import qualified Mir as Mir
import MirHousekeeping (verifyProgram)
import Native (availableProcessors, cacheDirectory, cachedProgram, cachedProgramWithArtifacts, cachedProgramIfPresentWithArtifacts, parallelBuilds, readProcessOutput, runCommandWithInputFull, runExecutable, runWithInputFull, spawnShared, stopOwnedProcess, validSignalTarget, withSpawnedProcess)
import qualified MirEval
import MirData (forNative, writeProgram)
import TestHarness
import Types (Type (..))
import Utils
import ValidatorNative (withVerdictLock)
import qualified ValidatorNative

richSource :: String
richSource = "struct Packet<n> { body: Array<Int, n> }; struct S { n: Int } invariant [{ affirm n >= 0; }]; fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n; }; p = Packet<2> { body: #[1, 2] }; s = S { n: f(get(p.body, 0)) }; return s.n;"

probeSource :: String
probeSource = "return 987021;"

invalidProbeSource :: String
invalidProbeSource = "return missing_hash_probe_987099(;"

testPhase1Cache :: Test
testPhase1Cache = TestList "testPhase1Cache"
    [ TestCase "source unit no-prelude policy isolates validated and compiled cache entries" phase1SourceCache
    , TestCase "selected roots markers sources and resolution conflicts govern no-prelude package reuse" (phase1PackageCache True)
    , TestCase "default package context does not widen filesystem source capture or mask new candidates" (phase1PackageCache False)
    , TestCase "native executable warm keys avoid P0 bodies and retain source and marker invalidation" nativeSnapshotReuse
    , TestCase "filesystem validator warm hits retain all helpers without another P1 body request" filesystemWarmParserReuse
    , TestCase "filesystem snapshot keys bind structure and misses parse exactly their captured bytes" filesystemSnapshotMisses
    , TestCase "in-memory default cached program and ownership ignore unimported declarations and match filesystem loading" phase1InMemoryCache
    ]

nativeSnapshotReuse :: IO TestResult
nativeSnapshotReuse = withToolsCacheHome $ \home -> do
    python <- findExecutable "python3"
    parser <- Seed.cachedParserSeed
    case (python, parser) of
        (Nothing, _) -> pure (Just "python3 is required for the private P0 request observer")
        (_, Error err) -> pure (Just err)
        (Just _, Ok exe) | not ((home ++ "/") `isPrefixOf` exe) -> pure (Just "P0 observation requires a private copied cache")
        (Just py, Ok exe) -> do
            let delegated = exe ++ ".native"
                requests = home </> "p0-bodies"
                entry = home </> "app" </> "source.tersus"
                count = do
                    present <- doesFileExist requests
                    if present then readFile requests >>= Exception.evaluate . length . lines else pure 0
                proxy = unlines
                    [ "#!" ++ py
                    , "import os, subprocess, sys"
                    , "data = sys.stdin.buffer.read()"
                    , "if data.startswith(b'tersus-file-parse 1\\n'):"
                    , "    with open(" ++ show requests ++ ", 'ab') as out: out.write(b'body\\n')"
                    , "status = subprocess.run([" ++ show delegated ++ "] + sys.argv[1:], input=data).returncode"
                    , "if status < 0: os.kill(os.getpid(), -status)"
                    , "sys.exit(status)"
                    ]
                install = withExecutableWrite $ do
                    renameFile exe delegated
                    writeFile exe proxy
                    setFileMode exe 0o700
                restore _ = withExecutableWrite (removeFile exe >> renameFile delegated exe)
                request = TestMirReader.programExecutable entry "snapshot-reuse"
            bracket install restore $ \_ -> do
                createDirectoryIfMissing True (takeDirectory entry)
                writeFile entry "return 1;"
                first <- request
                before <- count
                second <- request
                after <- count
                writeFile entry "return 2;"
                changed <- request
                actual <- case changed of Error err -> pure (ExitFailure 1, "", err); Ok path -> runExecutableBytes path [] ""
                writeFile entry "affirm 1 = 2; return 2;"
                refused <- request
                writeFile entry "return 2;"
                writeFile (takeDirectory entry </> "package.tersus") "noPrelude = false;"
                marked <- request
                let brokenSeed = home </> "invalid-parser-override.ll"
                writeFile brokenSeed "not a pinned parser seed"
                wrongProducer <- withCacheVariable "TERSUS_PARSER_SEED_FILE" brokenSeed request
                let noise = takeDirectory entry </> "noise" </> "noise.tersus"
                createDirectoryIfMissing True (takeDirectory noise)
                writeFile noise "unread invalid source"
                withNoise <- request
                writeFile noise "different unread invalid source"
                sameNoise <- request
                pure $ firstFailure
                    [ namedResult "native first/second key" (case (first, second) of
                        (Ok a, Ok b) -> testAssertEq a b
                        other -> Just (show other))
                    , namedResult "native warm P0 body requests" (testAssertEq after before)
                    , case (second, changed) of (Ok a, Ok b) -> testAssertTrue (a /= b); other -> Just (show other)
                    , testAssertEq actual (ExitSuccess, "2\n", "")
                    , testAssertErrorContains "Could not prove:" refused
                    , case (changed, marked) of (Ok a, Ok b) -> testAssertTrue (a /= b); other -> Just (show other)
                    , testAssertErrorContains "Could not verify the native test build identity or seed overrides" wrongProducer
                    , namedResult "native unrelated body key" (testAssertEq withNoise sameNoise)
                    ]

filesystemCacheFile :: Modules.LoadOptions -> String -> FilePath -> IO (Maybe FilePath)
filesystemCacheFile options stage entry = do
    input <- filesystemPackageCacheInput options entry
    case input of
        Error err -> fail err
        Ok key -> sharedProgramCacheFile ("package-" ++ stage) key

filesystemWarmParserReuse :: IO TestResult
filesystemWarmParserReuse = withNativeHome $ \home -> withCurrentDirectory home $ do
    mapM_ (\(path, source) -> createDirectoryIfMissing True (takeDirectory path) >> writeFile path source) validationPackageFiles
    requests <- newIORef (0 :: Int)
    let beforeParse = atomicModifyIORef' requests (\n -> (n + 1, ()))
        request = programFromFilesystemObserved beforeParse Modules.defaultLoadOptions MirHousekeeping.validationEntry
    first <- request
    before <- readIORef requests
    second <- request
    after <- readIORef requests
    pure $ case (first, second) of
        (Ok a, Ok b) -> firstFailure
            [ testAssertTrue (before > 0)
            , testAssertEq after before
            , testAssertEq a b
            , testAssertEq (Map.size (progFunctions a)) 884
            , testAssertTrue (all (`Map.member` progFunctions a) ["safeProduct", "containsValue", "commonContext", "driverReadAll"])
            ]
        other -> Just (show other)

filesystemSnapshotMisses :: IO TestResult
filesystemSnapshotMisses = withNativeHome $ \home -> do
    (entry, dependency) <- packageFixture home
    let original = "import app::geo; return geo::value();"
        noise = takeDirectory entry </> "noise" </> "noise.tersus"
    createDirectoryIfMissing True (takeDirectory noise)
    writeFile noise "unread invalid source"
    requests <- newIORef (0 :: Int)
    changed <- newIORef False
    let beforeParse = do
            atomicModifyIORef' requests (\n -> (n + 1, ()))
            first <- atomicModifyIORef' changed (\done -> (True, not done))
            when first (writeFile entry "return missingCapturedSource();")
        request = programFromFilesystemObserved beforeParse Modules.defaultLoadOptions entry
    first <- request
    before <- readIORef requests
    changedResult <- request
    afterChange <- readIORef requests
    writeFile entry original
    restored <- request
    beforeNoise <- readIORef requests
    writeFile noise "different unread invalid source"
    noiseResult <- request
    afterNoise <- readIORef requests
    writeFile dependency "fn value() -> Int { affirm 1 = 2; return 1; };"
    falseResult <- request
    afterFalse <- readIORef requests
    writeFile dependency "fn value() -> Int { return 1; };"
    writeFile (takeDirectory entry </> "geo.tersus") "fn extra() -> Int { return 9; };"
    competitor <- request
    pure $ firstFailure
        [ testAssertEq (first `bindResult` MirEval.runProgram) (Ok (Just (MirEval.MInt 1)))
        , testAssertErrorContains "missingCapturedSource" changedResult
        , testAssertTrue (afterChange > before)
        , testAssertEq first restored
        , testAssertEq restored noiseResult
        , testAssertEq afterNoise beforeNoise
        , testAssertErrorContains "Could not prove:" falseResult
        , testAssertTrue (afterFalse > afterNoise)
        , testAssertErrorContains "ambiguous import:" competitor
        ]

phase1SourceCache :: IO TestResult
phase1SourceCache = withToolsCacheHome $ \_ -> do
    let source = "return 991421;"
        invalid = "affirm 1 = 2; return 991421;"
    ordinary <- compileOnceNoPrelude False source
    optedOut <- compileOnceNoPrelude True source
    replay <- compileOnceNoPrelude True source
    ordinaryName <- compileOnceNoPrelude False "return hashCombine(1, 2);"
    refusedName <- compileOnceNoPrelude True "return hashCombine(1, 2);"
    refused <- validatedOnceNoPrelude True invalid
    keys <- mapM (\stage -> sharedProgramCacheFile stage source) ["compile", "compile-no-prelude", "validated", "validated-no-prelude"]
    badKey <- sharedProgramCacheFile "validated-no-prelude" invalid
    badPresent <- maybe (pure False) doesFileExist badKey
    pure $ case (ordinary, optedOut, replay) of
        (Ok normal, Ok independent, Ok again) -> testAssertEq (MirEval.runProgram normal) (MirEval.runProgram independent)
            <> testAssertEq independent again
            <> testAssertEq (MirEval.runProgram independent) (Ok (Just (MirEval.MInt 991421)))
            <> testAssertTrue (all (/= Nothing) keys && length (Map.fromList [(key, ()) | key <- keys]) == 4)
            <> strictValidation refused <> testAssertTrue (not badPresent)
            <> (case ordinaryName of Ok _ -> Nothing; Error err -> Just err)
            <> (case refusedName of Error err | "Undefined variable: hashCombine" `isInfixOf` err -> Nothing; other -> Just ("implicit name reused across policy: " ++ show other))
        other -> Just (show other)
  where
    strictValidation (Error err) | "Could not prove:" `isInfixOf` err = Nothing
    strictValidation other = Just ("no-prelude validation did not refuse the actual false assertion: " ++ show other)

phase1InMemoryCache :: IO TestResult
phase1InMemoryCache = withToolsCacheHome $ \home -> do
    let app = home </> "app"
        vendor = home </> "vendor"
        entry = app </> "main.tersus"
        unused = app </> "unused" </> "unused.tersus"
        files =
            [ (app </> "package.tersus", "")
            , (entry, "import vendor::api; return api::answer();")
            , (vendor </> "package.tersus", "noPrelude = true;")
            , (vendor </> "api" </> "api.tersus", "fn answer() -> Int { return 42; };")
            , (unused, "enum Secret { A { n: Int }, B };")
            ]
        changed = [(path, if path == unused then "struct Secret { flag: Bool };" else source) | (path,source) <- files]
        input = packageCacheInput entry files
    mapM_ (\(path, source) -> createDirectoryIfMissing True (takeDirectory path) >> writeFile path source) files
    before <- programFromFiles entry files
    ownedBefore <- ownedFromFiles entry files
    keys <- mapM (\stage -> sharedProgramCacheFile ("package-" ++ stage) input) ["program", "owned"]
    times <- mapM (mapM getModificationTime) keys
    after <- programFromFiles entry changed
    ownedAfter <- ownedFromFiles entry changed
    timesAfter <- mapM (mapM getModificationTime) keys
    fromDisk <- Pipeline.loadFromFilesystem entry
    let loaded = Pipeline.loadFromEntry (Modules.resolverFromFiles files) entry
        identity value = case value of
            Right (PackageResult pkg) -> Right (Modules.packageInputIdentity pkg)
            Left err -> Left err
            Right _ -> Left "expected package"
    pure $ firstFailure
        [ testAssertEq (before `bindResult` MirEval.runProgram) (Ok (Just (MirEval.MInt 42)))
        , sameProgram before after
        , sameProgram ownedBefore ownedAfter
        , case ownedBefore of Error err -> Just err; Ok _ -> Nothing
        , testAssertEq (packageCacheInput entry changed) input
        , testAssertTrue (all (/= Nothing) keys && times == timesAfter)
        , testAssertEq (identity fromDisk) (identity loaded)
        , case loaded of Right (PackageResult pkg) -> testAssertTrue (unused `notElem` map fst (Modules.packageSources pkg)); _ -> Just "default in-memory load failed"
        ]

phase1PackageCache :: Bool -> IO TestResult
phase1PackageCache noPrelude = withToolsCacheHome $ \home -> do
    let project = home </> "project"
        app = project </> "app"
        vendor = home </> "installed-v1"
        vendor2 = home </> "installed-v2"
        entry = app </> "main.tersus"
        dependency = vendor </> "api" </> "api.tersus"
        marker = vendor </> "package.tersus"
        options = Modules.defaultLoadOptions{Modules.packageRoots = Map.singleton "vendor" vendor, Modules.noPrelude = noPrelude}
        write path text = createDirectoryIfMissing True (takeDirectory path) >> writeFile path text
        request config = do
            loaded <- Pipeline.loadFromFilesystemWithOptions config entry
            result <- programFromFilesystemWith config entry
            case loaded of
                Right (PackageResult pkg) -> do
                    key <- filesystemCacheFile config "program" entry
                    pure (result, key, Modules.packageSources pkg)
                _ -> pure (result, Nothing, [])
        resultValue (Ok program, _, _) = MirEval.runProgram program
        resultValue (Error err, _, _) = Error err
        resultKey (_, key, _) = key
    write (app </> "package.tersus") ""
    write entry "import vendor::api; return api::answer();"
    write marker "noPrelude = true;"
    write dependency "fn answer() -> Int { return 42; };"
    write (vendor </> "unused-root.tersus") "unrelated root body is deliberately not valid source"
    write (project </> "noise" </> "package.tersus") "noPrelude = invalid;"
    write (project </> "noise" </> "noise.tersus") "not a program"
    write (app </> "unused" </> "unused.tersus") "also not a program"
    before@(_, beforeKey, selected) <- request options
    beforeTime <- mapM getModificationTime beforeKey
    write (project </> "noise" </> "noise.tersus") "changed unrelated sibling"
    write (app </> "unused" </> "unused.tersus") "changed unreachable module"
    write (vendor </> "unused-root.tersus") "changed unreachable noncandidate root body"
    after <- request options
    afterTime <- mapM getModificationTime (resultKey after)
    write dependency "fn answer() -> Int { return 43; };"
    changed <- request options
    write marker "noPrelude = false;"
    configured <- request options
    write (vendor2 </> "package.tersus") "noPrelude = true;"
    write (vendor2 </> "api" </> "api.tersus") "fn answer() -> Int { return 42; };"
    rerooted <- request options{Modules.packageRoots = Map.singleton "vendor" vendor2}
    write marker "noPrelude = true;"
    write dependency "fn answer() -> Int { affirm 1 = 2; return 43; };"
    invalid <- request options
    invalidPresent <- maybe (pure False) doesFileExist (resultKey invalid)
    write dependency "fn answer() -> Int { return 42; };"
    write (vendor </> "api.tersus") "fn answer() -> Int { return 99; };"
    (ambiguous, _, _) <- request options
    removeFile (vendor </> "api.tersus")
    write (project </> "vendor" </> "package.tersus") ""
    write (project </> "vendor" </> "api" </> "api.tersus") "fn answer() -> Int { return 99; };"
    (conflict, _, _) <- request options
    pure $ firstFailure
        [ testAssertEq (resultValue before) (Ok (Just (MirEval.MInt 42)))
        , testAssertEq (resultValue after) (resultValue before)
        , testAssertEq (resultKey after) beforeKey
        , testAssertTrue (beforeKey /= Nothing && beforeTime == afterTime)
        , testAssertTrue (all (\(path, _) -> not ("/noise/" `isInfixOf` path || "/unused/" `isInfixOf` path || "unused-root.tersus" `isSuffixOf` path)) selected)
        , testAssertEq (resultValue changed) (Ok (Just (MirEval.MInt 43)))
        , testAssertTrue (resultKey changed /= beforeKey && resultKey configured /= resultKey changed && resultKey rerooted /= beforeKey)
        , testAssertEq (resultValue configured) (Ok (Just (MirEval.MInt 43)))
        , testAssertEq (resultValue rerooted) (Ok (Just (MirEval.MInt 42)))
        , case invalid of (Error err, _, _) | "Could not prove:" `isInfixOf` err -> Nothing; other -> Just ("invalid dependency was not validated: " ++ show other)
        , testAssertTrue (not invalidPresent)
        , case ambiguous of Error err | "ambiguous import" `isInfixOf` err -> Nothing; other -> Just ("cached sources masked a new file/module candidate: " ++ show other)
        , case conflict of Error err | "conflicting roots" `isInfixOf` err -> Nothing; other -> Just ("cached roots masked a new conflict: " ++ show other)
        ]

testSharedCache :: Test
testSharedCache =
    TestList
        "testSharedCache"
        (codecCases
        ++ [ TestCase "atomic close-on-exec writes keep published tools executable across spawns" atomicExecutableWrites
           , TestCase "cancelled shared readers release executable writers and restore capabilities" cancelledSharedReaders
           , TestCase "captured process input closes on errors and preserves broken-pipe behavior" capturedInputErrors ]
        ++ singleSourceCases
        ++ map requireParser
        [ TestCase "truncated named List declaration is refused natively" (rawNamedTruncation "List" "")
        , TestCase "truncated named Box element is refused natively" (rawNamedTruncation "Box" " type")
        , TestCase "frozen tool reuse keeps the full freshly validated program" toolValidationParity
        , TestCase "package snapshots invalidate on dependencies, entry, imports and file layout" packageSnapshots
        , TestCase "duplicate paths and normalized aliases use the resolver's snapshot" packageAliases
        , TestCase "independent processes reuse a package snapshot" packageProcesses
        , TestCase "a failed frontend run is retried in the same process" parserRetry
        , TestCase "lossless roundtrip keeps contracts, invariants, generics and ghosts" roundtrip
        , TestCase "source change misses" sourceChange
        , TestCase "stage isolation" stageIsolation
        , TestCase "corrupt and truncated entries are rejected by the decoder" corruptRecomputes
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
        , TestCase "required compiler artifacts gate cached executable publication and reuse" requiredArtifactCache
        , TestCase "reader preparation retains successes and rebuilds evicted executables" readerPreparationCache
        , TestCase "independent native builds overlap and restore capabilities" parallelOverlap
        , TestCase "nested and overlapping build regions retain one capability lease" parallelCapabilityOverlap
        , TestCase "failed parallel builds cancel siblings and restore capabilities" parallelFailure
        , TestCase "first storage demand retries after parser seed repair" storageRetry
        , TestCase "content-key locators retain verified dependencies across cache homes" contentLocatorIntegrity
        , TestCase "prepared input aliases reuse verified bytes and repair corrupt or partial files" preparedAliasIntegrity
        , TestCase "proof-only changes invalidate checked certificates and verdict namespaces" proofCertificateNamespace
        , TestCase "changed core, driver and wire certificates cannot publish a checked validator" validatorCertificateRejections
        , testCase "signal targets reject self, process groups and malformed PID markers" $
            firstFailure
                [ testAssertTrue (all (not . validSignalTarget 20 10) [-1, 0, 1, 10, 20])
                , testAssertTrue (validSignalTarget 20 10 23)
                , testAssertEq (map readProcessID ["", "-1", "0", "1", "23 junk", "23 24", "9999999999999999999999"]) (replicate 7 Nothing)
                , testAssertEq (readProcessID "23\n") (Just 23)
                ]
        , TestCase "cancelled native subprocesses die and release the cache lock" nativeProcessCancellation
        , TestCase "cancelled captured tools are terminated and reaped directly" capturedProcessCancellation
        , TestCase "surviving children cannot retain close-on-exec cache locks" survivingChildLock
        , TestCase "available CPU count ignores unrelated OpenMP policy" affinityIgnoresOpenMP
        , TestCase "interactive children retain their SIGINT handler" interactiveControlC
        , TestCase "independent process threads do not form a false file-lock cycle" nativeThreadedProcesses
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

singleSourceCases :: [Test]
singleSourceCases =
    [ TestCase "compileFromValidated reuses the exact validated sentinel" compileFromValidated
    , TestCase "ownedFromCompile reuses the exact compiled sentinel" ownedFromCompile
    , TestCase "warm compile does not traverse upstream" (hotSingleSource "compile")
    , TestCase "warm owned does not traverse upstream" (hotSingleSource "owned")
    , TestCase "single-source stages preserve complete Programs in both request orders" singleSourceOrders
    , TestCase "fresh processes request mixed single-source stages without lock cycles" singleSourceProcesses
    , TestCase "single-source ownership still refuses unsized references" singleSourceUnsized
    ]

sameProgram :: Result Program String -> Result Program String -> TestResult
sameProgram actual expected = testAssertEq actual expected <> testAssertEq (show actual) (show expected)

compileFromValidated :: IO TestResult
compileFromValidated = withToolsCacheHome $ \_ -> do
    let source = "return 991101;"
        sentinel = Pipeline.validatedSource richSource
    calls <- newIORef (0 :: Int)
    seeded <- sharedProgram "validated" source $ do
        atomicModifyIORef' calls (\n -> (n + 1, ()))
        pure sentinel
    reused <- sharedProgram "validated" source (throwIO (userError "validated sentinel recomputed"))
    downstream <- compileOnce source
    count <- readIORef calls
    pure (sameProgram seeded sentinel <> sameProgram reused sentinel
        <> testAssertTrue (case sentinel of Ok _ -> True; Error _ -> False)
        <> testAssertEq count 1 <> sameProgram downstream (sentinel `bindResult` MirHousekeeping.eraseGhosts))

ownedFromCompile :: IO TestResult
ownedFromCompile = withToolsCacheHome $ \_ -> do
    let source = "return 991102;"
        sentinel = Pipeline.compileSource richSource
    calls <- newIORef (0 :: Int)
    seeded <- sharedProgram "compile" source $ do
        atomicModifyIORef' calls (\n -> (n + 1, ()))
        pure sentinel
    reused <- sharedProgram "compile" source (throwIO (userError "compiled sentinel recomputed"))
    downstream <- ownedOnce source
    count <- readIORef calls
    pure (sameProgram seeded sentinel <> sameProgram reused sentinel
        <> testAssertTrue (case sentinel of Ok _ -> True; Error _ -> False)
        <> testAssertEq count 1 <> sameProgram downstream (sentinel `bindResult` Pipeline.ownedOfProgram))

singleSourceStage :: String -> String -> IO (Result Program String)
singleSourceStage "validated" = validatedOnce
singleSourceStage "compile" = compileOnce
singleSourceStage "owned" = ownedOnce
singleSourceStage stage = const (pure (Error ("unknown single-source stage: " ++ stage)))

freshSingleSourceStage :: String -> String -> Result Program String
freshSingleSourceStage "validated" = Pipeline.validatedSource
freshSingleSourceStage "compile" = Pipeline.compileSource
freshSingleSourceStage "owned" = Pipeline.ownedSource
freshSingleSourceStage stage = const (Error ("unknown single-source stage: " ++ stage))

hotSource :: String -> String
hotSource stage = "return missing_hot_" ++ stage ++ "_991103(;"

hotSingleSource :: String -> IO TestResult
hotSingleSource stage = withToolsCacheHome $ \home -> do
    let sentinel = freshSingleSourceStage stage richSource
    seeded <- sharedProgram stage (hotSource stage) (pure sentinel)
    checked <- runSingleSourceProbe home ("hot-" ++ stage)
    pure (sameProgram seeded sentinel <> checked)

-- (the frontend reads and checks a single source: it is what a cached stage must not reach)
withFrontendTrap :: FilePath -> IO a -> IO a
withFrontendTrap marker action = do
    tool <- sourceElaboratorExecutable
    case tool of
        Error e -> fail e
        Ok parser -> bracket (renameFile parser (parser ++ ".held"))
            (\_ -> renameFile (parser ++ ".held") parser)
            (\_ -> do
                withExecutableWrite $ do
                    writeFile parser ("#!/bin/sh\nprintf trap >> '" ++ marker ++ "'\nprintf 'intentional upstream trap\\n' >&2\nexit 23\n")
                    setFileMode parser 0o755
                action)

singleSourceProbe :: String -> IO TestResult
singleSourceProbe mode = do
    Just marker <- lookupEnv "TERSUS_SHARED_CACHE_PROBE"
    result <- if "hot-" `isPrefixOf` mode then do
        let stage = drop 4 mode
            source = hotSource stage
            trap = marker ++ ".upstream"
            expected = freshSingleSourceStage stage richSource
        _ <- Exception.evaluate (force (show expected))
        withFrontendTrap trap $ do
            downstream <- singleSourceStage stage source
            eager <- doesFileExist trap
            control <- validatedOnce source
            reached <- doesFileExist trap
            pure (sameProgram downstream expected
                <> testAssertTrue (not eager) <> testAssertTrue reached
                <> testAssertErrorContains "intentional upstream trap" control)
      else do
        Just home <- lookupEnv "XDG_CACHE_HOME"
        when ("mixed-" `isPrefixOf` mode) $ do
            writeFile (marker ++ ".ready") ""
            awaitNativeFile (home </> "go")
        let stages = case mode of
                "forward" -> ["validated", "compile", "owned"]
                "reverse" -> ["owned", "compile", "validated"]
                _ -> [drop 6 mode]
            source = richSource ++ "\n// single-source stage orders\n"
        results <- mapM (\stage -> do
            actual <- singleSourceStage stage source
            _ <- Exception.evaluate (force (show actual))
            pure (sameProgram actual (freshSingleSourceStage stage source))) stages
        pure (firstFailure results)
    writeFile marker (maybe "pass" id result)
    pure result

spawnSingleSourceProbe :: FilePath -> String -> IO ProcessHandle
spawnSingleSourceProbe home mode = spawnProbeInGroup True home
    [("TERSUS_SINGLE_SOURCE_PROBE", mode), ("TERSUS_SHARED_CACHE_PROBE", home </> mode)]

withSingleSourceProbes :: [IO ProcessHandle] -> ([ProcessHandle] -> IO a) -> IO a
withSingleSourceProbes [] use = use []
withSingleSourceProbes (spawn : rest) use = bracket spawn (stopOwnedProcess True) $ \child ->
    withSingleSourceProbes rest (\others -> use (child : others))

runSingleSourceProbe :: FilePath -> String -> IO TestResult
runSingleSourceProbe home mode = bracket
    (spawnSingleSourceProbe home mode)
    (stopOwnedProcess True)
    (\child -> do
        code <- waitChild 300 child
        output <- readMarker (home </> mode)
        pure (testAssertEq code (Just ExitSuccess) <> testAssertEq output (Right "pass")))

singleSourceOrders :: IO TestResult
singleSourceOrders = firstFailure <$> mapM (\mode -> withToolsCacheHome $ \home -> do
    result <- runSingleSourceProbe home mode
    entries <- entryFiles home
    pure (result <> testAssertEq (length entries) 3)) ["forward", "reverse"]

singleSourceProcesses :: IO TestResult
singleSourceProcesses = withToolsCacheHome $ \home -> do
    let modes = map ("mixed-" ++) ["validated", "compile", "owned"]
    withSingleSourceProbes (map (spawnSingleSourceProbe home) modes) $ \children -> do
        mapM_ (awaitNativeFile . (\mode -> home </> (mode ++ ".ready"))) modes
        writeFile (home </> "go") ""
        codes <- mapM (waitChild 300) children
        outputs <- mapM (readMarker . (home </>)) modes
        entries <- entryFiles home
        before <- mapM getModificationTime entries
        warm <- runSingleSourceProbe home "reverse"
        after <- mapM getModificationTime entries
        pure (testAssertEq codes (replicate 3 (Just ExitSuccess))
            <> testAssertEq outputs (replicate 3 (Right "pass"))
            <> testAssertEq (length entries) 3 <> testAssertEq after before <> warm)

singleSourceUnsized :: IO TestResult
singleSourceUnsized = do
    let source = "fn f(b: Box<Array<Int>>) -> Int { a = &*b; return size(*a); }; return f(Box::new(#[10, 20]));"
    compiled <- compileOnce source
    owned <- ownedOnce source
    pure ((case compiled of Error e -> Just e; Ok _ -> Nothing)
        <> sameProgram owned (Pipeline.ownedSource source)
        <> testAssertErrorContains "a reference to an unsized value" owned)

testSharedCacheCodec :: Test
testSharedCacheCodec = TestList "testSharedCacheCodec" codecCases

codecCases :: [Test]
codecCases =
    [ TestCase "binary framing preserves all 27 lossless and malformed controls" (withNativeHome (\home -> binaryChecks home >> pure Nothing))
    , TestCase "binary disk reuse reaches no fallback in a fresh process" binaryProcesses
    , TestCase "changed source and stage actually reach the fallback" binaryKeyMisses
    , TestCase "invalid binary and legacy entries recompute without decoder fallback" binaryRejects
    , TestCase "runtime overrides cannot reuse process-local successes" binaryRuntimeScopes
    , TestCase "failed binary-cache computations can be retried" binaryFailureRetry
    ]

binarySource :: String
binarySource = "return 314159;"

binaryProbe :: String -> IO TestResult
binaryProbe mode = do
    Just marker <- lookupEnv "TERSUS_SHARED_CACHE_PROBE"
    source <- maybe binarySource id <$> lookupEnv "TERSUS_SHARED_BINARY_SOURCE"
    stage <- maybe "binary-probe" id <$> lookupEnv "TERSUS_SHARED_BINARY_STAGE"
    let compute = writeFile (marker ++ ".computed") "" >> pure (Ok richProgram)
        unexpected = throwIO (userError "binary cache fallback reached")
    if mode == "identity" then do
        file <- sharedProgramCacheFile stage source
        writeFile marker (unlines [maybe "<disabled>" id file, compilerIdentity, concreteBuildIdentity])
        pure Nothing
    else if mode == "miss" then do
        outcome <- try (sharedProgram stage source unexpected) :: IO (Either SomeException (Result Program String))
        pure $ case outcome of
            Left e | "binary cache fallback reached" `isInfixOf` displayException e -> Nothing
            _ -> Just "changed identity reused a cached Program"
    else do
        result <- sharedProgram stage source (if mode == "hit" then unexpected else compute)
        case result of
            Error e -> pure (Just e)
            Ok program -> do
                _ <- Exception.evaluate (force program)
                writeFile marker (encodeProgram program)
                pure $ firstFailure [testAssertEq program richProgram, testAssertEq (show program) (show richProgram)]

runBinaryProbe :: FilePath -> String -> String -> [(String, String)] -> IO (Maybe ExitCode)
runBinaryProbe home marker mode extra = bracket
    (spawnProbe home ([("TERSUS_SHARED_CACHE_PROBE", home </> marker), ("TERSUS_SHARED_BINARY_PROBE", mode)] ++ extra))
    (stopOwnedProcess False)
    (waitChild 15)

binaryProcesses :: IO TestResult
binaryProcesses = withCacheHome $ \home -> do
    seeded <- runBinaryProbe home "seed" "seed" []
    Just file <- sharedProgramCacheFile "binary-probe" binarySource
    before <- getModificationTime file
    original <- readBinaryMarker file
    reused <- runBinaryProbe home "hit" "hit" []
    after <- getModificationTime file
    bytes <- readBinaryMarker file
    first <- readMarker (home </> "seed")
    second <- readMarker (home </> "hit")
    computed <- doesFileExist (home </> "seed.computed")
    unexpected <- doesFileExist (home </> "hit.computed")
    pure $ firstFailure
        [ testAssertEq seeded (Just ExitSuccess), testAssertEq reused (Just ExitSuccess)
        , testAssertTrue computed, testAssertTrue (not unexpected)
        , testAssertEq after before, testAssertEq bytes original, testAssertEq second first
        , case bytes of
            Right entry -> case ProgramBinary.decodeEntry (takeFileName file) entry of
                Right p -> testAssertEq (show p) (show richProgram)
                Left e -> Just e
            Left e -> Just (show e)
        ]

binaryKeyMisses :: IO TestResult
binaryKeyMisses = withCacheHome $ \home -> do
    seeded <- runBinaryProbe home "seed" "seed" []
    sourceMiss <- runBinaryProbe home "source" "miss" [("TERSUS_SHARED_BINARY_SOURCE", binarySource ++ "\n")]
    stageMiss <- runBinaryProbe home "stage" "miss" [("TERSUS_SHARED_BINARY_STAGE", "binary-other-stage")]
    entries <- entryFiles home
    pure $ firstFailure
        [ testAssertEq seeded (Just ExitSuccess)
        , testAssertEq sourceMiss (Just ExitSuccess), testAssertEq stageMiss (Just ExitSuccess)
        , testAssertEq (length entries) 1
        ]

binaryRejects :: IO TestResult
binaryRejects = withCacheHome $ \home -> do
    seeded <- runBinaryProbe home "seed" "seed" []
    Just file <- sharedProgramCacheFile "binary-probe" binarySource
    Right original <- readBinaryMarker file
    let key = takeFileName file
        legacy = BL.fromStrict (BC.pack ("tersus-test-program 1\n" ++ key ++ "\n" ++ show richProgram ++ "\n"))
        altered = BL.init original <> BL.singleton (if BL.last original == 0 then 1 else 0)
        mutations = [("key", ProgramBinary.encodeEntry (replicate 64 '0') richProgram), ("truncated", BL.init original), ("trailing", original <> BL.singleton 0), ("header", BL.take 12 original), ("payload", altered), ("legacy", legacy)]
    results <- mapM (\(label, bytes) -> do
        BL.writeFile file bytes
        code <- runBinaryProbe home label "repair" []
        computed <- doesFileExist (home </> (label ++ ".computed"))
        repaired <- readBinaryMarker file
        pure (namedResult label (firstFailure [testAssertEq code (Just ExitSuccess), testAssertTrue computed, testAssertEq repaired (Right original)]))) mutations
    pure (firstFailure (testAssertEq seeded (Just ExitSuccess) : results))

withCacheVariable :: String -> String -> IO a -> IO a
withCacheVariable variable value action = bracket (lookupEnv variable)
    (maybe (unsetEnv variable) (setEnv variable))
    (\_ -> setEnv variable value >> action)

binaryRuntimeScopes :: IO TestResult
binaryRuntimeScopes = withCacheHome $ \home -> do
    let stage = "binary-runtime-scope"
        source = "return 314160;"
        refused = Error "expected changed override"
    first <- sharedProgram stage source (pure (Ok richProgram))
    writeFile (home </> "wrong-seed") "not a verified seed"
    seedMiss <- withCacheVariable "TERSUS_PARSER_SEED_FILE" (home </> "wrong-seed") $ do
        file <- sharedProgramCacheFile stage source
        result <- sharedProgram stage source (pure refused)
        pure (file, result)
    backendMiss <- withCacheVariable "TERSUS_PARSER" "invalid-probe-backend" (sharedProgram stage source (pure refused))
    path <- maybe "" id <$> lookupEnv "PATH"
    pathMiss <- withCacheVariable "PATH" (path ++ ":" ++ home) (sharedProgram stage source (pure refused))
    restored <- sharedProgram stage source (throwIO (userError "restored memory scope missed"))
    pure $ firstFailure
        [ testAssertEq first (Ok richProgram), testAssertEq seedMiss (Nothing, refused)
        , testAssertEq backendMiss refused, testAssertEq pathMiss refused
        , testAssertEq restored (Ok richProgram), testAssertEq (show restored) (show (Ok richProgram :: Result Program String))
        ]

binaryFailureRetry :: IO TestResult
binaryFailureRetry = withCacheHome $ \_ -> do
    let source = "return 314161;"
        stage = "binary-retry"
    first <- sharedProgram stage source (pure (Error "transient"))
    Just file <- sharedProgramCacheFile stage source
    absent <- not <$> doesFileExist file
    second <- sharedProgram stage source (pure (Ok richProgram))
    present <- doesFileExist file
    pure $ firstFailure [testAssertEq first (Error "transient"), testAssertTrue absent, testAssertEq second (Ok richProgram), testAssertTrue present]
requiredArtifactCache :: IO TestResult
requiredArtifactCache = withCacheHome $ \home -> do
    let artifact = home </> "tersus" </> "artifact-probe-key.ll"
        executable = home </> "tersus" </> "artifact-probe-key"
        make = cachedProgramWithArtifacts [".ll"] "artifact-probe" "key" "required artifact probe"
        complete output = writeFile artifact "successful IR" >> writeFile output "executable" >> pure (Ok ())
    first <- make complete
    ready <- cachedProgramIfPresentWithArtifacts [".ll"] "artifact-probe" "key"
    removeFile artifact
    missing <- cachedProgramIfPresentWithArtifacts [".ll"] "artifact-probe" "key"
    failed <- make (\output -> writeFile output "partial" >> pure (Ok ()))
    published <- doesFileExist executable
    repaired <- make complete
    pure $ firstFailure
        [ testAssertEq first (Ok executable), testAssertEq ready (Ok (Just executable))
        , testAssertEq missing (Ok Nothing)
        , testAssertEq failed (Error "cached program did not publish its required artifacts")
        , testAssertTrue (not published), testAssertEq repaired first
        ]

readerPreparationCache :: IO TestResult
readerPreparationCache = withNativeHome $ \home -> do
    box <- newMVar Nothing
    calls <- newIORef (0 :: Int)
    let path = home </> "reader"
        prepare = do
            atomicModifyIORef' calls (\n -> (n + 1, ()))
            writeFile path "prepared"
            pure (Ok path)
    refused <- memoizedTestExecutable box (pure (Error "prepare failed"))
    first <- memoizedTestExecutable box prepare
    hit <- memoizedTestExecutable box prepare
    removeFile path
    rebuilt <- memoizedTestExecutable box prepare
    count <- readIORef calls
    pure (testAssertEq refused (Error "prepare failed")
        <> testAssertEq [first, hit, rebuilt] (replicate 3 (Ok path)) <> testAssertEq count 2)

parallelOverlap :: IO TestResult
parallelOverlap = do
    before <- getNumCapabilities
    first <- newEmptyMVar
    second <- newEmptyMVar
    result <- timeout 2000000 $ parallelBuilds
        [ putMVar first () >> takeMVar second >> getMaskingState
        , takeMVar first >> putMVar second () >> getMaskingState
        ]
    after <- getNumCapabilities
    pure (testAssertEq result (Just [Unmasked, Unmasked]) <> testAssertEq after before)

parallelCapabilityOverlap :: IO TestResult
parallelCapabilityOverlap = do
    before <- getNumCapabilities
    processors <- availableProcessors
    heldA <- newEmptyMVar
    heldB <- newEmptyMVar
    releaseA <- newEmptyMVar
    releaseB <- newEmptyMVar
    overlapping <- withWorker (parallelBuilds [putMVar heldA () >> takeMVar releaseA] >> pure ()) $ \_ first -> do
        awaitVerdict heldA
        withWorker (parallelBuilds [putMVar heldB () >> takeMVar releaseB] >> pure ()) $ \_ second -> do
            awaitVerdict heldB
            putMVar releaseA ()
            a <- workerResult first
            during <- getNumCapabilities
            putMVar releaseB ()
            b <- workerResult second
            pure (testAssertEq a (Just (Right ())) <> testAssertEq b (Just (Right ()))
                <> testAssertEq during processors)
    afterOverlap <- getNumCapabilities
    nested <- parallelBuilds [parallelBuilds [getMaskingState]]
    afterNested <- getNumCapabilities
    pure (overlapping <> testAssertEq afterOverlap before
        <> testAssertEq nested [[Unmasked]] <> testAssertEq afterNested before)

parallelFailure :: IO TestResult
parallelFailure = do
    before <- getNumCapabilities
    started <- newEmptyMVar
    blocked <- newEmptyMVar
    stopped <- newEmptyMVar
    result <- timeout 2000000 (try (parallelBuilds
        [ (putMVar started () >> takeMVar blocked) `finally` putMVar stopped ()
        , takeMVar started >> throwIO (userError "parallel-build-failure")
        ]) :: IO (Either SomeException [()]))
    ended <- timeout 2000000 (takeMVar stopped)
    after <- getNumCapabilities
    pure $ firstFailure
        [ case result of
            Just (Left e) -> testAssertTrue ("parallel-build-failure" `isInfixOf` displayException e)
            _ -> Just "parallel build did not propagate its sibling failure"
        , testAssertEq ended (Just ())
        , testAssertEq after before
        ]

readProcessID :: String -> Maybe ProcessID
readProcessID text = case reads text :: [(Integer, String)] of
    [(pid, rest)] | pid > 1 && pid <= toInteger (maxBound :: ProcessID) && all isSpace rest -> Just (fromInteger pid)
    _ -> Nothing

markerProcessID :: FilePath -> IO ProcessID
markerProcessID path = do
    text <- readFile path
    case readProcessID text of
        Just pid -> pure pid
        Nothing -> ioError (userError ("invalid process marker: " ++ path))

stopMarkedChild :: FilePath -> [ProcessHandle] -> IO ()
stopMarkedChild path children = case children of
    [child] -> do
        declared <- markerProcessID path
        live <- getPid child
        if live == Just declared
            then stopOwnedProcess False child
            else ioError (userError "process marker does not name the still-owned child")
    _ -> ioError (userError "process marker requires exactly one owned child")

survivingChildLock :: IO TestResult
survivingChildLock = withCacheHome $ \home -> do
    childBox <- newMVar Nothing
    let marker = home </> "surviving-grandchild"
        make = cachedProgram "native-cloexec" "key" "close-on-exec lock probe"
        spawn = do
            -- Publish by rename: a plain redirect creates the marker before the pid is in it.
            (_, _, _, child) <- spawnShared (proc "/bin/sh"
                ["-c", "/bin/sleep 60 & printf '%s\\n' \"$!\" > \"$1.tmp\" && mv \"$1.tmp\" \"$1\"; wait", "surviving-grandchild", marker])
                {create_group = True, std_in = NoStream, std_out = NoStream, std_err = NoStream}
            pure child
        cleanup = readMVar childBox >>= mapM_ (stopOwnedProcess True)
    bracket (pure ()) (\_ -> cleanup) $ \_ -> do
        first <- make $ \output -> mask $ \restore ->
            bracketOnError spawn (stopOwnedProcess True) $ \child -> do
                modifyMVar childBox (\_ -> pure (Just child, ()))
                restore (writeFile output "built" >> pure (Ok ()))
        awaitNativeFile marker
        descendant <- markerProcessID marker
        child <- readMVar childBox
        owner <- maybe (pure Nothing) getPid child
        alive <- maybe (pure (Just (ExitFailure 1))) getProcessExitCode child
        (status, parent, _) <- runCommandWithInputFull "ps" ["-p", show descendant, "-o", "ppid="] ""
        reused <- timeout 2000000 (make (\_ -> pure (Error "surviving child forced a duplicate build")))
        pure (testAssertTrue (case first of Ok _ -> True; Error _ -> False)
            <> testAssertEq alive Nothing <> testAssertEq status ExitSuccess
            <> testAssertEq (readProcessID parent) owner <> testAssertEq reused (Just first))

-- Two things must not overlap. A descriptor a child inherits keeps the file
-- open for writing in that child, and the kernel refuses to execute a file
-- open for writing anywhere (ETXTBSY); close-on-exec drops the descriptor, but
-- only at the child's exec, so between clone and exec every descriptor this
-- process holds is held by that child too. The spawn lock covers the second
-- half and close-on-exec the first. These are controlled reproducers of that
-- failure class, not an account of any past run: the warm paired parser worker
-- was untraced and the historical erasure and runner shutdown failures remain
-- unexplained. Every write here goes through the helpers production uses.
capturedInputErrors :: IO TestResult
capturedInputErrors = do
    echo <- timeout 2000000 (readProcessOutput (proc "/bin/cat" []) "input λ\n")
    broken <- timeout 2000000 (readProcessOutput (proc "/bin/true" []) (replicate 1048576 'x'))
    invalid <- timeout 2000000 (try (readProcessOutput (proc "/bin/cat" []) "\xD800") :: IO (Either IOException (ExitCode, String, String)))
    pure $ firstFailure
        [ testAssertEq echo (Just (ExitSuccess, "input λ\n", ""))
        , testAssertEq broken (Just (ExitSuccess, "", ""))
        , case invalid of
            Just (Left _) -> Nothing
            _ -> Just "an input encoding error was hidden or left the child waiting for EOF"
        ]

atomicExecutableWrites :: IO TestResult
atomicExecutableWrites = withNativeHome $ \home -> do
    found <- findExecutable "true"
    case found of
        Nothing -> pure (Just "no 'true' to publish as a tool")
        Just tool -> do
            bytes <- BL.readFile tool
            _ <- Exception.evaluate (BL.length bytes)
            bulky <- publishPaddedTool home bytes
            padded <- runPublishedTool bulky
            held <- heldWriterSurvivesSpawn home bytes
            copied <- copiesSurviveSpawnLoops home tool bulky
            ordered <- spawnsWaitForExecutableWrites tool
            abandoned <- abandonedRoundCleansUp home bulky
            pure (firstFailure [namedResult "the padded tool itself" padded, held, copied, ordered, abandoned])

cancelledSharedReaders :: IO TestResult
cancelledSharedReaders = do
    original <- getNumCapabilities
    result <- bracket (pure original) setNumCapabilities $ \capabilities -> do
        setNumCapabilities (max 2 capabilities)
        rounds (1 :: Int)
    restored <- getNumCapabilities
    pure (result <> testAssertEq restored original)
  where
    rounds index
        | index > 128 = pure Nothing
        | otherwise = do
            ready <- withReaders (32 :: Int) $ \workers ->
                timeout 2000000 (mapM_ (takeMVar . fst . snd) workers)
            released <- timeout 2000000 (withExecutableWrite (pure ()))
            case (ready, released) of
                (Just (), Just ()) -> rounds (index + 1)
                _ -> pure (Just ("cancelled reader round " ++ show index ++ " retained lock ownership"))
    withReaders 0 use = use []
    withReaders count use = bracket start stop $ \worker ->
        withReaders (count - 1) (\workers -> use (worker : workers))
    start = do
        entered <- newEmptyMVar
        done <- newEmptyMVar
        thread <- forkIOWithUnmask $ \unmask -> do
            result <- try (unmask (do
                withSpawnShared (putMVar entered ())
                forever (withSpawnShared yield)))
            putMVar done (result :: Either SomeException ())
        pure (thread, (entered, done))
    -- These unmasked workers only yield or take the short spawn lock; none waits
    -- for a child or runs I/O that could make cancellation and joining unbounded.
    stop (thread, (_, done)) = Exception.uninterruptibleMask_ $
        killThread thread >> readMVar done >> pure ()

removeIfPresent :: FilePath -> IO ()
removeIfPresent path = do
    _ <- try (removeFile path) :: IO (Either IOException ())
    pure ()

-- Padding an executable leaves it executable, and makes the copy last long
-- enough for a spawn to fall inside it.
publishPaddedTool :: FilePath -> BL.ByteString -> IO FilePath
publishPaddedTool home bytes = do
    let published = home </> "bulky-tool"
    withExecutableTempFile home "bulky-tool.tmp" $ \(staging, handle) -> do
        hSetBinaryMode handle True
        BL.hPut handle (BL.append bytes (BL.replicate 8388608 0))
        setFileMode staging 0o755
        hClose handle
        renameFile staging published
        pure published

discardStaging :: (FilePath, Handle) -> IO ()
discardStaging (staging, handle) = hClose handle >> removeIfPresent staging

-- Run it with nothing between the publication and the exec: anything in
-- between is time for a child cloned during the write to reach its own exec,
-- which is the very overlap this case has to catch.
runPublishedTool :: FilePath -> IO TestResult
runPublishedTool path = do
    outcome <- try (withSpawnedProcess (proc path []){std_in = NoStream, std_out = NoStream, std_err = NoStream}
        (\(_, _, _, child) -> waitForProcess child)) :: IO (Either IOException ExitCode)
    pure $ case outcome of
        Right ExitSuccess -> Nothing
        Right code -> Just ("running " ++ takeFileName path ++ " gave " ++ show code)
        Left e -> Just ("could not run " ++ takeFileName path ++ ": " ++ show e)

-- Started the way the captured tools are: inheriting this process's
-- descriptors, over the posix_spawn fast path.
spawnSurvivingChild :: IO ProcessHandle
spawnSurvivingChild = do
    (_, _, _, child) <- spawnShared (proc "/bin/sleep" ["60"])
        {std_in = NoStream, std_out = NoStream, std_err = NoStream}
    pure child

-- One owner for the child from the spawn to the end of the region: the slot is
-- filled under the same mask as the spawn, so no outcome is dropped, and
-- leaving the region kills the thread, joins the slot and stops a child that
-- did start -- whether the body returned, failed or was cancelled.
withSpawnedChild :: (MVar (Either SomeException ProcessHandle) -> IO a) -> IO a
withSpawnedChild use = bracket start stop (use . snd)
  where
    start = do
        slot <- newEmptyMVar
        thread <- forkFinally
            (mask_ (spawnSurvivingChild >>= putMVar slot . Right))
            (either (\e -> tryPutMVar slot (Left e) >> pure ()) pure)
        pure (thread, slot)
    stop (thread, slot) = do
        killThread thread
        outcome <- readMVar slot
        either (const (pure ())) (stopOwnedProcess False) outcome

-- The writer is held open on this thread while a child is created on another:
-- the only arrangement in which that child can inherit it. Publishing inside
-- the exclusive region waits for every spawn in flight to have exec'd, so what
-- is left to prove is that the exec dropped the descriptor.
heldWriterSurvivesSpawn :: FilePath -> BL.ByteString -> IO TestResult
heldWriterSurvivesSpawn home bytes = do
    let published = home </> "held-tool"
    bracketOnError (openTempFileCloexec home "held-tool.tmp") discardStaging $ \(staging, handle) -> do
        hSetBinaryMode handle True
        BL.hPut handle bytes
        setFileMode staging 0o755
        withSpawnedChild $ \slot -> do
            spawned <- readMVar slot
            case spawned of
                Left e -> pure (Just ("the child did not start: " ++ displayException e))
                Right child -> do
                    withExecutableWrite (hClose handle >> renameFile staging published)
                    ran <- runPublishedTool published
                    living <- getProcessExitCode child
                    pure $ firstFailure
                        [ namedResult "a tool published while a child was spawned" ran
                        , namedResult "the child that could have inherited the writer"
                            (testAssertEq living Nothing)
                        ]

-- Processes are created on other threads throughout, while this one keeps
-- copying, publishing and running a fresh executable. Without the spawn lock a
-- child cloned during one of those copies is still short of its exec when the
-- copy is run, and holds the copy's writer.
copiesSurviveSpawnLoops :: FilePath -> FilePath -> FilePath -> IO TestResult
copiesSurviveSpawnLoops home quick tool = withSpawnLoops quick 4 $ \loopsAlive -> do
    outcome <- rounds (1 :: Int)
    alive <- loopsAlive
    pure (firstFailure [outcome, namedResult "the spawn loops" (testAssertTrue alive)])
  where
    rounds index
        | index > 16 = pure Nothing
        | otherwise = do
            let published = home </> ("copied-tool-" ++ show index)
            copyFileCloexec tool published
            ran <- runPublishedTool published
            case namedResult ("round " ++ show index) ran of
                Just failure -> pure (Just failure)
                Nothing -> removeIfPresent published >> rounds (index + 1)

-- The loops own their children: each creation is bracketed, so killing a loop
-- terminates and reaps whatever it had just started.
withSpawnLoops :: FilePath -> Int -> (IO Bool -> IO TestResult) -> IO TestResult
withSpawnLoops quick count use = bracket (mapM (const startOne) [1 .. count]) stop (use . alive)
  where
    quiet = (proc quick []){std_in = NoStream, std_out = NoStream, std_err = NoStream}
    spin = forever (withSpawnedProcess quiet (\(_, _, _, child) -> () <$ waitForProcess child))
    startOne = do
        slot <- newEmptyMVar
        thread <- forkFinally spin (putMVar slot)
        pure (thread, slot)
    stop = mapM_ (\(thread, slot) -> killThread thread >> readMVar slot >> pure ())
    alive slots = all isNothing <$> mapM (tryReadMVar . snd) slots

-- The lock's own invariant, which is what makes the overlap impossible rather
-- than merely unlikely: a process creation that begins while an executable is
-- being written cannot produce its child until that write has closed.
spawnsWaitForExecutableWrites :: FilePath -> IO TestResult
spawnsWaitForExecutableWrites quick = do
    entered <- newEmptyMVar
    spawnFinished <- newEmptyMVar
    withWorker (do
        takeMVar entered
        withSpawnedProcess (proc quick []){std_in = NoStream, std_out = NoStream, std_err = NoStream}
            (\(_, _, _, child) -> () <$ waitForProcess child)
        getMonotonicTime >>= putMVar spawnFinished) $ \_ done -> do
            writeEnded <- withExecutableWrite $ do
                putMVar entered ()
                threadDelay 200000
                getMonotonicTime
            outcome <- readMVar done
            case outcome of
                Left e -> pure (Just ("the spawn held under the write: " ++ displayException e))
                Right () -> do
                    spawnEnded <- readMVar spawnFinished
                    pure $ namedResult "a spawn that began during an executable write"
                        (testAssertTrue (spawnEnded >= writeEnded))

-- Abandoning an exclusive write releases the lock and leaves no live child and
-- no staging file: the copy after it must still publish and run.
abandonedRoundCleansUp :: FilePath -> FilePath -> IO TestResult
abandonedRoundCleansUp home tool = do
    observed <- newEmptyMVar
    failed <- try (withSpawnedChild $ \slot -> do
        child <- readMVar slot >>= either throwIO pure
        putMVar observed child
        copyFileCloexec (home </> "no-such-tool") (home </> "abandoned-copy"))
        :: IO (Either SomeException ())
    child <- takeMVar observed
    reaped <- getProcessExitCode child
    let recovered = home </> "recovered-copy"
    copyFileCloexec tool recovered
    ran <- runPublishedTool recovered
    names <- listDirectory home
    pure $ firstFailure
        [ namedResult "the abandoned copy" (testAssertTrue (either (const True) (const False) failed))
        , namedResult "the abandoned child" (testAssertTrue (reaped /= Nothing))
        , namedResult "the released exclusive lock" ran
        , namedResult "the abandoned staging file" (testAssertTrue (not (any stagingName names)))
        ]
  where
    stagingName name = "copy" `isPrefixOf` name && ".tmp" `isSuffixOf` name

contentLocatorIntegrity :: IO TestResult
contentLocatorIntegrity = withCacheHome $ \home -> do
    calls <- newIORef (0 :: Int)
    let input = "verified locator input"
        prepare = MirHousekeeping.cachedPreparedInput "locator-input" [] (== input) (pure (Ok input))
        make = do
            _ <- atomicModifyIORef' calls (\n -> (n + 1, ()))
            fmap (mapResult (\text -> MirHousekeeping.ownedContentKey "producer" text [])) prepare
        lookupKey = MirHousekeeping.cachedContentKey "locator-probe" [] [("locator-input", [])] make
    first <- lookupKey
    second <- lookupKey
    names <- listDirectory (home </> "tersus")
    copied <- withCacheHome $ \target -> do
        createDirectoryIfMissing True (target </> "tersus")
        mapM_ (\name -> copyCacheFile (home </> "tersus" </> name) (target </> "tersus" </> name))
            [name | name <- names, not (".lock" `isInfixOf` name)]
        lookupKey
    reused <- readIORef calls
    case ([home </> "tersus" </> name | name <- names, "prepared-" `isPrefixOf` name, not (".lock" `isInfixOf` name)],
          [home </> "tersus" </> name | name <- names, "content-key-" `isPrefixOf` name, not (".lock" `isInfixOf` name)]) of
        ([payload], [locator]) -> do
            writeFile payload "changed-header\ncorrupt payload"
            repaired <- lookupKey
            writeFile locator "partial locator"
            restored <- lookupKey
            distinct <- MirHousekeeping.cachedContentKey "locator-probe" ["-O0"] [("locator-input", [])]
                (pure (Error "different flags must miss"))
            incomplete <- MirHousekeeping.cachedContentKey "locator-probe" [] [("locator-input", []), ("missing-input", [])]
                (pure (Error "different dependencies must miss"))
            rebuilt <- readIORef calls
            pure $ firstFailure
                [ testAssertTrue (case first of Ok _ -> True; _ -> False)
                , testAssertEq [second, copied, repaired, restored] (replicate 4 first)
                , testAssertEq reused 1, testAssertEq rebuilt 3
                , testAssertEq distinct (Error "different flags must miss")
                , testAssertEq incomplete (Error "different dependencies must miss")
                ]
        _ -> pure (Just "locator test did not publish one input and one key")

preparedAliasIntegrity :: IO TestResult
preparedAliasIntegrity = withCacheHome $ \home -> do
    count <- newIORef (0 :: Int)
    let payload = "verified-owned-input"
        build = atomicModifyIORef' count (\n -> (n + 1, ())) >> pure (Ok payload)
        cached = MirHousekeeping.cachedPreparedInput "alias-probe" [] (== payload) build
    first <- cached
    second <- cached
    names <- listDirectory (home </> "tersus")
    case [home </> "tersus" </> name | name <- names, "prepared-" `isPrefixOf` name, not (".lock" `isInfixOf` name)] of
        [path] -> do
            writeFile path "partial"
            repaired <- cached
            writeFile path ("wrong-checksum\n" ++ payload)
            corrected <- cached
            let key = drop (length "prepared-") (takeFileName path)
                rejected = "decoder-rejects-this"
            writeFile path (fingerprint [key, rejected] ++ "\n" ++ rejected)
            decoded <- cached
            attempts <- readIORef count
            invalid <- MirHousekeeping.cachedPreparedInput "invalid-alias" [] (== payload) (pure (Ok "invalid"))
            failed <- MirHousekeeping.cachedPreparedInput "failed-alias" [] (== payload) (pure (Error "preparation failed"))
            remaining <- listDirectory (home </> "tersus")
            pure $ firstFailure
                [testAssertEq [first, second, repaired, corrected, decoded] (replicate 5 (Ok payload))
                , testAssertEq attempts 4, testAssertEq failed (Error "preparation failed")
                , testAssertEq invalid (Error "invalid prepared input")
                , testAssertEq (sort [name | name <- remaining, not (".lock" `isInfixOf` name)]) (sort [takeFileName path])]
        _ -> pure (Just "prepared cache did not publish exactly one input")

proofCertificateNamespace :: IO TestResult
proofCertificateNamespace = do
    let program post = Compile.lowerSource True ("fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return " ++ post ++ " 0; }] { return n; }; return f(3);")
        owned raw = mapResult writeProgram (MirHousekeeping.nativeProgram raw `bindResult` MirHousekeeping.insertOwnership)
    case (program ">", program "<") of
        (Ok good, Ok bad) -> case (owned good, owned bad, ValidatorNative.prepareTexts False good, ValidatorNative.prepareTexts False bad) of
            (Ok a, Ok b, Ok proofA, Ok proofB) -> withCacheHome $ \home -> do
                let native input = MirHousekeeping.ownedContentKey "producer" input ["-O2"]
                    checkedA = ValidatorNative.certificateKey (native a) [] (map snd proofA)
                    checkedB = ValidatorNative.certificateKey (native b) [] (map snd proofB)
                    query = "proof-namespace-probe"
                    verdict key = home </> "tersus" </> ("verdicts-" ++ key) </> fingerprint [query]
                    oldVerdict = verdict checkedA
                createDirectoryIfMissing True (takeDirectory oldVerdict)
                writeFile oldVerdict ("0 -1 -1\n" ++ query)
                first <- cachedProgram "certificate-probe" checkedA "proof certificate probe"
                    (\output -> writeFile output "checked" >> pure (Ok ()))
                changed <- cachedProgram "certificate-probe" checkedB "proof certificate probe"
                    (\_ -> pure (Error "changed proof must be checked"))
                withVerdictLock checkedB query (pure ())
                oldLock <- doesFileExist (oldVerdict ++ ".lock")
                newLock <- doesFileExist (verdict checkedB ++ ".lock")
                retained <- readFile oldVerdict
                pure $ firstFailure
                    [ testAssertEq a b, testAssertEq (native a) (native b)
                    , testAssertTrue (map snd proofA /= map snd proofB && checkedA /= checkedB)
                    , testAssertTrue (case first of Ok _ -> True; _ -> False)
                    , testAssertEq changed (Error "changed proof must be checked")
                    , testAssertEq (oldLock, newLock) (False, True)
                    , testAssertEq retained ("0 -1 -1\n" ++ query)
                    ]
            (Error e, _, _, _) -> pure (Just e)
            (_, Error e, _, _) -> pure (Just e)
            (_, _, Error e, _) -> pure (Just e)
            (_, _, _, Error e) -> pure (Just e)
        (Error e, _) -> pure (Just e)
        (_, Error e) -> pure (Just e)

validatorCertificateRejections :: IO TestResult
validatorCertificateRejections = do
    prepared <- MirHousekeeping.prepareValidator
    executable <- MirHousekeeping.cachedUncheckedValidator
    let falseSource = Compile.lowerSource True "fn falseCertificate() -> Int [{ }] [{ affirm 0 = 1; }] { return 0; }; return 0;"
    case (prepared, executable, MirHousekeeping.nativeStorage, falseSource) of
        (Ok (unchecked, raw, _), Ok exe, Ok (_, library), Ok falseProgram) ->
            case (ValidatorNative.prepareTexts True library, ValidatorNative.prepareTexts False raw, Map.lookup "falseCertificate" (progFunctions falseProgram)) of
                (Ok libraryChecks, Ok ownChecks, Just falseFunction) -> do
                    let failed name = raw{progFunctions = Map.adjust (\fn -> fn{fnSpec = (fnSpec fn){specEnsures = specEnsures (fnSpec falseFunction)}}) name (progFunctions raw)}
                        prepare name = case ValidatorNative.prepareTexts False (failed name) of
                            Error e -> Error e
                            Ok checks -> case lookup name checks of
                                Nothing -> Error ("missing certificate function " ++ name)
                                Just wire -> Ok (name, wire, map snd checks, "1")
                        malformed = "0\ni 0\nl 0\n"
                        wireChecks = malformed : map snd (drop 1 ownChecks)
                        variants = [prepare "noTemplates", prepare "driverPrintVerdict", Ok ("wire-context", malformed, wireChecks, "2")]
                        baseKey = ValidatorNative.certificateKey unchecked (map snd libraryChecks) (map snd ownChecks)
                    withCacheHome $ \home -> do
                        results <- forM variants $ \variant -> case variant of
                            Error e -> pure (Just e)
                            Ok (name, wire, checks, status) -> do
                                let key = ValidatorNative.certificateKey unchecked (map snd libraryChecks) checks
                                    rejected = "rejected certificate " ++ name
                                result <- cachedProgram "validator" key "invalid validator certificate control" $ \output -> do
                                    (exit, out, errors) <- runCommandWithInputFull "/bin/sh" ["-c", "ulimit -s unlimited 2>/dev/null || ulimit -s 65532 2>/dev/null; exec \"$0\"", exe] ("1\n" ++ wire)
                                    case (exit, words (takeWhile (/= '\n') out)) of
                                        (ExitSuccess, first : _) | first == status -> pure (Error rejected)
                                        (ExitSuccess, "0" : _) -> writeFile output "incorrectly checked" >> pure (Ok ())
                                        _ -> pure (Error ("certificate control failed: " ++ show exit ++ take 200 out ++ take 200 errors))
                                published <- doesFileExist (home </> "tersus" </> ("validator-" ++ key))
                                pure $ firstFailure [testAssertTrue (key /= baseKey), testAssertEq result (Error rejected), testAssertEq published False]
                        pure (firstFailure results)
                (Error e, _, _) -> pure (Just e)
                (_, Error e, _) -> pure (Just e)
                _ -> pure (Just "missing false certificate control")
        (Error e, _, _, _) -> pure (Just e)
        (_, Error e, _, _) -> pure (Just e)
        (_, _, Error e, _) -> pure (Just e)
        (_, _, _, Error e) -> pure (Just e)

nativeProcessCancellation :: IO TestResult
nativeProcessCancellation = processCancellation True

capturedProcessCancellation :: IO TestResult
capturedProcessCancellation = processCancellation False

processCancellation :: Bool -> IO TestResult
processCancellation isolatedCLI = withCacheHome $ \home -> do
    let marker = home </> "slow-native-child"
        pidFiles = [marker ++ ".owner"] ++ [marker ++ ".child" | isolatedCLI]
        build = cachedProgram "native-cancellation" "key" "native cancellation probe"
        script = if isolatedCLI
            then "sleep 60 & child=$!; printf '%s\\n' \"$$\" > \"$1.owner\"; printf '%s\\n' \"$child\" > \"$1.child\"; : > \"$1.started\"; wait"
            else "trap '' TERM; printf '%s\\n' \"$$\" > \"$1.owner\"; : > \"$1.started\"; exec sleep 60"
        constant label text =
            let bytes = encodeUtf8 text
                hex character = let digits = showHex (ord character) "" in '\\' : replicate (2 - length digits) '0' ++ digits
             in "@" ++ label ++ " = private constant [" ++ show (length bytes + 1) ++ " x i8] c\"" ++ concatMap hex bytes ++ "\\00\""
        cliIr = unlines
            [ constant "sh" "/bin/sh", constant "option" "-c", constant "script" script
            , constant "role" "native-process-cancellation", constant "marker" marker
            , "declare i32 @execl(ptr, ptr, ...)"
            , "define i32 @main(i32 %argc, ptr %argv) {"
            , "  %r = call i32 (ptr, ptr, ...) @execl(ptr @sh, ptr @sh, ptr @option, ptr @script, ptr @role, ptr @marker, ptr null)"
            , "  ret i32 %r", "}"
            ]
        nonTerminal action = bracket (hDuplicate stdin) hClose $ \saved ->
            withFile "/dev/null" ReadMode $ \input ->
                (hDuplicateTo input stdin >> action) `finally` hDuplicateTo saved stdin
    (do
        failed <- try (parallelBuilds
            [ build $ \output -> do
                outcome <- if isolatedCLI
                    then do
                        result <- nonTerminal (runExecutable cliIr [])
                        pure $ case result of Ok code -> (code, ""); Error e -> (ExitFailure 1, e)
                    else do
                        (code, _, errors) <- runCommandWithInputFull "/bin/sh" ["-c", script, "native-process-cancellation", marker] ""
                        pure (code, errors)
                case outcome of
                    (ExitSuccess, _) -> writeFile output "finished" >> pure (Ok ())
                    (_, errors) -> pure (Error errors)
            , awaitNativeFile (marker ++ ".started") >> throwIO (userError "cancel-native-branch")
            ]) :: IO (Either SomeException [Result FilePath String])
        pids <- mapM markerProcessID pidFiles
        let stopped = do
                statuses <- mapM (\pid -> do
                    (code, output, errors) <- runCommandWithInputFull "ps" ["-p", show pid, "-o", "stat="] ""
                    pure ((code /= ExitSuccess && null errors) || case dropWhile (== ' ') output of 'Z' : _ -> True; _ -> False)) pids
                if and statuses then pure () else threadDelay 10000 >> stopped
        gone <- timeout 2000000 stopped
        retried <- timeout 2000000 (build (\output -> writeFile output "retry" >> pure (Ok ())))
        pure $ firstFailure
            [ testAssertTrue (case failed of Left e -> "cancel-native-branch" `isInfixOf` displayException e; _ -> False)
            , testAssertEq gone (Just ())
            , testAssertTrue (case retried of Just (Ok _) -> True; _ -> False)
            ])

affinityIgnoresOpenMP :: IO TestResult
affinityIgnoresOpenMP = do
    expected <- availableProcessors
    let setting name value action = bracket (lookupEnv name) restore $ \_ -> setEnv name value >> action
          where restore Nothing = unsetEnv name; restore (Just value) = setEnv name value
    threads <- setting "OMP_NUM_THREADS" "32" availableProcessors
    limited <- setting "OMP_THREAD_LIMIT" "1" availableProcessors
    both <- setting "OMP_NUM_THREADS" "32" (setting "OMP_THREAD_LIMIT" "1" availableProcessors)
    noPath <- setting "PATH" "" availableProcessors
    pure (testAssertEq [threads, limited, both, noPath] (replicate 4 expected))

interactiveControlC :: IO TestResult
interactiveControlC = withNativeHome $ \home -> do
    self <- getExecutablePath
    let irPath = home </> "signal-handler.ll"
        scriptPath = home </> "terminal.py"
        ir = unlines
            [ "@ci10_ready = private constant [6 x i8] c\"READY\\00\""
            , "@ci10_irq = private constant [5 x i8] c\"INT\\0A\\00\""
            , "@ci10_done = private constant [8 x i8] c\"IGNORED\\00\""
            , "@ci10_buffer = global [1 x i8] zeroinitializer"
            , "declare ptr @signal(i32, ptr)", "declare i32 @puts(ptr)"
            , "declare i64 @write(i32, ptr, i64)", "declare i64 @read(i32, ptr, i64)"
            , "define void @ci10_handle(i32 %signal) {"
            , "  %w = call i64 @write(i32 1, ptr @ci10_irq, i64 4)", "  ret void", "}"
            , "define i32 @main(i32 %argc, ptr %argv) {"
            , "  %h = call ptr @signal(i32 2, ptr @ci10_handle)"
            , "  %p = call i32 @puts(ptr @ci10_ready)", "  br label %waiting"
            , "waiting:", "  %r = call i64 @read(i32 0, ptr @ci10_buffer, i64 1)"
            , "  %ok = icmp eq i64 %r, 1", "  br i1 %ok, label %finished, label %waiting"
            , "finished:", "  %q = call i32 @puts(ptr @ci10_done)", "  ret i32 0", "}"
            ]
        script = unlines
            [ "import fcntl, os, pty, select, signal, subprocess, sys, termios, time"
            , "master, slave = pty.openpty()"
            , "settings = termios.tcgetattr(slave); settings[3] |= termios.ISIG | termios.ICANON"
            , "settings[6][termios.VINTR] = b'\\x03'; termios.tcsetattr(slave, termios.TCSANOW, settings)"
            , "def terminal():", "    os.setsid(); fcntl.ioctl(0, termios.TIOCSCTTY, 0)"
            , "env = os.environ.copy(); env['TERSUS_TERMINAL_PROBE'] = sys.argv[2]"
            , "p = subprocess.Popen([sys.argv[1], 'testSharedCacheProbe', '--child', '+RTS', '-N1', '-RTS'], stdin=slave, stdout=slave, stderr=slave, env=env, preexec_fn=terminal)"
            , "os.close(slave); output = bytearray()"
            , "def until(marker):", "    deadline = time.monotonic() + 30"
            , "    while marker not in output:"
            , "        if time.monotonic() > deadline: raise RuntimeError(bytes(output))"
            , "        if select.select([master], [], [], .1)[0]: output.extend(os.read(master, 65536))"
            , "try:", "    until(b'READY'); os.write(master, b'\\x03'); until(b'INT')"
            , "    deadline = time.monotonic() + .15"
            , "    while time.monotonic() < deadline:"
            , "        if select.select([master], [], [], .01)[0]: output.extend(os.read(master, 65536))"
            , "        if p.poll() is not None: raise RuntimeError(bytes(output))"
            , "    os.write(master, b'\\n'); until(b'[CTRL-C-DELEGATED]')"
            , "    assert p.wait(timeout=5) == 0; print('PASS delegated terminal SIGINT')"
            , "finally:"
            , "    if p.poll() is None:"
            , "        assert p.pid > 1 and p.pid != os.getpid() and p.pid != os.getpgrp()"
            , "        group = os.getpgid(p.pid)"
            , "        if group != p.pid:"
            , "            p.kill(); p.wait(); raise RuntimeError('terminal child did not own its process group')"
            , "        os.killpg(p.pid, signal.SIGKILL)"
            , "    p.wait(); os.close(master)"
            ]
    writeFile irPath ir
    writeFile scriptPath script
    (code, output, errors) <- runCommandWithInputFull "python3" [scriptPath, self, irPath] ""
    pure (if code == ExitSuccess then Nothing else Just (output ++ errors))

validatorFlagNamespace :: IO TestResult
validatorFlagNamespace = withCacheHome $ \home -> do
    let hashes = [ValidatorNative.certificateKey (MirHousekeeping.ownedContentKey "emitter-producer" "owned-input" flags) ["library-check"] ["source-check"]
            | flags <- [["-O0"], ["-O2"], []]]
        text = "validator-build-flag-probe"
        file hash = home </> "tersus" </> ("verdicts-" ++ hash) </> fingerprint [text]
        stale = file (hashes !! 2)
        body = "0 -1 -1\n" ++ text
    createDirectoryIfMissing True (takeDirectory stale)
    writeFile stale body
    withVerdictLock (hashes !! 1) text (pure ())
    present <- mapM (doesFileExist . (++ ".lock") . file) hashes
    retained <- readMarker stale
    pure $ firstFailure
        [ testAssertEq present [False, True, False]
        , testAssertEq retained (Right body)
        , testAssertEq (length (Map.fromList [(hash, ()) | hash <- hashes])) 3
        ]

rawNamedTruncation :: String -> String -> IO TestResult
rawNamedTruncation name suffix = do
    cache <- cacheDirectory
    key <- TersusParser.parserKey
    case (cache, key) of
        (Error e, _) -> pure (Just e)
        (_, Error e) -> pure (Just e)
        (Ok dir, Ok identity) -> do
            let exe = dir </> ("tersus-parser-" ++ identity)
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
    terminal <- lookupEnv "TERSUS_TERMINAL_PROBE"
    routing <- lookupEnv "TERSUS_TEST_ROUTING_PROBE"
    content <- lookupEnv "TERSUS_CONTENT_RESTORE_PROBE"
    warm <- lookupEnv "TERSUS_WARM_START_PROBE"
    case terminal of
        Just path -> do
            ir <- readFile path
            result <- runExecutable ir []
            case result of
                Ok ExitSuccess -> putStrLn "[CTRL-C-DELEGATED]" >> pure Nothing
                other -> pure (Just (show other))
        Nothing -> case warm of
            Just "1" -> warmStartProbe
            _ -> case content of
                Just directory -> contentRestoreProbe directory
                Nothing -> case routing of
                    Just "1" -> getNumCapabilities >>= \count -> putStrLn ("[CAPABILITIES] " ++ show count) >> pure Nothing
                    _ -> cacheProbe

warmStartProbe :: IO TestResult
warmStartProbe = do
    start <- getMonotonicTime
    result <- Bootstrap.tersusLlvm "return 42;"
    elapsed <- (subtract start) <$> getMonotonicTime
    putStrLn ("[WARM-START] " ++ show elapsed ++ "s")
    pure $ case result of
        Error e -> Just e
        Ok ir -> testAssertTrue (not (null ir))

contentRestoreProbe :: FilePath -> IO TestResult
contentRestoreProbe directory = do
    start <- getMonotonicTime
    built <- Bootstrap.tersusLlvm "return 42;"
    elapsed <- (subtract start) <$> getMonotonicTime
    emitter <- MirHousekeeping.emitterKey
    parser <- TersusParser.parserKey
    checked <- ValidatorNative.validatorKey
    validator <- MirHousekeeping.cachedPreparedInput "validator" [] (const True) (pure (Error "validator input was not prepared"))
    emitterInput <- MirHousekeeping.cachedPreparedInput MirHousekeeping.emitterEntry [] (const True) (pure (Error "emitter input was not prepared"))
    parserInput <- MirHousekeeping.cachedPreparedInput "lib/parser/parser.tersus" [] (const True) (pure (Error "parser input was not prepared"))
    case (built, emitter, parser, checked, validator, emitterInput, parserInput) of
        (Ok ir, Ok e, Ok p, Ok v, Ok validatorBytes, Ok emitterBytes, Ok parserBytes) -> do
            createDirectoryIfMissing True directory
            writeFile (directory </> "identity") (show (compilerSnapshotHash, e, p, v))
            writeFile (directory </> "e1-owned.mir") emitterBytes
            writeFile (directory </> "p1-owned.mir") parserBytes
            writeFile (directory </> "validator-owned.mir") validatorBytes
            writeFile (directory </> "result.ll") ir
            putStrLn ("[CONTENT-READY] " ++ show elapsed ++ "s")
            pure Nothing
        (Error e, _, _, _, _, _, _) -> pure (Just e)
        (_, Error e, _, _, _, _, _) -> pure (Just e)
        (_, _, Error e, _, _, _, _) -> pure (Just e)
        (_, _, _, Error e, _, _, _) -> pure (Just e)
        (_, _, _, _, Error e, _, _) -> pure (Just e)
        (_, _, _, _, _, Error e, _) -> pure (Just e)
        (_, _, _, _, _, _, Error e) -> pure (Just e)

cacheProbe :: IO TestResult
cacheProbe = do
    singleSource <- lookupEnv "TERSUS_SINGLE_SOURCE_PROBE"
    binary <- lookupEnv "TERSUS_SHARED_BINARY_PROBE"
    case singleSource of
        Just mode -> singleSourceProbe mode
        Nothing -> maybe ordinaryCacheProbe binaryProbe binary

ordinaryCacheProbe :: IO TestResult
ordinaryCacheProbe = do
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
    storage <- lookupEnv "TERSUS_STORAGE_RETRY_PROBE"
    case (storage, retry) of
        (Just _, _) -> storageRetryProbe
        (_, Just _) -> parserRetryProbe
        _ -> regularSharedProbe

storageRetry :: IO TestResult
storageRetry = withNativeHome $ \home -> do
    primeBootstrapTools home
    bracket (spawnProbe home [("TERSUS_STORAGE_RETRY_PROBE", "1")])
        (\child -> stopOwnedProcess False child >> waitForProcess child >> pure ()) $ \child -> do
            code <- waitChild 300 child
            pure (testAssertEq code (Just ExitSuccess))

storageRetryProbe :: IO TestResult
storageRetryProbe = do
    Just home <- lookupEnv "XDG_CACHE_HOME"
    let broken = home </> "broken-parser.ll"
    writeFile broken "not the pinned parser seed\n"
    removeFile (home </> "tersus" </> ("parser-seed-" ++ parserSeedHash))
    previous <- lookupEnv "TERSUS_PARSER_SEED_FILE"
    let restore = maybe (unsetEnv "TERSUS_PARSER_SEED_FILE") (setEnv "TERSUS_PARSER_SEED_FILE") previous
    failed <- bracket (setEnv "TERSUS_PARSER_SEED_FILE" broken) (\_ -> restore)
        (\_ -> MirHousekeeping.listLibrary)
    repaired <- MirHousekeeping.listLibrary
    pure $ firstFailure
        [ testAssertTrue (case failed of Error _ -> True; _ -> False)
        , testAssertTrue (case repaired of Ok units -> not (null units); _ -> False)
        ]

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
    (home, handle) <- openTempFileCloexec tmp "tersus-native-cache-test"
    hClose handle
    removeFile home
    createDirectoryIfMissing True home
    use home `finally` removeDirectoryRecursive home

awaitFileWithin :: FilePath -> Int -> IO Bool
awaitFileWithin path tries
    | tries <= 0 = pure False
    | otherwise = do
        present <- doesFileExist path
        if present then pure True else threadDelay 100000 >> awaitFileWithin path (tries - 1)

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

nativeThreadedProcesses :: IO TestResult
nativeThreadedProcesses = withNativeHome $ \home ->
    withNativeChildren home [("A", "threaded-A"), ("B", "threaded-B")] $ \children -> do
        mapM_ (awaitNativeFile . (home </>)) ["A.waiting", "B.waiting"]
        early <- timeout 200000 $ let
            watch = do
                failed <- or <$> mapM (doesFileExist . (home </>)) ["A.failed", "B.failed"]
                if failed then pure () else threadDelay 10000 >> watch
            in watch
        writeFile (home </> "release") ""
        outcomes <- timeout 10000000 (mapM waitForProcess children)
        acquired <- mapM (doesFileExist . (home </>)) ["A.acquired", "B.acquired"]
        pure (testAssertEq early Nothing <> testAssertEq outcomes (Just [ExitSuccess, ExitSuccess])
            <> testAssertEq acquired [True, True])

nativeThreadedProbe :: String -> IO TestResult
nativeThreadedProbe role = do
    Just home <- lookupEnv "XDG_CACHE_HOME"
    let peer = if role == "A" then "B" else "A"
        marker suffix = home </> (role ++ suffix)
        make who build = cachedProgram ("native-threaded-" ++ who) "key" "native threaded lock probe" build
        owner = make role $ \output -> do
            writeFile (marker ".held") ""
            awaitNativeFile (home </> "release")
            writeFile output role
            pure (Ok ())
        waiter = do
            mapM_ (awaitNativeFile . (home </>)) [role ++ ".held", peer ++ ".held"]
            writeFile (marker ".waiting") ""
            answer <- make peer (\_ -> pure (Error "waiter duplicated its peer's build"))
            case answer of
                Ok _ -> writeFile (marker ".acquired") ""
                Error _ -> pure ()
            pure answer
    result <- try (parallelBuilds [owner, waiter]) :: IO (Either SomeException [Result FilePath String])
    let failure = case result of
            Left e -> Just (displayException e)
            Right answers -> firstFailure [case answer of Error e -> Just e; Ok _ -> Nothing | answer <- answers]
    case failure of
        Just e -> writeFile (marker ".failed") e
        Nothing -> pure ()
    pure failure

nativeProbe :: String -> IO TestResult
nativeProbe "threaded-A" = nativeThreadedProbe "A"
nativeProbe "threaded-B" = nativeThreadedProbe "B"
nativeProbe mode | mode `elem` ["verdict", "verdict-hold", "verdict-wait"] = do
    Just marker <- lookupEnv "TERSUS_SHARED_CACHE_PROBE"
    Just home <- lookupEnv "XDG_CACHE_HOME"
    writeFile (marker ++ ".started") ""
    when (mode == "verdict-wait") (awaitNativeFile (home </> "go"))
    withVerdictLock "lock-probe" "process-lock" $ do
        pid <- getProcessID
        writeFile (marker ++ ".pid") (show pid)
        writeFile (marker ++ ".entered") ""
        when (mode == "verdict-hold") (threadDelay 600000000)
        pure Nothing
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
    (mapM_ (\child -> stopOwnedProcess False child >> waitForProcess child >> pure ()))

testVerdictLocks :: Test
testVerdictLocks = TestList "testVerdictLocks"
    [ TestCase "bracketed lock worker computation is unmasked" verdictWorkerMasking
    , TestCase "same-path threads wait before opening a second Handle" (verdictThreads True)
    , TestCase "different-path threads do not serialize" (verdictThreads False)
    , TestCase "an exception releases the Handle and thread mutex" verdictException
    , TestCase "cancelling a lock holder releases the lock" verdictCancellation
    , TestCase "processes wait for the same verdict lock" verdictProcesses
    , TestCase "a killed process releases the verdict lock" verdictKilledProcess
    , TestCase "validator build flags isolate the verdict namespace" validatorFlagNamespace
    ]

withWorker :: IO () -> (ThreadId -> MVar (Either SomeException ()) -> IO TestResult) -> IO TestResult
withWorker action use = bracket start (killThread . fst) (uncurry use)
  where
    start = do
        done <- newEmptyMVar
        thread <- forkIOWithUnmask $ \unmask -> do
            result <- try (unmask action)
            putMVar done result
        pure (thread, done)

awaitVerdict :: MVar () -> IO ()
awaitVerdict ready = do
    outcome <- timeout 2000000 (takeMVar ready)
    case outcome of
        Just () -> pure ()
        Nothing -> ioError (userError "verdict lock worker did not reach its barrier")

workerResult :: MVar (Either SomeException ()) -> IO (Maybe (Either String ()))
workerResult done = fmap (fmap (either (Left . displayException) Right)) (timeout 2000000 (takeMVar done))

verdictWorkerMasking :: IO TestResult
verdictWorkerMasking = do
    observed <- newEmptyMVar
    withWorker (getMaskingState >>= putMVar observed) $ \_ done -> do
        state <- timeout 2000000 (takeMVar observed)
        result <- workerResult done
        pure $ firstFailure [testAssertEq state (Just Unmasked), testAssertEq result (Just (Right ()))]

verdictThreads :: Bool -> IO TestResult
verdictThreads same = withCacheHome $ \_ -> do
    held <- newEmptyMVar
    release <- newEmptyMVar
    started <- newEmptyMVar
    withWorker (withVerdictLock "lock-probe" "thread-lock" (putMVar held () >> takeMVar release)) $ \_ owner -> do
        awaitVerdict held
        let key = if same then "thread-lock" else "different-thread-lock"
        withWorker (putMVar started () >> withVerdictLock "lock-probe" key (pure ())) $ \_ waiter -> do
            awaitVerdict started
            early <- timeout (if same then 100000 else 2000000) (takeMVar waiter)
            putMVar release ()
            ownerResult <- workerResult owner
            waiterResult <- maybe (workerResult waiter) (pure . Just . either (Left . displayException) Right) early
            pure $ firstFailure
                [ testAssertEq (fmap (either (Left . displayException) Right) early) (if same then Nothing else Just (Right ()))
                , testAssertEq ownerResult (Just (Right ()))
                , testAssertEq waiterResult (Just (Right ()))
                ]

verdictException :: IO TestResult
verdictException = withCacheHome $ \_ -> do
    failed <- try (withVerdictLock "lock-probe" "exception-lock" (throwIO (userError "verdict lock exception"))) :: IO (Either SomeException ())
    retried <- timeout 2000000 (withVerdictLock "lock-probe" "exception-lock" (pure ()))
    pure $ firstFailure
        [ testAssertTrue (either (isInfixOf "verdict lock exception" . displayException) (const False) failed)
        , testAssertEq retried (Just ())
        ]

verdictCancellation :: IO TestResult
verdictCancellation = withCacheHome $ \_ -> do
    held <- newEmptyMVar
    release <- newEmptyMVar
    withWorker (withVerdictLock "lock-probe" "cancelled-lock" (putMVar held () >> takeMVar release)) $ \thread owner -> do
        awaitVerdict held
        killThread thread
        stopped <- workerResult owner
        retried <- timeout 2000000 (withVerdictLock "lock-probe" "cancelled-lock" (pure ()))
        pure $ firstFailure
            [ testAssertTrue (case stopped of Just (Left _) -> True; _ -> False)
            , testAssertEq retried (Just ())
            ]

verdictProcesses :: IO TestResult
verdictProcesses = withCacheHome $ \home ->
    -- Start the child before opening the lock Handle so it cannot inherit that fd.
    withNativeChildren home [("waiter", "verdict-wait")] $ \children -> do
        awaitNativeFile (home </> "waiter.started")
        enteredEarly <- withVerdictLock "lock-probe" "process-lock" $ do
            writeFile (home </> "go") ""
            threadDelay 100000
            doesFileExist (home </> "waiter.entered")
        codes <- mapM (waitChild 5) children
        entered <- doesFileExist (home </> "waiter.entered")
        pure $ firstFailure
            [ testAssertTrue (not enteredEarly)
            , testAssertEq codes [Just ExitSuccess]
            , testAssertTrue entered
            ]

verdictKilledProcess :: IO TestResult
verdictKilledProcess = withNativeHome $ \home ->
    withNativeChildren home [("owner", "verdict-hold")] $ \owners -> do
        awaitNativeFile (home </> "owner.entered")
        stopMarkedChild (home </> "owner.pid") owners
        ownerCodes <- mapM (waitChild 5) owners
        withNativeChildren home [("retry", "verdict")] $ \children -> do
            retryCodes <- mapM (waitChild 5) children
            entered <- doesFileExist (home </> "retry.entered")
            pure $ firstFailure
                [ testAssertTrue (all (maybe False (/= ExitSuccess)) ownerCodes)
                , testAssertEq retryCodes [Just ExitSuccess]
                , testAssertTrue entered
                ]

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
            stopMarkedChild (home </> "owner.pid") owners
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
        copyFileCloexec self copied
        env <- probeEnv home marker []
        let runChild = readProcessOutput
                (proc copied ["testSharedCacheProbe", "--child", "+RTS", "-N1", "-RTS"]){env = Just env} ""
        (code1, _, err1) <- runChild
        first <- readMarker marker
        entries <- entryFiles home
        case (code1, first, entries) of
            (ExitSuccess, Right original, [firstEntry, secondEntry]) -> do
                before <- mapM getModificationTime [firstEntry, secondEntry]
                setModificationTime copied (read "2000-01-01 00:00:00 UTC")
                (code2, _, err2) <- runChild
                second <- readMarker marker
                after <- mapM getModificationTime [firstEntry, secondEntry]
                afterEntries <- entryFiles home
                pure $ firstFailure
                    [ testAssertEq code2 ExitSuccess <? err2
                    , testAssertEq second (Right original)
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
            (Just ExitSuccess, Right expected, [_, _]) -> do
                Just compiledFile <- sharedProgramCacheFile "compile" probeSource
                let entry = home </> "tersus" </> "test-programs" </> takeFileName compiledFile
                Right bytes <- readBinaryMarker entry
                let stale = case decodeProgram expected of
                        Ok program -> ProgramBinary.encodeEntry (replicate 64 '0') program
                        Error e -> error e
                BL.writeFile entry stale
                child <- spawnProbe home []
                code <- waitChild 300 child
                got <- readMarker marker
                repaired <- readBinaryMarker entry
                pure $ firstFailure
                    [ testAssertEq code (Just ExitSuccess)
                    , testAssertEq got (Right expected)
                    , testAssertEq repaired (Right bytes)
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
                    poisoned = ProgramBinary.encodeEntry (takeFileName path) wrong
                createDirectoryIfMissing True (takeDirectory entry)
                BL.writeFile entry poisoned
                child <- spawnProbe home [("PATH", home), ("TERSUS_SHARED_CACHE_PROBE_INVALID", "1")]
                code <- waitChild 300 child
                when (code == Nothing) (stopOwnedProcess False child >> waitForProcess child >> pure ())
                got <- readMarker marker
                after <- readBinaryMarker entry
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
                , case ProgramBinary.decodeEntry (replicate 64 'a') (ProgramBinary.encodeEntry (replicate 64 'a') v) of
                    Left e -> Just e
                    Right decoded -> firstFailure [testAssertEq decoded v, testAssertEq (show decoded) (show v)]
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

-- Disk recompute after an unreadable/miskeyed entry is poisonedEntry's
-- slice (both go through decodeEntry's miss path in TestHarness); this
-- case keeps only the pure decoder rejects that no disk case covers.
corruptRecomputes :: IO TestResult
corruptRecomputes = do
    result <- compileOnce "return 987001;"
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
            BL.writeFile path (ProgramBinary.encodeEntry (replicate 64 '0') program)
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
            runChild = readProcessOutput (proc self ["testSharedCacheProbe", "--child", "+RTS", "-N1", "-RTS"]){env = Just childEnv} ""
        (code1, _, err1) <- runChild
        first <- try (readFile marker >>= \t -> length t `seq` pure t) :: IO (Either IOError String)
        entries <- entryFiles home
        case (code1, first, entries) of
            (ExitSuccess, Right text1, [firstEntry, secondEntry]) -> do
                before <- mapM getModificationTime [firstEntry, secondEntry]
                (code2, _, err2) <- runChild
                second <- try (readFile marker >>= \t -> length t `seq` pure t) :: IO (Either IOError String)
                after <- mapM getModificationTime [firstEntry, secondEntry]
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
            ([Just ExitSuccess, Just ExitSuccess, Just ExitSuccess, Just ExitSuccess], [Right a, Right b, Right c, Right d], [_, _]) ->
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
        holding <- awaitFileWithin (holderMarker ++ ".holding") 100
        if not holding
            then do
                stopOwnedProcess False holder
                pure (Just "the holder never took the lock")
            else do
                waiter <- spawnProbe home [("TERSUS_SHARED_CACHE_PROBE", home </> "waiter-marker")]
                threadDelay 1000000
                stopOwnedProcess False holder
                code <- waitChild 300 waiter
                entries <- entryFiles home
                marker <- readMarker (home </> "waiter-marker")
                pure $ case (code, entries, marker) of
                    (Just ExitSuccess, [_, _], Right _) -> Nothing
                    _ -> Just ("the waiter did not finish after the owner was killed: " ++ show code ++ " entries " ++ show entries))
        `finally` removeDirectoryRecursive home

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
                when isFile (copyCacheFile from (home </> "tersus" </> name))) names
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
spawnProbe = spawnProbeInGroup False

spawnProbeInGroup :: Bool -> FilePath -> [(String, String)] -> IO ProcessHandle
spawnProbeInGroup grouped home extra = do
    self <- getExecutablePath
    let marker = case lookup "TERSUS_SHARED_CACHE_PROBE" extra of
            Just m -> m
            Nothing -> home </> "marker"
    env <- probeEnv home marker extra
    withFile "/dev/null" WriteMode $ \sink -> do
        (_, _, _, handle) <- spawnShared (proc self ["testSharedCacheProbe", "--child", "+RTS", "-N1", "-RTS"]){create_group = grouped, env = Just env, std_out = UseHandle sink, std_err = UseHandle sink}
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

readBinaryMarker :: FilePath -> IO (Either IOError BL.ByteString)
readBinaryMarker = try . ProgramBinary.readEntryBytes

toolValidationParity :: IO TestResult
toolValidationParity =
    let entry = MirHousekeeping.mirEraseEntry
        fresh = case Modules.loadFromEntry (Modules.resolverFromFiles mirPackageFiles) entry of
            Left e -> Error e
            Right (Modules.PackageResult pkg) -> PackageCompile.compileModulesLinked (Modules.packageSnapshot pkg)
            Right _ -> Error "the frozen eraser is not a package"
     in pure (testAssertEq (MirHousekeeping.toolProgram entry) fresh)

-- The compiled tools of a cache (the validator, the emitter, the MIR checker
-- and eraser, the seed and the runtime), copied into another
copyCacheFile :: FilePath -> FilePath -> IO ()
copyCacheFile source target = do
    copyFileCloexec source target
    modified <- getModificationTime source
    setModificationTime target modified

copyCompiledTools :: FilePath -> FilePath -> IO ()
copyCompiledTools from to = do
    createDirectoryIfMissing True to
    names <- listDirectory from
    mapM_ (\name -> do
        regular <- doesFileExist (from </> name)
        when (regular && compiledToolName name) $
            copyCacheFile (from </> name) (to </> name)) names

compiledToolName :: String -> Bool
compiledToolName name = any (`isPrefixOf` name)
    ["validator-", "emitter-", "mir-verify-", "mir-erase-", "seed-", "parser-seed-", "frontend-", "tersus-parser-", "tersus_rt_", "prepared-", "content-key-"]
    && not (".lock" `isInfixOf` name)

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

-- Shared table runner for the overlapping mutate/evaluate slices of the
-- two package-invalidation cases: each named step mutates the fixture,
-- then re-evaluates the entry once. Distinct slices stay in each caller.
runPackageSteps :: FilePath -> [(String, IO ())] -> IO [(String, Result Program String)]
runPackageSteps entry steps = mapM runStep steps
  where
    runStep (name, mutate) = do
        mutate
        result <- validatedFromFile entry
        pure (name, result)

stepResult :: String -> [(String, Result Program String)] -> Result Program String
stepResult name results = case lookup name results of
    Just result -> result
    Nothing -> Error ("missing package step: " ++ name)

namedResult :: String -> TestResult -> TestResult
namedResult _ Nothing = Nothing
namedResult name (Just message) = Just (name ++ ": " ++ message)

packageSnapshots :: IO TestResult
packageSnapshots = do
    home <- freshHome "tersus-shared-package-snapshot"
    (do
        (entry, dependency) <- packageFixture home
        first <- validatedFromFile entry
        same <- validatedFromFile entry
        compiled <- programFromFile entry
        owned <- ownedFromFile entry
        steps <- runPackageSteps entry
            [ ("dependency contents", writeFile dependency "fn value() -> Int { return 2; };")
            , ("dependency contract", writeFile dependency "fn value() -> Int [{ }] [{ affirm return = 3; }] { return 2; };")
            , ("entry import", writeFile dependency "fn value() -> Int { return 2; };" >> writeFile entry "import app::geo::geo::value; return value() + 1;")
            , ("renamed dependency file", renameFile dependency (takeDirectory dependency </> "renamed.tersus"))
            , ("repaired import", writeFile entry "import app::geo::renamed::value; return value() + 1;")
            ]
        let changed = stepResult "dependency contents" steps
            refused = stepResult "dependency contract" steps
            changedEntry = stepResult "entry import" steps
            renamed = stepResult "renamed dependency file" steps
            repaired = stepResult "repaired import" steps
        pure $ case (first, same, compiled, owned, changed, refused, changedEntry, renamed, repaired) of
            (Ok a, Ok b, Ok _, Ok _, Ok c, Error _, Ok d, Error _, Ok _) -> firstFailure
                [ namedResult "same snapshot" (testAssertEq a b)
                , namedResult "dependency contents" (testAssertTrue (a /= c))
                , namedResult "entry import" (testAssertTrue (c /= d))
                ]
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
primeBootstrapTools :: FilePath -> IO ()
primeBootstrapTools home = do
    ready <- TersusParser.runParserTool False ["return 0;"]
    case ready of
        Left e -> fail e
        Right _ -> do
            tool <- TersusParser.parserExecutable
            case tool of
                Error e -> fail e
                Ok executable -> do
                    let source = takeDirectory executable
                        target = home </> "tersus"
                    createDirectoryIfMissing True target
                    names <- listDirectory source
                    mapM_ (\name -> do
                        let output = target </> name
                        exists <- doesFileExist output
                        when (not exists) (copyCacheFile (source </> name) output))
                        [name | name <- names, '.' `notElem` name || ("frontend-" `isPrefixOf` name && ".ll" `isSuffixOf` name),
                            any (`isPrefixOf` name) ["seed-", "parser-seed-", "frontend-", "emitter-", "mir-verify-", "mir-erase-", "tersus-parser-", "validator-", "prepared-", "content-key-"]]

packageProcesses :: IO TestResult
packageProcesses = do
    home <- freshHome "tersus-shared-package-processes"
    (do
        primeBootstrapTools home
        (entry, _) <- packageFixture home
        let run = do
                child <- spawnProbe home [("TERSUS_PACKAGE_CACHE_PROBE", entry), ("TERSUS_PARSER", "native")]
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
        primeBootstrapTools home
        child <- spawnProbe home [("TERSUS_SHARED_CACHE_PARSER_RETRY", "1")]
        code <- waitChild 300 child
        pure (testAssertEq code (Just ExitSuccess))) `finally` removeDirectoryRecursive home

parserRetryProbe :: IO TestResult
parserRetryProbe = do
    Just home <- lookupEnv "XDG_CACHE_HOME"
    -- (the compiler libraries are elaborated once per process; they are in place before the frontend fails)
    primed <- sourceElaboratorExecutable
    libraries <- compileOnce "return 987822;"
    case (primed, libraries) of
        (Error e, _) -> pure (Just e)
        (_, Error e) -> pure (Just e)
        (Ok parser, Ok _) -> do
            let source = "return 987823;"
            permissions <- getPermissions parser
            modified <- getModificationTime parser
            before <- bracket (renameFile parser (parser ++ ".held"))
                (\_ -> do
                    present <- doesFileExist parser
                    when present (removeFile parser)
                    renameFile (parser ++ ".held") parser)
                (\_ -> do
                    writeFile parser "#!/bin/sh\nprintf '%s\\n' 'intentional transient frontend failure' >&2\nexit 23\n"
                    setPermissions parser permissions
                    compileOnce source)
            restoredPermissions <- getPermissions parser
            restoredModified <- getModificationTime parser
            failedFile <- sharedProgramCacheFile "compile" source
            wasFiled <- maybe (pure False) doesFileExist failedFile
            after <- compileOnce source
            pure $ firstFailure
                [ testAssertEq (restoredPermissions, restoredModified) (permissions, modified)
                , testAssertTrue (not wasFiled)
                , case (before, after) of
                    (Error e, Ok _)
                        | "Elaborator tool failure:" `isInfixOf` e
                        , "exit 23" `isInfixOf` e
                        , "intentional transient frontend failure" `isInfixOf` e -> Nothing
                    _ -> Just ("frontend retry: before=" ++ describe before ++ "; after=" ++ describe after)
                ]
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

withToolsCacheHome :: (FilePath -> IO TestResult) -> IO TestResult
withToolsCacheHome use = do
    warm <- compileOnce "return 0;"
    original <- cacheDirectory
    case (warm, original) of
        (Error e, _) -> pure (Just e)
        (_, Error e) -> pure (Just e)
        (Ok _, Ok dir) -> withCacheHome $ \home -> do
            let cache = home </> "tersus"
            copyCompiledTools dir cache
            names <- listDirectory cache
            before <- mapM (toolIdentity cache) names
            entries <- entryFiles home
            result <- use home
            afterNames <- filter compiledToolName <$> listDirectory cache
            after <- mapM (toolIdentity cache) names
            pure $ firstFailure
                [ testAssertEq entries []
                , testAssertTrue (not (null names) && all (not . isPrefixOf "verdicts-") names)
                , result
                , testAssertEq (sort afterNames) (sort names)
                , testAssertEq after before
                ]
  where
    toolIdentity cache name = do
        let path = cache </> name
        digest <- executableDigest path
        time <- getModificationTime path
        pure (digest, time)

packageStages :: IO TestResult
packageStages = withToolsCacheHome $ \home -> do
    (entry, _) <- ciPackageFixture home
    owned <- ownedFromFile entry
    program <- programFromFile entry
    validated <- validatedFromFile entry
    files <- mapM (\stage -> filesystemCacheFile Modules.defaultLoadOptions stage entry) ["owned", "program", "validated"]
    present <- mapM (maybe (pure False) doesFileExist) files
    pure $ case (owned, program, validated) of
        (Ok _, Ok _, Ok original) -> firstFailure
            [ testAssertTrue (and present && length (Map.fromList [(file, ()) | Just file <- files]) == 3)
            , testAssertEq (decodeProgram (encodeProgram original)) (Ok original)
            ]
        other -> Just (show other)

packageInputs :: IO TestResult
packageInputs = withToolsCacheHome $ \home -> do
    (entry, dependency) <- ciPackageFixture home
    original <- validatedFromFile entry
    early <- runPackageSteps entry
        [ ("dependency contents", writeFile dependency "fn answer() -> Int [{ }] [{ }] { return 42; };")
        , ("invalid dependency", writeFile dependency "fn answer() -> Int [{ }] [{ }] { affirm 1 = 2; return 41; };")
        ]
    let changed = stepResult "dependency contents" early
        invalid = stepResult "invalid dependency" early
    invalidFile <- filesystemCacheFile Modules.defaultLoadOptions "validated" entry
    filed <- maybe (pure False) doesFileExist invalidFile
    late <- runPackageSteps entry
        [ ("module layout", writeFile dependency "fn answer() -> Int [{ }] [{ }] { return 41; };" >> writeFile (takeDirectory dependency </> "extra.tersus") "fn extra() -> Int { return 1; };")
        , ("restored dependency", removeFile (takeDirectory dependency </> "extra.tersus"))
        ]
    let layoutChanged = stepResult "module layout" late
        restored = stepResult "restored dependency" late
    pure $ case (original, changed, invalid, layoutChanged, restored) of
        (Ok a, Ok b, Error _, Error _, Ok c) -> firstFailure
            [ namedResult "dependency contents" (testAssertTrue (a /= b))
            , namedResult "restored dependency" (testAssertTrue (a == c))
            , namedResult "invalid dependency not filed" (testAssertTrue (not filed))
            ]
        other -> Just (show other)

ciPackageProcesses :: Bool -> IO TestResult
ciPackageProcesses concurrent =
  -- (each probe has 30 seconds for the package)
  withToolsCacheHome $ \home -> do
    primeBootstrapTools home
    (entry, _) <- ciPackageFixture home
    let markers = if concurrent then ["first" ++ show i | i <- [1 .. 4 :: Int]] else ["first"]
        extra marker = [("TERSUS_PACKAGE_CACHE_PROBE", entry), ("TERSUS_SHARED_CACHE_PROBE", home </> marker), ("TERSUS_PARSER", "native")]
    bracket (mapM (spawnProbe home . extra) markers)
        (mapM_ (\child -> stopOwnedProcess False child >> waitForProcess child >> pure ())) $ \children -> do
        codes <- mapM (waitChild 30) children
        outputs <- mapM (readMarker . (home </>)) markers
        entries <- entryFiles home
        before <- mapM getModificationTime entries
        bracket (spawnProbe home (extra "warm"))
            (\child -> stopOwnedProcess False child >> waitForProcess child >> pure ()) $ \child -> do
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
