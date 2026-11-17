module TestEmitterProvenance (testEmitterProvenance) where

import Control.Exception (bracket, evaluate)
import Control.Concurrent (forkFinally)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar, tryPutMVar, withMVar)
import Data.List (isPrefixOf)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.Directory (createDirectory, createDirectoryIfMissing, getCurrentDirectory, getTemporaryDirectory,
    removeDirectoryRecursive, removeFile, setCurrentDirectory, createFileLink, listDirectory)
import System.FilePath ((</>))
import System.IO (hClose)
import CacheLock (openTempFileCloexec)
import EmitterProvenance (approvedEmitterBuild, constructionIdentity, matchesConstruction, workingSourcesMatch, checkEmitterOutputs)
import PreludeSource (emitterConstructionOf)
import MirHousekeeping (guardEmitterDirectory, cachedEmitterContentKeyFor)
import Native (cacheDirectory, cacheLock, cachedProgramIfPresent)
import TestHarness
import Utils


testEmitterProvenance :: Test
testEmitterProvenance = TestList "testEmitterProvenance"
    [ TestCase "unknown, malformed and mismatched association cannot select the published emitter" $ pure $
        testAssertTrue (all (\(actual, expected) -> not (matchesConstruction actual expected))
            [(Ok Nothing, digest), (Error "unapproved", digest),
                (Ok (Just digest), ""), (Ok (Just digest), replicate 64 'x'),
                (Ok (Just digest), replicate 64 'b')])
    , TestCase "exact approved construction is a match" $ pure $
        testAssertTrue (matchesConstruction (Ok (Just digest)) digest)
    , TestCase "unapproved construction has no inferred identity" $ case approvedEmitterBuild of
        Just _ -> pure Nothing
        Nothing -> constructionIdentity ["input"] >>= \actual -> pure (testAssertEq actual (Ok Nothing))
    , TestCase "working source matches captured content and module listings" $ inSource $ \files ->
        workingSourcesMatch files >>= \same -> pure (testAssertTrue same)
    , TestCase "changed source misses and a restored source can match again" $ inSource $ \files -> do
        writeFile "src/Provider.hs" "changed"
        changed <- workingSourcesMatch files
        writeFile "src/Provider.hs" "captured"
        restored <- workingSourcesMatch files
        pure (testAssertEq (changed, restored) (False, True))
    , TestCase "a new sibling module file invalidates the captured source" $ inSource $ \files -> do
        writeFile "lib/mir/provider/added.tersus" "fn added() -> Int { return 1; };"
        same <- workingSourcesMatch files
        pure (testAssertTrue (not same))
    , TestCase "missing source cannot select the pin" $ inSource $ \files -> do
        removeFile "src/Provider.hs"
        same <- workingSourcesMatch files
        pure (testAssertTrue (not same))
    , TestCase "new Haskell boot source invalidates the build source listing" $ inSource $ \files -> do
        writeFile "src/Provider.hs-boot" "module Provider where"
        same <- workingSourcesMatch files
        pure (testAssertTrue (not same))
    , TestCase "unrelated root lib example does not change the selected compiler libraries" $ inSource $ \files -> do
        writeFile "lib/example.tersus" "return 4;"
        same <- workingSourcesMatch files
        pure (testAssertTrue same)
    , TestCase "deleting a checkout marker does not turn changed source into an installed binary" $ inSource $ \files -> do
        removeFile "package.yaml"
        writeFile "src/Provider.hs" "changed without marker"
        same <- workingSourcesMatch files
        pure (testAssertTrue (not same))
    , TestCase "an exact optional pin record accepts two words but refuses a third" $ inSource $ \_ -> do
        let pin = "candidate.pin"
        writeFile pin (digest ++ " " ++ digest ++ " EXTRA\n")
        extra <- emitterConstructionOf <$> strictText pin
        writeFile pin (digest ++ " " ++ digest ++ "\n")
        exact <- emitterConstructionOf <$> strictText pin
        writeFile pin (digest ++ "\n")
        absent <- emitterConstructionOf <$> strictText pin
        pure (testAssertEq (extra, exact, absent) ("", digest, ""))
    , TestCase "canonical output collisions perform no writes" outputCollisions
    , TestCase "a warm cache hit cannot discard a directory changed while waiting" warmDirectoryDrift
    , TestCase "a key provider directory change refuses before key publication" keyDirectoryDrift
    ]
  where
    digest = replicate 64 'a'

inSource :: ([(FilePath, String)] -> IO TestResult) -> IO TestResult
inSource use = bracket temporary removeDirectoryRecursive $ \directory -> do
    original <- getCurrentDirectory
    bracket (setCurrentDirectory directory) (const (setCurrentDirectory original)) $ \_ -> do
        let files = [("package.yaml", "name: captured"), ("src/Provider.hs", "captured"),
                ("lib/mir/provider/provider.tersus", "fn answer() -> Int { return 2; };"),
                ("lib/stdlib.tersus", "captured standard library")]
        createDirectoryIfMissing True "src"
        createDirectoryIfMissing True "lib/mir/provider"
        mapM_ (uncurry writeFile) files
        use files
  where
    temporary = do
        parent <- getTemporaryDirectory
        (path, handle) <- openTempFileCloexec parent "tersus-provenance-source.tmp"
        hClose handle
        removeFile path
        createDirectory path
        pure path

strictText :: FilePath -> IO String
strictText path = do
    text <- readFile path
    _ <- evaluate (length text)
    pure text

outputCollisions :: IO TestResult
outputCollisions = inSource $ \_ -> do
    createDirectory "bootstrap"
    createDirectory "relative"
    let protected = ["src/Provider.hs", "bootstrap/emitter.sha256", "seed.ll"]
        existing = protected ++ ["candidate.ll", "candidate.pin"]
    mapM_ (\path -> writeFile path ("original " ++ path)) existing
    createFileLink "src/Provider.hs" "source-link"
    createFileLink "bootstrap/emitter.sha256" "pin-link"
    createFileLink "seed.ll" "seed-link"
    let collisions = [["candidate.ll", "candidate.ll"], ["candidate.ll", "relative/../candidate.ll"],
            ["src/Provider.hs", "candidate.pin"], ["source-link", "candidate.pin"],
            ["pin-link", "candidate.pin"], ["candidate.ll", "seed-link"],
            ["bootstrap/emitter.sha256", "candidate.pin"]]
    before <- mapM strictText existing
    outcomes <- mapM (\outputs -> do
        checked <- checkEmitterOutputs protected outputs
        case checked of
            Error _ -> pure True
            Ok () -> mapM_ (\path -> writeFile path "unexpected publication") outputs >> pure False) collisions
    after <- mapM strictText existing
    valid <- checkEmitterOutputs protected ["candidate.ll", "candidate.pin"]
    pure (testAssertTrue (and outcomes && before == after && valid == Ok ()))

withCacheHomes :: (FilePath -> FilePath -> IO TestResult) -> IO TestResult
withCacheHomes use = inSource $ \_ -> do
    original <- lookupEnv "XDG_CACHE_HOME"
    directory <- getCurrentDirectory
    let first = directory </> "cache-a"
        second = directory </> "cache-b"
        restore = maybe (unsetEnv "XDG_CACHE_HOME") (setEnv "XDG_CACHE_HOME") original
    bracket (setEnv "XDG_CACHE_HOME" first) (const restore) $ \_ -> use first second

warmDirectoryDrift :: IO TestResult
warmDirectoryDrift = withCacheHomes $ \first second -> do
    initial <- cacheDirectory
    directory <- case initial of Error e -> fail e; Ok path -> pure path
    setEnv "XDG_CACHE_HOME" second
    other <- cacheDirectory
    otherDirectory <- case other of Error e -> fail e; Ok path -> pure path
    writeFile (otherDirectory </> "warm-key") "existing executable"
    setEnv "XDG_CACHE_HOME" first
    mutex <- cacheLock "warmkey"
    started <- newEmptyMVar
    finished <- newEmptyMVar
    withMVar mutex $ \_ -> do
        _ <- forkFinally (guardEmitterDirectory (True, "key", directory) $ do
                putMVar started ()
                cachedProgramIfPresent "warm" "key") $ \result -> do
                    _ <- tryPutMVar started ()
                    putMVar finished result
        takeMVar started
        setEnv "XDG_CACHE_HOME" second
    result <- takeMVar finished
    pure (case result of
        Right (Error _) -> Nothing
        Left e -> Just ("warm lookup failed unexpectedly: " ++ show e)
        Right (Ok _) -> Just "the selected directory was lost on a real warm lookup")

keyDirectoryDrift :: IO TestResult
keyDirectoryDrift = withCacheHomes $ \_ second -> do
    initial <- cacheDirectory
    directory <- case initial of Error e -> fail e; Ok path -> pure path
    result <- cachedEmitterContentKeyFor (True, "unit-producer", directory) "unit-key" [] [] $ do
        setEnv "XDG_CACHE_HOME" second
        pure (Ok "generated-key")
    names <- listDirectory directory
    pure (case result of
        Error _ | not (any ("content-key-" `isPrefixOf`) names) -> Nothing
        _ -> Just "a changed key-provider directory was accepted or published")
