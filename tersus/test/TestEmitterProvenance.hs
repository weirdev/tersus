module TestEmitterProvenance (testEmitterProvenance) where

import Control.Exception (bracket)
import System.Directory (createDirectory, createDirectoryIfMissing, getCurrentDirectory, getTemporaryDirectory,
    removeDirectoryRecursive, removeFile, setCurrentDirectory)
import System.FilePath ((</>))
import System.IO (hClose)
import CacheLock (openTempFileCloexec)
import EmitterProvenance (approvedEmitterBuild, constructionIdentity, matchesConstruction, workingSourcesMatch)
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
