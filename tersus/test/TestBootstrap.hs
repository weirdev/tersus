module TestBootstrap (testBootstrap) where

import Control.Exception (finally)
import Data.Char (isHexDigit)
import Data.List (sort)
import System.Directory (copyFile, createDirectoryIfMissing, getModificationTime, getTemporaryDirectory, listDirectory, removeDirectoryRecursive, doesDirectoryExist)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.FilePath ((</>))

import Bootstrap
import Cli (Command (..), makesIr)
import MirData (writeProgram)
import Pipeline (ownedSource)
import PreludeSource (emitterSource)
import TestHarness
import TestNative (clangAvailable)
import Utils

-- The compiler that compiles itself (step 31 of the roadmap and STEP31.md). The emitter in Tersus (examples/emit.tersus) is built from a seed, the IR of an emitter that is
-- a GitHub release asset pinned by bootstrap/emitter.sha256 (see Bootstrap):
-- - stage 0 is the seed built;
-- - stage 1 is the emitter as it is now, made from the IR that stage 0 writes for it.
-- The fixpoint is that stage 1 writes the same IR for the emitter as stage 0 does (so that the emitter built by stage 1 would be stage 1 again); stage 1 is the one
-- that compiles programs. That stage 1 writes the IR of every example and every program that native code is tested with is TestMirEmit's to check (it runs the
-- emitter stage 1 built, in every mode, on the same programs), and what that IR does when it is built and run is TestNative's. The cache that both stages are
-- kept in is tested too. The stages need clang, and the tests pass without it.
testBootstrap :: Test
testBootstrap =
    TestList
        "testBootstrap"
        [ TestCase "the hashes of what the emitter is made of" hashShape
        , TestCase "the seed pin and its release" seedPin
        , TestCase "the commands that make IR" commands
        , TestCase "the seed, stage 0 and stage 1 are a fixpoint, and the cache keeps them" bootstrap
        ]

hashShape :: IO TestResult
hashShape =
    pure $
        if all (\h -> length h == 16 && all isHexDigit h) [seedHash, emitterHash] && seedHash /= emitterHash
            then Nothing
            else Just ("the hashes are " ++ show (seedHash, emitterHash))

seedPin :: IO TestResult
seedPin =
    pure $
        if length seedSha256 == 64 && all isHexDigit seedSha256 && seedUrl == "https://github.com/weirdev/tersus/releases/download/bootstrap-" ++ take 12 seedSha256 ++ "/emitter.ll"
            then Nothing
            else Just ("the seed pin is " ++ show seedSha256 ++ " and its release is " ++ seedUrl)

commands :: IO TestResult
commands =
    pure $
        firstFailure
            [ testAssertEq (map makesIr [Llvm, Run, Build "a"]) [True, True, True]
            , testAssertEq (map makesIr [Check, Interpret, Mir, MirText, Owned]) [False, False, False, False, False]
            ]

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [failure | Just failure <- results] of
    failure : _ -> Just failure
    [] -> Nothing

-- A directory of the tests' own, emptied and made again
withDirectory :: String -> (FilePath -> IO a) -> IO a
withDirectory name use = do
    tmp <- getTemporaryDirectory
    let dir = tmp </> name
    exists <- doesDirectoryExist dir
    if exists then removeDirectoryRecursive dir else pure ()
    createDirectoryIfMissing True dir
    use dir `finally` removeDirectoryRecursive dir

bootstrap :: IO TestResult
bootstrap = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else do
            -- (the stages as they are kept for the compiler itself: stageZero and stageOne built them, and a run of the tests
            -- that finds them there does not build them again)
            built0 <- cachedSeed
            case built0 of
                Error e -> pure (Just ("stage 0: " ++ e))
                Ok zero -> do
                    built1 <- cachedEmitter
                    case built1 of
                        Error e -> pure (Just ("stage 1: " ++ e))
                        Ok one -> do
                            fixpoint <- sameEmitter zero one
                            kept <- cache zero one
                            pure $ case fixpoint of
                                [] -> kept
                                found -> Just (unlines (take 5 found))
  where
    -- Stage 0 and stage 1 write the same IR for the emitter, so the emitter built by stage 1 would be stage 1 again
    sameEmitter zero one = case ownedSource emitterSource of
        Error e -> pure ["the emitter: " ++ e]
        Ok owned -> do
            fromZero <- emitWith zero (writeProgram owned)
            fromOne <- emitWith one (writeProgram owned)
            pure [ "the emitter: stage 1 " ++ describe fromOne fromZero | not (sameIr fromOne fromZero) ]
      where
        sameIr (Ok a) (Ok b) = a == b
        sameIr _ _ = False
        describe (Ok text) (Ok expected) = "wrote " ++ show (length text) ++ " bytes for " ++ show (length expected) ++ firstDifference text expected
        describe (Error e) _ = "failed: " ++ take 300 e
        describe _ (Error e) = "stage 0 failed: " ++ take 300 e
-- Where the first line that differs is
firstDifference :: String -> String -> String
firstDifference output text = case [(n, a, b) | (n, a, b) <- zip3 [1 :: Int ..] (lines output) (lines text), a /= b] of
    (n, a, b) : _ -> "; line " ++ show n ++ ": " ++ show a ++ " for " ++ show b
    [] -> ""

-- The emitters that are in the cache are used, and not built again: a program is compiled with the cache that holds a copy of each and nothing else, and the copies
-- have not been written to
cache :: FilePath -> FilePath -> IO TestResult
cache zero one = withDirectory "tersus-cache-test" $ \home -> do
    saved <- lookupEnv "XDG_CACHE_HOME"
    let restore = maybe (unsetEnv "XDG_CACHE_HOME") (setEnv "XDG_CACHE_HOME") saved
        names = ["seed-" ++ seedHash, "emitter-" ++ emitterHash]
        kept = [home </> "tersus" </> name | name <- names]
    (do
        createDirectoryIfMissing True (home </> "tersus")
        mapM_ (uncurry copyFile) (zip [zero, one] kept)
        setEnv "XDG_CACHE_HOME" home
        before <- mapM getModificationTime kept
        let source = "x = 6 * 7; return x;"
        ir <- tersusLlvm source
        expected <- case ownedSource source of
            Error e -> pure (Error e)
            Ok owned -> emitWith one (writeProgram owned)
        after <- mapM getModificationTime kept
        entries <- listDirectory (home </> "tersus")
        pure $ case (ir, expected) of
            (Ok text, Ok fromStage1)
                | text /= fromStage1 -> Just "the IR is not what stage 1 writes"
                | before /= after || sort entries /= sort names -> Just ("the cache was written to: " ++ show entries)
                | otherwise -> Nothing
            (Error e, _) -> Just e
            (_, Error e) -> Just e)
        `finally` restore
