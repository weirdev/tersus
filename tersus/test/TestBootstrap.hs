module TestBootstrap (testBootstrap) where

import Control.Concurrent (forkIO, getNumCapabilities)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.QSem (newQSem, signalQSem, waitQSem)
import Control.Exception (SomeException, finally, mask, throwIO, try)
import Control.Monad (forM)
import Data.Char (isHexDigit)
import Data.List (isInfixOf, sort)
import System.Directory (copyFile, createDirectoryIfMissing, getModificationTime, getTemporaryDirectory, listDirectory, removeDirectoryRecursive, doesDirectoryExist)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.FilePath ((</>))

import Bootstrap
import Cli (Command (..), makesIr)
import MirData (writeProgram)
import Pipeline (ownedSource)
import PreludeSource (emitterSource)
import TestHarness
import TestNative (clangAvailable, nativeExamples, validatedPrograms)
import Utils

-- The compiler that compiles itself (step 31 of the roadmap and STEP31.md). The emitter in Tersus (examples/emit.tersus) is built from a seed, the IR of an emitter that is
-- kept in the repository (bootstrap/emitter.ll):
-- - stage 0 is the seed built;
-- - stage 1 is the emitter as it is now, made from the IR that stage 0 writes for it.
-- The fixpoint is that stage 1 writes the same IR for the emitter as stage 0 does (so that the emitter built by stage 1 would be stage 1 again); stage 1 is the one
-- that compiles programs, and it has to write the IR of every example and every program that native code is tested with (what that IR does when it is built and run
-- is TestNative's to check). The cache that both stages are kept in is tested too. The stages need clang, and the tests pass without it.
testBootstrap :: Test
testBootstrap =
    TestList
        "testBootstrap"
        [ TestCase "the hashes of what the emitter is made of" hashShape
        , TestCase "the commands that make IR" commands
        , TestCase "the seed, stage 0 and stage 1 are a fixpoint, and the cache keeps them" bootstrap
        ]

hashShape :: IO TestResult
hashShape =
    pure $
        if all (\h -> length h == 16 && all isHexDigit h) [seedHash, emitterHash] && seedHash /= emitterHash
            then Nothing
            else Just ("the hashes are " ++ show (seedHash, emitterHash))

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

-- Every program that native code is tested with
programs :: IO [(String, String)]
programs = do
    files <- forM nativeExamples (\path -> (,) path <$> readFile path)
    pure (files ++ validatedPrograms)

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
                            all' <- programs
                            fixpoint <- sameEmitter zero one
                            written <- parallelFor all' (writesIr one)
                            kept <- cache zero one
                            pure $ case fixpoint ++ concat written of
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
    -- Stage 1 writes the IR of a program
    writesIr exe (name, source) = case ownedSource source of
        Error e -> pure [name ++ ": " ++ e]
        Ok owned -> do
            written <- emitWith exe (writeProgram owned)
            pure $ case written of
                Ok text | "@tersus_main" `isInfixOf` text -> []
                Ok _ -> [name ++ ": the IR has no entry point"]
                Error e -> [name ++ ": " ++ take 300 e]

-- The results of an action over each of a list, with as many at once as there are cores (the programs are independent, and what takes the time is the front end
-- and the emitter, which use one core each)
parallelFor :: [a] -> (a -> IO b) -> IO [b]
parallelFor xs action = do
    cores <- getNumCapabilities
    slots <- newQSem cores
    vars <- forM xs $ \x -> do
        var <- newEmptyMVar
        _ <- forkIO (mask (\restore -> waitQSem slots >> (try (restore (action x)) >>= \r -> signalQSem slots >> putMVar var r)))
        pure var
    forM vars (\var -> takeMVar var >>= either (\e -> throwIO (e :: SomeException)) pure)

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
