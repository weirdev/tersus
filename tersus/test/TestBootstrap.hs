module TestBootstrap (testBootstrap) where

import Control.Concurrent (forkIO, getNumCapabilities)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.QSem (newQSem, signalQSem, waitQSem)
import Control.Exception (SomeException, finally, mask, throwIO, try)
import Control.Monad (forM)
import Data.Char (isHexDigit)
import System.Directory (copyFile, createDirectoryIfMissing, getModificationTime, getTemporaryDirectory, listDirectory, removeDirectoryRecursive, doesDirectoryExist)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.FilePath ((</>))

import Bootstrap
import Cli (Command (..), makesIr, splitEmitterFlag)
import MirData (writeProgram)
import LlvmEmit (emitOwned)
import Pipeline (llvmSource, ownedSource)
import PreludeSource (emitterSource)
import TestHarness
import TestNative (clangAvailable, nativeExamples, validatedPrograms)
import Utils

-- -- The compiler that compiles itself (step 31 of the roadmap and STEP31.md). The emitter in Tersus (examples/emit.tersus) is built in two stages:
-- - stage 0 is made from the IR that the Haskell emitter (LlvmEmit) writes for it;
-- - stage 1 is made from the IR that stage 0 writes for it.
-- The fixpoint is that the IR is the same text at both stages, and that stage 1 writes for every example and every program what the Haskell writes. The flag that makes
-- the command line use the emitter in Tersus, and the cache that stage 0 is kept in, are tested too. Stage 0 writes the same IR as the Haskell for every program, which
-- `TestMirEmit` checks, so here it is only asked for the emitter's own. The stages need clang, and the tests pass without it.
testBootstrap :: Test
testBootstrap =
    TestList
        "testBootstrap"
        [ TestCase "the hash of the sources of the emitter" hashShape
        , TestCase "the flag of the emitter in Tersus" flag
        , TestCase "stage 0 and stage 1 are a fixpoint, and the cache keeps stage 0" bootstrap
        ]

hashShape :: IO TestResult
hashShape = pure $ if length emitterHash == 16 && all isHexDigit emitterHash then Nothing else Just ("the hash is " ++ show emitterHash)

flag :: IO TestResult
flag =
    pure $
        firstFailure
            [ testAssertEq (splitEmitterFlag ["--tersus-emitter", "build", "a.tersus", "-o", "a"]) (True, ["build", "a.tersus", "-o", "a"])
            , testAssertEq (splitEmitterFlag ["run", "a.tersus", "--tersus-emitter"]) (False, ["run", "a.tersus", "--tersus-emitter"])
            , testAssertEq (map makesIr [Llvm, Run, Build "a"]) [True, True, True]
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

-- Every program that native code is tested with, as the MIR as data and the IR that LlvmEmit writes
programs :: IO [(String, String)]
programs = do
    files <- forM nativeExamples (\path -> (,) path <$> readFile path)
    pure (files ++ validatedPrograms)

bootstrap :: IO TestResult
bootstrap = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else withDirectory "tersus-bootstrap-test" $ \dir -> do
            let zero = dir </> "stage0"
                one = dir </> "stage1"
            built0 <- stageZero zero
            case built0 of
                Error e -> pure (Just ("stage 0: " ++ e))
                Ok () -> do
                    built1 <- stageOne zero one
                    case built1 of
                        Error e -> pure (Just ("stage 1: " ++ e))
                        Ok () -> do
                            all' <- programs
                            -- (stage 0 gives the IR that it was built from, and stage 1 what the Haskell gives for every program)
                            atZero <- check [("stage 0", zero)] ("the emitter", emitterSource)
                            atOne <- parallelFor (("the emitter", emitterSource) : all') (check [("stage 1", one)])
                            kept <- cache zero
                            pure $ case atZero ++ concat atOne of
                                [] -> kept
                                found -> Just (unlines (take 5 found))
  where
    -- (the IR that llvmSource gives is that of emitOwned over the owned MIR)
    check stages (name, source) = case ownedSource source of
        Error e -> pure [name ++ ": " ++ e]
        Ok owned -> case emitOwned owned of
            Error e -> pure [name ++ ": " ++ e]
            Ok expected -> do
                results <- forM stages (\(stage, exe) -> (,) stage <$> emitWith exe (writeProgram owned))
                pure [name ++ ": " ++ stage ++ " " ++ describe r expected | (stage, r) <- results, not (sameIr r expected)]
    sameIr (Ok text) expected = text == expected
    sameIr (Error _) _ = False
    describe (Ok text) expected = "wrote " ++ show (length text) ++ " bytes for " ++ show (length expected) ++ firstDifference text expected
    describe (Error e) _ = "failed: " ++ take 300 e

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

-- The emitter that is in the cache is used, and not built again: a program is compiled with the cache that holds a copy of stage 0 and nothing else, and the
-- copy has not been written to
cache :: FilePath -> IO TestResult
cache zero = withDirectory "tersus-cache-test" $ \home -> do
    saved <- lookupEnv "XDG_CACHE_HOME"
    let restore = maybe (unsetEnv "XDG_CACHE_HOME") (setEnv "XDG_CACHE_HOME") saved
        kept = home </> "tersus" </> ("emitter-" ++ emitterHash)
    (do
        createDirectoryIfMissing True (home </> "tersus")
        copyFile zero kept
        setEnv "XDG_CACHE_HOME" home
        before <- getModificationTime kept
        let source = "x = 6 * 7; return x;"
        ir <- tersusLlvm source
        after <- getModificationTime kept
        entries <- listDirectory (home </> "tersus")
        pure $ case (ir, llvmSource source) of
            (Ok text, Ok expected)
                | text /= expected -> Just "the IR is not what the Haskell writes"
                | before /= after || entries /= ["emitter-" ++ emitterHash] -> Just ("the cache was written to: " ++ show entries)
                | otherwise -> Nothing
            (Error e, _) -> Just e
            (_, Error e) -> Just e)
        `finally` restore
