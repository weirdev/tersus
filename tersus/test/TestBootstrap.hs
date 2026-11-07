module TestBootstrap (testBootstrap) where

import Control.Exception (bracket)
import Data.Char (isHexDigit)
import Data.List (sort)
import System.Directory (createDirectory, getModificationTime, getTemporaryDirectory, listDirectory, removeDirectoryRecursive, removeFile, doesDirectoryExist, doesFileExist)
import System.Environment (getEnvironment, getExecutablePath, lookupEnv)
import System.Exit (ExitCode (..))
import System.Process (CreateProcess (..), proc)
import Native (readProcessOutput)
import System.IO (hClose)
import CacheLock (openTempFileCloexec)
import System.FilePath (takeFileName, (</>))
import System.Posix.Process (getProcessID)

import qualified TersusParser
import Seed (parserSeedHash, parserSeedSha256, parserSeedUrl)
import Bootstrap
import Cli (Command (..), makesIr)
import MirData (writeProgram)
import Pipeline (ownedSource)
import Hash (fingerprint)
import MirHousekeeping (Tool (..), emitterEntry, emitterOwnedProgram, ownedToolWith, ownershipTool)
import PreludeSource (compilerSourceHash, libPackageFiles, mirPackageFiles, stdlibSource)
import TestHarness
import TestNative (clangAvailable)
import Utils

-- The compiler that compiles itself (step 31 of the roadmap and STEP31.md). The emitter in Tersus (lib/mir/emit/emit.tersus) is built from a seed, the IR of an emitter that is
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
        , TestCase "overlapping bootstrap directories retain their own files and cleanup" directoryIsolation
        , TestCase "cold bootstrap reaches a fixpoint and preserves cache entries" coldBootstrap
        ]

hashShape :: IO TestResult
hashShape =
    pure $
        if all (\h -> length h == 16 && all isHexDigit h) [seedHash, compilerSnapshotHash] && seedHash /= compilerSnapshotHash
            && compilerSnapshotHash == fingerprint ([seedHash, parserSeedHash] ++ concatMap (\(path, contents) -> [path, contents]) (mirPackageFiles ++ libPackageFiles) ++ [stdlibSource, compilerSourceHash])
            then Nothing
            else Just ("the hashes are " ++ show (seedHash, compilerSnapshotHash))

seedPin :: IO TestResult
seedPin =
    pure $
        if length seedSha256 == 64 && all isHexDigit seedSha256 && seedUrl == "https://github.com/weirdev/tersus/releases/download/bootstrap-" ++ take 12 seedSha256 ++ "/emitter.ll"
            && length parserSeedSha256 == 64 && all isHexDigit parserSeedSha256
            && parserSeedUrl == "https://github.com/weirdev/tersus/releases/download/bootstrap-" ++ take 12 parserSeedSha256 ++ "/parser.ll"
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

withDirectory :: String -> (FilePath -> IO a) -> IO a
withDirectory name = bracket make removeDirectoryRecursive
  where
    make = do
        tmp <- getTemporaryDirectory
        pid <- getProcessID
        (dir, handle) <- openTempFileCloexec tmp (name ++ "-" ++ show pid)
        hClose handle
        removeFile dir
        createDirectory dir
        pure dir

directoryIsolation :: IO TestResult
directoryIsolation = do
    (result, outer) <- withDirectory "tersus-bootstrap-directory-test" $ \outer -> do
        let marker = outer </> "outer"
        writeFile marker "kept"
        (inner, inside) <- withDirectory "tersus-bootstrap-directory-test" $ \inner -> do
            kept <- doesFileExist marker
            pure (inner, firstFailure [testAssertEq (inner /= outer) True, testAssertEq kept True])
        kept <- doesFileExist marker
        innerExists <- doesDirectoryExist inner
        pure (firstFailure [inside, testAssertEq kept True, testAssertEq innerExists False], outer)
    outerExists <- doesDirectoryExist outer
    pure (firstFailure [result, testAssertEq outerExists False])

coldBootstrap :: IO TestResult
coldBootstrap = do
    child <- lookupEnv "TERSUS_EMITTER_BOOTSTRAP_WORKER"
    case child of
        Just "1" -> bootstrap
        _ -> withDirectory "tersus-bootstrap-cold" $ \home -> do
            self <- getExecutablePath
            inherited <- getEnvironment
            let environment = [("TERSUS_EMITTER_BOOTSTRAP_WORKER", "1"), ("XDG_CACHE_HOME", home)] ++ [(key, value) | (key, value) <- inherited, key `notElem` ["TERSUS_EMITTER_BOOTSTRAP_WORKER", "XDG_CACHE_HOME"]]
            (status, out, err) <- readProcessOutput (proc self ["testBootstrap", "--child", "+RTS", "-N1", "-RTS"]){env = Just environment} ""
            pure $ case status of
                ExitSuccess -> Nothing
                _ -> Just ("fresh emitter bootstrap worker: " ++ out ++ err)

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
                            nativeParser <- TersusParser.runParserTool False ["return 0;"]
                            fixpoint <- sameEmitter zero one
                            kept <- cache zero one
                            pure $ case nativeParser of
                                Left err -> Just ("native parser bootstrap smoke: " ++ err)
                                Right _ -> case fixpoint of
                                    [] -> kept
                                    found -> Just (unlines (take 5 found))
  where
    -- Stage 0 and stage 1 each expand and own the emitter's source and write its IR: the same owned MIR, the same IR, and that IR
    -- is the pinned seed, so the emitter built by stage 1 would be stage 1 again
    -- (the pipeline's owned emitter is stage 1's: its ownership tool is the stage 1 executable, which is checked first)
    sameEmitter zero one = do
        fromZero <- ownedToolWith zero emitterEntry
        tool <- ownershipTool
        case tool of
            ToolNative path | path /= one -> pure ["the pipeline's ownership tool is not stage 1: " ++ path]
            ToolNative _ -> compareOwned fromZero
            ToolFailed e -> pure ["the pipeline's ownership tool: " ++ e]
            ToolInterpreted _ -> pure ["the pipeline's ownership tool is interpreted, not stage 1"]
      where
        compareOwned fromZero = case (fromZero, emitterOwnedProgram) of
            (Error e, _) -> pure ["stage 0 owning the emitter: " ++ e]
            (_, Error e) -> pure ["stage 1 owning the emitter: " ++ e]
            (Ok owned0, Ok owned1)
                | owned0 /= owned1 -> pure ["stage 0 and stage 1 own the emitter differently"]
                | otherwise -> do
                    irZero <- emitWith zero (writeProgram owned0)
                    irOne <- emitWith one (writeProgram owned1)
                    pinned <- case irOne of
                        Ok text -> isPinnedSeed text
                        Error _ -> pure True
                    pure ([ "the emitter: stage 1 " ++ describe irOne irZero | not (sameIr irOne irZero) ] ++ [ "the emitter's IR is not the seed pinned by bootstrap/emitter.sha256" | not pinned ])
        sameIr (Ok a) (Ok b) = a == b
        sameIr _ _ = False
        describe (Ok text) (Ok expected) = "wrote " ++ show (length text) ++ " bytes for " ++ show (length expected) ++ firstDifference text expected
        describe (Error e) _ = "failed: " ++ take 300 e
        describe _ (Error e) = "stage 0 failed: " ++ take 300 e

isPinnedSeed :: String -> IO Bool
isPinnedSeed ir = do
    (status, out, _) <- readProcessOutput (proc "sha256sum" []) ir
    pure (status == ExitSuccess && takeWhile (/= ' ') out == seedSha256)
-- Where the first line that differs is
firstDifference :: String -> String -> String
firstDifference output text = case [(n, a, b) | (n, a, b) <- zip3 [1 :: Int ..] (lines output) (lines text), a /= b] of
    (n, a, b) : _ -> "; line " ++ show n ++ ": " ++ show a ++ " for " ++ show b
    [] -> ""

cache :: FilePath -> FilePath -> IO TestResult
cache zero one = do
    selected <- lookupEnv "XDG_CACHE_HOME"
    case selected of
        Nothing -> pure (Just "cold cache directory was not set")
        Just home -> do
            let directory = home </> "tersus"
                source = "x = 6 * 7; return x;"
            primed <- tersusLlvm source
            case primed of
                Error e -> pure (Just e)
                Ok initial -> do
                    parserIdentity <- TersusParser.parserKey
                    names <- sort <$> listDirectory directory
                    before <- mapM (getModificationTime . (directory </>)) names
                    reusedZero <- cachedSeed
                    reusedOne <- cachedEmitter
                    ir <- tersusLlvm source
                    expected <- case ownedSource source of
                        Error e -> pure (Error e)
                        Ok owned -> emitWith one (writeProgram owned)
                    afterNames <- sort <$> listDirectory directory
                    after <- mapM (getModificationTime . (directory </>)) names
                    pure $ case (ir, expected) of
                        (Ok text, Ok fromStage1) -> firstFailure
                            [ if text == fromStage1 && text == initial then Nothing else Just "the IR is not what stage 1 writes"
                            , testAssertEq (reusedZero, reusedOne) (Ok zero, Ok one)
                            , testAssertEq (afterNames, after) (names, before)
                            , case parserIdentity of
                                Error e -> Just e
                                Ok key -> testAssertTrue (all (`elem` names)
                                    ["seed-" ++ seedHash, "parser-seed-" ++ parserSeedHash, takeFileName one, "tersus-parser-" ++ key])
                            ]
                        (Error e, _) -> Just e
                        (_, Error e) -> Just e
