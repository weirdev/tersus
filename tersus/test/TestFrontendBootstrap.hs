-- REPLACING_HASKELL.md, "The frontend seed": F0 is the elaborator written in Tersus built from pinned IR, F1 the
-- elaborator as it is now elaborated by F0, and F2 the same elaborated by F1.
module TestFrontendBootstrap (testFrontendBootstrap) where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (MVar, modifyMVar, newEmptyMVar, newMVar, putMVar, takeMVar)
import Control.Exception (SomeException, bracket, evaluate, throwIO, try)
import Data.Char (isHexDigit)
import Data.List (isInfixOf)
import System.Directory (createDirectory, getTemporaryDirectory, removeDirectoryRecursive, removeFile)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.FilePath ((</>))
import System.IO (hClose, hPutStr)
import System.IO.Unsafe (unsafePerformIO)

import CacheLock (openTempFileCloexec)
import Differential (Answers, Asked (..), Outcome (..), Unit (..), bootstrapFrontend, compareAnswers, executableCandidate, unitRequests)
import Compile (sourceRequest)
import ElaborateRequest (LoadKind (..), LoadResponse (..), Response (..))
import ElaboratorNative (frontendStage)
import ElaboratorTool (frontendSources, frontendToolFailure, nativeElaborator, nativeLoader)
import LibPackage (compileLibPackageWith)
import MirHousekeeping (emitterEntry, toolProgram, toolProgramWith, validationEntry)
import Native (cachedProgramIfPresent, cachedProgramIfPresentWithArtifacts)
import PreludeSource (frontendSeedSha256, frontendSeedSources)
import Seed (cachedFrontendSeed, frontendSeedHash)
import TestHarness
import Utils

testFrontendBootstrap :: Test
testFrontendBootstrap =
    TestList "testFrontendBootstrap"
        [ testCase "the seed pin is a SHA-256 digest" (testAssertTrue (length frontendSeedSha256 == 64 && all isHexDigit frontendSeedSha256))
        , testCase "the pin records the elaborator's sources as they are (a change to them comes with a new seed)" $
            testAssertEq frontendSources (Ok frontendSeedSources)
        -- (each waits for stage 1, which one of them builds, and then they elaborate side by side; stage 1 is built
        -- first, as the longest step, and the refusals, which change the process's environment, run alone after them)
        , TestParallel "stages"
            [ TestCase "stage 1 answers the requests of the elaborator and the compiler libraries as the seed does" (stageAgrees 1)
            , TestCase "stage 2 answers the requests of the elaborator and the compiler libraries as the seed does" (stageAgrees 2)
            , TestCase "stage 2 is stage 1: stage 1 elaborates the elaborator as the seed does" stagesFixpoint
            , TestCase "the host's programs elaborated by stage 1 are the ones the seed gives" toolsAgree
            ]
        , TestCase "the seed and the stages are kept in the cache" kept
        , TestCase "a missing or corrupt seed is refused, and an elaborator that fails refuses the module" refusals
        ]

-- (with a cache of its own, so that the seed in the shared cache is not what answers)
refusals :: IO TestResult
refusals = withScratch $ \home -> do
    (corrupt, handle) <- openTempFileCloexec home "frontend.ll"
    hPutStr handle "; not the seed\n"
    hClose handle
    corrupted <- withEnv [("XDG_CACHE_HOME", Just home), ("TERSUS_FRONTEND_SEED_FILE", Just corrupt)] cachedFrontendSeed
    missing <- withEnv [("XDG_CACHE_HOME", Just home), ("TERSUS_FRONTEND_SEED_FILE", Just (home </> "absent.ll"))] cachedFrontendSeed
    requests <- unitRequests bootstrapFrontend (SourceText "refusal" "return 1;")
    pure $ firstFailure
        [ refused "a corrupt seed" "does not match bootstrap/frontend.sha256" corrupted
        , refused "a missing seed" "frontend bootstrap seed" missing
        , case requests of
            Ok answered -> case [rq | (AskedModule rq, _) <- answered] of
                rq : _ -> case nativeElaborator (home </> "absent-elaborator") rq of
                    Refused e | frontendToolFailure e -> Nothing
                    _ -> Just "an elaborator that cannot run did not refuse the module as a tool failure"
                [] -> Just "no module request to send"
            Error e -> Just e
        , case nativeLoader (home </> "absent-elaborator") (sourceRequest LoadParse False False [] "return 1;") of
            NotLoaded e | frontendToolFailure e -> Nothing
            _ -> Just "an elaborator that cannot run did not refuse the load as a tool failure"
        ]
  where
    refused what expected built = case built of
        Ok exe -> Just (what ++ " was built: " ++ exe)
        Error e
            | expected `isInfixOf` e -> Nothing
            | otherwise -> Just (what ++ " was refused for another reason: " ++ e)

-- The requests of the elaborator's own package and of the compiler libraries, with the seed's answers: asked once, while
-- stage 1 is built
{-# NOINLINE seedRequests #-}
seedRequests :: MVar (Maybe (Result [(Asked, Answers)] String))
seedRequests = unsafePerformIO (newMVar Nothing)

requestsOfTheSeed :: IO (Result [(Asked, Answers)] String)
requestsOfTheSeed = modifyMVar seedRequests $ \known -> case known of
    Just requests -> pure (known, requests)
    Nothing -> do
        own <- unitRequests bootstrapFrontend (EmbeddedPackage "lib/elaborate/elaborate.tersus")
        libraries <- unitRequests bootstrapFrontend Libraries
        let requests = own `bindResult` \a -> mapResult (a ++) libraries
        _ <- evaluate (either length length (case requests of Ok r -> Right r; Error e -> Left e))
        pure (Just requests, requests)

-- (stage 2 is stage 1's executable when the fixpoint holds, and then there is nothing more to ask it)
stageAgrees :: Int -> IO TestResult
stageAgrees n = do
    asked <- newEmptyMVar
    _ <- forkIO (try requestsOfTheSeed >>= putMVar asked)
    stage <- frontendStage n
    one <- frontendStage 1
    requests <- takeMVar asked >>= either (\e -> throwIO (e :: SomeException)) pure
    case (stage, one, requests) of
        (Error e, _, _) -> pure (Just ("stage " ++ show n ++ ": " ++ e))
        (_, Error e, _) -> pure (Just ("stage 1: " ++ e))
        (_, _, Error e) -> pure (Just ("the requests: " ++ e))
        (Ok (exe, _), Ok (stageOne, _), Ok answered)
            | null answered -> pure (Just "no requests")
            | n > 1 && exe == stageOne -> pure Nothing
            | otherwise -> firstFailure <$> sequence [agree exe rq reference | (rq, reference) <- answered]
  where
    agree exe rq reference = do
        answer <- executableCandidate exe rq
        pure $ case answer of
            Ok response -> case compareAnswers reference response of
                Agree -> Nothing
                outcome -> Just (exe ++ " answered a request differently: " ++ show outcome)
            Error e -> Just (exe ++ " did not answer a request: " ++ e)

stagesFixpoint :: IO TestResult
stagesFixpoint = do
    one <- frontendStage 1
    two <- frontendStage 2
    pure $ case (one, two) of
        (Ok (_, a), Ok (_, b)) | a == b -> Nothing
        (Ok _, Ok _) -> Just "stage 1 elaborates the elaborator differently from the seed"
        (Error e, _) -> Just ("stage 1: " ++ e)
        (_, Error e) -> Just ("stage 2: " ++ e)

toolsAgree :: IO TestResult
toolsAgree = do
    one <- frontendStage 1
    case one of
        Error e -> pure (Just ("stage 1: " ++ e))
        -- (the compiler libraries stage 1 elaborates, once for every tool)
        Ok (exe, _) -> do
            let libraries = compileLibPackageWith (nativeLoader exe)
            firstFailure <$> boundedConcurrently 2 [evaluate (same exe libraries entry) | entry <- entries]
  where
    entries = [emitterEntry, "lib/mir/mir_verify/mir_verify.tersus", "lib/mir/mir_erase/mir_erase.tersus", "lib/parser/parser.tersus", "lib/ast_reader/ast_reader.tersus", validationEntry]
    same exe libraries entry = case (toolProgramWith (nativeLoader exe) libraries entry, toolProgram entry) of
        (Ok a, Ok b) | a == b -> Nothing
        (Ok _, Ok _) -> Just (entry ++ ": elaborated by stage 1, it is another program")
        (Error e, _) -> Just (entry ++ " elaborated by stage 1: " ++ e)
        (_, Error e) -> Just (entry ++ ": " ++ e)

kept :: IO TestResult
kept = do
    seed <- cachedProgramIfPresent "frontend-seed" frontendSeedHash
    one <- frontendStage 1
    stage <- case one of
        Ok (_, key) -> cachedProgramIfPresentWithArtifacts [".ll"] "frontend" key
        Error e -> pure (Error e)
    pure $ case (seed, stage) of
        (Ok (Just _), Ok (Just _)) -> Nothing
        (Ok Nothing, _) -> Just "the seed is not in the cache"
        (_, Ok Nothing) -> Just "stage 1 or its IR is not in the cache"
        (Error e, _) -> Just e
        (_, Error e) -> Just e

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [e | Just e <- results] of
    e : _ -> Just e
    [] -> Nothing

withScratch :: (FilePath -> IO a) -> IO a
withScratch = bracket make removeDirectoryRecursive
  where
    make = do
        tmp <- getTemporaryDirectory
        (home, handle) <- openTempFileCloexec tmp "tersus-frontend-bootstrap-test"
        hClose handle
        removeFile home
        createDirectory home
        pure home

-- (the cases of the group run one at a time, so the environment of the group's process is theirs while they run)
withEnv :: [(String, Maybe String)] -> IO a -> IO a
withEnv settings action = bracket set restore (const action)
  where
    set = mapM (\(name, value) -> do
        old <- lookupEnv name
        maybe (unsetEnv name) (setEnv name) value
        pure (name, old)) settings
    restore = mapM_ (\(name, old) -> maybe (unsetEnv name) (setEnv name) old)
