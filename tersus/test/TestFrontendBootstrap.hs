-- REPLACING_HASKELL.md, "The frontend seed": F0 is the elaborator written in Tersus built from pinned IR, F1 the
-- elaborator as it is now elaborated by F0, and F2 the same elaborated by F1.
module TestFrontendBootstrap (testFrontendBootstrap) where

import Control.Exception (bracket)
import Data.Char (isHexDigit)
import Data.List (isInfixOf, nub)
import System.Directory (createDirectory, getTemporaryDirectory, removeDirectoryRecursive, removeFile)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.FilePath ((</>))
import System.IO (hClose, hPutStr)

import CacheLock (openTempFileCloexec)
import Differential (Outcome (..), Unit (..), compareResponses, unitRequests)
import ElaborateRequest (Response (..))
import ElaboratorNative (frontendStage)
import ElaboratorTool (bootstrapElaborator, frontendSources, frontendToolFailure, nativeElaborator, runElaborator)
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
        , TestCase "a missing or corrupt seed is refused, and an elaborator that fails refuses the module" refusals
        , TestCase "stages 1 and 2 answer the requests of the elaborator and the compiler libraries as the seed does" stagesAgree
        , TestCase "stage 2 is stage 1: stage 1 elaborates the elaborator as the seed does" stagesFixpoint
        , TestCase "the host's programs elaborated by stage 1 are the ones the seed gives" toolsAgree
        , TestCase "the seed and the stages are kept in the cache" kept
        ]

-- (with a cache of its own, so that the seed in the shared cache is not what answers)
refusals :: IO TestResult
refusals = withScratch $ \home -> do
    (corrupt, handle) <- openTempFileCloexec home "frontend.ll"
    hPutStr handle "; not the seed\n"
    hClose handle
    corrupted <- withEnv [("XDG_CACHE_HOME", Just home), ("TERSUS_FRONTEND_SEED_FILE", Just corrupt)] cachedFrontendSeed
    missing <- withEnv [("XDG_CACHE_HOME", Just home), ("TERSUS_FRONTEND_SEED_FILE", Just (home </> "absent.ll"))] cachedFrontendSeed
    requests <- unitRequests bootstrapElaborator (SourceText "refusal" "return 1;")
    pure $ firstFailure
        [ refused "a corrupt seed" "does not match bootstrap/frontend.sha256" corrupted
        , refused "a missing seed" "frontend bootstrap seed" missing
        , case requests of
            Ok ((rq, _) : _) -> case nativeElaborator (home </> "absent-elaborator") rq of
                Refused e | frontendToolFailure e -> Nothing
                _ -> Just "an elaborator that cannot run did not refuse the module as a tool failure"
            Ok [] -> Just "no request to send"
            Error e -> Just e
        ]
  where
    refused what expected built = case built of
        Ok exe -> Just (what ++ " was built: " ++ exe)
        Error e
            | expected `isInfixOf` e -> Nothing
            | otherwise -> Just (what ++ " was refused for another reason: " ++ e)

-- (stage 2 is stage 1's executable when the fixpoint holds, and is asked only when it is not)
stagesAgree :: IO TestResult
stagesAgree = do
    one <- frontendStage 1
    two <- frontendStage 2
    own <- unitRequests bootstrapElaborator (FilePackage "lib/elaborate/elaborate.tersus")
    libraries <- unitRequests bootstrapElaborator Libraries
    let requests = own `bindResult` \a -> mapResult (a ++) libraries
    case (one, two, requests) of
        (Error e, _, _) -> pure (Just ("stage 1: " ++ e))
        (_, Error e, _) -> pure (Just ("stage 2: " ++ e))
        (_, _, Error e) -> pure (Just ("the requests: " ++ e))
        (Ok (stageOne, _), Ok (stageTwo, _), Ok answered)
            | null answered -> pure (Just "no requests")
            | otherwise -> firstFailure <$> sequence [agree exe rq reference | exe <- nub [stageOne, stageTwo], (rq, reference) <- answered]
  where
    agree exe rq reference = do
        answer <- runElaborator exe rq
        pure $ case answer of
            Ok response -> case compareResponses reference response of
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
        Ok (exe, _) -> pure (firstFailure (map (same exe) entries))
  where
    entries = [emitterEntry, "lib/mir/mir_verify/mir_verify.tersus", "lib/mir/mir_erase/mir_erase.tersus", "lib/parser/parser.tersus", "lib/ast_reader/ast_reader.tersus", validationEntry]
    same exe entry = case (toolProgramWith (nativeElaborator exe) entry, toolProgram entry) of
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
