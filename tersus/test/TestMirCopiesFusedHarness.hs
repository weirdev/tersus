module TestMirCopiesFusedHarness
    ( fusedLink, fusedRequest, fusedLinkRequest, oldLinkRequest, linkRequest, compareFused, compareBeforeWire
    , standaloneCopies, measureLink
    ) where

import Control.Exception (evaluate)
import Control.Monad (replicateM)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (sort, stripPrefix)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Clock (getMonotonicTimeNSec)
import Text.Printf (printf)

import DataCodec (quote)
import qualified Mir as M
import MirCopiesOracle (makeCopiesWith)
import MirCopiesNameProfile (nameProfilePrefix)
import MirPass (programData, runPassWith)
import PackageData (ModuleId (..))
import Seed (cachedSeed)
import TestHarness
import TestMirCopiesParity (compareProgram, nativeCopiesProbe)
import Utils

label :: String
label = "the linker written in Tersus"

oldLinkRequest :: String -> IO (Result M.Program String)
oldLinkRequest = runPassWith cachedSeed label

fusedRequest :: String -> IO (Result M.Program String)
fusedRequest input = runPassWith nativeCopiesProbe label ("link\n" ++ input)

linkRequest :: [(ModuleId, M.Program)] -> Result String String
linkRequest [] = Error "link error: no modules to link"
linkRequest units = flatResultMap part units `bindResult` \parts ->
    Ok ("pass link\nmerge " ++ show (length units) ++ "\n" ++ concat parts)
  where
    part (ModuleId pkg modu, p) = programData p `bindResult` \payload ->
        Ok (unwords ["unit", quote pkg, maybe "none" (("some " ++) . quote) modu, show (length (lines payload))] ++ "\n" ++ payload)

fusedLinkRequest :: [(ModuleId, M.Program)] -> Result String String
fusedLinkRequest units = linkRequest units `bindResult` \input ->
    Ok (linkOperation "merge-copies" input ++ nameProfilePrefix [input])

linkOperation :: String -> String -> String
linkOperation op input = case stripPrefix "pass link\nmerge " input of
    Just rest -> "pass link\n" ++ op ++ " " ++ rest
    Nothing -> input

fusedLink :: [(ModuleId, M.Program)] -> IO (Result M.Program String)
fusedLink units = case fusedLinkRequest units of
    Error e -> pure (Error e)
    Ok input -> fusedRequest input

oldCopies :: [(ModuleId, M.Program)] -> M.Program -> Result M.Program String
oldCopies units merged = case makeCopiesWith library (M.completeInstances merged) of
    Error e -> Error ("Validation failed: " ++ e)
    ok -> ok
  where
    library = Set.fromList [n | (ModuleId "tersuslib" _, p) <- units, n <- Map.keys (M.progBounded p)]

compareFused :: [(ModuleId, M.Program)] -> IO TestResult
compareFused units = case linkRequest units of
    Error e -> pure (Just e)
    Ok input -> do
        old <- oldLinkRequest input
        new <- fusedLink units
        pure (sameResult (old `bindResult` oldCopies units) new)

sameResult :: Result M.Program String -> Result M.Program String -> TestResult
sameResult (Ok p) (Ok q) = case programData q of
    Ok out -> compareProgram p out
    Error e -> Just e
sameResult (Error a) (Error b) = testAssertEq b a
sameResult (Error e) (Ok _) = Just ("fused accepted, old refused: " ++ e)
sameResult (Ok _) (Error e) = Just ("old accepted, fused refused: " ++ e)

compareBeforeWire :: [(ModuleId, M.Program)] -> IO TestResult
compareBeforeWire units = case linkRequest units of
    Error e -> pure (Just e)
    Ok input -> do
        old <- oldLinkRequest input
        case old of
            Error e -> pure (Just e)
            Ok p -> case programData p of
                Error e -> pure (Just e)
                Ok expected -> do
                    actual <- fusedRequest (linkOperation "inspect-merge" input ++ "expect-merge " ++ show (length (lines expected)) ++ "\n" ++ expected)
                    pure (sameResult old actual)

standaloneCopies :: Set.Set String -> M.Program -> IO (Result M.Program String)
standaloneCopies library p = case programData p of
    Error e -> pure (Error e)
    Ok payload ->
        let header = unwords ("copies" : show (length (lines payload)) : map quote (Set.toList library))
            input = "pass link\n" ++ header ++ "\n" ++ payload
         in fusedRequest (input ++ nameProfilePrefix [input])

measureLink :: [(ModuleId, M.Program)] -> IO TestResult
measureLink units = case linkRequest units of
    Error e -> pure (Just e)
    Ok input -> do
        let fused = linkOperation "merge-copies" input ++ nameProfilePrefix [input]
        _ <- evaluate (length fused)
        old <- oldRun input
        new <- fusedRequest fused
        case sameResult old new of
            Just e -> pure (Just e)
            Nothing -> do
                oldCount <- newIORef (0 :: Int)
                newCount <- newIORef (0 :: Int)
                let counted count action = modifyIORef' count (+ 1) >> action
                timings <- replicateM 9 $ do
                    a <- timed (counted oldCount (oldRun input))
                    b <- timed (counted newCount (fusedRequest fused))
                    pure (a, b)
                nOld <- readIORef oldCount
                nNew <- readIORef newCount
                let median = (!! 4) . sort
                printf "[FUSED] link units=%d input_bytes=%d profile_bytes=%d native_requests_old=%d native_requests_fused=%d samples=9 old_median_ms=%.3f fused_median_ms=%.3f\n"
                    (length units) (length input) (length fused - length input) nOld nNew (median (map fst timings)) (median (map snd timings))
                pure Nothing
  where
    oldRun input = do
        result <- oldLinkRequest input
        pure (result `bindResult` oldCopies units)
    timed action = do
        s <- getMonotonicTimeNSec
        r <- action
        _ <- evaluate (case r of Error e -> length e; Ok p -> length (show p))
        e <- getMonotonicTimeNSec
        pure (fromIntegral (e - s) / 1e6 :: Double)
