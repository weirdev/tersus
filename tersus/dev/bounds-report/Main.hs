-- Phase 0 spike of the variadic functions plan: elaborates and lowers each program or package entry it is given with the
-- elaborator as it is now (stage 1 when the sources are not the seed's), the compiler libraries included, without
-- validation, and prints the time each took. With TERSUS_BOUNDS_ONLY_REPORT set, each elaboration also writes its
-- bounds-only report there. BOUNDS_REPORT_ALTERNATE=<directory> times each entry twice in this process, with the report
-- off and on (into that directory), alternating which goes first; BOUNDS_REPORT_SEED=1 elaborates with the seed instead.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import GHC.Clock (getMonotonicTime)
import System.Environment (getArgs, lookupEnv, setEnv, unsetEnv)
import System.IO (hFlush, stdout)

import Compile (lowerSourcePartsWith)
import ElaborateRequest (Elaborator)
import ElaboratorTool (bootstrapElaborator, sourceElaborator)
import Hash (fingerprint)
import MirData (writeProgram)
import qualified Modules as Mod
import Pipeline (compileModulesBootstrapWith, loadFromFilesystem)
import TersusParser (parseSourcePartsNoPrelude)
import Utils

main :: IO ()
main = do
    paths <- getArgs
    seed <- lookupEnv "BOUNDS_REPORT_SEED"
    alternate <- lookupEnv "BOUNDS_REPORT_ALTERNATE"
    let elaborator = maybe sourceElaborator (const bootstrapElaborator) seed :: Elaborator
    case alternate of
        Nothing -> forM_ paths $ \path -> do
            (outcome, seconds) <- timed elaborator path
            putStrLn (path ++ " | " ++ outcome ++ " | " ++ show seconds)
            hFlush stdout
        Just dir -> forM_ (zip [0 :: Int ..] paths) $ \(i, path) -> do
            let off = unsetEnv "TERSUS_BOUNDS_ONLY_REPORT" >> timed elaborator path
                on = setEnv "TERSUS_BOUNDS_ONLY_REPORT" dir >> timed elaborator path
            ((offOutcome, offSeconds), (onOutcome, onSeconds)) <-
                if even i then (,) <$> off <*> on else (\b a -> (a, b)) <$> on <*> off
            putStrLn (path ++ " | off " ++ offOutcome ++ " " ++ show offSeconds ++ " | on " ++ onOutcome ++ " " ++ show onSeconds)
            hFlush stdout

timed :: Elaborator -> FilePath -> IO (String, Double)
timed elaborator path = do
    start <- getMonotonicTime
    loaded <- loadFromFilesystem path
    outcome <- case loaded of
        Right (Mod.PackageResult pkg) -> describe (compileModulesBootstrapWith elaborator pkg)
        -- (a file outside a package is read as `tersus check` reads it)
        _ -> do
            source <- readFile path
            describe (parseSourcePartsNoPrelude False True source `bindResult` lowerSourcePartsWith elaborator True)
    end <- getMonotonicTime
    pure (outcome, end - start)
  where
    describe result = case result of
        Ok program -> (\t -> "ok " ++ show (length t) ++ " " ++ fingerprint [t]) <$> evaluate (writeProgram program)
        Error e -> pure ("failed: " ++ take 300 (oneLine e))

oneLine :: String -> String
oneLine = map (\c -> if c == '\n' then ' ' else c)
