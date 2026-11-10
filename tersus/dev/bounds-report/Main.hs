-- Phase 0 spike of the variadic functions plan: elaborates and lowers each program or package entry it is given with the
-- elaborator as it is now (stage 1 when the sources are not the seed's), the compiler libraries included, without
-- validation, and prints the time each took. With TERSUS_BOUNDS_ONLY_REPORT set, each elaboration also writes its
-- bounds-only report there.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import GHC.Clock (getMonotonicTime)
import System.Environment (getArgs, lookupEnv)
import System.IO (hFlush, stdout)

import Compile (lowerSourcePartsWith)
import ElaborateRequest (Elaborator)
import ElaboratorTool (bootstrapElaborator, sourceElaborator)
import MirData (writeProgram)
import qualified Modules as Mod
import Pipeline (compileModulesBootstrapWith, loadFromFilesystem)
import TersusParser (parseSourcePartsNoPrelude)
import Utils

main :: IO ()
main = do
    paths <- getArgs
    -- (BOUNDS_REPORT_SEED=1 elaborates with the seed instead: a quick check that the seed accepts the elaborator's sources)
    seed <- lookupEnv "BOUNDS_REPORT_SEED"
    let elaborator = maybe sourceElaborator (const bootstrapElaborator) seed :: Elaborator
    forM_ paths $ \path -> do
        start <- getMonotonicTime
        loaded <- loadFromFilesystem path
        outcome <- case loaded of
            Left e -> pure ("load failed: " ++ oneLine e)
            Right (Mod.PackageResult pkg) -> describe (compileModulesBootstrapWith elaborator pkg)
            Right (Mod.StandaloneResult _ _) -> do
                source <- readFile path
                describe (parseSourcePartsNoPrelude False True source `bindResult` lowerSourcePartsWith elaborator True)
        end <- getMonotonicTime
        putStrLn (path ++ " | " ++ outcome ++ " | " ++ show (end - start))
        hFlush stdout
  where
    describe result = case result of
        Ok program -> (\n -> "ok " ++ show n) <$> evaluate (length (writeProgram program))
        Error e -> pure ("failed: " ++ take 300 (oneLine e))
    oneLine = map (\c -> if c == '\n' then ' ' else c)
