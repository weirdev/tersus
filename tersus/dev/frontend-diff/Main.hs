-- The differential harness on an elaborator executable (REPLACING_HASKELL.md):
--
--   frontend-diff compare EXE [FILE... | --package ENTRY...]
--                                          each request the compiler makes for the corpus (or for the given programs
--                                          and package entries), answered by EXE and by the Haskell elaborator
--   frontend-diff compare --haskell ...    the Haskell elaborator behind the text protocol, as the candidate
--   frontend-diff compare EXE --sources DIR
--                                          also the programs the tests wrote to DIR (run the suite with
--                                          TERSUS_DIFFERENTIAL_SOURCES=DIR: each program a test helper checks)
--   frontend-diff pipeline EXE [FILE... | --package ENTRY...]
--                                          the time the compiler takes to elaborate and lower each unit with EXE as
--                                          its elaborator and with the Haskell one (best of three each)
--   frontend-diff builtins OUT             write the builtin table (lib/data/builtins.ast) from BuiltinRegistry
--   frontend-diff build OUT                build the elaborator of lib/elaborate (and lib/data) as it is on disk, unvalidated
--
-- compare prints each request the candidate does not agree on and the counts, and exits 1 on a disagreement or a
-- candidate failure (a wording difference or a program it does not handle yet is reported, not a failure).
module Main (main) where

import Control.Exception (evaluate)
import GHC.Clock (getMonotonicTime)
import Text.Printf (printf)
import ElaborateRequest (respond)
import Control.Monad (forM_, when)
import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)
import System.FilePath ((</>))
import System.Environment (getArgs)
import System.Exit (exitFailure)

import BuiltinTable (builtinTableText)
import Differential
import Utils

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["build", out] -> do
            files <- packageFromDisk ["lib/elaborate", "lib/data", "lib/data/codec", "lib/data/ast", "lib/data/reader", "lib/data/arena"]
            buildElaborator files out >>= \r -> case r of
                Error e -> failWith e
                Ok () -> putStrLn ("built " ++ out)
        ["builtins", out] -> case builtinTableText of
            Error e -> failWith e
            Ok text -> writeFile out text
        "compare" : candidateArg : rest -> do
            let candidate = if candidateArg == "--haskell" then throughText else executableCandidate candidateArg
            (files, recorded) <- case rest of
                "--sources" : dir : more -> do
                    names <- sort . filter (".tersus" `isSuffixOf`) <$> listDirectory dir
                    texts <- mapM (\name -> SourceText name <$> readFile (dir </> name)) names
                    pure (more, texts)
                _ -> pure (rest, [])
            units <- (++ recorded) <$> if null files then corpusUnits else pure (unitsOf files)
            results <- runDifferential candidate units
            forM_ results $ \(unit, modu, outcome) -> when (outcome /= Agree) $
                putStrLn (describe unit ++ " " ++ modu ++ ": " ++ show outcome)
            let (agree, wording, disagree, unmodelled, failed) = tally [o | (_, _, o) <- results]
            putStrLn (show (length units) ++ " units, " ++ show (length results) ++ " requests: " ++ show agree ++ " agree, " ++ show wording ++ " wording, " ++ show disagree ++ " disagree, " ++ show unmodelled ++ " not modelled, " ++ show failed ++ " failed")
            when (disagree + failed > 0) exitFailure
        "pipeline" : exe : rest -> do
            units <- if null rest then corpusUnits else pure (unitsOf rest)
            totals <- mapM (pipelineUnit exe) units
            let (h, c) = foldr (\(a, b) (x, y) -> (a + x, b + y)) (0, 0) totals
            printf "total: haskell %.3fs, candidate %.3fs, ratio %.2f\n" h c (c / max 1e-9 h)
        _ -> failWith "usage: frontend-diff compare (EXE | --haskell) [FILE...] | frontend-diff pipeline EXE [FILE...] | frontend-diff builtins OUT | frontend-diff build OUT"
  where
    unitsOf args = case args of
        "--package" : entry : more -> FilePackage entry : unitsOf more
        path : more -> SourceFile path : unitsOf more
        [] -> []
    describe unit = case unit of
        SourceFile path -> path
        SourceText name _ -> name
        EmbeddedPackage entry -> entry
        FilePackage entry -> entry
        Libraries -> "lib"

pipelineUnit :: FilePath -> Unit -> IO (Double, Double)
pipelineUnit exe unit = do
    h <- best (unitThrough True respond unit >>= force)
    c <- best (unitThrough True (executableElaborator exe) unit >>= force)
    printf "%s: haskell %.3fs, candidate %.3fs\n" (show unit) h c
    pure (h, c)
  where
    force r = evaluate (length (show r)) >> pure ()
    best act = minimum <$> mapM (const (timed act)) [1 :: Int .. 3]
    timed act = do
        t0 <- getMonotonicTime
        _ <- act
        t1 <- getMonotonicTime
        pure (t1 - t0)

packageFromDisk :: [FilePath] -> IO [(FilePath, String)]
packageFromDisk dirs = concat <$> mapM files dirs
  where
    files dir = do
        names <- sort . filter (".tersus" `isSuffixOf`) <$> listDirectory dir
        mapM (\name -> do
            text <- readFile (dir </> name)
            _ <- evaluate (length text)
            pure (dir </> name, text)) names

failWith :: String -> IO a
failWith message = putStrLn message >> exitFailure
