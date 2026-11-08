-- The differential harness on an elaborator executable (REPLACING_HASKELL.md):
--
--   frontend-diff compare EXE [FILE... | --package ENTRY...]
--                                          each request the compiler makes for the corpus (or for the given programs
--                                          and package entries), answered by EXE and by the Haskell elaborator
--   frontend-diff compare --haskell ...    the Haskell elaborator behind the text protocol, as the candidate
--   frontend-diff compare EXE --sources DIR
--                                          also the programs the tests wrote to DIR (run the suite with
--                                          TERSUS_DIFFERENTIAL_SOURCES=DIR: each program a test helper checks)
--   frontend-diff builtins OUT             write the builtin table (lib/data/builtins.ast) from BuiltinRegistry
--
-- compare prints each request the candidate does not agree on and the counts, and exits 1 on a disagreement or a
-- candidate failure (a wording difference or a program it does not handle yet is reported, not a failure).
module Main (main) where

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
        _ -> failWith "usage: frontend-diff compare (EXE | --haskell) [FILE...] | frontend-diff builtins OUT"
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

failWith :: String -> IO a
failWith message = putStrLn message >> exitFailure
