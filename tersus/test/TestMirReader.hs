module TestMirReader (testMirReader, withProgram, programExecutable, sameText) where

import Control.Concurrent.MVar (MVar, newMVar)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import System.IO.Unsafe (unsafePerformIO)
import qualified TersusParser
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))

import Bootstrap (compilerSnapshotHash, llvmOfOwned, tersusLlvm)
import Cli (Command (..), World (..), noWorld, runProgramIn, runSourceIn)
import MirHousekeeping (toolOwnedProgram)
import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import Native (buildExecutable, cachedProgram)
import qualified Modules
import TestHarness
import TestNative (clangAvailable, nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The MIR as data, read and written by a program in Tersus (lib/mir/mir_reader/mir_reader.tersus, step 31 of the roadmap): what `tersus mir --data` prints for a program
-- is read into the types of the MIR and written again, and the output is the input. The reader is built once (it needs clang, and the tests pass without it),
-- and run on the data of every example and every program that native code is tested with; it also reads the data of itself. A smaller input is run by the
-- interpreter, which needs no clang.
testMirReader :: Test
testMirReader =
    TestList
        "testMirReader"
        [ TestList
            "interpreted"
            [ TestCase "the program of a loop" (readFile "examples/loops.tersus" >>= interpreted)
            , TestCase "names that are not ASCII" (interpreted "naïve = 3; café = naïve + 1; return café;")
            ]
        , TestParallel
            "every example and program, natively"
            ( [TestCase path (readFile path >>= nativeCheck path) | path <- nativeExamples]
                ++ [TestCase name (nativeCheck name source) | (name, source) <- validatedPrograms]
            )
        , TestCase "what is not the MIR is refused" refusals
        ]

-- The data of a program, or the reason it has none (the harness's shared cache: these programs are compiled once
-- between the groups that check them)
dataOf :: String -> IO (Result String String)
dataOf = mirDataOf

-- The text of a file is the same, but for the new lines at its end
sameText :: String -> String -> Bool
sameText a b = trim a == trim b
  where
    trim = reverse . dropWhile (== '\n') . reverse

interpreted :: String -> IO TestResult
interpreted source = do
    -- (the reader as the host builds it, not validated: testHostValidation validates it)
    reader <- bootstrapFromFile "lib/mir/mir_reader/mir_reader.tersus"
    dataText <- dataOf source
    pure $ case (reader, dataText) of
        (Error e, _) -> Just e
        (_, Error e) -> Just e
        (Ok prog, Ok text) -> case runProgramIn noWorld{worldInput = text} prog of
            Error e -> Just e
            Ok ((output, errors), _)
                | not (null errors) -> Just ("reported: " ++ errors)
                | sameText output text -> Nothing
                | otherwise -> Just ("wrote\n" ++ output ++ "\nfor\n" ++ text)

-- One of the compiler's own programs (the reader, the emitter, the MIR checker and eraser) as an executable, built as the host builds
-- them: lowered and owned without being validated (MirHousekeeping.ownedProgramOf), since whether each validates is testExamples' to
-- say. Built once for the tests that need it (clang is needed, and the tests pass without it).
-- The executable is kept in the cache directory of the user under a name made of the program and of what it is compiled with, so that the groups that need the same one
-- (each in a process of its own) build it once between them; a build that failed is not remembered, so the case that asked for it
-- reports why, and a build that is cut short leaves nothing at the name.
withProgram :: FilePath -> String -> (FilePath -> IO TestResult) -> IO TestResult
withProgram path name use = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else do
            built <- programExecutable path name
            case built of
                Error e -> pure (Just e)
                Ok exe -> use exe

programExecutable :: FilePath -> String -> IO (Result FilePath String)
programExecutable path name = do
    files <- Modules.snapshotFromFilesystem (Modules.normalizePath path)
    backend <- lookupEnv "TERSUS_PARSER"
    parser <- TersusParser.parserKey
    let build output = do
            ir <- if embeddedToolFile path
                then ownedFromFiles path files >>= \owned -> case owned of
                    Error e -> pure (Error e)
                    Ok prog -> llvmOfOwned prog
                else case lookup (Modules.normalizePath path) files of
                    Nothing -> pure (Error ("file not found: " ++ path))
                    Just source -> tersusLlvm source
            case ir of
                Error e -> pure (Error e)
                Ok text -> buildExecutable output text
    case parser of
        Error e -> pure (Error e)
        Ok identity -> do
            key <- evaluate (force (fingerprint [packageCacheInput path files, show backend, compilerSnapshotHash, identity, runtimeSource]))
            cachedProgram ("test-" ++ name) key ("the test " ++ name) build

{-# NOINLINE readerExecutable #-}
readerExecutable :: MVar (Maybe FilePath)
readerExecutable = unsafePerformIO (newMVar Nothing)

withReader :: (FilePath -> IO TestResult) -> IO TestResult
withReader use = do
    available <- clangAvailable
    if not available then pure Nothing else do
        built <- memoizedTestExecutable readerExecutable
            (programExecutable "lib/mir/mir_reader/mir_reader.tersus" "mir-reader")
        case built of
            Error e -> pure (Just e)
            Ok exe -> use exe

-- One case per program, so the sweep runs at the harness's parallelism instead of one program after another
-- inside a single case (withReader builds the reader executable once for the process).
nativeCheck :: String -> String -> IO TestResult
nativeCheck name source = withReader $ \exe -> do
    failures <- check exe (name, source)
    pure $ case failures of
        [] -> Nothing
        bad -> Just (unlines bad)
  where
    check exe (name, source) = do
        dataText <- if embeddedToolFile name then mirDataFromFile name else dataOf source
        case dataText of
            Error e -> pure [name ++ ": " ++ e]
            Ok text -> do
                (code, output, errors) <- runExecutableBytes exe [] text
                pure [name ++ ": " ++ describe code output errors text | code /= ExitSuccess || not (null errors) || not (sameText output text)]
    describe code output errors text =
        "exit " ++ show code ++ ", wrote " ++ show (length output) ++ " bytes for " ++ show (length text) ++ ", " ++ take 200 errors

-- Every way that a text is not the data of a program ends with a message and the value 1
refusals :: IO TestResult
refusals = withReader $ \exe -> do
    let header = "tersus-mir 1\n"
        entry = "main \"m\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0\n"
        cases =
            [ ("nothing", "")
            , ("not the MIR", "return 1;\n")
            , ("a version that is not 1", "tersus-mir 2\n" ++ entry ++ "end\n")
            , ("no main", header ++ "struct \"P\" 0\n")
            , ("a record that is not known", header ++ "bogus 1\n")
            , ("a function that is not ended", header ++ entry ++ "block 0\nreturn\n")
            , ("a block without a terminator", header ++ entry ++ "block 0\nassign 0 use const int 1\nend\n")
            , ("a name that is not closed", header ++ "struct \"P 0\n")
            , ("an escape that is not one", header ++ "struct \"P\\q\" 0\n")
            , ("a type that is not one", header ++ "struct \"P\" 1 \"x\" text\n")
            , ("a number that is too big", header ++ "struct \"P\" 1 \"x\" var 9223372036854775808\n")
            , ("more on a line than there should be", header ++ "struct \"P\" 0 0\n")
            , ("a count that is more than the line", header ++ "struct \"P\" 5 \"x\" int\n")
            , ("two mains", header ++ entry ++ "end\n" ++ entry ++ "end\n")
            ]
    failures <- mapM (refused exe) cases
    pure $ case concat failures of
        [] -> Nothing
        bad -> Just (unlines bad)
  where
    refused exe (name, text) = do
        (_, output, errors) <- runExecutableBytes exe [] text
        pure [name ++ ": read as " ++ show output ++ " with " ++ show errors | output /= "1\n" || null errors]

