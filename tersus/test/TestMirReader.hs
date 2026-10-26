module TestMirReader (testMirReader) where

import System.Directory (createDirectoryIfMissing, getTemporaryDirectory)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))

import Cli (Command (..), World (..), noWorld, runSourceIn)
import MirData (writeProgram)
import Native (buildExecutable)
import Pipeline (llvmSource, ownedSource)
import TestHarness
import TestNative (clangAvailable, nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The MIR as data, read and written by a program in Tersus (examples/mir_reader.tersus, step 31 of the roadmap): what `tersus mir --data` prints for a program
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
        , TestCase "every example and program, natively" everyProgram
        , TestCase "what is not the MIR is refused" refusals
        ]

readerSource :: IO String
readerSource = readFile "examples/mir_reader.tersus"

-- The data of a program, or the reason it has none
dataOf :: String -> Result String String
dataOf source = mapResult writeProgram (ownedSource source)

-- The text of a file is the same, but for the new lines at its end
sameText :: String -> String -> Bool
sameText a b = trim a == trim b
  where
    trim = reverse . dropWhile (== '\n') . reverse

interpreted :: String -> IO TestResult
interpreted source = do
    reader <- readerSource
    pure $ case dataOf source of
        Error e -> Just e
        Ok text -> case runSourceIn noWorld{worldInput = text} Interpret reader of
            Error e -> Just e
            Ok (output, errors)
                | not (null errors) -> Just ("reported: " ++ errors)
                | sameText output text -> Nothing
                | otherwise -> Just ("wrote\n" ++ output ++ "\nfor\n" ++ text)

-- The reader as an executable, built once for the tests that need it
withReader :: (FilePath -> IO TestResult) -> IO TestResult
withReader use = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else do
            reader <- readerSource
            tmp <- getTemporaryDirectory
            let dir = tmp </> "tersus-mir-reader-test"
                exe = dir </> "reader"
            createDirectoryIfMissing True dir
            case llvmSource reader of
                Error e -> pure (Just e)
                Ok ir -> do
                    built <- buildExecutable exe ir
                    case built of
                        Error e -> pure (Just e)
                        Ok () -> use exe

everyProgram :: IO TestResult
everyProgram = withReader $ \exe -> do
    files <- mapM (\path -> (,) path <$> readFile path) nativeExamples
    failures <- mapM (check exe) (files ++ validatedPrograms)
    pure $ case concat failures of
        [] -> Nothing
        bad -> Just (unlines (take 5 bad))
  where
    check exe (name, source) = case dataOf source of
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
