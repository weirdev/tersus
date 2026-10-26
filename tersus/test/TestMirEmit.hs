module TestMirEmit (testMirEmit) where

import Data.List (isPrefixOf)
import System.Exit (ExitCode (..))

import Cli (Command (..), World (..), noWorld, runSourceIn)
import LlvmEmit (emitOutline)
import MirData (forNative, writeProgram)
import Pipeline (ownedSource)
import TestHarness
import TestMirReader (sameText, withProgram)
import TestNative (nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The lowering to LLVM IR written in Tersus (examples/emit.tersus, step 31 of the roadmap and STEP31.md) while it is written a part at a time. It is given the MIR
-- as data, and its output is compared with the Haskell it replaces for every example and every program that native code is tested with. So far that is
-- `LlvmEmit.emitOutline`: the declarations, the descriptors of the types of the locals and the entry point. The emitter is built once (it needs clang, and the
-- tests pass without it); a smaller input is run by the interpreter.
testMirEmit :: Test
testMirEmit =
    TestList
        "testMirEmit"
        [ TestCase "the reader is the same in the reader and in the emitter" sameReader
        , TestList
            "interpreted"
            [ TestCase "a loop" (readFile "examples/loops.tersus" >>= interpreted)
            , TestCase "a struct and an enum" (readFile "examples/enums.tersus" >>= interpreted)
            ]
        , TestCase "every example and program, natively" everyProgram
        , TestCase "what is not the MIR is refused" refusal
        ]

-- The text of the reader between its two marker lines
readerOf :: String -> String
readerOf source = unlines (takeWhile (not . isPrefixOf "// ---- end of the reader ----") (dropWhile (not . isPrefixOf "// ---- the reader:") (lines source)))

sameReader :: IO TestResult
sameReader = do
    reader <- readFile "examples/mir_reader.tersus"
    emitter <- readFile "examples/emit.tersus"
    pure $
        if null (readerOf reader) || readerOf reader /= readerOf emitter
            then Just "the text between '// ---- the reader:' and '// ---- end of the reader ----' differs between examples/mir_reader.tersus and examples/emit.tersus"
            else Nothing

interpreted :: String -> IO TestResult
interpreted source = do
    emitter <- readFile "examples/emit.tersus"
    pure $ case ownedSource source of
        Error e -> Just e
        Ok owned -> case (emitOutline (forNative owned), runSourceIn noWorld{worldInput = writeProgram owned} Interpret emitter) of
            (Ok text, Ok (output, errors))
                | not (null errors) -> Just ("reported: " ++ errors)
                | sameText output text -> Nothing
                | otherwise -> Just ("wrote\n" ++ output ++ "\nfor\n" ++ text)
            (Error e, _) -> Just ("the Haskell gives no IR: " ++ e)
            (_, Error e) -> Just e

everyProgram :: IO TestResult
everyProgram = withProgram "examples/emit.tersus" "emit" $ \exe -> do
    files <- mapM (\path -> (,) path <$> readFile path) nativeExamples
    failures <- mapM (check exe) (files ++ validatedPrograms)
    pure $ case concat failures of
        [] -> Nothing
        bad -> Just (unlines (take 5 bad))
  where
    check exe (name, source) = case ownedSource source of
        Error e -> pure [name ++ ": " ++ e]
        Ok owned -> do
            (code, output, errors) <- runExecutableBytes exe [] (writeProgram owned)
            pure $ case emitOutline (forNative owned) of
                Ok text -> [name ++ ": " ++ describe code output errors text | code /= ExitSuccess || not (null errors) || output /= text]
                -- (a program that has no entry point: the reason on the standard error, and the value 1)
                Error e -> [name ++ ": wrote " ++ show output ++ " with " ++ show errors ++ " and not " ++ show e | output /= "1\n" || errors /= e ++ "\n"]
    describe code output errors text =
        "exit " ++ show code ++ ", wrote " ++ show (length output) ++ " bytes for " ++ show (length text) ++ ", " ++ take 200 errors

refusal :: IO TestResult
refusal = withProgram "examples/emit.tersus" "emit" $ \exe -> do
    (_, output, errors) <- runExecutableBytes exe [] "return 1;\n"
    pure (if output == "1\n" && not (null errors) then Nothing else Just ("read as " ++ show output ++ " with " ++ show errors))
