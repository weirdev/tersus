module TestMirEmit (testMirEmit) where

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import System.Exit (ExitCode (..))

import Cli (World (..), noWorld, runProgramIn)
import Mir
import MirData (readProgram, writeProgram)
import Pipeline (ownedSource)
import TestHarness
import TestMirReader (withProgram)
import TestNative (nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The lowering to LLVM IR written in Tersus (examples/emit.tersus, step 31 of the roadmap and STEP31.md) is the compiler's emitter. It is given the MIR as data,
-- and writes all of the IR with no argument, the declarations, the descriptors of the types and the entry point for `outline`, and the code of each function for
-- `bodies`. What it writes has to build and run as the program does, which TestNative checks for every example and program by building the IR; here every mode
-- is run on every one of them, and the data of a program and the data of the program read back from it have to make the same IR. A smaller input is run by the
-- interpreter.
-- The emitter is built once (it needs clang, and the tests pass without it).
testMirEmit :: Test
testMirEmit =
    TestList
        "testMirEmit"
        [ TestCase "the reader is the same in the reader and in the emitter" sameReader
        , TestCase "the IR of a loop, interpreted" (readFile "examples/loops.tersus" >>= interpretedIr)
        , TestCase "every example and program, natively" everyProgram
        , TestCase "what is not the MIR is refused" refusal
        ]

-- The text of the reader between its two marker lines
readerOf :: String -> String
readerOf source = unlines (takeWhile (not . isPrefixOf "// ---- end of the reader ----") (dropWhile (not . isPrefixOf "// ---- the reader:") (lines source)))

-- The emitter of examples/emit.tersus, compiled once: the three interpreted cases each run it for a part of the IR, and its
-- validation is the most expensive thing in this group.
emitterProgram :: IO (Result Program String)
emitterProgram = readFile "examples/emit.tersus" >>= compileOnce

runEmitter :: World -> Result Program String -> Result ((String, String), [(FilePath, String)]) String
runEmitter world compiled = case compiled of
    Error e -> Error e
    Ok program -> runProgramIn world program

sameReader :: IO TestResult
sameReader = do
    reader <- readFile "examples/mir_reader.tersus"
    emitter <- readFile "examples/emit.tersus"
    pure $
        if null (readerOf reader) || readerOf reader /= readerOf emitter
            then Just "the text between '// ---- the reader:' and '// ---- end of the reader ----' differs between examples/mir_reader.tersus and examples/emit.tersus"
            else Nothing

interpretedIr :: String -> IO TestResult
interpretedIr source = do
    emitter <- emitterProgram
    pure $ case ownedSource source of
        Error e -> Just e
        Ok owned -> case mapResult fst (runEmitter noWorld{worldInput = writeProgram owned} emitter) of
            Error e -> Just e
            Ok (output, errors)
                | not (null errors) -> Just ("reported: " ++ errors)
                | "@tersus_main" `isInfixOf` output && "define" `isInfixOf` output -> Nothing
                | otherwise -> Just ("wrote\n" ++ take 2000 output)



-- Every mode writes the IR of every program, and the data of the program read back from the data makes the same IR as the data
everyProgram :: IO TestResult
everyProgram = withProgram "examples/emit.tersus" "emit" $ \exe -> do
    files <- mapM (\path -> (,) path <$> readFile path) nativeExamples
    failures <- mapM (check exe) (files ++ validatedPrograms)
    let (bad, counts) = unzip failures
    pure $ case concat bad of
        [] | sum counts >= 100 -> Nothing
        [] -> Just ("only " ++ show (sum counts) ++ " functions were written")
        problems -> Just (unlines (take 5 problems))
  where
    check exe (name, source) = case ownedSource source of
        Error e -> pure ([name ++ ": " ++ e], 0)
        Ok owned -> do
            let dataText = writeProgram owned
                count = Map.size (progFunctions owned) + 1
            outline <- runExecutableBytes exe ["outline"] dataText
            bodies <- runExecutableBytes exe ["bodies"] dataText
            everything <- runExecutableBytes exe [] dataText
            roundTrip <- case readProgram dataText of
                Error e -> pure (["the data does not read back: " ++ e], 0)
                Ok back -> do
                    again <- runExecutableBytes exe [] (writeProgram back)
                    pure $ case (everything, again) of
                        ((ExitSuccess, output, ""), (ExitSuccess, output', "")) | output == output' -> ([], count)
                        ((ExitSuccess, _, ""), (code, _, errors)) -> (["the IR of the program read back: exit " ++ show code ++ ", " ++ take 200 errors], 0)
                        _ -> ([], 0)
            let modeProblems =
                    [ name ++ ": the " ++ mode ++ ": exit " ++ show code ++ ", " ++ take 200 errors
                    | (mode, (code, _, errors)) <- [("outline", outline), ("bodies", bodies), ("IR", everything)]
                    , code /= ExitSuccess || not (null errors)
                    ]
                    ++ [name ++ ": the IR has no entry point" | (code, output, _) <- [everything], code == ExitSuccess, not ("@tersus_main" `isInfixOf` output)]
            pure (modeProblems ++ fst roundTrip, snd roundTrip)

refusal :: IO TestResult
refusal = withProgram "examples/emit.tersus" "emit" $ \exe -> do
    (_, output, errors) <- runExecutableBytes exe ["outline"] "return 1;\n"
    (_, output', errors') <- runExecutableBytes exe ["nonsense"] "tersus-mir 1\n"
    pure $
        if output == "1\n" && not (null errors) && output' == "1\n" && not (null errors')
            then Nothing
            else Just ("read as " ++ show output ++ " with " ++ show errors ++ ", and " ++ show output' ++ " with " ++ show errors')
