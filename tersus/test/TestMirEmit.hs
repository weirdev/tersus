module TestMirEmit (testMirEmit, testMirEmitPrograms) where

import Data.List (isInfixOf, isPrefixOf)
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
        , TestParallel
            "every example, natively"
            [TestCase path (readFile path >>= nativeCheck path) | path <- nativeExamples]
        , TestCase "what is not the MIR is refused" refusal
        ]

-- The validated programs of the sweep as a group of their own, so the suite's group processes balance: this sweep
-- and testMirVerify's were the longest groups, and a group is a process.
testMirEmitPrograms :: Test
testMirEmitPrograms =
    TestParallel
        "testMirEmitPrograms"
        [TestCase name (nativeCheck name source) | (name, source) <- validatedPrograms]

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



-- Every mode writes the IR of a program, and the data of the program read back from the data makes the same IR
-- as the data. One case per program, so the sweep runs at the harness's parallelism instead of one program
-- after another inside a single case (withProgram builds the emitter executable once for the process). The data
-- comes from the harness's shared cache (mirDataOf): the groups between them compile these programs once.
nativeCheck :: String -> String -> IO TestResult
nativeCheck name source = withProgram "examples/emit.tersus" "emit" $ \exe -> do
    bad <- check exe (name, source)
    pure $ case bad of
        [] -> Nothing
        problems -> Just (unlines problems)
  where
    check exe (name, source) = do
        dataOf <- mirDataOf source
        case dataOf of
            Error e -> pure [name ++ ": " ++ e]
            Ok dataText -> do
                outline <- runExecutableBytes exe ["outline"] dataText
                bodies <- runExecutableBytes exe ["bodies"] dataText
                everything <- runExecutableBytes exe [] dataText
                roundTrip <- case readProgram dataText of
                    Error e -> pure ["the data does not read back: " ++ e]
                    Ok back -> do
                        again <- runExecutableBytes exe [] (writeProgram back)
                        pure $ case (everything, again) of
                            ((ExitSuccess, output, ""), (ExitSuccess, output', "")) | output == output' -> []
                            ((ExitSuccess, _, ""), (code, _, errors)) -> ["the IR of the program read back: exit " ++ show code ++ ", " ++ take 200 errors]
                            _ -> []
                let modeProblems =
                        [ name ++ ": the " ++ mode ++ ": exit " ++ show code ++ ", " ++ take 200 errors
                        | (mode, (code, _, errors)) <- [("outline", outline), ("bodies", bodies), ("IR", everything)]
                        , code /= ExitSuccess || not (null errors)
                        ]
                        ++ [name ++ ": the IR has no entry point" | (code, output, _) <- [everything], code == ExitSuccess, not ("@tersus_main" `isInfixOf` output)]
                pure (modeProblems ++ roundTrip)

refusal :: IO TestResult
refusal = withProgram "examples/emit.tersus" "emit" $ \exe -> do
    (_, output, errors) <- runExecutableBytes exe ["outline"] "return 1;\n"
    (_, output', errors') <- runExecutableBytes exe ["nonsense"] "tersus-mir 1\n"
    pure $
        if output == "1\n" && not (null errors) && output' == "1\n" && not (null errors')
            then Nothing
            else Just ("read as " ++ show output ++ " with " ++ show errors ++ ", and " ++ show output' ++ " with " ++ show errors')
