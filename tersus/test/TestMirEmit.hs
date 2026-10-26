module TestMirEmit (testMirEmit) where

import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import System.Exit (ExitCode (..))

import Cli (Command (..), World (..), noWorld, runSourceIn)
import LlvmEmit (emitBody, emitOutline, emitOwned)
import Mir
import MirData (forNative, writeProgram)
import Pipeline (ownedSource)
import Pretty (renderType)
import TersusTypes (Type (..))
import TestHarness
import TestMirReader (sameText, withProgram)
import TestNative (nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The lowering to LLVM IR written in Tersus (examples/emit.tersus, step 31 of the roadmap and STEP31.md). It is given the MIR as data, and what it writes is compared with
-- the Haskell it replaces, for every example and every program that native code is tested with:
-- - with no argument: all of the IR, byte for byte, against `LlvmEmit.emitOwned`;
-- - `outline`: the declarations, the descriptors of the types of the locals and the entry point, against `LlvmEmit.emitOutline`;
-- - `bodies`: the code of each function, against `LlvmEmit.emitBody` (a function that the Haskell cannot emit is `unsupported` in the Tersus too).
-- The emitter is built once (it needs clang, and the tests pass without it); a smaller input is run by the interpreter.
testMirEmit :: Test
testMirEmit =
    TestList
        "testMirEmit"
        [ TestCase "the reader is the same in the reader and in the emitter" sameReader
        , TestList
            "interpreted"
            [ TestCase "the IR of a loop" (readFile "examples/loops.tersus" >>= interpretedIr)
            , TestCase "the outline of a struct and an enum" (readFile "examples/enums.tersus" >>= interpretedOutline)
            , TestCase "the code of arithmetic" (readFile "examples/arithmetic.tersus" >>= interpretedBodies)
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

-- The code of the functions in order, then main: for each, the lines the Haskell gives (Nothing when it gives none)
bodySections :: Program -> [(Function, Maybe [String])]
bodySections program = zipWith section [0 :: Int ..] ([(False, f) | f <- Map.elems (progFunctions program)] ++ [(True, progMain program)])
  where
    section i (entry, f) = (f, either (const Nothing) Just (toEither (emitBody program entry f)) >>= \(globals, temps, code, types) -> Just (["; function " ++ show i, "; globals"] ++ globals ++ ["; temps"] ++ temps ++ ["; code"] ++ code ++ ["; types"] ++ map renderType types))
    toEither (Ok a) = Right a
    toEither (Error e) = Left e

-- The lines of what the emitter wrote, in a part for each function
sectionsOf :: String -> [[String]]
sectionsOf = go . lines
  where
    go [] = []
    go (l : ls) = let (body, rest) = break ("; function " `isPrefixOf`) ls in (l : body) : go rest

interpretedIr :: String -> IO TestResult
interpretedIr source = do
    emitter <- readFile "examples/emit.tersus"
    pure $ case ownedSource source of
        Error e -> Just e
        Ok owned -> case (emitOwned (forNative owned), runSourceIn noWorld{worldInput = writeProgram owned} Interpret emitter) of
            (Ok text, Ok (output, errors))
                | not (null errors) -> Just ("reported: " ++ errors)
                | sameText output text -> Nothing
                | otherwise -> Just ("wrote\n" ++ take 2000 output ++ "\nfor\n" ++ take 2000 text)
            (Error e, _) -> Just ("the Haskell gives no IR: " ++ e)
            (_, Error e) -> Just e

interpretedOutline :: String -> IO TestResult
interpretedOutline source = do
    emitter <- readFile "examples/emit.tersus"
    pure $ case ownedSource source of
        Error e -> Just e
        Ok owned -> case (emitOutline (forNative owned), runSourceIn noWorld{worldInput = writeProgram owned, worldArgs = ["outline"]} Interpret emitter) of
            (Ok text, Ok (output, errors))
                | not (null errors) -> Just ("reported: " ++ errors)
                | sameText output text -> Nothing
                | otherwise -> Just ("wrote\n" ++ output ++ "\nfor\n" ++ text)
            (Error e, _) -> Just ("the Haskell gives no IR: " ++ e)
            (_, Error e) -> Just e

interpretedBodies :: String -> IO TestResult
interpretedBodies source = do
    emitter <- readFile "examples/emit.tersus"
    pure $ case ownedSource source of
        Error e -> Just e
        Ok owned -> case runSourceIn noWorld{worldInput = writeProgram owned, worldArgs = ["bodies"]} Interpret emitter of
            Error e -> Just e
            Ok (output, errors)
                | not (null errors) -> Just ("reported: " ++ errors)
                | otherwise -> case compareBodies (forNative owned) output of
                    ([], supported) | supported > 0 -> Nothing
                    ([], _) -> Just "the emitter has no function of the program"
                    (bad, _) -> Just (unlines (take 3 bad))

-- What is wrong with the code the emitter wrote (it has the functions that the Haskell writes, and no other), and how many functions it had
compareBodies :: Program -> String -> ([String], Int)
compareBodies program output = (concat problems, length (filter id supported))
  where
    expected = bodySections program
    written = sectionsOf output
    results = zipWith3 check [0 :: Int ..] expected (map Just written ++ repeat Nothing)
    problems = map fst results
    supported = map snd results
    check i (_, haskell) w = case (haskell, w) of
        (_, Nothing) -> ([show i ++ ": nothing was written"], False)
        (Nothing, Just section)
            | section == ["; function " ++ show i, "; unsupported"] -> ([], False)
            | otherwise -> ([show i ++ ": the Haskell gives no code, and the emitter wrote some"], True)
        (Just lines', Just section)
            | section == ["; function " ++ show i, "; unsupported"] -> ([show i ++ ": unsupported, and the Haskell has code for it"], False)
            | section == lines' -> ([], True)
            | otherwise -> ([show i ++ ": wrote\n" ++ unlines (take 40 section) ++ "\nfor\n" ++ unlines (take 40 lines')], True)

everyProgram :: IO TestResult
everyProgram = withProgram "examples/emit.tersus" "emit" $ \exe -> do
    files <- mapM (\path -> (,) path <$> readFile path) nativeExamples
    failures <- mapM (check exe) (files ++ validatedPrograms)
    let (bad, counts) = unzip failures
    pure $ case concat bad of
        [] | sum counts >= 100 -> Nothing
        [] -> Just ("only " ++ show (sum counts) ++ " functions were compared")
        problems -> Just (unlines (take 5 problems))
  where
    check exe (name, source) = case ownedSource source of
        Error e -> pure ([name ++ ": " ++ e], 0)
        Ok owned -> do
            outline <- runExecutableBytes exe ["outline"] (writeProgram owned)
            bodies <- runExecutableBytes exe ["bodies"] (writeProgram owned)
            everything <- runExecutableBytes exe [] (writeProgram owned)
            let program = forNative owned
                (bodyProblems, count) = case bodies of
                    (ExitSuccess, output, "") -> compareBodies program output
                    (code, output, errors) -> (["exit " ++ show code ++ ", wrote " ++ show (length output) ++ " bytes, " ++ take 200 errors], 0)
                outlineProblems = case (outline, emitOutline program) of
                    ((ExitSuccess, output, ""), Ok text) | output == text -> []
                    ((_, output, errors), Ok text) -> ["the outline: wrote " ++ show (length output) ++ " bytes for " ++ show (length text) ++ ", " ++ take 200 errors]
                    -- (a program that has no entry point: the reason on the standard error, and the value 1)
                    ((_, output, errors), Error e) -> ["the outline: wrote " ++ show output ++ " with " ++ show errors ++ " and not " ++ show e | output /= "1\n" || errors /= e ++ "\n"]
                irProblems = case (everything, emitOwned program) of
                    ((ExitSuccess, output, ""), Ok text) | output == text -> []
                    ((_, output, errors), Ok text) -> ["the IR: wrote " ++ show (length output) ++ " bytes for " ++ show (length text) ++ ", " ++ take 200 errors ++ firstDifference output text]
                    -- (a program that cannot be made into code: the reason on the standard error, and the value 1)
                    ((_, output, errors), Error e) -> ["the IR: wrote " ++ show (take 100 output) ++ " with " ++ show errors ++ " and not " ++ show e | output /= "1\n" || errors /= e ++ "\n"]
            pure ([name ++ ": " ++ p | p <- outlineProblems ++ bodyProblems ++ irProblems], count)

-- Where the first line that differs is
firstDifference :: String -> String -> String
firstDifference output text = case [(n, a, b) | (n, a, b) <- zip3 [1 :: Int ..] (lines output) (lines text), a /= b] of
    (n, a, b) : _ -> "; line " ++ show n ++ ": " ++ show a ++ " for " ++ show b
    [] -> ""

refusal :: IO TestResult
refusal = withProgram "examples/emit.tersus" "emit" $ \exe -> do
    (_, output, errors) <- runExecutableBytes exe ["outline"] "return 1;\n"
    (_, output', errors') <- runExecutableBytes exe ["nonsense"] "tersus-mir 1\n"
    pure $
        if output == "1\n" && not (null errors) && output' == "1\n" && not (null errors')
            then Nothing
            else Just ("read as " ++ show output ++ " with " ++ show errors ++ ", and " ++ show output' ++ " with " ++ show errors')
