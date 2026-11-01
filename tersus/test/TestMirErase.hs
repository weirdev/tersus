module TestMirErase (testMirErase) where

import Data.List (isInfixOf, isSuffixOf)
import System.Exit (ExitCode (..))

import Cli (World (..), noWorld, runProgramIn)
import Mir (Program)
import MirData (writeProgram, writeProgramWithGhosts)
import MirGhost (eraseGhosts, withoutUninit)
import Pipeline (validatedSource)
import TestHarness
import TestMirReader (sameText, withProgram)
import TestNative (nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The rest of the MIR housekeeping of REPLACING_HASKELL.md target 3, in Tersus (examples/mir_erase.tersus): the erasure of the
-- ghosts of a program (MirGhost.eraseGhosts and withoutUninit) over the data of the program as it is before the
-- erasure (version 2 of the data, writeProgramWithGhosts), compared word for word with what the Haskell writes of
-- the program it erases. The Haskell can be deprecated once this and the check of examples/mir_verify.tersus hold.
testMirErase :: Test
testMirErase =
    TestList
        "testMirErase"
        [ TestList
            "interpreted"
            [ TestCase "a program with no ghosts is unchanged" (interpreted "return 1 + 2;")
            , TestCase "permissions are taken out" (interpreted pointers)
            , TestCase "a reference is read through" (interpreted borrowSource)
            , TestCase "a reference updates through a mutable borrow" (interpreted mutSource)
            , TestCase "what is not the MIR is refused" refused
            , TestCase "a cast of a permission to a bigger slot is refused" badCast
            , TestCase "a cast to a slot with a ghost field is allowed" (castAccepted twoLine "struct \"Two\" 2 \"a\" int \"b\" block int")
            , TestCase "a cast to a slot with an uninitialized field is allowed" (castAccepted twoLine "struct \"Two\" 1 \"a\" uninit int")
            ]
        , TestCase "every example and program, natively" everyProgram
        ]

pointers :: String
pointers = "(p, b) = Addr::alloc(2); b = Addr::write(p, 0, 5, b); x = Addr::get(p, 0, b); b = Addr::dropValue(p, 0, b); return x + Addr::free(p, b);"

borrowSource :: String
borrowSource = "xs = [1, 2, 3]; r = &xs; return size(*r) + get(*r, 0);"

mutSource :: String
mutSource = "x = 4; r = &mut x; *r = 9; return *r;"

-- The eraser compiled once for every interpreted case: compiling it is the expensive part, and every case
-- runs the same program over a different input (the pattern of TestMirVerify's verifierProgram).
eraserProgram :: IO (Result Program String)
eraserProgram = readFile "examples/mir_erase.tersus" >>= compileOnce

-- What the Haskell makes of the program before its ghosts are erased, as version 1 of the data
expectedOf :: String -> Result String String
expectedOf source = case validatedSource source of
    Error e -> Error e
    Ok program -> mapResult (writeProgram . withoutUninit) (eraseGhosts program)

interpreted :: String -> IO TestResult
interpreted source = do
    eraser <- eraserProgram
    pure $ case eraser of
        Error e -> Just ("the eraser does not compile: " ++ e)
        Ok eraserProgram -> case validatedSource source of
            Error e -> Just e
            Ok program -> case expectedOf source of
                Error e -> Just ("the Haskell refuses: " ++ e)
                Ok expected -> case runProgramIn noWorld{worldInput = writeProgramWithGhosts program} eraserProgram of
                    Error e -> Just e
                    Ok ((output, errors), _)
                        | null errors && sameText output expected -> Nothing
                        | otherwise -> Just ("wrote\n" ++ output ++ "\nwith errors " ++ show errors ++ "\nfor (expected)\n" ++ expected)

refused :: IO TestResult
refused = do
    eraser <- eraserProgram
    pure $ case eraser of
        Error e -> Just ("the eraser does not compile: " ++ e)
        Ok eraserProgram -> case runProgramIn noWorld eraserProgram of
            Error e -> Just e
            Ok ((output, errors), _)
                | output == "1" && not (null errors) -> Nothing
                | otherwise -> Just ("got output " ++ show output ++ " and errors " ++ show errors)

-- The program the eraser is given, with the cast of its permission made a cast to slots of another size: the
-- local the cast gives (a permission of Two, 8 bytes) is written as a permission of two Ints (16 bytes)
badCast :: IO TestResult
badCast = do
    eraser <- eraserProgram
    pure $ case eraser of
        Error e -> Just ("the eraser does not compile: " ++ e)
        Ok eraserProgram -> case validatedSource castSource of
            Error e -> Just e
            Ok program ->
                let text = map castLine (lines (writeProgramWithGhosts program))
                 in case runProgramIn noWorld{worldInput = unlines text} eraserProgram of
                        Error e -> Just e
                        Ok ((output, errors), _)
                            | output == "1" && not (null errors) -> Nothing
                            | otherwise -> Just ("got output " ++ show output ++ " and errors " ++ show errors ++ " for\n" ++ unlines text)
  where
    castLine line
        | " block named \"Two\"" `isSuffixOf` line = take (length line - length "named \"Two\"") line ++ "array int const 2"
        | otherwise = line

castSource :: String
castSource = "struct Two { a: I32, b: I32 }; impl Clone for Two { }; impl Copy for Two { }; (p, b) = Addr::alloc(2); c = Block::cast(b); q = Addr::cast(p); c = Addr::write(q, 0, Two { a: -1, b: 2 }, c); x = Addr::get(q, 0, c); c = Addr::dropValue(q, 0, c); return toInt(x.a) + toInt(x.b) + Addr::free(q, c);"

twoLine :: String
twoLine = "struct \"Two\" 2 \"a\" i32 \"b\" i32"

-- The cast the eraser is given, with the struct the cast is to written as another shape of the same layout
-- (Haskell `Mir.layoutOf`: a Block<T> field takes no room, and an Uninit<T> field the room of a T): the eraser writes the program
castAccepted :: String -> String -> IO TestResult
castAccepted from to = do
    eraser <- eraserProgram
    pure $ case eraser of
        Error e -> Just ("the eraser does not compile: " ++ e)
        Ok eraserProgram -> case validatedSource castSource of
            Error e -> Just e
            Ok program ->
                let text = map (\line -> if line == from then to else line) (lines (writeProgramWithGhosts program))
                 in case runProgramIn noWorld{worldInput = unlines text} eraserProgram of
                        Error e -> Just e
                        Ok ((output, errors), _)
                            | null errors && "tersus-mir 1\n" `isInfixOf` ('\n' : output) -> Nothing
                            | otherwise -> Just ("got output " ++ show (take 80 output) ++ " and errors " ++ show errors ++ " for\n" ++ unlines text)

everyProgram :: IO TestResult
everyProgram = withProgram "examples/mir_erase.tersus" "mir-erase" $ \exe -> do
    files <- mapM (\path -> (,) path <$> readFile path) nativeExamples
    failures <- mapM (check exe) (files ++ validatedPrograms)
    pure $ case concat failures of
        [] -> Nothing
        bad -> Just (unlines (take 5 bad))
  where
    check exe (name, source) = case validatedSource source of
        Error e -> pure [name ++ ": " ++ e]
        Ok program -> case eraseGhosts program of
            Error e -> pure [name ++ ": the Haskell refuses: " ++ e]
            Ok erased -> do
                (code, output, errors) <- runExecutableBytes exe [] (writeProgramWithGhosts program)
                let expected = writeProgram (withoutUninit erased)
                pure
                    [ name ++ ": wrote\n" ++ output ++ "\nwith errors " ++ take 200 errors ++ "\nfor (expected)\n" ++ expected
                    | code /= ExitSuccess || not (null errors) || not (sameText output expected)
                    ]
