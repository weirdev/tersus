module TestMirErase (testMirErase) where

import Data.List (isInfixOf, isPrefixOf, isSuffixOf)
import System.Exit (ExitCode (..))

import Cli (World (..), noWorld, runProgramIn)
import qualified Data.Map.Strict as Map
import Mir (BasicBlock (..), Function (..), Program (..), Statement (..))
import MirData (writeProgram, writeProgramWithGhosts)
import MirHousekeeping (eraseGhosts)
import Pipeline (compileSource, validatedSource)
import TestHarness
import TestMirReader (sameText, withProgram)
import TestNative (nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The rest of the MIR housekeeping of REPLACING_HASKELL.md target 3, in Tersus (examples/mir/mir_erase/mir_erase.tersus): the erasure of the
-- ghosts of a program over the data of the program as it is before the erasure (version 2 of the data, writeProgramWithGhosts),
-- compared word for word with the erasure the host runs (MirHousekeeping, which runs this program), and for the programs
-- below with the output recorded of the Haskell erasure it replaced. The erasure also makes each Uninit<T> a T.
testMirErase :: Test
testMirErase =
    TestList
        "testMirErase"
        [ TestList
            "interpreted"
            ( [ TestCase "a program with no ghosts is unchanged" (interpreted "return 1 + 2;")
              , TestCase "permissions are taken out" (interpretedGolden pointers pointersErased)
              , TestCase "a reference is read through" (interpretedGolden borrowSource borrowErased)
              , TestCase "a reference updates through a mutable borrow" (interpreted mutSource)
              , TestCase "the entry function's ghost statements are kept" entryGhostsKept
              , TestCase "what is not the MIR is refused" refused
              ]
                ++ [TestCase label (castCase rewrite expected) | (label, rewrite, expected) <- castCases]
            )
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
eraserProgram = bootstrapFromFile "examples/mir/mir_erase/mir_erase.tersus"

-- What the host makes of the program before its ghosts are erased, as version 1 of the data
expectedOf :: String -> Result String String
expectedOf source = case validatedSource source of
    Error e -> Error e
    Ok program -> mapResult writeProgram (eraseGhosts program)

-- Run the interpreted eraser once and assert both the host erasure and the recorded golden output.
interpretedGolden :: String -> String -> IO TestResult
interpretedGolden source recorded = do
    eraser <- eraserProgram
    pure $ case eraser of
        Error e -> Just ("the eraser does not compile: " ++ e)
        Ok eraserProgram -> case validatedSource source of
            Error e -> Just e
            Ok program -> case expectedOf source of
                Error e -> Just ("the host refuses: " ++ e)
                Ok expected -> case runProgramIn noWorld{worldInput = writeProgramWithGhosts program} eraserProgram of
                    Error e -> Just e
                    Ok ((output, errors), _)
                        | not (null errors) -> Just ("wrote\n" ++ output ++ "\nwith errors " ++ show errors)
                        | not (sameText output expected) -> Just ("wrote\n" ++ output ++ "\nwith errors " ++ show errors ++ "\nfor (expected)\n" ++ expected)
                        | not (sameText output recorded) -> Just ("wrote\n" ++ output ++ "\nwith errors " ++ show errors ++ "\nfor (recorded)\n" ++ recorded)
                        | otherwise -> Nothing

pointersErased :: String
pointersErased =
    unlines
        [ "tersus-mir 1"
        , "struct \"Tuple2<Addr<Int>, Block<Int>>\" 1 \"0\" addr int"
        , "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
        , "local 0 none int"
        , "local 1 none addr int"
        , "local 3 some \"$tuple 1:1\" named \"Tuple2\" 2 type addr int type block int"
        , "local 4 some \"p\" addr int"
        , "local 6 some \"x\" int"
        , "local 7 none int"
        , "local 8 none int"
        , "local 9 none int"
        , "block 0"
        , "assign 1 listop addrAlloc 1 const int 2"
        , "assign 3 makedata \"Tuple2<Addr<Int>, Block<Int>>\" 1 \"0\" copy 1"
        , "assign 4 readfield copy 3 \"Tuple2<Addr<Int>, Block<Int>>\" \"0\""
        , "assign 8 listop addrWrite 3 copy 4 const int 0 const int 5"
        , "assign 6 listop addrGet 2 copy 4 const int 0"
        , "assign 9 listop addrDropValue 2 copy 4 const int 0"
        , "assign 7 listop addrFree 1 copy 4"
        , "assign 0 binary add copy 6 copy 7"
        , "return"
        , "end"
        ]

borrowErased :: String
borrowErased =
    unlines
        [ "tersus-mir 1"
        , "struct \"List<Int>\" 3 \"addr\" addr int \"len\" int \"cap\" int"
        , "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
        , "local 0 none int"
        , "local 1 some \"xs\" named \"List\" 1 type int"
        , "local 2 some \"r\" ref named \"List\" 1 type int"
        , "local 3 none named \"List\" 1 type int"
        , "local 4 none int"
        , "local 5 none named \"List\" 1 type int"
        , "local 6 none int"
        , "block 0"
        , "assign 1 use const list 3 int 1 int 2 int 3"
        , "assign 2 borrow 1 0"
        , "assign 3 deref copy 2"
        , "assign 4 listop length 1 copy 3"
        , "assign 5 deref copy 2"
        , "assign 6 listop get 2 copy 5 const int 0"
        , "assign 0 binary add copy 4 copy 6"
        , "return"
        , "end"
        ]

interpreted :: String -> IO TestResult
interpreted source = do
    eraser <- eraserProgram
    pure $ case eraser of
        Error e -> Just ("the eraser does not compile: " ++ e)
        Ok eraserProgram -> case validatedSource source of
            Error e -> Just e
            Ok program -> case expectedOf source of
                Error e -> Just ("the host refuses: " ++ e)
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

castSource :: String
castSource = "struct Two { a: I32, b: I32 }; impl Clone for Two { }; impl Copy for Two { }; (p, b) = Addr::alloc(2); c = Block::cast(b); q = Addr::cast(p); c = Addr::write(q, 0, Two { a: -1, b: 2 }, c); x = Addr::get(q, 0, c); c = Addr::dropValue(q, 0, c); return toInt(x.a) + toInt(x.b) + Addr::free(q, c);"

twoLine :: String
twoLine = "struct \"Two\" 2 \"a\" i32 \"b\" i32"

data CastExpected = CastRefused | CastAccepted
    deriving (Eq, Show)

-- One table over castSource: (label, rewrite of the ghost data, expected verdict).
-- The first row makes the cast a cast to slots of another size (a permission of Two, 8 bytes, written as
-- two Ints, 16 bytes); the others write the struct the cast is to as another shape of the same layout
-- (Haskell `Mir.layoutOf`: a Block<T> field takes no room, and an Uninit<T> field the room of a T).
castCases :: [(String, String -> String, CastExpected)]
castCases =
    [ ("a cast of a permission to a bigger slot is refused", rewriteBigger, CastRefused)
    , ("a cast to a slot with a ghost field is allowed", replaceTwo "struct \"Two\" 2 \"a\" int \"b\" block int", CastAccepted)
    , ("a cast to a slot with an uninitialized field is allowed", replaceTwo "struct \"Two\" 1 \"a\" uninit int", CastAccepted)
    ]
  where
    rewriteBigger text = unlines (map castLine (lines text))
    castLine line
        | " block named \"Two\" 0" `isSuffixOf` line = take (length line - length "named \"Two\" 0") line ++ "array int c 2"
        | otherwise = line
    replaceTwo to text = unlines (map (\line -> if line == twoLine then to else line) (lines text))

castCase :: (String -> String) -> CastExpected -> IO TestResult
castCase rewrite expected = do
    eraser <- eraserProgram
    pure $ case eraser of
        Error e -> Just ("the eraser does not compile: " ++ e)
        Ok eraserProgram -> case validatedSource castSource of
            Error e -> Just e
            Ok program ->
                let text = rewrite (writeProgramWithGhosts program)
                 in case runProgramIn noWorld{worldInput = text} eraserProgram of
                        Error e -> Just e
                        Ok ((output, errors), _)
                            | expected == CastRefused && output == "1" && not (null errors) -> Nothing
                            | expected == CastAccepted && null errors && "tersus-mir 1\n" `isInfixOf` ('\n' : output) -> Nothing
                            | otherwise -> Just ("got output " ++ show (take 80 output) ++ " and errors " ++ show errors ++ " for\n" ++ text)

everyProgram :: IO TestResult
everyProgram = withProgram "examples/mir/mir_erase/mir_erase.tersus" "mir-erase" $ \exe -> do
    files <- mapM (\path -> (,) path <$> readFile path) nativeExamples
    failures <- mapM (check exe) (files ++ validatedPrograms)
    pure $ case concat failures of
        [] -> Nothing
        bad -> Just (unlines (take 5 bad))
  where
    check exe (name, source) = do
        validated <- if "examples/mir/" `isPrefixOf` name then linkedFromFile name else pure (validatedSource source)
        case validated of
            Error e -> pure [name ++ ": " ++ e]
            Ok program -> case eraseGhosts program of
                Error e -> pure [name ++ ": the host refuses: " ++ e]
                Ok erased -> do
                    (code, output, errors) <- runExecutableBytes exe [] (writeProgramWithGhosts program)
                    let expected = writeProgram erased
                    pure
                        [ name ++ ": wrote\n" ++ output ++ "\nwith errors " ++ take 200 errors ++ "\nfor (expected)\n" ++ expected
                        | code /= ExitSuccess || not (null errors) || not (sameText output expected)
                        ]

-- The host puts back what the data does not carry on the entry function as on any other: a program whose
-- top level holds a ghost statement keeps it through the erasure
entryGhostsKept :: IO TestResult
entryGhostsKept = pure $ case validatedSource "assume 1 = 1; return 1;" of
    Error e -> Just e
    Ok program -> case eraseGhosts program of
        Error e -> Just e
        Ok erased ->
            if any isGhost (concatMap blockStatements (Map.elems (fnBlocks (progMain erased))))
                then Nothing
                else Just "the entry function's ghost statements were dropped by the erasure"
  where
    isGhost (Ghost _ _) = True
    isGhost _ = False
