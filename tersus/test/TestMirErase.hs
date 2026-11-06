module TestMirErase (testMirErase) where

import Data.List (isInfixOf, isPrefixOf, isSuffixOf)
import System.Exit (ExitCode (..))

import Cli (World (..), noWorld, runProgramIn)
import qualified Data.Map.Strict as Map
import Mir (BasicBlock (..), Function (..), Program (..), Statement (..), Rvalue (..), LocalDecl (..), ListOp (..))
import MirData (writeProgram, writeProgramWithGhosts)
import MirHousekeeping (eraseGhosts, toolOwnedProgram, toolProgram)
import Types (Type (..))
import Pipeline (validatedSource)
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
        [ TestCase "local metadata borrows recursive declarations" metadataBorrows
        , TestList
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
        , TestList "local IDs, interpreted"
            [TestCase name (rawExact input output errors) | (name, input, output, errors) <- localCases]
        , TestCase "local IDs, natively" localNative
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
expectedOf :: Program -> Result String String
expectedOf program = mapResult writeProgram (eraseGhosts program)

-- Run the interpreted eraser once and assert both the host erasure and the recorded golden output.
interpretedGolden :: String -> String -> IO TestResult
interpretedGolden source recorded = do
    eraser <- eraserProgram
    pure $ case eraser of
        Error e -> Just ("the eraser does not compile: " ++ e)
        Ok eraserProgram -> case validatedSource source of
            Error e -> Just e
            Ok program -> case expectedOf program of
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
            Ok program -> case expectedOf program of
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
        validated <- if "examples/mir/" `isPrefixOf` name then linkedFromFile name else validatedOnce source
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

-- Metadata construction must not reintroduce a whole LocalDecl/Type clone through a projection.
metadataBorrows :: IO TestResult
metadataBorrows =
    pure $ case toolOwnedProgram "examples/mir/mir_erase/mir_erase.tersus" of
        Error e -> Just e
        Ok owned ->
            let large ty = case ty of
                    TNamed name _ -> name `elem` ["HashMap", "mir$reader$reader$Function", "mir$reader$reader$LocalDecl", "data$codec$codec$Type"]
                    _ -> False
                check name = case Map.lookup name (progFunctions owned) of
                    Nothing -> ["missing " ++ name]
                    Just fn ->
                        [ name ++ " clones " ++ show dest
                        | block <- Map.elems (fnBlocks fn)
                        , Assign dest rv <- blockStatements block
                        , copies rv
                        , Just decl <- [Map.lookup dest (fnLocals fn)]
                        , large (localType decl)
                        ]
                failures = concatMap check ["indexLocals", "localInfo", "castProblem", "eraseProgram"]
             in if null failures then Nothing else Just (unlines failures)
  where
    copies (CopyOf _) = True
    copies (ListOp Get _) = True
    copies _ = False

rawExact :: String -> String -> String -> IO TestResult
rawExact input expected expectedErrors = do
    eraser <- eraserProgram
    pure $ case eraser of
        Error e -> Just e
        Ok program -> case runProgramIn noWorld{worldInput = input} program of
            Error e -> Just e
            Ok ((output, errors), _)
                | output == expected && errors == expectedErrors -> Nothing
                | otherwise -> Just ("expected " ++ show (expected, expectedErrors) ++ ", got " ++ show (output, errors))

localNative :: IO TestResult
localNative = withProgram "examples/mir/mir_erase/mir_erase.tersus" "mir-erase" $ \exe -> do
    failures <- mapM (check exe) localCases
    pure $ case [failure | Just failure <- failures] of
        [] -> Nothing
        bad -> Just (unlines bad)
  where
    check exe (name, input, expected, expectedErrors) = do
        (code, output, errors) <- runExecutableBytes exe [] input
        let nativeExpected = if expected == "1" then "1\n" else expected
        pure $ if code == ExitSuccess && output == nativeExpected && errors == expectedErrors
            then Nothing
            else Just (name ++ ": expected " ++ show (nativeExpected, expectedErrors) ++ ", got " ++ show (code, output, errors))

localCases :: [(String, String, String, String)]
localCases =
    [ ("sparse out-of-order duplicate and missing IDs", wire 2 [] header sparse, wire 1 [] header sparseErased, "")
    , ("mixed ghost runtime and local zero retarget above maximum", wire 2 mixedTypes mixedHeader mixed, wire 1 erasedTypes erasedHeader mixedErased, "")
    , ("negative and large signed IDs", wire 2 [] header signed, wire 1 [] header signed, "")
    , ("empty local table", wire 2 [] header [], wire 1 [] header [], "")
    , ("metadata survives HashMap growth", wire 2 [] header growth, wire 1 [] header keptGrowth, "")
    , ("ghost type depth limit is unchanged", wire 2 deepTypes header deepLocals, wire 1 deepErasedTypes header deepKept, "")
    , cast "sparse cast reports layout before erasure" ["local 90 none block array int c 2", "local 7 none block int"] "copy 7" sizeError
    , cast "duplicate destination cast uses first declaration" ["local 90 none block array int c 2", "local 7 none block int", "local 90 none int"] "move 7" sizeError
    , cast "duplicate source cast uses first declaration" ["local 90 none block array int c 2", "local 7 none block int", "local 7 none block array int c 2"] "copy 7" sizeError
    , cast "cast reports unknown layout" ["local 90 none block int", "local 7 none block param \"T\""] "move 7" unknownError
    , ("missing cast source remains non-ghost", wire 2 [] header ["local 90 none block int", "block 0", "assign 90 listop blockCast 1 copy 999", "return"], wire 1 [] header ["block 0", "return"], "")
    , ("malformed local type is refused", wire 2 [] header ["local 7 none text"], "1", "the input is not the MIR as data\n")
    ]
  where
    header = "main \"main\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0"
    wire :: Int -> [String] -> String -> [String] -> String
    wire version types h body = unlines (["tersus-mir " ++ show version] ++ types ++ [h] ++ body ++ ["end"])
    sparse =
        [ "local 42 none block int", "local 7 none int", "local 0 none int", "local 7 none block bool", "local 42 none int"
        , "block 0", "assign 7 listop addrWrite 4 copy 42 move 7 copy 999 const int 3", "assign 999 use const int 5", "dissolve 42", "dissolve 999", "return"
        ]
    sparseErased =
        [ "local 7 none int", "local 0 none int", "local 7 none block bool"
        , "block 0", "assign 7 listop addrWrite 3 move 7 copy 999 const int 3", "assign 999 use const int 5", "peek 999 listop uninitEmpty 0", "return"
        ]
    mixedTypes = ["struct \"Ghost\" 1 \"g\" block int", "struct \"Mixed\" 2 \"g\" block int \"r\" int"]
    erasedTypes = ["struct \"Ghost\" 0", "struct \"Mixed\" 1 \"r\" int"]
    mixedHeader = "main \"main\" params 4 42 7 0 999 returns some block int sizeparams 0 typeparams 0 borrowed 3 42 7 0 mutborrowed 2 42 7 from 3 0 42 7"
    erasedHeader = "main \"main\" params 2 7 999 returns some int sizeparams 0 typeparams 0 borrowed 1 7 mutborrowed 1 7 from 1 7"
    mixed =
        [ "local 1024 none int", "local 42 none named \"Ghost\" 0", "local 7 none named \"Mixed\" 0", "local 0 some \"result\" block int"
        , "block 0", "assign 42 listop addrWrite 4 const int 1 const int 0 const int 3 copy 42"
        , "assign 7 makedata \"Mixed\" 2 \"g\" copy 42 \"r\" const int 3"
        , "assign 0 use copy 42", "assign 0 listop addrFree 2 const int 1 copy 0"
        , "call const fn \"missing\" 3 copy 42 copy 7 copy 999 42 1", "block 1", "return"
        ]
    mixedErased =
        [ "local 1024 none int", "local 7 none named \"Mixed\" 0", "local 0 some \"result\" int", "local 1025 none int", "local 1026 none int"
        , "block 0", "assign 1025 listop addrWrite 3 const int 1 const int 0 const int 3"
        , "assign 7 makedata \"Mixed\" 1 \"r\" const int 3", "assign 0 use const int 0", "assign 0 listop addrFree 1 const int 1"
        , "call const fn \"missing\" 2 copy 7 copy 999 1026 1", "block 1", "return"
        ]
    signed = ["local -9223372036854775808 none int", "local 9223372036854775806 none int", "local -3 none int", "block 0", "assign -3 use copy -9223372036854775808", "return"]
    growth = ["local " ++ show (i * 37) ++ " none " ++ if even i then "int" else "block int" | i <- [0..39 :: Int]] ++ ["block 0", "return"]
    keptGrowth = ["local " ++ show (i * 37) ++ " none int" | i <- [0,2..38 :: Int]] ++ ["block 0", "return"]
    deepTypes = ["struct \"G" ++ show i ++ "\" 1 \"g\" " ++ (if i == 16 then "block int" else "named \"G" ++ show (i + 1) ++ "\" 0") | i <- [0..16 :: Int]]
    deepErasedTypes = ["struct \"G" ++ show i ++ "\" 0" | i <- [0..16 :: Int]]
    deepLocals = ["local 8 none named \"G0\" 0", "local 9 none named \"G1\" 0", "block 0", "return"]
    deepKept = ["local 8 none named \"G0\" 0", "block 0", "return"]
    cast name locals operand errorText = (name, wire 2 [] header (locals ++ ["block 0", "assign 90 listop blockCast 1 " ++ operand, "return"]), "1", errorText)
    sizeError = "in main: Block::cast from Int to Array<Int, 2>, whose slots are not the same size, or are aligned more strictly (8,8) and (16,8), as bytes and alignment)\n"
    unknownError = "in main: Block::cast from 'T to Int, where the layout of a type parameter or a size parameter is not known\n"
