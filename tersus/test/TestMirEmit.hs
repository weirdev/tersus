module TestMirEmit (testMirEmit) where

import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import System.Exit (ExitCode (..))

import Cli (Command (..), World (..), noWorld, runSourceIn)
import LlvmEmit (emitBody, emitOutline)
import Mir
import MirData (forNative, writeProgram)
import Pipeline (ownedSource)
import Pretty (renderType)
import TersusTypes (Type (..))
import TestHarness
import TestMirReader (sameText, withProgram)
import TestNative (nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The lowering to LLVM IR written in Tersus (examples/emit.tersus, step 31 of the roadmap and STEP31.md) while it is written a part at a time. It is given the MIR
-- as data, and what it writes is compared with the Haskell it replaces, for every example and every program that native code is tested with:
-- - `outline`: the declarations, the descriptors of the types of the locals and the entry point, against `LlvmEmit.emitOutline`;
-- - `bodies`: the code of each function (operands, constants, arithmetic, the operations of the runtime, terminators and calls), against `LlvmEmit.emitBody`. The
--   emitter has so far the functions that make words; the others it reports as unsupported, and what is checked is that it has every one that makes only words
--   (`wordOnly`) and that what it writes for the others is what the Haskell writes.
-- The emitter is built once (it needs clang, and the tests pass without it); a smaller input is run by the interpreter.
testMirEmit :: Test
testMirEmit =
    TestList
        "testMirEmit"
        [ TestCase "the reader is the same in the reader and in the emitter" sameReader
        , TestList
            "interpreted"
            [ TestCase "the outline of a loop" (readFile "examples/loops.tersus" >>= interpretedOutline)
            , TestCase "the outline of a struct and an enum" (readFile "examples/enums.tersus" >>= interpretedOutline)
            , TestCase "the code of a loop" (readFile "examples/loops.tersus" >>= interpretedBodies)
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

-- Whether a function makes only words, which is what the emitter has so far
wordOnly :: Function -> Bool
wordOnly f = all (word . localType) (Map.elems (fnLocals f)) && all statementOk statements && all (terminatorOk . bTerm) blocks
  where
    blocks = Map.elems (fnBlocks f)
    bTerm (BasicBlock _ t) = t
    statements = concat [ss | BasicBlock ss _ <- blocks]
    word t = case t of
        TInt -> True
        TByte -> True
        TBool -> True
        TFn{} -> True
        _ -> False
    statementOk s = case s of
        Assign _ rv -> rvalueOk rv
        Peek _ rv -> rvalueOk rv
        Drop _ -> True
        Ghost _ _ -> True
    rvalueOk rv = case rv of
        Use o -> operandOk o
        BinaryOp _ a b -> operandOk a && operandOk b
        ListOp op os -> all operandOk os && (op, length os) `elem` [(ReadByte, 0), (PathByte, 1), (FileLoad, 0), (FileByte, 1), (StoreByte, 1), (FileStore, 0), (ArgCount, 0), (ArgByte, 2), (ToByte, 1), (FromByte, 1), (WriteError, 1), (WriteByte, 1)]
        _ -> False
    terminatorOk t = case t of
        SwitchBool o _ _ -> operandOk o
        Call callee args _ _ -> all operandOk (callee : args)
        _ -> True
    operandOk o = case o of
        Const (CInt _) -> True
        Const (CBool _) -> True
        Const (CFn _) -> True
        Const _ -> False
        _ -> True

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

-- What is wrong with the code the emitter wrote (the functions it has are those the Haskell writes, and it has all that make only words), and how many functions it had
compareBodies :: Program -> String -> ([String], Int)
compareBodies program output = (concat problems, length (filter id supported))
  where
    expected = bodySections program
    written = sectionsOf output
    results = zipWith3 check [0 :: Int ..] expected (map Just written ++ repeat Nothing)
    problems = map fst results
    supported = map snd results
    check i (f, haskell) w = case (haskell, w) of
        (_, Nothing) -> ([show i ++ ": nothing was written"], False)
        (Nothing, Just section)
            | section == ["; function " ++ show i, "; unsupported"] -> ([], False)
            | otherwise -> ([show i ++ ": the Haskell gives no code, and the emitter wrote some"], True)
        (Just lines', Just section)
            | section == ["; function " ++ show i, "; unsupported"] -> ([show i ++ ": unsupported but all words" | wordOnly f], False)
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
            let program = forNative owned
                (bodyProblems, count) = case bodies of
                    (ExitSuccess, output, "") -> compareBodies program output
                    (code, output, errors) -> (["exit " ++ show code ++ ", wrote " ++ show (length output) ++ " bytes, " ++ take 200 errors], 0)
                outlineProblems = case (outline, emitOutline program) of
                    ((ExitSuccess, output, ""), Ok text) | output == text -> []
                    ((_, output, errors), Ok text) -> ["the outline: wrote " ++ show (length output) ++ " bytes for " ++ show (length text) ++ ", " ++ take 200 errors]
                    -- (a program that has no entry point: the reason on the standard error, and the value 1)
                    ((_, output, errors), Error e) -> ["the outline: wrote " ++ show output ++ " with " ++ show errors ++ " and not " ++ show e | output /= "1\n" || errors /= e ++ "\n"]
            pure ([name ++ ": " ++ p | p <- outlineProblems ++ bodyProblems], count)

refusal :: IO TestResult
refusal = withProgram "examples/emit.tersus" "emit" $ \exe -> do
    (_, output, errors) <- runExecutableBytes exe ["outline"] "return 1;\n"
    (_, output', errors') <- runExecutableBytes exe ["nonsense"] "tersus-mir 1\n"
    pure $
        if output == "1\n" && not (null errors) && output' == "1\n" && not (null errors')
            then Nothing
            else Just ("read as " ++ show output ++ " with " ++ show errors ++ ", and " ++ show output' ++ " with " ++ show errors')
