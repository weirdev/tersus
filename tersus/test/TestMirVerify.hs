module TestMirVerify (testMirVerify) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import System.Exit (ExitCode (..))

import Cli (World (..), noWorld, runProgramIn)
import Mir
import MirData (forNative, readProgram, writeProgram)
import MirVerify (verifyProgram)
import Pipeline (ownedSource)
import TersusTypes (Type (..))
import TestHarness
import TestMirReader (sameText, withProgram)
import TestNative (nativeExamples, runExecutableBytes, validatedPrograms)
import Utils

-- The MIR housekeeping of REPLACING_HASKELL.md target 3, in Tersus (examples/mir_verify.tersus): the checks of
-- MirVerify that apply to a program as MirData writes it (the shape, and the types of statements, switches and
-- calls), run over the data of a program and compared verdict by verdict with the Haskell verifyProgram of the
-- same program. Ghost erasure is not here: MirData.forNative has already erased what it would erase, and a data
-- form that still held it would be needed to check that in Tersus.
testMirVerify :: Test
testMirVerify =
    TestList
        "testMirVerify"
        [ TestList
            "interpreted"
            [ TestCase "a well formed program is accepted" (interpreted goodSource id)
            , TestCase "a program with a list is accepted" (interpreted "xs = [1, 2, 3]; return size(xs) + first(xs);" id)
            , TestCase "no entry block" (interpreted goodSource noEntryBlock)
            , TestCase "a local of no known type" (interpreted goodSource varLocal)
            , TestCase "a switch on an Int" (interpreted goodSource switchOnInt)
            , TestCase "a call of a function that is not there" (interpreted goodSource unknownCall)
            , TestCase "an array with the same size parameter is accepted" (interpreted sizedSource id)
            , TestCase "an instance with another array size is refused" (interpreted holderSource wrongHolderArg)
            , TestCase "an array of lists that does not fit in a frame is refused" (interpreted "xs = array(3000, 0); return get(xs, 0);" arrayOfLists)
            , TestCase "what is not the MIR is refused" refused
            ]
        , TestParallel
            "every example and program, natively"
            ( [TestCase path (readFile path >>= nativeCheck path) | path <- nativeExamples]
                ++ [TestCase name (nativeCheck name source) | (name, source) <- validatedPrograms]
            )
        ]

goodSource :: String
goodSource = "fn double(n: Int) -> Int [{ }] [{ }] { return n + n; }; if double(2) = 4 { return 1; }; return 0;"

sizedSource :: String
sizedSource = "fn copyOf<n>(a: Array<Int, n>) -> Array<Int, n> [{ }] [{ }] { b = a; return b; }; xs = #[1, 2]; return size(copyOf(xs));"

holderSource :: String
holderSource = "struct Holder<T> { x: T }; fn take2(h: Holder<Array<Int, 2>>) -> Int [{ }] [{ }] { return get(h.x, 0); }; a = Holder<Array<Int, 2>> { x: #[1, 2] }; b = Holder<Array<Int, 3>> { x: #[1, 2, 3] }; return take2(a);"

-- The verifier compiled once for every interpreted case: compiling it is the expensive part, and every case
-- runs the same program over a different input (the pattern of TestMirEmit's emitterProgram).
verifierProgram :: IO (Result Program String)
verifierProgram = readFile "examples/mir_verify.tersus" >>= compileOnce

-- Whether the Haskell verifier accepts the program, as MirData writes it
referenceAccepts :: Program -> Bool
referenceAccepts program = case verifyProgram (forNative program) of
    Ok () -> True
    Error _ -> False

-- Run the verifier in the interpreter over the data of the mutated program, and compare the verdicts
interpreted :: String -> (Program -> Program) -> IO TestResult
interpreted source mutate = do
    verifier <- verifierProgram
    pure $ case verifier of
        Error e -> Just ("the verifier does not compile: " ++ e)
        Ok verifierProgram -> case ownedSource source of
            Error e -> Just e
            Ok owned ->
                let program = mutate owned
                    text = writeProgram program
                    expected = referenceAccepts program
                 in case runProgramIn noWorld{worldInput = text} verifierProgram of
                        Error e -> Just e
                        Ok ((output, errors), _)
                            | expected && sameText output "OK" && null errors -> Nothing
                            | not expected && output == "1" && not (null errors) -> Nothing
                            | otherwise -> Just ("expected " ++ verdict expected ++ ", got output " ++ show output ++ " and errors " ++ show errors ++ " for\n" ++ text)
  where
    verdict True = "acceptance"
    verdict False = "refusal"

refused :: IO TestResult
refused = do
    verifier <- verifierProgram
    pure $ case verifier of
        Error e -> Just ("the verifier does not compile: " ++ e)
        Ok verifierProgram -> case runProgramIn noWorld{worldInput = ""} verifierProgram of
            Error e -> Just e
            Ok ((output, errors), _)
                | output == "1" && "not the MIR as data" `isInfixOf` errors -> Nothing
                | otherwise -> Just ("got output " ++ show output ++ " and errors " ++ show errors)

noEntryBlock :: Program -> Program
noEntryBlock program = program{progMain = (progMain program){fnBlocks = Map.delete (BlockId 0) (fnBlocks (progMain program))}}

varLocal :: Program -> Program
varLocal program = program{progMain = change (progMain program)}
  where
    change fn = case Map.keys (fnLocals fn) of
        [] -> fn
        local : _ -> fn{fnLocals = Map.adjust (\decl -> decl{localType = TVar 0}) local (fnLocals fn)}

switchOnInt :: Program -> Program
switchOnInt = onEveryFunction change
  where
    change fn = fn{fnBlocks = Map.map block (fnBlocks fn)}
    block basic = basic{blockTerminator = case blockTerminator basic of
        SwitchBool _ yes no -> SwitchBool (Const (CInt 1)) yes no
        other -> other}

unknownCall :: Program -> Program
unknownCall = onEveryFunction change
  where
    change fn = fn{fnBlocks = Map.map block (fnBlocks fn)}
    block basic = basic{blockTerminator = case blockTerminator basic of
        Call _ args dest next -> Call (Const (CFn "noSuchFunction")) args dest next
        other -> other}

localNamed :: Function -> String -> Maybe Local
localNamed fn wanted = case [local | (local, decl) <- Map.toList (fnLocals fn), localName decl == Just wanted] of
    local : _ -> Just local
    [] -> Nothing

wrongHolderArg :: Program -> Program
wrongHolderArg program = case localNamed (progMain program) "b" of
    Nothing -> program
    Just b -> program{progMain = change (progMain program)}
      where
        change fn = fn{fnBlocks = Map.map block (fnBlocks fn)}
        block basic = basic{blockTerminator = case blockTerminator basic of
            Call callee@(Const (CFn "take2")) (_ : rest) dest next -> Call callee (Copy b : rest) dest next
            other -> other}

arrayOfLists :: Program -> Program
arrayOfLists program = case localNamed (progMain program) "xs" of
    Nothing -> program
    Just xs -> program{progMain = (progMain program){fnLocals = Map.adjust change xs (fnLocals (progMain program))}}
  where
    change decl = decl{localType = case localType decl of
        TArrayOf _ size -> TArrayOf (TList TInt) size
        other -> other}

onEveryFunction :: (Function -> Function) -> Program -> Program
onEveryFunction change program =
    program
        { progMain = change (progMain program)
        , progFunctions = Map.map change (progFunctions program)
        }

withVerifier :: (FilePath -> IO TestResult) -> IO TestResult
withVerifier = withProgram "examples/mir_verify.tersus" "mir-verify"

-- One case per program, so the sweep runs at the harness's parallelism instead of one program after another
-- inside a single case (withVerifier builds the verifier executable once for the process). The data comes from
-- the harness's shared cache (mirDataOf), and the Haskell verdict is taken on the program read back from it.
nativeCheck :: String -> String -> IO TestResult
nativeCheck name source = withVerifier $ \exe -> do
    failures <- check exe (name, source)
    pure $ case failures of
        [] -> Nothing
        bad -> Just (unlines bad)
  where
    check exe (name, source) = do
        dataOf <- mirDataOf source
        case dataOf of
            Error e -> pure [name ++ ": " ++ e]
            Ok text -> case readProgram text of
                Error e -> pure [name ++ ": the data does not read back: " ++ e]
                Ok program -> do
                    let expected = referenceAccepts program
                    (code, output, errors) <- runExecutableBytes exe [] text
                    let accepted = code == ExitSuccess && sameText output "OK"
                        refusedIt = code /= ExitSuccess && output == "1\n" && not (null errors)
                    pure
                        [ name ++ ": expected " ++ (if expected then "acceptance" else "refusal") ++ ", got exit " ++ show code ++ ", output " ++ show output ++ ", errors " ++ take 200 errors
                        | (expected && not accepted) || (not expected && not refusedIt)
                        ]
