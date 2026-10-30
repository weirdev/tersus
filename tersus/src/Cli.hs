module Cli
    ( Command (..)
    , parseCommandLine
    , parseProgramArguments
    , splitEmitterFlag
    , makesIr
    , World (..)
    , noWorld
    , runSourceIn
    , runSourceFiles
    , runProgramIn
    , readWorldFile
    , writeWorldFiles
    , runSource
    , runSourceWith
    , runSourceStreams
    , renderValue
    , usage
    , readSourceFile
    , readInputBytes
    , useUtf8
    ) where

import Data.List (intercalate)
import Control.Exception (IOException, try)
import System.IO
import System.IO.Unsafe (unsafePerformIO)

import Mir (Program, renderProgram)
import MirData (writeProgram)
import MirEval (Outcome (..), RunEnv (..), renderMirValue, runProgramEnv)
import Pipeline
import TersusTypes
import Utils

-- `Check` parses a program, lowers it to the MIR and validates that. `Run` is how a program is run: it validates it, compiles it
-- to native code (the same as `Build`, to an executable that is run and removed) and runs that. `Interpret` (`tersus eval`) runs the validated MIR with
-- the executor of MirEval instead, which is the reference that the native code is tested against and needs no compiler.
-- `Mir` prints the MIR instead, and `Owned` the MIR that native code is made from, with the owner of each value in it. `MirText` (`mir --data`)
-- prints that as data for a program to read (MirData).
-- `Llvm` prints the LLVM IR of the validated program, and `Build` compiles that to the
-- executable at the path.
-- `Assumptions` lists what the program takes on trust (`assume`, `Block::assume` and `axiom`), which the validator does not prove.
data Command = Check | Run | Interpret | Mir | MirText | Owned | Llvm | Build FilePath | Assumptions deriving (Show, Eq)

usage :: String
usage =
    unlines
        [ "Usage: tersus [--haskell-emitter] <command> <file> [-o <output>]"
        , ""
        , "Commands:"
        , "  check <file>  Parse and validate a program"
        , "  run <file> [args]"
        , "                Validate a program, compile it to native code (needs clang), run it with the arguments and print its return value"
        , "  eval <file> [args]"
        , "                Validate a program, then run its MIR with the reference interpreter (no compiler needed)"
        , "  mir <file>    Validate a program, then print its MIR"
        , "  mir --data <file>"
        , "                Validate a program, then print the MIR that native code is made from as data (see MirData)"
        , "  owned <file>  Validate a program, then print its MIR with moves, copies and frees for native code"
        , "  llvm <file>   Validate a program, then print its LLVM IR"
        , "  assumptions <file>"
        , "                Print what the program takes on trust, which the validator does not prove: each assume, Block::assume, extern fn and axiom"
        , "  build <file> -o <output>"
        , "                Validate a program, then compile it to an executable with clang"
        , ""
        , "Use - as the file to read the program from standard input."
        , ""
        , "llvm, build and run write the LLVM IR with the emitter that is written in Tersus (examples/emit.tersus; see Bootstrap), which is built with clang the"
        , "first time (from bootstrap/emitter.ll) and kept in the cache. With --haskell-emitter first they use the emitter in Haskell (LlvmEmit) instead, which needs no clang"
        , "to print the IR."
        ]

-- Splits the command line into a command and the file it applies to.
parseCommandLine :: [String] -> Maybe (Command, FilePath)
parseCommandLine ["check", file] = Just (Check, file)
parseCommandLine ["run", file] = Just (Run, file)
parseCommandLine ["eval", file] = Just (Interpret, file)
parseCommandLine ["mir", file] = Just (Mir, file)
parseCommandLine ["mir", "--data", file] = Just (MirText, file)
parseCommandLine ["owned", file] = Just (Owned, file)
parseCommandLine ["llvm", file] = Just (Llvm, file)
parseCommandLine ["build", file, "-o", output] = Just (Build output, file)
parseCommandLine ["assumptions", file] = Just (Assumptions, file)
parseCommandLine _ = Nothing

-- Whether the command line starts with the flag that has the emitter in Haskell write the LLVM IR (it is the emitter in Tersus that does otherwise), and the rest of it
splitEmitterFlag :: [String] -> (Bool, [String])
splitEmitterFlag ("--haskell-emitter" : rest) = (True, rest)
splitEmitterFlag args = (False, args)

-- The commands that make LLVM IR, and so have it written by the emitter in Tersus
makesIr :: Command -> Bool
makesIr Llvm = True
makesIr Run = True
makesIr (Build _) = True
makesIr _ = False

-- The same, with the arguments that `run` and `eval` give to the program after its file
parseProgramArguments :: [String] -> Maybe (Command, FilePath, [String])
parseProgramArguments ("run" : file : args) = Just (Run, file, args)
parseProgramArguments ("eval" : file : args) = Just (Interpret, file, args)
parseProgramArguments args = (\(command, file) -> (command, file, [])) <$> parseCommandLine args

-- What a program is run in, besides its source: the bytes of the standard input, and the bytes of each of its arguments (as characters from 0 to 255:
-- `Utils.encodeUtf8` for a text). An executable has its own.
data World = World
    { worldInput :: String
    , worldArgs :: [String]
    , worldFile :: FilePath -> Maybe String -- the files it can read: the contents of the file at a path, or Nothing (both as bytes)
    }

noWorld :: World
noWorld = World "" [] (const Nothing)

-- Runs a command over program source. Ok holds the text to print on success, which is
-- empty when there is nothing to report; Error holds the message for a failure.
runSource :: Command -> String -> Result String String
runSource = runSourceWith ""

-- The same for a program that has input (the bytes of the standard input, as characters from 0 to 255), which `Interpret` gives to `readByte`;
-- an executable reads its own
runSourceWith input command source = mapResult fst (runSourceStreams input command source)

-- The same with what a program wrote to the standard error too: the text for the standard output, and the text for the standard error
runSourceStreams :: String -> Command -> String -> Result (String, String) String
runSourceStreams input = runSourceIn noWorld{worldInput = input}

-- The same for a program that has a world
runSourceIn :: World -> Command -> String -> Result (String, String) String
runSourceIn world command source = mapResult fst (runSourceFiles world command source)

-- The same with the files that the program wrote (each path once, with what the file holds at the end), which `Interpret` does not write itself
runSourceFiles :: World -> Command -> String -> Result ((String, String), [(FilePath, String)]) String
runSourceFiles _ Check source = mapResult (\_ -> (("OK", ""), [])) (compileSource source)
runSourceFiles world Interpret source = compileSource source `bindResult` runProgramIn world
runSourceFiles world command source = mapResult (\text -> ((text, ""), [])) (runOther (worldInput world) command source)

-- What a validated program does when the reference interpreter runs it (what `Interpret` does after `compileSource`): the text it wrote to the
-- standard output and to the standard error, and the files it wrote. A test that runs the same program in several ways compiles it once and calls this.
runProgramIn :: World -> Program -> Result ((String, String), [(FilePath, String)]) String
runProgramIn world program =
    case runProgramEnv RunEnv{envArgs = worldArgs world, envInput = worldInput world, envFile = worldFile world} program of
        Error e -> Error ("Evaluation failed: " ++ e)
        -- (what the program wrote, then its value: the same text as an executable prints)
        Ok o -> Ok ((decodeUtf8 (outStdout o) ++ maybe "" renderMirValue (outValue o), decodeUtf8 (outStderr o)), outFiles o)

runOther :: String -> Command -> String -> Result String String
runOther _ Mir source = mapResult renderProgram (compileSource source)
runOther _ Owned source = mapResult renderProgram (ownedSource source)
runOther _ MirText source = mapResult writeProgram (ownedSource source)
runOther _ Llvm source = llvmSource source
runOther _ Assumptions source = mapResult (\found -> if null found then "No assumptions" else intercalate "\n" found) (assumptionsOf source)
-- (compiling the IR, and running it for `Run`, is left to the caller, since it runs clang)
runOther _ Run source = llvmSource source
runOther _ (Build _) source = llvmSource source
runOther _ _ _ = Error "not a command that is run on its own"

renderValue :: Value -> String
renderValue (VInt i) = show i
renderValue (VData name []) = name
renderValue (VData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderValue v | (f, v) <- fields] ++ " }"
renderValue (VList l) = "[" ++ intercalate ", " (map renderValue l) ++ "]"
renderValue (VBool True) = "true"
renderValue (VBool False) = "false"
renderValue VFunct{} = "<function>"
renderValue VFnRef{} = "<function>"

-- Source text is UTF-8 whatever the locale is (the parser accepts any letter in a name), and so is what is printed
readSourceFile :: FilePath -> IO String
readSourceFile "-" = hSetEncoding stdin utf8 >> getContents
readSourceFile file = do
    handle <- openFile file ReadMode
    hSetEncoding handle utf8
    hGetContents handle

-- The file at a path (as the bytes of the path), as the bytes of its contents, or Nothing when it cannot be read. The path is looked at when the program
-- asks, not before: the files a program may read are not known until it runs.
readWorldFile :: FilePath -> Maybe String
readWorldFile path = unsafePerformIO $ do
    outcome <- try (do
        handle <- openBinaryFile path ReadMode
        contents <- hGetContents handle
        length contents `seq` hClose handle
        return contents)
    return (either (\e -> const Nothing (e :: IOException)) Just outcome)

-- Writes the files that a program wrote, and gives the paths that could not be written
writeWorldFiles :: [(FilePath, String)] -> IO [FilePath]
writeWorldFiles files = concat <$> mapM write files
  where
    write (path, contents) = do
        outcome <- try (withBinaryFile path WriteMode (\handle -> hPutStr handle contents))
        return (either (\e -> const [path] (e :: IOException)) (const []) outcome)

-- The standard input as bytes (characters from 0 to 255), read as the program asks for them
readInputBytes :: IO String
readInputBytes = hSetEncoding stdin char8 >> getContents

useUtf8 :: IO ()
useUtf8 = mapM_ (`hSetEncoding` utf8) [stdout, stderr]
