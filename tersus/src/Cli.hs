module Cli
    ( Command (..)
    , parseCommandLine
    , runSource
    , runSourceWith
    , renderValue
    , usage
    , readSourceFile
    , readInputBytes
    , useUtf8
    ) where

import Data.List (intercalate)
import System.IO

import Mir (renderProgram)
import MirEval (renderMirValue, runProgramWith)
import Pipeline
import TersusTypes
import Utils

-- `Check` parses a program, lowers it to the MIR and validates that. `Run` is how a program is run: it validates it, compiles it
-- to native code (the same as `Build`, to an executable that is run and removed) and runs that. `Interpret` (`tersus eval`) runs the validated MIR with
-- the executor of MirEval instead, which is the reference that the native code is tested against and needs no compiler.
-- `Mir` prints the MIR instead, and `Owned` the MIR that native code is made from, with the owner of each value in it.
-- `Llvm` prints the LLVM IR of the validated program, and `Build` compiles that to the
-- executable at the path.
data Command = Check | Run | Interpret | Mir | Owned | Llvm | Build FilePath deriving (Show, Eq)

usage :: String
usage =
    unlines
        [ "Usage: tersus <command> <file> [-o <output>]"
        , ""
        , "Commands:"
        , "  check <file>  Parse and validate a program"
        , "  run <file>    Validate a program, compile it to native code (needs clang), run that and print its return value"
        , "  eval <file>   Validate a program, then run its MIR with the reference interpreter (no compiler needed)"
        , "  mir <file>    Validate a program, then print its MIR"
        , "  owned <file>  Validate a program, then print its MIR with moves, copies and frees for native code"
        , "  llvm <file>   Validate a program, then print its LLVM IR"
        , "  build <file> -o <output>"
        , "                Validate a program, then compile it to an executable with clang"
        , ""
        , "Use - as the file to read the program from standard input."
        ]

-- Splits the command line into a command and the file it applies to.
parseCommandLine :: [String] -> Maybe (Command, FilePath)
parseCommandLine ["check", file] = Just (Check, file)
parseCommandLine ["run", file] = Just (Run, file)
parseCommandLine ["eval", file] = Just (Interpret, file)
parseCommandLine ["mir", file] = Just (Mir, file)
parseCommandLine ["owned", file] = Just (Owned, file)
parseCommandLine ["llvm", file] = Just (Llvm, file)
parseCommandLine ["build", file, "-o", output] = Just (Build output, file)
parseCommandLine _ = Nothing

-- Runs a command over program source. Ok holds the text to print on success, which is
-- empty when there is nothing to report; Error holds the message for a failure.
runSource :: Command -> String -> Result String String
runSource = runSourceWith ""

-- The same for a program that has input (the bytes of the standard input, as characters from 0 to 255), which `Interpret` gives to `readByte`;
-- an executable reads its own
runSourceWith :: String -> Command -> String -> Result String String
runSourceWith _ Check source = mapResult (const "OK") (compileSource source)
runSourceWith input Interpret source =
    compileSource source `bindResult` \program ->
        case runProgramWith input program of
            Error e -> Error ("Evaluation failed: " ++ e)
            -- (what the program wrote, then its value: the same text as an executable prints)
            Ok (written, result) -> Ok (decodeUtf8 written ++ maybe "" renderMirValue result)
runSourceWith _ Mir source = mapResult renderProgram (compileSource source)
runSourceWith _ Owned source = mapResult renderProgram (ownedSource source)
runSourceWith _ Llvm source = llvmSource source
-- (compiling the IR, and running it for `Run`, is left to the caller, since it runs clang)
runSourceWith _ Run source = llvmSource source
runSourceWith _ (Build _) source = llvmSource source

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

-- The standard input as bytes (characters from 0 to 255), read as the program asks for them
readInputBytes :: IO String
readInputBytes = hSetEncoding stdin char8 >> getContents

useUtf8 :: IO ()
useUtf8 = mapM_ (`hSetEncoding` utf8) [stdout, stderr]
