module Cli
    ( Command (..)
    , parseCommandLine
    , runSource
    , renderValue
    , usage
    ) where

import Data.List (intercalate)

import Mir (renderProgram)
import MirEval (renderMirValue, runProgram)
import Pipeline
import TersusTypes
import Utils

-- `Check` parses and validates a program. `Run` also lowers it to the MIR and runs that, but only after it validates,
-- and `Mir` prints the MIR instead.
data Command = Check | Run | Mir deriving (Show, Eq)

usage :: String
usage =
    unlines
        [ "Usage: tersus <command> <file>"
        , ""
        , "Commands:"
        , "  check <file>  Parse and validate a program"
        , "  run <file>    Validate a program, then lower it to the MIR, run that and print its return value"
        , "  mir <file>    Validate a program, then print its MIR"
        , ""
        , "Use - as the file to read the program from standard input."
        ]

-- Splits the command line into a command and the file it applies to.
parseCommandLine :: [String] -> Maybe (Command, FilePath)
parseCommandLine ["check", file] = Just (Check, file)
parseCommandLine ["run", file] = Just (Run, file)
parseCommandLine ["mir", file] = Just (Mir, file)
parseCommandLine _ = Nothing

-- Runs a command over program source. Ok holds the text to print on success, which is
-- empty when there is nothing to report; Error holds the message for a failure.
runSource :: Command -> String -> Result String String
runSource Check source = mapResult (const "OK") (checkSource source)
runSource Run source =
    compileSource source `bindResult` \program ->
        case runProgram program of
            Error e -> Error ("Evaluation failed: " ++ e)
            Ok result -> Ok (maybe "" renderMirValue result)
runSource Mir source = mapResult renderProgram (compileSource source)

renderValue :: Value -> String
renderValue (VInt i) = show i
renderValue (VData name []) = name
renderValue (VData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderValue v | (f, v) <- fields] ++ " }"
renderValue (VList l) = "[" ++ intercalate ", " (map renderValue l) ++ "]"
renderValue (VBool True) = "true"
renderValue (VBool False) = "false"
renderValue VFunct{} = "<function>"
renderValue VFnRef{} = "<function>"
