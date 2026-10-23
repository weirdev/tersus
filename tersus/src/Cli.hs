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
import MirLower (lowerProgram)
import Parse
import Proof
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
runSource command source =
    case parseStatementBlock source of
        Left err -> Error ("Parse error: " ++ show err)
        Right stmts ->
            case validate stmts of
                Error e -> Error ("Validation failed: " ++ e)
                Ok _ -> case command of
                    Check -> Ok "OK"
                    Run -> lowered stmts `bindResult` \program ->
                        case runProgram program of
                            Error e -> Error ("Evaluation failed: " ++ e)
                            Ok result -> Ok (maybe "" renderMirValue result)
                    Mir -> mapResult renderProgram (lowered stmts)
  where
    lowered stmts = case lowerProgram stmts of
        Error e -> Error ("Lowering failed: " ++ e)
        Ok program -> Ok program

renderValue :: Value -> String
renderValue (VInt i) = show i
renderValue (VData name []) = name
renderValue (VData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderValue v | (f, v) <- fields] ++ " }"
renderValue (VList l) = "[" ++ intercalate ", " (map renderValue l) ++ "]"
renderValue (VBool True) = "true"
renderValue (VBool False) = "false"
renderValue VFunct{} = "<function>"
