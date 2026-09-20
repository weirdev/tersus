module Cli
    ( Command (..)
    , parseCommandLine
    , runSource
    , renderValue
    , usage
    ) where

import Data.List (intercalate)

import Parse
import Proof
import ProofHelpers (getReturn)
import TersusTypes
import Utils

-- `Check` parses and validates a program. `Run` also evaluates it, but only after it validates.
data Command = Check | Run deriving (Show, Eq)

usage :: String
usage =
    unlines
        [ "Usage: tersus <command> <file>"
        , ""
        , "Commands:"
        , "  check <file>  Parse and validate a program"
        , "  run <file>    Validate a program, then evaluate it and print its return value"
        , ""
        , "Use - as the file to read the program from standard input."
        ]

-- Splits the command line into a command and the file it applies to.
parseCommandLine :: [String] -> Maybe (Command, FilePath)
parseCommandLine ["check", file] = Just (Check, file)
parseCommandLine ["run", file] = Just (Run, file)
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
                    Run -> case evaluate stmts of
                        Error e -> Error ("Evaluation failed: " ++ e)
                        Ok state -> Ok (maybe "" renderValue (getReturn state))

renderValue :: Value -> String
renderValue (VInt i) = show i
renderValue (VIntList l) = "[" ++ intercalate ", " (map show l) ++ "]"
renderValue (VBool True) = "true"
renderValue (VBool False) = "false"
renderValue VFunct{} = "<function>"
