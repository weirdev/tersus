module Pipeline
    ( parseSource
    , compileSource
    , validateStatements
    , runStatements
    ) where

import qualified Mir as M
import MirEval (MirValue, runProgram)
import MirLower (lowerElaborated)
import MirValidate (Validated, validateProgram)
import Parse (parseStatementBlock)
import TersusTypes (Statement)
import TypeCheck (elaborate)
import Utils

-- The stages a program goes through, each built on the one before and each giving back what the next needs:
--
--   source -> AST (parseSource) -> checked AST (elaborate: types checked, each `shrinks` resolved)
--          -> MIR (lowerElaborated) -> validated MIR (validateProgram) -> executed (runProgram)
--
-- The program is type checked once, by `elaborate`; the lowering takes its result and the validator the MIR. Errors name
-- the stage that refused the program, as the command line prints them.

parseSource :: String -> Result [Statement] String
parseSource source = case parseStatementBlock source of
    Left err -> Error ("Parse error: " ++ show err)
    Right stmts -> Ok stmts

-- The MIR of a program that passes every check
compileSource :: String -> Result M.Program String
compileSource source =
    parseSource source `bindResult` \stmts ->
        stage "Validation failed: " (elaborate stmts) `bindResult` \elaborated ->
            stage "Lowering failed: " (lowerElaborated elaborated) `bindResult` \program ->
                stage "Validation failed: " (validateProgram program) `bindResult` \_ ->
                    Ok program

-- Checks and validates a program given as statements
validateStatements :: [Statement] -> Result Validated String
validateStatements stmts =
    elaborate stmts `bindResult` \elaborated ->
        lowerElaborated elaborated `bindResult` validateProgram

-- Runs a program given as statements, once it type checks, without validating it
runStatements :: [Statement] -> Result (Maybe MirValue) String
runStatements stmts =
    elaborate stmts `bindResult` \elaborated ->
        lowerElaborated elaborated `bindResult` runProgram

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
