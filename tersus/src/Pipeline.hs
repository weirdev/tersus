module Pipeline
    ( parseSource
    , checkSource
    , compileSource
    ) where

import qualified Mir as M
import MirLower (lowerElaborated)
import Parse (parseStatementBlock)
import Proof (validateElaborated)
import TersusTypes (Statement)
import TypeCheck (elaborate)
import Utils

-- The stages a program goes through, each built on the one before and each giving back what the next needs:
--
--   source -> AST (parseSource) -> checked AST (elaborate: types checked, each `shrinks` resolved)
--          -> validated (validateElaborated) -> MIR (lowerElaborated)
--
-- The program is type checked once, by `elaborate`; the validator and the lowering both take its result. Errors name the
-- stage that refused the program, as the command line prints them.

parseSource :: String -> Result [Statement] String
parseSource source = case parseStatementBlock source of
    Left err -> Error ("Parse error: " ++ show err)
    Right stmts -> Ok stmts

-- Parses, checks the types and validates; gives the program with each `shrinks` clause resolved
checkSource :: String -> Result [Statement] String
checkSource source =
    parseSource source `bindResult` \stmts ->
        stage "Validation failed: " (elaborate stmts) `bindResult` \elaborated ->
            stage "Validation failed: " (validateElaborated elaborated) `bindResult` \_ ->
                Ok elaborated

-- The MIR of a program that validates
compileSource :: String -> Result M.Program String
compileSource source =
    checkSource source `bindResult` \elaborated ->
        stage "Lowering failed: " (lowerElaborated elaborated)

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
