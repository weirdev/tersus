module Pipeline
    ( parseSource
    , compileSource
    , ownedSource
    , llvmSource
    , nativeProgram
    , validateStatements
    , runStatements
    ) where

import LlvmEmit (emitProgram)
import qualified Mir as M
import MirOwnership (insertOwnership)
import MirVerify (verifyProgram)
import MirEval (MirValue, runProgram)
import MirLower (lowerElaborated)
import MirValidate (Validated, validateProgram)
import Data.Char (isAlphaNum)
import Parse (emptyDecls, parseStatementBlock, parseStatementBlockWith)
import MirLists (lowerLists)
import PreludeSource (listsSource, preludeSource, stringSource)
import TersusTypes (Expression (..), Statement (..), Value (..))
import TypeCheck (elaborate)
import Utils

-- The stages a program goes through, each built on the one before and each giving back what the next needs:
--
--   source -> AST (parseSource) -> checked AST (elaborate: types checked, each `shrinks` resolved)
--          -> MIR (lowerElaborated) -> validated MIR (validateProgram) -> executed (runProgram)
--                                                                    or -> LLVM IR (emitProgram)
--
-- The program is type checked once, by `elaborate`; the lowering takes its result and the validator the MIR. Errors name
-- the stage that refused the program, as the command line prints them.

parseSource :: String -> Result [Statement] String
parseSource source = parseSourceWith True source

-- (the library of lists is the one program that may use the names that a program may not)
parseSourceWith :: Bool -> String -> Result [Statement] String
parseSourceWith reserving source = case libraries source of
    [] -> case parseStatementBlock source of
        Left err -> Error ("Parse error: " ++ show err)
        Right stmts -> checked stmts
    texts -> case readLibraries texts emptyDecls of
        Left err -> Error err
        Right (library, declared) -> case parseStatementBlockWith declared source of
            Left err -> Error ("Parse error: " ++ show err)
            Right (stmts, _) -> checked stmts `bindResult` \stmts' -> Ok (library ++ stmts')
  where
    readLibraries [] declared = Right ([], declared)
    readLibraries ((name, text) : more) declared = case parseStatementBlockWith declared text of
        Left err -> Left ("Parse error in " ++ name ++ ": " ++ show err)
        Right (stmts, declared') -> fmap (\(rest, final) -> (stmts ++ rest, final)) (readLibraries more declared')
    checked stmts = if reserving then maybe (Ok stmts) (\name -> Error ("Type error: " ++ name ++ " is reserved: native code makes a list of the struct StdList and the functions stdList... of lib/lists.tersus, so a program does not declare names like them")) (reservedName stmts) else Ok stmts

-- A name the program declares that native code uses for lists (see MirLists)
reservedName :: [Statement] -> Maybe String
reservedName stmts = case [name | stmt <- stmts, name <- declared stmt, reserved name] of
    name : _ -> Just name
    [] -> Nothing
  where
    declared stmt = case stmt of
        Assign name (Val VFunct{}) -> [name]
        StructDef name _ _ _ -> [name]
        EnumDef name _ -> [name]
        TraitDef name _ _ -> [name]
        BoundedDef _ (Assign name _) -> [name]
        _ -> []
    reserved name = name == "StdList" || take 7 name == "stdList"

-- The libraries that a program has in front of it, in order, unless it declares their names itself, so a program that has a `Vec` of its own is
-- unchanged: lib/prelude.tersus (the traits `Sequence` and `Growable`) if it mentions either, and lib/string.tersus (the struct `String` that a string
-- literal is a value of, which needs the traits) if it mentions `String` or has a literal
libraries :: String -> [(String, String)]
libraries source = [("the prelude", preludeSource) | prelude] ++ [("the string library", stringSource) | strings]
  where
    ws = names source
    ws' = zip ws (drop 1 ws)
    declares candidates = any (\(keyword, name) -> keyword `elem` ["struct", "enum", "trait"] && name `elem` candidates) ws'
    preludeFree = not (declares ["Sequence", "Growable"])
    strings = preludeFree && not (declares ["String"]) && ("String" `elem` ws || hasLiteral source)
    prelude = preludeFree && (strings || any (`elem` ws) ["Sequence", "Growable"])
    -- (the names in a text: runs of letters, digits and underscores)
    names text = case dropWhile (not . isNameChar) text of
        "" -> []
        rest -> let (w, more) = span isNameChar rest in w : names more
    isNameChar c = isAlphaNum c || c == '_'
    -- (a quote outside a comment)
    hasLiteral text = case text of
        '/' : '/' : more -> hasLiteral (dropWhile (/= '\n') more)
        '"' : _ -> True
        _ : more -> hasLiteral more
        [] -> False

-- The MIR of a program that passes every check
compileSource :: String -> Result M.Program String
compileSource = compileWith True

compileWith :: Bool -> String -> Result M.Program String
compileWith reserving source =
    parseSourceWith reserving source `bindResult` \stmts ->
        stage "Validation failed: " (elaborate stmts) `bindResult` \elaborated ->
            stage "Lowering failed: " (lowerElaborated elaborated) `bindResult` \program ->
                stage "Validation failed: " (validateProgram program) `bindResult` \_ ->
                    Ok program

-- The MIR of a program that passes every check, with who owns each value made explicit (MirOwnership), for native code
ownedSource :: String -> Result M.Program String
ownedSource source =
    compileSource source `bindResult` \program ->
        let owned = insertOwnership (nativeProgram program)
         in stage "Ownership failed: " (verifyProgram owned) `bindResult` \_ -> Ok owned

-- The LLVM IR of a program that passes every check
llvmSource :: String -> Result String String
llvmSource source = compileSource source `bindResult` \program -> stage "Native code failed: " (emitProgram (nativeProgram program))

-- The program that native code is made of: a validated program with each list made of the library's struct (see MirLists)
nativeProgram :: M.Program -> M.Program
nativeProgram = lowerLists listLibrary

-- The library, compiled and validated once
listLibrary :: M.Program
listLibrary = case compileWith False listsSource of
    Ok program -> program
    Error e -> error ("lib/lists.tersus does not compile: " ++ e)

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
