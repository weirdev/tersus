module Compile
    ( parseSource
    , parseWithEquality
    , lowerSource
    , lowerStatements
    ) where

import Data.Char (isAlphaNum)

import qualified Mir as M
import MirLower (lowerElaborated, lowerLibrary)
import Parse (emptyDecls, locating, parseStatementBlockWith)
import PreludeSource (cloneSource, eqSource, mapSource, preludeSource, setSource, stringSource)
import Syntax (Expression (..), Statement (..), Value (..))
import TypeCheck (elaborate)
import Utils

-- The front of the pipeline of Pipeline, split out so that MirHousekeeping can compile the checker and the
-- eraser written in Tersus without the pipeline that runs them: a program is parsed (with the libraries in
-- front of it), type checked by `elaborate`, and lowered to the MIR. What the lowered program then goes
-- through (the check of the MIR and the erasure of its ghosts, both written in Tersus and run by
-- MirHousekeeping, and the validation of MirValidate) is composed by Pipeline, so nothing here calls it.

parseSource :: String -> Result [Statement] String
parseSource source = parseSourceWith True source

-- A program with the equality library in front of it (unless it declares a trait Eq), as `=` on any type but a word needs, and with no
-- other library: how the tests of the language read a program
parseWithEquality :: String -> Either String [Statement]
parseWithEquality source = case [text | (name, text) <- libraries source, name `elem` ["the clone library", "the equality library"]] of
    [] -> either (Left . show) (Right . fst) (parseStatementBlockWith emptyDecls source)
    texts -> case readLibs emptyDecls texts of
        Left err -> Left err
        Right (library, declared) -> either (Left . show) (Right . (library ++) . fst) (parseStatementBlockWith declared source)
  where
    readLibs declared [] = Right ([], declared)
    readLibs declared (text : more) = case parseStatementBlockWith declared text of
        Left err -> Left ("Parse error in a library: " ++ show err)
        Right (library, declared') -> case readLibs declared' more of
            Left err -> Left err
            Right (rest, final) -> Right (library ++ rest, final)

-- (the library of lists is the one program that may use the names that a program may not)
parseSourceWith :: Bool -> String -> Result [Statement] String
parseSourceWith reserving source = case libraries source of
    [] -> case parseStatementBlockWith (locating emptyDecls) source of
        Left err -> Error ("Parse error: " ++ show err)
        Right (stmts, _) -> checked stmts
    texts -> case readLibraries texts emptyDecls of
        Left err -> Error err
        Right (library, declared) -> case parseStatementBlockWith (locating declared) source of
            Left err -> Error ("Parse error: " ++ show err)
            Right (stmts, _) -> checked stmts `bindResult` \stmts' -> Ok (library ++ stmts')
  where
    readLibraries [] declared = Right ([], declared)
    readLibraries ((name, text) : more) declared = case parseStatementBlockWith declared text of
        Left err -> Left ("Parse error in " ++ name ++ ": " ++ show err)
        Right (stmts, declared') -> fmap (\(rest, final) -> (stmts ++ rest, final)) (readLibraries more declared')
    checked stmts = if reserving then maybe (Ok stmts) (\name -> Error ("Type error: " ++ name ++ " is reserved: native code makes a list of the struct StdList and the functions stdList... of lib/lists.tersus, and a Box of the struct StdBox and the functions stdBox... of lib/box.tersus, so a program does not declare names like them")) (reservedName stmts) else Ok stmts

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
    reserved name = name `elem` ["StdList", "StdBox"] || take 7 name == "stdList" || take 6 name == "stdBox"

-- The libraries that a program has in front of it, in order, unless it declares their names itself, so a program that has a `Vec` of its own is
-- unchanged: lib/eq.tersus (the trait `Eq` that `=` calls, whose impls are made only for the types a program compares), lib/prelude.tersus (the traits `Sequence`, `Growable`, `Clone`, `Copy`, `Drop`, `Deref` and `Hash`) if it mentions any of them (or
-- `hashCombine`), lib/string.tersus (the struct `String` that a string literal is a value of, which needs the traits) if it mentions `String` or
-- has a literal, lib/map.tersus (the struct `HashMap`) if it mentions `HashMap`, and lib/set.tersus (the struct `HashSet`,
-- which is made of a map) if it mentions `HashSet`
libraries :: String -> [(String, String)]
libraries source = [("the clone library", cloneSource) | not (declares ["Clone"])] ++ [("the equality library", eqSource) | not (declares ["Eq"])] ++ [("the prelude", preludeSource) | prelude] ++ [("the string library", stringSource) | strings] ++ [("the map library", mapSource) | maps] ++ [("the set library", setSource) | sets]
  where
    code = withoutText source
    ws = names code
    ws' = zip ws (drop 1 ws)
    declares candidates = any (\(keyword, name) -> keyword `elem` ["struct", "enum", "trait"] && name `elem` candidates) ws'
    preludeFree = not (declares ["Sequence", "Growable", "Clone", "Copy", "Drop", "Deref", "Hash"])
    strings = preludeFree && not (declares ["String"]) && ("String" `elem` ws || '"' `elem` code)
    maps = preludeFree && not (declares ["HashMap"]) && ("HashMap" `elem` ws || sets)
    sets = preludeFree && not (declares ["HashSet"]) && "HashSet" `elem` ws
    prelude = preludeFree && (strings || maps || sets || any (`elem` ws) ["Sequence", "Growable", "Clone", "Copy", "Drop", "Deref", "Hash", "hashCombine"])
    -- (the names in a text: runs of letters, digits and underscores)
    names text = case dropWhile (not . isNameChar) text of
        "" -> []
        rest -> let (w, more) = span isNameChar rest in w : names more
    isNameChar c = isAlphaNum c || c == '_'
    -- (the program without its comments and the text of its literals, which are `""`: what a name there says is not the program's)
    withoutText text = case text of
        '/' : '/' : more -> withoutText (dropWhile (/= '\n') more)
        '"' : more -> '"' : '"' : withoutText (afterString more)
        c : more -> c : withoutText more
        [] -> []
    afterString text = case text of
        '\\' : _ : more -> afterString more
        '"' : more -> more
        '\n' : more -> '\n' : more
        _ : more -> afterString more
        [] -> []

-- A program lowered to the MIR, before it is checked, its ghosts erased or it is validated: the stages
-- Pipeline adds on top of this. Errors name the stage that refused the program, as the command line prints them.
lowerSource :: Bool -> String -> Result M.Program String
lowerSource reserving source =
    parseSourceWith reserving source `bindResult` \stmts ->
        stage "Validation failed: " (elaborate stmts) `bindResult` \elaborated ->
            stage "Lowering failed: " ((if reserving then lowerElaborated else lowerLibrary) elaborated)

-- The same for a program given as statements
lowerStatements :: [Statement] -> Result M.Program String
lowerStatements stmts = elaborate stmts `bindResult` lowerElaborated

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
