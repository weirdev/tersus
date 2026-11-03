module LibParsed
    ( LibParsed (..)
    , libParsed
    , libModules
    , libModuleNames
    , statementsForLibModules
    , declsForLibModules
    ) where

import qualified Data.Map.Strict as Map

import Parse (Decls, ParsedFile (..), declsFromStatements, emptyDecls, parseFileWith)
import PreludeSource (cloneSource, eqSource, mapSource, preludeSource, setSource, stringSource, typesSource)
import Syntax (Statement)

-- The compiler libraries (the texts of PreludeSource) parsed once:
-- every consumer of the libraries' parsed form -- the parse-time seed of
-- Modules, the probe and prepend of Compile, and the lib package that
-- LibPackage compiles -- derives what it needs from this one parse. The
-- import lines below exist only in the in-memory copies the parse reads,
-- so the embedded texts, and with them emitterHash, are unchanged.

-- (module name, the display name Compile.librariesFor selects by, text,
-- the lib modules it imports)
libModules :: [(String, String, String, [String])]
libModules =
    [ ("types", "the list and Box types", typesSource, [])
    , ("eq", "the equality library", eqSource, [])
    , ("clone", "the clone library", cloneSource, [])
    , ("prelude", "the prelude", preludeSource, ["clone"])
    , ("string", "the string library", stringSource, ["prelude", "eq", "clone"])
    , ("map", "the map library", mapSource, ["prelude", "eq", "clone"])
    , ("set", "the set library", setSource, ["map", "prelude", "eq", "clone"])
    ]

libModuleNames :: [String]
libModuleNames = [name | (name, _, _, _) <- libModules]

-- The order the texts are parsed in (each after the ones whose
-- declarations its own text is read with), which is also the order
-- librariesFor puts the libraries in front of a program.
libParseOrder :: [String]
libParseOrder = ["types", "clone", "eq", "prelude", "string", "map", "set"]

-- The imports share the first line of the text (a comment in every lib
-- file), so the reading of the library's own text is the one it has
-- without them.
libSourceWithImports :: (String, String, String, [String]) -> String
libSourceWithImports (_, _, text, deps) = concat ["import tersuslib::" ++ dep ++ "; " | dep <- deps] ++ text

data LibParsed = LibParsed
    { lpStatements :: Map.Map String [Statement]
    , lpDecls :: Decls
    }

-- The libraries are read without the places of their statements, as
-- they were when a program was read with the library texts in front of
-- it: a library statement's place is not a place of the program, and
-- where the libraries stand in front of one (Compile's textual prepend)
-- the last library place must not become the place of the program's own
-- statements that follow it.
-- This parse is the bootstrap boundary: use Parse, never TersusParser or
-- Pipeline. Building the native parser itself needs these libraries, so
-- selecting the production parser here would create a builtin dependency cycle.
libParsed :: Either String LibParsed
libParsed = go libParseOrder emptyDecls Map.empty
  where
    go [] decls statements = Right (LibParsed statements decls)
    go (name : rest) decls statements = case [modu | modu@(candidate, _, _, _) <- libModules, candidate == name] of
        modu : _ -> case parseFileWith decls (libSourceWithImports modu) of
            Left err -> Left ("Parse error in the " ++ name ++ " library: " ++ show err)
            Right (ParsedFile _ stmts, decls') -> go rest decls' (Map.insert name stmts statements)
        [] -> Left ("internal: no lib module named " ++ name)

-- The parsed statements of the named lib modules, in the order
-- librariesFor puts the libraries in front of a program.
statementsForLibModules :: LibParsed -> [String] -> [Statement]
statementsForLibModules parsed names = concat [Map.findWithDefault [] name (lpStatements parsed) | name <- libParseOrder, name `elem` names]

-- The declarations the named lib modules make, as a program read with
-- them in front of it accumulates them.
declsForLibModules :: LibParsed -> [String] -> Decls
declsForLibModules parsed names = declsFromStatements emptyDecls (statementsForLibModules parsed names)
