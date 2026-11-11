module LibParsed
    ( LibParsed (..)
    , libParsed
    , nativeLibParsed
    , libModules
    , libModuleNames
    , libPackageFiles
    , nativeStorageModules
    , statementsForLibModules
    , declsForLibModules
    , inlinedLibraryLength
    ) where

import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map

import ParsedFile (Decls, Import (..), ParsedFile (..), declsFromStatements, emptyDecls)
import ParserSeed (parseFileWith, parseImportPrefix, toolFailure)
import PreludeSource (libModules, nativeStorageModules, libPackageFiles)
import Syntax (Statement)

libModuleNames :: [String]
libModuleNames = [name | (name, _, _) <- libModules, name `notElem` nativeStorageModules]

data LibParsed = LibParsed
    { lpStatements :: Map.Map String [Statement]
    , lpDependencies :: Map.Map String [String]
    , lpOrder :: [String]
    , lpDecls :: Decls
    }

-- The native parser itself needs these modules: stay below its bootstrap
-- boundary, and do not force native helper parsing for a user-library request.
libParsed :: Either String LibParsed
libParsed = parseLibModules libModuleNames (LibParsed Map.empty Map.empty [] emptyDecls)

nativeLibParsed :: Either String LibParsed
nativeLibParsed = libParsed >>= parseLibModules nativeStorageModules

parseLibModules :: [String] -> LibParsed -> Either String LibParsed
parseLibModules names initial = foldl next (Right initial) [modu | modu@(name, _, _) <- libModules, name `elem` names]
  where
    next failed@(Left _) _ = failed
    next (Right parsed) (name, _, text) = do
        imports <- parseImportPrefix text
        deps <- mapM dependency imports
        case [dep | dep <- deps, dep `notElem` lpOrder parsed] of
            dep : _ -> Left ("lib module " ++ name ++ " imports " ++ dep ++ " before it is available")
            [] -> do
                let closure pending done = case pending of
                        [] -> done
                        dep : rest | dep `elem` done -> closure rest done
                        dep : rest -> closure (Map.findWithDefault [] dep (lpDependencies parsed) ++ rest) (dep : done)
                    declarations = declsForLibModules parsed (closure deps [])
                case parseFileWith declarations text of
                    Left err | toolFailure err -> Left err
                             | otherwise -> Left ("Parse error in the " ++ name ++ " library: " ++ err)
                    Right (ParsedFile _ stmts, _) ->
                        let updated = parsed
                                { lpStatements = Map.insert name stmts (lpStatements parsed)
                                , lpDependencies = Map.insert name deps (lpDependencies parsed)
                                , lpOrder = lpOrder parsed ++ [name]
                                }
                         in Right updated{lpDecls = declsForLibModules updated libModuleNames}
    dependency imp = case (importPath imp, importAlias imp, importNames imp) of
        (["tersuslib", name], Nothing, Nothing) -> Right name
        _ -> Left ("compiler library import must name a tersuslib module: " ++ show imp)

statementsForLibModules :: LibParsed -> [String] -> [Statement]
statementsForLibModules parsed names = concat [Map.findWithDefault [] name (lpStatements parsed) | name <- lpOrder parsed, name `elem` names]

declsForLibModules :: LibParsed -> [String] -> Decls
declsForLibModules parsed names = declsFromStatements emptyDecls (statementsForLibModules parsed names)

-- How many of a program's first statements are compiler libraries put in front of it as they are (as
-- SourceParse.parseWithEqualityWith does), each library in the order the libraries are parsed in
inlinedLibraryLength :: [Statement] -> Int
inlinedLibraryLength stmts = case libParsed of
    Left _ -> 0
    Right parsed -> strip stmts [Map.findWithDefault [] name (lpStatements parsed) | name <- lpOrder parsed]
  where
    strip rest (library : more)
        | not (null library) && library `isPrefixOf` rest = length library + strip (drop (length library) rest) more
        | otherwise = strip rest more
    strip _ [] = 0
