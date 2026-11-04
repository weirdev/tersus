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
    ) where

import qualified Data.Map.Strict as Map

import Parse (Decls, Import (..), ParsedFile (..), declsFromStatements, emptyDecls, parseFileWith, parseImportPrefix)
import PreludeSource (boxSource, cloneSource, eqSource, listsSource, mapSource, preludeSource, setSource, stringSource, typesSource)
import Syntax (Statement)

-- Compiler-owned modules retain bare names.
libModules :: [(String, String, String)]
libModules =
    [ ("types", "the list and Box types", typesSource)
    , ("clone", "the clone library", cloneSource)
    , ("eq", "the equality library", eqSource)
    , ("prelude", "the prelude", preludeSource)
    , ("string", "the string library", stringSource)
    , ("map", "the map library", mapSource)
    , ("set", "the set library", setSource)
    , ("lists", "the native list helpers", listsSource)
    , ("box", "the native Box helpers", boxSource)
    ]

nativeStorageModules :: [String]
nativeStorageModules = ["lists", "box"]

libModuleNames :: [String]
libModuleNames = [name | (name, _, _) <- libModules, name `notElem` nativeStorageModules]

libPackageFiles :: [(FilePath, String)]
libPackageFiles = ("tersuslib/package.tersus", "") : [("tersuslib/" ++ name ++ "/" ++ name ++ ".tersus", text) | (name, _, text) <- libModules]

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
        imports <- either (Left . show) Right (parseImportPrefix text)
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
                    Left err -> Left ("Parse error in the " ++ name ++ " library: " ++ show err)
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
