module ParsedFile
    ( Decls (..)
    , Import (..)
    , ParsedFile (..)
    , emptyDecls
    , declsFromStatements
    , locating
    , renderPath
    , splitPath
    ) where

import qualified Data.Map as Map
import Data.List (intercalate)
import Syntax (Statement (..), Expression (..), Value (..))
import Types (Name, Type, Variable)

data Decls = Decls
    { declCtors :: Map.Map Name [Variable]
    , declTypes :: Map.Map Name [Name]
    , declSelf :: Maybe Name
    , declSelfType :: Maybe Type
    , declTypeParams :: [Name]
    , declGenerics :: Map.Map Name [Variable]
    , declImplParams :: [Variable]
    , declOwnClone :: Bool
    , declLocate :: Bool
    , declFieldTypes :: Map.Map Name [(Variable, Type)]
    }
    deriving (Show, Eq)

emptyDecls :: Decls
emptyDecls = Decls Map.empty Map.empty Nothing Nothing [] Map.empty [] False False Map.empty

declsFromStatements :: Decls -> [Statement] -> Decls
declsFromStatements = foldl step
  where
    step d stmt = case stmt of
        StructDef name params fields _ ->
            d
                { declCtors = Map.insert name (map fst fields) (shadowedCtors name d)
                , declTypes = Map.insert name [name] (declTypes d)
                , declFieldTypes = Map.insert name fields (declFieldTypes d)
                , declGenerics = if null params then Map.delete name (declGenerics d) else Map.insert name params (declGenerics d)
                }
        EnumDef name variants ->
            d
                { declCtors = foldr (\(v, fields) m -> Map.insert v (map fst fields) m) (shadowedCtors name d) variants
                , declFieldTypes = foldr (\(v, fields) m -> Map.insert v fields m) (declFieldTypes d) variants
                , declTypes = Map.insert name (map fst variants) (declTypes d)
                , declGenerics = Map.delete name (declGenerics d)
                }
        TraitDef name params _ ->
            d
                { declCtors = shadowedCtors name d
                , declTypes = Map.delete name (declTypes d)
                , declGenerics = if null params then Map.delete name (declGenerics d) else Map.insert name params (declGenerics d)
                }
        BoundedDef _ inner -> step d inner
        Assign name (Val VFunct{}) | name == "clone" -> d{declOwnClone = True}
        _ -> d
    shadowedCtors name d = foldr Map.delete (declCtors d) (name : sourceVariants name (Map.findWithDefault [] name (declTypes d)))
    sourceVariants owner = map (\variant -> if '$' `elem` variant then owner ++ dropWhile (/= ':') variant else variant)

data Import = Import
    { importPath :: [Name]
    , importAlias :: Maybe Name
    , importNames :: Maybe [Name]
    , importLine :: Int
    , importColumn :: Int
    }
    deriving (Show, Eq, Ord)

data ParsedFile = ParsedFile
    { fileImports :: [Import]
    , fileBody :: [Statement]
    }
    deriving (Show, Eq, Ord)

locating :: Decls -> Decls
locating decls = decls{declLocate = True}

renderPath :: [Name] -> Name
renderPath = intercalate "::"

splitPath :: Name -> [Name]
splitPath name = case break (== ':') name of
    (segment, ':' : ':' : rest) -> segment : splitPath rest
    _ -> [name]
