module Modules
    ( ModuleIdentity (..)
    , rootModuleIdentity
    , fileModuleIdentity
    , canonicalPrefix
    , canonicalName
    , declarationNames
    , canonicalizeDeclarations
    ) where

import Data.List (intercalate, isPrefixOf, stripPrefix)
import qualified Data.Set as Set

import TersusTypes

data ModuleIdentity = ModuleIdentity
    { identityPackageDir :: FilePath
    , identityModuleDir :: FilePath
    , identityFile :: FilePath
    , identityIsRoot :: Bool
    }
    deriving (Eq, Show)

rootModuleIdentity :: FilePath -> FilePath -> ModuleIdentity
rootModuleIdentity packageDir file = ModuleIdentity packageDir packageDir file True

fileModuleIdentity :: FilePath -> FilePath -> FilePath -> ModuleIdentity
fileModuleIdentity packageDir moduleDir file = ModuleIdentity packageDir moduleDir file False

pathSegments :: FilePath -> [String]
pathSegments path =
    [ segment
    | segment <- split '/' path >>= split '\\'
    , segment /= "" && segment /= "."
    ]
  where
    split sep text = case break (== sep) text of
        (chunk, _ : rest) -> chunk : split sep rest
        (chunk, []) -> [chunk]

fileStem :: FilePath -> String
fileStem file = case pathSegments file of
    [] -> ""
    segments -> takeWhile (/= '.') (last segments)

canonicalPrefix :: ModuleIdentity -> Maybe String
canonicalPrefix identity
    | identityIsRoot identity = Nothing
    | otherwise =
        Just
            ( intercalate
                "$"
                ( pathSegments (identityPackageDir identity)
                    ++ pathSegments (identityModuleDir identity)
                    ++ [fileStem (identityFile identity)]
                )
            )

canonicalName :: ModuleIdentity -> Name -> Name
canonicalName identity local = case canonicalPrefix identity of
    Nothing -> local
    Just prefix -> prefix ++ "$" ++ local

declarationNames :: [Statement] -> [Name]
declarationNames = concatMap top
  where
    top stmt = case stmt of
        StructDef name _ _ _ -> [name]
        EnumDef name variants -> name : map fst variants
        TraitDef name _ _ -> [name]
        Assign name (Val VFunct{}) -> [name]
        BoundedDef _ inner -> top inner
        AxiomDef name _ _ _ -> [name]
        ProofDef name _ _ _ _ -> [name]
        ImplDef _ _ _ _ _ functions -> concatMap top functions
        _ -> []

canonicalizeDeclarations :: ModuleIdentity -> [Statement] -> [Statement]
canonicalizeDeclarations identity statements
    | identityIsRoot identity = statements
    | otherwise = map renameStatement statements
  where
    locals = Set.fromList [name | name <- declarationNames statements, '<' `notElem` name]
    canon name
        | Set.member name locals = canonicalName identity name
        | otherwise = name
    renameType ty = case ty of
        TNamed name -> TNamed (renameNamed name)
        TVariant name -> TVariant (renameVariant name)
        TList t -> TList (renameType t)
        TArrayOf t size -> TArrayOf (renameType t) size
        TBox t -> TBox (renameType t)
        TAddr t -> TAddr (renameType t)
        TBlock t -> TBlock (renameType t)
        TUninit t -> TUninit (renameType t)
        TRef t -> TRef (renameType t)
        TMutRef t -> TMutRef (renameType t)
        TFn args ret -> TFn (map renameType args) (renameType ret)
        TForall sizes types t -> TForall sizes types (renameType t)
        other -> other
    renameNamed name = case instanceOf name of
        Just (base, args) -> instanceName (canon base) (map renameArg args)
        Nothing -> canon name
    renameArg (ArgType t) = ArgType (renameType t)
    renameArg other = other
    renameVariant name =
        let segments = splitOn "::" name
         in case segments of
                owner : rest@(_ : _) | Set.member owner locals -> canonicalName identity owner ++ "::" ++ intercalate "::" rest
                _ -> name
    splitOn needle = go
      where
        go text
            | needle `isPrefixOf` text = "" : go (drop (length needle) text)
            | otherwise = case text of
                c : rest -> case go rest of
                    [] -> [[c]]
                    (chunk : chunks) -> (c : chunk) : chunks
                [] -> [[]]
    renameSignature (Signature params ret sizes types writes from) =
        Signature (map renameType params) (renameType ret) sizes types writes from
    renameFunction stmt = case stmt of
        Assign name (Val (VFunct params ins outs body exported)) ->
            Assign
                (renameAssignName name)
                (Val (VFunct params ins outs (renameBody body) exported))
        other -> renameStatement other
    renameAssignName name
        | Set.member name locals = canonicalName identity name
        | '<' `elem` name = renameImplFunction name
        | otherwise = name
    renameImplFunction name =
        let (inside, rest) = break (== '>') name
            function = drop 3 rest
            ownerAndTrait = drop 1 inside
         in case stripPrefix "" ownerAndTrait of
                _ -> case breakOn " as " ownerAndTrait of
                    Just (owner, trait) -> implFunctionName (renameNamed owner) (Just (canon trait)) function
                    Nothing -> implFunctionName (renameNamed ownerAndTrait) Nothing function
    breakOn needle = go ""
      where
        go acc text
            | needle `isPrefixOf` text = Just (reverse acc, drop (length needle) text)
            | otherwise = case text of
                c : rest -> go (c : acc) rest
                [] -> Nothing
    renameBody (NativeFunct signature termination body) = NativeFunct (renameSignature signature) termination body
    renameBody other = other
    renameStatement stmt = case stmt of
        StructDef name params fields invariant ->
            StructDef (canon name) params [(field, renameType ty) | (field, ty) <- fields] invariant
        EnumDef name variants ->
            EnumDef (canon name) [(renameVariant variant, [(field, renameType ty) | (field, ty) <- fields]) | (variant, fields) <- variants]
        TraitDef name params functions ->
            TraitDef (canon name) params [fn{traitFnSignature = renameSignature (traitFnSignature fn)} | fn <- functions]
        Assign{} -> renameFunction stmt
        BoundedDef bounds inner ->
            BoundedDef [(param, canon trait, map renameType args) | (param, trait, args) <- bounds] (renameFunction inner)
        AxiomDef name args ins outs -> AxiomDef (canon name) args ins outs
        ProofDef name args ins outs body -> ProofDef (canon name) args ins outs body
        ImplDef trait traitArgs typeName selfName bounds functions ->
            ImplDef
                (fmap canon trait)
                (map renameArg traitArgs)
                (renameNamed typeName)
                (renameNamed selfName)
                [(param, canon boundTrait, map renameType args) | (param, boundTrait, args) <- bounds]
                (map renameFunction functions)
        other -> other
