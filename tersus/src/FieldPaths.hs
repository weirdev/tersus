{-# LANGUAGE PatternSynonyms #-}

-- Where a value of one type can be inside a value of another, by the declared types alone: the one authority the move
-- check (MirMoves) and the validator's bridge (SelfHostedMir) use to tell the place a result under `from` is to, and the
-- places a field of references can be given.
module FieldPaths (fieldPaths, mayBe) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Mir (TypeDecl (..))
import Types (Name, Type (..), Variable, baseNameOf, instanceName, pattern TBox, pattern TList)

-- Every path of struct fields (struct, field) from a value of type `ty` to a part whose type may be `target`, or Nothing
-- when that list cannot be known to be complete: a type that is not resolved, an instance met again on the way, or an
-- element (of a List, Box, Array or Uninit) or an enum's variant that may hold a `target`. With `throughReferences`, a
-- reference whose referent may be or hold a `target` also makes it incomplete (what it is to can be such a place too,
-- outside the value); without, a reference is a word that is not a `target` place.
fieldPaths :: Bool -> Map.Map Name TypeDecl -> Type -> Type -> Maybe [[(Name, Variable)]]
fieldPaths throughReferences types target = go Set.empty
  where
    go seen ty
        | mayBe types ty target = ([] :) <$> inside seen ty
        | otherwise = inside seen ty
    inside seen ty = case ty of
        TInt -> Just []
        TByte -> Just []
        TBool -> Just []
        TWord _ _ -> Just []
        TFn _ _ -> Just []
        TRef referent -> word seen referent
        TMutRef referent -> word seen referent
        TArrayOf element _ -> sealed seen element
        TUninit element -> sealed seen element
        _ | ty `Set.member` seen -> Nothing
        TList element -> sealed (Set.insert ty seen) element
        TBox element -> sealed (Set.insert ty seen) element
        TNamed base args -> case Map.lookup (instanceName base args) types of
            Just (StructDecl fields) -> concat <$> mapM (\(field, fieldTy) -> map ((instanceName base args, field) :) <$> go (Set.insert ty seen) fieldTy) fields
            Just (EnumDecl variants) -> sealedAll (Set.insert ty seen) (concatMap snd variants)
            Nothing -> Nothing
        TVariant variant -> case [fields | EnumDecl variants <- Map.elems types, (other, fields) <- variants, other == variant] of
            [fields] -> sealedAll (Set.insert ty seen) fields
            _ -> Nothing
        _ -> Nothing
    -- (a part reached by no struct field: nothing in it may be a `target`)
    sealed seen ty = case go seen ty of
        Just [] -> Just []
        _ -> Nothing
    sealedAll seen fields = concat <$> mapM (sealed seen . snd) fields
    word seen referent
        | throughReferences = sealed seen referent
        | otherwise = Just []

-- Whether a reference to the one may be to a place of the other: a variant is its enum's type too, sizes, qualifiers and
-- the arguments of one type constructor (List and Box included) may unify, any two function types may, and a type
-- parameter may be anything
mayBe :: Map.Map Name TypeDecl -> Type -> Type -> Bool
mayBe types a b = case (a, b) of
    _ | a == b -> True
    (TArrayOf x _, TArrayOf y _) -> mayBe types x y
    (TRef x, TRef y) -> mayBe types x y
    (TRef x, TMutRef y) -> mayBe types x y
    (TMutRef x, TRef y) -> mayBe types x y
    (TMutRef x, TMutRef y) -> mayBe types x y
    (TNamed x _, TNamed y _) | baseNameOf x == baseNameOf y -> True
    (TFn _ _, TFn _ _) -> True
    (TForall{}, _) -> True
    (_, TForall{}) -> True
    (TAddr _, TAddr _) -> True
    (TBlock _, TBlock _) -> True
    (TUninit x, TUninit y) -> mayBe types x y
    (TVariant v, other) -> variant v other
    (other, TVariant v) -> variant v other
    (TParam _, _) -> True
    (_, TParam _) -> True
    (TVar _, _) -> True
    (_, TVar _) -> True
    _ -> False
  where
    variant v other = case other of
        TVariant w -> enumsOf v == enumsOf w
        TNamed base args -> instanceName base args `elem` enumsOf v || baseNameOf base `elem` map baseNameOf (enumsOf v)
        TParam _ -> True
        TVar _ -> True
        _ -> False
    enumsOf v = [name | (name, EnumDecl variants) <- Map.toList types, v `elem` map fst variants]
