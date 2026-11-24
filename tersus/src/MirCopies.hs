module MirCopies
    ( copyName
    , isCopyName
    , opaqueKey
    , boundCallParts
    , genericKey
    , coveredKey
    , isStubName
    , withoutGeneric
    , contractSuffix
    , proofPackElement
    ) where

import Data.List (intercalate, isPrefixOf, stripPrefix)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Mir
import Syntax (parseImplCheckName)
import Types (Name, Size (..), Storage (..), Type (..), Variable, baseNameOf, listElement, renderTypeForName, tupleGeneric)

-- The name of a copy that no reference wrote (one made for a copy, from a body with type parameters)
copyName :: Name -> [Type] -> [Integer] -> Name
copyName f tys sizes = f ++ "[" ++ intercalate ", " (map renderTypeForName tys ++ map show sizes) ++ "]"

-- The entry of a copy's environment that marks a local opaque to its proofs (no program writes a name with `$`)
opaqueKey :: Local -> Name
opaqueKey (Local n) = "$opaque " ++ show n

-- Whether a function is a copy of a function with bounds (or lifted out of one), by the naming scheme copyName and the
-- elaborator's Instance names share (no name a program writes has a `[`), and not the check function of an impl
isCopyName :: Name -> Bool
isCopyName name = '[' `elem` name && parseImplCheckName name == Nothing

-- `<$param T as Tr>::g` as the parameter, the trait and the function
boundCallParts :: Name -> Maybe (Variable, Name, Name)
boundCallParts name = do
    rest <- stripPrefix "<$param " name
    let (p, afterP) = breakOn " as " rest
    afterAs <- stripPrefix " as " afterP
    let (trait, afterTrait) = breakOn ">::" afterAs
    function <- stripPrefix ">::" afterTrait
    if null p || null trait || null function then Nothing else Just (p, trait, function)
  where
    breakOn pat text = go "" text
      where
        go acc rest
            | pat `isPrefixOf` rest = (reverse acc, rest)
            | otherwise = case rest of
                c : more -> go (c : acc) more
                [] -> (reverse acc, [])

-- The marks of a function the validator checks generically and of a copy it does not check (no name a program writes has `$`)
genericKey, coveredKey :: Name
genericKey = "$generic"
coveredKey = "$covered"

isStubName :: Name -> Bool
isStubName name = case parseImplCheckName name of
    Just (_, "$Self", _) -> True
    _ -> False

mapEnvs :: (Env -> Env) -> Function -> Function
mapEnvs f fn = fn{fnSpec = completeSpec (fnSpec fn), fnBlocks = Map.map completeBlock (fnBlocks fn)}
  where
    completeBlock (BasicBlock stmts term) = BasicBlock (map completeStatement stmts) term
    completeStatement (Ghost e g) = Ghost (f e) g
    completeStatement other = other
    completeSpec spec = spec{specEnv = f (specEnv spec), specLoops = Map.map (\loop -> loop{loopEnv = f (loopEnv loop)}) (specLoops spec)}

contractSuffix :: String
contractSuffix = "$contract"

packConsName :: Name
packConsName = "<$packcons>"

packSliceName :: Name
packSliceName = "<$packslice>"

-- A validated program without what only the validator reads: the generic bodies, the stubs and their markers, and the
-- marks on the copies
withoutGeneric :: Program -> Program
withoutGeneric program =
    completeInstances program{progTypes = Map.filterWithKey (\name _ -> not (derived name)) (progTypes program), progFunctions = Map.map strip kept, progMain = strip (progMain program)}
  where
    derived name =
        let base = baseNameOf name
         in base /= name && maybe False (const True) (maybe (tupleGeneric base) Just (Map.lookup base (progGenerics program)))
    validatorOnly fn = Map.member genericKey (specEnv (fnSpec fn)) || isStubName (fnName fn) || fnName fn `elem` [packSliceName, packConsName]
    kept = Map.filter (not . validatorOnly) (progFunctions program)
    goneNames = Map.keysSet (Map.filter validatorOnly (progFunctions program))
    gone n = Set.member n goneNames
    strip fn = mapEnvs (Map.filterWithKey (\k o -> k /= coveredKey && case o of Const (CFn n) -> not (gone n); _ -> True)) fn{fnBlocks = Map.map block (fnBlocks fn)}
    block (BasicBlock ss t) = BasicBlock (filter (not . marker) ss) t
    marker st = case st of
        Ghost _ (GhostFunction n _ _) -> gone n
        _ -> False

proofPackElement :: Storage -> Type -> Maybe Variable
proofPackElement storage ty = case ty of
    TArrayOf (TParam pack) SizeAny | null (storageList storage), ".." `isPrefixOf` pack -> Just pack
    _ -> case listElement storage ty of
        Just (TParam pack) | ".." `isPrefixOf` pack -> Just pack
        _ -> Nothing
