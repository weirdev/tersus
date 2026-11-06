module MirOwnership
    ( Role (..)
    , roles
    , isProjection
    , operandLocal
    ) where

import Mir

data Role = Read | Consume
    deriving (Eq)

roles :: Rvalue -> [(Operand, Role)]
roles rv = case rv of
    Use o -> [(o, Consume)]
    BinaryOp _ a b -> [(a, Read), (b, Read)]
    ListOp Push [l, x] -> [(l, Consume), (x, Consume)]
    ListOp Pop [l] -> [(l, Consume)]
    ListOp FromList [l] -> [(l, Consume)]
    ListOp Set [l, i, x] -> [(l, Consume), (i, Read), (x, Consume)]
    ListOp AddrWrite (p : i : x : rest) -> [(p, Read), (i, Read), (x, Consume)] ++ [(b, Consume) | b <- rest]
    ListOp AddrDropValue [p, i, b] -> [(p, Read), (i, Read), (b, Consume)]
    ListOp AddrDropRange [p, i, n, b] -> [(p, Read), (i, Read), (n, Read), (b, Consume)]
    ListOp AddrFree [p, b] -> [(p, Read), (b, Consume)]
    ListOp op (b : rest) | op `elem` [BlockTaken, BlockResized, BlockSplitHi, BlockCast] -> (b, Consume) : [(o, Read) | o <- rest]
    ListOp BlockJoin os -> [(o, Consume) | o <- os]
    ListOp op [u] | op `elem` [UninitNew, UninitTake, UninitDiscard] -> [(u, Consume)]
    ListOp _ os -> [(o, Read) | o <- os]
    MakeList os -> [(o, Consume) | o <- os]
    MakeBox o -> [(o, Consume)]
    Unbox o -> [(o, Consume)]
    Unsize o -> [(o, Consume)]
    MakeData _ fields -> [(o, Consume) | (_, o) <- fields]
    ReadField o _ _ -> [(o, Read)]
    IsVariant o _ -> [(o, Read)]
    AsVariant o _ -> [(o, Consume)]
    CopyOf o -> [(o, Read)]
    TakeField l _ _ -> [(Copy l, Read)]
    Borrow root steps _ -> (Copy root, Read) : [(o, Read) | RefIndex o <- steps]
    Deref o -> [(o, Read)]

isProjection :: Rvalue -> Bool
isProjection (ListOp op _) = op `elem` [First, Last, Get, AddrGet, UninitGet]
isProjection ReadField{} = True
isProjection Deref{} = True
isProjection _ = False

operandLocal :: Operand -> Maybe Local
operandLocal (Copy l) = Just l
operandLocal (Move l) = Just l
operandLocal _ = Nothing
