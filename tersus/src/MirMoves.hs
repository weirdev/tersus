{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

module MirMoves
    ( checkMoves
    , checkMovesExcluding
    , finishLowered
    , checkSpawns
    , isCopyType
    , stripPositions
    , Role (..)
    , roles
    , isProjection
    , operandLocal
    , liveness
    ) where

import Control.Applicative ((<|>))
import Data.Char (isDigit)
import Data.List (foldl', intercalate, isPrefixOf, nub, tails, zip4)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust, listToMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import FieldPaths (fieldPaths)
import Mir
import Types (Arg (..), Name, Type (..), pattern TList, pattern TBox, Variable, baseNameOf, instanceFields, instanceName, renderTypeForName, tupleGeneric)
import Utils (Result (..))

-- A copy of a value is made where the program writes `clone(x)`, and nowhere else: a value that is not `Copy` is moved to where it
-- is wanted, and the local it came from holds nothing after. So a program cannot use it again, and this checks that it does not.
-- It runs on the MIR that lowering makes, before the program is validated (it is cheap, and a program that fails it has no meaning for
-- the passes after it).
--
-- What the check follows is a *place*: a local and the fields (or the elements of a list) that are followed from it. It keeps the
-- places that have been moved out, along every path, and reports:
--
--   * a use of a place after it was moved (or of a part of it, or of the whole it is a part of), along any path to the use;
--   * a move of an element of a list, which the list still holds: write `clone(get(l, i))`;
--   * a move of a parameter that is lent (`&T`), or of a part of one, which the caller still has;
--   * a place that an operation is lent (a lent argument of a call, or what a reference it is given is to) and
--     that the same operation moves, or a value that holds it or a part of it.
--
-- A field or an element that is read into a local (`row = get(rows, i)`, `l = t.left`) is a *view* of the place it comes from, so
-- reading it moves nothing, and moving it moves the place. A Copy value is copied wherever it is wanted and is never moved. A
-- value that a call or an operation makes is its own place and has nothing to do with the rest.

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

-- The Copy types are Int, Byte, Bool, functions, addresses, an array of a Copy type, a tuple of Copy types, and a struct or an enum that declares `impl Copy` (and
-- all of whose fields are Copy, for an instance of a struct with parameters). A list or a Box never is.
isCopyType :: Set Name -> Program -> Type -> Bool
isCopyType copies program = go (0 :: Int)
  where
    go depth ty
        | depth > 32 = False
        | otherwise = case ty of
            TInt -> True
            TByte -> True
            TWord _ _ -> True
            TBool -> True
            TFn{} -> True
            TFnContract{} -> True
            TBoxedClosure{} -> False
            TAddr _ -> True
            TUninit t -> not (ownsHeap program t) && go (depth + 1) t
            TArrayOf t _ -> go (depth + 1) t
            TRef _ -> True
            TNamed base args -> declared depth (instanceName base args)
            TVariant v -> maybe False (declared depth) (ownerOf program v)
            -- (an element of a pack, `..T#0`, is Copy when the pack is)
            TParam p -> parameterCopy (takeWhile (`notElem` "#@") p) `Set.member` copies
            _ -> False
    declared depth n =
        let base = baseNameOf n
         in (base `Set.member` copies || isJust (tupleGeneric base)) && fieldsCopy depth n
    fieldsCopy depth n = case Map.lookup n (progTypes program) of
        Just (StructDecl fields) -> all (go (depth + 1) . snd) fields
        Just (EnumDecl variants) -> all (go (depth + 1) . snd) (concatMap snd variants)
        Nothing -> True

-- Whether a value of the type owns something on the heap: a list or a Box, in it at any depth (before native code, a list is a list)
ownsHeap :: Program -> Type -> Bool
ownsHeap program = go Set.empty
  where
    go seen ty = case ty of
        TList _ -> True
        TBox _ -> True
        TArrayOf t _ -> go seen t
        TUninit t -> go seen t
        TNamed base args | Set.member (instanceName base args) seen -> False
        TNamed base args -> declared (Set.insert (instanceName base args) seen) (instanceName base args)
        TVariant v -> maybe False (declared seen) (ownerOf program v)
        _ -> False
    declared seen n = case Map.lookup n (progTypes program) of
        Just (StructDecl fields) -> any (go seen . snd) fields
        Just (EnumDecl variants) -> any (go seen . snd) (concatMap snd variants)
        Nothing -> False

-- Whether a copy of a value of the type would copy a value with a drop bitwise: it holds, at any depth (fields, variants, the
-- elements of a list, a Box, an array or an address), a struct or an enum with a drop and no Clone of its own. A look at such a
-- part is made in place (the ownership pass peeks it), so what it is a part of must not change before its last use. This is
-- `holdsOwnDrop` of lib/mir/ownership/common.tersus at the types of the program as written. A type parameter is taken not to be
-- one (taking it to be one refuses the elements of a variadic pack that a function reads into one name), so the copy of a generic
-- function for such a type is checked by the ownership pass alone, which applies the same rule at the types native code is made
-- of and refuses what this misses (testOwnership "the ownership pass's own refusals").
holdsDrop :: Cx -> Type -> Bool
holdsDrop cx
    | Set.null (cxDrops cx) = const False
    | otherwise = go Set.empty
  where
    program = cxProgram cx
    -- (an instance has a Clone of its own when its type has one and none of its type arguments holds a value with a drop and no
    -- Clone, which a Clone bounded by Clone on that argument could not clone: dropHolders in lib/mir/ownership/common.tersus)
    cloned seen base args = base `Set.member` cxCloned cx && not (any (go seen) [t | ArgType t <- args])
    go seen ty = case ty of
        TArrayOf t _ -> go seen t
        TUninit t -> go seen t
        TAddr t -> go seen t
        TNamed base args | cloned seen base args -> False
        TNamed base _ | base `Set.member` cxDrops cx -> True
        TNamed base args
            | instanceName base args `Set.member` seen -> False
            | otherwise -> case Map.lookup (instanceName base args) (progTypes program) of
                Just decl -> declared (Set.insert (instanceName base args) seen) decl
                Nothing -> any (go seen) [t | ArgType t <- args]
        TVariant v -> case ownerOf program v of
            -- (a variant of an instance with type arguments is taken to have no Clone of its own: its arguments are not at hand)
            Just n | baseNameOf n == n, cloned seen n [] -> False
            Just n | baseNameOf n `Set.member` cxDrops cx -> True
            Just n | Just decl <- Map.lookup n (progTypes program), n `Set.notMember` seen -> declared (Set.insert n seen) decl
            _ -> False
        _ -> False
    declared seen decl = case decl of
        StructDecl fields -> any (go seen . snd) fields
        EnumDecl variants -> any (go seen . snd) (concatMap snd variants)

-- The structs and enums with a Clone of their own (`<T as Clone>::clone`), which a copy of them calls
cloneBases :: Program -> Set Name
cloneBases program = Set.fromList [baseNameOf (takeWhile (/= ' ') (drop 1 name)) | name <- Map.keys (progFunctions program), " as Clone>::clone" `isInfixOf'` name, take 1 name == "<"]
  where
    isInfixOf' needle hay = any (needle `isPrefixOf`) (tails hay)

-- The place changes while a live local looks at a part of it that holds a value with a drop: that look is made in place
-- and cannot be copied
viewsDisturbed :: Cx -> Pos -> St -> [Local] -> String -> Place -> [String]
viewsDisturbed cx pos st except how place =
    [ message cx pos (describe cx place ++ " " ++ how ++ " here while " ++ describeLocal cx v ++ " still looks at " ++ describe cx (if overlaps place q then q else head ([owned o | o <- ownerPlaces q, overlaps place (owned o)] ++ [q])) ++ ", which holds a value with a drop and cannot be copied: use " ++ describeLocal cx v ++ " before that, or take the value apart")
    | (v, ps) <- Map.toList (stViews st)
    , v `notElem` except
    , v `Set.member` cxLiveNow cx
    , holdsDrop cx (typeOf cx v)
    , q <- Set.toList ps
    , overlaps place q || any (overlaps place . owned) (ownerPlaces q)
    ]
  where
    -- (a view taken through a reference, `(*r).x` or the result of a call `from` an argument, is of what the reference is to, for as
    -- long as the view is used, whether or not the reference still is: every place the reference may be to, its loan and the places
    -- carried with it (a result from several arguments, a reference read out of a holder), followed through reborrows and views)
    owned (root, steps) = (root, if isReference cx root then steps else filter (/= SDeref) steps)
    ownerPlaces = go (8 :: Int) Set.empty
      where
        go 0 _ q = [q]
        go n seen q@(root, steps)
            | root `Set.member` seen = [q]
            | isReference cx root, Just (target, _, _) <- Map.lookup root (stLoans st) =
                q : concat [go (n - 1) (Set.insert root seen) (r2, s2 ++ steps) | (r2, s2) <- nub (target : Map.findWithDefault [] root (stExtraLoans st) ++ maybe [] pure (Map.lookup root (stExact st)))]
            | Just vs <- Map.lookup root (stViews st), not (Set.null vs) = q : concat [go (n - 1) (Set.insert root seen) (r2, s2 ++ steps) | (r2, s2) <- Set.toList vs]
            | otherwise = [q]

-- How many statements give the local a value
definitionsOf :: Function -> Local -> Int
definitionsOf fn l = length ([() | l `elem` fnParams fn] ++ [() | BasicBlock stmts _ <- Map.elems (fnBlocks fn), Assign d _ <- stmts, d == l] ++ [() | BasicBlock _ (Call _ _ d _) <- Map.elems (fnBlocks fn), d == l])

-- A step from a value to a part of it: a field, an element of a list, the tag of an enum, or a slot of the memory a permission is for
data Step = SField Name String | SElem (Maybe Integer) | STag | SSlot | SDeref
    deriving (Eq, Ord)

type Place = (Local, [Step])

type Pos = Maybe (Int, Int)

-- Along the paths that reach a point: the places that may have been moved out (and where), and the places that a local is a view of
-- on every path (a local that is a view on one path and not on another is taken for a value of its own, so a move of it is not reported
-- as a move out of what it was a view of)
-- stMay holds the places a local may be a view of on some path (a local that is a view on one path and owns its value on another is in it),
-- which only decides whether a move is allowed: a move out of a list or out of a lent parameter on any path is an error.
--
-- stHeld holds the places that hold a permission (a Block, or the field or part of a value that is one) that may not have been used yet
-- on some path, with where they were given it. A permission is linear: it has to be used exactly once, by the operation that frees or
-- changes it, or by being given on (to a call, into a struct, returned). So one that is still held at a return is lost, and so is one
-- that is held by a local that is assigned again.
-- A loan: the place a reference local is to, whether it may update it, and where it was made (REFERENCES.md).
-- A loan is live at a point where its reference local may still be used (the liveness below), which is what
-- "the interval of a borrow" means here: past the last use of the reference, the place is free again.
type Loan = (Place, Bool, Pos)

-- stParents holds what a local's loans were taken from: the reference a reborrow is made through, the value a reference is read out of,
-- the values a value holding references was made of, the arguments a result is from. A parent is suspended while the local is live
-- (REFERENCES.md, Core rules).
-- stThrough holds, for a view read through a reference (`*r`, or a part of such a view), the references it may have been read through.
-- stShared holds the locals whose value may, on some path, be or hold what was reached through a shared reference or a parameter
-- lent to be read (sharedTransfer, MIR.md "Shared paths").
data St = St {stMoved :: Map Place (Pos, Maybe String), stViews :: Map Local (Set Place), stMay :: Map Local (Set Place), stHeld :: Map Place Pos, stLoans :: Map Local Loan, stExtraLoans :: Map Local [Place], stFieldLoans :: Map (Local, Variable) [Place], stConst :: Map Local Integer, stFnAlias :: Map Local Name, stParents :: Map Local [Local], stThrough :: Map Local (Set Local), stReborrowedThrough :: Map Local [Local], stExact :: Map Local Place, stShared :: Set Local}
    deriving (Eq)

emptySt :: St
emptySt = St Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Set.empty

joinSt :: St -> St -> St
joinSt a b = St (Map.union (stMoved a) (stMoved b)) (Map.intersectionWith Set.union (stViews a) (stViews b)) (Map.unionWith Set.union (stMay a) (stMay b)) (Map.union (stHeld a) (stHeld b)) (Map.union (stLoans a) (stLoans b)) extras (Map.unionWith unionPlaces (stFieldLoans a) (stFieldLoans b)) (Map.mapMaybe id (Map.intersectionWith (\x y -> if x == y then Just x else Nothing) (stConst a) (stConst b))) (Map.fromList [(k, v) | (k, v) <- Map.toList (stFnAlias a), Map.lookup k (stFnAlias b) == Just v]) (Map.unionWith unionPlaces (stParents a) (stParents b)) (Map.unionWith Set.union (stThrough a) (stThrough b)) (Map.mapMaybe id (Map.intersectionWith (\x y -> if x == y then Just x else Nothing) (stReborrowedThrough a) (stReborrowedThrough b))) (Map.mapMaybe id (Map.intersectionWith (\x y -> if x == y then Just x else Nothing) (stExact a) (stExact b))) (Set.union (stShared a) (stShared b))
  where
    -- (a reference the two branches leave to different places may be to either)
    alternatives = Map.fromListWith unionPlaces [(ref, [other]) | (ref, (place, _, _)) <- Map.toList (stLoans a), Just (other, _, _) <- [Map.lookup ref (stLoans b)], place /= other]
    extras = Map.unionWith unionPlaces (Map.unionWith unionPlaces (stExtraLoans a) (stExtraLoans b)) alternatives

-- (only what is new is appended, so that joining a state that is already in a join changes nothing: the fixpoint of
-- checkFunction skips a block whose predecessors' states have not changed)
unionPlaces :: Eq a => [a] -> [a] -> [a]
unionPlaces xs ys = xs ++ [y | y <- ys, y `notElem` xs]

sameShape :: St -> St -> Bool
sameShape a b = Map.keysSet (stMoved a) == Map.keysSet (stMoved b) && stViews a == stViews b && stMay a == stMay b && Map.keysSet (stHeld a) == Map.keysSet (stHeld b) && Map.map (\(place, mutable, _) -> (place, mutable)) (stLoans a) == Map.map (\(place, mutable, _) -> (place, mutable)) (stLoans b) && Map.map (Set.fromList) (stExtraLoans a) == Map.map (Set.fromList) (stExtraLoans b) && Map.map (Set.fromList) (stFieldLoans a) == Map.map (Set.fromList) (stFieldLoans b) && stParents a == stParents b && stThrough a == stThrough b && stReborrowedThrough a == stReborrowedThrough b && stExact a == stExact b && stShared a == stShared b

-- Every loan that freezes a place: a reference's own place, the other places a result that may be from
-- more than one parameter freezes (a call result: which of them it is is the callee's choice), and what a value that
-- holds references, borrowed or held by a loan, is to (carriedBy), which is never a place the loan is to
loanEntries :: Cx -> St -> [(Local, Place, Bool)]
loanEntries cx st = [(ref, place, mutable) | (ref, place, mutable, _) <- loanRows cx st]

-- The same, each with the holder whose reference field it is carried through (Nothing for the loan's own places). A
-- carried place is held for updating only through update references all the way (a loan of a holder for updating
-- does not make what its read references are to updatable)
loanRows :: Cx -> St -> [(Local, Place, Bool, Maybe Local)]
loanRows cx st = [row | (ref, place, mutable) <- direct, row <- (ref, place, mutable, Nothing) : [(ref, held, mutable && updating, Just holder) | (held, holder, updating) <- carriedBy cx st place]]
  where
    direct = [(ref, place, mutable) | (ref, (place, mutable, _)) <- Map.toList (stLoans st)] ++ [(ref, place, maybe (place `elem` carried) (\(_, mutable, _) -> mutable) (Map.lookup ref (stLoans st))) | (ref, places) <- Map.toList (stExtraLoans st), let carried = carriedUpdates st ref, place <- places]

-- What a place that holds references is to, through holders inside holders, each with the holder it is held by and
-- whether every holder on the way is to it through update references only (each route, as place, holder and mode,
-- reached once: the places the state knows are finite)
carriedBy :: Cx -> St -> Place -> [(Place, Local, Bool)]
carriedBy cx st start = go Set.empty (heldOf True start)
  where
    go _ [] = []
    go seen ((place, holder, updating) : rest)
        | (place, holder, updating) `Set.member` seen = go seen rest
        | otherwise = (place, holder, updating) : go (Set.insert (place, holder, updating) seen) (rest ++ heldOf updating place)
    heldOf updating place@(root, _) = [(held, root, updating && mutableHolderLoan cx st root held) | held <- heldPlaces place]
    heldPlaces place@(root, steps) = case steps of
        _ | Just ty <- placeType cx place, not (mayHoldReference (cxProgram cx) ty) -> []
        SField _ f : _ -> fromMaybe (loansOf root) (Map.lookup (root, f) (stFieldLoans st))
        _ -> loansOf root
    loansOf l = case Map.lookup l (stLoans st) of
        Just (place, _, _) -> place : Map.findWithDefault [] l (stExtraLoans st)
        Nothing -> Map.findWithDefault [] l (stExtraLoans st)

-- The places a value that holds references holds an update reference to: those of the update references it was made of,
-- directly or through the values that hold them
carriedUpdates :: St -> Local -> [Place]
carriedUpdates st holder = filter (`elem` Map.findWithDefault [] holder (stExtraLoans st)) (go (Set.singleton holder) (Map.findWithDefault [] holder (stParents st)))
  where
    go _ [] = []
    go seen (l : rest)
        | l `Set.member` seen = go seen rest
        | otherwise = case Map.lookup l (stLoans st) of
            Just (place, mutable, _) -> [place | mutable] ++ go (Set.insert l seen) rest
            Nothing -> go (Set.insert l seen) (Map.findWithDefault [] l (stParents st) ++ rest)

-- The locals and every local their loans were taken from, at any remove
ancestorsOrSelf :: St -> [Local] -> Set Local
ancestorsOrSelf st = go Set.empty
  where
    go seen [] = seen
    go seen (l : rest)
        | l `Set.member` seen = go seen rest
        | otherwise = go (Set.insert l seen) (Map.findWithDefault [] l (stParents st) ++ rest)

-- The parts of a value of the type that are permissions or values of a linear type, as the steps to each from the value: the value itself
-- for a Block or a linear struct or enum, the fields that are (or hold) one for any other struct. An enum that holds one in a variant is taken
-- as a whole.
-- A struct or an enum with a drop is not linear: its drop is its use, wherever it goes out of scope.
linearParts :: Set Name -> Set Name -> Program -> Type -> [[Step]]
linearParts linear drops program = go (0 :: Int)
  where
    go depth ty
        | depth > 8 = []
        | otherwise = case ty of
            TBlock _ -> [[]]
            -- (a list and a Box are structs of the prelude, but no value of one holds a permission: an element may
            -- not be one, so there is no linear part inside one for this pass to follow)
            TList _ -> []
            TBox _ -> []
            TNamed base _ | base `Set.member` drops -> []
            TVariant v | Just n <- ownerOf program v, baseNameOf n `Set.member` drops -> []
            -- (an Uninit of a value that owns something is linear: what it holds is freed only by taking it out)
            TUninit t | ownsHeap program t -> [[]]
            TNamed base _ | base `Set.member` linear -> [[]]
            TVariant v | Just n <- ownerOf program v, baseNameOf n `Set.member` linear -> [[]]
            TNamed base args -> declared depth (instanceName base args)
            TVariant v -> maybe [] (declared depth) (ownerOf program v)
            _ -> []
    declared depth n = case Map.lookup n (progTypes program) of
        Just (StructDecl fields) -> concat [map (SField n f :) (go (depth + 1) t) | (f, t) <- fields]
        Just (EnumDecl variants) | any (not . null . go (depth + 1) . snd) (concatMap snd variants) -> [[]]
        _ -> []

overlaps :: Place -> Place -> Bool
overlaps (l, a) (m, b) = l == m && (stepPrefix a b || stepPrefix b a)
  where
    stepPrefix [] _ = True
    stepPrefix _ [] = False
    stepPrefix (x : xs) (y : ys) = stepCompat x y && stepPrefix xs ys
    stepCompat (SElem a) (SElem b) = a == b || a == Nothing || b == Nothing
    stepCompat x y = x == y

data Cx = Cx
    { cxProgram :: Program
    , cxCopies :: Set Name
    , cxFn :: Function
    , cxLent :: Set Local
    , cxLinear :: Set Name
    , cxDrops :: Set Name
    , -- the value that a drop is given (`self` of `<T as Drop>::drop`): lent, except for the permissions it holds, which the drop uses
      cxDropSelf :: Maybe Local
    , cxLiveAfter :: Map BlockId [Set Local] -- the locals live after each statement of a block, by the block
    , cxLiveOut :: Map BlockId (Set Local) -- the locals live at the end of a block
    , cxLiveNow :: Set Local -- the locals live after the statement or terminator being checked
    , cxCallArgs :: Set Local -- the temporaries given to the call that ends the block being checked
    , cxCloned :: Set Name -- the structs and enums with a Clone of their own (cloneBases), found once for the program
    }

-- The locals a statement or a terminator reads, and the local it gives a value
stmtUses :: Statement -> [Local]
stmtUses (Assign _ rv) = rvalueUses rv
stmtUses (Peek _ rv) = rvalueUses rv
stmtUses (AssignRef root steps rv) = root : rvalueUses rv ++ [l | RefIndex o <- steps, Just l <- [operandLocal o]]
stmtUses _ = []

rvalueUses :: Rvalue -> [Local]
rvalueUses rv = [l | (l, _, _) <- accesses rv] ++ [root | Borrow root _ _ <- [rv]]

termUses :: Terminator -> [Local]
termUses term = [l | o <- operands, Just l <- [operandLocal o]]
  where
    operands = case term of
        SwitchBool o _ _ -> [o]
        Call callee args _ _ -> callee : args
        _ -> []

-- Where each local is still going to be read: for every block, the set live after each of its statements and at
-- its end. Computed backwards from the ends of the function, as the usual liveness of locals.
liveness :: Function -> (Map BlockId [Set Local], Map BlockId (Set Local))
liveness fn = go (Map.keysSet blocks) Map.empty Map.empty Map.empty
  where
    blocks = fnBlocks fn
    predecessors = Map.fromListWith (++) [(s, [b]) | (b, BasicBlock _ term) <- Map.toList blocks, s <- successors term]
    -- (the highest block first: lowering numbers blocks in program order, so liveness, which flows backwards, crosses a
    -- block's successors before the block itself)
    go pending after liveIn liveOut = case Set.maxView pending of
        Nothing -> (after, liveOut)
        Just (b, rest) -> case Map.lookup b blocks of
            Nothing -> go rest after liveIn liveOut
            Just (BasicBlock stmts term) ->
                let liveEnd = Set.unions [Map.findWithDefault Set.empty s liveIn | s <- successors term]
                    termLive = Set.fromList (termUses term) `Set.union` (liveEnd `Set.difference` callDest term)
                    stmtAfter = scanBack termLive stmts
                    liveBefore = case (stmts, stmtAfter) of
                        (stmt : _, after0 : _) -> Set.fromList (stmtUses stmt) `Set.union` (after0 `Set.difference` defOf stmt)
                        _ -> termLive
                    pending'
                        | liveBefore == Map.findWithDefault Set.empty b liveIn = rest
                        | otherwise = foldr Set.insert rest (Map.findWithDefault [] b predecessors)
                 in go pending' (Map.insert b stmtAfter after) (Map.insert b liveBefore liveIn) (Map.insert b liveEnd liveOut)
    callDest (Call _ _ d _) = Set.singleton d
    callDest _ = Set.empty
    defOf (Assign d _) = Set.singleton d
    defOf (Peek d _) = Set.singleton d
    defOf _ = Set.empty
    scanBack liveAfterLast stmts = snd (foldl step (liveAfterLast, []) (reverse stmts))
      where
        step (liveAfter, acc) stmt = (Set.fromList (stmtUses stmt) `Set.union` (liveAfter `Set.difference` defOf stmt), liveAfter : acc)

typeOf :: Cx -> Local -> Type
typeOf cx l = maybe TInt localType (Map.lookup l (fnLocals (cxFn cx)))

isCopy :: Cx -> Local -> Bool
isCopy cx = isCopyType (cxCopies cx) (cxProgram cx) . typeOf cx

-- The errors of a program: none if it never uses a value that was moved
checkMoves :: Set Name -> Set Name -> Set Name -> Program -> [String]
checkMoves copies linear drops program = checkMovesExcluding copies linear drops Set.empty program

-- As checkMoves, but the named functions are not checked themselves: they stay in the program so that
-- calls of them are still seen with their signatures (what they lend, and what a result is from).
checkMovesExcluding :: Set Name -> Set Name -> Set Name -> Set Name -> Program -> [String]
checkMovesExcluding copies linear drops excluded program = concatMap (\fn -> checkFunction (copiesIn fn) linear drops cloned program fn) ([fn | fn <- Map.elems (progFunctions program), fnName fn `Set.notMember` excluded] ++ [progMain program])
  where
    cloned = cloneBases program
    -- (a type parameter of a function with bounds is Copy in its body, and in the functions lifted out of it that do not
    -- have a type parameter of that name of their own, when a bound says so)
    copiesIn fn = Set.union copies (Set.fromList [parameterCopy p | (name, bounded) <- Map.toList (progBounded program), p <- boundedCopy bounded, name == fnName fn || (fnName fn `elem` boundedLifted bounded && p `notElem` fnTypeParams fn)])

-- What the record of a move of the pack says when a call forwarded it, not a loop over it
forwardedMark :: String
forwardedMark = "$forwarded"

-- The pack parameter of a variadic function (its type is the pack of types `..T` itself, not one of its elements')
isPackRoot :: Cx -> Local -> Bool
isPackRoot cx r = case typeOf cx r of
    TParam p -> ".." `isPrefixOf` p && all (`notElem` "#@") p
    _ -> False

-- How a type parameter bounded by Copy is named among the Copy types (no type's name has a space)
parameterCopy :: Variable -> Name
parameterCopy p = "$param " ++ p

checkFunction :: Set Name -> Set Name -> Set Name -> Set Name -> Program -> Function -> [String]
checkFunction copies linear drops cloned program fn = nub (concat [snd (runBlock cx b st block) | (b, st) <- Map.toList ins, Just block <- [Map.lookup b (fnBlocks fn)]])
  where
    -- (the drop of a type, `<T as Drop>::drop`, is given the value to free: it only reads what native code frees after it (its fields), and
    -- it has to use the permissions the value holds, which nothing else will)
    dropOf = case (implOwner (fnName fn), fnParams fn) of
        (Just owner, self : _) | " as Drop>::drop" `isSuffixOf'` fnName fn -> Just (owner, self)
        _ -> Nothing
    lent = Set.fromList (fnBorrowed fn ++ [self | Just (_, self) <- [dropOf]])
    (liveAfter, liveOut) = liveness fn
    cx = Cx program copies fn lent linear drops (snd <$> dropOf) liveAfter liveOut Set.empty Set.empty cloned
    -- (a permission given to the function, and not lent, is the function's to use)
    entry = emptySt{stHeld = Map.fromList ([((p, steps), Nothing) | p <- fnParams fn, p `Set.notMember` lent, steps <- linearParts linear drops program (typeOf cx p)] ++ [((self, steps), Nothing) | Just (owner, self) <- [dropOf], steps <- linearParts linear (Set.delete owner drops) program (typeOf cx self), not (null steps)]), stFieldLoans = incomingFields, stExtraLoans = incomingExtras}
    incomingFields = Map.fromList [((param, field), [incomingRoot]) | param <- fnParams fn, field <- refFieldNames cx (typeOf cx param)]
    incomingExtras = Map.fromList [(param, [incomingRoot]) | param <- fnParams fn, referenceContents cx (typeOf cx param)]
    isSuffixOf' suffix text = reverse suffix == take (length suffix) (reverse text)
    -- The fixpoint goes in rounds: each round joins every reached block's state with what its predecessors' states lead
    -- to (in the order of the predecessors), and the first round that changes no block's shape ends it. It keeps rounds,
    -- rather than joining as it goes, because a join keeps the record of the move that reaches it first, and a message
    -- says where that move was. A block whose state a round leaves equal is not run again, and a block none of whose
    -- predecessors was run is not joined again: the join is idempotent, so neither would change anything.
    predecessors = Map.fromListWith (flip (++)) [(s, [b]) | (b, block) <- Map.toAscList (fnBlocks fn), s <- successors (blockTerminator block)]
    ins = fixpoint (Map.singleton (BlockId 0) entry) Map.empty (Set.singleton (BlockId 0))
    fixpoint known outs changed =
        let ran = [(b, block) | b <- Set.toList changed, Just block <- [Map.lookup b (fnBlocks fn)]]
            outs' = foldl' (\m (b, block) -> Map.insert b (fst (runBlock cx b (known Map.! b) block)) m) outs ran
            touched = Set.fromList [s | (_, block) <- ran, s <- successors (blockTerminator block)]
            reached s = foldl1 joinSt [out | p <- Map.findWithDefault [] s predecessors, Just out <- [Map.lookup p outs']]
            joined = [(s, st) | s <- Set.toList touched, let st = maybe (reached s) (`joinSt` reached s) (Map.lookup s known), Map.lookup s known /= Just st]
            known' = foldl' (\m (s, st) -> Map.insert s st m) known joined
         in if and [maybe False (sameShape st) (Map.lookup s known) | (s, st) <- joined] then known else fixpoint known' outs' (Set.fromList (map fst joined))

runBlock :: Cx -> BlockId -> St -> BasicBlock -> (St, [String])
runBlock cx0 b st0 (BasicBlock stmts term) = (st2, reverse errs1 ++ errs2)
  where
    cx = cx0{cxCallArgs = Set.fromList [l | Call _ args _ _ <- [term], Just l <- map operandLocal args, localSource cx0 l == Nothing]}
    (st1, pos1, errs1) = foldl' step (st0, Nothing, []) (zip [0 ..] stmts)
    (st2, errs2) = terminator cx{cxLiveNow = Map.findWithDefault Set.empty b (cxLiveOut cx)} pos1 st1 term
    step (st, pos, errs) (i, s) = case s of
        Ghost _ (GhostPosition line column) -> (st, Just (line, column), errs)
        Assign d rv ->
            let liveNow = case drop i (Map.findWithDefault [] b (cxLiveAfter cx)) of
                    (x : _) -> x
                    [] -> Map.findWithDefault Set.empty b (cxLiveOut cx)
                (st', es) = assign cx{cxLiveNow = liveNow} pos st d rv
             in (st', pos, reverse es ++ errs)
        AssignRef root steps rv ->
            let liveNow = case drop i (Map.findWithDefault [] b (cxLiveAfter cx)) of
                    (x : _) -> x
                    [] -> Map.findWithDefault Set.empty b (cxLiveOut cx)
                (st', es) = updatePlace cx{cxLiveNow = liveNow} pos st root steps rv
             in (st', pos, reverse es ++ errs)
        Ghost _ _ -> (st, pos, errs)
        -- (the ownership pass makes these, after this check)
        Drop _ -> (st, pos, errs)
        Peek d _
            | mayHoldReference (cxProgram cx) (typeOf cx d) -> (st, pos, unmodelledLoan cx pos d : errs)
            | otherwise -> (st, pos, errs)

refStepOf :: RefStep -> Step
refStepOf (RefField ctor field) = SField ctor field
refStepOf (RefIndex o) = SElem (case o of Const (CInt n) -> Just n; _ -> Nothing)

refStepConst :: Map Local Integer -> RefStep -> Step
refStepConst consts (RefIndex o) = SElem (case o of Const (CInt n) -> Just n; Copy l -> Map.lookup l consts; Move l -> Map.lookup l consts; _ -> Nothing)
refStepConst _ other = refStepOf other

-- What an rvalue does with the locals it names: the part of the local, and whether it reads it or takes it
accesses :: Rvalue -> [(Local, [Step], Role)]
accesses rv = case rv of
    Borrow root steps _ -> (root, map refStepOf steps, Read) : [(l, [], Read) | RefIndex o <- steps, Just l <- [operandLocal o]]
    Deref o -> [(l, [], Read) | Just l <- [operandLocal o]]
    ReadField o name field -> [(l, [SField name field], Read) | Just l <- [operandLocal o]]
    IsVariant o _ -> [(l, [STag], Read) | Just l <- [operandLocal o]]
    AsVariant o _ -> [(l, [], Read) | Just l <- [operandLocal o]]
    Unbox o -> [(l, [], Read) | Just l <- [operandLocal o]]
    -- (n copies of x are made of the value that is given, which is moved into them)
    ListOp op [n, x] | op `elem` [NewArray, NewBoxed] -> [(l, [], role) | (o, role) <- [(n, Read), (x, Consume)], Just l <- [operandLocal o]]
    _ -> [(l, [], role) | (o, role) <- roles rv, Just l <- [operandLocal o]]

-- The place a place is ultimately of: through the loans of the reference locals it starts from, and the views
-- it was read by, so that a reborrow overlaps what its parent borrow is of
resolvePlace :: Cx -> St -> Place -> Place
resolvePlace cx st place = fst (resolvePlaceChain cx st place)

-- As resolvePlace, with the reference locals the place was resolved through: a borrow of one is a reborrow of
-- its loan, not a second loan that conflicts with it. A value that holds references has loans too, but its
-- places are its own: what its references are to is carried with a loan of it (`carriedBy`), not resolved to
resolvePlaceChain :: Cx -> St -> Place -> (Place, [Local])
resolvePlaceChain cx st = go (8 :: Int) []
  where
    go 0 chain place = (place, chain)
    go n chain (root, steps) = case Map.lookup root (stLoans st) of
        Just ((r2, s2), _, _) | isReference cx root -> go (n - 1) (root : chain) (r2, s2 ++ steps)
        _ -> case Map.lookup root (stViews st) of
            Just ps | not (Set.null ps) -> let (r2, s2) = head (Set.toList ps) in go (n - 1) chain (r2, s2 ++ steps)
            _ -> ((root, steps), chain)

-- Incoming field pointees may alias, so they share one symbolic root.
incomingRoot :: Place
incomingRoot = (Local (-1), [])

unmodelledLoan :: Cx -> Pos -> Local -> String
unmodelledLoan cx pos d = message cx pos ("the loans of " ++ describeLocal cx d ++ " are not modelled for this operation, and it can hold a reference")

isReference :: Cx -> Local -> Bool
isReference cx l = case typeOf cx l of
    TRef _ -> True
    TMutRef _ -> True
    _ -> False

-- (an update parameter is lent too, and the value a drop is given is lent only so that its parts are not moved out)
readLentParam :: Cx -> Local -> Bool
readLentParam cx l = l `elem` fnBorrowed (cxFn cx) && l `notElem` fnMutBorrowed (cxFn cx)

sharedThrough :: Cx -> St -> Local -> Bool
sharedThrough cx st l = readLentParam cx l || l `Set.member` stShared st || case typeOf cx l of
    TRef _ -> True
    _ -> False

-- (a Copy value holds no update reference, and a value holding a shared reference is not read through it until it is read out)
sharedHeld :: Cx -> St -> Local -> Bool
sharedHeld cx st l = not (isCopy cx l) && (readLentParam cx l || l `Set.member` stShared st)

sharedTransfer :: Cx -> St -> [Local] -> Rvalue -> Bool
sharedTransfer cx st moved rv = case rv of
    Use o -> carries [o]
    -- (Clone refuses a type that holds an update reference, so a clone of a type parameter is a value of its own)
    CopyOf o -> carries [o | Just l <- [operandLocal o], mayHoldUpdate (cxProgram cx) (typeOf cx l)]
    AsVariant o _ -> carries [o]
    Unsize o -> carries [o]
    MakeBox o -> carries [o]
    MakeList os -> carries os
    MakeData _ fields -> carries (map snd fields)
    TakeField l _ _ -> carries [Copy l]
    ReadField o _ _ -> through [o]
    Deref o -> through [o]
    Unbox o -> through [o]
    Borrow{} -> False
    BinaryOp{} -> False
    IsVariant{} -> False
    ListOp op os -> case op of
        First -> through (take 1 os)
        Last -> through (take 1 os)
        Get -> through (take 1 os)
        AddrGet -> through (lastOf os)
        AddrTake -> through (lastOf os)
        UninitGet -> through (lastOf os)
        UninitTake -> through (lastOf os)
        Push -> carries os
        Set -> carries os
        Pop -> carries os
        FromList -> carries os
        NewArray -> carries os
        NewBoxed -> carries os
        UninitNew -> carries os
        AddrWrite -> carries os
        AddrDropValue -> carries os
        AddrDropRange -> carries os
        BlockTaken -> carries os
        BlockResized -> carries os
        BlockSplitLo -> carries os
        BlockSplitHi -> carries os
        BlockJoin -> carries os
        BlockCast -> carries os
        AddrAlloc -> False
        BlockNew -> False
        BlockAssume -> False
        NewEmptyBoxed -> False
        UninitEmpty -> False
        UninitDiscard -> False
        AddrResize -> False
        AddrFree -> False
        Length -> False
        WriteByte -> False
        WriteError -> False
        ReadByte -> False
        ArgCount -> False
        ArgByte -> False
        PathByte -> False
        FileLoad -> False
        FileByte -> False
        StoreByte -> False
        FileStore -> False
        ToByte -> False
        FromByte -> False
        AddrNull -> False
        AddrOffset -> False
        AddrCast -> False
        AddrToInt -> False
        AddrFromInt -> False
        Narrow _ _ -> False
  where
    -- (a move of what may be reached through a shared path is refused, so only what is read is carried on)
    carries os = any (sharedHeld cx st) [l | Just l <- map operandLocal os, l `notElem` moved]
    through os = any (sharedThrough cx st) [l | Just l <- map operandLocal os]
    lastOf os = drop (length os - 1) os

sharedPathError :: Cx -> Pos -> Local -> String -> String
sharedPathError cx pos l action = message cx pos (describeLocal cx l ++ " may be reached through a shared reference or a parameter lent to be read (&T), so nothing can be changed through it: it cannot be " ++ action)

-- The places a local stands for: those it is a view of, or itself
placesOf :: St -> Local -> [Place]
placesOf st l = case Map.lookup l (stViews st) of
    Just ps | not (Set.null ps) -> Set.toList ps
    _ -> [(l, [])]

assign :: Cx -> Pos -> St -> Local -> Rvalue -> (St, [String])
assign cx pos st0 d rv = (base{stLoans = loans'', stExtraLoans = extras'', stFieldLoans = fieldLoans'', stConst = consts'', stFnAlias = fnAlias', stParents = parents'', stThrough = through'', stReborrowedThrough = reborrowed', stExact = exact', stShared = shared'}, errs ++ lost cx pos st1 d ++ loanErrs ++ readOutErrs ++ readThroughErrs ++ placeReadErrs ++ disturbErrs ++ lookErrs ++ unmodelledErrs ++ slotErrs ++ sharedBorrowErrs ++ externValues cx pos (operandsOfRvalue rv))
  where
    shared' = if not (isCopy cx d) && sharedTransfer cx st1 [l | (l, _, Consume) <- used] rv then Set.insert d (stShared base) else stShared base
    sharedBorrowErrs = [sharedPathError cx pos root "lent for updating" | Borrow root _ True <- [rv], sharedThrough cx st1 root]
    -- (the one place a reference is certainly to goes with a copy of it)
    exact' = case rv of
        Use operand | Just src <- operandLocal operand, Just place <- Map.lookup src (stExact st1) -> Map.insert d place (stExact base)
        CopyOf operand | Just src <- operandLocal operand, Just place <- Map.lookup src (stExact st1) -> Map.insert d place (stExact base)
        _ -> stExact base
    -- (the references a reborrow was taken through, which lending it to a call does not conflict with)
    reborrowed' = case (borrowPlace, rv) of
        (Just _, _) | not (null borrowChain) -> Map.insert d (nub (borrowChain ++ concat [Map.findWithDefault [] link (stReborrowedThrough st1) | link <- borrowChain])) (stReborrowedThrough base)
        (Nothing, Use operand) | isRefType ty, Just src <- operandLocal operand, Just chain <- Map.lookup src (stReborrowedThrough st1) -> Map.insert d chain (stReborrowedThrough base)
        (Nothing, CopyOf operand) | isRefType ty, Just src <- operandLocal operand, Just chain <- Map.lookup src (stReborrowedThrough st1) -> Map.insert d chain (stReborrowedThrough base)
        _ -> stReborrowedThrough base
    disturbErrs = take 1 (viewsDisturbed cx pos st1 [d] "is given another value" (d, []) ++ concat [viewsDisturbed cx pos st1 [d] "is lent for updating" place | Just (place, True) <- [borrowPlace]])
    -- (a look at a value that holds one with a drop is made in place, never copied, so it is the only value its local is given)
    lookErrs = case view of
        q : _ | holdsDrop cx ty, definitionsOf (cxFn cx) d > 1 ->
            [message cx pos (describeLocal cx d ++ " looks at " ++ describe cx q ++ ", which holds a value with a drop, and is given a value elsewhere too: a look at a value with a drop is made in place, so give it a name of its own")]
        _ -> []
    through'' = case (view, rv) of
        ([], _) -> Map.delete d (stThrough base)
        (_, Deref o) | Just r <- operandLocal o, isReference cx r || r `Set.member` cxLent cx -> Map.insert d (Set.singleton r) (stThrough base)
        _ -> case Set.unions [rs | (l, _, _) <- accesses rv, Just rs <- [Map.lookup l (stThrough st1)]] of
            rs | Set.null rs -> Map.delete d (stThrough base)
               | otherwise -> Map.insert d rs (stThrough base)
    -- (making a view reads none of it yet, so only a loan of all of it stands against that; the size of a list reads no element)
    placeReadErrs = case rv of
        Borrow{} -> []
        _ -> placeReads cx pos st1 (d : [l | callCopy, l <- Set.toList (cxCallArgs cx)]) [(l, if isProjection rv && Just l == sourceLocal rv then ps ++ [stepOf rv] else ps, isCopy cx l || (null view && not lengthOnly)) | (l, ps, role) <- used, role == Read || isCopy cx l]
    lengthOnly = case rv of
        ListOp Length _ -> True
        _ -> False
    -- (a Copy part of a value read into a value of its own that is an argument of the call ending the block is read where
    -- the call is made, so the borrows made for that call do not stand against it: LANGUAGE.md, Lent parameters)
    callCopy = isCopy cx d && d `Set.member` cxCallArgs cx && case rv of
        ReadField{} -> True
        _ -> isProjection rv
    parents'' = case rv of
        Borrow{} -> parentsAre borrowParents
        ReadField o _ field | isReference cx d, Just src <- operandLocal o, Just (_ : _) <- fieldLoansThrough src field -> parentsAre (readOutOf src)
        Unbox o | isReference cx d, Just src <- operandLocal o, not (null (loansOf src)) -> parentsAre (readOutOf src)
        ListOp op (_ : _) | isReference cx d, Just src <- readOutSource, op `elem` [Get, First, Last, UninitGet, UninitTake], not (null (loansOf src)) -> parentsAre (readOutOf src)
        ListOp op args | op `elem` [Pop, FromList, NewArray, NewBoxed, UninitNew, AddrWrite, AddrDropValue, AddrDropRange, BlockTaken, BlockResized, BlockSplitLo, BlockSplitHi, BlockJoin, BlockCast] -> parentsAre (carrying args)
        Unsize o -> parentsAre (carrying [o])
        Deref o | isReference cx d, Just src <- operandLocal o -> parentsAre (src : Map.findWithDefault [] src (stParents st1))
        AsVariant o _ | Just src <- operandLocal o -> parentsAre (Map.findWithDefault [] src (stParents st1))
        MakeData _ fields -> parentsAre (carrying [o | (_, o) <- fields])
        MakeList items -> parentsAre (carrying items)
        MakeBox o -> parentsAre (carrying [o])
        ListOp Push args -> parentsAre (carrying args)
        ListOp Set args -> parentsAre (carrying args)
        Use (Move src) -> parentsAre (Map.findWithDefault [] src (stParents st1))
        Use (Copy src) -> parentsAre (Map.findWithDefault [] src (stParents st1))
        CopyOf o | Just src <- operandLocal o -> parentsAre (Map.findWithDefault [] src (stParents st1))
        _ -> parentsAre []
    parentsAre ps = case nub (concat [if l == d then Map.findWithDefault [] d (stParents st1) else [l] | l <- ps]) of
        [] -> Map.delete d (stParents base)
        ps' -> Map.insert d ps' (stParents base)
    carrying os = [l | Just l <- map operandLocal os, not (null (loansOf l))]
    readOutOf src = src : concat [root : chain | place <- placesOf st1 src, let ((root, _), chain) = resolvePlaceChain cx st1 place]
    borrowParents = case rv of
        Borrow root _ _ -> nub (borrowChain ++ [root | isReference cx root])
        _ -> []
    fnAlias' = case rv of
        Use (Const (CFn name)) -> Map.insert d name (stFnAlias base)
        _ -> Map.delete d (stFnAlias base)
    -- (what a local is borrowed for updating may be changed through the borrow, so its constant is not known after it)
    consts'' = case borrowPlace of
        Just ((root, _), True) -> Map.delete root consts'
        _ -> consts'
    consts' = case rv of
        Use (Const (CInt n)) -> Map.insert d n (stConst base)
        Use (Copy src) -> maybe (Map.delete d (stConst base)) (\n -> Map.insert d n (stConst base)) (Map.lookup src (stConst base))
        Use (Move src) -> maybe (Map.delete d (stConst base)) (\n -> Map.insert d n (stConst base)) (Map.lookup src (stConst base))
        _ -> Map.delete d (stConst base)
    base = hold cx pos (define cx st1 d view) d view
    -- the places the fields of a value that holds references are to: made at its construction, read out of
    -- it by a field read, and carried with it when it is moved (the holder's own extra loans freeze them
    -- while the holder is live)
    loansOf l = case Map.lookup l (stLoans st1) of
        Just (place, _, _) -> place : Map.findWithDefault [] l (stExtraLoans st1)
        Nothing -> Map.findWithDefault [] l (stExtraLoans st1)
    clearedFields = Map.filterWithKey (\(root, _) _ -> root /= d) (stFieldLoans base)
    (loans'', extras'', fieldLoans'') = fromMaybe none loanRule
    unmodelledErrs = [unmodelledLoan cx pos d | Nothing <- [loanRule], holds ty]
    slotErrs = [message cx pos "Addr::get cannot read a slot that may hold an update reference yet: take the slot instead" | ListOp AddrGet _ <- [rv], mayHoldUpdate (cxProgram cx) ty]
    holds = mayHoldReference (cxProgram cx)
    none = (loans', Map.delete d (stExtraLoans base), clearedFields)
    keepExtras places = if null places then Map.delete d (stExtraLoans base) else Map.insert d places (stExtraLoans base)
    carry os = Just (loans', keepExtras (concat [loansOf l | Just l <- map operandLocal os]), clearedFields)
    copied src = Just (loans', case Map.lookup src (stExtraLoans st1) of Just places -> Map.insert d places (stExtraLoans base); Nothing -> Map.delete d (stExtraLoans base), transferFields src False)
    extrasOf l = Map.findWithDefault [] l (stExtraLoans st1)
    -- (a part read out of a value: a reference is a loan of one of the places, a value holding references holds them all)
    readOut places
        | isRefType ty = case places of
            place : more -> Just (Map.insert d (place, isMutRef ty, pos) (stLoans base), keepExtras more, clearedFields)
            [] -> Just none
        | holds ty = Just (loans', keepExtras places, foldl' (\out field -> Map.insert (d, field) places out) clearedFields (refFieldNames cx ty))
        | otherwise = Just none
    loanRule = case rv of
        Use (Const _) -> Just none
        Use (Move src) -> Just (loans', transferExtras src, transferFields src True)
        Use (Copy src) -> copied src
        CopyOf o -> maybe (Just none) copied (operandLocal o)
        AsVariant o _ -> maybe (Just none) copied (operandLocal o)
        BinaryOp{} -> Just none
        IsVariant{} -> Just none
        MakeData _ fields ->
            let made = [(f, loansOf l) | (f, o) <- fields, Just l <- [operandLocal o], not (null (loansOf l))]
             in Just (loans', if null made then Map.delete d (stExtraLoans base) else Map.insert d (concatMap snd made) (stExtraLoans base), foldl' (\m (f, places) -> Map.insert (d, f) places m) clearedFields made)
        MakeList items -> carry items
        MakeBox o -> carry [o]
        Unsize o -> carry [o]
        ReadField operand _ field
            | Just src <- operandLocal operand, not (isRefType ty), Just places <- Map.lookup (src, field) (stFieldLoans st1), not (null (refFieldNames cx ty)) ->
                Just (loans', Map.insert d places (stExtraLoans base), foldl' (\out child -> Map.insert (d, child) places out) clearedFields (refFieldNames cx ty))
            | Just src <- operandLocal operand -> readOut (fromMaybe [] (fieldLoansThrough src field))
            | otherwise -> Just none
        Deref operand
            | Just src <- operandLocal operand, isRefType ty -> readOut (derefLoans src)
            | Just src <- operandLocal operand, holds ty ->
                let made = [(field, nub (concatMap (heldThrough field) (derefPlaces src))) | field <- refFieldNames cx ty]
                 in Just (loans', keepExtras (derefLoans src), foldl' (\out (field, places) -> Map.insert (d, field) places out) clearedFields made)
            | otherwise -> Just none
        Unbox o -> maybe (Just none) (readOut . loansOf) (operandLocal o)
        Borrow root steps _
            | isRefType (typeOf cx root) ->
                let primary = fmap (\(place, _, _) -> place) (Map.lookup d loans')
                    alternatives = filter (\place -> Just place /= primary) (nub [resolvePlace cx st1 (owner, prefix ++ map (refStepConst (stConst st1)) steps) | (owner, prefix) <- Map.findWithDefault [] root (stExtraLoans st1)])
                 in Just (loans', keepExtras alternatives, clearedFields)
            | otherwise -> Just none
        TakeField{} -> Nothing
        ListOp op args -> listLoans op args
    listLoans op args = case op of
        Push | [xs, x] <- args -> Just (loans', keepExtras (concat [loansOf l | Just l <- [operandLocal x]] ++ concat [extrasOf l | Just l <- [operandLocal xs]]), clearedFields)
        Set | [xs, _, x] <- args -> Just (loans', keepExtras (concat [loansOf l | Just l <- [operandLocal x]] ++ concat [extrasOf l | Just l <- [operandLocal xs]]), clearedFields)
        Push -> Nothing
        Set -> Nothing
        Pop -> carry args
        FromList -> carry args
        NewArray -> carry (drop 1 args)
        NewBoxed -> carry (drop 1 args)
        First -> readOutOfList
        Last -> readOutOfList
        Get -> readOutOfList
        AddrWrite -> carry args
        AddrGet -> readOutOfLast
        AddrTake -> readOutOfLast
        UninitNew -> carry args
        UninitGet -> readOutOfLast
        UninitTake -> readOutOfLast
        -- (a permission given back is the one given: it holds what was written into its slots)
        AddrDropValue -> carry args
        AddrDropRange -> carry args
        BlockTaken -> carry args
        BlockResized -> carry args
        BlockSplitLo -> carry args
        BlockSplitHi -> carry args
        BlockJoin -> carry args
        BlockCast -> carry args
        -- These mint empty permissions, including Block::assume.
        AddrAlloc -> Just none
        BlockNew -> Just none
        BlockAssume -> Just none
        NewEmptyBoxed -> Just none
        UninitEmpty -> Just none
        -- (numbers, bytes, addresses, and lists of bytes)
        AddrResize -> Just none
        UninitDiscard -> Just none
        AddrFree -> Just none
        Length -> Just none
        WriteByte -> Just none
        WriteError -> Just none
        ReadByte -> Just none
        ArgCount -> Just none
        ArgByte -> Just none
        PathByte -> Just none
        FileLoad -> Just none
        FileByte -> Just none
        StoreByte -> Just none
        FileStore -> Just none
        ToByte -> Just none
        FromByte -> Just none
        AddrNull -> Just none
        AddrOffset -> Just none
        AddrCast -> Just none
        AddrToInt -> Just none
        AddrFromInt -> Just none
        Narrow _ _ -> Just none
      where
        readOutOfList = maybe (Just none) (readOut . extrasOf) (listOperand >>= operandLocal)
        readOutOfLast = maybe (Just none) (readOut . loansOf) readOutSource
        listOperand = case args of
            o : _ -> Just o
            [] -> Nothing
    derefLoans src = nub (concatMap (heldThrough "") (derefPlaces src))
    derefPlaces src = case Map.lookup src (stLoans st1) of
        Just (place, _, _) -> place : extrasOf src
        Nothing -> mayPlacesOf st1 src
    -- (the value a part is read out of: a permission or an Uninit is the last operand)
    readOutSource = case rv of
        ReadField o _ _ -> operandLocal o
        Deref o -> operandLocal o
        Unbox o -> operandLocal o
        ListOp op os@(_ : _) | op `elem` [AddrGet, AddrTake, UninitGet, UninitTake] -> operandLocal (last os)
        ListOp op (o : _) | op `elem` [Get, First, Last] -> operandLocal o
        _ -> Nothing
    -- (a reference field read through a view of its holder, or through a reference to it, is to what the holder's field
    -- is to; a holder whose fields are not followed one by one, such as a Box, an enum or a call result, gives all its loans)
    fieldLoansThrough src field = case Map.lookup (src, field) (stFieldLoans st1) of
        Just places -> Just places
        Nothing -> case concat [heldThrough field (resolvePlace cx st1 place) | place <- placesOf st1 src] of
            [] -> Nothing
            found -> Just found
    heldThrough field (root, steps) = case filter (/= SDeref) steps of
        [] -> fromMaybe (loansOf root) (Map.lookup (root, field) (stFieldLoans st1))
        SField _ f : _ -> fromMaybe (loansOf root) (Map.lookup (root, f) (stFieldLoans st1))
        _ -> loansOf root
    transferExtras src = case Map.lookup src (stExtraLoans st1) of
        Just places -> Map.insert d places (Map.delete src (stExtraLoans base))
        Nothing -> Map.delete d (stExtraLoans base)
    transferFields src move =
        let from = [(f, places) | ((root, f), places) <- Map.toList (stFieldLoans st1), root == src]
            kept = if move then Map.filterWithKey (\(root, _) _ -> root /= src) clearedFields else clearedFields
         in foldl' (\m (f, places) -> Map.insert (d, f) places m) kept from
    (borrowPlace, borrowChain) = case rv of
        Borrow root steps mutable -> let (place, chain) = resolvePlaceChain cx st1 (root, map (refStepConst (stConst st1)) steps) in (Just (place, mutable), chain)
        _ -> (Nothing, [])
    loans' = case borrowPlace of
        Just (place, mutable) -> Map.insert d (place, mutable, pos) (stLoans base)
        Nothing -> case rv of
            Use operand | isRefType ty, Just src <- operandLocal operand -> copyLoan src
            CopyOf operand | isRefType ty, Just src <- operandLocal operand -> copyLoan src
            _ -> Map.delete d (stLoans base)
    copyLoan src = case Map.lookup src (stLoans st1) of
        Just (target, _, at) -> Map.insert d (target, case ty of TMutRef{} -> True; _ -> False, at) (stLoans base)
        Nothing -> Map.delete d (stLoans base)
    isRefType TRef{} = True
    isRefType TMutRef{} = True
    isRefType _ = False
    isMutRef TMutRef{} = True
    isMutRef _ = False
    activeLoans = [(ref, place, lmut) | (ref, place, lmut) <- loanEntries cx st1, ref `Set.member` cxLiveNow cx, ref /= d]
    loanErrs = case borrowPlace of
        Just (place, mutable) ->
            [ message cx pos (describe cx place ++ " is borrowed by " ++ describeLocal cx ref ++ ", so it cannot be borrowed" ++ (if mutable then " for updating" else "") ++ " while that borrow is live: the borrow ends at the last use of " ++ describeLocal cx ref)
            | (ref, lplace, lmut) <- activeLoans, ref `Set.notMember` ancestorsOrSelf st1 borrowParents, overlaps place lplace, mutable || lmut
            ]
        Nothing ->
            [ message cx pos (describeLocal cx d ++ " cannot be assigned while it is borrowed by " ++ describeLocal cx ref ++ ": the borrow ends at the last use of " ++ describeLocal cx ref)
            | (ref, lplace, _) <- activeLoans, fst lplace == d
            ]
    -- (an update reference cannot be duplicated: one read out of a value stands in for the value's own until its
    -- last use, so the same reference cannot be read out of it again before then)
    readOutErrs = case typeOf cx d of
        TMutRef _ ->
            [ message cx pos (describe cx lplace ++ " is borrowed by " ++ describeLocal cx ref ++ ", so another update reference to it cannot be read out of " ++ describe cx q ++ " while that borrow is live: the borrow ends at the last use of " ++ describeLocal cx ref)
            | (ref, (lplace, True, _)) <- Map.toList (stLoans st1)
            , ref /= d
            , ref `Set.member` cxLiveNow cx
            , Just from <- [Map.lookup ref (stMay st1)]
            , q <- map (readPlace cx st1) view
            , any (overlaps q . readPlace cx st1) (Set.toList from)
            ]
        _ -> []
    readThroughErrs = case rv of
        Deref o | Just r <- operandLocal o, isReference cx r, isCopy cx d -> suspendedReads cx pos st1 d r
        _ -> []
    -- (the size of the pack of a variadic function is a number in each copy, which reads none of its elements)
    packSize = case rv of
        ListOp Length [o] | Just l <- operandLocal o, TParam p <- typeOf cx l -> ".." `isPrefixOf` p
        _ -> False
    used
        | packSize = []
        | forLoopList = [(l, ps, Read) | (l, ps, _) <- accesses rv]
        | tuplePart = [(l, ps, Consume) | (l, ps, _) <- accesses rv]
        | otherwise = accesses rv
    sameStatement = take 1 (lentAndMoved cx pos st0 "borrowed in this expression" (loanPlacesOf cx st0 (rvalueUses rv)) [l | (l, _, Consume) <- used])
    (st1, errs) = takenApart (foldl' (access cx pos) (st0, sameStatement) used)
    -- (a value of a linear type is used when a function of its own impl takes it apart: reads a field of it, or tests or casts its variant)
    takenApart (st, es) = case rv of
        ReadField o _ _ | Just l <- operandLocal o, ownImpl l -> (consumed st l, es)
        IsVariant o _ | Just l <- operandLocal o, ownImpl l -> (consumed st l, es)
        AsVariant o _ | Just l <- operandLocal o, ownImpl l -> (consumed st l, es)
        _ -> (st, es)
    ownImpl l = case typeOf cx l of
        TNamed base _ -> owned base
        TVariant v -> maybe False owned (ownerOf (cxProgram cx) v)
        _ -> False
    owned base = base `Set.member` cxLinear cx && implOwner (fnName (cxFn cx)) == Just base
    consumed st l = let places = placesOf st l in st{stHeld = Map.filterWithKey (\h _ -> not (any (overlaps h) places)) (stHeld st)}
    ty = typeOf cx d
    -- (a part of a tuple that is taken apart, `(a, b) = e`, is taken out of it: the name has it, and not a view of the hidden tuple)
    tuplePart = case rv of
        ReadField o _ _ | Just l <- operandLocal o -> maybe False (\n -> "$tuple " `isPrefixOf` n || "$struct " `isPrefixOf` n) (localNameOf cx l)
        _ -> False
    -- (the list that a `for` loop goes through and the value that a `match` takes apart are read where they are)
    forLoopList = maybe False (\name -> "$list " `isPrefixOf` name || name == "$match") (localNameOf cx d)
    -- what the value that d gets is a view of, if it is one: a part of a value that is not Copy, or the value that a cast is of
    view = case rv of
        _ | tuplePart -> []
        _ | isProjection rv, not (isCopy cx d) -> [(r, ps ++ [stepOf rv]) | Just l <- [sourceLocal rv], (r, ps) <- placesOf st1 l]
        AsVariant o _ | not (isCopyType (cxCopies cx) (cxProgram cx) ty), Just l <- operandLocal o -> placesOf st1 l
        Deref o | not (isCopy cx d), Just l <- operandLocal o -> case Map.lookup l (stLoans st1) of
            Just ((root, steps), _, _) -> [(root, steps ++ [SDeref])]
            Nothing | l `Set.member` cxLent cx -> [(l, [SDeref])]
            Nothing -> []
        -- (what a Box holds is read through it, and is the Box's when it is taken)
        Unbox o | not (isCopyType (cxCopies cx) (cxProgram cx) ty), Just l <- operandLocal o -> placesOf st1 l
        Use o | forLoopList, Just l <- operandLocal o -> placesOf st1 l
        _ -> []
    sourceLocal r = case r of
        Deref o -> operandLocal o
        ReadField o _ _ -> operandLocal o
        -- (the value in a slot is a view of the permission, which is the last operand: once the permission is changed or freed, the view is gone)
        ListOp AddrGet os@(_ : _) -> operandLocal (last os)
        ListOp _ (o : _) -> operandLocal o
        _ -> Nothing
    stepOf r = case r of
        Deref _ -> SDeref
        ReadField _ name field -> SField name field
        ListOp AddrGet _ -> SSlot
        ListOp UninitGet _ -> SSlot
        ListOp Get [_, i] -> refStepConst (stConst st1) (RefIndex i)
        _ -> SElem Nothing

-- An assignment through a reference: the root gets a new version, and no other live loan to the place may be
-- there but those of the reference it goes through and of what that reference was taken from
updatePlace :: Cx -> Pos -> St -> Local -> [RefStep] -> Rvalue -> (St, [String])
updatePlace cx pos st0 root steps rv = (updated, errs ++ placeReads cx pos st1 [] [(l, ps, True) | (l, ps, role) <- accesses rv, role == Read || isCopy cx l] ++ conflicts ++ storeErrs ++ callersStoreErrs ++ sharedWriteErrs ++ externValues cx pos (operandsOfRvalue rv) ++ take 1 (concatMap (viewsDisturbed cx pos st1 [] "is changed through a reference") targets))
  where
    callersStoreErrs =
        [ message cx pos ("a reference cannot be stored through " ++ describeStoreRoot cx st1 root ++ ", which is the caller's: return the value that holds it instead")
        | Just l <- [source]
        , mayHoldReference (cxProgram cx) (typeOf cx l)
        , any (callersPlace cx st1) targets
        ]
    -- (a write through root does not assign root: what it was reborrowed through stays)
    defined = (define cx st1 root []){stReborrowedThrough = stReborrowedThrough st1, stExact = stExact st1, stShared = shared'}
    shared'
        | sharedTransfer cx st1 [l | (l, _, Consume) <- accesses rv] rv = foldl' (flip Set.insert) (stShared st1) [owner | (owner, _) <- targets, not (isCopy cx owner)]
        | otherwise = stShared st1
    sharedWriteErrs = [sharedPathError cx pos root "written through" | sharedThrough cx st1 root]
    bases = case (Map.lookup root (stExact st1), Map.lookup root (stLoans st1)) of
        (Just exact, _) -> [exact]
        (_, Just (target, _, _)) -> target : Map.findWithDefault [] root (stExtraLoans st1)
        _ -> placesOf st1 root
    targets = Set.toList (Set.fromList [resolvePlace cx st1 (owner, prefix ++ map refStepOf steps) | (owner, prefix) <- bases])
    storeErrs = case rv of
        Use _ -> []
        CopyOf _ -> []
        _ | any (maybe True (mayHoldReference (cxProgram cx)) . placeType cx) targets -> [unmodelledLoan cx pos root]
          | otherwise -> []
    source = case rv of Use operand -> operandLocal operand; CopyOf operand -> operandLocal operand; _ -> Nothing
    incoming = case source of
        Just local -> maybe [] (\(target, _, _) -> [target]) (Map.lookup local (stLoans st1)) ++ Map.findWithDefault [] local (stExtraLoans st1)
        Nothing -> []
    strong = length targets == 1
    fieldsAfter = foldl' updateFields (stFieldLoans defined) targets
    updateFields fields (owner, path) = case path of
        [] ->
            let kept = if strong then Map.filterWithKey (\(local, _) _ -> local /= owner) fields else fields
                moved = [(field, refs) | ((local, field), refs) <- Map.toList (stFieldLoans st1), Just local == source]
                merge new old = if strong then new else Set.toList (Set.fromList (new ++ old))
             in foldl' (\out (field, refs) -> Map.insertWith merge (owner, field) refs out) kept moved
        SField _ field : _ | not (null incoming) ->
            let old = Map.findWithDefault [] (owner, field) fields
                replace = strong && length path == 1
             in Map.insert (owner, field) (Set.toList (Set.fromList (incoming ++ if replace then [] else old))) fields
        _ -> fields
    extrasAfter = foldl' updateExtras (stExtraLoans defined) targets
    updateExtras extras (owner, path) =
        let oldFields = concat [refs | ((local, _), refs) <- Map.toList (stFieldLoans st1), local == owner]
            newFields = concat [refs | ((local, _), refs) <- Map.toList fieldsAfter, local == owner]
            untracked = filter (`notElem` oldFields) (Map.findWithDefault [] owner extras)
            refs = if null path && strong then incoming else untracked ++ newFields ++ incoming
         in if null refs then Map.delete owner extras else Map.insert owner (Set.toList (Set.fromList refs)) extras
    updated = defined{stFieldLoans = fieldsAfter, stExtraLoans = extrasAfter}
    (st1, errs) = foldl' (access cx pos) (st0, []) (accesses rv ++ [(root, map refStepOf steps, Read)])
    through = [root | isMutRef (typeOf cx root)]
    isMutRef ty = case ty of
        TMutRef _ -> True
        _ -> False
    conflicts =
        [ message cx pos (describe cx place ++ " is borrowed by " ++ describeLocal cx ref ++ ", so it cannot be changed through another reference while that borrow is live: the borrow ends at the last use of " ++ describeLocal cx ref)
        | place <- targets
        , (ref, lplace, lmut, via) <- loanRows cx st1
        , ref `Set.member` cxLiveNow cx
        , overlaps place lplace
        , ref `Set.notMember` ancestorsOrSelf st1 through
        , not (ref == root && lmut && contains lplace place || maybe False (\holder -> mutableHolderLoan cx st1 holder place) via)
        ]
    contains (owner, prefix) (target, path) = owner == target && prefix `isPrefixOf` path

-- A read of all a reference is to while a live reborrow of it overlaps it
suspendedReads :: Cx -> Pos -> St -> Local -> Local -> [String]
suspendedReads cx pos st except r =
    [ suspendedRead cx pos ref lplace r
    | (ref, lplace, True) <- loanEntries cx st
    , ref /= r
    , ref /= except
    , ref `Set.member` cxLiveNow cx
    , descendsFrom st ref r
    , overlaps target lplace
    ]
  where
    target = maybe (r, []) (\(place, _, _) -> place) (Map.lookup r (stLoans st))

suspendedRead :: Cx -> Pos -> Local -> Place -> Local -> String
suspendedRead cx pos ref lplace r = message cx pos (describe cx lplace ++ " is borrowed by " ++ describeLocal cx ref ++ ", so it cannot be read through " ++ describeLocal cx r ++ " while that borrow is live: the borrow ends at the last use of " ++ describeLocal cx ref)

descendsFrom :: St -> Local -> Local -> Bool
descendsFrom st ref r = r `Set.member` ancestorsOrSelf st (Map.findWithDefault [] ref (stParents st))

-- Reads of places that a live update loan overlaps (REFERENCES.md, Core rules: no independent read of what an update is to):
-- of an owner, or of a view read through a reference that a live reborrow suspends. A read flagged False makes a view, and
-- only a loan of all of it counts.
placeReads :: Cx -> Pos -> St -> [Local] -> [(Local, [Step], Bool)] -> [String]
placeReads cx pos st except reads = nub
    [ case throughs of
        Nothing -> message cx pos (describe cx lplace ++ " is borrowed by " ++ describeLocal cx ref ++ ", so it cannot be read while that borrow is live: the borrow ends at the last use of " ++ describeLocal cx ref)
        Just rs -> suspendedRead cx pos ref lplace (Set.findMin rs)
    | (l, steps, whole) <- reads
    , not (isReference cx l) || Map.member l (stThrough st)
    , let throughs = Map.lookup l (stThrough st)
    , q <- [readPlace cx st (r, ps ++ steps) | (r, ps) <- placesOf st l]
    , (ref, lplace, True) <- loanEntries cx st
    , ref `notElem` except
    , ref `Set.member` cxLiveNow cx
    , overlaps q lplace
    , whole || length (snd lplace) <= length (snd q)
    , case throughs of
        Nothing -> ref `Set.notMember` ancestorsOrSelf st [l]
        Just rs -> all (\r -> ref /= r && descendsFrom st ref r) (Set.toList rs)
    ]

-- The effect of the use of a part of a local
-- The elements of a pack a call forwards that are outside the bounds of the part forwarded, when those are numbers: the call
-- does not give them, so what is done to them does not count against the forward
forwardedOutside :: Cx -> [Operand] -> Local -> Place -> Bool
forwardedOutside cx args l q = case q of
    (r, SField "$pack" k : _) | r == l, all isDigit k, not (null k), isPackRoot cx l -> or [outsideOf (read k) more | (a : more) <- tails args, operandLocal a == Just l]
    _ -> False
  where
    outsideOf k more = case more of
        Const (CInt lo) : rest -> k < lo || (case rest of Const (CInt hi) : _ -> k >= hi; _ -> False)
        _ -> False

access :: Cx -> Pos -> (St, [String]) -> (Local, [Step], Role) -> (St, [String])
access = accessExcept (const False)

-- An access that does not see the places the predicate gives: their moves and their loans
accessExcept :: (Place -> Bool) -> Cx -> Pos -> (St, [String]) -> (Local, [Step], Role) -> (St, [String])
accessExcept except cx pos (st, errs) (l, steps, role) = (st', errs ++ useErrs ++ moveErrs ++ sharedGiven ++ loanErrs ++ disturbErrs)
  where
    -- (the other move rules see only the views a local has on every path, or one level of those it may have)
    sharedGiven = [sharedPathError cx pos l "given on" | taking, null moveErrs, sharedHeld cx st l]
    disturbErrs
        | taking = take 1 (concatMap (viewsDisturbed cx pos st [l] "is moved") places)
        | otherwise = []
    loanErrs
        | role == Consume && not (isCopy cx l) =
            [ message cx pos (describe cx q ++ " is borrowed by " ++ describeLocal cx ref ++ ", so it cannot be moved while that borrow is live: the borrow ends at the last use of " ++ describeLocal cx ref)
            | q <- places
            , (ref, lplace, _) <- loanEntries cx st
            , ref `Set.member` cxLiveNow cx
            , ref /= l
            , overlaps q lplace
            , not (except lplace)
            ]
        | otherwise = []
    places = [(r, ps ++ steps) | (r, ps) <- placesOf st l]
    useErrs = take 1 [message cx pos (movedText q m mpos via) | q <- places, (m, (mpos, via)) <- Map.toList (stMoved st), overlaps q m, not (except m)]
    -- (the text names what the program wrote where the place was moved: the variable that was used, or else the place)
    movedText q m mpos via =
        let written = fromMaybe (describe cx m) via
            label = maybe (describe cx m) (\v -> if v == describe cx m then v else v ++ " (" ++ describe cx m ++ ")") via
         in if null (snd m) && packLocal (fst m) && via == Just forwardedMark
                then describe cx m ++ " was forwarded" ++ at mpos ++ " to a pack taken by value and cannot be used after it: forward it to a lent pack (&..U) to keep it"
            else if null (snd m) && packLocal (fst m)
                then describe cx m ++ " was taken by the loop over it" ++ at mpos ++ " (for a in " ++ describe cx m ++ " takes the elements of a pack taken by value) and cannot be used after it: loop with for a in &" ++ describe cx m ++ " to keep it"
            else if q == m
                then label ++ " was moved" ++ at mpos ++ " and cannot be used again: write clone(" ++ written ++ ") where it is moved to keep it"
                else label ++ " was moved" ++ at mpos ++ ", and " ++ describe cx q ++ " is a part of it or has it as a part: write clone(" ++ written ++ ") where it is moved to keep it"
    -- (the pack of a variadic function is moved only by a loop that takes its elements: lowerPackLoop in lib/elaborate/lower.tersus)
    packLocal r = isPackRoot cx r
    taking = role == Consume && not (isCopy cx l)
    moveErrs
        | not taking = []
        | otherwise = concatMap moveError (places ++ [(r, ps ++ steps) | Just may <- [Map.lookup l (stMay st)], (r, ps) <- Set.toList may, (r, ps ++ steps) `notElem` places])
    moveError q@(root, ps)
        | SDeref `elem` ps = [message cx pos ("cannot move *" ++ describe cx (root, filter (/= SDeref) ps) ++ " out of the reference *" ++ describe cx (root, filter (/= SDeref) ps) ++ ", which still holds it: write clone(*" ++ describe cx (root, filter (/= SDeref) ps) ++ ") to copy it, or replace what the reference is to through it")]
        | permissionPlace q, root `Set.notMember` cxLent cx, Just n <- dropTypeOf root, maybe True (not . ("$struct " `isPrefixOf`)) (localNameOf cx root) =
            [message cx pos ("the permission " ++ named q ++ " is moved out of a value of " ++ n ++ ", which has a drop that would free the memory again: take the value apart, as in " ++ n ++ " { ... } = " ++ describeLocal cx root ++ ";, which uses it up")]
        | SSlot `elem` ps = [message cx pos ("cannot move " ++ named q ++ " out of the memory of a permission or an Uninit, which still holds it: write clone(" ++ fromMaybe (describe cx q) (localSource cx l) ++ ") to copy it, or take it out with Addr::take or Uninit::take")]
        | isPackRoot cx root, (SElem _ : _) <- ps = [message cx pos ("cannot move " ++ named q ++ " out of the pack " ++ describeLocal cx root ++ ": an element at an index that is not a number, or read by for a in &" ++ describeLocal cx root ++ ", is only read: take the elements with for a in " ++ describeLocal cx root ++ " over a pack taken by value, or write clone(" ++ fromMaybe (describe cx q) (localSource cx l) ++ ")")]
        | isPackRoot cx root, (SField "$pack" _ : _) <- ps, root `Set.member` cxLent cx = [message cx pos ("cannot move " ++ named q ++ " out of the pack " ++ describeLocal cx root ++ ", which is lent (&..T) to this function and can only be read: write clone(" ++ fromMaybe (describe cx q) (localSource cx l) ++ ") to get a value of its own")]
        | [s | s@(SElem _) <- ps] /= [] = [message cx pos ("cannot move " ++ named q ++ " out of a list, which still holds it: write clone(" ++ fromMaybe (describe cx q) (localSource cx l) ++ ") to copy it")]
        | root `Set.member` cxLent cx, permissionPlace q, not (dropsPermission q) = [message cx pos (named q ++ " is a permission in a value that is lent (&T) to this function, which can lend it to an operation (Addr::get) but not use it up")]
        | root `Set.member` cxLent cx, not (dropsPermission q) = [message cx pos (describe cx q ++ " is lent (&T) to this function and can only be read: write clone(" ++ describe cx q ++ ") to get a value of its own")]
        | root `Set.notMember` cxLent cx, Just (n, owner) <- droppedOwner q =
            [message cx pos ("cannot move " ++ named q ++ " out of a value of " ++ n ++ ", whose drop is given the whole value: write clone(" ++ fromMaybe (describe cx q) (localSource cx l) ++ ") to copy it, or take the value apart, as in " ++ n ++ " { ... } = " ++ describe cx owner ++ ";")]
        | otherwise = []
    named q = maybe (describe cx q) (\v -> v ++ " (" ++ describe cx q ++ ")") (localSource cx l)
    permissionPlace q = case placeType cx q of
        Just (TBlock _) -> True
        _ -> False
    -- (a permission in the value that a drop is given is the drop's to use, once; one in any other value that is lent is not)
    dropsPermission q@(root, _) = permissionPlace q && Just root == cxDropSelf cx
    dropTypeOf root = case typeOf cx root of
        TNamed base _ | base `Set.member` cxDrops cx -> Just base
        _ -> Nothing
    -- (the first value with a drop that the place is a field of, at any depth: a field of it moves only when it is taken apart, and a
    -- destructuring assignment takes apart its `$struct` local, which can also be a view of the value, as of `Box::unbox(b)`)
    droppedOwner (root, ps) = listToMaybe
        [ (n, (root, take k ps))
        | (k, SField _ _) <- zip [0 :: Int ..] ps
        , not ((k == 0 && takenApart root) || (k == length ps - length steps && takenApart l))
        , Just n <- [placeType cx (root, take k ps) >>= dropName]
        ]
    takenApart local = maybe False ("$struct " `isPrefixOf`) (localNameOf cx local)
    -- (a field read through a Box is a field of the value it holds)
    dropName ty = case ty of
        TBox held -> dropName held
        TNamed base _ | base `Set.member` cxDrops cx -> Just base
        TVariant v | Just owner <- ownerOf (cxProgram cx) v, baseNameOf owner `Set.member` cxDrops cx -> Just (baseNameOf owner)
        _ -> Nothing
    st'
        | taking =
            let moved = [q | q@(root, ps) <- places, all (\s -> case s of SElem _ -> False; _ -> True) ps, SSlot `notElem` ps, root `Set.notMember` cxLent cx || dropsPermission q]
                -- (a local that is a view of a permission on one path and has one of its own on another uses whichever it has)
                used = moved ++ [q | q@(root, _) <- places, root `Set.member` cxLent cx] ++ [(r, ps ++ steps) | Just may <- [Map.lookup l (stMay st)], (r, ps) <- Set.toList may]
             in st{stMoved = foldl' (\m q -> Map.insert q (pos, localSource cx l) m) (stMoved st) moved, stHeld = Map.filterWithKey (\h _ -> not (any (overlaps h) used)) (stHeld st)}
        | otherwise = st
    at p = maybe "" (\(line, column) -> " at line " ++ show line ++ ":" ++ show column) p

-- The places a local may stand for on some path
mayPlacesOf :: St -> Local -> [Place]
mayPlacesOf st l = nub (placesOf st l ++ maybe [] Set.toList (Map.lookup l (stMay st)))

-- The places that the references among these locals, and the values among them that hold references, are to
loanPlacesOf :: Cx -> St -> [Local] -> [Place]
loanPlacesOf cx st ls = [place | (ref, place, _) <- loanEntries cx st, ref `elem` ls]

-- A place read through a reference is a place of what the reference is to, which `*` does not change
readPlace :: Cx -> St -> Place -> Place
readPlace cx st place = case resolvePlace cx st place of
    (root, steps) -> if isReference cx root then (root, steps) else (root, filter (/= SDeref) steps)

-- A place lent to an operation stays in use until the operation ends, so the operation cannot also move it, a
-- value that holds it, or a part of it
lentAndMoved :: Cx -> Pos -> St -> String -> [Place] -> [Local] -> [String]
lentAndMoved = lentAndMovedExcept (\_ _ -> False)

lentAndMovedExcept :: (Place -> Place -> Bool) -> Cx -> Pos -> St -> String -> [Place] -> [Local] -> [String]
lentAndMovedExcept except cx pos st how lent consumed =
    [ message cx pos (text h q)
    | c <- consumed
    , not (isCopy cx c)
    , q <- mayPlacesOf st c
    , h <- map (readPlace cx st) lent
    , overlaps h q
    , not (except h q)
    ]
  where
    text h q
        | h == q = describe cx h ++ " is " ++ how ++ " and moved by it too: write clone(" ++ describe cx h ++ ") for one of them"
        | length (snd q) < length (snd h) = describe cx h ++ " is " ++ how ++ ", and " ++ describe cx q ++ ", which holds it, is moved by it too: write clone(" ++ describe cx q ++ ") where it is moved"
        | otherwise = describe cx h ++ " is " ++ how ++ ", and " ++ describe cx q ++ ", a part of it, is moved by it too: write clone(" ++ describe cx q ++ ") where it is moved"

-- A local that gets a value that is or holds a permission, of its own (not a view of one), holds it
hold :: Cx -> Pos -> St -> Local -> [Place] -> St
hold cx pos st d view
    | null view = st{stHeld = foldl' (\m steps -> Map.insert (d, steps) pos m) (Map.filterWithKey (\(root, _) _ -> root /= d) (stHeld st)) (linearParts (cxLinear cx) (cxDrops cx) (cxProgram cx) (typeOf cx d))}
    | otherwise = st{stHeld = Map.filterWithKey (\(root, _) _ -> root /= d) (stHeld st)}

-- The permissions a local still holds when it is given another value, which are lost
lost :: Cx -> Pos -> St -> Local -> [String]
lost cx pos st d =
    take 1 [message cx pos (unused cx st q given ++ ", and " ++ describeLocal cx d ++ " is given another value here") | (q@(root, _), given) <- Map.toList (stHeld st), root == d]

-- What is said of a permission that is not used
unused :: Cx -> St -> Place -> Pos -> String
unused cx st q@(root, steps) given =
    (case [v | (l, ps) <- Map.toList (stViews st), q `Set.member` ps, Just v <- [localSource cx l]] of
        -- (a part of a tuple that is taken apart, `(p, b) = Addr::alloc(n)`, is named by the name it was given)
        v : _ | Nothing <- localSource cx root -> v ++ what
        _ | null steps -> describe cx q ++ what
        _ -> describe cx q ++ what ++ " (in " ++ describeLocal cx root ++ ")")
        ++ ""
        ++ maybe "" (\(line, column) -> " given at line " ++ show line ++ ":" ++ show column) given
        ++ " that is not used: " ++ how
  where
    permission = case placeType cx q of
        Just (TBlock _) -> True
        _ -> False
    what = if permission then " is a permission" else " is a value of a linear type"
    how =
        if permission
            then "a permission is used exactly once, by the operation that frees or changes its memory (Addr::free, Addr::write, ...) or by giving it on"
            else "a value of a linear type is used exactly once, by giving it on or by a function of its impl that takes it apart"

-- The type of a part of a local
placeType :: Cx -> Place -> Maybe Type
placeType cx (root, steps) = foldl step (Just (typeOf cx root)) steps
  where
    step ty s = case (ty, s) of
        (Just _, SField name field) -> case Map.lookup name (progTypes (cxProgram cx)) of
            Just (StructDecl fields) -> lookup field fields
            _ -> lookup field (concat [fs | EnumDecl variants <- Map.elems (progTypes (cxProgram cx)), (v, fs) <- variants, v == name])
        _ -> Nothing

-- The one place a reference to `target` under `from` can be: every bound must be a whole local the function declares
-- (a place of its own storage, not a path through an earlier result), the declared types must list every place of a
-- `target` in them completely (FieldPaths, with references that may be to one making it incomplete), and together they
-- must name exactly one place. Otherwise Nothing: the reference is to somewhere in its bounds. (A bound inside a whole
-- local that is itself a bound adds no place: that local's places are all listed.)
exactCandidate :: Cx -> Type -> [Place] -> Maybe Place
exactCandidate cx target bounds = do
    let whole = [root | (root, []) <- bounds]
    found <- concat <$> mapM candidates [bound | bound@(root, steps) <- bounds, null steps || root `notElem` whole]
    case nub found of
        [place] -> Just place
        _ -> Nothing
  where
    candidates (root, []) | Map.member root (fnLocals (cxFn cx)) = map (\path -> (root, map (uncurry SField) path)) <$> fieldPaths True (progTypes (cxProgram cx)) target (typeOf cx root)
    candidates _ = Nothing

-- The types a value of the type holds references to, through value fields and elements (Nothing when it cannot tell)
pointeeTypes :: Cx -> Type -> Maybe [Type]
pointeeTypes cx = fmap nub . go Set.empty
  where
    types = progTypes (cxProgram cx)
    go seen ty = case ty of
        TRef inner -> Just [inner]
        TMutRef inner -> Just [inner]
        TList element -> go seen element
        TBox element -> go seen element
        TArrayOf element _ -> go seen element
        TUninit element -> go seen element
        TInt -> Just []
        TByte -> Just []
        TBool -> Just []
        TWord _ _ -> Just []
        TFn _ _ -> Just []
        TFnContract _ _ _ -> Just []
        TBoxedClosure{} -> Nothing
        TNamed base args ->
            let name = instanceName base args
             in if name `Set.member` seen then Just [] else case Map.lookup name types of
                    Just (StructDecl fields) -> concat <$> mapM (go (Set.insert name seen) . snd) fields
                    Just (EnumDecl variants) -> concat <$> mapM (go (Set.insert name seen) . snd) (concatMap snd variants)
                    Nothing -> Nothing
        TVariant variant
            | variant `Set.member` seen -> Just []
            | otherwise -> case [fields | EnumDecl variants <- Map.elems types, (other, fields) <- variants, other == variant] of
                [fields] -> concat <$> mapM (go (Set.insert variant seen) . snd) fields
                _ -> Nothing
        _ -> Nothing

-- The struct or enum whose impl a function is of (`<T>::f`, `<T<'U>>::f`, `<T as Trait>::f`)
implOwner :: Name -> Maybe Name
implOwner name = case name of
    '<' : rest | owner@(_ : _) <- takeWhile (`notElem` "<> ") rest -> Just owner
    _ -> Nothing

-- The local gets a new value: nothing is moved out of it, and it is a view of the places the value comes from (if it is a view)
define :: Cx -> St -> Local -> [Place] -> St
define _ st d view0 =
    -- (a path is followed to a fixed depth, so that a loop down a recursive value reaches a fixed point: the place that is left is a prefix, which stands for
    -- everything below it)
    let view = view0
        view' = [(r, take maxDepth ps) | (r, ps) <- view0]
     in
    St
        { stMoved = Map.filterWithKey (\(root, _) _ -> root /= d) (stMoved st)
        , stViews = if null view then Map.delete d (stViews st) else Map.insert d (Set.fromList view') (stViews st)
        , stMay = if null view then Map.delete d (stMay st) else Map.insert d (Set.fromList view') (stMay st)
        , stHeld = stHeld st
        , stLoans = stLoans st
        , stExtraLoans = stExtraLoans st
        , stFieldLoans = stFieldLoans st
        , stConst = stConst st
        , stFnAlias = stFnAlias st
        , stParents = stParents st
        , stThrough = stThrough st
        -- (a reborrow taken through the old value of d is not taken through the new one)
        , stReborrowedThrough = Map.map (filter (/= d)) (Map.delete d (stReborrowedThrough st))
        , stExact = Map.delete d (stExact st)
        , stShared = Set.delete d (stShared st)
        }

terminator :: Cx -> Pos -> St -> Terminator -> (St, [String])
terminator cx pos st term = case term of
    SwitchBool o _ _ -> let (st', errs) = accessAll [(l, [], Read) | Just l <- [operandLocal o]] in (st', errs ++ placeReads cx pos st [] [(l, [], True) | Just l <- [operandLocal o]])
    Call callee args dest _ ->
        let lent = lentArguments cx callee (length args)
            mut = mutArguments cx callee (length args)
            argLocals = [(l, b) | (a, b) <- zip args lent, Just l <- [operandLocal a]]
            lentPlaces = [q | (l, True) <- argLocals, q <- mayPlacesOf st l] ++ loanPlacesOf cx st (map fst argLocals)
            conflicts = lentAndMovedExcept (\h q -> null (snd h) && forwardedOutside cx args (fst h) q) cx pos st "lent to this call" lentPlaces [l | (l, False) <- argLocals]
            activeBorrowLoans = cxLiveNow cx `Set.union` Set.fromList [local | (local, borrowed) <- argLocals, borrowed]
            argPlaces l = case Map.lookup l (stLoans st) of
                Just (place, _, _) -> place : Map.findWithDefault [] l (stExtraLoans st)
                Nothing -> placesOf st l
            borrowedPlaces = [(index, l, place, mutable) | (index, (arg, borrowed, mutable)) <- zip [1 :: Int ..] (zip3 args lent mut), borrowed, Just l <- [operandLocal arg], place <- argPlaces l]
            mutErrs =
                [ message cx pos (describe cx place ++ " is borrowed by " ++ describeLocal cx ref ++ ", so it cannot be lent for updating to this call: the borrow ends at the last use of " ++ describeLocal cx ref)
                | (a, isMut) <- zip args mut
                , isMut
                , Just l <- [operandLocal a]
                , place <- argPlaces l
                , (ref, lplace, _) <- loanEntries cx st
                , ref `Set.member` activeBorrowLoans
                , ref `Set.notMember` ancestorsOrSelf st [l]
                , ref `notElem` Map.findWithDefault [] l (stReborrowedThrough st)
                , overlaps place lplace
                ] ++
                [ message cx pos (describe cx (if leftMut then leftPlace else rightPlace) ++ " is borrowed by " ++ describeLocal cx (if leftMut then right else left) ++ " in another argument of this call, so it cannot be lent for updating")
                | (leftIndex, left, leftPlace, leftMut) <- borrowedPlaces
                , (rightIndex, right, rightPlace, rightMut) <- borrowedPlaces
                , leftIndex < rightIndex
                , leftMut || rightMut
                , overlaps leftPlace rightPlace
                ]
            mutLocals = [l | (a, True) <- zip args mut, Just l <- [operandLocal a]]
            readAndUpdated =
                [ message cx pos (describe cx h ++ " is lent to this call" ++ (if h == updated then " and lent to it for updating too" else ", and " ++ describe cx updated ++ " is lent to it for updating") ++ ": write clone(" ++ describe cx h ++ ") for the one that is read")
                | m <- mutLocals
                , updated <- argPlaces m
                , (l, True) <- argLocals
                , l `notElem` mutLocals
                , h <- map (readPlace cx st) (mayPlacesOf st l)
                , overlaps h updated
                ]
            heldErrs = concatMap heldConflict (heldMutationPlaces cx st callee args)
            sharedLentErrs = [sharedPathError cx pos l "lent for updating" | l <- nub mutLocals, sharedThrough cx st l]
            heldConflict (arg, owners, mutable, readonly) =
                if null mutable then [message cx pos (describeLocal cx arg ++ " contains update references whose borrowed targets cannot be resolved for this call")]
                else [message cx pos (describe cx target ++ " is borrowed by " ++ describeLocal cx ref ++ ", so it cannot be lent for updating to this call: the borrow ends at the last use of " ++ describeLocal cx ref)
                     | target <- mutable, (ref, place, _) <- loanEntries cx st, ref `Set.member` activeBorrowLoans, overlaps target place
                     , not (mutableHolderLoan cx st ref target || ref `elem` owners && target `notElem` readonly)]
            -- (a forwarded pack is followed by the bounds of the part forwarded: an element outside bounds written as numbers,
            -- which are those of every copy, is not given to the call, so its moves, its loans and the other arguments of the
            -- call that move it do not stop the forward)
            outside = forwardedOutside cx args
            (st', errs) = foldl' (\acc (l, steps, role) -> accessExcept (outside l) cx pos acc (l, steps, role)) (st, []) ([(l, [], Read) | Just l <- [operandLocal callee]] ++ [(l, [], if b then Read else Consume) | (l, b) <- argLocals])
            forwarded = [l | (l, False) <- argLocals, isPackRoot cx l]
            stMarked = st'{stMoved = foldl' (\m l -> Map.adjust (\(p, _) -> (p, Just forwardedMark)) (l, []) m) (stMoved st') forwarded}
            -- (a call of a function whose body is checked here leaves what the caller's holders hold as it was)
            returnedFields = if storingCallee (cxProgram cx) callName then returnedArgumentLoans cx stMarked callee args lent mut else stMarked
            defined = (define cx returnedFields dest []){stLoans = Map.delete dest (stLoans returnedFields), stExtraLoans = Map.delete dest (stExtraLoans returnedFields), stFieldLoans = Map.filterWithKey (\(owner, _) _ -> owner /= dest) (stFieldLoans returnedFields), stConst = Map.delete dest (stConst returnedFields)}
            -- (a result that is a reference is a borrow of a place of one of the arguments it is from, made here)
            declared = resultFromArgs cx returnedFields callee args
            resultType = typeOf cx dest
            defaultSources = [(a, b) | (a, b) <- zip args lent, Just l <- [operandLocal a], b || mayHoldReference (cxProgram cx) (typeOf cx l)]
            -- The elaborator's from annotation describes ordinary references, not permission slots.
            sources = [(a, True) | a <- declared] ++
                (if null declared && mayHoldReference (cxProgram cx) resultType || holdsPermissionReferences (cxProgram cx) resultType
                    then defaultSources else [])
            resultPlaces = resultSourcePlaces returnedFields sources
            loaned = case resultPlaces of
                [] -> defined
                place : more | (case typeOf cx dest of TRef{} -> True; TMutRef{} -> True; _ -> False) -> defined{stLoans = Map.insert dest (place, case typeOf cx dest of TMutRef _ -> True; _ -> False, pos) (stLoans defined), stExtraLoans = if null more then Map.delete dest (stExtraLoans defined) else Map.insert dest more (stExtraLoans defined)}
                places | mayHoldReference (cxProgram cx) (typeOf cx dest) -> defined{stLoans = Map.delete dest (stLoans defined), stExtraLoans = Map.insert dest places (stExtraLoans defined)}
                _ -> defined{stLoans = Map.delete dest (stLoans defined), stExtraLoans = Map.delete dest (stExtraLoans defined)}
            -- (a result that holds references: each reference field of it is to one of the same places)
            windowed = case (refFieldNames cx (typeOf cx dest), resultPlaces) of
                (fields@(_ : _), places@(_ : _)) -> loaned{stFieldLoans = foldl' (\m f -> Map.insert (dest, f) places m) (Map.filterWithKey (\(root, _) _ -> root /= dest) (stFieldLoans loaned)) fields, stExtraLoans = Map.insert dest places (stExtraLoans loaned)}
                _ -> loaned
            readErrs = concat [suspendedReads cx pos st dest r | Just r <- map operandLocal args, isReference cx r] ++ placeReads cx pos st [dest] [(l, [], True) | (l, lentArg) <- [(l, True) | Just l <- [operandLocal callee]] ++ argLocals, lentArg || isCopy cx l]
            parented = windowed{stParents = case [l | (a, _) <- sources, Just l <- [operandLocal a], l /= dest] of
                [] -> Map.delete dest (stParents windowed)
                from -> Map.insert dest (nub from) (stParents windowed)}
            boundary = boundaryHolders cx st callName args lent mut
            -- (what a holder of the caller's holds is the caller's references, which the call may move about in it too)
            callersHolderErrs = take 1
                [ message cx pos ("this call may store a reference to " ++ describeHeld cx (head (filter (/= incomingRoot) places ++ [incomingRoot])) ++ " through " ++ describeHolder cx holder ++ ", which is the caller's: return the value that holds it instead")
                | (holder, _, places) <- boundary
                , callersPlace cx st (holder, [])
                ]
            storing = [(holder, from, places) | (holder, from, places@(_ : _)) <- boundary, holder /= dest, not (callersPlace cx st (holder, []))]
            stored = foldl' (\acc (holder, from, places) -> acc{stParents = Map.insertWith (flip unionPlaces) holder from (stParents acc), stExtraLoans = Map.insertWith (flip unionPlaces) holder places (stExtraLoans acc), stFieldLoans = Map.mapWithKey (\(root, _) ps -> if root == holder then unionPlaces ps places else ps) (stFieldLoans acc)}) parented storing
            -- (a result that is one known place of what it is from is that place, of the state the call left)
            declaredPlaces = resultSourcePlaces returnedFields [(a, True) | a <- declared]
            exactResult = case typeOf cx dest of
                TRef target | Just place <- exactCandidate cx target declaredPlaces -> stored{stExact = Map.insert dest place (stExact stored)}
                TMutRef target | Just place <- exactCandidate cx target declaredPlaces -> stored{stExact = Map.insert dest place (stExact stored)}
                _ -> stored
            disturbed = take 1 (viewsDisturbed cx pos st' [dest] "is given another value" (dest, []) ++ concatMap (\l -> concatMap (viewsDisturbed cx pos st' [dest] "is lent for updating") (argPlaces l)) mutLocals)
            callName = knownCallee st callee
            foreignCall = [message cx pos (drop 7 name ++ " is an extern fn and gives a value that can hold a reference") | Just name <- [callName], "extern " `isPrefixOf` name, mayHoldReference (cxProgram cx) (typeOf cx dest)]
            foreignBlock = [message cx pos (drop 7 name ++ " is an extern fn and cannot accept a Block that may hold a reference") | Just name <- [callName], "extern " `isPrefixOf` name, any (maybe False (foreignBlockType cx . typeOf cx) . operandLocal) args]
            -- (a generic call's result holds what its arguments lend and hold, which may be nothing: a generic body makes no reference of its own)
            unsourced = [message cx pos ("the loans of " ++ describeLocal cx dest ++ " are not modelled: the call gives a value that can hold a reference and is given nothing it could hold or borrow") | null sources, mayHoldReference (cxProgram cx) (typeOf cx dest), not (genericCallee (cxProgram cx) callName)]
         in (hold cx pos exactResult dest [], take 1 conflicts ++ take 1 readAndUpdated ++ errs ++ mutErrs ++ heldErrs ++ sharedLentErrs ++ readErrs ++ callersHolderErrs ++ disturbed ++ foreignCall ++ foreignBlock ++ externValues cx pos args ++ unsourced ++ lost cx pos st' dest)
    -- (what a function returns is given to its caller, and a permission it has not used by then is lost)
    Return ->
        let (st', errs) = if Local 0 `Map.member` fnLocals (cxFn cx) then accessAll [(Local 0, [], Consume)] else (st, [])
            ownReturned = take 1
                [ message cx pos ("the value returned holds a reference to " ++ describe cx place ++ ", which is " ++ fnName (cxFn cx) ++ "'s own and ends with the call")
                | let dest = Local 0
                , dest `Map.member` fnLocals (cxFn cx)
                , mayHoldReference (cxProgram cx) (typeOf cx dest)
                , place <- nub (maybe [] (\(q, _, _) -> [q]) (Map.lookup dest (stLoans st)) ++ Map.findWithDefault [] dest (stExtraLoans st) ++ concat [ps | ((root, _), ps) <- Map.toList (stFieldLoans st), root == dest])
                , not (callersPlace cx st place)
                ]
         in (st', errs ++ ownReturned ++ [message cx pos (unused cx st' q given) | (q, given) <- Map.toList (stHeld st')])
    Goto _ -> (st, [])
    Unreachable -> (st, [])
  where
    accessAll as = foldl' (access cx pos) (st, []) as

-- Whether a value of the type may hold a reference: yes for a type the checker cannot see into (no declaration, an
-- unsolved type variable); no for a type parameter in its own generic body, which holds no reference to that body's
-- places, and for a function value, which captures nothing yet
mayHoldReference :: Program -> Type -> Bool
mayHoldReference = referenceReach AnyReference

mayHoldUpdate :: Program -> Type -> Bool
mayHoldUpdate = referenceReach UpdateReference

holdsPermissionReferences :: Program -> Type -> Bool
holdsPermissionReferences = referenceReach SlotReference

data ReferenceReach = AnyReference | UpdateReference | SlotReference
    deriving (Eq, Ord)

referenceReach :: ReferenceReach -> Program -> Type -> Bool
referenceReach query program = go query Set.empty
  where
    go reach seen ty = case ty of
        TRef inner -> reach == AnyReference || child inner
        TMutRef inner -> reach /= SlotReference || child inner
        TVar _ -> True
        TArrayOf t _ -> child t
        TUninit t -> child t
        TBlock t -> go (if reach == SlotReference then AnyReference else reach) seen t
        TNamed base args -> named reach seen (instanceName base args) (loanDeclaration program base args) builtinElement
          where
            builtinElement = case ty of TList t -> Just t; TBox t -> Just t; _ -> Nothing
        TVariant v -> case ownerOf program v of
            Just n -> named reach seen n (Map.lookup n (progTypes program)) Nothing
            Nothing -> True
        TParam _ -> False
        TFn _ _ -> False
        TFnContract _ _ _ -> False
        TBoxedClosure{} -> True
        TForall _ _ _ -> False
        TAddr _ -> False
        TInt -> False
        TByte -> False
        TBool -> False
        TWord _ _ -> False
      where
        child = go reach seen
    named reach seen name decl builtinElement
        | Set.member (reach, name) seen = False
        | otherwise = case decl of
            Just (StructDecl fields) -> any (child . snd) fields
            Just (EnumDecl variants) -> any (child . snd) (concatMap snd variants)
            Nothing -> maybe True child builtinElement
      where
        child = go reach (Set.insert (reach, name) seen)

loanDeclaration :: Program -> Name -> [Arg] -> Maybe TypeDecl
loanDeclaration program base args =
    Map.lookup (instanceName base args) types <|> instantiated <|> Map.lookup base types
  where
    types = progTypes program
    instantiated = do
        (params, fields) <- Map.lookup base (progGenerics program) <|> tupleGeneric base
        StructDecl <$> instanceFields params args fields

indirectParameterTypes :: Cx -> Operand -> Maybe [Type]
indirectParameterTypes cx callee = do
    local <- operandLocal callee
    case typeOf cx local of
        TFn args _ -> Just args
        TFnContract args _ _ -> Just args
        _ -> Nothing

-- Which of the arguments of a call are lent: the parameters that the function declares as such, or the ones that the type of a function value marks
lentArguments :: Cx -> Operand -> Int -> [Bool]
lentArguments cx callee count = case callee of
    Const (CFn name) | Just f <- Map.lookup name (progFunctions (cxProgram cx)) -> [p `elem` fnBorrowed f | p <- fnParams f]
    _ | Just args <- indirectParameterTypes cx callee -> map isRef args
    _ -> replicate count False
  where
    isRef (TRef _) = True
    isRef (TMutRef _) = True
    isRef _ = False

referenceBounds :: St -> [Place] -> [Place]
referenceBounds st start = nub (start ++ reachable Set.empty start)
  where
    reachable seen [] = Set.toList seen
    reachable seen (place@(owner, _) : rest)
        | place `Set.member` seen = reachable seen rest
        | otherwise = reachable (Set.insert place seen) (contents owner ++ rest)
    contents owner = Map.findWithDefault [] owner (stExtraLoans st) ++ concat [places | ((root, _), places) <- Map.toList (stFieldLoans st), root == owner]

returnedArgumentLoans :: Cx -> St -> Operand -> [Operand] -> [Bool] -> [Bool] -> St
returnedArgumentLoans cx initial callee args borrowed mutable = foldl' update initial receivers
  where
    roots local = case Map.lookup local (stLoans initial) of
        Just (place, _, _) -> place : Map.findWithDefault [] local (stExtraLoans initial)
        Nothing -> placesOf initial local
    references local = Map.findWithDefault [] local (stExtraLoans initial) ++ concat [places | ((owner, _), places) <- Map.toList (stFieldLoans initial), owner == local]
    sources = referenceBounds initial (concat [references local ++ if isBorrowed then roots local else [] | (arg, isBorrowed) <- zip args borrowed, Just local <- [operandLocal arg]])
    direct = [(owner, path, unref (typeOf cx local)) | (arg, isMutable) <- zip args mutable, isMutable, Just local <- [operandLocal arg], referenceContents cx (unref (typeOf cx local)), (owner, path) <- roots local]
    contained = [(owner, path, referent) | (arg, owners, _, _) <- heldMutationPlaces cx initial callee args, object <- nub (arg : owners), (field, fieldTy) <- referenceFields cx (typeOf cx object), referent <- mutableReferenceReferents cx fieldTy, (owner, path) <- Map.findWithDefault [] (object, field) (stFieldLoans initial)]
    sequences = [(owner, path, referent) | (arg, owners, _, _) <- heldMutationPlaces cx initial callee args, object <- nub (arg : owners), null (referenceFields cx (typeOf cx object)), referent <- mutableReferenceReferents cx (unref (typeOf cx object)), (owner, path) <- Map.findWithDefault [] object (stExtraLoans initial)]
    receivers = nub (direct ++ contained ++ sequences)
    unref (TRef inner) = inner
    unref (TMutRef inner) = inner
    unref other = other
    update state (owner, path, referent) =
        let fields = case path of SField _ field : _ -> [(field, Nothing)]; [] -> [(field, Just fieldTy) | (field, fieldTy) <- referenceFields cx referent, field `elem` refFieldNames cx referent]; _ -> []
            add incoming old = nub (incoming ++ old)
            received = [(field, maybe sources (storeable sources) fieldTy) | (field, fieldTy) <- fields]
            fieldLoans = foldl' (\out (field, places) -> Map.insertWith add (owner, field) places out) (stFieldLoans state) received
            extras = Map.insertWith add owner (if null fields || any (\(_, fieldTy) -> fieldTy == Nothing) fields then sources else nub (concatMap snd received)) (stExtraLoans state)
         in state{stFieldLoans = fieldLoans, stExtraLoans = extras}
    -- (a field holding references to U can only be given places of a U: a source that cannot hold one is not one of its
    -- places, and a source holding some is given as those places, when that can be told completely)
    storeable places fieldTy = case pointeeTypes cx fieldTy of
        Just pointees@(_ : _) -> nub (concatMap (narrowTo pointees) places)
        _ -> places
    -- (only a whole local the function declares is narrowed, to the places of its own storage that may be a U; what its
    -- references are to are other sources)
    narrowTo pointees place@(root, []) | Map.member root (fnLocals (cxFn cx)) = case mapM (\pointee -> fieldPaths False (progTypes (cxProgram cx)) pointee (typeOf cx root)) pointees of
        Just found -> nub [(root, map (uncurry SField) path) | path <- concat found]
        Nothing -> [place]
    narrowTo _ place = [place]

mutableReferenceReferents :: Cx -> Type -> [Type]
mutableReferenceReferents cx = go Set.empty
  where
    go seen ty = case ty of
        TMutRef inner | referenceContents cx inner -> [inner]
        TRef inner -> go seen inner
        TList inner -> go seen inner
        TBox inner -> go seen inner
        TArrayOf inner _ -> go seen inner
        TUninit inner -> go seen inner
        TNamed name args -> descend (instanceName name args) ty seen
        TVariant name -> descend name ty seen
        _ -> []
    descend key ty seen = if key `Set.member` seen then [] else concat [go (Set.insert key seen) fieldTy | (_, fieldTy) <- referenceFields cx ty]

mutableHolderLoan :: Cx -> St -> Local -> Place -> Bool
mutableHolderLoan cx st owner target = hasUpdate && not hasRead
  where
    fieldTypes = case typeOf cx owner of TRef{} -> []; TMutRef{} -> []; ty -> referenceFields cx ty
    refers field = target `elem` Map.findWithDefault [] (owner, field) (stFieldLoans st)
    hasUpdate = any (\(field, ty) -> referenceQualifiers cx ty == Set.singleton True && refers field) fieldTypes
    hasRead = any (\(field, ty) -> Set.member False (referenceQualifiers cx ty) && refers field) fieldTypes

heldMutationPlaces :: Cx -> St -> Operand -> [Operand] -> [(Local, [Local], [Place], [Place])]
heldMutationPlaces cx st callee args =
    [ (local, owners, mutable, readonly)
    | (arg, ty) <- zip args parameterTypes, referenceContentsBy True cx (unref ty), Just local <- [operandLocal arg]
    , let objects = nub ((local, []) : placesOf st local ++ case Map.lookup local (stLoans st) of Just (place, _, _) -> place : Map.findWithDefault [] local (stExtraLoans st); Nothing -> [])
          owners = nub [owner | (owner, path) <- objects, null path]
          mutable = nub (concatMap (fieldTargets True) objects)
          readonly = nub (concatMap (fieldTargets False) objects)
    ]
  where
    program = cxProgram cx
    parameters fn = [localType decl | param <- fnParams fn, Just decl <- [Map.lookup param (fnLocals fn)]]
    parameterTypes = case callee of
        Const (CFn name) -> maybe [] parameters (Map.lookup name (progFunctions program))
        _ -> case operandLocal callee >>= (`Map.lookup` stFnAlias st) >>= (`Map.lookup` progFunctions program) of
            Just fn -> parameters fn
            Nothing -> fromMaybe [] (indirectParameterTypes cx callee)
    unref (TRef inner) = inner
    unref (TMutRef inner) = inner
    unref other = other
    fields = referenceFields cx
    fieldTargets wanted (owner, path) = case path of
        SField _ field : _ -> Map.findWithDefault [] (owner, field) (stFieldLoans st)
        _ ->
            let matching = [(field, fieldTy) | (field, fieldTy) <- fields (typeOf cx owner), referenceContentsBy True cx fieldTy == wanted]
                known = concat [refs | (field, _) <- matching, Just refs <- [Map.lookup (owner, field) (stFieldLoans st)]]
             in if null known && null (fields (typeOf cx owner)) && (wanted || Set.member False (referenceQualifiers cx (unref (typeOf cx owner))))
                then Map.findWithDefault [] owner (stExtraLoans st)
                else known

-- Which of the arguments of a call are lent for updating: the parameters the function declares &mut, or the ones
-- that the type of a function value marks
mutArguments :: Cx -> Operand -> Int -> [Bool]
mutArguments cx callee count = case callee of
    Const (CFn name) | Just f <- Map.lookup name (progFunctions (cxProgram cx)) -> [case Map.lookup p (fnLocals f) of Just d -> maybe False (`elem` specMutParams (fnSpec f)) (localName d); Nothing -> False | p <- fnParams f]
    _ | Just args <- indirectParameterTypes cx callee -> map isMutRef args
    _ -> replicate count False
  where
    isMutRef (TMutRef _) = True
    isMutRef _ = False

-- Explicit from bounds and lent arguments can contribute storage. By-value
-- arguments can contribute their references, not their own storage.
resultSourcePlaces :: St -> [(Operand, Bool)] -> [Place]
resultSourcePlaces st sources = referenceBounds st (concatMap argumentPlaces sources)
  where
    argumentPlaces (operand, borrowed) = case operandLocal operand of
        Just l ->
            let carried = Map.findWithDefault [] l (stExtraLoans st) ++ concat [ps | ((root, _), ps) <- Map.toList (stFieldLoans st), root == l]
                storage = case Map.lookup l (stLoans st) of
                    Just (place, _, _) -> [place]
                    Nothing | borrowed -> mayPlacesOf st l
                    Nothing -> []
             in storage ++ carried
        Nothing -> []

knownCallee :: St -> Operand -> Maybe Name
knownCallee st operand = case operand of
    Const (CFn name) -> Just name
    Const _ -> Nothing
    Copy l -> Map.lookup l (stFnAlias st)
    Move l -> Map.lookup l (stFnAlias st)

foreignBlockType :: Cx -> Type -> Bool
foreignBlockType cx ty = case ty of
    TRef inner -> foreignBlockType cx inner
    TMutRef inner -> foreignBlockType cx inner
    TBlock inner -> mayHoldReference (cxProgram cx) inner
    _ -> False

externValues :: Cx -> Pos -> [Operand] -> [String]
externValues cx pos operands = concat
    [ case Map.lookup name (progFunctions (cxProgram cx)) of
        Nothing -> [refusal name]
        Just fn
            | maybe True (mayHoldReference (cxProgram cx)) (fnReturns fn) -> [refusal name]
            | any (foreignBlockType cx . localType) [d | l <- fnParams fn, Just d <- [Map.lookup l (fnLocals fn)]] ->
                [message cx pos (drop 7 name ++ " is an extern fn that accepts a Block that may hold a reference, so it cannot be used as a value")]
            | otherwise -> []
    | Const (CFn name) <- operands, "extern " `isPrefixOf` name
    ]
  where
    refusal name = message cx pos (drop 7 name ++ " is an extern fn that gives a value that can hold a reference, so it cannot be used as a value")

callersPlace :: Cx -> St -> Place -> Bool
callersPlace cx st (r, _) = (r, []) == incomingRoot || (r `elem` fnParams (cxFn cx) && (isReference cx r || r `Set.member` cxLent cx)) || (isReference cx r && not (Map.member r (stLoans st)))

-- The arguments given for the parameters a call's result is from
resultFromArgs :: Cx -> St -> Operand -> [Operand] -> [Operand]
resultFromArgs cx st callee args = case calleeName of
    Just name | Just f <- Map.lookup name (progFunctions (cxProgram cx)) ->
        let names = [maybe Nothing localName (Map.lookup p (fnLocals f)) | p <- fnParams f]
         in [args !! i | (i, Just n) <- zip [0 ..] names, n `elem` specFrom (fnSpec f), i < length args]
    _ -> []
  where
    calleeName = case callee of
        Const (CFn name) -> Just name
        Copy l -> Map.lookup l (stFnAlias st)
        Move l -> Map.lookup l (stFnAlias st)
        _ -> Nothing

-- Each holder a call's arguments reach that the callee may store into, with the arguments and places it may take (MIR.md,
-- Moves, "Function boundaries")
boundaryHolders :: Cx -> St -> Maybe Name -> [Operand] -> [Bool] -> [Bool] -> [(Local, [Local], [Place])]
boundaryHolders cx st callName args lent mut
    | not (storingCallee program callName) = []
    | otherwise = holders
  where
    program = cxProgram cx
    argLocals = [(i, l, isLent, isMut) | (i, a, isLent, isMut) <- zip4 [0 :: Int ..] args (lent ++ repeat False) (mut ++ repeat False), Just l <- [operandLocal a]]
    loansOf l = maybe [] (\(place, _, _) -> [place]) (Map.lookup l (stLoans st)) ++ Map.findWithDefault [] l (stExtraLoans st)
    ownPlaces l = case Map.lookup l (stLoans st) of
        Just (place, _, _) -> place : Map.findWithDefault [] l (stExtraLoans st)
        Nothing -> mayPlacesOf st l
    held l = Map.findWithDefault [] l (stExtraLoans st) ++ concat [places | ((root, _), places) <- Map.toList (stFieldLoans st), root == l]
    -- (an argument lent, or a reference, is a place the body can keep a reference to; one given by value keeps only what it holds)
    starts l isLent = if isLent || isReference cx l then ownPlaces l else held l
    stored = referenceBounds st (concat [starts l isLent | (_, l, isLent, _) <- argLocals])
    sources = nub [l | (_, l, isLent, _) <- argLocals, not (null (starts l isLent))]
    calleeParams = case callName >>= (`Map.lookup` progFunctions program) of
        Just f -> [localType <$> Map.lookup p (fnLocals f) | p <- fnParams f]
        Nothing -> []
    paramType i = if i < length calleeParams then calleeParams !! i else Nothing
    isMutRefType ty = case ty of
        TMutRef _ -> True
        _ -> False
    updates i l isMut = isMut || (isMutRefType (typeOf cx l) && maybe True isMutRefType (paramType i))
    holderRoot r = r == fst incomingRoot || mayHoldReference program (typeOf cx r)
    -- (only an update reference can be written through: nothing reached through a shared one is a holder, MIR.md "Shared paths")
    heldHolders r = if r /= fst incomingRoot && mayHoldUpdate program (typeOf cx r) then map fst (loansOf r) else []
    direct = nub [(root, Just l) | (i, l, _, isMut) <- argLocals, updates i l isMut, (root, _) <- ownPlaces l, holderRoot root]
    byValue = [l | (_, l, isLent, _) <- argLocals, not isLent, not (isReference cx l), mayHoldUpdate program (typeOf cx l)]
    reached = go Set.empty (concatMap (heldHolders . fst) direct ++ concat [map fst (loansOf l) | l <- byValue])
      where
        go _ [] = []
        go seen (r : rest)
            | Set.member r seen = go seen rest
            | holderRoot r = r : go (Set.insert r seen) (rest ++ heldHolders r)
            | otherwise = go (Set.insert r seen) rest
    holders =
        [ (holder, [l | l <- sources, l /= holder, Just l /= via], [place | place <- stored, place /= (holder, []), maybe True (\l -> place `notElem` ownPlaces l) via])
        | (holder, via) <- direct ++ [(r, Nothing) | r <- nub reached, r `notElem` map fst direct]
        ]

-- Whether a call of the function may store what it is given into what its arguments reach: a function this check sees the body
-- of at the call's types stores nothing (a store into its caller's storage is refused in it), any other one may
storingCallee :: Program -> Maybe Name -> Bool
storingCallee program name = case name of
    Just n
        | Just (_, targs) <- Map.lookup n (progInstances program) -> any (mayHoldReference program) [t | ArgType t <- targs]
        | genericCallee program name -> True
        | "<$param " `isPrefixOf` n -> True
        | otherwise -> not (Map.member n (progFunctions program))
    Nothing -> True

-- A generic function, or a copy of one with bounds or a pack
genericCallee :: Program -> Maybe Name -> Bool
genericCallee program name = case name of
    Just n -> Map.member n (progInstances program) || maybe False (not . null . fnTypeParams) (Map.lookup n (progFunctions program))
    Nothing -> False

describeHeld :: Cx -> Place -> String
describeHeld cx place = if place == incomingRoot then "what a parameter's references are to" else describe cx place

describeHolder :: Cx -> Local -> String
describeHolder cx holder = if (holder, []) == incomingRoot then "a reference a parameter holds" else describeLocal cx holder

-- (a write through a reference read out of a value names where it was read from)
describeStoreRoot :: Cx -> St -> Local -> String
describeStoreRoot cx st root = case placesOf st root of
    [place] | place /= (root, []), Nothing <- localSource cx root -> describe cx place
    _ -> describeLocal cx root

-- The reference fields of a struct type, which a value of it holds loans in
referenceFields :: Cx -> Type -> [(Variable, Type)]
referenceFields cx ty = case ty of
    TRef inner -> referenceFields cx inner
    TMutRef inner -> referenceFields cx inner
    TList{} -> []
    TBox{} -> []
    TArrayOf{} -> []
    TNamed name tys -> case Map.lookup (instanceName name tys) (progTypes (cxProgram cx)) of Just (StructDecl fields) -> fields; Just (EnumDecl variants) -> concatMap snd variants; _ -> []
    TVariant name -> concat [fields | EnumDecl variants <- Map.elems (progTypes (cxProgram cx)), (variant, fields) <- variants, variant == name]
    _ -> []

referenceQualifiers :: Cx -> Type -> Set.Set Bool
referenceQualifiers cx = go Set.empty
  where
    go seen ty = case ty of
        TRef{} -> Set.singleton False
        TMutRef{} -> Set.singleton True
        TList inner -> go seen inner
        TBox inner -> go seen inner
        TArrayOf inner _ -> go seen inner
        TUninit inner -> go seen inner
        TNamed name tys -> let key = instanceName name tys in if Set.member key seen then Set.empty else Set.unions [go (Set.insert key seen) fieldTy | (_, fieldTy) <- referenceFields cx ty]
        TVariant name -> if Set.member name seen then Set.empty else Set.unions [go (Set.insert name seen) fieldTy | (_, fieldTy) <- referenceFields cx ty]
        _ -> Set.empty

referenceContents :: Cx -> Type -> Bool
referenceContents = referenceContentsBy False

referenceContentsBy :: Bool -> Cx -> Type -> Bool
referenceContentsBy mutableOnly cx = go Set.empty
  where
    go seen ty = case ty of
        TRef inner -> not mutableOnly || go seen inner
        TMutRef{} -> True
        TList inner -> go seen inner
        TBox inner -> go seen inner
        TArrayOf inner _ -> go seen inner
        TUninit inner -> go seen inner
        TBlock inner -> not mutableOnly && go seen inner
        TNamed name tys -> let key = instanceName name tys in not (Set.member key seen) && any (go (Set.insert key seen) . snd) (referenceFields cx ty)
        TVariant name -> not (Set.member name seen) && any (go (Set.insert name seen) . snd) (referenceFields cx ty)
        _ -> False

refFieldNames :: Cx -> Type -> [Variable]
refFieldNames _ TRef{} = []
refFieldNames _ TMutRef{} = []
refFieldNames cx ty = [field | (field, fieldTy) <- referenceFields cx ty, referenceContents cx fieldTy]

-- Messages

localNameOf :: Cx -> Local -> Maybe String
localNameOf cx l = Map.lookup l (fnLocals (cxFn cx)) >>= localName

-- The name that the program gave a local, if it did (a variable or a pattern's name, not a temporary or one that is hidden)
localSource :: Cx -> Local -> Maybe String
localSource cx l = case localNameOf cx l of
    Just name | take 1 name /= "$" -> Just name
    _ -> Nothing

describeLocal :: Cx -> Local -> String
describeLocal cx l = case localNameOf cx l of
    Just ('$' : 'l' : 'i' : 's' : 't' : ' ' : _) -> "the list of the for loop"
    Just name | take 1 name /= "$" -> name
    _ -> "the value in " ++ show l

describe :: Cx -> Place -> String
describe cx (l, SField "$pack" k : steps) = "get(" ++ describeLocal cx l ++ ", " ++ k ++ ")" ++ describe cx (l, steps) `withoutRoot` describeLocal cx l
  where
    withoutRoot text root = drop (length root) text
describe cx (l, SElem _ : steps) | TParam p <- typeOf cx l, ".." `isPrefixOf` p = "get(" ++ describeLocal cx l ++ ", i)" ++ drop (length (describeLocal cx l)) (describe cx (l, steps))
describe cx (l, steps) = describeLocal cx l ++ concat [part s | s <- steps]
  where
    part (SField _ field) = "." ++ field
    part (SElem mi) = maybe "[..]" (\i -> "[" ++ show i ++ "]") mi
    part SSlot = "[slot]"
    part STag = ""
    part SDeref = " (through a reference)"

message :: Cx -> Pos -> String -> String
message cx pos text = "in " ++ fnName (cxFn cx) ++ maybe "" (\(line, column) -> ", line " ++ show line ++ ":" ++ show column) pos ++ ": " ++ text

-- A lowered module as the pipeline takes it: its instances completed, its moves checked, the places lowering wrote
-- taken out, and the stubs of imported functions dropped. (That the program is well formed is checked by the pipeline
-- on what is lowered, with the checker written in Tersus (MirHousekeeping): it is not checked here, so that the
-- checker and the eraser can themselves be lowered to be made from the seed. The stubs stay in the program for the
-- check of moves, so a call of one is seen with its signature; they are not checked themselves.)
finishLowered :: Lowered -> Result Program String
finishLowered lowered =
    case checkMovesExcluding (lowCopies lowered) (lowLinear lowered) (lowDrops lowered) (lowStubs lowered) completed of
        [] ->
            let stripped = stripPositions completed
             in Ok stripped{progFunctions = Map.filterWithKey (\name _ -> name `Set.notMember` lowStubs lowered) (progFunctions stripped)}
        errors -> Error (intercalate "\n" (take 100 (map ("Move error: " ++) errors) ++ ["... and " ++ show (length errors - 100) ++ " more" | length errors > 100]))
  where
    completed = completeInstances (lowProgram lowered)

-- A thread shares nothing with the program that starts it (lib/thread.tersus): each copy of the thread library's spawn
-- is refused when the closure it is given, or the Thread it gives, can hold a reference
checkSpawns :: Set Name -> Program -> Result Program String
checkSpawns library program
    | spawn `Set.notMember` library = Ok program
    | otherwise = case concatMap refusals copies of
        [] -> Ok program
        errors -> Error (intercalate "\n" (map ("Move error: " ++) errors))
  where
    spawn = "<Thread>::spawn"
    copies = [fn | fn <- Map.elems (progFunctions program), (spawn ++ "[") `isPrefixOf` fnName fn]
    refusals fn =
        [ "Thread::spawn is given " ++ describe ty ++ ": a thread cannot hold a reference (capture by value with move fn)"
        | [p] <- [fnParams fn], Just d <- [Map.lookup p (fnLocals fn)], let ty = localType d, mayHoldReference program ty ]
            ++ [ "Thread::spawn gives a " ++ renderTypeForName ty ++ ", which can hold a reference, and a thread's result cannot"
               | Just ty <- [fnReturns fn], mayHoldReference program ty ]
    describe ty = case ty of
        TNamed base args
            | "$closure$" `isPrefixOf` base
            , Just (StructDecl fields) <- Map.lookup (instanceName base args) (progTypes program) ->
                case [field | (field, t) <- fields, mayHoldReference program t] of
                    [] -> "a closure that can hold a reference"
                    borrowed -> "a closure that borrows " ++ intercalate ", " borrowed
        _ -> "a " ++ renderTypeForName ty ++ ", which can hold a reference"

-- The program without the places that lowering wrote into it
stripPositions :: Program -> Program
stripPositions program = program{progFunctions = Map.map strip (progFunctions program), progMain = strip (progMain program)}
  where
    strip fn = fn{fnBlocks = Map.map (\(BasicBlock stmts term) -> BasicBlock (filter (not . position) stmts) term) (fnBlocks fn)}
    position (Ghost _ GhostPosition{}) = True
    position _ = False

maxDepth :: Int
maxDepth = 6
