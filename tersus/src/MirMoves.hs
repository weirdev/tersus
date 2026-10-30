module MirMoves
    ( checkMoves
    , isCopyType
    , stripPositions
    ) where

import Data.List (foldl', isPrefixOf, nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Set (Set)
import qualified Data.Set as Set

import Mir
import MirOwnership (Role (..), isProjection, operandLocal, roles)
import TersusTypes (Name, Type (..), instanceOf, tupleGeneric)

-- A copy of a value is made where the program writes `clone(x)`, and nowhere else: a value that is not `Copy` is moved to where it
-- is wanted, and the local it came from holds nothing after. So a program cannot use it again, and this checks that it does not.
-- It runs on the MIR that lowering makes, before the program is validated (it is cheap, and a program that fails it has no meaning for
-- the passes after it), and `MirOwnership`, which inserted a `Clone` wherever a value was wanted twice, now finds none that the
-- program did not write.
--
-- What the check follows is a *place*: a local and the fields (or the elements of a list) that are followed from it. It keeps the
-- places that have been moved out, along every path, and reports:
--
--   * a use of a place after it was moved (or of a part of it, or of the whole it is a part of), along any path to the use;
--   * a move of an element of a list, which the list still holds: write `clone(get(l, i))`;
--   * a move of a parameter that is lent (`&T`), or of a part of one, which the caller still has;
--   * a local that is lent to a call and moved by the same call.
--
-- A field or an element that is read into a local (`row = get(rows, i)`, `l = t.left`) is a *view* of the place it comes from, so
-- reading it moves nothing, and moving it moves the place. A Copy value is copied wherever it is wanted and is never moved. A
-- value that a call or an operation makes is its own place and has nothing to do with the rest.

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
            TAddr _ -> True
            TUninit t -> not (ownsHeap program t) && go (depth + 1) t
            TArrayOf t _ -> go (depth + 1) t
            TRef t -> go (depth + 1) t
            TNamed n -> declared depth n
            TVariant v -> maybe False (declared depth) (ownerOf program v)
            _ -> False
    declared depth n =
        let base = maybe n fst (instanceOf n)
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
        TNamed n | Set.member n seen -> False
        TNamed n -> declared (Set.insert n seen) n
        TVariant v -> maybe False (declared seen) (ownerOf program v)
        _ -> False
    declared seen n = case Map.lookup n (progTypes program) of
        Just (StructDecl fields) -> any (go seen . snd) fields
        Just (EnumDecl variants) -> any (go seen . snd) (concatMap snd variants)
        Nothing -> False

-- A step from a value to a part of it: a field, an element of a list, the tag of an enum, or a slot of the memory a permission is for
data Step = SField Name String | SElem | STag | SSlot
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
data St = St {stMoved :: Map Place (Pos, Maybe String), stViews :: Map Local (Set Place), stMay :: Map Local (Set Place), stHeld :: Map Place Pos}

emptySt :: St
emptySt = St Map.empty Map.empty Map.empty Map.empty

joinSt :: St -> St -> St
joinSt a b = St (Map.union (stMoved a) (stMoved b)) (Map.intersectionWith Set.union (stViews a) (stViews b)) (Map.unionWith Set.union (stMay a) (stMay b)) (Map.union (stHeld a) (stHeld b))

sameShape :: St -> St -> Bool
sameShape a b = Map.keysSet (stMoved a) == Map.keysSet (stMoved b) && stViews a == stViews b && stMay a == stMay b && Map.keysSet (stHeld a) == Map.keysSet (stHeld b)

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
            TNamed n | maybe n fst (instanceOf n) `Set.member` drops -> []
            TVariant v | Just n <- ownerOf program v, maybe n fst (instanceOf n) `Set.member` drops -> []
            -- (an Uninit of a value that owns something is linear: what it holds is freed only by taking it out)
            TUninit t | ownsHeap program t -> [[]]
            TNamed n | maybe n fst (instanceOf n) `Set.member` linear -> [[]]
            TVariant v | Just n <- ownerOf program v, maybe n fst (instanceOf n) `Set.member` linear -> [[]]
            TNamed n -> declared depth n
            TVariant v -> maybe [] (declared depth) (ownerOf program v)
            _ -> []
    declared depth n = case Map.lookup n (progTypes program) of
        Just (StructDecl fields) -> concat [map (SField n f :) (go (depth + 1) t) | (f, t) <- fields]
        Just (EnumDecl variants) | any (not . null . go (depth + 1) . snd) (concatMap snd variants) -> [[]]
        _ -> []

overlaps :: Place -> Place -> Bool
overlaps (l, a) (m, b) = l == m && (a `isPrefixOf` b || b `isPrefixOf` a)

data Cx = Cx
    { cxProgram :: Program
    , cxCopies :: Set Name
    , cxFn :: Function
    , cxLent :: Set Local
    , cxLinear :: Set Name
    , cxDrops :: Set Name
    , -- the value that a drop is given (`self` of `<T as Drop>::drop`): lent, except for the permissions it holds, which the drop uses
      cxDropSelf :: Maybe Local
    }

typeOf :: Cx -> Local -> Type
typeOf cx l = maybe TInt localType (Map.lookup l (fnLocals (cxFn cx)))

isCopy :: Cx -> Local -> Bool
isCopy cx = isCopyType (cxCopies cx) (cxProgram cx) . typeOf cx

-- The errors of a program: none if it never uses a value that was moved
checkMoves :: Set Name -> Set Name -> Set Name -> Program -> [String]
checkMoves copies linear drops program = concatMap (checkFunction copies linear drops program) (Map.elems (progFunctions program) ++ [progMain program])

checkFunction :: Set Name -> Set Name -> Set Name -> Program -> Function -> [String]
checkFunction copies linear drops program fn = nub (concat [snd (runBlock cx st block) | (b, st) <- Map.toList ins, Just block <- [Map.lookup b (fnBlocks fn)]])
  where
    -- (the drop of a type, `<T as Drop>::drop`, is given the value to free: it only reads what native code frees after it (its fields), and
    -- it has to use the permissions the value holds, which nothing else will)
    dropOf = case (implOwner (fnName fn), fnParams fn) of
        (Just owner, self : _) | " as Drop>::drop" `isSuffixOf'` fnName fn -> Just (owner, self)
        _ -> Nothing
    lent = Set.fromList (fnBorrowed fn ++ [self | Just (_, self) <- [dropOf]])
    cx = Cx program copies fn lent linear drops (snd <$> dropOf)
    -- (a permission given to the function, and not lent, is the function's to use)
    entry = emptySt{stHeld = Map.fromList ([((p, steps), Nothing) | p <- fnParams fn, p `Set.notMember` lent, steps <- linearParts linear drops program (typeOf cx p)] ++ [((self, steps), Nothing) | Just (owner, self) <- [dropOf], steps <- linearParts linear (Set.delete owner drops) program (typeOf cx self), not (null steps)])}
    isSuffixOf' suffix text = reverse suffix == take (length suffix) (reverse text)
    ins = fixpoint (Map.singleton (BlockId 0) entry)
    fixpoint known =
        let outs = [(b, fst (runBlock cx st block)) | (b, st) <- Map.toList known, Just block <- [Map.lookup b (fnBlocks fn)]]
            reached = Map.fromListWith (flip joinSt) [(s, out) | (b, out) <- outs, Just block <- [Map.lookup b (fnBlocks fn)], s <- successors (blockTerminator block)]
            known' = Map.unionWith joinSt known reached
         in if Map.keysSet known' == Map.keysSet known && and (Map.elems (Map.intersectionWith sameShape known known')) then known else fixpoint known'

runBlock :: Cx -> St -> BasicBlock -> (St, [String])
runBlock cx st0 (BasicBlock stmts term) = (st2, reverse errs1 ++ errs2)
  where
    (st1, pos1, errs1) = foldl' step (st0, Nothing, []) stmts
    (st2, errs2) = terminator cx pos1 st1 term
    step (st, pos, errs) s = case s of
        Ghost _ (GhostPosition line column) -> (st, Just (line, column), errs)
        Assign d rv ->
            let (st', es) = assign cx pos st d rv
             in (st', pos, reverse es ++ errs)
        _ -> (st, pos, errs)

-- What an rvalue does with the locals it names: the part of the local, and whether it reads it or takes it
accesses :: Rvalue -> [(Local, [Step], Role)]
accesses rv = case rv of
    ReadField o name field -> [(l, [SField name field], Read) | Just l <- [operandLocal o]]
    IsVariant o _ -> [(l, [STag], Read) | Just l <- [operandLocal o]]
    AsVariant o _ -> [(l, [], Read) | Just l <- [operandLocal o]]
    Unbox o -> [(l, [], Read) | Just l <- [operandLocal o]]
    -- (n copies of x are made of the value that is given, which is moved into them)
    ListOp op [n, x] | op `elem` [NewArray, NewBoxed] -> [(l, [], role) | (o, role) <- [(n, Read), (x, Consume)], Just l <- [operandLocal o]]
    _ -> [(l, [], role) | (o, role) <- roles rv, Just l <- [operandLocal o]]

-- The places a local stands for: those it is a view of, or itself
placesOf :: St -> Local -> [Place]
placesOf st l = case Map.lookup l (stViews st) of
    Just ps | not (Set.null ps) -> Set.toList ps
    _ -> [(l, [])]

assign :: Cx -> Pos -> St -> Local -> Rvalue -> (St, [String])
assign cx pos st0 d rv = (hold cx pos (define cx st1 d view) d view, errs ++ lost cx pos st1 d)
  where
    (st1, errs) = takenApart (foldl' (access cx pos) (st0, []) (if forLoopList then [(l, ps, Read) | (l, ps, _) <- accesses rv] else if tuplePart then [(l, ps, Consume) | (l, ps, _) <- accesses rv] else accesses rv))
    -- (a value of a linear type is used when a function of its own impl takes it apart: reads a field of it, or tests or casts its variant)
    takenApart (st, es) = case rv of
        ReadField o _ _ | Just l <- operandLocal o, ownImpl l -> (consumed st l, es)
        IsVariant o _ | Just l <- operandLocal o, ownImpl l -> (consumed st l, es)
        AsVariant o _ | Just l <- operandLocal o, ownImpl l -> (consumed st l, es)
        _ -> (st, es)
    ownImpl l = case typeOf cx l of
        TNamed n -> owned n
        TVariant v -> maybe False owned (ownerOf (cxProgram cx) v)
        _ -> False
    owned n = let base = maybe n fst (instanceOf n) in base `Set.member` cxLinear cx && implOwner (fnName (cxFn cx)) == Just base
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
        -- (what a Box holds is read through it, and is the Box's when it is taken)
        Unbox o | not (isCopyType (cxCopies cx) (cxProgram cx) ty), Just l <- operandLocal o -> placesOf st1 l
        Use o | forLoopList, Just l <- operandLocal o -> placesOf st1 l
        _ -> []
    sourceLocal r = case r of
        ReadField o _ _ -> operandLocal o
        -- (the value in a slot is a view of the permission, which is the last operand: once the permission is changed or freed, the view is gone)
        ListOp AddrGet os@(_ : _) -> operandLocal (last os)
        ListOp _ (o : _) -> operandLocal o
        _ -> Nothing
    stepOf r = case r of
        ReadField _ name field -> SField name field
        ListOp AddrGet _ -> SSlot
        ListOp UninitGet _ -> SSlot
        _ -> SElem

-- The effect of the use of a part of a local
access :: Cx -> Pos -> (St, [String]) -> (Local, [Step], Role) -> (St, [String])
access cx pos (st, errs) (l, steps, role) = (st', errs ++ useErrs ++ moveErrs)
  where
    places = [(r, ps ++ steps) | (r, ps) <- placesOf st l]
    useErrs = take 1 [message cx pos (movedText q m mpos via) | q <- places, (m, (mpos, via)) <- Map.toList (stMoved st), overlaps q m]
    -- (the text names what the program wrote where the place was moved: the variable that was used, or else the place)
    movedText q m mpos via =
        let written = fromMaybe (describe cx m) via
            label = maybe (describe cx m) (\v -> if v == describe cx m then v else v ++ " (" ++ describe cx m ++ ")") via
         in if q == m
                then label ++ " was moved" ++ at mpos ++ " and cannot be used again: write clone(" ++ written ++ ") where it is moved to keep it"
                else label ++ " was moved" ++ at mpos ++ ", and " ++ describe cx q ++ " is a part of it or has it as a part: write clone(" ++ written ++ ") where it is moved to keep it"
    taking = role == Consume && not (isCopy cx l)
    moveErrs
        | not taking = []
        | otherwise = concatMap moveError (places ++ [(r, ps ++ steps) | Just may <- [Map.lookup l (stMay st)], (r, ps) <- Set.toList may, (r, ps ++ steps) `notElem` places])
    moveError q@(root, ps)
        | permissionPlace q, root `Set.notMember` cxLent cx, Just n <- dropTypeOf root, maybe True (not . ("$struct " `isPrefixOf`)) (localNameOf cx root) =
            [message cx pos ("the permission " ++ named q ++ " is moved out of a value of " ++ n ++ ", which has a drop that would free the memory again: take the value apart, as in " ++ n ++ " { ... } = " ++ describeLocal cx root ++ ";, which uses it up")]
        | SSlot `elem` ps = [message cx pos ("cannot move " ++ named q ++ " out of the memory of a permission or an Uninit, which still holds it: write clone(" ++ fromMaybe (describe cx q) (localSource cx l) ++ ") to copy it, or take it out with Addr::take or Uninit::take")]
        | SElem `elem` ps = [message cx pos ("cannot move " ++ named q ++ " out of a list, which still holds it: write clone(" ++ fromMaybe (describe cx q) (localSource cx l) ++ ") to copy it")]
        | root `Set.member` cxLent cx, permissionPlace q, not (dropsPermission q) = [message cx pos (named q ++ " is a permission in a value that is lent (&T) to this function, which can lend it to an operation (Addr::get) but not use it up")]
        | root `Set.member` cxLent cx, not (dropsPermission q) = [message cx pos (describe cx q ++ " is lent (&T) to this function and can only be read: write clone(" ++ describe cx q ++ ") to get a value of its own")]
        | otherwise = []
    named q = maybe (describe cx q) (\v -> v ++ " (" ++ describe cx q ++ ")") (localSource cx l)
    permissionPlace q = case placeType cx q of
        Just (TBlock _) -> True
        _ -> False
    -- (a permission in the value that a drop is given is the drop's to use, once; one in any other value that is lent is not)
    dropsPermission q@(root, _) = permissionPlace q && Just root == cxDropSelf cx
    dropTypeOf root = case typeOf cx root of
        TNamed n | maybe n fst (instanceOf n) `Set.member` cxDrops cx -> Just (maybe n fst (instanceOf n))
        _ -> Nothing
    st'
        | taking =
            let moved = [q | q@(root, ps) <- places, SElem `notElem` ps, SSlot `notElem` ps, root `Set.notMember` cxLent cx || dropsPermission q]
                -- (a local that is a view of a permission on one path and has one of its own on another uses whichever it has)
                used = moved ++ [q | q@(root, _) <- places, root `Set.member` cxLent cx] ++ [(r, ps ++ steps) | Just may <- [Map.lookup l (stMay st)], (r, ps) <- Set.toList may]
             in st{stMoved = foldl' (\m q -> Map.insert q (pos, localSource cx l) m) (stMoved st) moved, stHeld = Map.filterWithKey (\h _ -> not (any (overlaps h) used)) (stHeld st)}
        | otherwise = st
    at p = maybe "" (\(line, column) -> " at line " ++ show line ++ ":" ++ show column) p

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
        }

terminator :: Cx -> Pos -> St -> Terminator -> (St, [String])
terminator cx pos st term = case term of
    SwitchBool o _ _ -> accessAll [(l, [], Read) | Just l <- [operandLocal o]]
    Call callee args dest _ ->
        let lent = lentArguments cx callee (length args)
            argLocals = [(l, b) | (a, b) <- zip args lent, Just l <- [operandLocal a]]
            conflicts = [message cx pos (describeLocal cx l ++ " is lent to this call and moved by it too: write clone(" ++ describeLocal cx l ++ ") for one of them") | (l, True) <- argLocals, (l', False) <- argLocals, l == l', not (isCopy cx l)]
            (st', errs) = foldl' (access cx pos) (st, []) ([(l, [], Read) | Just l <- [operandLocal callee]] ++ [(l, [], if b then Read else Consume) | (l, b) <- argLocals])
         in (hold cx pos (define cx st' dest []) dest [], errs ++ take 1 conflicts ++ lost cx pos st' dest)
    -- (what a function returns is given to its caller, and a permission it has not used by then is lost)
    Return ->
        let (st', errs) = if Local 0 `Map.member` fnLocals (cxFn cx) then accessAll [(Local 0, [], Consume)] else (st, [])
         in (st', errs ++ [message cx pos (unused cx st' q given) | (q, given) <- Map.toList (stHeld st')])
    _ -> (st, [])
  where
    accessAll as = foldl' (access cx pos) (st, []) as

-- Which of the arguments of a call are lent: the parameters that the function declares as such, or the ones that the type of a function value marks
lentArguments :: Cx -> Operand -> Int -> [Bool]
lentArguments cx callee count = case callee of
    Const (CFn name) | Just f <- Map.lookup name (progFunctions (cxProgram cx)) -> [p `elem` fnBorrowed f | p <- fnParams f]
    Copy l | Just (TFn args _) <- Map.lookup l types -> map isRef args
    Move l | Just (TFn args _) <- Map.lookup l types -> map isRef args
    _ -> replicate count False
  where
    types = Map.map localType (fnLocals (cxFn cx))
    isRef (TRef _) = True
    isRef _ = False

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
describe cx (l, steps) = describeLocal cx l ++ concat [part s | s <- steps]
  where
    part (SField _ field) = "." ++ field
    part SElem = "[..]"
    part SSlot = "[slot]"
    part STag = ""

message :: Cx -> Pos -> String -> String
message cx pos text = "in " ++ fnName (cxFn cx) ++ maybe "" (\(line, column) -> ", line " ++ show line ++ ":" ++ show column) pos ++ ": " ++ text

-- The program without the places that lowering wrote into it
stripPositions :: Program -> Program
stripPositions program = program{progFunctions = Map.map strip (progFunctions program), progMain = strip (progMain program)}
  where
    strip fn = fn{fnBlocks = Map.map (\(BasicBlock stmts term) -> BasicBlock (filter (not . position) stmts) term) (fnBlocks fn)}
    position (Ghost _ GhostPosition{}) = True
    position _ = False

maxDepth :: Int
maxDepth = 6
