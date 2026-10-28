module MirMoves
    ( checkMoves
    , isCopyType
    , stripPositions
    ) where

import Data.List (foldl', isPrefixOf, nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Mir
import MirOwnership (Role (..), isProjection, operandLocal, roles)
import TersusTypes (Name, Type (..), instanceOf)

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

-- The Copy types are Int, Byte, Bool, functions, an array of a Copy type, and a struct or an enum that declares `impl Copy` (and
-- all of whose fields are Copy, for an instance of a struct with parameters). A list or a Box never is.
isCopyType :: Set Name -> Program -> Type -> Bool
isCopyType copies program = go (0 :: Int)
  where
    go depth ty
        | depth > 32 = False
        | otherwise = case ty of
            TInt -> True
            TByte -> True
            TBool -> True
            TFn{} -> True
            TArrayOf t _ -> go (depth + 1) t
            TRef t -> go (depth + 1) t
            TNamed n -> declared depth n
            TVariant v -> maybe False (declared depth) (ownerOf program v)
            _ -> False
    declared depth n =
        let base = maybe n fst (instanceOf n)
         in base `Set.member` copies && fieldsCopy depth n
    fieldsCopy depth n = case Map.lookup n (progTypes program) of
        Just (StructDecl fields) -> all (go (depth + 1) . snd) fields
        Just (EnumDecl variants) -> all (go (depth + 1) . snd) (concatMap snd variants)
        Nothing -> True

-- A step from a value to a part of it
data Step = SField Name String | SElem | STag
    deriving (Eq, Ord)

type Place = (Local, [Step])

type Pos = Maybe (Int, Int)

-- Along the paths that reach a point: the places that may have been moved out (and where), and the places that a local is a view of
-- on every path (a local that is a view on one path and not on another is taken for a value of its own, so a move of it is not reported
-- as a move out of what it was a view of)
data St = St {stMoved :: Map Place (Pos, Maybe String), stViews :: Map Local (Set Place)}

emptySt :: St
emptySt = St Map.empty Map.empty

joinSt :: St -> St -> St
joinSt a b = St (Map.union (stMoved a) (stMoved b)) (Map.intersectionWith Set.union (stViews a) (stViews b))

sameShape :: St -> St -> Bool
sameShape a b = Map.keysSet (stMoved a) == Map.keysSet (stMoved b) && stViews a == stViews b

overlaps :: Place -> Place -> Bool
overlaps (l, a) (m, b) = l == m && (a `isPrefixOf` b || b `isPrefixOf` a)

data Cx = Cx
    { cxProgram :: Program
    , cxCopies :: Set Name
    , cxFn :: Function
    , cxLent :: Set Local
    }

typeOf :: Cx -> Local -> Type
typeOf cx l = maybe TInt localType (Map.lookup l (fnLocals (cxFn cx)))

isCopy :: Cx -> Local -> Bool
isCopy cx = isCopyType (cxCopies cx) (cxProgram cx) . typeOf cx

-- The errors of a program: none if it never uses a value that was moved
checkMoves :: Set Name -> Program -> [String]
checkMoves copies program = concatMap (checkFunction copies program) (Map.elems (progFunctions program) ++ [progMain program])

checkFunction :: Set Name -> Program -> Function -> [String]
checkFunction copies program fn = nub (concat [snd (runBlock cx st block) | (b, st) <- Map.toList ins, Just block <- [Map.lookup b (fnBlocks fn)]])
  where
    cx = Cx program copies fn (Set.fromList (fnBorrowed fn))
    ins = fixpoint (Map.singleton (BlockId 0) emptySt)
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
assign cx pos st0 d rv = (define cx st1 d view, errs)
  where
    (st1, errs) = foldl' (access cx pos) (st0, []) (if forLoopList then [(l, ps, Read) | (l, ps, _) <- accesses rv] else accesses rv)
    ty = typeOf cx d
    -- (the list that a `for` loop goes through and the value that a `match` takes apart are read where they are)
    forLoopList = maybe False (\name -> "$list " `isPrefixOf` name || name == "$match") (localNameOf cx d)
    -- what the value that d gets is a view of, if it is one: a part of a value that is not Copy, or the value that a cast is of
    view = case rv of
        _ | isProjection rv, not (isCopy cx d) -> [(r, ps ++ [stepOf rv]) | Just l <- [sourceLocal rv], (r, ps) <- placesOf st1 l]
        AsVariant o _ | not (isCopyType (cxCopies cx) (cxProgram cx) ty), Just l <- operandLocal o -> placesOf st1 l
        -- (what a Box holds is read through it, and is the Box's when it is taken)
        Unbox o | not (isCopyType (cxCopies cx) (cxProgram cx) ty), Just l <- operandLocal o -> placesOf st1 l
        Use o | forLoopList, Just l <- operandLocal o -> placesOf st1 l
        _ -> []
    sourceLocal r = case r of
        ReadField o _ _ -> operandLocal o
        ListOp _ (o : _) -> operandLocal o
        _ -> Nothing
    stepOf r = case r of
        ReadField _ name field -> SField name field
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
        | otherwise = concatMap moveError places
    moveError q@(root, ps)
        | SElem `elem` ps = [message cx pos ("cannot move " ++ named q ++ " out of a list, which still holds it: write clone(" ++ fromMaybe (describe cx q) (localSource cx l) ++ ") to copy it")]
        | root `Set.member` cxLent cx = [message cx pos (describe cx q ++ " is lent (&T) to this function and can only be read: write clone(" ++ describe cx q ++ ") to get a value of its own")]
        | otherwise = []
    named q = maybe (describe cx q) (\v -> v ++ " (" ++ describe cx q ++ ")") (localSource cx l)
    st'
        | taking = st{stMoved = foldl' (\m q -> Map.insert q (pos, localSource cx l) m) (stMoved st) [q | q@(root, ps) <- places, SElem `notElem` ps, root `Set.notMember` cxLent cx]}
        | otherwise = st
    at p = maybe "" (\(line, column) -> " at line " ++ show line ++ ":" ++ show column) p

-- The local gets a new value: nothing is moved out of it, and it is a view of the places the value comes from (if it is a view)
define :: Cx -> St -> Local -> [Place] -> St
define _ st d view =
    St
        { stMoved = Map.filterWithKey (\(root, _) _ -> root /= d) (stMoved st)
        , stViews = if null view then Map.delete d (stViews st) else Map.insert d (Set.fromList view) (stViews st)
        }

terminator :: Cx -> Pos -> St -> Terminator -> (St, [String])
terminator cx pos st term = case term of
    SwitchBool o _ _ -> accessAll [(l, [], Read) | Just l <- [operandLocal o]]
    Call callee args dest _ ->
        let lent = lentArguments cx callee (length args)
            argLocals = [(l, b) | (a, b) <- zip args lent, Just l <- [operandLocal a]]
            conflicts = [message cx pos (describeLocal cx l ++ " is lent to this call and moved by it too: write clone(" ++ describeLocal cx l ++ ") for one of them") | (l, True) <- argLocals, (l', False) <- argLocals, l == l', not (isCopy cx l)]
            (st', errs) = foldl' (access cx pos) (st, []) ([(l, [], Read) | Just l <- [operandLocal callee]] ++ [(l, [], if b then Read else Consume) | (l, b) <- argLocals])
         in (define cx st' dest [], errs ++ take 1 conflicts)
    -- (what a function returns is given to its caller)
    Return | Local 0 `Map.member` fnLocals (cxFn cx) -> accessAll [(Local 0, [], Consume)]
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
