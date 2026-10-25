module MirMono
    ( monomorphize
    ) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Mir
import TersusTypes (Name, Size (..), Type (..), instanceOf, substSizes)

-- A function with size parameters (`fn dot<n>(a: Array<Int, n>, ...)`) is validated once, with each size a parameter it can reason
-- about, and its callers give the sizes as its last arguments. Native code holds an array inline, so it needs the size of every
-- array when it is made: this makes a copy of the function for each list of sizes it is called with (`dot<3>`), with the size
-- parameters replaced by the constants. A call gives a constant, or a size parameter of the function that calls, which the copy of
-- that one has replaced, so the copies there are to make are those that the program reaches, and there are finitely many (a size is
-- never worked out from others). A program with no function of the kind is returned as it is.
monomorphize :: Program -> Program
monomorphize program
    | not (any generic (Map.elems (progFunctions program))) = program
    | otherwise =
        withInstances
            program
                { progFunctions = Map.fromList [(fnName f, f) | f <- map unspecified (plain' ++ Map.elems instances)]
                , progMain = unspecified main'
                }
  where
    -- (the structs with sizes that the copies mention are declared, and those that only a function with sizes mentioned, whose sizes
    -- were names, are not there any more)
    withInstances p =
        let complete = completeInstances p
         in complete{progTypes = Map.filterWithKey (\name _ -> not (symbolic name)) (progTypes complete)}
    symbolic name = case instanceOf name of
        Just (_, sizes) -> any isParam sizes
        Nothing -> False
    isParam size = case size of
        SizeParam _ -> True
        _ -> False
    -- (what the validator was told names functions that are not there any more; nothing after it needs it)
    unspecified f = f{fnSpec = emptySpec, fnBlocks = Map.map (\(BasicBlock stmts term) -> BasicBlock [s | s <- stmts, not (isGhost s)] term) (fnBlocks f)}
    isGhost s = case s of
        Ghost _ _ -> True
        _ -> False
    generic = not . null . fnSizeParams
    (main', mainNeeds) = redirect program (progMain program)
    redirected = [redirect program f | f <- Map.elems (progFunctions program), not (generic f)]
    plain' = map fst redirected
    instances = build program (mainNeeds ++ concatMap snd redirected) Map.empty

-- The copies to make, with those that the copies need
build :: Program -> [(Name, [Integer])] -> Map (Name, [Integer]) Function -> Map (Name, [Integer]) Function
build _ [] done = done
build program (key@(name, sizes) : rest) done
    | Map.member key done = build program rest done
    | otherwise = case Map.lookup name (progFunctions program) of
        Nothing -> build program rest done
        Just generic ->
            let (copy, needs) = redirect program (instantiate generic sizes)
             in build program (rest ++ needs) (Map.insert key copy done)

instanceName :: Name -> [Integer] -> Name
instanceName name sizes = name ++ "<" ++ intercalate ", " (map show sizes) ++ ">"

-- The function with its size parameters replaced by the sizes
instantiate :: Function -> [Integer] -> Function
instantiate fn sizes =
    fn
        { fnName = instanceName (fnName fn) sizes
        , fnParams = keptParams
        , fnReturns = fmap types (fnReturns fn)
        , fnLocals = Map.map (\d -> d{localType = types (localType d)}) (Map.filterWithKey (\l _ -> l `notElem` sizeLocals) (fnLocals fn))
        , fnBlocks = Map.map block (fnBlocks fn)
        , fnSizeParams = []
        , fnSpec = spec (fnSpec fn)
        }
  where
    count = length (fnSizeParams fn)
    keptParams = take (length (fnParams fn) - count) (fnParams fn)
    sizeLocals = drop (length keptParams) (fnParams fn)
    values = Map.fromList (zip sizeLocals sizes)
    pairs = zip (fnSizeParams fn) (map SizeConst sizes)
    types = substSizes pairs
    -- (the name of a struct with sizes names them)
    named name = case substSizes pairs (TNamed name) of
        TNamed name' -> name'
        _ -> name
    constant c = case c of
        CData name fields -> CData (named name) [(f, constant v) | (f, v) <- fields]
        CList cs -> CList (map constant cs)
        CArray cs -> CArray (map constant cs)
        _ -> c
    operand o = case o of
        Copy l | Just c <- Map.lookup l values -> Const (CInt c)
        Move l | Just c <- Map.lookup l values -> Const (CInt c)
        Const c -> Const (constant c)
        _ -> o
    env = Map.map operand
    block (BasicBlock stmts term) = BasicBlock (map statement stmts) (terminator term)
    statement s = case s of
        Assign l rv -> Assign l (rvalue rv)
        Peek l rv -> Peek l (rvalue rv)
        Ghost e g -> Ghost (env e) g
        Drop _ -> s
    terminator t = case t of
        SwitchBool o yes no -> SwitchBool (operand o) yes no
        Call callee args dest next -> Call (operand callee) (map operand args) dest next
        _ -> t
    rvalue rv = case rv of
        Use o -> Use (operand o)
        BinaryOp op a b -> BinaryOp op (operand a) (operand b)
        ListOp op os -> ListOp op (map operand os)
        MakeList os -> MakeList (map operand os)
        MakeBox o -> MakeBox (operand o)
        Unbox o -> Unbox (operand o)
        Unsize o -> Unsize (operand o)
        MakeData name fields -> MakeData (named name) [(f, operand o) | (f, o) <- fields]
        ReadField o name field -> ReadField (operand o) (named name) field
        IsVariant o name -> IsVariant (operand o) (named name)
        AsVariant o name -> AsVariant (operand o) (named name)
        Clone o -> Clone (operand o)
        TakeField l name field -> TakeField l (named name) field
    spec s = s{specEnv = env (specEnv s), specLoops = Map.map (\l -> l{loopEnv = env (loopEnv l)}) (specLoops s)}

-- The function with each call of a function with size parameters made a call of the copy for its sizes, and the copies that need
-- making. The sizes are the last arguments of the call, which are constants here.
redirect :: Program -> Function -> (Function, [(Name, [Integer])])
redirect program fn = (fn{fnBlocks = Map.fromList (map fst blocks)}, concatMap snd blocks)
  where
    blocks = [((b, BasicBlock stmts term'), needs) | (b, BasicBlock stmts term) <- Map.toList (fnBlocks fn), let (term', needs) = call term]
    call term = case term of
        Call (Const (CFn callee)) args dest next
            | Just target <- Map.lookup callee (progFunctions program)
            , not (null (fnSizeParams target))
            , let (explicit, given) = splitAt (length args - length (fnSizeParams target)) args
            , Just sizes <- mapM constantSize given ->
                (Call (Const (CFn (instanceName callee sizes))) explicit dest next, [(callee, sizes)])
        _ -> (term, [])
    constantSize o = case o of
        Const (CInt c) -> Just c
        _ -> Nothing
