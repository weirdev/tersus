module MirMono
    ( monomorphize
    ) where

import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Mir
import Pretty (renderType)
import TersusTypes (Name, Size (..), Type (..), Variable, instanceOf, substitute)

-- A function with type parameters (`fn first<T>(a: &List<T>) -> T`) is made the same way, a copy for each list of types. A call does not
-- say them: they are what the types of the arguments and of the local that gets the result make the types of the parameters and of the
-- result (`first` of a `List<Int>` that gives an `Int` is `first<Int>`), and one that nothing decides is an `Int`.
--
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
    generic f = not (null (fnSizeParams f) && null (fnTypeParams f))
    (main', mainNeeds) = redirect program (progMain program)
    redirected = [redirect program f | f <- Map.elems (progFunctions program), not (generic f)]
    plain' = map fst redirected
    instances = build program (mainNeeds ++ concatMap snd redirected) Map.empty

-- The copies to make, with those that the copies need
-- (the types and the sizes that a copy is for)
type Key = (Name, [Type], [Integer])

build :: Program -> [Key] -> Map Key Function -> Map Key Function
build _ [] done = done
build program (key@(name, tys, sizes) : rest) done
    | Map.member key done = build program rest done
    | otherwise = case Map.lookup name (progFunctions program) of
        Nothing -> build program rest done
        Just generic ->
            let (copy, needs) = redirect program (instantiate generic tys sizes)
             in build program (rest ++ needs) (Map.insert key copy done)

instanceName :: Name -> [Type] -> [Integer] -> Name
instanceName name tys sizes = name ++ "<" ++ intercalate ", " (map renderType tys ++ map show sizes) ++ ">"

-- The function with its type and size parameters replaced by the types and the sizes
instantiate :: Function -> [Type] -> [Integer] -> Function
instantiate fn tys sizes =
    fn
        { fnName = instanceName (fnName fn) tys sizes
        , fnParams = keptParams
        , fnReturns = fmap types (fnReturns fn)
        , fnLocals = Map.map (\d -> d{localType = types (localType d)}) (Map.filterWithKey (\l _ -> l `notElem` sizeLocals) (fnLocals fn))
        , fnBlocks = Map.map block (fnBlocks fn)
        , fnSizeParams = []
        , fnTypeParams = []
        , fnBorrowed = [l | l <- fnBorrowed fn, l `notElem` sizeLocals]
        , fnSpec = spec (fnSpec fn)
        }
  where
    count = length (fnSizeParams fn)
    keptParams = take (length (fnParams fn) - count) (fnParams fn)
    sizeLocals = drop (length keptParams) (fnParams fn)
    values = Map.fromList (zip sizeLocals sizes)
    pairs = zip (fnSizeParams fn) (map SizeConst sizes)
    types = substitute pairs (zip (fnTypeParams fn) tys)
    -- (the name of a struct with sizes names them)
    named name = case types (TNamed name) of
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
redirect :: Program -> Function -> (Function, [Key])
redirect program fn = (fn{fnBlocks = Map.fromList (map fst blocks)}, concatMap snd blocks)
  where
    blocks = [((b, BasicBlock stmts term'), needs) | (b, BasicBlock stmts term) <- Map.toList (fnBlocks fn), let (term', needs) = call term]
    call term = case term of
        Call (Const (CFn callee)) args dest next
            | Just target <- Map.lookup callee (progFunctions program)
            , not (null (fnSizeParams target) && null (fnTypeParams target))
            , let (explicit, given) = splitAt (length args - length (fnSizeParams target)) args
            , Just sizes <- mapM constantSize given
            , let tys = typeArguments fn target explicit dest ->
                (Call (Const (CFn (instanceName callee tys sizes))) explicit dest next, [(callee, tys, sizes)])
        _ -> (term, [])
    constantSize o = case o of
        Const (CInt c) -> Just c
        _ -> Nothing

-- The types that a call gives the type parameters of the function it calls: those that make the types of the parameters the types
-- of the arguments, and the type of the result the type of the local that gets it
typeArguments :: Function -> Function -> [Operand] -> Local -> [Type]
typeArguments caller target args dest = [fromMaybe TInt (lookup t found) | t <- fnTypeParams target]
  where
    found =
        concat [match p a | (param, arg) <- zip (fnParams target) args, Just p <- [declared param], Just a <- [argumentType arg]]
            ++ concat [match r d | Just r <- [fnReturns target], Just d <- [localType <$> Map.lookup dest (fnLocals caller)]]
    declared l = localType <$> Map.lookup l (fnLocals target)
    argumentType o = case o of
        Copy l -> localType <$> Map.lookup l (fnLocals caller)
        Move l -> localType <$> Map.lookup l (fnLocals caller)
        Const c -> constantType c
    constantType c = case c of
        CInt _ -> Just TInt
        CBool _ -> Just TBool
        CList (x : _) -> TList <$> constantType x
        CArray cs@(x : _) -> (\t -> TArrayOf t (SizeConst (toInteger (length cs)))) <$> constantType x
        CData name _ -> Just (TNamed name)
        _ -> Nothing

-- What the type parameters of a type are, given the type it stands for
match :: Type -> Type -> [(Variable, Type)]
match pattern actual = case (pattern, actual) of
    (TParam name, a) -> [(name, a)]
    (TList p, TList a) -> match p a
    (TBox p, TBox a) -> match p a
    (TRef p, a) -> match p a
    (p, TRef a) -> match p a
    (TArrayOf p _, TArrayOf a _) -> match p a
    (TFn ps p, TFn as a) -> concat (zipWith match (p : ps) (a : as))
    _ -> []
