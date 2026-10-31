{-# LANGUAGE PatternSynonyms #-}

module MirVerify (verifyProgram) where

import Data.Maybe (fromMaybe)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Mir hiding (Env)
import qualified Mir
import Pretty (renderType)
import TypeCheck (functionType, maxArraySlots, solveInstanceArgs)
import TersusTypes (Arg (..), Name, Rel (..), Size (..), Type (..), Variable, baseNameOf, instanceName, namedMatches, pattern TArray, substSizes, tupleGeneric, tupleType, wordRange)
import Utils (Result (..))

-- Whether the program is a well formed MIR: the shape (every block a jump names is there, every local and function
-- used is declared), and the types (every operation is applied to operands of the types it takes, and gives the type
-- of the local that receives it). Lowering gives every local the type `elaborate` worked out, and native code
-- built on a wrong type is a wrong program, so this is what every lowering goes
-- through, and what every pass over the MIR should go through again.
verifyProgram :: Program -> Result () String
verifyProgram program =
    case concatMap (problems program) (progMain program : Map.elems (progFunctions program)) of
        [] -> Ok ()
        problem : _ -> Error problem

-- What the program declares: the constructors with the type they build, and the type of each function
data Env = Env
    { envCtors :: Map Name (Name, [(Variable, Type)])
    , envFns :: Map Name Type
    , envGenerics :: Map Name ([Variable], [(Variable, Type)])
    }

environment :: Program -> Env
environment program =
    Env
        { envCtors = Map.fromList (concatMap ctors (Map.toList (progTypes program)))
        , envFns = Map.fromList [(fnName f, fnType f) | f <- Map.elems (progFunctions program)]
        , envGenerics = progGenerics program
        }
  where
    ctors (name, StructDecl fields) = [(name, (name, fields))]
    ctors (name, EnumDecl variants) = [(v, (name, fields)) | (v, fields) <- variants]
    fnType f = functionType (fnSizeParams f) (fnTypeParams f) [(if p `elem` fnBorrowed f then TRef else id) (maybe (TVar 0) localType (Map.lookup p (fnLocals f))) | p <- fnParams f] (fromMaybe (TVar 0) (fnReturns f))

problems :: Program -> Function -> [String]
problems program fn =
    map (("In " ++ fnName fn ++ ": ") ++) $
        [ "no entry block bb0" | not (block (BlockId 0)) ]
            ++ [show l ++ " has no known type" | (l, d) <- Map.toList (fnLocals fn), hasUnknown (localType d)]
            -- (the size of an array can come from a size parameter, so the limit of a frame is looked at once the sizes are constants)
            ++ [ show l ++ " is " ++ renderType t ++ ", which takes " ++ show (slotsOf program t) ++ " words, more than the " ++ show maxArraySlots ++ " that an array held in a frame can have"
               | (l, d) <- Map.toList (fnLocals fn)
               , let t = localType d
               , isArrayType t
               , slotsOf program t > maxArraySlots
               ]
            ++ ["parameter " ++ show l ++ " is not declared" | l <- fnParams fn, not (declared l)]
            ++ ["_0 is not declared" | Just _ <- [fnReturns fn], not (declared (Local 0))]
            ++ ["_0 is " ++ renderType t ++ " but the function returns " ++ renderType r | Just r <- [fnReturns fn], Just d <- [Map.lookup (Local 0) (fnLocals fn)], let t = localType d, t /= r]
            ++ concat
                [ shape b stmts term ++ concatMap (map ((show b ++ ": ") ++) . statementProblems) stmts ++ map ((show b ++ ": ") ++) (terminatorProblems term)
                | (b, BasicBlock stmts term) <- Map.toList (fnBlocks fn)
                ]
            ++ ["a loop is at " ++ show b ++ ", which is not there" | b <- Map.keys (specLoops (fnSpec fn)), not (block b)]
            ++ ["a name of the specification stands for the undeclared " ++ show l | l <- specLocals, not (declared l)]
            ++ ["a name of the specification stands for the function " ++ n ++ ", which is not there" | n <- specFunctions, n `notElem` functionNames]
  where
    env = environment program
    declared l = Map.member l (fnLocals fn)
    block b = Map.member b (fnBlocks fn)
    functionNames = Map.keys (progFunctions program)
    specEnvs = specEnv (fnSpec fn) : map loopEnv (Map.elems (specLoops (fnSpec fn)))
    specLocals = concatMap envLocals specEnvs
    specFunctions = concatMap envFunctions specEnvs

    shape b stmts term =
        [show b ++ " uses the undeclared " ++ show l | l <- concatMap statementLocals stmts ++ terminatorLocals term, not (declared l)]
            ++ [show b ++ " jumps to " ++ show t ++ ", which is not there" | t <- successors term, not (block t)]
            ++ [show b ++ " names the function " ++ n ++ ", which is not there" | n <- concatMap statementFunctions stmts ++ terminatorFunctions term, n `notElem` functionNames]

    localTy l = localType <$> Map.lookup l (fnLocals fn)

    statementProblems stmt@(Assign dest rv) =
        case localTy dest of
            Nothing -> []
            Just d -> [renderStatement stmt ++ " is ill typed: " ++ why | why <- rvalueProblems env localTy d rv]
    statementProblems (Peek dest rv) = statementProblems (Assign dest rv)
    statementProblems Ghost{} = []
    statementProblems Drop{} = []

    terminatorProblems term = case term of
        SwitchBool test _ _ -> [renderTerminator term ++ " is ill typed: the test is not a Bool" | not (fits env localTy TBool test)]
        Call callee args dest _ ->
            let why = case instantiated args (operandType env localTy callee) of
                    Just (TFn params result)
                        | length params /= length args -> ["it takes " ++ show (length params) ++ " arguments, got " ++ show (length args)]
                        | otherwise ->
                            ["argument " ++ show i ++ " is not " ++ renderType p | (i, p, a) <- zip3 [1 :: Int ..] params args, not (fits env localTy p a)]
                                ++ ["the result is " ++ renderType result ++ ", not " ++ maybe "?" renderType (localTy dest) | Just d <- [localTy dest], not (sub env d result)]
                    _ -> ["the callee is not a function"]
             in [renderTerminator term ++ " is ill typed: " ++ w | w <- why]
        _ -> []

    -- a function with size parameters is called with their values as its last arguments (a constant, or a size parameter of the
    -- function that calls), which the types of the other parameters are taken with
    instantiated args t = case t of
        Just (TForall names _ inner)
            | length args >= length names ->
                let given = drop (length args - length names) args
                 in Just (substSizes (zip names (map sizeOf given)) inner)
        _ -> t
    sizeOf o = case o of
        Const (CInt c) -> SizeConst c
        Copy l -> maybe SizeAny SizeParam (nameOf l)
        Move l -> maybe SizeAny SizeParam (nameOf l)
        _ -> SizeAny
    nameOf l = Map.lookup l (fnLocals fn) >>= localName
    isArrayType t = case t of
        TArrayOf{} -> True
        _ -> False
    hasUnknown (TVar _) = True
    hasUnknown (TList t) = hasUnknown t
    hasUnknown (TArray t _) = hasUnknown t
    hasUnknown (TBox t) = hasUnknown t
    hasUnknown (TAddr t) = hasUnknown t
    hasUnknown (TUninit t) = hasUnknown t
    hasUnknown (TBlock t) = hasUnknown t
    hasUnknown (TRef t) = hasUnknown t
    hasUnknown (TFn args ret) = any hasUnknown (ret : args)
    hasUnknown (TNamed _ args) = or [hasUnknown u | ArgType u <- args]
    hasUnknown _ = False

-- Why the rvalue cannot give a value of the type of the local it is assigned to
rvalueProblems :: Env -> (Local -> Maybe Type) -> Type -> Rvalue -> [String]
rvalueProblems env localTy d rv =
    case rv of
        Use o -> [expected d o | not (fits' d o)]
        BinaryOp op a b -> case op of
            Compare Eq -> comparison a b
            Compare NotEq -> comparison a b
            Compare _ -> ints [a, b] ++ result TBool
            _ -> ints [a, b] ++ result TInt
        ListOp Length [l] -> [expected' "a list" l | not (isList l)] ++ result TInt
        ListOp First [l] -> [expected (TList d) l | not (fitsSequence d l)]
        ListOp Last [l] -> [expected (TList d) l | not (fitsSequence d l)]
        ListOp Get [l, i] -> [expected (TList d) l | not (fitsSequence d l)] ++ ints [i]
        ListOp NewArray [n, x] -> case (d, n) of
            (TArray e size, Const (CInt given))
                | size == given -> [expected e x | not (fits' e x)]
                | otherwise -> ["the size of the array is " ++ show given ++ ", not " ++ show size]
            -- (the size of an array made from a size parameter is that parameter)
            (TArrayOf e (SizeParam _), Copy _) -> [expected e x | not (fits' e x)]
            _ -> ["array needs a result that is an array and a size that is a constant"]
        ListOp WriteByte [b] -> [expected TByte b | not (fits' TByte b)] ++ result TByte
        ListOp WriteError [b] -> [expected TByte b | not (fits' TByte b)] ++ result TByte
        ListOp ReadByte [] -> result TInt
        ListOp ArgCount [] -> result TInt
        ListOp ArgByte [i, j] -> ints [i, j] ++ result TInt
        ListOp PathByte [b] -> [expected TByte b | not (fits' TByte b)] ++ result TInt
        ListOp FileLoad [] -> result TInt
        ListOp FileByte [i] -> ints [i] ++ result TInt
        ListOp StoreByte [b] -> [expected TByte b | not (fits' TByte b)] ++ result TInt
        ListOp FileStore [] -> result TInt
        ListOp ToByte [x] -> ints [x] ++ result TByte
        ListOp FromByte [b] -> [expected TByte b | not (fits' TByte b || any (\t -> fits' t b) [TWord s n | s <- [True, False], n <- [8, 16, 32]])] ++ result TInt
        ListOp (Narrow signed bits) [x] -> ints [x] ++ result (TWord signed bits)
        ListOp NewEmptyBoxed [] -> case d of
            TBox (TArrayOf _ SizeAny) -> []
            _ -> ["Array::empty needs a result that is a Box of an array of any size"]
        ListOp NewBoxed [n, x] -> case d of
            TBox (TArrayOf e SizeAny) -> ints [n] ++ [expected e x | not (fits' e x)]
            _ -> ["Array::boxed needs a result that is a Box of an array of any size"]
        ListOp Pop [l] -> [expected d l | not (fits' d l)]
        ListOp Push [l, x] -> withElement (\e -> [expected d l | not (fits' d l)] ++ [expected e x | not (fits' e x)])
        ListOp Set [l, i, x] -> withElement (\e -> [expected d l | not (fits' d l)] ++ ints [i] ++ [expected e x | not (fits' e x)])
        ListOp op os | Just problems <- pointerProblems op os -> problems
        ListOp op os -> [show op ++ " is applied to " ++ show (length os) ++ " operands"]
        MakeList os -> withElement (\e -> [expected e o | o <- os, not (fits' e o)])
        Unbox o -> case operandType env localTy o of
            Just (TBox held) -> ["the result is " ++ renderType d ++ ", not " ++ renderType held | not (sub env d held)]
            -- (a Box of an array is a list of native code, lib/lists.tersus, which gives its elements to an inline array)
            Just (TNamed "StdList" [ArgType e]) -> case d of
                TArrayOf e' _ | sub env e' e -> []
                _ -> ["the result is " ++ renderType d ++ ", not an array of " ++ renderType e]
            _ -> [expected' "a Box" o]
        Unsize o -> case (d, operandType env localTy o) of
            (TBox (TArrayOf e SizeAny), Just (TBox (TArrayOf e' size))) | size /= SizeAny -> [expected d o | not (sub env e e')]
            _ -> ["unsize needs a Box of an array, and a result that is a Box of an array of any size"]
        MakeBox o -> case d of
            TBox held -> [expected held o | not (fits' held o)]
            TNamed "StdList" [ArgType e] -> case operandType env localTy o of
                Just (TArrayOf e' (SizeConst _)) | sub env e e' -> []
                Nothing | Const (CArray _) <- o -> []
                _ -> [expected' ("an array of " ++ renderType e) o]
            _ -> ["the result is " ++ renderType d ++ ", not a Box"]
        MakeData name fields -> case Map.lookup name (envCtors env) of
            Nothing -> ["there is no constructor " ++ name]
            Just (typeName, declared)
                | map fst declared /= map fst fields -> [name ++ " is built with the wrong fields"]
                | otherwise -> ["the result is " ++ renderType d ++ ", not " ++ typeName | not (namedMatches d typeName)] ++ [expected t o | ((_, t), (_, o)) <- zip declared fields, not (fits' t o)]
        ReadField o name field -> case Map.lookup name (envCtors env) of
            Nothing -> ["there is no constructor " ++ name]
            Just (typeName, declared) ->
                [expected' ("a " ++ name) o | not (isValueOf typeName o)]
                    ++ case lookup field declared of
                        Nothing -> [name ++ " has no field " ++ field]
                        Just t -> ["the field is " ++ renderType t ++ ", not " ++ renderType d | not (sub env d t)]
        IsVariant o name -> case Map.lookup name (envCtors env) of
            Nothing -> ["there is no constructor " ++ name]
            Just (typeName, _) -> [expected' ("a " ++ typeName) o | not (isValueOf typeName o)] ++ result TBool
        AsVariant o name -> case Map.lookup name (envCtors env) of
            Nothing -> ["there is no constructor " ++ name]
            Just (typeName, _) ->
                [expected' ("a " ++ typeName) o | not (isValueOf typeName o)]
                    ++ ["the result is " ++ renderType d ++ ", not " ++ name | not (sub env d (TVariant name))]
        Clone o -> [expected d o | not (fits' d o)]
        TakeField l name field -> rvalueProblems env localTy d (ReadField (Copy l) name field)
  where
    fits' = fits env localTy
    -- (the operations on addresses, with the permission they are given, or without it after it is erased; see MirGhost)
    pointerProblems op os = case (op, os) of
        (AddrNull, []) -> Just (anAddress d)
        (AddrOffset, [p, i]) -> Just (addressOf p (\_ -> [expected' "the address" p | not (fits' d p)]) ++ ints [i])
        (AddrCast, [p]) -> Just (addressOf p (const []) ++ anAddress d)
        (AddrToInt, [p]) -> Just (addressOf p (const []) ++ result TInt)
        (AddrFromInt, [n]) -> Just (ints [n] ++ anAddress d)
        (AddrAlloc, [n]) -> Just (ints [n] ++ anAddress d)
        (AddrGet, p : i : rest) | length rest <= 1 -> Just (addressOf p (\t -> ["the result is " ++ renderType d ++ ", not " ++ renderType t | not (sub env d t)]) ++ ints [i])
        (AddrTake, p : i : rest) | length rest <= 1 -> Just (addressOf p (\t -> ["the result is " ++ renderType d ++ ", not " ++ renderType t | not (sub env d t)]) ++ ints [i])
        (AddrWrite, p : i : x : rest) | length rest <= 1 -> Just (addressOf p (\t -> [expected t x | not (fits' t x)]) ++ ints [i] ++ permissionOrZero rest)
        (AddrDropValue, p : i : rest) | length rest <= 1 -> Just (addressOf p (const []) ++ ints [i] ++ permissionOrZero rest)
        (AddrDropRange, p : i : n : rest) | length rest <= 1 -> Just (addressOf p (const []) ++ ints [i, n] ++ permissionOrZero rest)
        (AddrResize, p : n : rest) | length rest <= 1 -> Just (addressOf p (const []) ++ ints [n] ++ [expected' "the address" p | not (fits' d p)])
        (AddrFree, p : rest) | length rest <= 1 -> Just (addressOf p (const []) ++ result TInt)
        -- (an Uninit<T> is a T in native code, so its types are not looked at closely)
        (UninitEmpty, []) -> Just []
        (UninitNew, [_]) -> Just []
        (UninitGet, [_]) -> Just []
        (UninitTake, [_]) -> Just []
        (UninitDiscard, [_]) -> Just (result TInt)
        _ | op `elem` [BlockNew, BlockTaken, BlockResized, BlockSplitLo, BlockSplitHi, BlockJoin, BlockAssume, BlockCast] -> Just (case d of
            TBlock _ -> []
            _ -> ["the result is " ++ renderType d ++ ", not a permission"])
        _ -> Nothing
    anAddress t = case t of
        TAddr _ -> []
        _ -> ["the result is " ++ renderType t ++ ", not an address"]
    addressOf p k = case operandType env localTy p of
        Just (TAddr t) -> k t
        _ -> [expected' "an address" p]
    -- (an operation that gives the permission after gives 0 once the permissions are erased)
    permissionOrZero rest = case (rest, d) of
        ([_], TBlock _) -> []
        ([], TInt) -> []
        _ -> ["the result is " ++ renderType d ++ ", not " ++ (if null rest then "Int" else "a permission")]
    -- the sequence an element is read from is a list or an array
    fitsSequence e l = fits' (TList e) l || any (\ty -> fits' ty l) [t | Just t <- [arrayOf l e]] || arrayConstant l e
    arrayConstant l e = case l of
        Const (CArray cs) -> all (constantFits env e) cs
        _ -> False
    -- (an array operand that is a local has its type; a constant array is not typed by its elements alone)
    arrayOf l e = case operandType env localTy l of
        Just ty@(TArrayOf e' _) | sub env e e' -> Just ty
        Just ty@(TBox (TArrayOf e' _)) | sub env e e' -> Just ty
        -- (a list of native code is read as the array it holds)
        Just ty@(TNamed "StdList" [ArgType e']) | sub env e e' -> Just ty
        _ -> Nothing
    -- the result of set is the array it was given; the result of array(n, x) is an array
    arrayResult = case rv of
        ListOp Set [l, _, _] -> fits' d l
        ListOp NewArray _ -> True
        _ -> False
    expected t o = renderOperand' o ++ " is not " ++ renderType t
    expected' what o = renderOperand' o ++ " is not " ++ what
    renderOperand' o = case o of
        Move l -> renderOperand' (Copy l)
        Copy l -> show l ++ maybe "" (\t -> " (" ++ renderType t ++ ")") (localTy l)
        Const _ -> "the constant"
    ints os = [expected TInt o | o <- os, not (fits' TInt o)]
    result t = ["the result is " ++ renderType t ++ ", not " ++ renderType d | d /= t]
    withElement k = case d of
        TList e -> k e
        TArrayOf e _ | arrayResult -> k e
        TBox (TArrayOf e _) | arrayResult -> k e
        _ -> ["the result is " ++ renderType d ++ ", not a list"]
    comparison a b =
        result TBool
            ++ case (operandType env localTy a, operandType env localTy b) of
                (Just x, Just y)
                    | isFn x || isFn y -> ["functions cannot be compared"]
                    | not (sub env x y || sub env y x) -> ["the operands are " ++ renderType x ++ " and " ++ renderType y]
                _ -> []
    isFn TFn{} = True
    isFn _ = False
    isList o = case operandType env localTy o of
        Just (TList _) -> True
        Just TArrayOf{} -> True
        Just (TBox TArrayOf{}) -> True
        Nothing -> case o of
            Const (CList _) -> True
            Const (CArray _) -> True
            _ -> False
        _ -> False
    -- a value of the type with this name, or of one of its variants
    isValueOf typeName o = case operandType env localTy o of
        -- (a Box is looked into, and so is the struct a Box is made of in native code, lib/box.tersus)
        Just (TBox t) -> namedMatches t typeName || sub env (TNamed typeName []) t
        Just t@(TNamed "StdBox" [ArgType held]) -> namedMatches t typeName || sub env (TNamed typeName []) t || namedMatches held typeName || sub env (TNamed typeName []) held
        Just t -> namedMatches t typeName || sub env (TNamed typeName []) t
        Nothing -> False

-- The type a constructor builds, from its owner name and declared fields
ctorType :: Env -> (Name, [(Variable, Type)]) -> Type
ctorType env (typeName, declared) =
    let base = baseNameOf typeName
     in case tupleGeneric base of
            Just _ -> tupleType (map snd declared)
            Nothing -> case Map.lookup base (envGenerics env) of
                Just (params, template) -> TNamed base (solveInstanceArgs params template (map snd declared))
                Nothing -> TNamed typeName []

-- The type an operand is known to have; none for a list constant, whose element type is not in it
operandType :: Env -> (Local -> Maybe Type) -> Operand -> Maybe Type
operandType env localTy o = case o of
    Copy l -> localTy l
    Move l -> localTy l
    Const c -> case c of
        CInt _ -> Just TInt
        CBool _ -> Just TBool
        CList _ -> Nothing
        CArray _ -> Nothing
        CData name _ -> ctorType env <$> Map.lookup name (envCtors env)
        CFn name -> Map.lookup name (envFns env)

-- Whether the operand can be used where the type is wanted
fits :: Env -> (Local -> Maybe Type) -> Type -> Operand -> Bool
fits env localTy wanted o = case o of
    Copy l -> maybe False (sub env wanted) (localTy l)
    Move l -> fits env localTy wanted (Copy l)
    Const c -> constantFits env wanted c

constantFits :: Env -> Type -> Constant -> Bool
constantFits env (TRef wanted) c = constantFits env wanted c
constantFits _ TParam{} _ = True
constantFits env wanted c = case c of
    CInt n -> wanted == TInt || (wanted == TByte && n >= 0 && n < 256) || (case wanted of TWord s b -> n >= fst (wordRange s b) && n < snd (wordRange s b); _ -> False)
    CBool _ -> wanted == TBool
    CList cs -> case wanted of
        TList e -> all (constantFits env e) cs
        _ -> False
    CArray cs -> case wanted of
        TArray e n -> toInteger (length cs) == n && all (constantFits env e) cs
        _ -> False
    CData name fields -> case Map.lookup name (envCtors env) of
        Nothing -> False
        Just (typeName, declared) ->
            sub env wanted (ctorType env (typeName, declared))
                && map fst declared == map fst fields
                && and [constantFits env t v | ((_, t), (_, v)) <- zip declared fields]
    CFn name -> maybe False (sub env wanted) (Map.lookup name (envFns env))

-- Whether a value of the second type can be used where the first is wanted: the same type, or a variant of an enum
-- where the enum is wanted (but not the other way), also inside a list
sub :: Env -> Type -> Type -> Bool
sub env wanted actual = case (wanted, actual) of
    (TNamed base args, TVariant v) -> maybe False ((== instanceName base args) . fst) (Map.lookup v (envCtors env))
    (TList a, TList b) -> sub env a b
    (TArray a n, TArray b m) -> n == m && sub env a b
    (TArrayOf a SizeAny, TArrayOf b SizeAny) -> sub env a b
    (TBox a, TBox b) -> sub env a b
    (TAddr a, TAddr b) -> sub env a b
    (TUninit a, TUninit b) -> sub env a b
    (TBlock a, TBlock b) -> sub env a b
    (TNamed bx xs, TNamed by ys)
        | bx == by, length xs == length ys -> and (zipWith argSub xs ys)
    (TRef a, b) -> sub env a b
    (a, TRef b) -> sub env a b
    -- (a type parameter is any type to a call, which the checker has seen the types of)
    (TFn xs x, TFn ys y) | length xs == length ys -> and (zipWith (sub env) (x : xs) (y : ys))
    (TParam _, _) -> True
    (_, TParam _) -> True
    _ -> wanted == actual
  where
    argSub (ArgType x) (ArgType y) = sub env x y
    argSub (ArgSize x) (ArgSize y) = x == y || isParameter x || isParameter y
    argSub _ _ = False
    isParameter (SizeParam _) = True
    isParameter _ = False

statementLocals :: Statement -> [Local]
statementLocals (Assign dest rv) = dest : concatMap operandLocals (rvalueOperands rv)
statementLocals (Ghost env _) = envLocals env
statementLocals (Drop l) = [l]
statementLocals (Peek dest rv) = statementLocals (Assign dest rv)

rvalueOperands :: Rvalue -> [Operand]
rvalueOperands (Use o) = [o]
rvalueOperands (BinaryOp _ a b) = [a, b]
rvalueOperands (ListOp _ os) = os
rvalueOperands (MakeList os) = os
rvalueOperands (MakeBox o) = [o]
rvalueOperands (Unbox o) = [o]
rvalueOperands (Unsize o) = [o]
rvalueOperands (MakeData _ fields) = map snd fields
rvalueOperands (ReadField o _ _) = [o]
rvalueOperands (IsVariant o _) = [o]
rvalueOperands (AsVariant o _) = [o]
rvalueOperands (Clone o) = [o]
rvalueOperands (TakeField l _ _) = [Copy l]

operandLocals :: Operand -> [Local]
operandLocals (Copy l) = [l]
operandLocals (Move l) = [l]
operandLocals (Const _) = []

terminatorLocals :: Terminator -> [Local]
terminatorLocals (SwitchBool o _ _) = operandLocals o
terminatorLocals (Call f args dest _) = dest : concatMap operandLocals (f : args)
terminatorLocals _ = []

statementFunctions :: Statement -> [Name]
statementFunctions (Assign _ rv) = concatMap operandFunctions (rvalueOperands rv)
statementFunctions (Ghost env g) = envFunctions env ++ [n | GhostFunction n _ _ <- [g]]
statementFunctions (Drop _) = []
statementFunctions (Peek dest rv) = statementFunctions (Assign dest rv)

envLocals :: Mir.Env -> [Local]
envLocals env = [l | Copy l <- Map.elems env]

envFunctions :: Mir.Env -> [Name]
envFunctions env = concat [constantFunctions c | Const c <- Map.elems env]

terminatorFunctions :: Terminator -> [Name]
terminatorFunctions (SwitchBool o _ _) = operandFunctions o
terminatorFunctions (Call f args _ _) = concatMap operandFunctions (f : args)
terminatorFunctions _ = []

operandFunctions :: Operand -> [Name]
operandFunctions (Const c) = constantFunctions c
operandFunctions _ = []

constantFunctions :: Constant -> [Name]
constantFunctions (CFn n) = [n]
constantFunctions (CList cs) = concatMap constantFunctions cs
constantFunctions (CArray cs) = concatMap constantFunctions cs
constantFunctions (CData _ fs) = concatMap (constantFunctions . snd) fs
constantFunctions _ = []

