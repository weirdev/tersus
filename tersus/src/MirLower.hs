module MirLower (lowerProgram, lowerElaborated) where

import Control.Monad (unless, when)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Mir as M
import MirVerify (verifyProgram)
import StdLib (stdLibCtx)
import TersusTypes
import TypeCheck
import Utils

-- Lowers a program that has passed validation to the MIR: control flow becomes blocks that jump, nested expressions
-- become temporaries, nested functions are lifted to the top, and the scopes that decide which variable an assignment
-- means are resolved to numbered locals.
--
-- Every local and temporary has a type. The AST has none (the checker erases them), so lowering replays the checker's
-- inference over the same program with the same unifier (TypeCheck's TC), taking the type of each piece from
-- the steps of inferExpr: that is how `x = []` gets the element type that a later `push(x, 1)` decides.
lowerProgram :: [Statement] -> Result M.Program String
lowerProgram stmts = elaborate stmts `bindResult` lowerElaborated

-- For a program that `elaborate` has checked and handed back (the pipeline checks a program once)
lowerElaborated :: [Statement] -> Result M.Program String
lowerElaborated elaborated =
    case runL (program elaborated) (initialState elaborated) of
        Left e -> Error e
        Right (p, _) -> Ok p

-- The lowering monad: state, and failure for what should not happen to a program that has been checked
newtype L a = L {runL :: LS -> Either String (a, LS)}

instance Functor L where
    fmap f (L g) = L (\s -> fmap (\(a, s') -> (f a, s')) (g s))

instance Applicative L where
    pure a = L (\s -> Right (a, s))
    L f <*> L g = L (\s -> case f s of
        Left e -> Left e
        Right (h, s') -> fmap (\(a, s'') -> (h a, s'')) (g s'))

instance Monad L where
    L g >>= f = L (\s -> case g s of
        Left e -> Left e
        Right (a, s') -> runL (f a) s')

failL :: String -> L a
failL e = L (\_ -> Left e)

getS :: L LS
getS = L (\s -> Right (s, s))

modifyS :: (LS -> LS) -> L ()
modifyS f = L (\s -> Right ((), f s))

-- Runs a step of the checker on the state it keeps
tc :: TC a -> L a
tc action = L (\s -> case runTcState action (lsTc s) of
    Left e -> Left ("Lowering: " ++ e)
    Right (a, t) -> Right (a, s{lsTc = t}))

-- What a name means: a local, or a function of the program
data Binding = BLocal M.Local Type | BFn Name Type

-- The function being built: its locals, the blocks that are done, and the one being written
data Builder = Builder
    { bName :: Name
    , bIsMain :: Bool
    , bSizes :: [Variable] -- the size parameters of the function
    , bTypeParams :: [Variable] -- its type parameters
    , bBorrowed :: [M.Local] -- the parameters it borrows
    , bReturns :: Maybe Type
    , bParams :: [M.Local]
    , bLocals :: Map M.Local M.LocalDecl
    , bNextLocal :: Int
    , bBlocks :: Map M.BlockId M.BasicBlock
    , bNextBlock :: Int
    , bOpen :: Maybe (M.BlockId, [M.Statement]) -- the block being written, with its statements last first; Nothing after a return
    , bScopes :: [Map Variable Binding] -- innermost first
    , bLoops :: Map M.BlockId M.LoopSpec
    }

data LS = LS
    { lsTc :: TcState
    , lsTypes :: Map Name M.TypeDecl
    , lsFunctions :: Map Name M.Function
    , lsNames :: Set.Set Name
    , lsGlobals :: Map Variable (Name, Type) -- the functions defined at the top of the program
    , lsAssigned :: Set.Set Variable -- the names the program assigns other than by defining a function
    , lsBuilder :: Builder
    , lsGenerics :: Map Name ([Variable], [(Variable, Type)]) -- the structs with sizes
    , lsInvariants :: Map Name [ValidationStatement] -- what every value of a struct meets
    }

initialState :: [Statement] -> LS
initialState stmts = LS initialTcState Map.empty Map.empty (Set.singleton "main") Map.empty (assignedNames stmts) (newBuilder "main" True Nothing) Map.empty Map.empty

-- The variables that statements assign (or bind with let), other than the names of the functions they define. A function
-- whose name is one of them may be replaced by another value (`f = size;`), so its name is a local of its own; the
-- others are known functions, and a call of one is a call by name.
assignedNames :: [Statement] -> Set.Set Variable
assignedNames = foldMap names
  where
    names stmt = case stmt of
        Assign _ (Val (VFunct _ _ _ (NativeFunct _ _ body) _)) -> assignedNames body
        Assign var _ -> Set.singleton var
        Let var _ -> Set.singleton var
        Block body -> assignedNames body
        If _ thenStmts elseStmts -> assignedNames thenStmts <> assignedNames elseStmts
        While _ _ _ body -> assignedNames body
        _ -> Set.empty

newBuilder :: Name -> Bool -> Maybe Type -> Builder
newBuilder name isMain returns =
    Builder
        { bName = name
        , bIsMain = isMain
        , bSizes = []
        , bTypeParams = []
        , bBorrowed = []
        , bReturns = returns
        , bParams = []
        , bLocals = maybe Map.empty (\t -> Map.singleton (M.Local 0) (M.LocalDecl t Nothing)) returns
        , bNextLocal = 1
        , bBlocks = Map.empty
        , bNextBlock = 1
        , bOpen = Just (M.BlockId 0, [])
        , bScopes = [Map.empty]
        , bLoops = Map.empty
        }

builder :: L Builder
builder = lsBuilder <$> getS

modifyB :: (Builder -> Builder) -> L ()
modifyB f = modifyS (\s -> s{lsBuilder = f (lsBuilder s)})

-- Building blocks

newLocal :: Maybe Variable -> Type -> L M.Local
newLocal name ty = do
    b <- builder
    let l = M.Local (bNextLocal b)
    modifyB (\b' -> b'{bNextLocal = bNextLocal b' + 1, bLocals = Map.insert l (M.LocalDecl ty name) (bLocals b')})
    return l

newBlock :: L M.BlockId
newBlock = do
    b <- builder
    modifyB (\b' -> b'{bNextBlock = bNextBlock b' + 1})
    return (M.BlockId (bNextBlock b))

isOpen :: L Bool
isOpen = maybe False (const True) . bOpen <$> builder

-- (does nothing after a return, where nothing can run)
emit :: M.Statement -> L ()
emit stmt = modifyB (\b -> b{bOpen = fmap (\(id', ss) -> (id', stmt : ss)) (bOpen b)})

terminate :: M.Terminator -> L ()
terminate term =
    modifyB
        ( \b -> case bOpen b of
            Just (id', ss) -> b{bOpen = Nothing, bBlocks = Map.insert id' (M.BasicBlock (reverse ss) term) (bBlocks b)}
            Nothing -> b
        )

openBlock :: M.BlockId -> L ()
openBlock id' = modifyB (\b -> b{bOpen = Just (id', [])})

scoped :: L a -> L a
scoped action = do
    modifyB (\b -> b{bScopes = Map.empty : bScopes b})
    a <- action
    modifyB (\b -> b{bScopes = drop 1 (bScopes b)})
    return a

bindName :: Variable -> Binding -> L ()
bindName var binding = modifyB (\b -> case bScopes b of
    scope : outer -> b{bScopes = Map.insert var binding scope : outer}
    [] -> b{bScopes = [Map.singleton var binding]})

lookupBinding :: Variable -> L (Maybe Binding)
lookupBinding var = do
    b <- builder
    return (case [x | scope <- bScopes b, Just x <- [Map.lookup var scope]] of
        x : _ -> Just x
        [] -> Nothing)

-- A name that no function has yet
uniqueName :: Name -> L Name
uniqueName base = do
    s <- getS
    let candidates = base : [base ++ "#" ++ show n | n <- [2 :: Int ..]]
        name = head (filter (`Set.notMember` lsNames s) candidates)
    modifyS (\s' -> s'{lsNames = Set.insert name (lsNames s')})
    return name

-- Programs

program :: [Statement] -> L M.Program
program stmts = do
    lowerStatements stmts
    open <- isOpen
    when open (terminate M.Return)
    b <- builder
    let main' = buildFunction [] [] Nothing Map.empty b
    s <- getS
    let functions = Map.elems (lsFunctions s)
    resolved <- mapM resolveFunction (main' : functions)
    let (resolvedMain, others) = case resolved of
            m : rest -> (m, rest)
            [] -> (main', [])
        result = M.completeInstances (M.Program (lsTypes s) (Map.fromList [(M.fnName f, f) | f <- others]) resolvedMain (lsGenerics s) (lsInvariants s))
    case verifyProgram result of
        Error e -> failL ("Lowering produced a malformed program: " ++ e)
        Ok () -> return result

-- Applies what the checker learned about the type variables; one it never learned (the elements of a list that is
-- never used) is an Int
resolveFunction :: M.Function -> L M.Function
resolveFunction fn = do
    locals <- mapM (\d -> (\t -> d{M.localType = t}) <$> resolveType (M.localType d)) (M.fnLocals fn)
    returns <- mapM resolveType (M.fnReturns fn)
    -- (an element that no use decided was not looked at when the array was made: what it came to is looked at now)
    mapM_ (mapM_ arrayHolds . universe . M.localType) (Map.elems locals)
    return fn{M.fnLocals = locals, M.fnReturns = returns}
  where
    universe ty = ty : case ty of
        TList t -> universe t
        TArrayOf t _ -> universe t
        TBox t -> universe t
        TFn args ret -> concatMap universe (ret : args)
        _ -> []
    arrayHolds ty = case ty of
        TArrayOf t _ | not (arrayElement t) -> failL ("Type error: an array holds values that have a size, not " ++ renderType t)
        _ -> return ()

resolveType :: Type -> L Type
resolveType ty = defaultType <$> tc (zonk ty)
  where
    defaultType (TVar _) = TInt
    defaultType (TList t) = TList (defaultType t)
    defaultType (TArrayOf t n) = TArrayOf (defaultType t) n
    defaultType (TBox t) = TBox (defaultType t)
    defaultType (TRef t) = TRef (defaultType t)
    defaultType (TFn args ret) = TFn (map defaultType args) (defaultType ret)
    defaultType t = t

-- Finished blocks, numbered in the order a walk from the entry reaches them; blocks nothing jumps to are dropped
buildFunction :: [ValidationStatement] -> [ValidationStatement] -> Maybe Termination -> M.Env -> Builder -> M.Function
buildFunction requires ensures term env b =
    M.Function
        { M.fnName = bName b
        , M.fnParams = bParams b
        , M.fnReturns = bReturns b
        , M.fnLocals = bLocals b
        , M.fnSizeParams = bSizes b
        , M.fnTypeParams = bTypeParams b
        , M.fnBorrowed = bBorrowed b
        , M.fnBlocks = Map.fromList [(rename old, M.BasicBlock stmts (renameTerm t)) | old <- order, Just (M.BasicBlock stmts t) <- [Map.lookup old (bBlocks b)]]
        , M.fnSpec = M.FunctionSpec requires ensures term (Map.fromList [(rename h, spec) | (h, spec) <- Map.toList (bLoops b), Map.member h mapping]) env
        }
  where
    order = reverse (walk [] (M.BlockId 0))
    walk seen block
        | block `elem` seen = seen
        | otherwise = case Map.lookup block (bBlocks b) of
            Nothing -> seen
            Just (M.BasicBlock _ t) -> foldl walk (block : seen) (M.successors t)
    mapping = Map.fromList (zip order (map M.BlockId [0 ..]))
    rename block = Map.findWithDefault block block mapping
    renameTerm t = case t of
        M.Goto x -> M.Goto (rename x)
        M.SwitchBool o x y -> M.SwitchBool o (rename x) (rename y)
        M.Call f args dest next -> M.Call f args dest (rename next)
        M.Return -> M.Return
        M.Unreachable -> M.Unreachable

-- Statements

lowerStatements :: [Statement] -> L ()
lowerStatements [] = return ()
lowerStatements (stmt : rest) = do
    lowerStatement stmt
    open <- isOpen
    -- after a return nothing runs, as in the evaluator, which drops the rest
    when open (lowerStatements rest)

lowerStatement :: Statement -> L ()
lowerStatement stmt =
    case stmt of
        Assign var (Val (VFunct params ins outs (NativeFunct sig term body) _)) -> defineFunction var params ins outs sig term body
        Assign var expr -> do
            (pending, ty) <- lowerLast expr
            dest <- assignTarget var ty
            finishInto dest pending
        Let var expr -> do
            (pending, ty) <- lowerLast expr
            dest <- newLocal (Just var) ty
            bindName var (BLocal dest ty)
            finishInto dest pending
        Return expr -> lowerReturn expr
        ValidationStatement vs -> ghost (M.GhostValidation vs)
        StructDef name sizes fields invariant | not (null sizes) -> do
            tc (declareGeneric name sizes fields)
            modifyS (\s -> s{lsGenerics = Map.insert name (sizes, fields) (lsGenerics s), lsInvariants = withInvariant name invariant (lsInvariants s)})
        StructDef name _ fields invariant -> do
            tc (declareType name >> mapM_ (checkType . snd) fields >> registerCtors name [(name, fields)])
            addType name (M.StructDecl fields)
            modifyS (\s -> s{lsInvariants = withInvariant name invariant (lsInvariants s)})
        EnumDef name variants -> do
            tc (declareTypeWith name (map fst variants) >> mapM_ (mapM_ (checkType . snd) . snd) variants >> registerCtors name variants)
            addType name (M.EnumDecl variants)
        -- (the checker takes a trait apart and hands an impl back as the functions it defines)
        TraitDef{} -> failL "A trait reached the lowering"
        ImplDef{} -> failL "An impl reached the lowering"
        BoundedDef{} -> failL "A function with bounds reached the lowering"
        AxiomDef name args ins outs -> ghost (M.GhostAxiom name args ins outs)
        ProofDef name args ins outs body -> ghost (M.GhostProof name args ins outs body)
        Block stmts -> scoped (lowerStatements stmts)
        If cond thenStmts elseStmts -> lowerIf cond thenStmts elseStmts
        While cond invariant term body -> lowerWhile cond invariant term body

-- A statement for the validator, with the names the program can use where it stands
ghost :: M.GhostStatement -> L ()
ghost g = visibleEnv >>= \env -> emit (M.Ghost env g)

-- What the names visible here stand for: the locals of the scopes (the innermost first), and the functions defined at the top
visibleEnv :: L M.Env
visibleEnv = do
    b <- builder
    s <- getS
    let globals = Map.fromList [(var, M.Const (M.CFn name)) | (var, (name, _)) <- Map.toList (lsGlobals s)]
        scoped' = Map.unions [Map.map operandOf scope | scope <- bScopes b]
        operandOf (BLocal l _) = M.Copy l
        operandOf (BFn name _) = M.Const (M.CFn name)
    return (Map.union scoped' globals)

withInvariant :: Name -> [ValidationStatement] -> Map Name [ValidationStatement] -> Map Name [ValidationStatement]
withInvariant _ [] invariants = invariants
withInvariant name invariant invariants = Map.insert name invariant invariants

addType :: Name -> M.TypeDecl -> L ()
addType name decl = modifyS (\s -> s{lsTypes = Map.insert name decl (lsTypes s)})

-- Assigning a variable that exists keeps its local; a new one gets one in the innermost scope. A function name does
-- not stand for a local, so assigning it makes one.
assignTarget :: Variable -> Type -> L M.Local
assignTarget var ty = do
    binding <- lookupBinding var
    case binding of
        Just (BLocal l existing) -> tc (expect ("assignment to " ++ var) existing ty) >> return l
        _ -> do
            l <- newLocal (Just var) ty
            bindName var (BLocal l ty)
            return l

lowerReturn :: Expression -> L ()
lowerReturn expr = do
    (pending, ty) <- lowerLast expr
    b <- builder
    case bReturns b of
        Just declared -> tc (expect "returned value" declared ty)
        Nothing -> do
            -- the program has no declared type: the first return decides it
            modifyB (\b' -> b'{bReturns = Just ty, bLocals = Map.insert (M.Local 0) (M.LocalDecl ty Nothing) (bLocals b')})
    finishInto (M.Local 0) pending
    terminate M.Return

lowerIf :: Expression -> [Statement] -> [Statement] -> L ()
lowerIf cond thenStmts elseStmts = do
    (test, ty) <- lowerOperand cond
    tc (expect "condition of if" TBool ty)
    thenB <- newBlock
    elseB <- newBlock
    joinB <- newBlock
    terminate (M.SwitchBool test thenB elseB)
    openBlock thenB
    scoped (lowerStatements thenStmts)
    thenOpen <- isOpen
    when thenOpen (terminate (M.Goto joinB))
    openBlock elseB
    scoped (lowerStatements elseStmts)
    elseOpen <- isOpen
    when elseOpen (terminate (M.Goto joinB))
    -- when both branches returned nothing reaches the join, and nothing after the if runs
    when (thenOpen || elseOpen) (openBlock joinB)

lowerWhile :: Expression -> [ValidationStatement] -> Maybe Termination -> [Statement] -> L ()
lowerWhile cond invariant term body = do
    header <- newBlock
    bodyB <- newBlock
    exit <- newBlock
    terminate (M.Goto header)
    openBlock header
    env <- visibleEnv
    modifyB (\b -> b{bLoops = Map.insert header (M.LoopSpec invariant term env) (bLoops b)})
    (test, ty) <- lowerOperand cond
    tc (expect "condition of while" TBool ty)
    terminate (M.SwitchBool test bodyB exit)
    openBlock bodyB
    scoped (lowerStatements body)
    open <- isOpen
    when open (terminate (M.Goto header))
    openBlock exit

-- A function becomes a function of the program, lifted to the top whatever it is nested in (a body sees only its
-- parameters and the functions at the top, so there is nothing to capture). One defined at the top of the program is
-- found by name from the bodies of the functions after it, and from itself; any other is a name in its scope.
defineFunction :: Variable -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> Signature -> Maybe Termination -> [Statement] -> L ()
defineFunction var params ins outs (Signature ptys rty sizes types) term body = do
    enclosing <- builder
    let atTop = bIsMain enclosing && length (bScopes enclosing) == 1
        fnTy = functionType sizes types ptys rty
    name <- uniqueName (if atTop then var else bName enclosing ++ "::" ++ var)
    -- (a function with sizes is called by name, which its sizes are given to: it has no value to put in a local)
    assigned <- (\s -> Set.member var (lsAssigned s) && null sizes) <$> getS
    -- (the bodies of the functions after it find a function at the top by name, whatever the program does to the variable)
    when atTop (modifyS (\s -> s{lsGlobals = Map.insert var (name, fnTy) (lsGlobals s)}))
    ghost (M.GhostFunction name var atTop)
    if assigned
        then do
            l <- newLocal (Just var) fnTy
            bindName var (BLocal l fnTy)
            emit (M.Assign l (M.Use (M.Const (M.CFn name))))
        else unless atTop (bindName var (BFn name fnTy))
    tc (withGenerics sizes types (mapM_ checkType (rty : map unrefType ptys)))
    outer <- builder
    -- the body is lowered as a function of its own, then the outer one goes on
    modifyB (const (newBuilder name False (Just rty)){bSizes = sizes, bTypeParams = types})
    -- (a borrowed parameter is a local of its type, which the function only reads)
    paramLocals <- mapM (\(p, ty) -> (\l -> (p, l, unrefType ty)) <$> newLocal (Just p) (unrefType ty)) (zip params ptys)
    modifyB (\b -> b{bBorrowed = [l | ((_, l, _), TRef _) <- zip paramLocals ptys]})
    modifyB (\b -> b{bParams = [l | (_, l, _) <- paramLocals], bScopes = [Map.fromList [(p, BLocal l ty) | (p, l, ty) <- paramLocals]]})
    env <- visibleEnv
    lowerStatements body
    open <- isOpen
    when open (terminate M.Unreachable)
    inner <- builder
    modifyB (const outer)
    let fn = buildFunction ins outs term env inner
    modifyS (\s -> s{lsFunctions = Map.insert name fn (lsFunctions s)})

unrefType :: Type -> Type
unrefType (TRef t) = t
unrefType t = t

-- Expressions

-- The last step of an expression, which gives its value to a local: an operation, or a call (a call ends a block)
data Pending = PRvalue M.Rvalue | PCall M.Operand [M.Operand]

finishInto :: M.Local -> Pending -> L ()
finishInto dest (PRvalue rv) = emit (M.Assign dest rv)
finishInto dest (PCall callee args) = do
    open <- isOpen
    when open $ do
        next <- newBlock
        terminate (M.Call callee args dest next)
        openBlock next

-- The operand that holds the value of an expression, and the type of the value
lowerOperand :: Expression -> L (M.Operand, Type)
lowerOperand (Val v) = valueOperand v
lowerOperand (Var name) = varOperand name
lowerOperand expr = do
    (pending, ty) <- lowerLast expr
    case pending of
        PRvalue (M.Use operand) -> return (operand, ty)
        _ -> do
            temp <- newLocal Nothing ty
            finishInto temp pending
            return (M.Copy temp, ty)

-- The arguments are evaluated left to right, then the operation or call is the last step
lowerLast :: Expression -> L (Pending, Type)
lowerLast (Val v) = (\(o, ty) -> (PRvalue (M.Use o), ty)) <$> valueOperand v
lowerLast (Var name) = (\(o, ty) -> (PRvalue (M.Use o), ty)) <$> varOperand name
lowerLast (F funct args) = do
    target <- resolveHead funct
    case target of
        Builtin b -> lowerBuiltin b args
        Callable callee ty -> do
            operands <- mapM lowerOperand args
            result <- tc (checkCall "call" ty (map snd operands))
            return (PCall callee (map fst operands), result)

-- What is being applied
data Head = Builtin BuiltinFunct | Callable M.Operand Type

resolveHead :: Expression -> L Head
resolveHead (Val (VFunct _ _ _ (BuiltinFunct b) _)) = return (Builtin b)
resolveHead (Var name) = do
    binding <- lookupBinding name
    s <- getS
    case binding of
        Just (BLocal l ty) -> return (Callable (M.Copy l) ty)
        Just (BFn fn ty) -> return (Callable (M.Const (M.CFn fn)) ty)
        Nothing -> case Map.lookup name (lsGlobals s) of
            Just (fn, ty) -> return (Callable (M.Const (M.CFn fn)) ty)
            Nothing -> case Map.lookup name stdLibCtx of
                Just (VFunct _ _ _ (BuiltinFunct b) _) -> return (Builtin b)
                _ -> failL ("Undefined variable: " ++ name)
resolveHead other = uncurry Callable <$> lowerOperand other

lowerBuiltin :: BuiltinFunct -> [Expression] -> L (Pending, Type)
lowerBuiltin b args = do
    operands <- mapM lowerOperand args
    let tys = map snd operands
    result <- case (b, operands) of
        -- (the size is a constant: the checker has folded it, and the element decides the rest)
        (NewArray, [(M.Const (M.CInt n), _), (_, elementTy)]) -> return (TArray elementTy n)
        -- (the size is a size parameter of the function: the local that holds it is named like it)
        (NewArray, [(M.Copy l, _), (_, elementTy)]) -> do
            b' <- builder
            case Map.lookup l (bLocals b') of
                Just (M.LocalDecl _ (Just name)) | name `elem` bSizes b' -> return (TArrayOf elementTy (SizeParam name))
                _ -> failL "array was not given a constant size"
        (NewArray, _) -> failL "array was not given a constant size"
        (NewBox, [(_, held)]) -> return (TBox held)
        (NewBoxedArray, [_, (_, elementTy)]) -> return (TBox (TArrayOf elementTy SizeAny))
        (NewEmptyArray, []) -> tc freshVar >>= \elementTy -> return (TBox (TArrayOf elementTy SizeAny))
        (Unsize, [(_, boxTy)]) -> tc (zonk boxTy) >>= \t -> case t of
            TBox (TArrayOf elementTy _) -> return (TBox (TArrayOf elementTy SizeAny))
            _ -> failL "unsize was given something that is not a Box of an array"
        (UnBox, [(_, boxTy)]) -> tc (zonk boxTy) >>= \t -> case t of
            TBox held -> return held
            _ -> failL "Box::unbox was given something that is not a Box"
        (ArrayFrom, [(M.Const (M.CList items), TList elementTy)]) -> return (TArray elementTy (fromIntegral (length items)))
        (ArrayFrom, _) -> failL "an array literal was not made from a list of constants"
        _ -> builtinResult b tys
    rv <- builtinRvalue b tys (map fst operands)
    return (PRvalue rv, result)
  where
    builtinResult b' tys' = case (b', tys') of
        (Field owner field, [structTy]) -> tc (readField owner field structTy)
        (Ctor name fields, _) -> tc (checkConstruct name fields tys')
        _ -> tc (builtinType b' >>= \ft -> checkBuiltinCall (Just b') "call" ft tys')

-- The operation that a builtin applied to operands stands for. `as` keeps the value and gives it the variant's type.
builtinRvalue :: BuiltinFunct -> [Type] -> [M.Operand] -> L M.Rvalue
builtinRvalue b tys ops =
    case (b, ops) of
        (Size, [_]) -> return (M.ListOp M.Length ops)
        (First, [_]) -> return (M.ListOp M.First ops)
        (Last, [_]) -> return (M.ListOp M.Last ops)
        (Get, [_, _]) -> return (M.ListOp M.Get ops)
        (Push, [_, _]) -> return (M.ListOp M.Push ops)
        (Pop, [_]) -> return (M.ListOp M.Pop ops)
        (Set, [_, _, _]) -> return (M.ListOp M.Set ops)
        (NewArray, [_, _]) -> return (M.ListOp M.NewArray ops)
        -- (the list of the literal, held as an array)
        (ArrayFrom, [M.Const (M.CList items)]) -> return (M.Use (M.Const (M.CArray items)))
        (ArrayFrom, [o]) -> return (M.Use o)
        (Plus, [x, y]) -> return (M.BinaryOp M.Add x y)
        (Minus, [x, y]) -> return (M.BinaryOp M.Sub x y)
        (Times, [x, y]) -> return (M.BinaryOp M.Mul x y)
        (Div, [x, y]) -> return (M.BinaryOp M.Div x y)
        (Mod, [x, y]) -> return (M.BinaryOp M.Mod x y)
        (Rel rel, [x, y]) -> return (M.BinaryOp (M.Compare rel) x y)
        (Ctor name fields, _) | length fields == length ops -> return (M.MakeData name (zip fields ops))
        (Field owner field, [o]) -> do
            ctor <- maybe (structCtor (head tys)) return owner
            return (M.ReadField o ctor field)
        (Project variant field, [o]) -> return (M.ReadField o variant field)
        (NewBox, [o]) -> return (M.MakeBox o)
        (NewBoxedArray, [_, _]) -> return (M.ListOp M.NewBoxed ops)
        (NewEmptyArray, []) -> return (M.ListOp M.NewEmptyBoxed [])
        (WriteByte, [_]) -> return (M.ListOp M.WriteByte ops)
        (WriteError, [_]) -> return (M.ListOp M.WriteError ops)
        (ReadByte, []) -> return (M.ListOp M.ReadByte [])
        (ArgCount, []) -> return (M.ListOp M.ArgCount [])
        (ArgByte, [_, _]) -> return (M.ListOp M.ArgByte ops)
        (PathByte, [_]) -> return (M.ListOp M.PathByte ops)
        (FileLoad, []) -> return (M.ListOp M.FileLoad [])
        (FileByte, [_]) -> return (M.ListOp M.FileByte ops)
        (StoreByte, [_]) -> return (M.ListOp M.StoreByte ops)
        (FileStore, []) -> return (M.ListOp M.FileStore [])
        (ToByte, [_]) -> return (M.ListOp M.ToByte ops)
        (FromByte, [_]) -> return (M.ListOp M.FromByte ops)
        -- (the list of the literal, as a list of Bytes: the numbers are the same)
        (BytesFrom, [M.Const (M.CList items)])
            | all (\i -> case i of M.CInt n -> n >= 0 && n < 256; _ -> False) items -> return (M.Use (M.Const (M.CList items)))
        (BytesFrom, _) -> failL "A list of bytes is written with numbers from 0 to 255"
        (Unsize, [o]) -> return (M.Unsize o)
        (UnBox, [o]) -> return (M.Unbox o)
        (Is variant, [o]) -> return (M.IsVariant o variant)
        (Cast variant, [o]) -> return (M.AsVariant o variant)
        (Within, _) -> failL "within only exists in proofs"
        _ -> failL ("A builtin was applied to the wrong number of arguments: " ++ show b)

-- The constructor that a struct type has, or the variant a value is known to be
structCtor :: Type -> L Name
structCtor ty = do
    t <- tc (zonk ty)
    case t of
        TBox inner -> structCtor inner
        TNamed name -> do
            ctors <- tc (typeCtors name)
            case ctors of
                [ctor] -> return ctor
                _ -> failL ("The field of an enum " ++ name ++ " is read without a cast")
        TVariant variant -> return variant
        _ -> failL "A field is read from something that is not a struct"

varOperand :: Variable -> L (M.Operand, Type)
varOperand name = do
    binding <- lookupBinding name
    s <- getS
    case binding of
        Just (BLocal l ty) -> return (M.Copy l, ty)
        Just (BFn fn ty) -> return (M.Const (M.CFn fn), ty)
        Nothing -> case Map.lookup name (lsGlobals s) of
            Just (fn, ty) -> return (M.Const (M.CFn fn), ty)
            Nothing -> case Map.lookup name stdLibCtx of
                Just builtin -> valueOperand builtin
                Nothing -> failL ("Undefined variable: " ++ name)

valueOperand :: Value -> L (M.Operand, Type)
valueOperand (VFunct _ _ _ (BuiltinFunct b) _) = builtinFunction b
valueOperand VFunct{} = failL "A function is defined by a statement, not written in an expression"
valueOperand v = do
    ty <- tc (valueType v)
    c <- constantOf v
    return (M.Const c, ty)

constantOf :: Value -> L M.Constant
constantOf (VInt i) = return (M.CInt i)
constantOf (VBool b) = return (M.CBool b)
constantOf (VList vs) = M.CList <$> mapM constantOf vs
constantOf (VData name fields) = M.CData name <$> mapM (\(f, v) -> (,) f <$> constantOf v) fields
constantOf VFunct{} = failL "A function is not a constant"
constantOf (VFnRef name) = return (M.CFn name)

-- A builtin used as a value, such as `+` passed to a function, is a function of the program that applies it
builtinFunction :: BuiltinFunct -> L (M.Operand, Type)
builtinFunction b = do
    ft <- tc (builtinType b)
    ft' <- tc (zonk ft)
    case ft' of
        TFn ptys rty -> do
            name <- uniqueName ("builtin::" ++ builtinLabel b)
            outer <- builder
            modifyB (const (newBuilder name False (Just rty)))
            params <- mapM (newLocal Nothing) ptys
            modifyB (\b' -> b'{bParams = params})
            rv <- builtinRvalue b ptys (map M.Copy params)
            emit (M.Assign (M.Local 0) rv)
            terminate M.Return
            inner <- builder
            modifyB (const outer)
            modifyS (\s -> s{lsFunctions = Map.insert name (buildFunction [] [] Nothing Map.empty inner) (lsFunctions s)})
            return (M.Const (M.CFn name), ft')
        _ -> failL "A builtin is not a function"

builtinLabel :: BuiltinFunct -> String
builtinLabel b = case b of
    Size -> "size"
    First -> "first"
    Last -> "last"
    Get -> "get"
    Push -> "push"
    Pop -> "pop"
    Set -> "set"
    NewBox -> "box"
    UnBox -> "unbox"
    NewArray -> "array"
    NewBoxedArray -> "boxed_array"
    NewEmptyArray -> "empty_array"
    Unsize -> "unsize"
    WriteByte -> "writeByte"
    WriteError -> "writeError"
    ReadByte -> "readByte"
    ArgCount -> "argCount"
    ArgByte -> "argByte"
    PathByte -> "pathByte"
    FileLoad -> "fileLoad"
    FileByte -> "fileByte"
    StoreByte -> "storeByte"
    FileStore -> "fileStore"
    ToByte -> "toByte"
    FromByte -> "toInt"
    BytesFrom -> "bytes_from"
    ArrayFrom -> "array_from"
    Plus -> "add"
    Minus -> "sub"
    Times -> "mul"
    Div -> "div"
    Mod -> "mod"
    Rel rel -> "compare_" ++ show rel
    Within -> "within"
    Ctor name _ -> name
    Field _ field -> "field_" ++ field
    Is variant -> "is_" ++ variant
    Project variant field -> variant ++ "." ++ field
    Cast variant -> "as_" ++ variant
