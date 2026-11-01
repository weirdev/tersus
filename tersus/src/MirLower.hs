module MirLower (lowerProgram, lowerElaborated, lowerLibrary) where

import Control.Monad (forM, unless, when)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Mir as M
import MirMoves (checkMoves, stripPositions)
import MirVerify (verifyProgram)
import Pretty (renderType)
import StdLibDefs (stdLibCtx)
import TersusTypes
import TypeCheck (Elaborated (..), arrayElement, elaborate, functionType)
import Utils

-- Lowers a program that has passed validation to the MIR: control flow becomes blocks that jump, nested expressions
-- become temporaries, nested functions are lifted to the top, and the scopes that decide which variable an assignment
-- means are resolved to numbered locals.
--
-- Every local and temporary has a type, which the AST does not carry: `elaborate` hands them over with the
-- program (see TypeCheck.Elaborated), one for each expression in the order the lowering visits them, fully
-- resolved: that is how `x = []` gets the element type that a later `push(x, 1)` decides. The lowering takes
-- the next one as it reaches each expression (`claim`), and infers nothing itself.
lowerProgram :: [Statement] -> Result M.Program String
lowerProgram stmts = elaborate stmts `bindResult` lowerElaborated

-- For a program that `elaborate` has checked and handed back (the pipeline checks a program once)
lowerElaborated :: Elaborated -> Result M.Program String
lowerElaborated = lowerWith True

-- A library of the compiler (lib/lists.tersus and lib/box.tersus), checked for moves like any program:
-- the exemption it had would have let a reference in library code go unchecked (REFERENCES.md, stage 5)
lowerLibrary :: Elaborated -> Result M.Program String
lowerLibrary = lowerWith True

lowerWith :: Bool -> Elaborated -> Result M.Program String
lowerWith checking elaborated@(Elaborated stmts _) =
    case runL (program stmts) ((initialState elaborated){lsChecking = checking}) of
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

-- The type `elaborate` gave the expression the lowering has just reached. A missing one means the
-- elaboration and the lowering disagree about the program, which is a fault in the compiler.
claim :: L Type
claim = do
    s <- getS
    case lsElabTypes s of
        t : rest -> modifyS (\s' -> s'{lsElabTypes = rest}) >> return t
        [] -> failL "Lowering: the elaborated program ran out of expression types"

-- What a name means: a local, or a function of the program
data Binding = BLocal M.Local Type | BFn Name Type

-- The function being built: its locals, the blocks that are done, and the one being written
data Builder = Builder
    { bName :: Name
    , bIsMain :: Bool
    , bSizes :: [Variable] -- the size parameters of the function
    , bTypeParams :: [Variable] -- its type parameters
    , bBorrowed :: [M.Local] -- the parameters it borrows
    , bMutBorrowed :: [M.Local] -- the parameters it may update through (&mut T)
    , bRefTargets :: Map M.Local (M.Local, [M.RefStep]) -- the place each reference local is to, when it was made by &place or &mut place in this function
    , bReturns :: Maybe Type
    , bParams :: [M.Local]
    , bLocals :: Map M.Local M.LocalDecl
    , bNextLocal :: Int
    , bBlocks :: Map M.BlockId M.BasicBlock
    , bNextBlock :: Int
    , bOpen :: Maybe (M.BlockId, [M.Statement]) -- the block being written, with its statements last first; Nothing after a return
    , bScopes :: [Map Variable Binding] -- innermost first
    , bLoops :: Map M.BlockId M.LoopSpec
    , bPlace :: Maybe (Int, Int) -- the place in the source of the statement being lowered, when the program was parsed with places
    }

data LS = LS
    { lsElabTypes :: [Type] -- the types `elaborate` gave the expressions not reached yet, in visit order
    , lsTypes :: Map Name M.TypeDecl
    , lsFunctions :: Map Name M.Function
    , lsNames :: Set.Set Name
    , lsGlobals :: Map Variable (Name, Type) -- the functions defined at the top of the program
    , lsAssigned :: Set.Set Variable -- the names the program assigns other than by defining a function
    , lsBuilder :: Builder
    , lsGenerics :: Map Name ([Variable], [(Variable, Type)]) -- the structs with sizes
    , lsInvariants :: Map Name [ValidationStatement] -- what every value of a struct meets
    , lsChecking :: Bool -- whether the program is checked for values used after they were moved
    , lsCopies :: Set.Set Name -- the structs and enums that implement Copy
    , lsLinear :: Set.Set Name -- the structs and enums that are linear
    , lsExterns :: Set.Set Variable -- the functions that are extern
    , lsDrops :: Set.Set Name -- the structs and enums that have a drop
    , lsPrereg :: Map Variable [Name] -- the names given to the functions defined at the top, before any body is lowered (one for each definition of the name)
    }

initialState :: Elaborated -> LS
initialState (Elaborated stmts types) = LS types Map.empty Map.empty (Set.singleton "main") Map.empty (assignedNames stmts) (newBuilder "main" True Nothing) Map.empty Map.empty True Set.empty Set.empty Set.empty Set.empty Map.empty
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
        , bMutBorrowed = []
        , bRefTargets = Map.empty
        , bReturns = returns
        , bParams = []
        , bLocals = maybe Map.empty (\t -> Map.singleton (M.Local 0) (M.LocalDecl t Nothing)) returns
        , bNextLocal = 1
        , bBlocks = Map.empty
        , bNextBlock = 1
        , bOpen = Just (M.BlockId 0, [])
        , bScopes = [Map.empty]
        , bLoops = Map.empty
        , bPlace = Nothing
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

-- (a block starts with the place of the statement it continues, so that each statement and each call has the one before it)
openBlock :: M.BlockId -> L ()
openBlock id' = do
    modifyB (\b -> b{bOpen = Just (id', [])})
    b <- builder
    mapM_ (\(line, column) -> emit (M.Ghost Map.empty (M.GhostPosition line column))) (bPlace b)

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

-- Every function defined at the top gets its name before any body is lowered, so a body finds the functions
-- defined after it as it finds the ones before it. The names are given in the order of the definitions, as
-- they were when each was given at its definition.
registerTopLevel :: [Statement] -> L ()
registerTopLevel stmts = do
    modifyS (\s -> s{lsExterns = Set.union (lsExterns s) (Set.fromList [name | ExternDef name <- stmts])})
    mapM_ register stmts
  where
    register (Assign var (Val (VFunct _ _ _ (NativeFunct (Signature ptys rty sizes types _ _) _ _) _))) = do
        extern <- Set.member var . lsExterns <$> getS
        assigned <- (\s -> Set.member var (lsAssigned s) && null sizes) <$> getS
        name <- uniqueName (if extern then "extern " ++ var else var)
        modifyS (\s -> s{lsPrereg = Map.insertWith (\new old -> old ++ new) var [name] (lsPrereg s), lsGlobals = if assigned then lsGlobals s else Map.insert var (name, functionType sizes types ptys rty) (lsGlobals s)})
    register _ = return ()

program :: [Statement] -> L M.Program
program stmts = do
    registerTopLevel stmts
    lowerStatements stmts
    -- the definitions past a return of the program are lowered too: a function defined there can be called
    -- from the ones before it, so its body has to be in the program. Its GhostFunction goes in the entry
    -- block, which is kept, where the validator will find it.
    prereg <- lsPrereg <$> getS
    let leftover = [stmt | stmt@(Assign var _) <- stmts, maybe False (not . null) (Map.lookup var prereg)]
    unless (null leftover) $ do
        env <- visibleEnv
        mapM_
            ( \stmt -> case stmt of
                Assign var _ -> do
                    names <- Map.findWithDefault [] var . lsPrereg <$> getS
                    lowerStatement stmt
                    case names of
                        name : _ -> modifyB (\b -> b{bBlocks = Map.adjust (\(M.BasicBlock ss t) -> M.BasicBlock (ss ++ [M.Ghost env (M.GhostFunction name var True)]) t) (M.BlockId 0) (bBlocks b)})
                        [] -> return ()
                _ -> return ()
            )
            leftover
    open <- isOpen
    when open (terminate M.Return)
    b <- builder
    let main' = buildFunction [] [] Nothing Map.empty b
    s <- getS
    unless (null (lsElabTypes s)) (failL "Lowering: the elaborated program has expression types the lowering never reached")
    let functions = Map.elems (lsFunctions s)
    resolved <- mapM resolveFunction (main' : functions)
    let (resolvedMain, others) = case resolved of
            m : rest -> (m, rest)
            [] -> (main', [])
        result = M.completeInstances (M.Program (lsTypes s) (Map.fromList [(M.fnName f, f) | f <- others]) resolvedMain (lsGenerics s) (lsInvariants s))
    case verifyProgram result of
        Error e -> failL ("Lowering produced a malformed program: " ++ e)
        Ok () -> case if lsChecking s then checkMoves (lsCopies s) (lsLinear s) (lsDrops s) result else [] of
            [] -> return (stripPositions result)
            errors -> failL (intercalate "\n" (take 100 (map ("Move error: " ++) errors) ++ ["... and " ++ show (length errors - 100) ++ " more" | length errors > 100]))

-- One type variable the checker never learned (the elements of a list that is never used) is an Int
resolveFunction :: M.Function -> L M.Function
resolveFunction fn = do
    locals <- mapM (\d -> (\t -> d{M.localType = t}) <$> resolveType (M.localType d)) (M.fnLocals fn)
    returns <- mapM resolveType (M.fnReturns fn)
    -- (a struct that is named by types that were not known when it was made, a tuple, has the name of what they came to:
    -- the name a MakeData writes is the resolved type of the local it is assigned to)
    let resolveBlock (M.BasicBlock stmts term) = (\stmts' -> M.BasicBlock stmts' term) <$> mapM resolveStatement stmts
        resolveStatement stmt = case stmt of
            M.Assign l rv -> M.Assign l <$> resolveRvalue l rv
            _ -> return stmt
        resolveRvalue dest rv = case rv of
            M.MakeData name fields
                | Just (TNamed b a) <- M.localType <$> Map.lookup dest locals, baseNameOf name == b -> return (M.MakeData (instanceName b a) fields)
            M.MakeData name fields -> (\n -> M.MakeData n fields) <$> resolveName name
            M.ReadField o name field
                | Just l <- operandLocalOf o, Just (TNamed b a) <- M.localType <$> Map.lookup l locals, baseNameOf name == b -> return (M.ReadField o (instanceName b a) field)
            M.ReadField o name field -> (\n -> M.ReadField o n field) <$> resolveName name
            _ -> return rv
        resolveName name
            | Just ty <- Map.lookup name oldNamed = typeName <$> resolveType ty
            | otherwise = return name
        operandLocalOf o = case o of M.Copy l -> Just l; M.Move l -> Just l; _ -> Nothing
    blocks <- mapM resolveBlock (M.fnBlocks fn)
    -- (an element that no use decided was not looked at when the array was made: what it came to is looked at now)
    mapM_ (mapM_ arrayHolds . universe . M.localType) (Map.elems locals)
    return fn{M.fnLocals = locals, M.fnReturns = returns, M.fnBlocks = blocks}
  where
    universe ty = ty : case ty of
        TList t -> universe t
        TArrayOf t _ -> universe t
        TBox t -> universe t
        TFn args ret -> concatMap universe (ret : args)
        TNamed _ args -> concat [universe u | ArgType u <- args]
        _ -> []
    arrayHolds ty = case ty of
        TArrayOf t _ | not (arrayElement t) -> failL ("Type error: an array holds values that have a size, not " ++ renderType t)
        _ -> return ()
    -- the named types this function had before resolution, by rendered name
    oldNamed = Map.fromList [(instanceName b a, TNamed b a) | ty <- map M.localType (Map.elems (M.fnLocals fn)) ++ maybe [] (: []) (M.fnReturns fn), (b, a) <- subs ty]
    subs ty = case ty of
        TNamed b a -> (b, a) : concat [subs u | ArgType u <- a]
        TList u -> subs u
        TArrayOf u _ -> subs u
        TBox u -> subs u
        TAddr u -> subs u
        TBlock u -> subs u
        TUninit u -> subs u
        TRef u -> subs u
        TFn as r -> concatMap subs (r : as)
        _ -> []

resolveType :: Type -> L Type
resolveType ty = return (defaultType ty)
  where
    defaultType (TVar _) = TInt
    defaultType (TNamed base args) = TNamed base (map defaultArg args)
    defaultType (TAddr t) = TAddr (defaultType t)
    defaultType (TUninit t) = TUninit (defaultType t)
    defaultType (TBlock t) = TBlock (defaultType t)
    defaultType (TList t) = TList (defaultType t)
    defaultType (TArrayOf t n) = TArrayOf (defaultType t) n
    defaultType (TBox t) = TBox (defaultType t)
    defaultType (TRef t) = TRef (defaultType t)
    defaultType (TFn args ret) = TFn (map defaultType args) (defaultType ret)
    defaultType t = t
    defaultArg (ArgType t) = ArgType (defaultType t)
    defaultArg arg = arg

-- The name of the struct a type is (a tuple whose types were not all known when it was made is named again when they are: see resolveFunction)
typeName :: Type -> Name
typeName (TNamed base args) = instanceName base args
typeName _ = ""

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
        , M.fnMutBorrowed = bMutBorrowed b
        , M.fnFrom = []
        , M.fnBlocks = Map.fromList [(rename old, M.BasicBlock stmts (renameTerm t)) | old <- order, Just (M.BasicBlock stmts t) <- [Map.lookup old (bBlocks b)]]
        , M.fnSpec = M.FunctionSpec requires ensures term (Map.fromList [(rename h, spec{M.loopBody = rename (M.loopBody spec)}) | (h, spec) <- Map.toList (bLoops b), Map.member h mapping]) env [] [] []
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
    -- after a return nothing runs, as in the evaluator, which drops the rest: its expression types are
    -- taken and dropped, so the types of what follows the block still line up
    if open then lowerStatements rest else skipStatements rest

-- Takes the expression types of statements that are not lowered (after a return), in the order
-- `elaborate` gave them
skipStatements :: [Statement] -> L ()
skipStatements = mapM_ skipStatement

skipStatement :: Statement -> L ()
skipStatement stmt = case stmt of
    Assign _ (Val (VFunct _ _ _ (NativeFunct _ _ body) _)) -> skipStatements body
    AssignDeref lhs expr -> skipExpr expr >> skipExpr lhs
    Assign _ expr -> skipExpr expr
    Let _ expr -> skipExpr expr
    Return expr -> skipExpr expr
    Block stmts -> skipStatements stmts
    If cond thenStmts elseStmts -> skipExpr cond >> skipStatements thenStmts >> skipStatements elseStmts
    While cond _ _ body -> skipExpr cond >> skipStatements body
    _ -> return ()

skipExpr :: Expression -> L ()
skipExpr expr = do
    _ <- claim
    case expr of
        F funct args -> skipHead funct >> mapM_ skipExpr args
        _ -> return ()
  where
    skipHead funct = case funct of
        Val _ -> return ()
        Var _ -> return ()
        _ -> skipExpr funct

lowerStatement :: Statement -> L ()
lowerStatement stmt =
    case stmt of
        Assign var (Val (VFunct params ins outs (NativeFunct sig term body) _)) -> defineFunction var params ins outs sig term body
        Assign var expr -> do
            (pending, ty) <- lowerLast expr
            dest <- assignTarget var ty
            finishInto dest pending
        AssignDeref lhs expr -> do
            (value, _) <- lowerOperand expr
            (root, steps, _) <- lowerDerefPlace lhs
            emit (M.AssignRef root steps (M.Use value))
        Let var expr -> do
            (pending, ty) <- lowerLast expr
            dest <- newLocal (Just var) ty
            bindName var (BLocal dest ty)
            finishInto dest pending
        Return expr -> lowerReturn expr
        ValidationStatement vs -> ghost (M.GhostValidation vs)
        CopyDef name -> modifyS (\s -> s{lsCopies = Set.insert name (lsCopies s)})
        LinearDef name -> modifyS (\s -> s{lsLinear = Set.insert name (lsLinear s)})
        DropDef name -> modifyS (\s -> s{lsDrops = Set.insert name (lsDrops s)})
        ExternDef name -> modifyS (\s -> s{lsExterns = Set.insert name (lsExterns s)})
        Dissolve var -> do
            binding <- lookupBinding var
            case binding of
                Just (BLocal l _) -> emit (M.Ghost Map.empty (M.GhostDissolve l))
                _ -> failL ("Undefined variable: " ++ var)
        Mark line column -> do
            modifyB (\b -> b{bPlace = Just (line, column)})
            emit (M.Ghost Map.empty (M.GhostPosition line column))
        StructDef name sizes fields invariant | not (null sizes) -> do
            modifyS (\s -> s{lsGenerics = Map.insert name (sizes, fields) (lsGenerics s), lsInvariants = withInvariant name invariant (lsInvariants s)})
        StructDef name _ fields invariant -> do
            addType name (M.StructDecl fields)
            modifyS (\s -> s{lsInvariants = withInvariant name invariant (lsInvariants s)})
        EnumDef name variants -> do
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
        Just (BLocal l _) -> return l
        _ -> do
            l <- newLocal (Just var) ty
            bindName var (BLocal l ty)
            return l

lowerReturn :: Expression -> L ()
lowerReturn expr = do
    -- (a reference parameter that is returned is returned as a reference to its place: in the body the
    -- parameter is the value it is to, and the caller is given the reference, which `from` names)
    b0 <- builder
    (pending, ty) <- case (bReturns b0, expr) of
        (Just (TRef rt), Var v) -> do
            _ <- claim
            binding <- lookupBinding v
            case binding of
                Just (BLocal l _) | l `elem` bBorrowed b0 || l `elem` bMutBorrowed b0 -> return (PRvalue (M.Borrow l [] False), TRef rt)
                _ -> lowerLast expr
        (Just (TMutRef rt), Var v) -> do
            _ <- claim
            binding <- lookupBinding v
            case binding of
                Just (BLocal l _) | l `elem` bMutBorrowed b0 -> return (PRvalue (M.Borrow l [] True), TMutRef rt)
                _ -> lowerLast expr
        _ -> lowerLast expr
    b <- builder
    case bReturns b of
        Just _ -> return ()
        Nothing -> do
            -- the program has no declared type: the first return decides it
            modifyB (\b' -> b'{bReturns = Just ty, bLocals = Map.insert (M.Local 0) (M.LocalDecl ty Nothing) (bLocals b')})
    finishInto (M.Local 0) pending
    terminate M.Return

lowerIf :: Expression -> [Statement] -> [Statement] -> L ()
lowerIf cond thenStmts elseStmts = do
    thenB <- newBlock
    elseB <- newBlock
    joinB <- newBlock
    lowerCondition "condition of if" cond thenB elseB
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

-- A condition ends the block it is lowered in with the jumps it stands for: to one block when it holds and to another when it does not. One made
-- of `&&`, `||` and `!` is a test for each part that is evaluated (`a && b` does not evaluate b when a is false, and so the validator knows
-- a when it checks b: `i < size(l) && get(l, i) = 0`), without the value of a Bool being made.
lowerCondition :: String -> Expression -> M.BlockId -> M.BlockId -> L ()
lowerCondition what cond yes no = do
    ty <- claim
    lowerConditionWith what cond ty yes no

-- A condition whose own type has been taken already (the value of a connective, lowered as a condition)
lowerConditionWith :: String -> Expression -> Type -> M.BlockId -> M.BlockId -> L ()
lowerConditionWith what cond ty condYes condNo = case connective cond of
    Just (And, [a, b]) -> do
        middle <- newBlock
        lowerCondition what a middle condNo
        openBlock middle
        lowerCondition what b condYes condNo
    Just (Or, [a, b]) -> do
        middle <- newBlock
        lowerCondition what a condYes middle
        openBlock middle
        lowerCondition what b condYes condNo
    Just (Not, [a]) -> lowerCondition what a condNo condYes
    _ -> do
        (test, _) <- lowerOperandWith cond ty
        terminate (M.SwitchBool test condYes condNo)

-- The connective that an expression is the application of, and what it is applied to
connective :: Expression -> Maybe (BuiltinFunct, [Expression])
connective (F (Val (VFunct _ _ _ (BuiltinFunct b) _)) args) | b `elem` [And, Or, Not] = Just (b, args)
connective _ = Nothing

lowerWhile :: Expression -> [ValidationStatement] -> Maybe Termination -> [Statement] -> L ()
lowerWhile cond invariant term body = do
    header <- newBlock
    bodyB <- newBlock
    exit <- newBlock
    terminate (M.Goto header)
    openBlock header
    env <- visibleEnv
    modifyB (\b -> b{bLoops = Map.insert header (M.LoopSpec invariant term env bodyB) (bLoops b)})
    lowerCondition "condition of while" cond bodyB exit
    openBlock bodyB
    scoped (lowerStatements body)
    open <- isOpen
    when open (terminate (M.Goto header))
    openBlock exit

-- A function becomes a function of the program, lifted to the top whatever it is nested in (a body sees only its
-- parameters and the functions at the top, so there is nothing to capture). One defined at the top of the program is
-- found by name from the bodies of the functions after it, and from itself; any other is a name in its scope.
defineFunction :: Variable -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> Signature -> Maybe Termination -> [Statement] -> L ()
defineFunction var params ins outs (Signature ptys rty sizes types writes sigFrom) term body = do
    enclosing <- builder
    let atTop = bIsMain enclosing && length (bScopes enclosing) == 1
        fnTy = functionType sizes types ptys rty
    -- (an extern function is named `extern f`, which no program can write: native code calls the C function f)
    extern <- Set.member var . lsExterns <$> getS
    name <-
        if atTop
            then do
                prereg <- lsPrereg <$> getS
                case Map.lookup var prereg of
                    Just (n : rest) -> modifyS (\s -> s{lsPrereg = Map.insert var rest (lsPrereg s)}) >> return n
                    _ -> uniqueName (if extern then "extern " ++ var else var)
            else uniqueName (bName enclosing ++ "::" ++ var)
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
    outer <- builder
    -- the body is lowered as a function of its own, then the outer one goes on
    modifyB (const (newBuilder name False (Just rty)){bSizes = sizes, bTypeParams = types})
    -- (a borrowed parameter is a local of its type, which the function only reads)
    paramLocals <- mapM (\(p, ty) -> (\l -> (p, l, unrefType ty)) <$> newLocal (Just p) (unrefType ty)) (zip params ptys)
    modifyB (\b -> b{bBorrowed = [l | ((_, l, _), ty) <- zip paramLocals ptys, isRefType ty], bMutBorrowed = [l | ((_, l, _), TMutRef _) <- zip paramLocals ptys]})
    modifyB (\b -> b{bParams = [l | (_, l, _) <- paramLocals], bScopes = [Map.fromList [(p, BLocal l ty) | (p, l, ty) <- paramLocals]]})
    env <- visibleEnv
    lowerStatements body
    open <- isOpen
    when open (terminate M.Unreachable)
    inner <- builder
    modifyB (const outer)
    let fn0 = buildFunction ins outs term env inner
        fn = fn0{M.fnSpec = (M.fnSpec fn0){M.specWrites = writes, M.specMutParams = [p | (p, TMutRef _) <- zip params ptys], M.specFrom = sigFrom}, M.fnFrom = [l | (p, l, _) <- paramLocals, p `elem` sigFrom]}
    modifyS (\s -> s{lsFunctions = Map.insert name fn (lsFunctions s)})

unrefType :: Type -> Type
unrefType (TRef t) = t
unrefType (TMutRef t) = t
unrefType t = t

isRefType :: Type -> Bool
isRefType (TRef _) = True
isRefType (TMutRef _) = True
isRefType _ = False

isMutRefType :: Type -> Bool
isMutRefType (TMutRef _) = True
isMutRefType _ = False

-- Expressions

-- The last step of an expression, which gives its value to a local: an operation, or a call (a call ends a block)
data Pending = PRvalue M.Rvalue | PCall M.Operand [M.Operand]

finishInto :: M.Local -> Pending -> L ()
finishInto dest (PRvalue rv@(M.Borrow root steps _)) = do
    emit (M.Assign dest rv)
    modifyB (\b -> b{bRefTargets = Map.insert dest (root, steps) (bRefTargets b)})
finishInto dest (PRvalue rv) = emit (M.Assign dest rv)
finishInto dest (PCall callee args) = do
    open <- isOpen
    when open $ do
        next <- newBlock
        terminate (M.Call callee args dest next)
        openBlock next

-- The operand that holds the value of an expression, and the type of the value
lowerOperand :: Expression -> L (M.Operand, Type)
lowerOperand expr = do
    ty <- claim
    lowerOperandWith expr ty

-- An operand whose expression's type has been taken already
lowerOperandWith :: Expression -> Type -> L (M.Operand, Type)
lowerOperandWith (Val v) ty = valueOperand v ty
lowerOperandWith (Var name) ty = varOperand name ty
lowerOperandWith expr ty = do
    (pending, _) <- lowerLastWith expr ty
    case pending of
        PRvalue (M.Use operand) -> return (operand, ty)
        _ -> do
            temp <- newLocal Nothing ty
            finishInto temp pending
            return (M.Copy temp, ty)

-- The arguments are evaluated left to right, then the operation or call is the last step
lowerLast :: Expression -> L (Pending, Type)
lowerLast expr = do
    ty <- claim
    lowerLastWith expr ty

-- A last step whose expression's type has been taken already
lowerLastWith :: Expression -> Type -> L (Pending, Type)
lowerLastWith (Val v) ty = (\(o, _) -> (PRvalue (M.Use o), ty)) <$> valueOperand v ty
lowerLastWith (Var name) ty = (\(o, _) -> (PRvalue (M.Use o), ty)) <$> varOperand name ty
lowerLastWith expr ty | Just (b, [_, _]) <- connective expr, b `elem` [And, Or] = lowerValueOfConnective expr ty
lowerLastWith (F funct args) ty = do
    target <- resolveHead funct
    case target of
        Builtin b -> lowerBuiltin b args ty
        Callable callee -> do
            operands <- mapM lowerOperand args
            return (PCall callee (map fst operands), ty)

-- A connective where the Bool is wanted (`ok = a && b;`): the whole expression is lowered as a condition, so every test is known to the ones after it (`i >= 0
-- && i < size(l) && get(l, i) = 0`), and the local that holds the value is assigned in each of the two ways to get there
lowerValueOfConnective :: Expression -> Type -> L (Pending, Type)
lowerValueOfConnective expr ty = do
    result <- newLocal Nothing ty
    yesB <- newBlock
    noB <- newBlock
    joinB <- newBlock
    lowerConditionWith "operand of a connective" expr ty yesB noB
    openBlock yesB
    emit (M.Assign result (M.Use (M.Const (M.CBool True))))
    terminate (M.Goto joinB)
    openBlock noB
    emit (M.Assign result (M.Use (M.Const (M.CBool False))))
    terminate (M.Goto joinB)
    openBlock joinB
    return (PRvalue (M.Use (M.Copy result)), ty)

-- What is being applied
data Head = Builtin BuiltinFunct | Callable M.Operand

resolveHead :: Expression -> L Head
resolveHead (Val (VFunct _ _ _ (BuiltinFunct b) _)) = return (Builtin b)
resolveHead (Var name) = do
    binding <- lookupBinding name
    s <- getS
    case binding of
        Just (BLocal l _) -> return (Callable (M.Copy l))
        Just (BFn fn _) -> return (Callable (M.Const (M.CFn fn)))
        Nothing -> case Map.lookup name (lsGlobals s) of
            Just (fn, _) -> return (Callable (M.Const (M.CFn fn)))
            Nothing -> case Map.lookup name stdLibCtx of
                Just (VFunct _ _ _ (BuiltinFunct b) _) -> return (Builtin b)
                _ -> failL ("Undefined variable: " ++ name)
resolveHead other = Callable . fst <$> lowerOperand other

-- A place as the root local it starts from, the steps from there, and its type (REFERENCES.md). Each
-- expression of the place takes the type `elaborate` gave it (`claim`), in the order it gave them: the
-- checker has already decided what a field read and an index give, so the lowering infers nothing here.
lowerPlace :: Expression -> L (M.Local, [M.RefStep], Type)
lowerPlace expr = case expr of
    Var name -> do
        ty <- claim
        binding <- lookupBinding name
        case binding of
            Just (BLocal l _) -> return (l, [], ty)
            _ -> failL ("Lowering failed: " ++ name ++ " is not a value that a place can start from")
    F (Val (VFunct _ _ _ (BuiltinFunct (Field _ field)) _)) [sub] -> do
        fieldTy <- claim
        (root, steps, subTy) <- lowerPlace sub
        ctor <- structCtor subTy
        return (root, steps ++ [M.RefField ctor field], fieldTy)
    F (Val (VFunct _ _ _ (BuiltinFunct Get) _)) [sub, index] -> lowerIndexPlace sub index
    F (Var "get") [sub, index] -> lowerIndexPlace sub index
    F (Val (VFunct _ _ _ (BuiltinFunct DerefOf) _)) [inner] -> do
        ty <- claim
        (root, _) <- lowerRefRoot inner
        return (root, [], ty)
    _ -> do
        (operand, ty) <- lowerOperand expr
        case operand of
            M.Copy l -> return (l, [], ty)
            M.Move l -> return (l, [], ty)
            M.Const _ -> failL "Lowering failed: a reference cannot be to a value that has no place"
  where
    lowerIndexPlace sub index = do
        elementTy <- claim
        (root, steps, _) <- lowerPlace sub
        (indexOperand, _) <- lowerOperand index
        return (root, steps ++ [M.RefIndex indexOperand], elementTy)

-- The local a reference expression stands in, and the type it is a reference to
lowerRefRoot :: Expression -> L (M.Local, Type)
lowerRefRoot (Var name) = do
    _ <- claim
    binding <- lookupBinding name
    b <- builder
    case binding of
        Just (BLocal l ty)
            | isRefType ty -> return (l, unrefType ty)
            | TBox inner <- ty -> return (l, inner)
            | l `elem` bBorrowed b -> return (l, ty)
            | otherwise -> failL ("Lowering failed: " ++ name ++ " is not a reference")
        _ -> failL ("Lowering failed: " ++ name ++ " is not a reference")
lowerRefRoot expr = do
    (operand, ty) <- lowerOperand expr
    case operand of
        M.Copy l -> return (l, unrefType ty)
        M.Move l -> return (l, unrefType ty)
        M.Const _ -> failL "Lowering failed: * of a value that is not a reference"

lowerBorrow :: Bool -> Expression -> Type -> L (Pending, Type)
lowerBorrow mutable place result = do
    (root, steps, _) <- lowerPlace place
    -- (an index of the place is the value it has here, where the reference is made: the reference is to that
    -- element, not to whichever element the index names when the reference is used)
    steps' <- mapM captureStep steps
    return (PRvalue (M.Borrow root steps' mutable), result)
  where
    captureStep (M.RefIndex (M.Copy l)) = captureIndex (M.Copy l)
    captureStep (M.RefIndex (M.Move l)) = captureIndex (M.Move l)
    captureStep step = return step
    captureIndex operand = do
        at <- newLocal Nothing TInt
        emit (M.Assign at (M.Use operand))
        return (M.RefIndex (M.Copy at))

-- `root.steps = value` as assignments of the root: a field is rebuilt from its other fields, an element is `set`
emitAssignPlace :: M.Local -> [M.RefStep] -> M.Operand -> L ()
emitAssignPlace root [] value = emit (M.Assign root (M.Use value))
emitAssignPlace root (M.RefField ctor field : rest) value = do
    types <- lsTypes <$> getS
    case Map.lookup ctor types of
        Just (M.StructDecl fields) -> do
            sub <- newLocal Nothing (fieldTypeOf fields)
            emit (M.Assign sub (M.ReadField (M.Copy root) ctor field))
            emitAssignPlace sub rest value
            rebuilt <- forM fields $ \(f, _) ->
                if f == field
                    then return (f, M.Copy sub)
                    else do
                        kept <- newLocal Nothing (fieldTypeOf' f fields)
                        emit (M.Assign kept (M.ReadField (M.Copy root) ctor f))
                        return (f, M.Copy kept)
            emit (M.Assign root (M.MakeData ctor rebuilt))
        _ -> failL ("Lowering failed: an assignment through a reference is to a field of " ++ ctor ++ ", which is not a struct here")
  where
    fieldTypeOf fields = maybe TInt id (lookup field fields)
    fieldTypeOf' f fields = maybe TInt id (lookup f fields)
emitAssignPlace root (M.RefIndex index : rest) value = do
    subTy <- localTypeOf root
    let elementTy = case subTy of
            TList e -> e
            TArrayOf e _ -> e
            TBox (TArrayOf e _) -> e
            _ -> TInt
    element <- newLocal Nothing elementTy
    emit (M.Assign element (M.ListOp M.Get [M.Copy root, index]))
    emitAssignPlace element rest value
    emit (M.Assign root (M.ListOp M.Set [M.Copy root, index, M.Copy element]))

localTypeOf :: M.Local -> L Type
localTypeOf l = do
    b <- builder
    case Map.lookup l (bLocals b) of
        Just (M.LocalDecl ty _) -> return ty
        Nothing -> return TInt

-- The place an assignment through a reference is to: through an update parameter (the parameter local itself), or
-- through a reference local made by &mut place in this function (the place it was made to). Like `lowerPlace`,
-- each expression of the place takes the type `elaborate` gave it.
lowerDerefPlace :: Expression -> L (M.Local, [M.RefStep], Type)
lowerDerefPlace expr = case expr of
    F (Val (VFunct _ _ _ (BuiltinFunct DerefOf) _)) [inner] -> do
        ty <- claim
        case inner of
            Var name -> do
                _ <- claim
                binding <- lookupBinding name
                b <- builder
                case binding of
                    Just (BLocal l bty)
                        | l `elem` bMutBorrowed b -> return (l, [], ty)
                        | isRefType bty -> case Map.lookup l (bRefTargets b) of
                            Just (root, steps) -> return (root, steps, ty)
                            Nothing
                                | isMutRefType bty -> return (l, [], ty)
                                | otherwise -> failL ("Lowering failed: the place that " ++ name ++ " is a reference to is not known here: a reference that is assigned through must be made by &mut place in this function, or be an update parameter")
                        | otherwise -> failL ("Lowering failed: " ++ name ++ " is not a reference")
                    _ -> failL ("Lowering failed: " ++ name ++ " is not a reference")
            _ -> do
                (root, _) <- lowerRefRoot inner
                return (root, [], ty)
    F (Val (VFunct _ _ _ (BuiltinFunct (Field _ field)) _)) [sub] -> do
        fieldTy <- claim
        (root, steps, subTy) <- lowerDerefPlace sub
        ctor <- structCtor subTy
        return (root, steps ++ [M.RefField ctor field], fieldTy)
    F (Val (VFunct _ _ _ (BuiltinFunct Get) _)) [sub, index] -> lowerDerefIndex sub index
    F (Var "get") [sub, index] -> lowerDerefIndex sub index
    _ -> failL "Lowering failed: an assignment through a reference is to *r, (*r).field or (*r) at an index"
  where
    lowerDerefIndex sub index = do
        elementTy <- claim
        (root, steps, _) <- lowerDerefPlace sub
        (indexOperand, _) <- lowerOperand index
        return (root, steps ++ [M.RefIndex indexOperand], elementTy)

-- The result type is the one `elaborate` gave the application; the checker has already folded the
-- size of an array into it, and decided what a field read, a constructor and each builtin gives
lowerBuiltin :: BuiltinFunct -> [Expression] -> Type -> L (Pending, Type)
lowerBuiltin BorrowOf args result = case args of
    [place] -> lowerBorrow False place result
    _ -> failL "& takes a place"
lowerBuiltin BorrowMutOf args result = case args of
    [place] -> lowerBorrow True place result
    _ -> failL "&mut takes a place"
lowerBuiltin DerefOf args result = case args of
    [inner] -> do
        (operand, _) <- lowerOperand inner
        return (PRvalue (M.Deref operand), result)
    _ -> failL "* takes a reference"
lowerBuiltin b args result = do
    operands <- mapM lowerOperand args
    let tys = map snd operands
    rv <- case (pairParts b, b, map fst operands) of
        (Just (first, second), _, ops) -> pairRvalue b first second result ops
        -- replace(a, i, x): the element is copied out (it is what the list or array held, a value of its own), then x is put in its place
        (_, Replace, [a, i, x]) -> do
            case tupleParts result of
                Just [containerTy, elementTy] -> do
                    view <- newLocal Nothing elementTy
                    emit (M.Assign view (M.ListOp M.Get [a, i]))
                    old <- newLocal Nothing elementTy
                    emit (M.Assign old (M.CopyOf (M.Copy view)))
                    changed <- newLocal Nothing containerTy
                    emit (M.Assign changed (M.ListOp M.Set [a, i, x]))
                    return (M.MakeData (typeName result) [("0", M.Copy changed), ("1", M.Copy old)])
                _ -> failL "The result of replace is not a pair"
        (_, _, ops) -> builtinRvalue b tys ops
    -- (a value built in the check of an instance of a template is built by the name the template wrote, which names
    -- the parameters: the value is of the instance the check is of)
    rv' <- case rv of
        M.MakeData name fields | '<' `elem` name -> case result of
            TNamed cbase _ | baseNameOf name == cbase -> return (M.MakeData (typeName result) fields)
            _ -> return rv
        _ -> return rv
    return (PRvalue rv', result)

-- The forms that give two things, an address or a value and a permission: each is two operations, and the tuple of what they give
pairParts :: BuiltinFunct -> Maybe (M.ListOp, M.ListOp)
pairParts b = case b of
    AllocPair -> Just (M.AddrAlloc, M.BlockNew)
    TakePair -> Just (M.AddrTake, M.BlockTaken)
    ResizePair -> Just (M.AddrResize, M.BlockResized)
    SplitPair -> Just (M.BlockSplitLo, M.BlockSplitHi)
    _ -> Nothing

-- The first operation reads the permission (the second takes it), and the second is given what the first made where it needs it:
-- Addr::alloc(n) is p = AddrAlloc(n), b = BlockNew(p, n); Addr::take(p, i, b) is x = AddrTake(p, i, b), b2 = BlockTaken(b, i);
-- Addr::resize(p, n, b) is q = AddrResize(p, n, b), b2 = BlockResized(b, q, n); Block::split(b, i) is BlockSplitLo(b, i), BlockSplitHi(b, i)
pairRvalue :: BuiltinFunct -> M.ListOp -> M.ListOp -> Type -> [M.Operand] -> L M.Rvalue
pairRvalue b first second result ops = do
    case tupleParts result of
        Just [firstTy, secondTy] -> do
            x <- newLocal Nothing firstTy
            emit (M.Assign x (M.ListOp first ops))
            y <- newLocal Nothing secondTy
            secondOps <- case (b, ops) of
                (AllocPair, [n]) -> return [M.Copy x, n]
                (TakePair, [_, i, blk]) -> return [blk, i]
                (ResizePair, [_, n, blk]) -> return [blk, M.Copy x, n]
                (SplitPair, _) -> return ops
                _ -> failL ("A builtin was applied to the wrong number of arguments: " ++ show b)
            emit (M.Assign y (M.ListOp second secondOps))
            return (M.MakeData (typeName result) [("0", M.Copy x), ("1", M.Copy y)])
        _ -> failL ("The result of " ++ show b ++ " is not a pair")

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
        (ArrayFromList, [_]) -> return (M.ListOp M.FromList ops)
        -- (the list of the literal, held as an array)
        (ArrayFrom, [M.Const (M.CList items)]) -> return (M.Use (M.Const (M.CArray items)))
        (ArrayFrom, [o]) -> return (M.Use o)
        (Plus, [x, y]) -> return (M.BinaryOp M.Add x y)
        (Minus, [x, y]) -> return (M.BinaryOp M.Sub x y)
        (Times, [x, y]) -> return (M.BinaryOp M.Mul x y)
        (Div, [x, y]) -> return (M.BinaryOp M.Div x y)
        (Mod, [x, y]) -> return (M.BinaryOp M.Mod x y)
        (Rel rel, [x, y]) -> return (M.BinaryOp (M.Compare rel) x y)
        (Not, [x]) -> return (M.BinaryOp (M.Compare Eq) x (M.Const (M.CBool False)))
        -- (a tuple is a literal of the instance of its struct for the types of its parts)
        (Ctor name _ fields, _) | Just _ <- tupleGeneric name, length fields == length ops -> return (M.MakeData (typeName (tupleType tys)) (zip fields ops))
        (Ctor name _ fields, _) | length fields == length ops -> return (M.MakeData name (zip fields ops))
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
        (ToWord signed bits, [_]) -> return (M.ListOp (M.Narrow signed bits) ops)
        -- (the list of the literal, as a list of Bytes: the numbers are the same)
        (BytesFrom, [M.Const (M.CList items)])
            | all (\i -> case i of M.CInt n -> n >= 0 && n < 256; _ -> False) items -> return (M.Use (M.Const (M.CList items)))
        (BytesFrom, _) -> failL "A list of bytes is written with numbers from 0 to 255"
        (Unsize, [o]) -> return (M.Unsize o)
        (UnBox, [o]) -> return (M.Unbox o)
        (CloneOf, [o]) -> return (M.CopyOf o)
        (Is variant, [o]) -> return (M.IsVariant o variant)
        (Cast variant, [o]) -> return (M.AsVariant o variant)
        (Within, _) -> failL "within only exists in proofs"
        _ | Just op <- pointerOp b -> return (M.ListOp op ops)
        _ -> failL ("A builtin was applied to the wrong number of arguments: " ++ show b)

-- The operations on addresses and permissions that are one operation of the MIR
pointerOp :: BuiltinFunct -> Maybe M.ListOp
pointerOp b = lookup b
    [ (AddrNull, M.AddrNull), (AddrOffset, M.AddrOffset), (AddrCast, M.AddrCast), (AddrToInt, M.AddrToInt), (AddrFromInt, M.AddrFromInt)
    , (AddrAlloc, M.AddrAlloc), (AddrGet, M.AddrGet), (AddrWrite, M.AddrWrite), (AddrTake, M.AddrTake), (AddrDropValue, M.AddrDropValue)
    , (AddrDropRange, M.AddrDropRange), (AddrResize, M.AddrResize), (AddrFree, M.AddrFree)
    , (BlockNew, M.BlockNew), (BlockTaken, M.BlockTaken), (BlockResized, M.BlockResized), (BlockSplitLo, M.BlockSplitLo)
    , (BlockSplitHi, M.BlockSplitHi), (BlockJoin, M.BlockJoin), (BlockAssume, M.BlockAssume), (BlockCast, M.BlockCast)
    , (UninitEmpty, M.UninitEmpty), (UninitNew, M.UninitNew), (UninitGet, M.UninitGet), (UninitTake, M.UninitTake), (UninitDiscard, M.UninitDiscard)
    ]

-- The constructor that a struct type has, or the variant a value is known to be
structCtor :: Type -> L Name
structCtor ty = case ty of
    TBox inner -> structCtor inner
    TNamed base args -> do
        let name = instanceName base args
        s <- getS
        let ctors = case Map.lookup name (lsTypes s) of
                Just (M.StructDecl _) -> [name]
                Just (M.EnumDecl variants) -> map fst variants
                Nothing -> case Map.lookup base (lsTypes s) of
                    Just (M.StructDecl _) -> [name]
                    Just (M.EnumDecl variants) -> map fst variants
                    Nothing
                        | Map.member base (lsGenerics s) -> [name]
                        | Just _ <- tupleGeneric base -> [name]
                        | otherwise -> []
        case ctors of
            [ctor] -> return ctor
            _ -> failL ("The field of an enum " ++ name ++ " is read without a cast")
    TVariant variant -> return variant
    _ -> failL "A field is read from something that is not a struct"

varOperand :: Variable -> Type -> L (M.Operand, Type)
varOperand name ty = do
    binding <- lookupBinding name
    s <- getS
    case binding of
        Just (BLocal l _) -> return (M.Copy l, ty)
        Just (BFn fn _) -> return (M.Const (M.CFn fn), ty)
        Nothing -> case Map.lookup name (lsGlobals s) of
            Just (fn, _) -> return (M.Const (M.CFn fn), ty)
            Nothing -> case Map.lookup name stdLibCtx of
                Just builtin -> valueOperand builtin ty
                Nothing -> failL ("Undefined variable: " ++ name)

valueOperand :: Value -> Type -> L (M.Operand, Type)
valueOperand (VFunct _ _ _ (BuiltinFunct b) _) ty = builtinFunction b ty
valueOperand VFunct{} _ = failL "A function is defined by a statement, not written in an expression"
valueOperand v ty = do
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
builtinFunction :: BuiltinFunct -> Type -> L (M.Operand, Type)
builtinFunction b ft' = do
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
    CloneOf -> "clone"
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
    ArrayFromList -> "array_from_list"
    Plus -> "add"
    Minus -> "sub"
    Times -> "mul"
    Div -> "div"
    Mod -> "mod"
    Rel rel -> "compare_" ++ show rel
    Within -> "within"
    Ctor name _ _ -> name
    Field _ field -> "field_" ++ field
    Is variant -> "is_" ++ variant
    Project variant field -> variant ++ "." ++ field
    Cast variant -> "as_" ++ variant
    other -> show other
