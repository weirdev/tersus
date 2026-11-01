module TypeCheck
    ( typeCheck
    , elaborate
    , Elaborated (..)
    , PreparedPrefix
    , preparePrefix
    , elaborateAfter
    , gatheredSignatures
    ) where

import Control.Monad (filterM, forM, forM_, unless, void, when)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (intercalate, isInfixOf, (\\))
import Data.Maybe (isJust, isNothing, fromMaybe)
import qualified Data.Set as Set

import BuiltinRegistry (SigScheme (..), ghostBuiltinByName, methodBuiltinByName, methodNameFor, pointerBuiltinByName, signatureScheme)
import Pretty (renderType)
import StdLib
import StdLibDefs (stdLibCtx)
import Types
import Syntax
import Utils
import TypeCheckCore

-- Types are checked between parsing and validation. Parameters and return types are written in the
-- program, locals take the type of their first assignment, and the builtins have the signatures below.
-- Checking is unification inside one function body, with no polymorphism for user functions.

typeCheck :: [Statement] -> Result () String
typeCheck stmts = mapResult (const ()) (elaborate stmts)

-- Checks the program and gives it back with each `shrinks e` resolved by the type of e: an Int counts down to 0 (Counting),
-- an enum or struct loses a field at a time (Parts). The validator only sees the resolved clauses.
--
-- The result also carries the type of every expression of the program's code, fully resolved, in the order the
-- lowering visits those expressions: an expression, then the expression it applies when that is itself computed
-- (not a name or a value), then its arguments, statement by statement (a function's body where it is defined).
-- That is all the lowering needs to give every local and temporary its type, so it never infers a type itself.
data Elaborated = Elaborated [Statement] [Type]
    deriving (Show)

data PreparedPrefix = PreparedPrefix Ctx Env [Statement] [Type] TcState

preparePrefix :: Map Variable Type -> [Statement] -> Result PreparedPrefix String
preparePrefix gathered stmts = case runTcState (checkStatementsWithContext True (Ctx gathered Nothing) [Map.empty] stmts) initialTcState of
    Left err -> Error err
    Right ((ctx, env, stmts', types), state) -> Ok (PreparedPrefix ctx env stmts' types state)

elaborateAfter :: PreparedPrefix -> [Statement] -> Result Elaborated String
elaborateAfter (PreparedPrefix ctx env prefix prefixTypes state) stmts =
    case runTcState checked state of
        Left err -> Error err
        Right (elaborated, _) -> Ok elaborated
  where
    checked = do
        (_, stmts', types) <- checkStatements True ctx env stmts
        resolved <- mapM zonk (prefixTypes ++ types)
        return (Elaborated (prefix ++ stmts') resolved)

elaborate :: [Statement] -> Result Elaborated String
elaborate stmts = preparePrefix (gatheredSignatures stmts) [] `bindResult` \prefix -> elaborateAfter prefix stmts

-- An expression looked through one step, by a call of its type's `deref` where it has a Deref impl. Nothing for a Box (whose
-- look-through the language gives, in the type) and for anything that is not looked through.
derefStepExpr :: Ctx -> Env -> TExpr -> TC (Maybe TExpr)
derefStepExpr ctx env texpr = do
    t <- zonk (tType texpr)
    case t of
        TBox _ -> return Nothing
        _ -> do
            target <- derefTarget t
            case target of
                Just _ -> do
                    owner <- derefOwner t
                    Just <$> inferExprR ctx env (F (Var (implFunctionName owner (Just "Deref") "deref")) [tExpr texpr])
                Nothing -> return Nothing

-- An expression looked through to the value it holds, a step at a time (see derefStepExpr). The result is the value that is
-- looked at, so what is read from it, tested or taken apart is a view of a value the calls give, and the value it came from is
-- only lent to them.
derefExpr :: Ctx -> Env -> TExpr -> TC TExpr
derefExpr ctx env texpr = do
    next <- derefStepExpr ctx env texpr
    case next of
        Just stepped -> derefExpr ctx env stepped
        Nothing -> return texpr

-- The invariant of a struct is written with the names of its fields, and a function of the program defined before the struct may be called
checkInvariant :: Ctx -> [(Variable, Type)] -> [ValidationStatement] -> TC [ValidationStatement]
checkInvariant _ _ [] = return []
checkInvariant ctx fields invariant = do
    (_, checked) <- checkValidations ctx [Map.fromList fields] invariant
    return checked

-- The signature of every function defined at the top is known before any body is checked, so a function
-- can call the ones defined after it (and they can call it back). A name the language itself gives a
-- meaning (a builtin, or a ghost function of proofs such as `filled`) is not gathered: in a proof
-- before its definition such a name is the language's, as it was when it was only seen after it.
gatheredSignatures :: [Statement] -> Map Variable Type
gatheredSignatures stmts = Map.fromList [(var, functionType sizes types ptys rty) | Assign var (Val (VFunct _ _ _ (NativeFunct (Signature ptys rty sizes types _ _) _ _) _)) <- stmts, not (Map.member var stdLibCtx), ghostFunction var == Nothing]

-- Statements run in order; a top-level function is visible to the functions after it, and the
-- returned environment holds the variables the statements defined in the innermost scope.
checkStatements :: Bool -> Ctx -> Env -> [Statement] -> TC (Env, [Statement], [Type])
checkStatements top ctx env stmts = do
    (_, env', stmts', types) <- checkStatementsWithContext top ctx env stmts
    return (env', stmts', types)

checkStatementsWithContext :: Bool -> Ctx -> Env -> [Statement] -> TC (Ctx, Env, [Statement], [Type])
checkStatementsWithContext _ ctx env [] = return (ctx, env, [], [])
checkStatementsWithContext top ctx env (stmt : rest) = do
    (ctx', env', stmts', types) <- checkItem top ctx env stmt
    -- (the functions that templates were made into while it was checked come before it)
    made <- if top then takeEmitted else return []
    let (madeStmts, madeTypes) = unzip made
    (ctxAfter, envAfter, rest', restTypes) <- checkStatementsWithContext top ctx' env' rest
    return (ctxAfter, envAfter, madeStmts ++ stmts' ++ rest', concat madeTypes ++ types ++ restTypes)

takeEmitted :: TC [(Statement, [Type])]
takeEmitted = do
    s <- getState
    putState s{tcEmitted = []}
    return (tcEmitted s)

-- A trait is taken apart here and an impl becomes the functions it defines (and the checks of the trait's contracts, see
-- implementation), so each statement gives back the statements that stand for it
checkItem :: Bool -> Ctx -> Env -> Statement -> TC (Ctx, Env, [Statement], [Type])
checkItem top ctx env stmt =
    case stmt of
        TraitDef name params functions
            | top -> checkTrait name params functions >> return (ctx, env, [], [])
            | otherwise -> failTc "Type error: a trait can only be defined at the top of the program"
        ImplDef trait traitArgs typeName selfType bounds functions
            | top -> do
                -- (a copy of a linear value would use it twice, and a copy of a value with a drop would be dropped twice)
                when (trait == Just "Clone") $ do
                    s <- getState
                    when (Set.member typeName (tcLinear s)) $
                        failTc ("Type error: impl Clone for " ++ typeName ++ ": " ++ typeName ++ " is linear, so a value of it is used exactly once and is never copied")
                    when (Set.member typeName (tcDrops s)) $
                        failTc ("Type error: impl Clone for " ++ typeName ++ ": " ++ typeName ++ " has a drop, and a copy of a value with a drop would be dropped twice")
                (ctx', env', functions', ftypes) <- checkImpl ctx env trait traitArgs typeName selfType bounds functions
                return (ctx', env', functions', ftypes)
            | otherwise -> failTc "Type error: an impl can only be written at the top of the program"
        BoundedDef bounds (Assign name (Val (VFunct params ins outs (NativeFunct signature term body) _)))
            | top -> do
                declareTemplate ctx name bounds params signature ins outs term body
                return (ctx, env, [], [])
            | otherwise -> failTc "Type error: a function with bounds on its types can only be defined at the top of the program"
        BoundedDef{} -> failTc "Type error: only a function can have bounds on its types"
        _ -> do
            (ctx', env', stmt', types) <- checkStatement top ctx env stmt
            return (ctx', env', [stmt'], types)

-- Also gives the statement back with its termination clauses resolved, and the types of its code
-- expressions in the order the lowering visits them (a function's body where it is defined)
checkStatement :: Bool -> Ctx -> Env -> Statement -> TC (Ctx, Env, Statement, [Type])
checkStatement top ctx env stmt =
    case stmt of
        Assign var (Val (VFunct params ins outs (NativeFunct (Signature ptys rty sizes types _writes _from) term body) proofs)) -> do
            templates <- tcTemplates <$> getState
            when (Map.member var templates) $ failTc ("Type error: " ++ var ++ " is already defined")
            let fnTy = functionType sizes types ptys rty
                ctx' = if top then ctx{ctxFns = Map.insert var fnTy (ctxFns ctx)} else ctx
            env' <- assignVar ctx env var fnTy
            (term', ins', outs', body', bodyTypes, from) <- checkFunction ctx' var params ptys rty sizes types ins outs _writes _from term body
            st <- getState
            unless (null from) $ putState st{tcRefResults = Map.insert var (params, from) (tcRefResults st)}
            return (ctx', env', Assign var (Val (VFunct params ins' outs' (NativeFunct (Signature ptys rty sizes types _writes from) term' body') proofs)), bodyTypes)
        AssignDeref lhs expr -> do
            -- (the place must be through an update reference; the value is evaluated before the replacement, which
            -- the lowering keeps by lowering the value first, so its types come first here too)
            lhsT <- inferExprR ctx env lhs
            let targetTy = tType lhsT
            case derefRoot lhs of
                Just refExpr -> do
                    st <- getState
                    mutable <- case refExpr of
                        Var var | var `elem` tcMutParams st -> return True
                        _ -> do
                            rtT <- inferExprR ctx env refExpr
                            rtz <- zonk (tType rtT)
                            return (isMutRef rtz)
                    unless mutable $ failTc "Type error: assignment is through a read reference (&T), which does not allow updating what it is to: borrow the place with &mut"
                    -- (a writes footprint bounds which places of an update parameter this function may change,
                    -- through a reference a local holds as much as through the parameter itself)
                    case (placeSteps lhs, tcWrites st) of
                        (Just (root, steps), writes@(_ : _)) -> do
                            let place = resolveRefPlace st root steps
                            when (fst place `elem` tcMutParams st) $
                                unless (withinWrites writes place) $
                                    failTc ("Type error: this assignment changes " ++ writesTarget place ++ ", which the writes clause of the function does not allow (writes(" ++ intercalate ", " writes ++ "))")
                        _ -> return ()
                Nothing -> failTc "Type error: assignment through a reference is written *r = value; or (*r).field = value;"
            inferred <- inferExprR ctx env expr
            exprT <- coerce targetTy inferred
            return (ctx, env, AssignDeref (tExpr lhsT) (tExpr exprT), tTypes exprT ++ tTypes lhsT)
        Assign var expr -> do
            notSize var
            inferred <- inferExprR ctx env expr
            -- (a variable that has a type already is given a value of it)
            texpr <- case [existing | scope <- env, Just existing <- [Map.lookup var scope]] of
                existing : _ -> coerce existing inferred
                [] -> return inferred
            env' <- assignVar ctx env var (tType texpr)
            recordAlias var (tType texpr) (tExpr texpr)
            recordOrigins ctx env var (tType texpr) (tExpr texpr)
            return (ctx, env', Assign var (tExpr texpr), tTypes texpr)
        Let var expr -> do
            notSize var
            texpr <- inferExprR ctx env expr
            recordAlias var (tType texpr) (tExpr texpr)
            recordOrigins ctx env var (tType texpr) (tExpr texpr)
            case env of
                scope : outer -> return (ctx, Map.insert var (tType texpr) scope : outer, Let var (tExpr texpr), tTypes texpr)
                [] -> return (ctx, [Map.singleton var (tType texpr)], Let var (tExpr texpr), tTypes texpr)
        Return expr -> do
            inferred0 <- inferExprR ctx env expr
            -- (a reference parameter returned is the reference: in the body the parameter is the value it is to,
            -- and returning it is returning a reference to the caller's place, which `from` names)
            inferred <- case (ctxReturn ctx, inferred0, expr) of
                (Just rty, texpr@(TExpr _ _ _), Var v)
                    | Just rt <- refTarget rty -> do
                        tz <- zonk (tType texpr)
                        st <- getState
                        if isRefType tz || (v `elem` tcReadOnly st || v `elem` tcMutParams st)
                            then case texpr of TExpr _ e inner -> expect "returned value" rt tz >> return (TExpr rty e inner)
                            else return inferred0
                _ -> return inferred0
            texpr <- maybe (return inferred) (\rty -> coerce rty inferred) (ctxReturn ctx)
            let t = tType texpr
            case ctxReturn ctx of
                Just rty -> do
                    expect "returned value" rty t
                    -- (a reference that is returned has to be from a parameter the signature names)
                    st <- getState
                    case tcResultFrom st of
                        Just froms -> do
                            origins <- exprRefOrigins ctx env expr
                            unless (not (null origins) && all (`elem` froms) origins) $
                                failTc ("Type error: the value returned is not a reference from " ++ intercalate ", " froms ++ ", which the signature names: return a reference to a place of one of them")
                        Nothing -> return ()
                -- the program has no declared type: every return in it has the type of the first
                Nothing -> do
                    when (isRefType t) $ failTc "Type error: the program cannot return a reference: a reference is from a place in the program, and no place outlives it"
                    s <- getState
                    case tcProgramReturn s of
                        Nothing -> putState s{tcProgramReturn = Just t}
                        Just first -> expect "returned value of the program" first t
            return (ctx, env, Return (tExpr texpr), tTypes texpr)
        ValidationStatement vs -> do
            (env', vs') <- checkValidation ctx env vs
            return (ctx, env', ValidationStatement vs', [])
        StructDef name params fields invariant
            | not (null params) -> do
                declareGeneric name params fields
                invariant' <- withGenerics (filter (not . isTypeName) params) (filter isTypeName params) (checkInvariant ctx fields invariant)
                return (ctx, env, StructDef name params fields invariant', [])
        StructDef name _ fields invariant -> do
            declareType name
            mapM_ (checkFieldType . snd) fields
            registerCtors name [(name, fields)]
            checkFinite name [fields]
            invariant' <- checkInvariant ctx fields invariant
            return (ctx, env, StructDef name [] fields invariant', [])
        EnumDef name variants -> do
            -- the type is known before its fields are checked, so a variant may hold the enum itself
            declareTypeWith name (map fst variants)
            mapM_ (mapM_ (\(_, ty) -> checkFieldType ty) . snd) variants
            registerCtors name variants
            checkFinite name (map snd variants)
            return (ctx, env, stmt, [])
        AxiomDef{} -> return (ctx, env, stmt, [])
        ProofDef{} -> return (ctx, env, stmt, [])
        Mark{} -> return (ctx, env, stmt, [])
        Dissolve var -> lookupVar ctx env var >> return (ctx, env, stmt, [])
        CopyDef{} -> return (ctx, env, stmt, [])
        DropDef{} -> return (ctx, env, stmt, [])
        ExternDef _ -> return (ctx, env, stmt, [])
        LinearDef name -> do
            getState >>= \s -> putState s{tcLinear = Set.insert name (tcLinear s)}
            return (ctx, env, stmt, [])
        TraitDef{} -> failTc "Type error: a trait can only be defined at the top of the program"
        ImplDef{} -> failTc "Type error: an impl can only be written at the top of the program"
        BoundedDef{} -> failTc "Type error: a function with bounds on its types cannot be written in an impl or a block"
        Block stmts -> do
            (_, stmts', types) <- checkStatements False ctx (Map.empty : env) stmts
            return (ctx, env, Block stmts', types)
        If cond thenStmts elseStmts -> do
            cond' <- inferExprR ctx env cond
            expect "condition of if" TBool (tType cond')
            (_, thenStmts', thenTypes) <- checkStatements False ctx (Map.empty : env) thenStmts
            (_, elseStmts', elseTypes) <- checkStatements False ctx (Map.empty : env) elseStmts
            return (ctx, env, If (tExpr cond') thenStmts' elseStmts', tTypes cond' ++ thenTypes ++ elseTypes)
        While cond invariant term body -> do
            cond' <- inferExprR ctx env cond
            expect "condition of while" TBool (tType cond')
            (_, invariant') <- checkValidations ctx env invariant
            term' <- resolveTermination ctx env term
            (_, body', bodyTypes) <- checkStatements False ctx (Map.empty : env) body
            return (ctx, env, While (tExpr cond') invariant' term' body', tTypes cond' ++ bodyTypes)

-- The body sees its parameters, the functions defined before it (and itself), and nothing else
checkFunction :: Ctx -> Variable -> [Variable] -> [Type] -> Type -> [Variable] -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> [Variable] -> [Variable] -> Maybe Termination -> [Statement] -> TC (Maybe Termination, [ValidationStatement], [ValidationStatement], [Statement], [Type], [Variable])
checkFunction ctx name params ptys rty sizes types ins outs writes fromNames term body = do
    outer <- getState
    -- the sizes and types the function declares are the names its types may use, and the sizes are the last parameters (Ints)
    putState outer{tcSizeScope = sizes, tcTypeScope = types, tcCurrent = Just name}
    when (length sizes /= length (nub' sizes) || any (`elem` take (length params - length sizes) params) sizes) $
        failTc ("Type error: function " ++ name ++ " names a size twice, or the same as a parameter")
    from <- refResultFrom name params ptys rty fromNames
    mapM_ checkType ptys
    case rty of
        TRef inner -> checkType inner
        _ -> checkType rty
    if length params /= length ptys
        then failTc ("Type error: function " ++ name ++ " has " ++ show (length params) ++ " parameters but " ++ show (length ptys) ++ " types")
        else return ()
    let bodyCtx = ctx{ctxReturn = Just rty}
        paramEnv = [Map.fromList (zip params (map unref ptys))]
    -- (a parameter that is borrowed is only read; one that may update is assigned only through it)
    withBorrowed <- getState
    putState withBorrowed{tcReadOnly = [p | (p, TRef _) <- zip params ptys], tcMutParams = [p | (p, TMutRef _) <- zip params ptys], tcWrites = writes, tcRefAliases = Map.empty, tcResultFrom = if null from then Nothing else Just from, tcParams = params, tcRefOrigins = Map.empty}
    -- (writes(...) names update parameters, whole or by a field)
    forM_ writes $ \w -> do
        let (root, field) = case break (== '.') w of
                (r, '.' : f) -> (r, Just f)
                (r, _) -> (r, Nothing)
        case lookup root (zip params ptys) of
            Just (TMutRef referent) -> case field of
                Nothing -> return ()
                Just f -> do
                    fieldTy <- readField Nothing f referent
                    _ <- zonk fieldTy
                    return ()
            _ -> failTc ("Type error: writes(" ++ w ++ ") in " ++ name ++ " does not name an update parameter (&mut T) of the function")
    let outsOld = map rewriteOldStatement outs
    (inEnv, ins') <- checkValidations bodyCtx paramEnv ins
    term' <- resolveTermination bodyCtx inEnv term
    (_, outs') <- checkValidations bodyCtx (Map.insert "return" rty (Map.fromList [("$old " ++ p, unref t) | (p, t) <- zip params ptys, isMutRef t] `Map.union` head inEnv) : tail inEnv) outsOld
    (_, body', bodyTypes) <- checkStatements False bodyCtx (Map.empty : paramEnv) body
    -- (the sizes of the function end with it)
    after <- getState
    putState after{tcSizeScope = tcSizeScope outer, tcTypeScope = tcTypeScope outer, tcReadOnly = tcReadOnly outer, tcMutParams = tcMutParams outer, tcWrites = tcWrites outer, tcRefAliases = tcRefAliases outer, tcResultFrom = tcResultFrom outer, tcParams = tcParams outer, tcRefOrigins = tcRefOrigins outer, tcCurrent = tcCurrent outer}
    return (term', ins', outs', body', bodyTypes, from)
  where
    nub' = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- A size is given by the call and is the same for the whole function
notSize :: Variable -> TC ()
notSize var = do
    s <- getState
    when (var `elem` tcReadOnly s) $
        failTc ("Type error: " ++ var ++ " is borrowed (&), so it is only read: a copy of it can be assigned to another variable")
    when (var `elem` tcMutParams s) $
        failTc ("Type error: " ++ var ++ " is borrowed (&mut), so it is assigned through it, as in *" ++ var ++ " = value;: the parameter itself cannot be assigned")
    when (var `elem` tcSizeScope s) $
        failTc ("Type error: " ++ var ++ " is a size parameter of the function, which a call gives, and it cannot be assigned")

-- What shrinks is an integer, which counts down to 0, or a struct or enum value, which loses a field at a time
resolveTermination :: Ctx -> Env -> Maybe Termination -> TC (Maybe Termination)
resolveTermination ctx env (Just (Shrinks variant)) = do
    variant0 <- inferExprR ctx env variant
    -- (what shrinks is what the value is looked through to, as for a Box: the parts of that are smaller)
    variant'' <- derefExpr ctx env variant0
    ty <- zonk (tType variant'')
    let variant' = tExpr variant''
    case ty of
        TInt -> return (Just (Counting variant'))
        TNamed _ _ -> return (Just (Parts variant'))
        TVariant _ -> return (Just (Parts variant'))
        TBox _ -> return (Just (Parts variant'))
        _ -> failTc ("Type error: shrinks needs an Int, an enum or a struct, got " ++ renderType ty)
resolveTermination _ _ term = return term

checkValidations :: Ctx -> Env -> [ValidationStatement] -> TC (Env, [ValidationStatement])
checkValidations _ env [] = return (env, [])
checkValidations ctx env (vs : rest) = do
    (env', vs') <- checkValidation ctx env vs
    (envAfter, rest') <- checkValidations ctx env' rest
    return (envAfter, vs' : rest')

checkValidation :: Ctx -> Env -> ValidationStatement -> TC (Env, ValidationStatement)
checkValidation ctx env vs =
    case vs of
        ProofAssert proof -> do
            (t, proof') <- inferProofR ctx env proof
            expect "affirmed proof" TBool t
            return (env, ProofAssert proof')
        Assume proof -> do
            (t, proof') <- inferProofR ctx env proof
            expect "assumed proof" TBool t
            return (env, Assume proof')
        AssignProofVar var expr -> do
            -- (a define is the validator's, so it can read what is known of a permission: `define o = origin(b);`)
            outer <- tcGhost <$> getState
            getState >>= \s -> putState s{tcGhost = True}
            texpr <- inferExprR ctx env expr
            getState >>= \s -> putState s{tcGhost = outer}
            env' <- assignVar ctx env var (tType texpr)
            return (env', AssignProofVar var (tExpr texpr))
        Rewrite rule -> do
            rule' <- case rule of
                Refl proof -> Refl . snd <$> inferProofR ctx env proof
                Eval var -> Eval var <$ lookupVar ctx env var
                EvalAll -> return rule
                CheckGtZero proof -> CheckGtZero . snd <$> inferProofR ctx env proof
                CheckRel proof -> CheckRel . snd <$> inferProofR ctx env proof
                UserRewrite name proofs -> UserRewrite name <$> mapM (fmap snd . inferProofR ctx env) proofs
            return (env, Rewrite rule')

-- Expressions and proofs

-- The type of an expression, and the expression with each call of a function that belongs to a type resolved: x.f(a) and
-- Trait::f(x, a) are calls of Type::f for the type of x, and nothing after the checker sees anything else.
inferExprR :: Ctx -> Env -> Expression -> TC TExpr
inferExprR ctx env expr =
    case expr of
        Val value -> (\t -> tLeaf t expr) <$> valueType value
        Var var -> do
            t <- lookupVar ctx env var
            t' <- zonk t
            case t' of
                TForall sizes types _ -> failTc ("Type error: " ++ var ++ " has parameters <" ++ intercalate ", " (types ++ sizes) ++ ">, so it is called, as in " ++ var ++ "(...), and cannot be used as a value")
                _ -> return (tLeaf t expr)
        F funct@(Val (VFunct _ _ _ (BuiltinFunct (Field owner field)) _)) [struct] -> do
            struct0 <- inferExprR ctx env struct
            -- (a field of the value itself is read as it is, and so is one of each value it is looked through to in turn; a field
            -- none of them has is read from the last of them, which is where the error names it)
            let go texpr = do
                    direct <- tryTc (readField owner field (tType texpr))
                    case direct of
                        Just t -> return (t, texpr)
                        Nothing -> do
                            next <- derefStepExpr ctx env texpr
                            case next of
                                Just stepped -> go stepped
                                Nothing -> do
                                    t <- readField owner field (tType texpr)
                                    return (t, texpr)
            (t, struct'') <- go struct0
            return (TExpr t (F funct [tExpr struct'']) [struct''])
        F funct@(Val (VFunct _ _ _ (BuiltinFunct (Ctor name ctorArgs fields)) _)) args -> do
            inferred0 <- mapM (inferExprR ctx env) args
            -- (a tuple's parts are what they are: it is made of their types)
            unless (isJust (tupleGeneric (baseNameOf name))) $ ensureInstance (TNamed (baseNameOf name) ctorArgs)
            declared <- if isJust (tupleGeneric (baseNameOf name)) then return [] else snd <$> ctorInfo name
            inferred <- if length declared == length inferred0 then mapM (uncurry coerce) (zip (map snd declared) inferred0) else return inferred0
            t <- checkConstruct (TNamed (baseNameOf name) ctorArgs) fields (map tType inferred)
            return (TExpr t (F funct (map tExpr inferred)) inferred)
        -- &place, &mut place: a reference to a place (REFERENCES.md, stages 2 and 3)
        F (Val (VFunct _ _ _ (BuiltinFunct BorrowOf) _)) [place] -> borrowCall False place
        F (Val (VFunct _ _ _ (BuiltinFunct BorrowMutOf) _)) [place] -> borrowCall True place
        F (Val (VFunct _ _ _ (BuiltinFunct BorrowOf) _)) args -> failTc ("Type error: & takes a place, got " ++ show (length args) ++ " arguments")
        F (Val (VFunct _ _ _ (BuiltinFunct BorrowMutOf) _)) args -> failTc ("Type error: &mut takes a place, got " ++ show (length args) ++ " arguments")
        -- *r: the value a reference is to
        F (Val (VFunct _ _ _ (BuiltinFunct DerefOf) _)) [inner] -> do
            st <- getState
            case inner of
                Var var | var `elem` tcReadOnly st || var `elem` tcMutParams st -> do
                    inner' <- inferExprR ctx env inner
                    return (TExpr (tType inner') (F (Val (builtinFunct DerefOf)) [tExpr inner']) [inner'])
                _ -> do
                    inner' <- inferExprR ctx env inner
                    etz <- zonk (tType inner')
                    case etz of
                        TRef t -> return (TExpr t (F (Val (builtinFunct DerefOf)) [tExpr inner']) [inner'])
                        TMutRef t -> return (TExpr t (F (Val (builtinFunct DerefOf)) [tExpr inner']) [inner'])
                        _ -> failTc ("Type error: * is only through a reference, and the value here is " ++ renderType etz ++ ": write *r for a reference r, or clone(x) for a copy of a value")
        F (Val (VFunct _ _ _ (BuiltinFunct DerefOf) _)) args -> failTc ("Type error: * takes a reference, got " ++ show (length args) ++ " arguments")
        F (Val (VFunct _ _ _ (BuiltinFunct OldOf) _)) _ -> failTc "Type error: old(...) is only written in a postcondition, of the place an update parameter is to"
        -- Box::new(x): x held in a Box, which has its value
        F (Var "Box::new") args -> case args of
            [x] -> do
                x' <- inferExprR ctx env x
                return (TExpr (TBox (tType x')) (F (Val (builtinFunct NewBox)) [tExpr x']) [x'])
            _ -> failTc ("Type error: Box::new takes 1 argument, got " ++ show (length args))
        -- Box::unbox(b): the value that b holds
        F (Var "Box::unbox") args -> case args of
            [b] -> do
                b' <- inferExprR ctx env b
                t <- zonk (tType b')
                case t of
                    TBox (TArrayOf _ SizeAny) -> failTc "Type error: Box::unbox cannot take an array of no size out of its Box, since it would not know how much to take: read its elements with get and size"
                    TBox inner -> return (TExpr inner (F (Val (builtinFunct UnBox)) [tExpr b']) [b'])
                    _ -> failTc ("Type error: Box::unbox takes a Box, got " ++ renderType t)
            _ -> failTc ("Type error: Box::unbox takes 1 argument, got " ++ show (length args))
        -- Array::empty(): an array of no elements, of the element type that the program decides
        F (Var "Array::empty") args -> case args of
            [] -> do
                elementTy <- freshVar
                let ty = TArrayOf elementTy SizeAny
                return (TExpr (TBox ty) (F (Val (builtinFunct NewEmptyArray)) []) [])
            _ -> failTc ("Type error: Array::empty takes no arguments, got " ++ show (length args))
        -- Array::fromList(xs): the array of the elements of a list, which is taken: its size is the size the result is used at
        F (Var "Array::fromList") args -> case args of
            [xs] -> do
                xs' <- inferExprR ctx env xs
                xtz <- zonk (tType xs')
                case xtz of
                    TList elementTy -> do
                        size <- freshSize
                        let ty = TArrayOf elementTy size
                        arrayOk ty
                        return (TExpr ty (F (Val (builtinFunct ArrayFromList)) [tExpr xs']) [xs'])
                    _ -> failTc ("Type error: Array::fromList takes a list, got " ++ renderType xtz)
            _ -> failTc ("Type error: Array::fromList takes 1 argument, got " ++ show (length args))
        -- Array::uninit(n): n slots that hold nothing, in a Box that carries the size
        F (Var "Array::uninit") args -> case args of
            [n] -> inferExprR ctx env (F (Var "Array::boxed") [n, F (Var "Uninit::empty") []])
            _ -> failTc ("Type error: Array::uninit takes 1 argument, got " ++ show (length args))
        -- Array::boxed(n, x): n copies of x, n known only when the program runs, in a Box that carries the size
        F (Var "Array::boxed") args -> case args of
            [n, x] -> do
                n' <- inferExprR ctx env n
                expect "argument 1 of Array::boxed" TInt (tType n')
                x' <- inferExprR ctx env x
                let ty = TArrayOf (tType x') SizeAny
                arrayOk ty
                requireClone (tType x')
                return (TExpr (TBox ty) (F (Val (builtinFunct NewBoxedArray)) [tExpr n', tExpr x']) [n', x'])
            _ -> failTc ("Type error: Array::boxed takes 2 arguments, got " ++ show (length args))
        F funct args
            | Just NewArray <- builtinHead ctx env funct -> case args of
                [n, x] -> do
                    n' <- inferExprR ctx env n
                    expect "argument 1 of array" TInt (tType n')
                    x' <- inferExprR ctx env x
                    (size, sizeArg) <- arraySize (constantInt (tExpr n')) (tExpr n')
                    let ty = TArrayOf (tType x') size
                    arrayOk ty
                    requireClone (tType x')
                    return (TExpr ty (F funct [sizeArg, tExpr x']) [tLeaf TInt sizeArg, x'])
                _ -> failTc ("Type error: array takes 2 arguments, got " ++ show (length args))
        F (Val (VFunct _ _ _ (BuiltinFunct ArrayFrom) _)) [Val literal@(VList items)] -> do
            listTy <- valueType literal
            case listTy of
                TList e -> do
                    let ty = TArray e (fromIntegral (length items))
                    arrayOk ty
                    literalOk e
                    return (TExpr ty expr [tLeaf listTy (Val literal)])
                _ -> failTc "Type error: an array literal is made from a list"
        F (Val (VFunct _ _ _ (BuiltinFunct CloneOf) _)) args -> cloneCall args
        -- clone(x) and x.clone(): a copy of x, which has its value (unless the program has a function of that name)
        F (Var "clone") args
            | not (Map.member "clone" (ctxFns ctx)), not (any (Map.member "clone") env) -> cloneCall args
        F (Var ".clone") args@[receiver] -> do
            receiver' <- inferExprR ctx env receiver
            t <- zonk (tType receiver')
            s <- getState
            let owned = case t of
                    TNamed base _ -> Map.member (base, "clone") (tcAssoc s)
                    _ -> False
            if owned then methodCall "clone" args else cloneCall args
        F (Var ('.' : method)) (receiver : args) -> methodCall method (receiver : args)
        -- what is known of a permission, in an expression of the validator (a define); in code it is not a value there is
        F (Var name) args
            | Just b <- ghostFunction name, b `notElem` [AddrNull, AddrOffset, AddrCast, AddrToInt, AddrFromInt], not (any (Map.member name) env), not (Map.member name (ctxFns ctx)) -> do
              -- (only of a permission: a function of the program named `count`, as a template is, is the program's)
              ofPermission <- permissionArgument b args (\e -> (\te -> (tType te, e)) <$> inferExprR ctx env e)
              if not ofPermission then general (Var name) args else do
                ghostly <- tcGhost <$> getState
                unless ghostly $ failTc ("Type error: " ++ name ++ " is what the validator knows of a permission, and is not a value the program has: it is written in an affirm, a contract, an invariant or a define")
                inferred <- mapM (inferExprR ctx env) args
                ft <- builtinType b
                case (b, inferred) of
                    _ | b `elem` [BlockFilled, BlockContents], [u'] <- inferred -> do
                        let b' = if b == BlockFilled then UninitFilled else UninitAt
                        ft' <- builtinType b'
                        result <- checkCall name ft' [tType u']
                        return (TExpr result (F (Val (builtinFunct b')) [tExpr u']) [u'])
                    _ | b `elem` [BlockFilled, BlockContents] -> case inferred of
                        [b', i'] -> do
                            listTy <- checkCall name ft [tType b']
                            expect ("argument 2 of " ++ name) TInt (tType i')
                            elementTy <- freshVar
                            expect name (TList elementTy) listTy
                            let inner = TExpr listTy (F (Val (builtinFunct b)) [tExpr b']) [b']
                            return (TExpr elementTy (F (Val (builtinFunct Get)) [tExpr inner, tExpr i']) [inner, i'])
                        _ -> failTc ("Type error: " ++ name ++ " takes a permission and a slot, as in " ++ name ++ "(b, i)")
                    _ -> do
                        result <- checkCall name ft (map tType inferred)
                        return (TExpr result (F (Val (builtinFunct b)) (map tExpr inferred)) inferred)
        -- Addr::alloc(n), Addr::get(p, i, b), Block::split(b, i), ...: the operations on addresses and permissions (POINTERS.md)
        F (Var name) args
            | Just b <- pointerBuiltin name, not (any (Map.member name) env), not (Map.member name (ctxFns ctx)) -> do
                inferred0 <- mapM (inferExprR ctx env) args
                ft <- builtinType b
                inferred <- coerceArguments ft inferred0
                result <- checkBuiltinCall (Just b) name ft (map tType inferred)
                return (TExpr result (F (Val (builtinFunct b)) (map tExpr inferred)) inferred)
        F (Var name@('<' : _)) args -> mapM (inferExprR ctx env) args >>= callResolved name
        F (Var name) args
            | Just (path, function) <- traitPath name -> traitCall path function args
        -- a = b and a != b in code: the words of a value of a primitive type are compared, and any other value is compared by its Eq
        -- (lib/eq.tersus); in an expression of the validator (a define) it is the validator's equality, as in a proof
        F funct@(Val (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) [a, b]
            | rel `elem` [Eq, NotEq] -> do
                ghostly <- tcGhost <$> getState
                if ghostly then general funct [a, b] else do
                    inferred <- mapM (inferExprR ctx env) [a, b]
                    let [at, bt] = map tType inferred
                    at' <- unref <$> zonk at
                    bt' <- unref <$> zonk bt
                    expect "argument 2 of the comparison" at' bt'
                    -- (an empty list compared before what it holds is known is a list of Int)
                    zonk at' >>= defaultUnknown
                    t0 <- zonk at'
                    -- (a Box has the value of what it holds, so two Boxes are compared by what they hold: a function of a type that
                    -- holds itself in a Box compares the parts by calling itself)
                    let unboxed (TBox inner@(TArrayOf _ SizeAny)) operands = (TBox inner, operands)
                        unboxed (TBox inner) operands = unboxed inner [TExpr inner (F (Val (builtinFunct UnBox)) [tExpr e]) [e] | e <- operands]
                        unboxed other operands = (other, operands)
                        (t, operands) = unboxed t0 inferred
                    if primitiveEq t
                        then do
                            functT <- inferExprR ctx env funct
                            ordinaryBuiltin funct functT (tType functT) operands
                        else do
                            comparing funct [t]
                            callT <- case t of
                                TBox (TArrayOf _ SizeAny) -> do
                                    gives <- traitArguments "Eq" t
                                    when (isNothing gives) $ failTc ("Type error: " ++ renderType t ++ " is compared with =, which needs its elements to implement Eq")
                                    callResolved "eqBoxedArrays" operands
                                _ -> equalityCall t operands
                            return (if rel == NotEq then TExpr TBool (F (Val (builtinFunct Not)) [tExpr callT]) [callT] else callT)
        F funct args -> general funct args
  where
    defaultUnknown t = case t of
        TVar _ -> void (unify t TInt)
        TList u -> defaultUnknown u
        TBox u -> defaultUnknown u
        TArrayOf u _ -> defaultUnknown u
        _ -> return ()
    equalityCall t inferred = do
        s <- getState
        unless (Map.member "Eq" (tcTraits s)) $
            failTc ("Type error: " ++ renderType t ++ " is compared with =, which needs the trait Eq of lib/eq.tersus, which a program has unless it declares a trait Eq of its own")
        gives <- traitArguments "Eq" t
        when (isNothing gives) $ case t of
            TVar _ -> failTc "Type error: the type of the values compared is not known yet; annotate it"
            TParam p -> failTc ("Type error: " ++ p ++ " is compared with =, which needs it to implement Eq: bound it, as in <" ++ p ++ ": Eq>")
            _ -> do
                lacking <- missingEq t
                failTc ("Type error: " ++ renderType t ++ " is compared with =, which needs it to implement Eq, and " ++ lacking)
        owner <- traitOwner "eq" t
        callResolved (implFunctionName owner (Just "Eq") "eq") inferred
    -- (which part of a type has no Eq, to say what to write)
    missingEq t = case t of
        TList e -> inner t e
        TBox e -> inner t e
        TArrayOf e _ -> inner t e
        TNamed base args -> do
            s <- getState
            if Set.member ("Eq", base) (tcImpls s)
                then do
                    parts <- filterM (fmap isNothing . traitArguments "Eq") [u | ArgType u <- args]
                    case parts of
                        u : _ -> missingEq u
                        [] -> return (renderType t ++ " does not")
                else return (base ++ " does not: write impl Eq for " ++ base ++ " { }; to compare its fields")
        TVariant variant -> ctorInfo variant >>= \(enum, _) -> return (enum ++ " does not: write impl Eq for " ++ enum ++ " { }; to compare its fields")
        _ -> return (renderType t ++ " does not")
      where
        inner whole e = do
            ok <- traitArguments "Eq" e
            if isJust ok then return (renderType whole ++ " does not") else zonk e >>= missingEq
    borrowCall mutable place = do
        unless (placeForm place) $ failTc "Type error: & is to a place (a variable, a field of one, an element of one, or through a reference, as in &p.x, &get(xs, 0) or &*r): bind the value to a variable first if it needs borrowing"
        st <- getState
        placeT <- case place of
            F (Val (VFunct _ _ _ (BuiltinFunct DerefOf) _)) [inner] -> do
                innerT <- inferExprR ctx env inner
                itz <- zonk (tType innerT)
                case itz of
                    TBox innerTy -> return (TExpr innerTy (F (Val (builtinFunct DerefOf)) [tExpr innerT]) [innerT])
                    _ -> inferExprR ctx env place
            _ -> inferExprR ctx env place
        let pt = tType placeT
            place' = tExpr placeT
        ptz <- zonk pt
        case ptz of
            TRef _ -> failTc "Type error: a reference to a reference is not in the language: write &*r to borrow what a reference is to"
            TMutRef _ -> failTc "Type error: a reference to a reference is not in the language: write &*r to borrow what a reference is to"
            _ -> return ()
        when mutable $ do
            case placeRoot place of
                Just root | root `elem` tcReadOnly st -> failTc ("Type error: " ++ root ++ " is lent (&T) to this function and can only be read, so it cannot be borrowed for updating (&mut)")
                _ -> return ()
            case place of
                F (Val (VFunct _ _ _ (BuiltinFunct DerefOf) _)) [inner] -> do
                    itT <- inferExprR ctx env inner
                    itz <- zonk (tType itT)
                    case itz of
                        TRef _ -> failTc "Type error: an update reference (&mut) cannot be made through a read reference (&T): the read reference does not allow updating what it is to"
                        _ -> return ()
                _ -> return ()
        return (TExpr (if mutable then TMutRef ptz else TRef ptz) (F (Val (builtinFunct (if mutable then BorrowMutOf else BorrowOf))) [place']) [placeT])
    placeForm expr = case expr of
        Var _ -> True
        F (Val (VFunct _ _ _ (BuiltinFunct (Field _ _)) _)) [sub] -> placeForm sub
        F (Val (VFunct _ _ _ (BuiltinFunct Get) _)) [sub, _] -> placeForm sub
        F (Var "get") [sub, _] -> placeForm sub
        F (Val (VFunct _ _ _ (BuiltinFunct DerefOf) _)) [_] -> True
        _ -> False
    placeRoot expr = case expr of
        Var var -> Just var
        F (Val (VFunct _ _ _ (BuiltinFunct (Field _ _)) _)) [sub] -> placeRoot sub
        F (Val (VFunct _ _ _ (BuiltinFunct Get) _)) [sub, _] -> placeRoot sub
        F (Var "get") [sub, _] -> placeRoot sub
        F (Val (VFunct _ _ _ (BuiltinFunct DerefOf) _)) [sub] -> placeRoot sub
        _ -> Nothing
    cloneCall args = case args of
        [x] -> do
            x' <- inferExprR ctx env x
            let xt = tType x'
            xtz <- zonk xt
            case xtz of
                TBlock _ -> requireClone xt >> return x'
                TUninit e -> do
                    owning <- ownsHeap e
                    if owning
                        then requireClone xt >> return x'
                        else return (TExpr xt (F (Val (builtinFunct CloneOf)) [tExpr x']) [x'])
                -- (a word, an address or a function is its own copy: there is no impl of Clone for them to call)
                TInt -> return x'
                TByte -> return x'
                TBool -> return x'
                TWord _ _ -> return x'
                TAddr _ -> return x'
                TFn _ _ -> return x'
                -- (a reference is a word: the copy of it is it)
                TRef _ -> return x'
                TMutRef _ -> return x'
                -- (a type parameter of a function that is checked for all of its types at once (not a template, which is
                -- checked for each of the types it is given, where this is the call of its Clone): the copy is the value
                -- itself, as the copies the checker makes for its own reasons are, and no code of an impl runs for it)
                TParam _ -> return (TExpr xt (F (Val (builtinFunct CloneOf)) [tExpr x']) [x'])
                TVar _ -> return (TExpr xt (F (Val (builtinFunct CloneOf)) [tExpr x']) [x'])
                _ | mentionsParameter xtz -> return (TExpr xt (F (Val (builtinFunct CloneOf)) [tExpr x']) [x'])
                -- (a Box of an array of no size is cloned element by element, as a Box of one is compared (lib/clone.tersus))
                TBox (TArrayOf _ SizeAny) -> do
                    s <- getState
                    if Map.member "cloneBoxedArray" (tcTemplates s) || Map.member "cloneBoxedArray" (ctxFns ctx)
                        then general (Var "cloneBoxedArray") [x]
                        else traitCall "Clone" "clone" [x]
                -- (a tuple is cloned part by part, as a struct is by its impl)
                TNamed base args | Just _ <- tupleGeneric base -> do
                    let name = instanceName base args
                    (_, fields) <- ctorInfo name
                    parts <- mapM (\(field, _) -> cloneCall [F (Val (builtinFunct (Field (Just name) field))) [tExpr x']]) fields
                    return (TExpr xt (F (Val (builtinFunct (Ctor name args (map fst fields)))) (map tExpr parts)) parts)
                _ -> traitCall "Clone" "clone" [x]
        _ -> failTc ("Type error: clone takes 1 argument, got " ++ show (length args))
    methodCall method (receiver : args) = do
            inferred <- mapM (inferExprR ctx env) (receiver : args)
            receiverTy <- unref <$> zonk (tType (head inferred))
            case (listMethod method, receiverTy) of
                -- l.push(x), l.size(), a.get(i): the function of that name on a list or an array
                -- (with the arguments that are inferred already: a chain of them is inferred once)
                (Just b, ty) | sequenceType ty -> do
                    let funct = Val (builtinFunct b)
                    funct' <- inferExprR ctx env funct
                    ordinaryBuiltin funct funct' (tType funct') inferred
                _ -> do
                    owner <- ownerOfValue method (tType (head inferred))
                    resolveAssociated owner method >>= \name -> callResolved name inferred
    methodCall _ [] = failTc "Type error: a method is called on a value"
    -- Trait::f(x) and Type::f(x)
    traitCall path function args = do
                s <- getState
                case (Map.lookup path (tcTraits s), Map.member path (tcTypes s) || Map.member path (tcGenerics s)) of
                    (Just functions, _) -> do
                        inferred <- mapM (inferExprR ctx env) args
                        primed <- primitiveTraitCall ctx env path functions function inferred
                        case primed of
                            Just done -> return done
                            Nothing -> do
                                owner <- ownerThroughTrait path functions function (map tType inferred)
                                callResolved (implFunctionName owner (Just path) function) inferred
                    (Nothing, True) -> do
                        inferred <- mapM (inferExprR ctx env) args
                        resolveAssociated path function >>= \full -> callResolved full inferred
                    _ -> general (Var (path ++ "::" ++ function)) args
    general funct args = do
        texpr <- generalDispatch funct args
        -- (a reference result has to come from a function whose signature names what it is from, called by name:
        -- through a function value the origin cannot be told)
        case tType texpr of
            t | isRefType t -> do
                st <- getState
                unless (case funct of Var name -> Map.member name (tcRefResults st) || Just name == tcCurrent st; Val _ -> True; _ -> False) $
                    failTc "Type error: this call returns a reference, but what the result is from is not known: a reference result comes from a function whose signature names it (as in -> &T from xs), called by name"
            _ -> return ()
        return texpr
    generalDispatch funct args = do
        s <- getState
        case funct of
            Var name | Just template <- Map.lookup name (tcTemplates s), not (any (Map.member name) env) -> do
                inferred <- mapM (inferExprR ctx env) args
                (result, instance', args', sizes) <- templateCall ctx name template inferred
                return (TExpr result (F (Var instance') (map tExpr (args' ++ sizes))) (args' ++ sizes))
            _ -> generalCall funct args
    generalCall funct args = do
        (ft, funct') <- case funct of
            Var name | Nothing <- builtinHead ctx env funct -> (\t -> (t, tLeaf t funct)) <$> lookupVar ctx env name
            _ -> (\te -> (tType te, te)) <$> inferExprR ctx env funct
        ftz <- zonk ft
        case ftz of
            TForall sizes types inner -> do
                inferredG <- mapM (inferExprR ctx env) args
                (result, args') <- genericCall (describe funct) sizes types inner inferredG
                return (TExpr result (F (tExpr funct') (map tExpr args')) (headTExpr funct' ++ args'))
            _ -> ordinary funct funct' ft args
    headTExpr funct' = case tExpr funct' of
        F{} -> [funct']
        _ -> []
    ordinary funct funct' ft args = do
        inferred0 <- mapM (inferExprR ctx env) args
        -- (size(v), get(v, i), ... on a value of a struct are the functions of its impl)
        owner <- case (builtinHead ctx env funct, inferred0) of
            (Just b, xt : _) | Just fname <- sequenceFunction b -> (,) fname <$> structOwner (tType xt)
            _ -> return ("", Nothing)
        case owner of
            (fname, Just struct) -> resolveAssociated struct fname >>= \full -> callResolved full inferred0
            _ -> ordinaryBuiltin funct funct' ft inferred0
    ordinaryBuiltin funct funct' ft inferred0 = do
        -- (a value that is tested for its variant, cast to one or read for a field is looked through what it holds first, Box or Deref)
        inferred0 <- case (builtinHead ctx env funct, inferred0) of
            (Just b, first : rest) | isLookThrough b -> do
                first' <- derefExpr ctx env first
                return (first' : rest)
            _ -> return inferred0
        -- (a builtin takes what it is given: it looks through a Box itself)
        inferred <- case builtinHead ctx env funct of
            -- (the builtins of bytes take a number written out as a Byte)
            Just b | b `elem` [WriteByte, WriteError, PathByte, StoreByte] -> coerceArguments ft inferred0
            Just _ -> return inferred0
            Nothing -> coerceArguments ft inferred0
        let ats = map tType inferred
        result <- checkBuiltinCall (builtinHead ctx env funct) (describe funct) ft ats
        comparing funct ats
        return (TExpr result (F (tExpr funct') (map tExpr inferred)) (headTExpr funct' ++ inferred))
    describe (Var name) = name
    describe _ = "call"
    isSuffixOf' suffix text = reverse suffix == take (length suffix) (reverse text)
    -- the call of a function of the program by name, with arguments that are checked already
    callResolved name inferred0 = do
        -- (a drop is called by native code where a value goes out of scope, and by the check of its impl, and by nothing else)
        current <- tcCurrent <$> getState
        when (" as Drop>::drop" `isSuffixOf'` name && maybe True (\c -> take 9 c /= "Drop for ") current) $
            failTc ("Type error: " ++ name ++ " is a drop, which is called where a value goes out of scope, and not by the program")
        templates <- tcTemplates <$> getState
        case Map.lookup name templates of
            Just template -> do
                (result, instanceName', args', sizeGiven) <- templateCall ctx name template inferred0
                return (TExpr result (F (Var instanceName') (map tExpr (args' ++ sizeGiven))) (args' ++ sizeGiven))
            Nothing -> do
                unless (Map.member name (ctxFns ctx)) $
                    failTc ("Type error: " ++ name ++ " is not defined before this call (there is no such function, or its impl comes later)")
                ft <- lookupVar ctx env name
                ftz <- zonk ft
                case ftz of
                    -- (a function of `impl<T> Vec<T>` has the types and sizes of the impl: the arguments decide them)
                    TForall sizes types inner -> do
                        (result, args') <- genericCall name sizes types inner inferred0
                        return (TExpr result (F (Var name) (map tExpr args')) args')
                    _ -> do
                        inferred <- coerceArguments ft inferred0
                        result <- checkCall name ft (map tType inferred)
                        return (TExpr result (F (Var name) (map tExpr inferred)) inferred)

-- The function that Type::f means: the one function of that name that the impls of Type define. If several do, the call has
-- to say which, with Trait::f(x), <Type as Trait>::f(...) or <Type>::f(...).
resolveAssociated :: Name -> Name -> TC Name
resolveAssociated owner function = do
    s <- getState
    case Map.findWithDefault [] (owner, function) (tcAssoc s) of
        [] -> failTc ("Type error: " ++ owner ++ "::" ++ function ++ " is not defined before this call (there is no such function, or its impl comes later)")
        [origin] -> return (implFunctionName owner origin function)
        origins ->
            failTc
                ( "Type error: "
                    ++ owner
                    ++ "::"
                    ++ function
                    ++ " is ambiguous, several impls define it. Call the one that is meant by its path: "
                    ++ intercalate " or " [implFunctionName owner origin function ++ "(...)" | origin <- origins]
                )

-- Trait::function
traitPath :: Name -> Maybe (Name, Name)
traitPath = go ""
  where
    go acc (':' : ':' : rest) | not (null acc) && not (null rest) = Just (reverse acc, rest)
    go acc (c : rest) = go (c : acc) rest
    go _ [] = Nothing

-- The struct or enum a value belongs to, whose function a call names
ownerOfValue :: Name -> Type -> TC Name
ownerOfValue function ty = do
    t <- zonk ty
    case t of
        -- (a struct with types and sizes has the functions of its impl, whatever it is given)
        TNamed base _ -> return base
        TInt -> return "Int"
        TByte -> return "Byte"
        TBool -> return "Bool"
        TList _ -> return "List"
        TVariant variant -> fst <$> ctorInfo variant
        TVar _ -> failTc ("Type error: the type of the value whose function " ++ function ++ " is called is not known yet; annotate it")
        other@TBox{} -> failTc ("Type error: " ++ function ++ " is called on a " ++ renderType other ++ ", which has no functions: call it on the value inside, as in Box::unbox(b)." ++ function ++ "(...)")
        other -> failTc ("Type error: " ++ function ++ " is called on a " ++ renderType other ++ ", which has no functions")

-- The type that owns an impl, for a call through a trait: a struct or enum, a list, an array and a Box, which are the types an
-- impl can be written for. (A call of a method on a Box is refused by ownerOfValue instead, since it is called on what it holds.)
traitOwner :: Name -> Type -> TC Name
traitOwner function ty = do
    t <- zonk ty
    case t of
        TArrayOf _ _ -> return "Array"
        TBox _ -> return "Box"
        _ -> ownerOfValue function ty

-- Trait::function(x, ...) is the function of the type of the argument that the trait's signature gives the type Self. That
-- type must implement the trait.
ownerThroughTrait :: Name -> [TraitFn] -> Name -> [Type] -> TC Name
ownerThroughTrait trait functions function ats =
    case [f | f <- functions, traitFnName f == function] of
        [] -> failTc ("Type error: trait " ++ trait ++ " has no function " ++ function)
        f : _ -> do
            let Signature ptys _ _ _ _writes _from = traitFnSignature f
                path = trait ++ "::" ++ function
            when (length ptys /= length ats) $
                failTc ("Type error: " ++ path ++ " takes " ++ show (length ptys) ++ " arguments, got " ++ show (length ats))
            case [i | (i, t) <- zip [0 :: Int ..] ptys, unref t == TNamed "Self" []] of
                [] -> failTc ("Type error: " ++ path ++ " has no Self parameter to tell the type by: call it on the type, as in Type::" ++ function ++ "(...)")
                i : _ -> do
                    -- (through a trait an array and a Box of one have the impls written for them, as a list does; called as a
                    -- method they are looked through or refused as they were)
                    owner <- traitOwner path (ats !! i)
                    impls <- tcImpls <$> getState
                    unless (Set.member (trait, owner) impls) $ failTc ("Type error: " ++ owner ++ " does not implement " ++ trait)
                    return owner

-- The words implement Eq by the language, so a call of Eq::eq on them is the builtin comparison rather than a function:
-- `Eq::eq(a, b)` on words says what `a = b` does, and there is no impl of it to call
primitiveTraitCall :: Ctx -> Env -> Name -> [TraitFn] -> Name -> [TExpr] -> TC (Maybe TExpr)
primitiveTraitCall ctx env "Eq" functions "eq" inferred = do
    case [f | f <- functions, traitFnName f == "eq"] of
        f : _ | length inferred == 2 -> do
            let [a, b] = inferred
            at' <- unref <$> zonk (tType a)
            bt' <- unref <$> zonk (tType b)
            if primitiveEq at' && primitiveEq bt'
                then do
                    let Signature ptys rty _ _ _ _ = traitFnSignature f
                    expect "argument 1 of Eq::eq" at' (unref (tType a))
                    expect "argument 2 of Eq::eq" bt' (unref (tType b))
                    return (Just (TExpr rty (F (Val (VFunct [] [] [] (BuiltinFunct (Rel Eq)) [])) [tExpr a, tExpr b]) [a, b]))
                else return Nothing
        _ -> return Nothing
primitiveTraitCall _ _ _ _ _ _ = return Nothing

-- Traits and impls

-- The functions of a trait have their types and contracts checked with Self as a type that has no constructors, so a
-- mistake in the trait is reported at the trait and not at its first impl
checkTrait :: Name -> [Variable] -> [TraitFn] -> TC ()
checkTrait name params functions = do
    s <- getState
    when (Map.member name (tcTraits s) || Map.member name (tcTypes s)) $ failTc ("Type error: " ++ name ++ " is already defined")
    putState s{tcTypes = Map.insert "Self" [] (tcTypes s), tcTraitSelf = Just (functions ++ concat (Map.elems (tcTraits s)))}
    -- (the types of the trait are types in its signatures and contracts)
    withGenerics [] params $ forM_ functions $ \f -> do
        let Signature ptys rty _ _ _writes _from = traitFnSignature f
            ctx = Ctx Map.empty (Just rty)
            paramEnv = [Map.fromList (zip (traitFnParams f) (map unref ptys))]
        mapM_ checkType (rty : ptys)
        (inEnv, _) <- checkValidations ctx paramEnv (traitFnRequires f)
        _ <- checkValidations ctx (Map.insert "return" rty (head inEnv) : tail inEnv) (traitFnEnsures f)
        return ()
    s' <- getState
    let refResults = [(name ++ "::" ++ traitFnName f, (traitFnParams f, froms)) | f <- functions, let Signature ptys rty _ _ _ fromNames = traitFnSignature f, let froms = if not (null fromNames) then fromNames else case [p | (p, t) <- zip (traitFnParams f) ptys, isRefType t] of [only] -> [only]; _ -> [], not (null froms), isRefType rty || False]
    putState s'{tcTypes = Map.delete "Self" (tcTypes s'), tcTraits = Map.insert name functions (tcTraits s'), tcTraitParams = Map.insert name params (tcTraitParams s'), tcTraitSelf = Nothing, tcRefResults = Map.union (Map.fromList refResults) (tcRefResults s')}

-- The types of a trait replaced by the types an impl gives it
substTraitArgs :: [Variable] -> [Arg] -> Type -> Type
substTraitArgs params args = substitute [] [(p, t) | (p, ArgType t) <- zip params args]

-- Self as a type: the type an impl is for, which is a list for an impl for one (`impl<T> Sequence<T> for List<T>`, lib/prelude.tersus)
substSelfAs :: Name -> Type -> Type -> Type
substSelfAs selfName selfType ty = case ty of
    TNamed "Self" _ -> selfType
    TNamed base args | instanceName base args == selfName -> selfType
    TList t -> TList (go t)
    TArrayOf t size -> TArrayOf (go t) size
    TBox t -> TBox (go t)
    TAddr t -> TAddr (go t)
    TUninit t -> TUninit (go t)
    TBlock t -> TBlock (go t)
    TRef t -> TRef (go t)
    TFn args ret -> TFn (map go args) (go ret)
    _ -> ty
  where
    go = substSelfAs selfName selfType

substSelf :: Name -> Type -> Type
substSelf owner (TNamed "Self" _) = TNamed owner []
substSelf owner (TList t) = TList (substSelf owner t)
substSelf owner (TArrayOf t size) = TArrayOf (substSelf owner t) size
substSelf owner (TBox t) = TBox (substSelf owner t)
substSelf owner (TAddr t) = TAddr (substSelf owner t)
substSelf owner (TUninit t) = TUninit (substSelf owner t)
substSelf owner (TBlock t) = TBlock (substSelf owner t)
substSelf owner (TRef t) = TRef (substSelf owner t)
substSelf owner (TMutRef t) = TMutRef (substSelf owner t)
substSelf owner (TFn args ret) = TFn (map (substSelf owner) args) (substSelf owner ret)
substSelf _ t = t

-- The functions of an impl are checked as definitions at the top of the program, in order. For a trait impl they are then
-- compared with the trait: the same functions, with the types the trait gives with Self replaced by the type. Each trait
-- function also gets a function of the program that has the trait's contracts and calls the impl's function:
--
--   fn "Area for Shape::area"(self: Shape) -> Int [{ the trait's input contract }] [{ the trait's output contract }] {
--       return Shape::area(self);
--   };
--
-- The validator checks it like any function, and what it proves is that the impl may be used wherever the trait is: the
-- trait's input contract must give the impl's (the call is checked against the impl's input contract), and the impl's
-- output contract must give the trait's (the return is checked against it).
checkImpl :: Ctx -> Env -> Maybe Name -> [Arg] -> Name -> Type -> [Bound] -> [Statement] -> TC (Ctx, Env, [Statement], [Type])
checkImpl ctx env trait traitArgs typeName selfTypeInput bounds functions
    | not (null bounds) = do
        let selfName = case selfTypeInput of TNamed b a -> instanceName b a; other -> renderType other
            selfType = case (typeName, selfTypeInput) of
                ("List", TNamed _ [ArgType t]) -> TList t
                ("Box", TNamed _ [ArgType t]) -> TBox t
                ("Array", TNamed _ [ArgType t, ArgSize s]) -> TArrayOf t s
                ("Int", _) -> TInt
                ("Byte", _) -> TByte
                ("Bool", _) -> TBool
                _ -> selfTypeInput
            asSelf = substSelfAs selfName selfType
            rewriteSig stmt = case stmt of
                Assign name (Val (VFunct params ins outs (NativeFunct (Signature ptys rty sizes types writes from) term body) proofs)) -> Assign name (Val (VFunct params ins outs (NativeFunct (Signature (map asSelf ptys) (asSelf rty) sizes types writes from) term body) proofs))
                _ -> stmt
            functions' = map rewriteSig functions
        forM_ bounds $ \(param, traitName, args) -> do
            s <- getState
            case Map.lookup traitName (tcTraitParams s) of
                Nothing | Map.member traitName (tcTraits s) -> unless (null args) $ failTc ("Type error: trait " ++ traitName ++ " has no types, but the bound on " ++ param ++ " of the impl for " ++ typeName ++ " gives it some")
                Nothing -> failTc ("Type error: unknown trait " ++ traitName ++ " in the bound on " ++ param ++ " of the impl for " ++ typeName)
                Just params' -> when (length params' /= length args) $
                    failTc ("Type error: trait " ++ traitName ++ " has parameters <" ++ intercalate ", " params' ++ ">, which the bound on " ++ param ++ " of the impl for " ++ typeName ++ " gives " ++ show (length args))
        -- (an impl of a trait with bounds implements it for the types that meet them, and is checked against it for each, as its
        -- functions are: the check of each function is a template too, made with it)
        wrappers <- case trait of
            Nothing -> return []
            Just traitName -> do
                s <- getState
                required <- maybe (failTc ("Type error: unknown trait " ++ traitName)) return (Map.lookup traitName (tcTraits s))
                let traitParams = Map.findWithDefault [] traitName (tcTraitParams s)
                    here = "impl " ++ traitName ++ " for " ++ typeName
                when (length traitParams /= length traitArgs) $
                    failTc ("Type error: trait " ++ traitName ++ " has parameters <" ++ intercalate ", " traitParams ++ ">, which impl " ++ traitName ++ " for " ++ typeName ++ " gives " ++ show (length traitArgs))
                when (Set.member (traitName, typeName) (tcImpls s)) $ failTc ("Type error: " ++ typeName ++ " already implements " ++ traitName)
                when (null required) $ failTc ("Type error: " ++ here ++ " has bounds, and " ++ traitName ++ " has no functions: the bounds of a marker impl are not supported")
                putState s{tcImpls = Set.insert (traitName, typeName) (tcImpls s), tcImplArgs = Map.insert (traitName, typeName) (selfTypeInput, traitArgs) (tcImplArgs s), tcImplBounds = Map.insert (traitName, typeName) bounds (tcImplBounds s)}
                let defined = [(implFunctionPart name, (params, signature)) | Assign name (Val (VFunct params _ _ (NativeFunct signature _ _) _)) <- functions']
                    wanted = map traitFnName required
                    inImpl = substTraitArgs traitParams traitArgs . substSelfAs selfName selfType
                case map fst defined \\ wanted of
                    extra : _ -> failTc ("Type error: " ++ here ++ " has a function " ++ extra ++ ", which " ++ traitName ++ " does not declare")
                    [] -> return ()
                case wanted \\ map fst defined of
                    missing : _ -> failTc ("Type error: " ++ here ++ " lacks the function " ++ missing)
                    [] -> return ()
                forM required $ \f -> do
                    let Signature ptys rty _ _ _ _ = traitFnSignature f
                        expected = Signature (map inImpl ptys) (inImpl rty) [] [] [] []
                    case lookup (traitFnName f) defined of
                        Just (implParams, signature@(Signature aptys arty asizes _ _ _)) -> do
                            let actual = Signature (take (length aptys - length asizes) aptys) arty [] [] [] []
                            when (actual /= expected) $
                                failTc ("Type error: " ++ here ++ ": " ++ traitFnName f ++ " is " ++ renderType (TFn (take (length aptys - length asizes) aptys) arty) ++ ", but " ++ traitName ++ " declares " ++ renderType (TFn (map inImpl ptys) (inImpl rty)))
                            let term = head ([t | Assign name (Val (VFunct _ _ _ (NativeFunct _ t _) _)) <- functions', implFunctionPart name == traitFnName f] ++ [Nothing])
                            return (implFunctionName typeName (Just traitName) (traitFnName f), traitCheckWrapper traitName typeName f (traitFnParams f ++ drop (length implParams - length asizes) implParams) signature term)
                        Nothing -> failTc ("Type error: " ++ here ++ " lacks the function " ++ traitFnName f)
        forM_ functions' $ \stmt -> case stmt of
            Assign name (Val (VFunct params ins outs (NativeFunct signature@(Signature _ _ _ sigTypes _ _) term body) _)) -> do
                forM_ bounds $ \(param, traitName, _) -> unless (param `elem` sigTypes) $ failTc ("Type error: " ++ param ++ " is bounded by " ++ traitName ++ " in the impl for " ++ typeName ++ " but is not a type of " ++ name)
                s <- getState
                when (Map.member name (tcTemplates s) || Map.member name (ctxFns ctx)) $ failTc ("Type error: " ++ name ++ " is already defined")
                putState s{tcTemplates = Map.insert name (Template bounds ctx params signature ins outs term body) (tcTemplates s), tcAssoc = Map.insertWith (\new old -> old ++ new) (typeName, implFunctionPart name) [trait] (tcAssoc s)}
            _ -> failTc "Type error: an impl with bounds can only hold functions"
        forM_ wrappers $ \(function, stmt) -> case stmt of
            Assign name (Val (VFunct params ins outs (NativeFunct signature term body) _)) -> do
                s <- getState
                putState s{tcTemplates = Map.insert name (Template bounds ctx params signature ins outs term body) (tcTemplates s), tcCompanions = Map.insertWith (++) function [name] (tcCompanions s)}
            _ -> return ()
        return (ctx, env, [], [])
checkImpl ctx env trait traitArgs typeName selfTypeInput _bounds functions = do
    let selfName = case selfTypeInput of TNamed b a -> instanceName b a; other -> renderType other
    declared <- getState
    -- (a struct with parameters has them in the impl, `impl<T> Vec<T>`, and its type is a different one for each; a list is the one
    -- type with an impl that is not declared as a struct, and Self for it is a List of the type the impl names)
    let selfType = case (typeName, selfTypeInput) of
            ("List", TNamed _ [ArgType t]) -> TList t
            ("Box", TNamed _ [ArgType t]) -> TBox t
            ("Array", TNamed _ [ArgType t, ArgSize s]) -> TArrayOf t s
            ("Int", _) -> TInt
            ("Byte", _) -> TByte
            ("Bool", _) -> TBool
            _ -> selfTypeInput
        asSelf = substSelfAs selfName selfType
        functions' = map (rewriteSignature asSelf) functions
    unless (typeName `elem` ["List", "Box", "Array", "Int", "Byte", "Bool"] || Map.member typeName (tcGenerics declared)) $ void (typeCtors typeName)
    -- (the type implements the trait from the first function on, so a function can call an earlier one through the trait; if the
    -- impl is not accepted the program is refused, so this is never seen)
    (required, traitParams) <- case trait of
        Nothing -> return ([], [])
        Just traitName -> do
            s <- getState
            found <- maybe (failTc ("Type error: unknown trait " ++ traitName)) return (Map.lookup traitName (tcTraits s))
            let params = Map.findWithDefault [] traitName (tcTraitParams s)
            when (length params /= length traitArgs) $
                failTc ("Type error: trait " ++ traitName ++ " has parameters <" ++ intercalate ", " params ++ ">, which impl " ++ traitName ++ " for " ++ typeName ++ " gives " ++ show (length traitArgs))
            when (Set.member (traitName, typeName) (tcImpls s)) $ failTc ("Type error: " ++ typeName ++ " already implements " ++ traitName)
            when (traitName == "Eq" && typeName `elem` ["Int", "Byte", "Bool"]) $ failTc ("Type error: " ++ typeName ++ " implements Eq by the language: its values are compared as words")
            putState s{tcImpls = Set.insert (traitName, typeName) (tcImpls s), tcImplArgs = Map.insert (traitName, typeName) (selfTypeInput, traitArgs) (tcImplArgs s)}
            when (traitName `elem` ["Clone", "Copy"] && null found && null params) $ checkMarkerImpl traitName typeName
            -- (a type with a drop is freed by it: it is not linear, and not copied, since each copy would be freed)
            when (traitName == "Drop") $ do
                s' <- getState
                when (Set.member typeName (tcLinear s')) $ failTc ("Type error: impl Drop for " ++ typeName ++ ": " ++ typeName ++ " is linear, so it is used by the program and not dropped")
                when (Set.member ("Clone", typeName) (tcImpls s') || Set.member ("Copy", typeName) (tcImpls s')) $
                    failTc ("Type error: impl Drop for " ++ typeName ++ ": " ++ typeName ++ " is Clone, and a copy of a value with a drop would be dropped twice")
                -- (a drop frees the memory a value holds: native code tells a value that was moved out by its bytes being 0, which a value
                -- that holds memory never is, since the address of an allocation is not 0, so a type with a drop holds a permission)
                holding <- case Map.lookup typeName (tcGenerics s') of
                    Just (_, fields) -> or <$> mapM (holdsGhost . snd) fields
                    Nothing -> holdsGhost (TNamed typeName [])
                unless holding $ failTc ("Type error: impl Drop for " ++ typeName ++ ": " ++ typeName ++ " holds no permission (Block<T>), and a drop is how a value frees the memory it holds; a value that has to be closed is a linear type, closed by a call")
                putState s'{tcDrops = Set.insert typeName (tcDrops s')}
            return (found, params)
    (ctx', env', checked, checkedTypes) <- definitions True (ctx, env, [], []) functions'
    case trait of
        Nothing -> return (ctx', env', checked, checkedTypes)
        Just traitName -> do
            let here = "impl " ++ traitName ++ " for " ++ typeName
                defined = [(implFunctionPart name, (params, Signature ptys rty sizes types _writes _from, term)) | Assign name (Val (VFunct params _ _ (NativeFunct (Signature ptys rty sizes types _writes _from) term _) _)) <- checked]
                wanted = map traitFnName required
                -- (what the trait asks for, with Self the type and the types of the trait the ones this impl gives)
                inImpl = substTraitArgs traitParams traitArgs . substSelfAs selfName selfType
            case map fst defined \\ wanted of
                extra : _ -> failTc ("Type error: " ++ here ++ " has a function " ++ extra ++ ", which " ++ traitName ++ " does not declare")
                [] -> return ()
            case wanted \\ map fst defined of
                missing : _ -> failTc ("Type error: " ++ here ++ " lacks the function " ++ missing)
                [] -> return ()
            wrappers <- forM required $ \f -> do
                let Signature ptys rty _ _ _writes _from = traitFnSignature f
                    expected = Signature (map inImpl ptys) (inImpl rty) [] [] [] []
                case lookup (traitFnName f) defined of
                    Just (implParams, Signature aptys arty asizes atypes _writes _from, term) -> do
                        -- (the sizes of the type, and any of the function, are given to it as its last parameters, which the
                        -- trait does not declare, so they are not part of the type the trait asks for)
                        let actual = Signature (take (length aptys - length asizes) aptys) arty [] [] [] []
                        when (actual /= expected) $
                            failTc ("Type error: " ++ here ++ ": " ++ traitFnName f ++ " is " ++ renderSignature actual ++ ", but " ++ traitName ++ " declares " ++ renderSignature expected)
                        -- (an impl of a struct with types is for any of them, and the check of it is too)
                        return (traitCheckWrapper traitName typeName f (traitFnParams f ++ drop (length implParams - length asizes) implParams) (Signature aptys arty asizes atypes _writes _from) term)
                    Nothing -> failTc ("Type error: " ++ here ++ " lacks the function " ++ traitFnName f)
            (ctx'', env'', wrapped, wrappedTypes) <- definitions False (ctx', env', [], []) wrappers
            return (ctx'', env'', [CopyDef typeName | traitName == "Copy", null required] ++ [DropDef typeName | traitName == "Drop"] ++ checked ++ wrapped, checkedTypes ++ wrappedTypes)
  where
    -- The functions of the impl can be called as Type::f from the next one on, itself included; the functions that check
    -- the impl against its trait cannot
    definitions _ state [] = return state
    definitions own (c, e, done, doneTypes) (stmt : rest) = do
        case stmt of
            Assign name _ | own -> do
                s <- getState
                putState s{tcAssoc = Map.insertWith (\new old -> old ++ new) (typeName, implFunctionPart name) [trait] (tcAssoc s)}
            _ -> return ()
        (c', e', stmt', types) <- checkStatement True c e stmt
        definitions own (c', e', done ++ [stmt'], doneTypes ++ types) rest
    renderSignature (Signature ptys rty _ _ _writes _from) = renderType (TFn ptys rty)
    -- (Self in the signature of a function of the impl is the type the impl is for, as the parser wrote it and as it is)
    rewriteSignature asSelf stmt = case stmt of
        Assign name (Val (VFunct params ins outs (NativeFunct (Signature ptys rty sizes types _writes _from) term body) proofs)) ->
            Assign name (Val (VFunct params ins outs (NativeFunct (Signature (map asSelf ptys) (asSelf rty) sizes types _writes _from) term body) proofs))
        _ -> stmt

-- The function that checks a function of an impl against its trait: the trait's contracts, and a call of the impl's function
traitCheckWrapper :: Name -> Name -> TraitFn -> [Variable] -> Signature -> Maybe Termination -> Statement
traitCheckWrapper traitName owner f params signature term =
    Assign
        (implCheckName traitName owner (traitFnName f))
        ( Val
            ( VFunct
                params
                (traitFnRequires f)
                (traitFnEnsures f)
                (NativeFunct signature (if term == Just MayDiverge then Just MayDiverge else Nothing) [Return (F (Var (implFunctionName owner (Just traitName) (traitFnName f))) (map Var (traitFnParams f)))])
                []
            )
        )

inferProof :: Ctx -> Env -> VariableProof -> TC Type
inferProof ctx env proof = fst <$> inferProofR ctx env proof

-- The type of a proof, and the proof with each call of a function of the program resolved: `Type::f(x)` and `Trait::f(x)` are calls of
-- the impl's function for the type, and a function with sizes is given them as its last arguments, as a call is.
inferProofR :: Ctx -> Env -> VariableProof -> TC (Type, VariableProof)
inferProofR ctx env proof =
    case proof of
        ATerm var -> (\t -> (t, proof)) <$> lookupProofVar ctx env var
        BVar var -> (\t -> (t, proof)) <$> lookupVar ctx env var
        CTerm value -> (\t -> (t, proof)) <$> valueType value
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct OldOf) _)) _ -> failTc "Type error: old(...) is only written in a postcondition, of the place an update parameter is to"
        FApp funct@(CTerm (VFunct _ _ _ (BuiltinFunct DerefOf) _)) [inner] -> do
            (t, inner') <- inferProofR ctx env inner
            tz <- zonk t
            referent <- case tz of
                TRef u -> return u
                TMutRef u -> return u
                -- (a borrowed parameter is its referent in the body, so *p is p)
                _ -> return tz
            return (referent, FApp funct [inner'])
        FApp funct@(CTerm (VFunct _ _ _ (BuiltinFunct (Field owner field)) _)) [struct] -> do
            (structTy, struct') <- inferProofR ctx env struct
            let go (ty, proof) = do
                    direct <- tryTc (readField owner field ty)
                    case direct of
                        Just t -> return (t, proof)
                        Nothing -> do
                            next <- derefStepProof (ty, proof)
                            case next of
                                Just stepped -> go stepped
                                Nothing -> do
                                    t <- readField owner field ty
                                    return (t, proof)
            (t, struct'') <- go (structTy, struct')
            return (t, FApp funct [struct''])
        FApp funct@(CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name ctorArgs fields)) _)) args -> do
            inferred <- mapM (inferProofR ctx env) args
            t <- checkConstruct (TNamed (baseNameOf name) ctorArgs) fields (map fst inferred)
            return (t, FApp funct (map snd inferred))
        FApp funct@(CTerm (VFunct _ _ _ (BuiltinFunct NewArray) _)) [n, x] -> do
            (nt, n') <- inferProofR ctx env n
            expect "argument 1 of array" TInt nt
            (xt, x') <- inferProofR ctx env x
            size <- proofSize (constantProofInt n) n
            let ty = TArrayOf xt size
            arrayOk ty
            return (ty, FApp funct [n', x'])
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct NewArray) _)) args -> failTc ("Type error: array takes 2 arguments, got " ++ show (length args))
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct ArrayFrom) _)) [CTerm literal@(VList items)] -> do
            listTy <- valueType literal
            case listTy of
                TList e -> do
                    let ty = TArray e (fromIntegral (length items))
                    arrayOk ty
                    literalOk e
                    return (ty, proof)
                _ -> failTc "Type error: an array literal is made from a list"
        -- what is known of a permission (base(b), cap(b), filled(b, i), at(b, i), ...) and the operations on addresses that need none
        FApp (ATerm name) args
            | not (shadowedByFunction name), not (Map.member name (ctxFns ctx)), Just b <- ghostFunction name -> do
              ofPermission <- permissionArgument b args (inferProofR ctx env)
              if not ofPermission then ordinaryCall name args else do
                inferred <- mapM (inferProofR ctx env) args
                ft <- builtinType b
                case b of
                    -- (filled(u) and at(u) of an Uninit)
                    _ | b `elem` [BlockFilled, BlockContents], [(ut, u')] <- inferred -> do
                        let b' = if b == BlockFilled then UninitFilled else UninitAt
                        ft' <- builtinType b'
                        result <- checkCall name ft' [ut]
                        return (result, FApp (CTerm (builtinFunct b')) [u'])
                    -- (filled(b, i) and at(b, i) are elements of the two arrays of the block)
                    _ | b `elem` [BlockFilled, BlockContents] -> case inferred of
                        [(bt, b'), (it, i')] -> do
                            listTy <- checkCall name ft [bt]
                            expect ("argument 2 of " ++ name) TInt it
                            elementTy <- freshVar
                            expect name (TList elementTy) listTy
                            return (elementTy, FApp (CTerm (builtinFunct Get)) [FApp (CTerm (builtinFunct b)) [b'], i'])
                        _ -> failTc ("Type error: " ++ name ++ " takes a permission and a slot, as in " ++ name ++ "(b, i)")
                    _ -> do
                        result <- checkCall name ft (map fst inferred)
                        return (result, FApp (CTerm (builtinFunct b)) (map snd inferred))
            | not (shadowed name), not (Map.member name (ctxFns ctx)), name == "whole" ->
                failTc "Type error: whole(b) is a statement of its own, affirm whole(b); (it is two facts: start(b) = 0 and cap(b) = extent(origin(b)))"
        -- a function with bounds is the function made for the types of the arguments; any other function of the program is itself
        FApp (ATerm name) args | not (shadowed name) -> ordinaryCall name args
        FApp funct args -> do
            (_, funct') <- inferProofR ctx env funct
            inferred0 <- mapM (inferProofR ctx env) args
            inferred <- case (proofBuiltin funct', inferred0) of
                (Just b, first : rest) | isLookThrough b -> do
                    first' <- derefProof first
                    return (first' : rest)
                _ -> return inferred0
            owner <- case (proofBuiltin funct', inferred) of
                (Just b, (xt, _) : _) | Just fname <- sequenceFunction b -> (,) fname <$> structOwner xt
                _ -> return ("", Nothing)
            case owner of
                -- size(v), get(v, i), ...: on a value of a struct they are the functions of its impl, and in a trait on a Self
                (fname, Just "Self") -> do
                    traitFns <- tcTraitSelf <$> getState
                    case [f | Just fs <- [traitFns], f <- fs, traitFnName f == fname] of
                        f : _ | length (fst (signatureTypes f)) == length inferred -> return (snd (signatureTypes f), FApp funct' (map snd inferred))
                        _ -> failTc ("Type error: " ++ fname ++ " is called on a Self, which the trait has no function " ++ fname ++ " for")
                (fname, Just struct) -> do
                    full <- resolveAssociated struct fname
                    ghostCall full inferred
                _ -> general funct' inferred
        Forall index guards body -> do
            let env' = Map.singleton index TInt : env
            guards' <- mapM (\g -> inferProofR ctx env' g >>= \(t, g') -> expect "guard of forall" TBool t >> return g') guards
            (bt, body') <- inferProofR ctx env' body
            expect "body of forall" TBool bt
            return (TBool, Forall index guards' body')
  where
    -- A proof looked through one step, by a call of its type's `deref`, as an expression is (see derefStepExpr)
    derefStepProof (ty, proof) = do
        t <- zonk ty
        case t of
            TBox _ -> return Nothing
            _ -> do
                target <- derefTarget t
                case target of
                    Just _ -> do
                        owner <- derefOwner t
                        Just <$> ghostCall (implFunctionName owner (Just "Deref") "deref") [(t, proof)]
                    Nothing -> return Nothing
    -- A proof looked through to the value it holds, a step at a time
    derefProof (ty, proof) = do
        next <- derefStepProof (ty, proof)
        case next of
            Just stepped -> derefProof stepped
            Nothing -> return (ty, proof)
    ordinaryCall name args = do
        inferred <- mapM (inferProofR ctx env) args
        s <- getState
        case Map.lookup name (tcTemplates s) of
            Just template -> do
                (result, instance', _, sizes) <- templateCall ctx name template [tLeaf t (Val (VInt 0)) | (t, _) <- inferred]
                return (result, FApp (ATerm instance') (map snd inferred ++ map (exprToProof . tExpr) sizes))
            Nothing -> do
                target <- ghostTarget name (map fst inferred)
                case target of
                    Just full -> ghostCall full inferred
                    Nothing -> general (ATerm name) inferred
    shadowed name = any (Map.member name) env
    -- (a field or a variable named like a ghost function, `cap`, does not hide it: it is not called)
    shadowedByFunction name = or [isFunction t | scope <- env, Just t <- [Map.lookup name scope]]
    isFunction t = case t of
        TFn{} -> True
        TForall{} -> True
        _ -> False
    signatureTypes f = let Signature ptys rty _ _ _writes _from = traitFnSignature f in (ptys, rty)
    ghostCall full inferred = do
        ft <- lookupVar ctx env full
        ftz <- zonk ft
        case ftz of
            TForall sizes types inner -> do
                (result, args') <- genericCall full sizes types inner [tLeaf t (Val (VInt 0)) | (t, _) <- inferred]
                return (result, FApp (ATerm full) (map snd inferred ++ map (exprToProof . tExpr) (drop (length inferred) args')))
            _ -> do
                result <- checkCall full ft (map fst inferred)
                return (result, FApp (ATerm full) (map snd inferred))
    general funct inferred = do
        ft <- inferProof ctx env funct
        result <- checkBuiltinCall (proofBuiltin funct) "call" ft (map fst inferred)
        comparing (proofHead funct) (map fst inferred)
        return (result, FApp funct (map snd inferred))
    -- the function of the program that a name in a call stands for, if it stands for one
    ghostTarget name argTypes
        | take 1 name == "<" = return (Just name)
        | Just (path, function) <- traitPath name = do
            s <- getState
            case (Map.lookup path (tcTraits s), Map.member path (tcTypes s) || Map.member path (tcGenerics s)) of
                (Just functions, _) -> do
                    owner <- ownerThroughTrait path functions function argTypes
                    return (Just (implFunctionName owner (Just path) function))
                (Nothing, True) -> Just <$> resolveAssociated path function
                _ -> return Nothing
        | Map.member name (ctxFns ctx) = return (Just name)
        | otherwise = return Nothing

-- Whether a ghost function is applied to a permission, which is what makes it one: `count(v)` of a value that is not a permission is a call of
-- a function of the program named count (the operations on addresses and `extent`, of an origin, are taken as they are)
permissionArgument :: BuiltinFunct -> [a] -> (a -> TC (Type, a)) -> TC Bool
permissionArgument b args infer
    | b `elem` [AddrNull, AddrOffset, AddrCast, AddrToInt, AddrFromInt, BlockExtent] = return True
    | otherwise = case args of
        first : _ -> do
            (t, _) <- infer first
            t' <- zonk t
            return $ case t' of
                TBlock _ -> True
                TRef (TBlock _) -> True
                TMutRef (TBlock _) -> True
                TUninit _ -> b `elem` [BlockFilled, BlockContents]
                TRef (TUninit _) -> b `elem` [BlockFilled, BlockContents]
                TMutRef (TUninit _) -> b `elem` [BlockFilled, BlockContents]
                _ -> False
        [] -> return False

-- The operations on addresses and permissions, by the names a program calls them by (BuiltinRegistry)
pointerBuiltin :: Name -> Maybe BuiltinFunct
pointerBuiltin = pointerBuiltinByName

-- What a proof can say of a permission, and the operations on addresses a proof can use (BuiltinRegistry)
ghostFunction :: Name -> Maybe BuiltinFunct
ghostFunction = ghostBuiltinByName

-- The builtin that a method of a list or an array is (BuiltinRegistry)
listMethod :: Name -> Maybe BuiltinFunct
listMethod = methodBuiltinByName

-- Whether a type is a list or an array, which have the functions of the builtins as methods
sequenceType :: Type -> Bool
sequenceType ty = case ty of
    TList _ -> True
    TArrayOf{} -> True
    TBox TArrayOf{} -> True
    _ -> False

-- The functions of a list that a struct can have of its own: `size(v)` is the function `size` of the impl of the type of `v` (BuiltinRegistry)
sequenceFunction :: BuiltinFunct -> Maybe Name
sequenceFunction = methodNameFor

-- The struct (without the types it is given) that a type is, or Self in a trait
structOwner :: Type -> TC (Maybe Name)
structOwner ty = do
    t <- zonk ty
    return $ case t of
        TNamed base _ -> Just base
        _ -> Nothing

-- (a name in a proof is a variable of the program or the builtin of that name, as for an expression)
proofBuiltin :: VariableProof -> Maybe BuiltinFunct
proofBuiltin (CTerm (VFunct _ _ _ (BuiltinFunct b) _)) = Just b
proofBuiltin _ = Nothing

-- Equality is structural, which functions do not have
comparing :: Expression -> [Type] -> TC ()
comparing (Val (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) (t : _)
    | rel `elem` [Eq, NotEq] = do
        t' <- zonk t
        case t' of
            TFn{} -> failTc "Type error: functions cannot be compared"
            TUninit _ -> failTc "Type error: an Uninit cannot be compared, since it may hold nothing: what it holds is compared, as in Uninit::get(a) = Uninit::get(b)"
            _ -> do
                ghostly <- holdsGhost t'
                when ghostly $ failTc ("Type error: " ++ renderType t' ++ " holds a permission, which cannot be compared: what a permission says is compared, as in at(a, 0) = at(b, 0)")
comparing _ _ = return ()

proofHead :: VariableProof -> Expression
proofHead (CTerm value) = Val value
proofHead _ = Var ""

declareTemplate :: Ctx -> Name -> [Bound] -> [Variable] -> Signature -> [ValidationStatement] -> [ValidationStatement] -> Maybe Termination -> [Statement] -> TC ()
declareTemplate ctx name bounds params signature@(Signature _ _ _ types _writes _from) ins outs term body = do
    s <- getState
    when (Map.member name (ctxFns ctx) || Map.member name (tcTemplates s) || Map.member name stdLibCtx) $ failTc ("Type error: " ++ name ++ " is already defined")
    forM_ bounds $ \(param, trait, args) -> do
        unless (param `elem` types) $ failTc ("Type error: " ++ param ++ " is bounded by " ++ trait ++ " but is not a type of " ++ name)
        case Map.lookup trait (tcTraitParams s) of
            Nothing | Map.member trait (tcTraits s) -> unless (null args) $ failTc ("Type error: trait " ++ trait ++ " has no types, but the bound on " ++ param ++ " gives it some")
            Nothing -> failTc ("Type error: unknown trait " ++ trait ++ " in the bound on " ++ param ++ " of " ++ name)
            Just params' -> when (length params' /= length args) $
                failTc ("Type error: trait " ++ trait ++ " has parameters <" ++ intercalate ", " params' ++ ">, which the bound on " ++ param ++ " of " ++ name ++ " gives " ++ show (length args))
    putState s{tcTemplates = Map.insert name (Template bounds ctx params signature ins outs term body) (tcTemplates s)}

-- A call of a function with bounds: the types of the arguments give the types of the function, each of which has to implement what its bounds say,
-- and the function is checked for those types, once (it is a function of the program named after them: total[Vec<Int>]). The call is a call of that.
templateCall :: Ctx -> Name -> Template -> [TExpr] -> TC (Type, Name, [TExpr], [TExpr])
templateCall ctx name template inferred = do
    let Signature ptys rty sizes types _writes _from = tmplSignature template
    (instantiated, sizeVars, typeVars) <- instantiateGenerics sizes types (TFn ptys rty)
    case instantiated of
        TFn pts result
            | length pts - length sizes /= length inferred ->
                failTc ("Type error: " ++ name ++ " takes " ++ show (length pts - length sizes) ++ " arguments, got " ++ show (length inferred))
            | otherwise -> do
                args <- mapM (\(i, pt, arg) -> do
                    ptz <- zonk pt
                    arg' <- coerce (unref ptz) arg
                    atz <- zonk (tType arg')
                    case (ptz, atz) of
                        (TRef a, TRef b) -> expect ("argument " ++ show (i :: Int) ++ " of " ++ name) a b
                        (TRef a, TMutRef b) -> expect ("argument " ++ show (i :: Int) ++ " of " ++ name) a b
                        (TMutRef a, TMutRef b) -> expect ("argument " ++ show (i :: Int) ++ " of " ++ name) a b
                        _ -> expect ("argument " ++ show (i :: Int) ++ " of " ++ name) (unref ptz) atz
                    return arg') (zip3 [1 ..] pts inferred)
                let given = zip types typeVars
                -- (a bound on a type that another bound decides waits until that one has: the passes end when all are met, or none can be)
                let attempt pending = do
                        results <- forM pending $ \bound@(param, _, _) -> do
                            t <- maybe (return TInt) zonk (lookup param given)
                            case t of
                                TVar _ -> return (Just bound)
                                _ -> checkBound given bound t >> return Nothing
                        let left = [bound | Just bound <- results]
                        if null left
                            then return ()
                            else
                                if length left == length pending
                                    then failTc ("Type error: the type " ++ (\(param, _, _) -> param) (head left) ++ " of " ++ name ++ " cannot be worked out from its arguments")
                                    else attempt left
                attempt (tmplBounds template)
                concrete <- mapM zonk typeVars
                forM_ (zip types concrete) $ \(n, t) -> do
                    when (unknown t) $ failTc ("Type error: the type " ++ n ++ " of " ++ name ++ " cannot be worked out from its arguments")
                    when (mentionsParameter t) $
                        failTc ("Type error: the type " ++ n ++ " of " ++ name ++ " would be " ++ renderType t ++ ", which is made of a type parameter of the function that calls: a function with bounds is made for types a call writes")
                let suffix = "[" ++ intercalate ", " (map renderTypeForName concrete) ++ "]"
                    instanceName' = name ++ suffix
                    bigness = sum (map typeBigness concrete)
                instances <- tcInstances <$> getState
                active <- tcActive <$> getState
                unless (Map.member instanceName' instances) $ do
                    -- (a function that calls itself with a type that is not its own would be made for a new one at each depth, unless the
                    -- types get smaller, as the impl for a list of lists compares lists of the elements)
                    when (any (\(n, b) -> n == name && bigness >= b) active) $
                        failTc ("Type error: " ++ name ++ " calls itself with the types " ++ intercalate ", " (map renderType concrete) ++ ", which are not those it is made for: a function with bounds is made for each type, and one that is made for a bigger type at each call would never end")
                    makeTemplateInstance ctx name template instanceName' bigness (zip types concrete)
                    companions <- Map.findWithDefault [] name . tcCompanions <$> getState
                    forM_ companions $ \companion -> do
                        s <- getState
                        case Map.lookup companion (tcTemplates s) of
                            Just companionTemplate | not (Map.member (companion ++ suffix) (tcInstances s)) ->
                                makeTemplateInstance ctx companion companionTemplate (companion ++ suffix) bigness (zip types concrete)
                            _ -> return ()
                sizeGiven <- mapM (\(n, size) -> zonkSize size >>= sizeArgument name n) (zip sizes sizeVars)
                resultTy <- zonk result
                return (resultTy, instanceName', args, map (tLeaf TInt) sizeGiven)
        _ -> failTc ("Type error: " ++ name ++ " is not a function")
  where
    -- the type meets the bound: it implements the trait, with the types that the bound writes
    checkBound given (param, trait, wanted) t = do
        gives <- traitArguments trait t
        case gives of
            Nothing -> failTc ("Type error: " ++ name ++ " needs " ++ param ++ " to implement " ++ trait ++ ", and " ++ renderType t ++ " does not")
            Just actual -> do
                when (length actual /= length wanted) $
                    failTc ("Type error: " ++ renderType t ++ " gives " ++ trait ++ " " ++ show (length actual) ++ " types, but the bound on " ++ param ++ " of " ++ name ++ " has " ++ show (length wanted))
                forM_ (zip actual wanted) $ \(have, want) -> do
                    have' <- zonk have
                    want' <- zonk (substitute [] given want)
                    ok <- unify have' want'
                    unless ok $ do
                        h <- zonk have'
                        w <- zonk want'
                        failTc ("Type error: " ++ name ++ " needs " ++ param ++ " to implement " ++ trait ++ "<" ++ renderType w ++ ">, and " ++ renderType t ++ " implements " ++ trait ++ "<" ++ renderType h ++ ">")
    unknown t = case t of
        TVar _ -> True
        TList u -> unknown u
        TBox u -> unknown u
        TAddr u -> unknown u
        TUninit u -> unknown u
        TBlock u -> unknown u
        TNamed _ args -> or [unknown u | ArgType u <- args]
        TRef u -> unknown u
        TMutRef u -> unknown u
        TArrayOf u _ -> unknown u
        TFn args r -> any unknown (r : args)
        _ -> False

-- How big a type is, so that a function with bounds can call itself for a part of the type it is made for
typeBigness :: Type -> Int
typeBigness t = case t of
    TList u -> 1 + typeBigness u
    TBox u -> 1 + typeBigness u
    TArrayOf u _ -> 1 + typeBigness u
    TAddr u -> 1 + typeBigness u
    TUninit u -> 1 + typeBigness u
    TBlock u -> 1 + typeBigness u
    TRef u -> 1 + typeBigness u
    TMutRef u -> 1 + typeBigness u
    TNamed _ args -> 1 + sum [typeBigness u | ArgType u <- args]
    TFn args r -> 1 + sum (map typeBigness (r : args))
    _ -> 1

-- A template with the types it was called with in place of its own, which is checked like any function
makeTemplateInstance :: Ctx -> Name -> Template -> Name -> Int -> [(Variable, Type)] -> TC ()
makeTemplateInstance ctx name template instanceName' bigness bindings = do
    let Signature ptys rty sizes _ _writes _from = tmplSignature template
        ptys' = map (substitute [] bindings) ptys
        rty' = substitute [] bindings rty
        fnTy = functionType sizes [] ptys' rty'
        instanceCtx = (tmplCtx template){ctxFns = Map.insert instanceName' fnTy (Map.union (ctxFns ctx) (ctxFns (tmplCtx template)))}
    s <- getState
    putState s{tcInstances = Map.insert instanceName' fnTy (tcInstances s), tcActive = (name, bigness) : tcActive s}
    (term', ins', outs', body', bodyTypes, from) <- checkFunction instanceCtx instanceName' (tmplParams template) ptys' rty' sizes [] (tmplRequires template) (tmplEnsures template) [] _from (tmplTermination template) (tmplBody template)
    let function = Assign instanceName' (Val (VFunct (tmplParams template) ins' outs' (NativeFunct (Signature ptys' rty' sizes [] [] from) term' body') []))
    s' <- getState
    putState s'{tcEmitted = tcEmitted s' ++ [(function, bodyTypes)], tcActive = tcActive s, tcRefResults = if null from then tcRefResults s' else Map.insert instanceName' (tmplParams template, from) (tcRefResults s')}

