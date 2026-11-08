module TypeCheckScope (localScopes) where

import qualified Data.Map as Map
import Data.Map (Map)

import Syntax
import TypeCheckCore
import Types (Variable)

localScopes :: [Statement] -> TC [Statement]
localScopes stmts = fst <$> statements Map.empty stmts

statements :: Map Variable Variable -> [Statement] -> TC ([Statement], Map Variable Variable)
statements names [] = return ([], names)
statements names (stmt : rest) = do
    (stmt', names') <- statement names stmt
    (rest', final) <- statements names' rest
    return (stmt' : rest', final)

statement :: Map Variable Variable -> Statement -> TC (Statement, Map Variable Variable)
statement names stmt = case stmt of
    Let name expr -> do
        expr' <- expression names expr
        st <- getState
        let fresh = "$local " ++ show (tcNext st) ++ " " ++ name
        putState st{tcNext = tcNext st + 1}
        return (Let fresh expr', Map.insert name fresh names)
    Assign name expr -> do
        expr' <- expression names expr
        return (Assign (variable names name) expr', names)
    AssignDeref lhs rhs -> do
        lhs' <- expression names lhs
        rhs' <- expression names rhs
        return (AssignDeref lhs' rhs', names)
    Return expr -> same . Return <$> expression names expr
    ValidationStatement v -> same . ValidationStatement <$> validation names v
    Block body -> same . Block . fst <$> statements names body
    If cond yes no -> do
        cond' <- expression names cond
        yes' <- fst <$> statements names yes
        no' <- fst <$> statements names no
        return (If cond' yes' no', names)
    While cond invariant term body -> do
        cond' <- expression names cond
        invariant' <- mapM (validation names) invariant
        term' <- mapM (termination names) term
        body' <- fst <$> statements names body
        return (While cond' invariant' term' body', names)
    ImplDef trait args name ty bounds body -> do
        body' <- localScopes body
        return (ImplDef trait args name ty bounds body', names)
    BoundedDef bounds inner -> do
        (inner', _) <- statement names inner
        return (BoundedDef bounds inner', names)
    Dissolve name -> return (Dissolve (variable names name), names)
    _ -> return (stmt, names)
  where
    same s = (s, names)

expression :: Map Variable Variable -> Expression -> TC Expression
expression names expr = case expr of
    Var name -> return (Var (variable names name))
    F f args -> F <$> expression names f <*> mapM (expression names) args
    IfExpr cond yes no -> IfExpr <$> expression names cond <*> expression names yes <*> expression names no
    BlockExpr body result -> do
        (body', inner) <- statements names body
        BlockExpr body' <$> expression inner result
    Ascribed inner ty -> (`Ascribed` ty) <$> expression names inner
    Val (VFunct params ins outs (NativeFunct sig term body) exports) -> do
        body' <- localScopes body
        return (Val (VFunct params ins outs (NativeFunct sig term body') exports))
    _ -> return expr

validation :: Map Variable Variable -> ValidationStatement -> TC ValidationStatement
validation names v = case v of
    ProofAssert p -> return (ProofAssert (proof names p))
    Assume p -> return (Assume (proof names p))
    AssignProofVar name expr -> AssignProofVar (variable names name) <$> expression names expr
    Rewrite rule -> return (Rewrite (case rule of
        Refl p -> Refl (proof names p)
        Eval name -> Eval (variable names name)
        CheckGtZero p -> CheckGtZero (proof names p)
        CheckRel p -> CheckRel (proof names p)
        UserRewrite name args -> UserRewrite name (map (proof names) args)
        EvalAll -> EvalAll))

proof :: Map Variable Variable -> VariableProof -> VariableProof
proof names p = case p of
    ATerm name -> ATerm (variable names name)
    FApp f args -> FApp (proof names f) (map (proof names) args)
    Forall name guards body -> Forall name (map (proof inner) guards) (proof inner body)
      where inner = Map.delete name names
    _ -> p

termination :: Map Variable Variable -> Termination -> TC Termination
termination names term = case term of
    Shrinks e -> Shrinks <$> expression names e
    Counting e -> Counting <$> expression names e
    Parts e -> Parts <$> expression names e
    Recursing inner -> Recursing <$> mapM (termination names) inner
    MayDiverge -> return MayDiverge

variable :: Map Variable Variable -> Variable -> Variable
variable names name = Map.findWithDefault name name names
