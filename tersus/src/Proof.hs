module Proof where

import Data.Map (
    Map,
    empty,
    fromList,
    insert,
    toList,
  )

import Data.List (nub)
import Data.Maybe (mapMaybe)
import qualified Data.Map as Map

import qualified ProofEngine as Engine
import ProofHelpers
import StdLib
import TersusTypes
import Utils

-- Public fns
evaluate :: [Statement] -> Result State String
evaluate [] = Ok initState
evaluate l = evalBlock $ initStateWStatements l

validate :: [Statement] -> Result VState String
validate [] = Ok $ VState emptyVScopeState empty [] [] stdLibRuleCtx
validate l = case valBlock $ initVStateWStatements l of
    Ok (VState vScopeState iotaCtx proofCtx remainingIotas ruleCtx) ->
        case remainingIotas of
            nextIota : _ -> Ok $ VState vScopeState iotaCtx proofCtx [nextIota] ruleCtx
            [] -> Error "Validation exhausted the available iota sequence"
    Error e -> Error e

-- Private fns
evalBlock :: State -> Result State String
evalBlock state = case state of
    State (ScopeState _ (Continuations []) _) _ -> Ok state
    State (ScopeState _ (Continuations (_ : _)) _) _ ->
        case evalNextStatement state of
            Ok nState -> evalBlock nState
            Error e -> Error e

evalReturningBlock :: State -> Result (State, Maybe Value) String
evalReturningBlock state =
    case evalBlock state of
        Ok rState -> Ok (rState, getReturn rState)
        Error e -> Error e

valBlock :: VState -> Result VState String
valBlock state = case state of
    VState (VScopeState _ _ (Continuations []) _) _ _ _ _ -> Ok state
    VState (VScopeState _ _ (Continuations (_ : _)) _) _ _ _ _ ->
        case valNextStatement state of
            Ok state' -> valBlock state'
            e -> e

valReturningBlock :: VState -> Result (VState, Maybe Iota) String
valReturningBlock state =
    let result = valBlock state
     in case result of
            Ok rstate ->
                case vGetReturn rstate of
                    Ok ret -> Ok (rstate, Just ret)
                    Error e -> Error e
            Error e -> Error e

evalNextStatement :: State -> Result State String
evalNextStatement state = case nextStatement state of
    Ok (Assign var expr) -> evalAssignStatement state var expr
    Ok (Return expr) -> evalReturnStatement state expr
    Ok ValidationStatement{} -> advanceStatement state
    Ok AxiomDef{} -> advanceStatement state
    Ok ProofDef{} -> advanceStatement state
    Ok (Block statements) -> evalBlockStatement state statements
    Ok (If cond thenStmts elseStmts) -> evalIfStatement state cond thenStmts elseStmts
    Ok loop@(While cond _ body) -> evalWhileStatement state loop cond body
    Ok LoopEnd{} -> Error "LoopEnd is only used during validation"
    Ok EndBlock -> evalEndBlockStatement state
    Error e -> Error e

nextStatement :: State -> Result Statement String
nextStatement (State (ScopeState _ (Continuations (stmt : _)) _) _) = Ok stmt
nextStatement _ = Error "No next statement available"

evalAssignStatement :: State -> Variable -> Expression -> Result State String
evalAssignStatement state var expr =
    case advanceStatement state of
        Ok advancedState ->
            case evalExpression advancedState expr of
                Ok (val, rState) -> Ok $ insertVar rState var val
                Error e -> Error e
        Error e -> Error e

evalReturnStatement :: State -> Expression -> Result State String
evalReturnStatement state expr =
    case advanceStatement state of
        Ok advancedState ->
            case evalExpression advancedState expr of
                Ok (val, rState) -> Ok $ setReturn (topLevelScope rState) val
                Error e -> Error e
        Error e -> Error e

evalBlockStatement :: State -> [Statement] -> Result State String
evalBlockStatement (State scope ctxVals) statements =
    case scopeAdvanceStatement scope of
        Ok advancedScope ->
            Ok $
                State
                    (ScopeState empty (Continuations (statements ++ [EndBlock])) (Just advancedScope))
                    ctxVals
        Error e -> Error e

-- The chosen branch runs as an ordinary block: it gets a child scope, assignments to
-- existing outer variables update them, and new variables stay local to the branch.
evalIfStatement :: State -> Expression -> [Statement] -> [Statement] -> Result State String
evalIfStatement state cond thenStmts elseStmts =
    case advanceStatement state of
        Ok advancedState ->
            case evalExpression advancedState cond of
                Ok (VBool True, condState) -> evalBlockStatementInPlace condState thenStmts
                Ok (VBool False, condState) -> evalBlockStatementInPlace condState elseStmts
                Ok _ -> Error "Condition must be a boolean"
                Error e -> Error e
        Error e -> Error e

-- While the condition holds, run one iteration of the body as a block and then the loop
-- again, by putting both at the front of the statements that are still to run.
evalWhileStatement :: State -> Statement -> Expression -> [Statement] -> Result State String
evalWhileStatement state loop cond body =
    case advanceStatement state of
        Ok advancedState ->
            case evalExpression advancedState cond of
                Ok (VBool True, condState) ->
                    let Continuations rest = getContinuations condState
                     in Ok (setContinuations condState (Continuations (Block body : loop : rest)))
                Ok (VBool False, condState) -> Ok condState
                Ok _ -> Error "Condition must be a boolean"
                Error e -> Error e
        Error e -> Error e

-- Like evalBlockStatement, for a state whose current statement was already advanced past.
evalBlockStatementInPlace :: State -> [Statement] -> Result State String
evalBlockStatementInPlace (State scope ctxVals) statements =
    Ok $
        State
            (ScopeState empty (Continuations (statements ++ [EndBlock])) (Just scope))
            ctxVals

evalEndBlockStatement :: State -> Result State String
evalEndBlockStatement (State (ScopeState _ _ pScope) ctxVals) =
    case pScope of
        Just rpScope -> Ok $ State rpScope ctxVals
        _ -> Error "EndBlock must have a parent scope"

valNextStatement :: VState -> Result VState String
valNextStatement state =
    case vNextStatement state of
        Ok stmt ->
            let tracedStmt = doTraceStatements ("valNextStatement: " ++ show stmt) stmt
             in case tracedStmt of
                    Assign var expr -> valAssignStatement state var expr
                    Return expr -> valReturnStatement state expr
                    ValidationStatement valStmt -> valValidationStatement state valStmt
                    AxiomDef name args inputs outputs -> valAxiomDef state name args inputs outputs
                    ProofDef name args inputs outputs body -> valProofDef state name args inputs outputs body
                    Block bstmts -> valBlockStatement state bstmts
                    If cond thenStmts elseStmts -> valIfStatement state cond thenStmts elseStmts
                    While cond invariant body -> valWhileStatement state cond invariant body
                    LoopEnd invariant -> valLoopEnd state invariant
                    EndBlock -> valEndBlockStatement state
        Error e -> Error e

vNextStatement :: VState -> Result Statement String
vNextStatement (VState (VScopeState _ _ (Continuations (stmt : _)) _) _ _ _ _) = Ok stmt
vNextStatement _ = Error "No next validation statement available"

valAssignStatement :: VState -> Variable -> Expression -> Result VState String
valAssignStatement state var expr =
    case vAdvanceStatement state of
        Ok advancedState ->
            case popIotaFromSeq advancedState of
                Ok (niota, state') ->
                    case valExpression state' niota expr of
                        Ok (exprState, nproofs) -> doTrace3 (var ++ " = " ++ show nproofs) (Ok $ vInsertVar exprState var niota nproofs)
                        Error e -> Error e
                Error e -> Error e
        Error e -> Error e

-- Return proofs are trimmed to names visible at the call boundary so nested block-local
-- iotas do not leak out when a function or block returns a value.
valReturnStatement :: VState -> Expression -> Result VState String
valReturnStatement state expr =
    let VState scope _ _ _ _ = state
        proofs = vScopeGetProofs scope
     in case vAdvanceStatement state of
            Ok advancedState ->
                case popIotaFromSeq advancedState of
                    Ok (niota, state') ->
                        case valExpression state' niota expr of
                            Ok (exprState, nproofs) ->
                                let -- nproofs are also equality sources: they link the arguments of a returned call to the
                                    -- caller's variables, which the call's output contract needs
                                    refledNProofs = filter (not . isTrivialEq) (reflProofsByProofs nproofs (proofs ++ nproofs))
                                    visibleIotas = niota : map snd (toList (vVisibleVars exprState))
                                    state'' = vTopLevelScope exprState
                                 in Ok $ vSetReturn state'' niota (filter (proofOnlyOfIotasOrConst visibleIotas) (nproofs ++ refledNProofs))
                            Error e -> Error e
                    Error e -> Error e
            Error e -> Error e

valBlockStatement :: VState -> [Statement] -> Result VState String
valBlockStatement (VState scope iotaCtx proofCtx iotaseq ruleCtx) bstmts =
    case vScopeAdvanceStatement scope of
        Ok advancedScope -> valBlock $ VState (VScopeState empty [] (Continuations $ bstmts ++ [EndBlock]) (Just advancedScope)) iotaCtx proofCtx iotaseq ruleCtx
        Error e -> Error e

-- Validates both branches from the state after the condition, then joins them.
--
-- Proofs are facts about immutable iotas, but assigning an outer variable inside a block
-- appends its proofs to the scope that owns the variable. Reusing that for a branch would
-- leak facts that only hold under the branch condition, so each branch is validated in
-- isolation and only what both branches establish is carried forward (see joinBranches).
--
-- A branch that contains `return` cannot be joined this way, because the statements after the
-- `if` do not run on the path that returned. Those are validated separately (valReturningIf).
valIfStatement :: VState -> Expression -> [Statement] -> [Statement] -> Result VState String
valIfStatement state cond thenStmts elseStmts =
    vAdvanceStatement state `bindResult` \advanced ->
        popIotaFromSeq advanced `bindResult` \(condIota, state') ->
            valExpression state' condIota cond `bindResult` \(condState, condProofs) ->
                let s0 = vInsertProofs condState condProofs
                 in conditionAssumptions True cond condIota s0 `bindResult` \thenAssumed ->
                        conditionAssumptions False cond condIota s0 `bindResult` \elseAssumed ->
                            if containsReturn (thenStmts ++ elseStmts)
                                then valReturningIf s0 thenAssumed thenStmts elseAssumed elseStmts
                                else
                                    valBranch s0 thenAssumed thenStmts `bindResult` \sThen ->
                                        -- Continue the iota sequence so the two branches never share iotas
                                        valBranch (vSetIotaSeq s0 (vGetIotaSeq sThen)) elseAssumed elseStmts `bindResult` \sElse ->
                                            joinBranches s0 (assignedOuterVars s0 (thenStmts ++ elseStmts)) sThen sElse

-- An `if` with a `return` in a branch. Each branch is followed by the rest of the program (the
-- statements after the `if`, then those after the block around it, and so on) and validated to
-- the end. A `return` ends its path, so a guard clause such as `if n < 1 { return 0; }` leaves
-- the rest of the program to be validated only under `n >= 1`. The two paths are then joined
-- by joinReturnPaths.
--
-- A path validates the rest of the program again, so `if` statements that both fall through
-- and contain a `return` somewhere multiply the work.
valReturningIf :: VState -> [IotaProof] -> [Statement] -> [IotaProof] -> [Statement] -> Result VState String
valReturningIf s0 thenAssumed thenStmts elseAssumed elseStmts =
    valPath s0 thenAssumed thenStmts `bindResult` \pThen ->
        valPath (vSetIotaSeq s0 (vGetIotaSeq pThen)) elseAssumed elseStmts `bindResult` \pElse ->
            joinReturnPaths s0 pThen pElse

-- Runs the branch as a block, followed by whatever statements come after it, with the
-- branch condition assumed. The result is the state where the program ended, which is the top
-- level scope either after a `return` or after the last statement.
valPath :: VState -> [IotaProof] -> [Statement] -> Result VState String
valPath state assumptions stmts =
    let VState (VScopeState iotas proofs (Continuations rest) parent) iotaCtx proofCtx iotaseq ruleCtx = state
     in valBlock $
            VState
                (VScopeState iotas (nub (proofs ++ assumptions)) (Continuations (Block stmts : rest)) parent)
                iotaCtx
                proofCtx
                iotaseq
                ruleCtx

-- Continues from the top level scope as it was before the `if`, since both paths have ended.
-- What both paths establish is kept, in the same way as joinBranches. If both paths return,
-- their return values are replaced by one fresh iota. If one falls off the end without
-- returning, the joined state has no return value. A path that only went back to a loop
-- condition (see vMarkLoopBack) places no requirement on the other, which is used as is.
joinReturnPaths :: VState -> VState -> VState -> Result VState String
joinReturnPaths _ pThen pElse
    | vIsLoopBack pThen = Ok pElse
    | vIsLoopBack pElse = Ok (vSetIotaSeq pThen (vGetIotaSeq pElse))
joinReturnPaths s0 pThen pElse =
    let base = vSetContinuations (vTopLevelScope s0) emptyContinuations
        returns = case (vGetReturn pThen, vGetReturn pElse) of
            (Ok thenRet, Ok elseRet) -> [(thenRet, elseRet)]
            _ -> []
     in popNIotasFromSeq pElse (length returns) `bindResult` \(mergeIotas, sAfter) ->
            let merges = zip mergeIotas returns
                baseFacts = vGetProofs base
                visible = nub (concatMap proofIotas baseFacts ++ Map.elems (vVisibleVars base) ++ mergeIotas)
                toMerged proof =
                    foldl
                        (\p (m, (thenRet, _)) -> maybe p id (substituteProofTerm (ATerm thenRet) (ATerm m) p))
                        proof
                        merges
                candidates =
                    filter
                        (\p -> p `notElem` baseFacts && all (`elem` visible) (proofIotas p))
                        (nub (map toMerged (vGetProofs pThen)))
                elseEqualities = [FApp eqProof [ATerm m, ATerm elseRet] | (m, (_, elseRet)) <- merges]
                elseContext = Engine.proofContextFromFacts (vGetProofs pElse ++ elseEqualities)
                kept = [candidate | (candidate, True) <- zip candidates (Engine.entailsAll candidates elseContext)]
                based = vSetIotaSeq base (vGetIotaSeq sAfter)
                withReturn = foldl (\s (m, _) -> vSetReturn s m []) based merges
             in Ok (vInsertProofs withReturn kept)

-- Runs a branch in a child scope that starts with the branch condition assumed. Unlike a
-- plain block there is no EndBlock, so the returned state still has the child scope and
-- everything the branch proved in it. The result is only used to read what the branch
-- established; it is never continued from.
valBranch :: VState -> [IotaProof] -> [Statement] -> Result VState String
valBranch (VState scope iotaCtx proofCtx iotaseq ruleCtx) assumptions stmts =
    valBlock (VState (VScopeState empty assumptions (Continuations stmts) (Just scope)) iotaCtx proofCtx iotaseq ruleCtx)

-- What holds inside a branch: the branch's truth value for the condition iota and, when the
-- condition is a relation, the relation itself (negated for the else branch).
-- Equality has no negation to record, so the else branch of `x = y` learns only the truth value.
conditionAssumptions :: Bool -> Expression -> Iota -> VState -> Result [IotaProof] String
conditionAssumptions branch cond condIota state =
    let truthProof = FApp eqProof [ATerm condIota, CTerm (VBool branch)]
     in case relationCondition branch cond of
            Nothing -> Ok [truthProof]
            Just relCond ->
                case varProofToIotaProof (exprToProof relCond) state of
                    Ok relProof -> Ok [truthProof, relProof]
                    Error e -> Error e

relationCondition :: Bool -> Expression -> Maybe Expression
relationCondition branch (F (Val (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) args) =
    fmap (\r -> F (Val (builtinFunct (Rel r))) args) (if branch then Just rel else negateRel rel)
relationCondition _ _ = Nothing

negateRel :: Rel -> Maybe Rel
negateRel Lt = Just GtEq
negateRel Gt = Just LtEq
negateRel LtEq = Just Gt
negateRel GtEq = Just Lt
negateRel Eq = Nothing

containsReturn :: [Statement] -> Bool
containsReturn = any returns
  where
    returns (Return _) = True
    returns (Block stmts) = containsReturn stmts
    returns (If _ thenStmts elseStmts) = containsReturn thenStmts || containsReturn elseStmts
    returns (While _ _ body) = containsReturn body
    returns _ = False

-- Variables assigned anywhere in the statements, including nested blocks
assignedVars :: [Statement] -> [Variable]
assignedVars = nub . concatMap assigned
  where
    assigned (Assign var _) = [var]
    assigned (Block stmts) = assignedVars stmts
    assigned (If _ thenStmts elseStmts) = assignedVars thenStmts ++ assignedVars elseStmts
    assigned (While _ _ body) = assignedVars body
    assigned _ = []

-- Assigned variables that already exist outside the statements. Assigning any other variable
-- creates a binding local to the branch, which is gone once the branch ends.
assignedOuterVars :: VState -> [Statement] -> [Variable]
assignedOuterVars state stmts =
    filter (`Map.member` vVisibleVars state) (assignedVars stmts)

-- Continues from the state before the branches. Each outer variable assigned in a branch is
-- rebound to a fresh iota `m` that equals the variable's final iota in each branch, and a fact
-- is kept only if both branches establish it. The then-branch's facts are the candidates and
-- the else-branch's facts are what they must be entailed by, so facts that hold only under
-- the condition (including the condition itself) are dropped.
joinBranches :: VState -> [Variable] -> VState -> VState -> Result VState String
joinBranches s0 vars sThen sElse =
    case popNIotasFromSeq sElse (length vars) of
        Error e -> Error e
        Ok (mergeIotas, sAfter) ->
            case (traverseResult (finalIota sThen) vars, traverseResult (finalIota sElse) vars) of
                (Ok thenIotas, Ok elseIotas) ->
                    let merges = zip3 vars mergeIotas (zip thenIotas elseIotas)
                        s0Facts = vGetProofs s0
                        visible =
                            nub (concatMap proofIotas s0Facts ++ Map.elems (vVisibleVars s0) ++ mergeIotas)
                        toMerged proof =
                            foldl
                                (\p (_, m, (thenIota, _)) -> maybe p id (substituteProofTerm (ATerm thenIota) (ATerm m) p))
                                proof
                                merges
                        candidates =
                            filter
                                (\p -> p `notElem` s0Facts && all (`elem` visible) (proofIotas p))
                                (nub (map toMerged (vGetProofs sThen)))
                        elseEqualities = [FApp eqProof [ATerm m, ATerm elseIota] | (_, m, (_, elseIota)) <- merges]
                        elseContext = Engine.proofContextFromFacts (vGetProofs sElse ++ elseEqualities)
                        kept = [candidate | (candidate, True) <- zip candidates (Engine.entailsAll candidates elseContext)]
                        base = vSetIotaSeq s0 (vGetIotaSeq sAfter)
                        factsFor m = filter (elem m . proofIotas) kept
                        rebound = foldl (\s (var, m, _) -> vInsertVar s var m (factsFor m)) base merges
                        boundFacts = concatMap (\(_, m, _) -> factsFor m) merges
                     in Ok (vInsertProofs rebound (filter (`notElem` boundFacts) kept))
                (Error e, _) -> Error e
                (_, Error e) -> Error e
  where
    finalIota state var = case vLookupVar state var of
        Just iota -> Ok iota
        Nothing -> Error ("Variable not found while joining branches: " ++ var)

traverseResult :: (a -> Result b String) -> [a] -> Result [b] String
traverseResult = flatResultMap

-- Validates a loop by its invariant, without unrolling it. This proves partial correctness
-- only: nothing shows the loop terminates, and that is deliberately not checked.
--
-- 1. The invariant must hold before the first iteration.
-- 2. Every outer variable the body assigns is rebound to a fresh value with no facts, so
--    nothing about its earlier values is assumed. Facts about other values stay true because
--    values are immutable.
-- 3. Assuming the invariant and the condition, the body must re-establish the invariant.
-- 4. After the loop, the invariant holds and the condition does not.
--
-- A body that contains `return` is validated as paths, see valReturningWhile.
valWhileStatement :: VState -> Expression -> [ValidationStatement] -> [Statement] -> Result VState String
valWhileStatement state cond invariant body =
    vAdvanceStatement state `bindResult` \advanced ->
        prefixError "Loop invariant does not hold on entry: " (validateUserRuleInputs advanced invariant) `bindResult` \_ ->
            let loopVars = assignedOuterVars advanced body
             in popNIotasFromSeq advanced (length loopVars) `bindResult` \(freshIotas, popped) ->
                    let havocked = foldl (\s (var, iota) -> vInsertVar s var iota []) popped (zip loopVars freshIotas)
                     in assumeValStmts havocked invariant `bindResult` \assumed ->
                            valLoopCondition assumed cond `bindResult` \(condState, condIota) ->
                                conditionAssumptions True cond condIota condState `bindResult` \bodyAssumptions ->
                                    if containsReturn body
                                        then valReturningWhile assumed cond invariant body bodyAssumptions
                                        else
                                            valBranch condState bodyAssumptions body `bindResult` \bodyState ->
                                                prefixError "Loop invariant is not preserved: " (validateUserRuleInputs bodyState invariant) `bindResult` \_ ->
                                                    valLoopExit (vSetIotaSeq assumed (vGetIotaSeq bodyState)) cond

-- The state after a loop: the invariant holds (already assumed in the given state) and the
-- condition is false
valLoopExit :: VState -> Expression -> Result VState String
valLoopExit state cond =
    valLoopCondition state cond `bindResult` \(exitState, exitIota) ->
        conditionAssumptions False cond exitIota exitState `bindResult` \exitAssumptions ->
            Ok (vInsertProofs exitState exitAssumptions)

-- A loop whose body contains `return`. The body ends when it returns, so it is validated as a
-- path of its own (like the branches in valReturningIf), and the program after the loop is a
-- second path that starts from the state where the loop condition is false.
--
-- The body path ends with LoopEnd, which checks that the invariant is preserved on every way
-- of reaching the end of the body and then discards that path, since control only goes back
-- to the condition. Only the paths that return are joined with the path after the loop.
valReturningWhile :: VState -> Expression -> [ValidationStatement] -> [Statement] -> [IotaProof] -> Result VState String
valReturningWhile assumed cond invariant body bodyAssumptions =
    valLoopCondition assumed cond `bindResult` \(condState, _) ->
        valPath (vSetContinuations condState emptyContinuations) bodyAssumptions (body ++ [LoopEnd invariant]) `bindResult` \pBody ->
            valLoopExit (vSetIotaSeq assumed (vGetIotaSeq pBody)) cond `bindResult` \exitState ->
                valBlock exitState `bindResult` \pExit ->
                    joinReturnPaths assumed pBody pExit

-- The end of a loop body: the invariant must hold again. The path then stops, as control
-- goes back to the loop condition.
valLoopEnd :: VState -> [ValidationStatement] -> Result VState String
valLoopEnd state invariant =
    vAdvanceStatement state `bindResult` \advanced ->
        prefixError "Loop invariant is not preserved: " (validateUserRuleInputs advanced invariant) `bindResult` \_ ->
            Ok (vMarkLoopBack (vSetContinuations (vTopLevelScope advanced) emptyContinuations))

-- Validates the loop condition in the given state, recording what it says about its result
valLoopCondition :: VState -> Expression -> Result (VState, Iota) String
valLoopCondition state cond =
    popIotaFromSeq state `bindResult` \(condIota, state') ->
        valExpression state' condIota cond `bindResult` \(condState, condProofs) ->
            Ok (vInsertProofs condState condProofs, condIota)

prefixError :: String -> Result a String -> Result a String
prefixError _ (Ok a) = Ok a
prefixError prefix (Error e) = Error (prefix ++ e)

valEndBlockStatement :: VState -> Result VState String
valEndBlockStatement (VState (VScopeState _ _ _ pscope) iotaCtx proofCtx iotaseq ruleCtx) =
    case pscope of
        Just ps -> Ok $ VState ps iotaCtx proofCtx iotaseq ruleCtx
        _ -> Error "EndBlock must have a parent state"

-- Rewrite proofs using eq relation
-- proofs to change -> eq relations -> updated proofs
reflProofsByProofs :: [IotaProof] -> [IotaProof] -> [IotaProof]
reflProofsByProofs = Engine.reflectProofsByProofs

valValidationStatement :: VState -> ValidationStatement -> Result VState String
valValidationStatement state (Rewrite rwrule) =
    case vAdvanceStatement (doTrace "starting rewrite" state) of
        Ok advancedState -> doTrace "rewrite" (valRewrite advancedState rwrule)
        Error e -> Error e
valValidationStatement state (ProofAssert varproof) =
    case vAdvanceStatement (doTrace "proofAssert" state) of
        Ok state' ->
            case varProofToIotaProof varproof state' of
                Ok iotaProof ->
                    let proofs = vGetProofs state'
                        proofContext = Engine.proofContextFromFacts proofs
                     in if Engine.entails iotaProof proofContext
                            then Ok state'
                            else doTrace4 ("Had vars: " ++ show (vGetVars state')) (doTrace4 ("Had proofs: " ++ show proofs) (Error $ "Assertion failed: " ++ show varproof))
                Error e -> Error e
        Error e -> Error e
valValidationStatement state (AssignProofVar var expr) =
    case vAdvanceStatement state of
        Ok advancedState -> assignProofVarImpl advancedState var expr
        Error e -> Error e

valAxiomDef :: VState -> Variable -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> Result VState String
valAxiomDef state name args inputValStmts outputValStmts =
    case vAdvanceStatement state of
        Ok advancedState -> vInsertRule advancedState name (AxiomRule args inputValStmts outputValStmts)
        Error e -> Error e

valProofDef :: VState -> Variable -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> [ValidationStatement] -> Result VState String
valProofDef state name args inputValStmts outputValStmts bodyValStmts =
    case vAdvanceStatement state of
        Error e -> Error e
        Ok advancedState ->
            case validateProofRuleDefinition advancedState args inputValStmts outputValStmts bodyValStmts of
                Error e -> Error e
                Ok exportedProofs -> vInsertRule advancedState name (ProofRule args inputValStmts exportedProofs)

validateProofRuleDefinition :: VState -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> [ValidationStatement] -> Result [VariableProof] String
validateProofRuleDefinition state args inputValStmts outputValStmts bodyValStmts =
    let newState = vSetScope state emptyVScopeState
        bodyStmts = map ValidationStatement bodyValStmts
        prepared = prepareProofRuleValidationState newState args inputValStmts bodyStmts
     in case prepared of
            Error e -> Error e
            Ok ruleState ->
                case valBlock ruleState of
                    Error e -> Error e
                    Ok bodyState -> exportFunctOutputProofs bodyState args inputValStmts outputValStmts

prepareProofRuleValidationState :: VState -> [Variable] -> [ValidationStatement] -> [Statement] -> Result VState String
prepareProofRuleValidationState state args inputValStmts stmts =
    prepareFunctionValidationState state args inputValStmts stmts

assignProofVarImpl :: VState -> Variable -> Expression -> Result VState String
assignProofVarImpl state var expr =
    case popIotaFromSeq state of
        Ok (niota, state') ->
            case doTrace "apv1" (valExpression state' niota expr) of
                -- TODO: Convert expression to iota proof p1, and add additional proof (niota == p1)
                Ok (exprState, nproofs) ->
                    -- TODO: Should we be doing this in the ordinary valExpression?
                    case varProofToIotaProof (exprToProof expr) exprState of
                        Ok exprAsProof ->
                            let nonEvalProof = FApp eqProof [ATerm niota, exprAsProof]
                                reverseNonEvalProof = reverseEqProof nonEvalProof
                                refledProofs =
                                    reflProofsByProofs (vGetProofs exprState) [nonEvalProof, reverseNonEvalProof]
                                newProofs = nonEvalProof : nproofs ++ refledProofs
                             in doTrace2
                                    ("New assign proof var proofs: " ++ show newProofs)
                                    (Ok $ doTrace "apv2" (vInsertVar exprState var niota newProofs))
                        Error e -> Error e
                Error e -> Error e
        Error e -> Error e

valRewrite :: VState -> RwRule -> Result VState String
valRewrite state (Refl varProof) = rewriteRefl state varProof
valRewrite state (Eval var) = rewriteEval state var
valRewrite state EvalAll = rewriteEvalAll state
valRewrite state (CheckGtZero varProof) = rewriteCheckGtZero state varProof
valRewrite state (CheckRel varProof) = rewriteCheckRel state varProof
valRewrite state (UserRewrite name args) = rewriteUserRule state name args

applyEngineRewrite :: VState -> Engine.EngineRewriteRule -> Result VState String
applyEngineRewrite state rule =
    let oldContext = Engine.proofContextFromFacts (vGetProofs state)
     in case Engine.applyRewrite evalBuiltinFunct rule oldContext of
            Ok newContext ->
                Ok $ vInsertProofs state (Engine.proofContextDelta oldContext newContext)
            Error e -> Error e

rewriteRefl :: VState -> VariableProof -> Result VState String
rewriteRefl state varProof =
    case varProofToIotaProof varProof state of
        Ok _iotaProof ->
            applyEngineRewrite state Engine.EngineRefl
        Error e -> Error e

rewriteEval :: VState -> Variable -> Result VState String
rewriteEval state var =
    case vLookupVar state var of
        Nothing -> Error $ "(Eval) Undefined variable: " ++ var
        Just iota ->
            applyEngineRewrite state (Engine.EngineEval iota)

rewriteEvalAll :: VState -> Result VState String
rewriteEvalAll state =
    applyEngineRewrite state Engine.EngineEvalAll

rewriteCheckGtZero :: VState -> VariableProof -> Result VState String
rewriteCheckGtZero state varProof =
    case varProofToIotaProof varProof state of
        Ok iotaProof -> applyEngineRewrite state (Engine.EngineCheckGtZero iotaProof)
        Error e -> Error e

rewriteCheckRel :: VState -> VariableProof -> Result VState String
rewriteCheckRel state varProof =
    case varProofToIotaProof varProof state of
        Ok iotaProof -> applyEngineRewrite state (Engine.EngineCheckRel iotaProof)
        Error e -> Error e

rewriteUserRule :: VState -> Variable -> [VariableProof] -> Result VState String
rewriteUserRule state name actualArgs =
    case vLookupRule state name of
        Nothing -> Error $ "Unknown rewrite rule: " ++ name
        Just (AxiomRule formals inputValStmts outputValStmts) ->
            applyUserRule state name formals inputValStmts outputValStmts actualArgs
        Just (ProofRule formals inputValStmts exportedProofs) ->
            applyProofRule state name formals inputValStmts exportedProofs actualArgs

applyUserRule :: VState -> Variable -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> [VariableProof] -> Result VState String
applyUserRule state name formals inputValStmts outputValStmts actualArgs
    | length formals /= length actualArgs =
        Error $ "Rewrite rule " ++ name ++ " expected " ++ show (length formals) ++ " arguments, got " ++ show (length actualArgs)
    | otherwise =
        let bindings = Map.fromList (zip formals actualArgs)
            instInputs = map (substituteValidationStatement bindings) inputValStmts
            instOutputs = map (substituteValidationStatement bindings) outputValStmts
         in case validateUserRuleInputs state instInputs of
                Error e -> Error $ "Rewrite rule " ++ name ++ " input validation failed: " ++ e
                Ok _ ->
                    case assumeValStmts state instOutputs of
                        Error e -> Error $ "Rewrite rule " ++ name ++ " output instantiation failed: " ++ e
                        Ok stateWithOutputs -> applyEngineRewrite stateWithOutputs Engine.EngineRefl

applyProofRule :: VState -> Variable -> [Variable] -> [ValidationStatement] -> [VariableProof] -> [VariableProof] -> Result VState String
applyProofRule state name formals inputValStmts exportedProofs actualArgs
    | length formals /= length actualArgs =
        Error $ "Rewrite rule " ++ name ++ " expected " ++ show (length formals) ++ " arguments, got " ++ show (length actualArgs)
    | otherwise =
        let bindings = Map.fromList (zip formals actualArgs)
            instInputs = map (substituteValidationStatement bindings) inputValStmts
            instOutputs = map (substituteVariableProof bindings) exportedProofs
         in case validateUserRuleInputs state instInputs of
                Error e -> Error $ "Rewrite rule " ++ name ++ " input validation failed: " ++ e
                Ok _ ->
                    case flatResultMap (`varProofToIotaProof` state) instOutputs of
                        Error e -> Error $ "Rewrite rule " ++ name ++ " output instantiation failed: " ++ e
                        Ok iotaProofs -> applyEngineRewrite (vInsertProofs state iotaProofs) Engine.EngineRefl

validateUserRuleInputs :: VState -> [ValidationStatement] -> Result VState String
validateUserRuleInputs state [] = Ok state
validateUserRuleInputs state valStmts =
    let VState _ iotaCtx proofCtx iotaseq ruleCtx = state
     in valBlock $
            VState
                (VScopeState (vVisibleVars state) (vGetProofs state) (Continuations (map ValidationStatement valStmts)) Nothing)
                iotaCtx
                proofCtx
                iotaseq
                ruleCtx

substituteValidationStatement :: Map Variable VariableProof -> ValidationStatement -> ValidationStatement
substituteValidationStatement bindings (Rewrite rwrule) = Rewrite (substituteRwRule bindings rwrule)
substituteValidationStatement bindings (ProofAssert varproof) = ProofAssert (substituteVariableProof bindings varproof)
substituteValidationStatement bindings (AssignProofVar var expr) = AssignProofVar var (substituteExpression bindings expr)

substituteRwRule :: Map Variable VariableProof -> RwRule -> RwRule
substituteRwRule bindings (Refl varproof) = Refl (substituteVariableProof bindings varproof)
substituteRwRule _ (Eval var) = Eval var
substituteRwRule _ EvalAll = EvalAll
substituteRwRule bindings (CheckGtZero varproof) = CheckGtZero (substituteVariableProof bindings varproof)
substituteRwRule bindings (CheckRel varproof) = CheckRel (substituteVariableProof bindings varproof)
substituteRwRule bindings (UserRewrite name args) = UserRewrite name (map (substituteVariableProof bindings) args)

substituteVariableProof :: Map Variable VariableProof -> VariableProof -> VariableProof
substituteVariableProof bindings (ATerm var) =
    case Map.lookup var bindings of
        Just proof -> proof
        Nothing -> ATerm var
substituteVariableProof _ cterm@CTerm{} = cterm
substituteVariableProof bindings (FApp funct args) =
    FApp (substituteVariableProof bindings funct) (map (substituteVariableProof bindings) args)

substituteExpression :: Map Variable VariableProof -> Expression -> Expression
substituteExpression bindings (Var var) =
    case Map.lookup var bindings of
        Just replacement -> proofToExpression replacement
        _ -> Var var
substituteExpression _ val@Val{} = val
substituteExpression bindings (F funct args) =
    F (substituteExpression bindings funct) (map (substituteExpression bindings) args)

proofToExpression :: VariableProof -> Expression
proofToExpression (ATerm var) = Var var
proofToExpression (CTerm val) = Val val
proofToExpression (FApp funct args) = F (proofToExpression funct) (map proofToExpression args)

evalExpressionList :: State -> [Expression] -> Result (State, [Value]) String
evalExpressionList state [] = Ok (state, [])
evalExpressionList sstate (expr : exprs) =
    case evalExpression sstate expr of
        Ok (val, estate) ->
            case evalExpressionList estate exprs of
                Ok (state, vals) -> Ok (state, val : vals)
                Error e -> Error e
        Error e -> Error e

evalExpression :: State -> Expression -> Result (Value, State) String
evalExpression state (Val val) = Ok (val, state)
evalExpression state (Var var) =
    case lookupVar state var of
        Just val -> Ok (val, state)
        Nothing -> Error $ "Undefined variable: " ++ var
evalExpression sstate (F fnExpr argExprs) =
    case evalExpressionList sstate (fnExpr : argExprs) of
        Ok (State scope valCtx, fval : argVals) ->
            case evalFunctCall fval valCtx argVals of
                Ok val -> Ok (val, State scope valCtx)
                Error e -> Error e
        Ok (_, []) -> Error "Function expression must produce a value"
        Error e -> Error e

-- State -> iota of result -> expression -> Result (updated state, proofs about result iota) String
valExpression :: VState -> Iota -> Expression -> Result (VState, [IotaProof]) String
valExpression state iota (Val val) = valExpressionValue state iota val
valExpression state iota (Var var) = valExpressionVar state iota var
valExpression state iota (F fnexpr argexprs) = valExpressionFunction state iota fnexpr argexprs
valExpression _ _ e = Error $ "Unsupported expression: " ++ show e

valExpressionValue :: VState -> Iota -> Value -> Result (VState, [IotaProof]) String
valExpressionValue state iota val =
    let functValResult = validateValue state val
        r = mapResult (\validatedVal -> (state, [FApp eqProof [ATerm iota, CTerm validatedVal]])) functValResult
     in doTrace3 (show r) r

valExpressionVar :: VState -> Iota -> Variable -> Result (VState, [IotaProof]) String
valExpressionVar state iota var =
    case vLookupVar state var of
        Nothing -> Error $ "(Validate Expression) Undefined variable: " ++ var ++ " \nState: " ++ show state
        Just oiota ->
            let iotaEq = FApp eqProof [ATerm iota, ATerm oiota]
                reverseIotaEq = reverseEqProof iotaEq
                refledEqProofs = reflProofsByProofs (vGetProofs state) [iotaEq, reverseIotaEq]
             in Ok (state, iotaEq : reverseIotaEq : refledEqProofs)

valExpressionFunction :: VState -> Iota -> Expression -> [Expression] -> Result (VState, [IotaProof]) String
valExpressionFunction (VState scope iotaCtx proofCtx iotaseq ruleCtx) iota fnexpr argexprs =
    case valFunctExprHelper (VState scope iotaCtx proofCtx iotaseq ruleCtx) fnexpr argexprs iota of
        Ok (nextState, flatInputProofs, functProofs, argIotas) ->
            case varProofToIotaProof (exprToProof (F fnexpr argexprs)) nextState of
                Ok fnProof ->
                    let nonEvalProof = FApp eqProof [ATerm iota, fnProof]
                        -- Only the direct equalities between an argument's fresh iota and another
                        -- iota are kept: the reflected copies of every other fact would bloat the context.
                        argLinks = filter (isArgLink argIotas) flatInputProofs
                     in -- The links tie each argument's fresh iota to the caller's variable, which output
                        -- contracts that mention the arguments (size(return) = size(list) + 1) need
                        Ok (nextState, nonEvalProof : functProofs ++ argLinks)
                Error e -> Error e
        Error e -> Error e

isTrivialEq :: IotaProof -> Bool
isTrivialEq (FApp funct [lhs, rhs]) = funct == eqProof && lhs == rhs
isTrivialEq _ = False

isArgLink :: [Iota] -> IotaProof -> Bool
isArgLink argIotas (FApp funct [ATerm lhs, ATerm rhs]) = funct == eqProof && (lhs `elem` argIotas || rhs `elem` argIotas)
isArgLink _ _ = False

validateValue :: VState -> Value -> Result Value String
validateValue state val = case val of
    VFunct args inputValStmts outputValStmts body _ ->
        mapResult
            (VFunct args inputValStmts outputValStmts body)
            (valFunctDef state args inputValStmts outputValStmts body)
    _ -> Ok val

valFunctDef :: VState -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> FunctBody -> Result [VariableProof] String
valFunctDef state args inputValStmts outputValStmts (NativeFunct stmts) =
    case prepareFunctionValidationState state args inputValStmts stmts of
            Ok fnValState ->
                let valResult =
                        doTrace4
                            ("valFunctDef: Validating body: " ++ show (vGetContinuations fnValState))
                            (doTrace4 ("Preval fn body: Vars: " ++ show (vGetVars fnValState) ++ " Proofs: " ++ show (vGetProofs fnValState)) (valReturningBlock fnValState))
                 in case doTrace3 ("valFunctDef val result: " ++ show valResult) valResult of
                        Ok (bodyState, _) -> exportFunctOutputProofs bodyState args inputValStmts outputValStmts
                        Error e -> Error e
            Error e -> Error e
valFunctDef _ _ _ _ BuiltinFunct{} = Ok [] -- Builtin functions assumed to be validly defined

prepareFunctionValidationState :: VState -> [Variable] -> [ValidationStatement] -> [Statement] -> Result VState String
prepareFunctionValidationState state args inputValStmts stmts =
    let newState = vSetScope state emptyVScopeState
        wContinuations =
            doTrace4
                ("valFunctDef: Setting conts: " ++ show stmts)
                (vSetContinuations newState (Continuations stmts))
     in case popNIotasFromSeq wContinuations (length args) of
            Ok (niotas, newState') ->
                case zipMap args niotas (,) of
                    Ok (argIotas, _) ->
                        let preInputValState = vInsertVars newState' argIotas []
                         in assumeValStmts preInputValState inputValStmts
                    Error e -> Error e
            Error e -> Error e

exportFunctOutputProofs :: VState -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> Result [VariableProof] String
exportFunctOutputProofs bodyState args inputValStmts outputValStmts =
    let bodyStateWithOutput =
            if null outputValStmts
                then Ok bodyState
                else
                    valBlock
                        ( vSetContinuations
                            bodyState
                            (Continuations (map ValidationStatement outputValStmts))
                        )
     in case bodyStateWithOutput of
            Error e -> Error e
            Ok outputState ->
                let allowedNames = nub (args ++ ["return"] ++ concatMap valStmtDefinedVars inputValStmts ++ concatMap valStmtDefinedVars outputValStmts)
                 in let allowedBindings =
                            mapMaybe
                                (\var -> case vLookupVar outputState var of
                                    Just iota -> Just (var, iota)
                                    Nothing -> Nothing)
                                allowedNames
                    in let namedIotas = namedIotaMap allowedBindings
                       in let exportedProofs =
                                  nub $
                                      mapMaybe
                                          (iotaProofToVarProof namedIotas)
                                          ( filter
                                              (proofOnlyOfNamedIotasOrConst namedIotas)
                                              (vGetProofs outputState)
                                          )
                          in Ok exportedProofs

assumeValStmts :: VState -> [ValidationStatement] -> Result VState String
assumeValStmts state [] = Ok state
assumeValStmts state (stmt : stmts) = doTraceStatements ("assumeValStmt: " ++ show stmt) $
    case assumeValStmt state stmt of
        Ok newState -> assumeValStmts newState stmts
        Error e -> Error e

assumeValStmt :: VState -> ValidationStatement -> Result VState String
assumeValStmt state (Rewrite rwrule) = Ok state -- TODO: Instead of ignoring rewrites entirely during assumptions, should we just ignore failures?
--  doTrace4 ("assume rewrite: " ++ show rwrule ++ " Proofs: " ++ show (vGetProofs state)) (valRewrite state rwrule)
assumeValStmt state (ProofAssert varproof) =
    case varProofToIotaProof varproof state of
        Ok proof -> Ok $ vInsertProofs state [proof]
        Error e -> Error e
assumeValStmt state (AssignProofVar var expr) = assignProofVarImpl state var expr

-- Given expression evaluating to a function object, expressions evaluating to
-- the function's arguments, and the iota corresponding to the function return value,
-- validate and return:
-- 1) proofs of input expressions 2) proofs of the evaluated fn result 3) the new iotas used
-- state -> fnexpr -> argexprs -> (argProofs, functresultproofs, new iotas)
valFunctExprHelper :: VState -> Expression -> [Expression] -> Iota -> Result (VState, [IotaProof], [IotaProof], [Iota]) String
valFunctExprHelper (VState scope iotaCtx proofCtx iotaseq ruleCtx) functionExpr argExprs resultIota =
    let proofs = vGetProofs (VState scope iotaCtx proofCtx iotaseq ruleCtx)
     in -- Get proofs from the function and arg expressions
         let exprsToVal = functionExpr : argExprs
          in let (freshIotas, iotaseq') = splitAt (length exprsToVal) iotaseq
               in let exprState = VState scope iotaCtx proofCtx iotaseq' ruleCtx
                   in case valExpressionSeq exprState exprsToVal freshIotas of
                         Error e -> Error e
                         Ok (exprValidatedState, inputProofGroups) ->
                             let flatInputProofs = concat inputProofGroups
                              in let reflectedInputProofs =
                                         reflProofsByProofs flatInputProofs (proofs ++ proofCtx)
                                   in let availableInputProofs = reflectedInputProofs ++ flatInputProofs
                                      in case freshIotas of
                                            functionIota : inputIotas ->
                                                case valFunctCall exprValidatedState functionIota inputIotas availableInputProofs resultIota of
                                                    Ok (callState, functionProofs) -> Ok (callState, flatInputProofs, functionProofs, freshIotas)
                                                    Error e -> Error e
                                            [] -> Error "Not enough fresh iotas for function expression"

valExpressionSeq :: VState -> [Expression] -> [Iota] -> Result (VState, [[IotaProof]]) String
valExpressionSeq state [] [] = Ok (state, [])
valExpressionSeq state (expr : exprs) (iota : iotas) =
    case valExpression state iota expr of
        Ok (nextState, proofs) ->
            case valExpressionSeq nextState exprs iotas of
                Ok (finalState, remainingProofs) -> Ok (finalState, proofs : remainingProofs)
                Error e -> Error e
        Error e -> Error e
valExpressionSeq _ _ _ = Error "Expression/iota arity mismatch"

evalFunctCall :: Value -> Map Variable Value -> [Value] -> Result Value String
evalFunctCall (VFunct vars _ _ _ _) _ args
    | length vars /= length args = Error (arityMismatchMessage vars args)
evalFunctCall (VFunct _ _ _ (BuiltinFunct builtin) _) valCtx args =
    evalBuiltinFunct builtin args
evalFunctCall (VFunct vars _ _ (NativeFunct block) _) valCtx args =
    case zipMap vars args (,) of
        Ok (argVals, _) ->
            let varMap = foldl (\vm (var, val) -> insert var val vm) empty argVals
                scope = ScopeState varMap (Continuations block) (Just emptyScopeState)
             in case evalReturningBlock (State scope valCtx) of
                    Ok (_, Just val) -> Ok val
                    Ok (_, Nothing) -> Error "Function did not return a value"
                    Error e -> Error e
        Error e -> Error e
evalFunctCall _ _ _ = Error "Object being called must be a function"

arityMismatchMessage :: [Variable] -> [a] -> String
arityMismatchMessage formals actuals =
    "Function expected " ++ show (length formals) ++ " arguments, got " ++ show (length actuals)

evalBuiltinFunct :: BuiltinFunct -> [Value] -> Result Value String
evalBuiltinFunct Size [VIntList l] = Ok $ VInt (fromIntegral (length l))
evalBuiltinFunct Size _ = Error "Size only valid for IntList"
evalBuiltinFunct First [VIntList []] = Error "First requires a non-empty IntList"
evalBuiltinFunct First [VIntList l] = Ok $ VInt (head l)
evalBuiltinFunct First _ = Error "First only valid for IntList"
evalBuiltinFunct Last [VIntList []] = Error "Last requires a non-empty IntList"
evalBuiltinFunct Last [VIntList l] = Ok $ VInt (last l)
evalBuiltinFunct Last _ = Error "Last only valid for IntList"
evalBuiltinFunct Get [VIntList l, VInt i]
    | i < 0 || i >= fromIntegral (length l) = Error "Get index out of range"
    | otherwise = Ok $ VInt (l !! fromIntegral i)
evalBuiltinFunct Get _ = Error "Get only valid for an IntList and an int"
evalBuiltinFunct Push [VIntList l, VInt x] = Ok $ VIntList (l ++ [x])
evalBuiltinFunct Push _ = Error "Push only valid for an IntList and an int"
evalBuiltinFunct Minus [VInt v1, VInt v2] = Ok $ VInt (v1 - v2)
evalBuiltinFunct Minus _ = Error "Plus only valid for two ints"
evalBuiltinFunct Plus [VInt v1, VInt v2] = Ok $ VInt (v1 + v2)
evalBuiltinFunct Plus _ = Error "Plus only valid for two ints"
evalBuiltinFunct (Rel Eq) [VInt v1, VInt v2] = Ok $ VBool (v1 == v2)
evalBuiltinFunct (Rel Eq) _ = Error "Eq only valid for two ints"
evalBuiltinFunct (Rel Lt) [VInt v1, VInt v2] = Ok $ VBool (v1 < v2)
evalBuiltinFunct (Rel Lt) _ = Error "Lt only valid for two ints"
evalBuiltinFunct (Rel Gt) [VInt v1, VInt v2] = Ok $ VBool (v1 > v2)
evalBuiltinFunct (Rel Gt) _ = Error "Rt only valid for two ints"
evalBuiltinFunct (Rel LtEq) [VInt v1, VInt v2] = Ok $ VBool (v1 <= v2)
evalBuiltinFunct (Rel LtEq) _ = Error "LtEq only valid for two ints"
evalBuiltinFunct (Rel GtEq) [VInt v1, VInt v2] = Ok $ VBool (v1 >= v2)
evalBuiltinFunct (Rel GtEq) _ = Error "GtEq only valid for two ints"

iotaMapToConcreteMap :: (Ord a) => Map a Iota -> [IotaProof] -> Map a Value
iotaMapToConcreteMap imap proofs =
    Data.Map.fromList $
        mapMaybe
            ( \(k, i) -> case iotaToValueWProofList i proofs of
                Just val -> Just (k, val)
                Nothing -> Nothing
            )
            (Data.Map.toList imap)

concreteValOfIotaMaybe :: Iota -> [IotaProof] -> Maybe Value
concreteValOfIotaMaybe _ [] = Nothing
concreteValOfIotaMaybe iota (proof : ptail) = case concreteValOfIotaFromProofMaybe iota proof of
    Just val -> Just val
    Nothing -> concreteValOfIotaMaybe iota ptail

concreteValOfIotaFromProofMaybe :: Iota -> IotaProof -> Maybe Value
concreteValOfIotaFromProofMaybe iota proof = case proof of
    FApp funct [ATerm piota, CTerm val] | funct == eqProof && piota == iota -> Just val
    _ -> Nothing

-- Takes: Funct iota, funct input iotas, funct input proofs, result iota
-- Returns: Proofs for result iota
-- TODO: Currently only supporting producing concrete proof results
-- (ex. size(iotaA=[5, 4]) = iotaB=2)
-- Later update to produce abstract FApp proofs
-- (ex. size(iotaA) = iotaB)
valFunctCall :: VState -> Iota -> [Iota] -> [IotaProof] -> Iota -> Result (VState, [IotaProof]) String
valFunctCall state fniota iiotas iproofs retiota =
    case resolveValidatedFunction fniota iproofs of
        Error e -> Error e
        Ok (VFunct varArgs _ _ _ _)
            | length varArgs /= length iiotas -> Error (arityMismatchMessage varArgs iiotas)
        Ok fnVal@(VFunct varArgs inputValStmts _ _ exportedProofs) ->
            case valFunctInput state varArgs iiotas iproofs inputValStmts of
                Error e -> Error $ "Funct input validation failed: " ++ e
                Ok fnValState ->
                    case instantiateFunctOutputProofs state varArgs iiotas retiota exportedProofs of
                        Error e -> Error e
                        Ok (stateWithExports, instantiatedProofs) ->
                            Ok (stateWithExports, maybeConcreteFunctionResult fnValState fnVal iiotas iproofs retiota instantiatedProofs)

resolveValidatedFunction :: Iota -> [IotaProof] -> Result Value String
resolveValidatedFunction fniota iproofs =
    case concreteValOfIotaMaybe fniota iproofs of
        Just fnVal@VFunct{} -> Ok fnVal
        Just _ -> Error "Non-function value called"
        Nothing ->
            Error $
                "Function object not validated. Function iota: "
                    ++ show fniota
                    ++ ". Input proofs: "
                    ++ show iproofs

maybeConcreteFunctionResult :: VState -> Value -> [Iota] -> [IotaProof] -> Iota -> [IotaProof] -> [IotaProof]
maybeConcreteFunctionResult fnValState fnVal iiotas iproofs retiota instantiatedProofs =
    case collectMaybes (`concreteValOfIotaMaybe` iproofs) iiotas of
        Just argVals ->
            let VState _ iotaCtx proofCtx _ _ = fnValState
             in case evalFunctCall fnVal (iotaMapToConcreteMap iotaCtx proofCtx) argVals of
                    Ok functResult -> FApp eqProof [ATerm retiota, CTerm functResult] : instantiatedProofs
                    Error _ -> instantiatedProofs
        Nothing -> instantiatedProofs

-- Exported proof variables are rebound to fresh caller-side iotas before the callee's
-- proof templates are converted back into concrete caller-visible proofs.
instantiateFunctOutputProofs :: VState -> [Variable] -> [Iota] -> Iota -> [VariableProof] -> Result (VState, [IotaProof]) String
instantiateFunctOutputProofs state _ _ _ [] = Ok (state, [])
instantiateFunctOutputProofs state varArgs argIotas returnIota exportedProofs =
    let exportedNames = nub (concatMap proofVars exportedProofs)
     in let exportedProofVarNames = filter (\var -> var /= "return" && notElem var varArgs) exportedNames
         in case popNIotasFromSeq state (length exportedProofVarNames) of
                Ok (exportedProofVarIotas, state') ->
                    let argBindings = zip (varArgs ++ ["return"]) (argIotas ++ [returnIota])
                        proofVarBindings = exportedProofVarNames `zip` exportedProofVarIotas
                        exportBindings = argBindings ++ proofVarBindings
                        exportState = buildVarToIotaState state' exportBindings [] (case state' of VState _ _ _ remaining _ -> remaining)
                     in case flatResultMap (`varProofToIotaProof` exportState) exportedProofs of
                            Ok instantiatedProofs -> Ok (vInsertVars state' proofVarBindings instantiatedProofs, instantiatedProofs)
                            Error e -> Error e
                Error e -> Error e

-- Validate the input arguments of a function call using the functions validation block
-- (outer) state -> function arg names -> function arg iotas -> function arg proofs -> function validation block
-- -> function validation state
valFunctInput :: VState -> [Variable] -> [Iota] -> [IotaProof] -> [ValidationStatement] -> Result VState String
valFunctInput state _ _ _ [] = Ok state
valFunctInput state varArgs argIotas argProofs valStmts =
    let VState _ iotaCtx proofCtx iotaseq ruleCtx = state
     in case doTrace3 ("Arg iotas: " ++ show argIotas) (doTrace3 ("Arg proofs: " ++ show argProofs) (zipMap varArgs argIotas (,))) of
            Ok (argIotasMap, _) ->
                let stmts = map ValidationStatement valStmts
                 in valBlock $
                        VState
                            (VScopeState (Data.Map.fromList argIotasMap) (argProofs ++ vGetProofs state) (Continuations stmts) Nothing)
                            iotaCtx
                            proofCtx
                            iotaseq
                            ruleCtx
            Error e -> Error e

-- TODO: Export validation vars from this into the function body
-- WIP: ^^ + use refling rather than evaling the function call in the input validation

iotaLhsEq :: Iota -> [IotaProof] -> [IotaProof]
iotaLhsEq _ [] = []
iotaLhsEq iota (proof : tail) =
    case proof of
        FApp funct [ATerm liota, rhsProof]
            | funct == eqProof && liota == iota ->
                rhsProof : iotaLhsEq iota tail
        _ -> iotaLhsEq iota tail

findIotaEqToFn :: [Variable] -> [IotaProof] -> Maybe Iota
findIotaEqToFn _ [] = Nothing
findIotaEqToFn varList (proof : tail) =
    case proof of
        FApp funct [ATerm iota, CTerm (VFunct argList _ _ _ _)]
            | funct == eqProof && argList == varList ->
                Just iota
        _ -> findIotaEqToFn varList tail
