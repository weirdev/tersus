module Proof where

import Data.Map (
    Map,
    empty,
    fromList,
    insert,
    toList,
  )

import Data.Containers.ListUtils (nubOrd)
import Data.List (isInfixOf)
import Data.Maybe (isNothing, mapMaybe, fromMaybe)
import qualified Data.Map as Map

import qualified ProofEngine as Engine
import Pretty (renderVarProof)
import ProofHelpers
import StdLib
import TersusTypes
import TypeCheck (elaborate)
import Utils

-- Public fns
evaluate :: [Statement] -> Result State String
evaluate [] = Ok initState
evaluate l = evalBlock $ initStateWStatements l

validate :: [Statement] -> Result VState String
validate [] = Ok $ VState emptyVScopeState empty [] [] stdLibRuleCtx
validate l = case elaborate l of {Error e -> Error e; Ok l' -> validateTyped l'}

validateTyped :: [Statement] -> Result VState String
validateTyped l = case valBlock $ initVStateWStatements l of
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

-- Concrete evaluation normally runs until the program ends. When the validator evaluates a call to learn
-- its result, the evaluation carries a budget of statements in a name no program can write, and fails
-- once the budget is spent, so that validating a program cannot depend on a long or endless computation.
fuelKey :: Variable
fuelKey = "$fuel"

validationFuel :: Integer
validationFuel = 100000

-- Takes one statement's worth of fuel, if the evaluation has any
spendFuel :: State -> Result State String
spendFuel state@(State scope ctxVals) =
    case Map.lookup fuelKey ctxVals of
        Just (VInt n)
            | n <= 0 -> Error "Evaluation ran out of fuel"
            | otherwise -> Ok (State scope (Map.insert fuelKey (VInt (n - 1)) ctxVals))
        _ -> Ok state

evalNextStatement :: State -> Result State String
evalNextStatement fuelState = spendFuel fuelState `bindResult` evalNextStatementWithFuel

evalNextStatementWithFuel :: State -> Result State String
evalNextStatementWithFuel state = case nextStatement state of
    Ok (Assign var expr) -> evalAssignStatement state var expr
    Ok (Let var expr) -> evalLetStatement state var expr
    Ok (Return expr) -> evalReturnStatement state expr
    Ok ValidationStatement{} -> advanceStatement state
    Ok AxiomDef{} -> advanceStatement state
    Ok StructDef{} -> advanceStatement state
    Ok EnumDef{} -> advanceStatement state
    Ok ProofDef{} -> advanceStatement state
    Ok (Block statements) -> evalBlockStatement state statements
    Ok (If cond thenStmts elseStmts) -> evalIfStatement state cond thenStmts elseStmts
    Ok loop@(While cond _ _ body) -> evalWhileStatement state loop cond body
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
                Ok (val, rState) -> registerGlobalFunction var val (insertVar rState var val)
                Error e -> Error e
        Error e -> Error e

-- A function defined at the top level can be called from the functions defined after it, which
-- see it by name like the standard library. It is not a closure: the bodies of those functions
-- see only their own arguments, the standard library and these functions. A name is defined once.
registerGlobalFunction :: Variable -> Value -> State -> Result State String
registerGlobalFunction var val@(VFunct _ _ _ NativeFunct{} _) (State scope@(ScopeState _ _ Nothing) ctxVals)
    | Map.member var ctxVals = Error ("Function already defined: " ++ var)
    | otherwise = Ok (State scope (Map.insert var val ctxVals))
registerGlobalFunction _ _ state = Ok state

evalLetStatement :: State -> Variable -> Expression -> Result State String
evalLetStatement state var expr =
    advanceStatement state `bindResult` \advancedState ->
        evalExpression advancedState expr `bindResult` \(val, rState) -> Ok (bindVar rState var val)

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
                    Let var expr -> valLetStatement state var expr
                    Return expr -> valReturnStatement state expr
                    ValidationStatement valStmt -> valValidationStatement state valStmt
                    StructDef{} -> vAdvanceStatement state
                    EnumDef{} -> vAdvanceStatement state
                    AxiomDef name args inputs outputs -> valAxiomDef state name args inputs outputs
                    ProofDef name args inputs outputs body -> valProofDef state name args inputs outputs body
                    Block bstmts -> valBlockStatement state bstmts
                    If cond thenStmts elseStmts -> valIfStatement state cond thenStmts elseStmts
                    While cond invariant term body -> valWhileStatement state cond invariant term body
                    LoopEnd invariant decrease -> valLoopEnd state invariant decrease
                    EndBlock -> valEndBlockStatement state
        Error e -> Error e

vNextStatement :: VState -> Result Statement String
vNextStatement (VState (VScopeState _ _ (Continuations (stmt : _)) _) _ _ _ _) = Ok stmt
vNextStatement _ = Error "No next validation statement available"

valAssignStatement :: VState -> Variable -> Expression -> Result VState String
valAssignStatement state var expr =
    vAdvanceStatement state `bindResult` \advancedState ->
        popIotaFromSeq advancedState `bindResult` \(niota, state') ->
            bindFunctionToItself var expr state' `bindResult` \stateWithSelf ->
                valExpression stateWithSelf niota expr `bindResult` \(exprState, nproofs) ->
                    registerGlobalFunctionProof var niota expr nproofs (vInsertVar (withGlobalsOf state' exprState) var niota nproofs)

valLetStatement :: VState -> Variable -> Expression -> Result VState String
valLetStatement state var expr =
    vAdvanceStatement state `bindResult` \advancedState ->
        popIotaFromSeq advancedState `bindResult` \(niota, state') ->
            valExpression state' niota expr `bindResult` \(exprState, nproofs) ->
                Ok (vBindVar exprState var niota nproofs)

-- A function defined at the top level can call itself. Its body is validated with its own name bound to
-- a copy of the function that exports what its output contract asserts, without having shown it yet:
-- the body is validated assuming the contract, and the contract is then checked against the body.
-- A call to the copy has to show that the function ends, see callTermination.
bindFunctionToItself :: Variable -> Expression -> VState -> Result VState String
bindFunctionToItself var (Val (VFunct args ins outs (NativeFunct sig term stmts) _)) state@(VState scope@(VScopeState _ _ _ Nothing) iotaCtx proofCtx _ ruleCtx)
    | Map.member var iotaCtx || Map.member functionBodyMarker iotaCtx = Ok state
    | otherwise =
        popIotaFromSeq state `bindResult` \(selfIota, VState _ _ _ iotaseq _) ->
            let body = NativeFunct sig (Just (Recursing term)) stmts
                assumed = VFunct args ins outs body [p | ProofAssert p <- outs, all (`elem` ("return" : args)) (proofVars p)]
                fact = FApp eqProof [ATerm selfIota, CTerm assumed]
             in Ok (withFacts state [fact] (VState scope (Map.insert var selfIota iotaCtx) (proofCtx ++ [fact]) iotaseq ruleCtx))
bindFunctionToItself _ _ state = Ok state

-- The state after an expression, without the global bindings that were added only to validate it
withGlobalsOf :: VState -> VState -> VState
withGlobalsOf (VState _ iotaCtx proofCtx _ _) expr@(VState scope _ _ iotaseq ruleCtx) = keepCache expr (VState scope iotaCtx proofCtx iotaseq ruleCtx)

-- The validation counterpart of registerGlobalFunction: the function's iota and the proof of its value
-- join the global context, which the bodies of later functions are validated in.
registerGlobalFunctionProof :: Variable -> Iota -> Expression -> [IotaProof] -> VState -> Result VState String
registerGlobalFunctionProof var niota (Val (VFunct _ _ _ NativeFunct{} _)) nproofs state@(VState scope@(VScopeState _ _ _ Nothing) iotaCtx proofCtx iotaseq ruleCtx)
    | Map.member functionBodyMarker iotaCtx = Ok state
    | Map.member var iotaCtx = Error ("Function already defined: " ++ var)
    | otherwise = Ok (withFacts state nproofs (VState scope (Map.insert var niota iotaCtx) (proofCtx ++ nproofs) iotaseq ruleCtx))
registerGlobalFunctionProof _ _ _ _ state = Ok state

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
                                    -- caller's variables, which the call's output contract needs. Two rounds, because a
                                    -- fact such as get(return, size(list)) = x needs both list and x replaced.
                                    eqSources = proofs ++ nproofs
                                    reflectedOnce = reflProofsByProofs nproofs eqSources
                                    reflectedTwice = reflProofsByProofs (nproofs ++ reflectedOnce) eqSources
                                    refledNProofs = filter (not . isTrivialEq) (nubOrd (reflectedOnce ++ reflectedTwice))
                                    visibleIotas = niota : map snd (toList (vVisibleVars exprState))
                                    state'' = vTopLevelScope exprState
                                 in Ok $ vSetReturn state'' niota (filter (proofOnlyOfIotasOrConst visibleIotas) (nproofs ++ refledNProofs))
                            Error e -> Error e
                    Error e -> Error e
            Error e -> Error e

valBlockStatement :: VState -> [Statement] -> Result VState String
valBlockStatement state@(VState scope iotaCtx proofCtx iotaseq ruleCtx) bstmts =
    case vScopeAdvanceStatement scope of
        Ok advancedScope -> valBlock $ keepCache state (VState (VScopeState empty [] (Continuations $ bstmts ++ [EndBlock]) (Just advancedScope)) iotaCtx proofCtx iotaseq ruleCtx)
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
            withFacts
                state
                assumptions
                ( VState
                    (VScopeState iotas (nubOrd (proofs ++ assumptions)) (Continuations (Block stmts : rest)) parent)
                    iotaCtx
                    proofCtx
                    iotaseq
                    ruleCtx
                )

-- Continues from the top level scope as it was before the `if`, since both paths have ended.
-- What both paths establish is kept, in the same way as joinBranches. If both paths return,
-- their return values are replaced by one fresh iota. If one falls off the end without
-- returning, the joined state has no return value. A path that only went back to a loop
-- condition (see vMarkLoopBack) places no requirement on the other, which is used as is.
joinReturnPaths :: VState -> VState -> VState -> Result VState String
joinReturnPaths _ pThen pElse
    | vIsLoopBack pThen = Ok pElse
    | vIsLoopBack pElse = Ok (vSetIotaSeq pThen (vGetIotaSeq pElse))
joinReturnPaths s0 pThen pElse
    | vacuous pThen && not (vacuous pElse) = joinReturnPathsFrom s0 pElse (vSetIotaSeq pThen (vGetIotaSeq pElse))
    | otherwise = joinReturnPathsFrom s0 pThen pElse

joinReturnPathsFrom :: VState -> VState -> VState -> Result VState String
joinReturnPathsFrom s0 pThen pElse =
    let base = vSetContinuations (vTopLevelScope s0) emptyContinuations
        returns = case (vGetReturn pThen, vGetReturn pElse) of
            (Ok thenRet, Ok elseRet) -> [(thenRet, elseRet)]
            _ -> []
     in popNIotasFromSeq pElse (length returns) `bindResult` \(mergeIotas, sAfter) ->
            let merges = zip mergeIotas returns
                baseFacts = vGetProofs base
                visible = nubOrd (concatMap proofIotas baseFacts ++ Map.elems (vVisibleVars base) ++ mergeIotas)
                toMerged proof =
                    foldl
                        (\p (m, (thenRet, _)) -> maybe p id (substituteProofTerm (ATerm thenRet) (ATerm m) p))
                        proof
                        merges
                candidates =
                    filter
                        (\p -> p `notElem` baseFacts && all (`elem` visible) (proofIotas p))
                        (nubOrd (map toMerged (vGetProofs pThen)))
                elseEqualities = [FApp eqProof [ATerm m, ATerm elseRet] | (m, (_, elseRet)) <- merges]
                elseContext = vProofContextWith pElse elseEqualities
                keptFromThen = [candidate | (candidate, True) <- zip candidates (Engine.entailsAll candidates elseContext)]
                -- The output contract of the function, about the merged return value: it is checked once the paths are joined,
                -- so a path does not have to state it for the join to keep it when both entail it
                returned = foldl (\s (m, _) -> vInsertVar s "return" m []) base merges
                wanted = [proof | not (null merges), variableProof <- markedProofs outputsMarker s0, Ok proof <- [varProofToIotaProof variableProof returned]]
                extras = take maxJoinCandidates (nubOrd [c | c <- wanted, c `notElem` baseFacts, c `notElem` candidates, all (`elem` visible) (proofIotas c)])
                thenContext = vProofContextWith pThen [FApp eqProof [ATerm m, ATerm thenRet] | (m, (thenRet, _)) <- merges]
                keptExtras = [c | (c, True, True) <- zip3 extras (Engine.entailsAll extras thenContext) (Engine.entailsAll extras elseContext)]
                kept = keptFromThen ++ keptExtras
                based = vSetIotaSeq base (vGetIotaSeq sAfter)
                withReturn = foldl (\s (m, _) -> vSetReturn s m []) based merges
             in Ok (vInsertProofs withReturn kept)

-- Runs a branch in a child scope that starts with the branch condition assumed. Unlike a
-- plain block there is no EndBlock, so the returned state still has the child scope and
-- everything the branch proved in it. The result is only used to read what the branch
-- established; it is never continued from.
valBranch :: VState -> [IotaProof] -> [Statement] -> Result VState String
valBranch state@(VState scope iotaCtx proofCtx iotaseq ruleCtx) assumptions stmts =
    valBlock (withFacts state assumptions (VState (VScopeState empty assumptions (Continuations stmts) (Just scope)) iotaCtx proofCtx iotaseq ruleCtx))

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
negateRel Eq = Just NotEq
negateRel NotEq = Just Eq

containsReturn :: [Statement] -> Bool
containsReturn = any returns
  where
    returns (Return _) = True
    returns (Block stmts) = containsReturn stmts
    returns (If _ thenStmts elseStmts) = containsReturn thenStmts || containsReturn elseStmts
    returns (While _ _ _ body) = containsReturn body
    returns _ = False

-- Variables assigned anywhere in the statements, including nested blocks
assignedVars :: [Statement] -> [Variable]
assignedVars = nubOrd . concatMap assigned
  where
    assigned (Assign var _) = [var]
    assigned (Block stmts) = assignedVars stmts
    assigned (If _ thenStmts elseStmts) = assignedVars thenStmts ++ assignedVars elseStmts
    assigned (While _ _ _ body) = assignedVars body
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
-- A branch whose facts contradict each other cannot run, so the join is the other branch: the facts are
-- taken from the branch that can run. (Otherwise they come from the first branch and must hold in the second.)
vacuous :: VState -> Bool
vacuous state = Engine.entails zeroBelowZero (vProofContext state)
  where
    zeroBelowZero = FApp (CTerm (builtinFunct (Rel Lt))) [CTerm (VInt 0), CTerm (VInt 0)]

joinBranches :: VState -> [Variable] -> VState -> VState -> Result VState String
joinBranches s0 vars sThen sElse
    | vacuous sThen && not (vacuous sElse) = joinBranchesFrom s0 vars sElse (vSetIotaSeq sThen (vGetIotaSeq sElse))
    | otherwise = joinBranchesFrom s0 vars sThen sElse

joinBranchesFrom :: VState -> [Variable] -> VState -> VState -> Result VState String
joinBranchesFrom s0 vars sThen sElse =
    case popNIotasFromSeq sElse (length vars) of
        Error e -> Error e
        Ok (mergeIotas, sAfter) ->
            case (traverseResult (finalIota sThen) vars, traverseResult (finalIota sElse) vars) of
                (Ok thenIotas, Ok elseIotas) ->
                    let merges = zip3 vars mergeIotas (zip thenIotas elseIotas)
                        s0Facts = vGetProofs s0
                        visible =
                            nubOrd (concatMap proofIotas s0Facts ++ Map.elems (vVisibleVars s0) ++ mergeIotas)
                        toMerged proof =
                            foldl
                                (\p (_, m, (thenIota, _)) -> maybe p id (substituteProofTerm (ATerm thenIota) (ATerm m) p))
                                proof
                                merges
                        candidates =
                            filter
                                (\p -> p `notElem` s0Facts && all (`elem` visible) (proofIotas p))
                                (nubOrd (map toMerged (vGetProofs sThen)))
                        elseEqualities = [FApp eqProof [ATerm m, ATerm elseIota] | (_, m, (_, elseIota)) <- merges]
                        elseContext = vProofContextWith sElse elseEqualities
                        keptFromThen = [candidate | (candidate, True) <- zip candidates (Engine.entailsAll candidates elseContext)]
                        base = vSetIotaSeq s0 (vGetIotaSeq sAfter)
                        -- Facts the join was not handed by the then-branch, that both branches may still establish; each is kept
                        -- only if both branches entail it, so they only have to be worth trying
                        joined = foldl (\s (var, m, _) -> vInsertVar s var m []) base merges
                        oldIotas = [(oldIota, m) | (var, m, _) <- merges, Just oldIota <- [vLookupVar s0 var]]
                        toMergedElse proof =
                            foldl
                                (\p (_, m, (_, elseIota)) -> maybe p id (substituteProofTerm (ATerm elseIota) (ATerm m) p))
                                proof
                                merges
                        wanted = [proof | variableProof <- loopEndProofs s0 ++ upcomingProofs s0 ++ upcomingOutputs s0, Ok proof <- [varProofToIotaProof variableProof joined]]
                        carried =
                            [ proof'
                            | proof <- s0Facts
                            , let proof' = foldl (\p (oldIota, m) -> maybe p id (substituteProofTerm (ATerm oldIota) (ATerm m) p)) proof oldIotas
                            , proof' /= proof
                            ]
                        extras =
                            take maxJoinCandidates $
                                nubOrd
                                    [ candidate
                                    | candidate <- wanted ++ carried ++ map toMergedElse (vGetProofs sElse)
                                    , candidate `notElem` s0Facts
                                    , candidate `notElem` candidates
                                    , all (`elem` visible) (proofIotas candidate)
                                    ]
                        thenContext = vProofContextWith sThen [FApp eqProof [ATerm m, ATerm thenIota] | (_, m, (thenIota, _)) <- merges]
                        keptExtras = [candidate | (candidate, True, True) <- zip3 extras (Engine.entailsDirect extras thenContext) (Engine.entailsDirect extras elseContext)]
                        kept = keptFromThen ++ keptExtras
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

-- What the join of an `if` tries to keep, besides what the branches state: the proofs the program is about to need.
-- The statements still to run in the block and in the blocks around it assert some (`affirm`, the invariant of a
-- loop that follows), and the end of a loop body asserts the invariant and that the variant got smaller. A join that
-- keeps a fact like that spares the program from stating it again in each branch.
upcomingProofs :: VState -> [VariableProof]
upcomingProofs (VState scope _ _ _ ruleCtx) = go scope
  where
    go (VScopeState _ _ (Continuations rest) parent) = concatMap proofsOf rest ++ maybe [] go parent
    proofsOf (ValidationStatement stmt) = assertedProofs ruleCtx [stmt]
    proofsOf (While _ invariant _ _) = assertedProofs ruleCtx invariant
    proofsOf (LoopEnd invariant decrease) = assertedProofs ruleCtx (invariant ++ decrease)
    proofsOf _ = []

-- The proofs that stating the statements asserts, with a variable they define replaced by its definition. A rewrite
-- asserts what it needs to hold where it is used.
assertedProofs :: RuleContext -> [ValidationStatement] -> [VariableProof]
assertedProofs rules stmts = [substituteVars definitions proof | proof <- concatMap asserted stmts]
  where
    definitions = Map.fromList [(var, exprToProof expr) | AssignProofVar var expr <- stmts]
    asserted (ProofAssert proof) = [proof]
    asserted (Rewrite rule) = rewriteNeeds rules rule
    asserted _ = []

-- What a rewrite needs to hold where it is applied: the relation a check asks about, and the input contract of a rule
rewriteNeeds :: RuleContext -> RwRule -> [VariableProof]
rewriteNeeds _ (CheckRel proof) = [proof]
rewriteNeeds _ (CheckGtZero proof) = [FApp (CTerm (builtinFunct (Rel Gt))) [proof, CTerm (VInt 0)]]
rewriteNeeds rules (UserRewrite name args) =
    case Map.lookup name rules of
        Just (AxiomRule vars inputs _) -> instantiate vars inputs
        Just (ProofRule vars inputs _) -> instantiate vars inputs
        Nothing -> []
  where
    instantiate vars inputs
        | length vars == length args = [substituteVars (Map.fromList (zip vars args)) proof | ProofAssert proof <- inputs]
        | otherwise = []
rewriteNeeds _ _ = []

substituteVars :: Map.Map Variable VariableProof -> VariableProof -> VariableProof
substituteVars replacements = replace
  where
    replace (ATerm var) = fromMaybe (ATerm var) (Map.lookup var replacements)
    replace (FApp funct args) = FApp (replace funct) (map replace args)
    replace (Forall index guards body) = Forall index (map replace guards) (replace body)
    replace proof = proof

-- Statements the join of an `if` may try to keep, carried in the rule context under a name no program can write, since
-- the state of a block has nowhere else to carry them:
--   * the end of the body of the loop being validated: the invariant and the variant check;
--   * the output contract of the function being validated, which is checked after the body and so after any join.
loopEndMarker :: Variable
loopEndMarker = "$loop end"

outputsMarker :: Variable
outputsMarker = "$outputs"

withMarked :: Variable -> [ValidationStatement] -> VState -> VState
withMarked marker stmts state@(VState scope iotaCtx proofCtx iotaseq ruleCtx) =
    keepCache state (VState scope iotaCtx proofCtx iotaseq (Map.insert marker (AxiomRule [] stmts []) ruleCtx))

markedProofs :: Variable -> VState -> [VariableProof]
markedProofs marker (VState _ _ _ _ ruleCtx) =
    case Map.lookup marker ruleCtx of
        Just (AxiomRule _ stmts _) -> assertedProofs ruleCtx stmts
        _ -> []

withLoopEnd :: [ValidationStatement] -> VState -> VState
withLoopEnd = withMarked loopEndMarker

loopEndProofs :: VState -> [VariableProof]
loopEndProofs = markedProofs loopEndMarker

withOutputs :: [ValidationStatement] -> VState -> VState
withOutputs = withMarked outputsMarker

-- The output contract, about the value of the `return` that follows, if the statements still to run have one
upcomingOutputs :: VState -> [VariableProof]
upcomingOutputs state@(VState scope _ _ _ _) =
    case returned scope of
        Just expr -> map (replaceReturn (exprToProof expr)) (markedProofs outputsMarker state)
        Nothing -> []
  where
    returned (VScopeState _ _ (Continuations rest) parent) =
        case [expr | Return expr <- rest] of
            expr : _ -> Just expr
            [] -> parent >>= returned
    replaceReturn value (ATerm "return") = value
    replaceReturn value (FApp funct args) = FApp (replaceReturn value funct) (map (replaceReturn value) args)
    replaceReturn value (Forall index guards body) = Forall index (map (replaceReturn value) guards) (replaceReturn value body)
    replaceReturn _ proof = proof

maxJoinCandidates :: Int
maxJoinCandidates = 40

traverseResult :: (a -> Result b String) -> [a] -> Result [b] String
traverseResult = flatResultMap

-- Validates a loop by its invariant, without unrolling it.
--
-- 1. The loop has to say how it ends, see loopTermination.
-- 2. The invariant must hold before the first iteration.
-- 3. Every outer variable the body assigns is rebound to a fresh value with no facts, so
--    nothing about its earlier values is assumed. Facts about other values stay true because
--    values are immutable.
-- 4. Assuming the invariant and the condition, the body must re-establish the invariant, and the
--    variant (if the loop has one) must be at least 0 at the start and smaller at the end.
-- 5. After the loop, the invariant holds and the condition does not.
--
-- A body that contains `return` is validated as paths, see valReturningWhile.
valWhileStatement :: VState -> Expression -> [ValidationStatement] -> Maybe Termination -> [Statement] -> Result VState String
valWhileStatement state cond invariant term body =
    vAdvanceStatement state `bindResult` \advanced ->
        loopTermination advanced term `bindResult` \_ ->
            prefixError "Loop invariant does not hold on entry: " (rangeHint (validateUserRuleInputs advanced invariant)) `bindResult` \_ ->
                let loopVars = assignedOuterVars advanced body
                 in popNIotasFromSeq advanced (length loopVars) `bindResult` \(freshIotas, popped) ->
                        let havocked = foldl (\s (var, iota) -> vInsertVar s var iota []) popped (zip loopVars freshIotas)
                            inferred = inferInvariants advanced havocked loopVars cond invariant body
                            attempt extra = valLoopFrom havocked cond (invariant ++ extra) term body
                         in -- The inferred invariants were shown to be preserved. If the loop is refused because one of them is
                            -- not, which would be a surprise, the error should be about the program's own invariant instead
                            case attempt inferred of
                                Error e | namesInferred e inferred -> attempt []
                                result -> result

-- A for loop whose range is not known to end at or after its start does not hold its bounds on entry
rangeHint :: Result a String -> Result a String
rangeHint (Error e) | "(end of for" `isInfixOf` e = Error (e ++ " (the range has to be known to end at or after its start, as 0..n does with n >= 0)")
rangeHint result = result

-- Whether an error says that one of the invariants was not preserved
namesInferred :: String -> [ValidationStatement] -> Bool
namesInferred e inferred = or [e == "Loop invariant is not preserved: Could not prove: " ++ renderVarProof p | ProofAssert p <- inferred]

-- The rest of the validation of a loop, from the state where the variables its body assigns are unknown
valLoopFrom :: VState -> Expression -> [ValidationStatement] -> Maybe Termination -> [Statement] -> Result VState String
valLoopFrom havocked cond invariant term body =
    assumeValStmts havocked invariant `bindResult` \assumed ->
        valLoopCondition assumed cond `bindResult` \(condState, condIota) ->
            conditionAssumptions True cond condIota condState `bindResult` \bodyAssumptions ->
                if containsReturn body
                    then valReturningWhile assumed cond invariant term body bodyAssumptions
                    else
                        startIteration condState bodyAssumptions term `bindResult` \(iterState, decrease) ->
                            valBranch (withLoopEnd (invariant ++ decrease) iterState) bodyAssumptions body `bindResult` \bodyState ->
                                prefixError "Loop invariant is not preserved: " (validateUserRuleInputs bodyState invariant) `bindResult` \_ ->
                                    variantFailure "Loop variant does not shrink" decrease (validateUserRuleInputs bodyState decrease) `bindResult` \_ ->
                                        valLoopExit (vSetIotaSeq assumed (vGetIotaSeq bodyState)) cond

-- Invariants that a loop gets without the program writing them. The variables the body assigns start with
-- candidates, from what the facts say when the loop is entered:
--   * a variable that is a number there is at least and at most that number, the size of a list likewise, and
--     two of these differ by what they differed by;
--   * a variable (or the size of a list) that is not known to be a number is compared with the other variables
--     the loop does not assign, and the comparison is a candidate if the facts already entail it (i <= n when
--     i starts at 0 and n is size(a), size(out) = size(a) when out starts as a copy of a).
-- A candidate is kept only if the body establishes it again, assuming the candidates that are left, which is
-- repeated until none is dropped, so what is kept is an invariant: it holds on entry, and is preserved. A body
-- that does not validate infers nothing. For a body that returns, a candidate that is not preserved is found
-- from the error and dropped, one at a time.
inferInvariants :: VState -> VState -> [Variable] -> Expression -> [ValidationStatement] -> [Statement] -> [ValidationStatement]
inferInvariants entry havocked loopVars cond invariant body
    | null candidates = []
    | containsReturn body = dropByError maxDropRounds (map ProofAssert candidates)
    | otherwise = houdini maxInferenceRounds (map ProofAssert candidates)
  where
    context = vProofContext entry
    sizeOf term = FApp (CTerm (builtinFunct Size)) [term]
    relation rel lhs rhs = FApp (CTerm (builtinFunct (Rel rel))) [lhs, rhs]
    -- The terms of a variable that candidates are about, with the number they equal on entry if there is one
    -- (a variable that is not a known number or list can still have a size that is known: push(push([], a), b) has size 2)
    termsOf var (Just (VInt n)) _ = [(ATerm var, Just n)]
    termsOf var (Just (VList items)) _ = [(sizeOf (ATerm var), Just (fromIntegral (length items)))]
    termsOf _ (Just _) _ = []
    termsOf var Nothing size = [(ATerm var, Nothing), (sizeOf (ATerm var), size)]
    -- the first elements of a list, which a loop that only pushes (or sets elsewhere) leaves as they were
    elementsOf var (Just (VList items)) _ = [(element var k, Just n) | (k, VInt n) <- take maxInferenceElements (zip [0 ..] items)]
    elementsOf var Nothing size = [(element var k, Nothing) | Just n <- [size], k <- [0 .. min n (fromIntegral maxInferenceElements) - 1]]
    elementsOf _ _ _ = []
    element var k = FApp (CTerm (builtinFunct Get)) [ATerm var, CTerm (VInt k)]
    loopValues = Engine.constantValues [ATerm (fromMaybe (Iota var) (vLookupVar entry var)) | var <- loopVars] context
    loopSizes = [case value of Just (VInt n) -> Just n; _ -> Nothing | value <- Engine.constantValues [sizeOf (ATerm (fromMaybe (Iota var) (vLookupVar entry var))) | var <- loopVars] context]
    loopEntries = zip3 loopVars loopValues loopSizes
    -- (the numbers and sizes come first, so that the elements of the lists never push a counter out)
    loopTerms = take maxInferenceTerms (concat [termsOf var value size | (var, value, size) <- loopEntries] ++ concat [elementsOf var value size | (var, value, size) <- loopEntries])
    -- Variables the loop does not assign, that are not known to be a number or a list, and that the program wrote
    anchorVars = take maxInferenceAnchors [var | var <- Map.keys (vVisibleVars entry), var `notElem` loopVars, ' ' `notElem` var, take 1 var /= "$"]
    anchorValues = Engine.constantValues [ATerm (fromMaybe (Iota var) (vLookupVar entry var)) | var <- anchorVars] context
    anchors = concat [termsOf var Nothing Nothing | (var, Nothing) <- zip anchorVars anchorValues]
    isElement (FApp (CTerm funct) [ATerm _, CTerm (VInt _)]) = funct == builtinFunct Get
    isElement _ = False
    known = [(term, k) | (term, Just k) <- loopTerms, not (isElement term)]
    -- (an element that starts as a number is only bounded, and after the rest, since there can be many)
    elementBounds = concat [[relation GtEq term (CTerm (VInt k)), relation LtEq term (CTerm (VInt k))] | (term, Just k) <- loopTerms, isElement term]
    constantCandidates =
        concat [[relation GtEq term (CTerm (VInt k)), relation LtEq term (CTerm (VInt k))] | (term, k) <- known]
            ++ [ relation Eq t1 (if k1 == k2 then t2 else FApp (CTerm (builtinFunct Plus)) [t2, CTerm (VInt (k1 - k2))])
               | (i, (t1, k1)) <- zip [0 :: Int ..] known
               , (j, (t2, k2)) <- zip [0 ..] known
               , i < j
               ]
    comparisons = [relation rel term anchor | (term, _) <- loopTerms, (anchor, _) <- anchors, rel <- [Eq, LtEq, GtEq]]
    -- a sum of two terms that is a variable the loop does not assign, plus the number one of them starts at: s + i = n
    sums =
        [ relation Eq (FApp (CTerm (builtinFunct Plus)) [t1, t2]) (if offset == 0 then anchor else FApp (CTerm (builtinFunct Plus)) [anchor, CTerm (VInt offset)])
        | (i, (t1, k1)) <- zip [0 :: Int ..] loopTerms
        , (j, (t2, k2)) <- zip [0 ..] loopTerms
        , i < j
        , isNothing k1 || isNothing k2
        , let offset = fromMaybe 0 k1 + fromMaybe 0 k2
        , (anchor, _) <- anchors
        ]
    converted = [(c, goal) | c <- comparisons ++ sums, Ok goal <- [varProofToIotaProof c entry]]
    entailedAt goals = [c | ((c, _), True) <- zip goals (Engine.entailsDirect (map snd goals) context)]
    entailedBasic = entailedAt converted
    -- a term that starts at a variable the loop does not assign, next to a term that starts at a number: i = lo, size(out) = 0
    -- gives i = size(out) + lo, which holds as long as both grow by the same amount (slice of a buffer from lo)
    differences =
        [ relation Eq t (FApp (CTerm (builtinFunct Plus)) [t2, if k == 0 then anchor else FApp (CTerm (builtinFunct Plus)) [anchor, CTerm (VInt (negate k))]])
        | FApp rel [t, anchor] <- entailedBasic
        , rel == CTerm (builtinFunct (Rel Eq))
        , t `elem` unknownTerms
        , (t2, k) <- known
        , t2 /= t
        ]
    unknownTerms = [term | (term, Nothing) <- loopTerms]
    convertedDifferences = [(c, goal) | c <- differences, Ok goal <- [varProofToIotaProof c entry]]
    entailed = entailedBasic ++ entailedAt convertedDifferences
    -- sums of terms that start at numbers, last so that they never push out the distances and comparisons
    knownSums =
        [ relation Eq (FApp (CTerm (builtinFunct Plus)) [t1, t2]) (CTerm (VInt (k1 + k2)))
        | (i, (t1, k1)) <- zip [0 :: Int ..] known
        , (j, (t2, k2)) <- zip [0 ..] known
        , i < j
        ]
    candidates = take maxInferenceCandidates (constantCandidates ++ entailed ++ knownSums ++ elementBounds)
    houdini rounds survivors
        | null survivors || rounds <= 0 = []
        | otherwise = case iterationEnd survivors of
            Nothing -> []
            Just bodyState ->
                let kept = [c | c <- survivors, isOk (validateUserRuleInputs bodyState [c])]
                 in if length kept == length survivors then survivors else houdini (rounds - 1) kept
    iterationEnd survivors =
        case assumeValStmts havocked (invariant ++ survivors) of
            Ok assumed -> case valLoopCondition assumed cond of
                Ok (condState, condIota) -> case conditionAssumptions True cond condIota condState of
                    Ok bodyAssumptions -> case valBranch (withLoopEnd (invariant ++ survivors) condState) bodyAssumptions body of
                        Ok bodyState -> Just bodyState
                        Error _ -> Nothing
                    Error _ -> Nothing
                Error _ -> Nothing
            Error _ -> Nothing
    dropByError rounds survivors
        | null survivors || rounds <= 0 = []
        | otherwise = case returningBodyPath havocked cond (invariant ++ survivors) body of
            Ok _ -> survivors
            Error e -> case [c | c@(ProofAssert p) <- survivors, e == "Loop invariant is not preserved: Could not prove: " ++ renderVarProof p] of
                c : _ -> dropByError (rounds - 1) (filter (/= c) survivors)
                [] -> []
    isOk (Ok _) = True
    isOk (Error _) = False

-- The path through the body of a loop that returns, to the end of an iteration, where the invariant is checked
returningBodyPath :: VState -> Expression -> [ValidationStatement] -> [Statement] -> Result VState String
returningBodyPath havocked cond invariant body =
    assumeValStmts havocked invariant `bindResult` \assumed ->
        valLoopCondition assumed cond `bindResult` \(condState, condIota) ->
            conditionAssumptions True cond condIota condState `bindResult` \bodyAssumptions ->
                valPath (vSetContinuations condState emptyContinuations) bodyAssumptions (body ++ [LoopEnd invariant []])

maxInferenceRounds :: Int
maxInferenceRounds = 4

maxDropRounds :: Int
maxDropRounds = 12

maxInferenceTerms :: Int
maxInferenceTerms = 8

-- The first elements of a list that are looked at
maxInferenceElements :: Int
maxInferenceElements = 3

maxInferenceAnchors :: Int
maxInferenceAnchors = 12

maxInferenceCandidates :: Int
maxInferenceCandidates = 32

-- A loop has to say how it ends. One that may not end is code that may not terminate, which a function
-- has to be declared ~ to contain.
loopTermination :: VState -> Maybe Termination -> Result () String
loopTermination _ Nothing = Error "Loop must say how it ends: add `shrinks <expression>` before its body, or `~`"
loopTermination state (Just MayDiverge) = noteDivergence state "a loop is declared ~"
loopTermination _ _ = Ok ()

-- The variant of a loop or function is an integer that has to be at least 0 where it starts, and smaller
-- each time round. Its value at the start is kept in a variable that has a name no program can write, and
-- the statements below check the value later on against it.
--
-- `shrinks e` is resolved by the type checker. An integer variant (Counting) has to be at least 0 and smaller. An enum or
-- struct (Parts) needs no bound and is smaller when it is a part of the earlier value.
variantStatements :: Variable -> Expression -> [ValidationStatement]
variantStatements name variant = [AssignProofVar name variant]

-- The expression of a clause that has a variant
variantOf :: Maybe Termination -> Maybe Expression
variantOf (Just (Counting variant)) = Just variant
variantOf (Just (Parts variant)) = Just variant
variantOf _ = Nothing

boundedBelow :: Variable -> Termination -> Expression -> [ValidationStatement]
boundedBelow name (Counting _) variant = variantStatements name variant ++ [ProofAssert (FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm name, CTerm (VInt 0)])]
boundedBelow name _ variant = variantStatements name variant

smallerThan :: Variable -> Variable -> Termination -> Expression -> [ValidationStatement]
smallerThan name earlier (Counting _) variant = variantStatements name variant ++ [ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm name, ATerm earlier])]
smallerThan name earlier _ variant = variantStatements name variant ++ [ProofAssert (FApp (CTerm (builtinFunct Within)) [ATerm name, ATerm earlier])]

-- Says which variant it was that could not be shown to be fine
variantFailure :: String -> [ValidationStatement] -> Result a String -> Result a String
variantFailure _ _ (Ok a) = Ok a
variantFailure what (AssignProofVar _ variant : _) (Error e) = Error (what ++ ": " ++ renderVarProof (exprToProof variant))
variantFailure what _ (Error e) = Error (what ++ ": " ++ e)

-- The names are made from the next iota, which no other loop in the program has
variantName :: VState -> Variable
variantName state = "variant " ++ case vGetIotaSeq state of
    Iota name : _ -> name
    [] -> ""

-- The state at the start of an iteration, where the invariant and the condition hold. For a loop with a
-- variant, that must be at least 0, and the state keeps its value. Also the statements that check at the
-- end of the iteration that it is smaller.
startIteration :: VState -> [IotaProof] -> Maybe Termination -> Result (VState, [ValidationStatement]) String
startIteration condState bodyAssumptions (Just clause)
    | Just variant <- variantOf (Just clause) =
    let name = variantName condState
        bounded = boundedBelow name clause variant
     in variantFailure "Loop variant is not bounded below" bounded (validateUserRuleInputs (vInsertProofs condState bodyAssumptions) bounded) `bindResult` \_ ->
            assumeValStmts condState (variantStatements name variant) `bindResult` \iterState ->
                Ok (iterState, smallerThan (name ++ " after") name clause variant)
startIteration condState _ _ = Ok (condState, [])

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
valReturningWhile :: VState -> Expression -> [ValidationStatement] -> Maybe Termination -> [Statement] -> [IotaProof] -> Result VState String
valReturningWhile assumed cond invariant term body bodyAssumptions =
    valLoopCondition assumed cond `bindResult` \(condState, _) ->
        startIteration condState bodyAssumptions term `bindResult` \(iterState, decrease) ->
            valPath (vSetContinuations iterState emptyContinuations) bodyAssumptions (body ++ [LoopEnd invariant decrease]) `bindResult` \pBody ->
                valLoopExit (vSetIotaSeq assumed (vGetIotaSeq pBody)) cond `bindResult` \exitState ->
                    valBlock exitState `bindResult` \pExit ->
                        joinReturnPaths assumed pBody pExit

-- The end of a loop body: the invariant must hold again, and the variant must be smaller. The path then
-- stops, as control goes back to the loop condition.
valLoopEnd :: VState -> [ValidationStatement] -> [ValidationStatement] -> Result VState String
valLoopEnd state invariant decrease =
    vAdvanceStatement state `bindResult` \advanced ->
        prefixError "Loop invariant is not preserved: " (validateUserRuleInputs advanced invariant) `bindResult` \_ ->
            variantFailure "Loop variant does not shrink" decrease (validateUserRuleInputs advanced decrease) `bindResult` \_ ->
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
                        proofContext = vProofContext state'
                     in if Engine.entails iotaProof proofContext
                            then Ok (vInsertProofs state' [iotaProof])
                            else doTrace4 ("Had vars: " ++ show (vGetVars state')) (doTrace4 ("Had proofs: " ++ show proofs) (Error $ "Could not prove: " ++ renderVarProof varproof))
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
    prepareFunctionValidationState state args inputValStmts (Just MayDiverge) stmts

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
    let oldContext = vProofContext state
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
    | any proofHasForall actualArgs = Error $ "Rewrite rule " ++ name ++ " cannot take a forall as an argument"
    | otherwise =
        let bindings = Map.fromList (zip formals actualArgs)
            instInputs = map (substituteValidationStatement bindings) inputValStmts
            instOutputs = map (substituteValidationStatement bindings) outputValStmts
         in case validateUserRuleInputs state instInputs of
                Error e -> Error $ "Rewrite rule " ++ name ++ " input validation failed: " ++ e
                Ok _ ->
                    case assumeValStmts state instOutputs of
                        Error e -> Error $ "Rewrite rule " ++ name ++ " output instantiation failed: " ++ e
                        Ok stateWithOutputs -> Ok stateWithOutputs

applyProofRule :: VState -> Variable -> [Variable] -> [ValidationStatement] -> [VariableProof] -> [VariableProof] -> Result VState String
applyProofRule state name formals inputValStmts exportedProofs actualArgs
    | length formals /= length actualArgs =
        Error $ "Rewrite rule " ++ name ++ " expected " ++ show (length formals) ++ " arguments, got " ++ show (length actualArgs)
    | any proofHasForall actualArgs = Error $ "Rewrite rule " ++ name ++ " cannot take a forall as an argument"
    | otherwise =
        let bindings = Map.fromList (zip formals actualArgs)
            instInputs = map (substituteValidationStatement bindings) inputValStmts
            instOutputs = map (substituteVariableProof bindings) exportedProofs
         in case validateUserRuleInputs state instInputs of
                Error e -> Error $ "Rewrite rule " ++ name ++ " input validation failed: " ++ e
                Ok _ ->
                    case flatResultMap (`varProofToIotaProof` state) instOutputs of
                        Error e -> Error $ "Rewrite rule " ++ name ++ " output instantiation failed: " ++ e
                        Ok iotaProofs -> Ok (vInsertProofs state iotaProofs)

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
substituteVariableProof _ bvar@BVar{} = bvar
substituteVariableProof bindings (Forall index guards body) =
    Forall index (map (substituteVariableProof bindings) guards) (substituteVariableProof bindings body)
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
-- A forall cannot be an expression: applyUserRule and applyProofRule reject forall arguments
proofToExpression (BVar index) = Var index
proofToExpression Forall{} = error "proofToExpression: forall is not an expression"
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
            case evalFunctCallWithContext fval valCtx argVals of
                Ok (val, valCtx') -> Ok (val, State scope valCtx')
                Error e -> Error e
        Ok (_, []) -> Error "Function expression must produce a value"
        Error e -> Error e

-- State -> iota of result -> expression -> Result (updated state, proofs about result iota) String
valExpression :: VState -> Iota -> Expression -> Result (VState, [IotaProof]) String
valExpression state iota (Val val) = valExpressionValue state iota val
valExpression state iota (Var var) = valExpressionVar state iota var
valExpression state iota (F fnexpr argexprs) = valExpressionFunction state iota fnexpr argexprs

valExpressionValue :: VState -> Iota -> Value -> Result (VState, [IotaProof]) String
valExpressionValue state iota val =
    let functValResult = validateValue state val
        r = mapResult (\validatedVal -> (state, [FApp eqProof [ATerm iota, CTerm validatedVal]])) functValResult
     in doTrace3 (show r) r

valExpressionVar :: VState -> Iota -> Variable -> Result (VState, [IotaProof]) String
valExpressionVar state iota var =
    case vLookupVar state var of
        Nothing -> Error $ "Undefined variable: " ++ var ++ " (a function must be defined before the functions that call it)"
        Just oiota ->
            let iotaEq = FApp eqProof [ATerm iota, ATerm oiota]
                reverseIotaEq = reverseEqProof iotaEq
                refledEqProofs = reflProofsByProofs (vGetProofs state) [iotaEq, reverseIotaEq]
             in Ok (state, iotaEq : reverseIotaEq : refledEqProofs)

valExpressionFunction :: VState -> Iota -> Expression -> [Expression] -> Result (VState, [IotaProof]) String
valExpressionFunction state iota fnexpr argexprs =
    case valFunctExprHelper state fnexpr argexprs iota of
        Ok (nextState, flatInputProofs, functProofs, argIotas, nestedCallProofs) ->
            case varProofToIotaProof (exprToProof (F fnexpr argexprs)) nextState of
                Ok fnProof ->
                    let nonEvalProof = FApp eqProof [ATerm iota, fnProof]
                        -- Only the direct equalities between an argument's fresh iota and another
                        -- iota are kept: the reflected copies of every other fact would bloat the context.
                        -- The exception is an argument that is a literal, when the callee's output proofs
                        -- mention it: set(a, i, 20) leaves get(return, i) = x, and x is 20.
                        outputIotas = concatMap proofIotas functProofs
                        -- A call nested in an argument, such as get(a, i) in push(out, get(a, i)), has
                        -- arguments of its own, and their links keep its result tied to the caller's variables.
                        nestedCallIotas = concatMap proofIotas (filter (not . isIotaEquality) flatInputProofs)
                        linkedIotas = argIotas ++ nestedCallIotas
                        argLinks = filter (\p -> isArgLink linkedIotas p || isLiteralArgLink outputIotas linkedIotas p || isCallDefinition argIotas p) flatInputProofs
                     in -- The links tie each argument's fresh iota to the caller's variable, which output
                        -- contracts that mention the arguments (size(return) = size(list) + 1) need
                        Ok (nextState, nonEvalProof : functProofs ++ nubOrd (argLinks ++ nestedCallProofs))
                Error e -> Error e
        Error e -> Error e

isTrivialEq :: IotaProof -> Bool
isTrivialEq (FApp funct [lhs, rhs]) = funct == eqProof && lhs == rhs
isTrivialEq _ = False

-- What an argument that is itself a call is equal to: t0 = (get(a, i) + 1) for the argument t0 of
-- push(out, get(a, i) + 1), which the callee's output proofs about t0 need
isCallDefinition :: [Iota] -> IotaProof -> Bool
isCallDefinition argIotas (FApp funct [ATerm lhs, FApp _ _]) = funct == eqProof && lhs `elem` argIotas
isCallDefinition _ _ = False

-- An equality between two iotas
isIotaEquality :: IotaProof -> Bool
isIotaEquality (FApp funct [ATerm _, ATerm _]) = funct == eqProof
isIotaEquality _ = False

-- An equality between an argument's fresh iota and another iota
isArgLink :: [Iota] -> IotaProof -> Bool
isArgLink argIotas (FApp funct [ATerm lhs, ATerm rhs]) = funct == eqProof && (lhs `elem` argIotas || rhs `elem` argIotas)
isArgLink _ _ = False

-- An equality between an argument's fresh iota and a constant, for an argument that the callee's
-- output proofs mention
isLiteralArgLink :: [Iota] -> [Iota] -> IotaProof -> Bool
isLiteralArgLink outputIotas argIotas (FApp funct [ATerm lhs, CTerm _]) =
    funct == eqProof && lhs `elem` argIotas && lhs `elem` outputIotas
isLiteralArgLink _ _ _ = False

validateValue :: VState -> Value -> Result Value String
validateValue state val = case val of
    VFunct args inputValStmts outputValStmts body _ ->
        mapResult
            (VFunct args inputValStmts outputValStmts body)
            (valFunctDef state args inputValStmts outputValStmts body)
    _ -> Ok val

valFunctDef :: VState -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> FunctBody -> Result [VariableProof] String
valFunctDef state args inputValStmts outputValStmts (NativeFunct _ term stmts) =
    case prepareFunctionValidationState state args inputValStmts term stmts of
            Ok preparedState ->
                let fnValState = withOutputs outputValStmts preparedState
                    valResult =
                        doTrace4
                            ("valFunctDef: Validating body: " ++ show (vGetContinuations fnValState))
                            (doTrace4 ("Preval fn body: Vars: " ++ show (vGetVars fnValState) ++ " Proofs: " ++ show (vGetProofs fnValState)) (valReturningBlock fnValState))
                 in case doTrace3 ("valFunctDef val result: " ++ show valResult) valResult of
                        Ok (bodyState, _) -> exportFunctOutputProofs bodyState args inputValStmts outputValStmts
                        Error e -> Error e
            Error e -> Error e
valFunctDef _ _ _ _ BuiltinFunct{} = Ok [] -- Builtin functions assumed to be validly defined

prepareFunctionValidationState :: VState -> [Variable] -> [ValidationStatement] -> Maybe Termination -> [Statement] -> Result VState String
prepareFunctionValidationState state args inputValStmts term stmts =
    let newState = markFunctionBody term (vSetScope state emptyVScopeState)
        wContinuations =
            doTrace4
                ("valFunctDef: Setting conts: " ++ show stmts)
                (vSetContinuations newState (Continuations stmts))
     in case popNIotasFromSeq wContinuations (length args) of
            Ok (niotas, newState') ->
                case zipMap args niotas (,) of
                    Ok (argIotas, _) ->
                        let preInputValState = vInsertVars newState' argIotas []
                         in assumeValStmts preInputValState inputValStmts `bindResult` startFunctionVariant term
                    Error e -> Error e
            Error e -> Error e

-- A function body is validated in a scope with no parent, like the program, but a function defined
-- inside it is local and is not a global function, so the body's state is marked
functionBodyMarker :: Variable
functionBodyMarker = "$body"

-- Present in the state of the body of a function that is guaranteed to terminate, so that the body may not
-- have code that is not, see noteDivergence
terminatesMarker :: Variable
terminatesMarker = "$terminates"

markFunctionBody :: Maybe Termination -> VState -> VState
markFunctionBody term state@(VState scope iotaCtx proofCtx iotaseq ruleCtx) =
    let marked = Map.insert functionBodyMarker (Iota functionBodyMarker) iotaCtx
        terminating = case term of
            Just MayDiverge -> Map.delete terminatesMarker marked
            _ -> Map.insert terminatesMarker (Iota terminatesMarker) marked
     in keepCache state (VState scope terminating proofCtx iotaseq ruleCtx)

-- What a recursive call compares its variant with: the variant's value when the function was called
entryVariantName :: Variable
entryVariantName = "variant at entry"

-- A function that says what shrinks has it at least 0 for any arguments that meet the input contract, and
-- keeps its value at the start
startFunctionVariant :: Maybe Termination -> VState -> Result VState String
startFunctionVariant (Just clause) state
    | Just variant <- variantOf (Just clause) =
    let bounded = boundedBelow entryVariantName clause variant
     in variantFailure "Function variant is not bounded below" bounded (validateUserRuleInputs state bounded) `bindResult` \_ ->
            assumeValStmts state (variantStatements entryVariantName variant)
startFunctionVariant _ state = Ok state

-- Whether the facts known at this point contradict each other, so that nothing here can run
unreachable :: VState -> Bool
unreachable state =
    let context = vProofContext state
        impossible = FApp (CTerm (builtinFunct (Rel Lt))) [CTerm (VInt 0), CTerm (VInt 0)]
     in Engine.entails (CTerm (VBool False)) context || Engine.entails impossible context

-- Code that may not terminate, in a function that was not declared ~, is an error if it can be
-- reached. The code is also not guaranteed to terminate in the program or a function that is declared
-- ~, but they do not mind.
noteDivergence :: VState -> String -> Result () String
noteDivergence state why =
    let VState _ iotaCtx _ _ _ = state
     in if Map.member terminatesMarker iotaCtx && not (unreachable state)
            then Error ("Not guaranteed to terminate: " ++ why ++ ". Declare the function ~ if that is intended")
            else Ok ()

-- What calling a function says about whether the caller ends. Calling a function declared ~ may
-- not end. A function calling itself needs a variant that is smaller for the call than for the call it is
-- in; without one it may not end.
callTermination :: VState -> [Variable] -> [Iota] -> [IotaProof] -> FunctBody -> Result () String
callTermination state varArgs argIotas argProofs (NativeFunct _ (Just term) _) = case term of
    MayDiverge -> noteDivergence state "it calls a function that is declared ~"
    Recursing Nothing -> noteDivergence state "it calls itself and does not say what shrinks"
    -- Inside the function itself this is not an error, as the function is declared ~ too. From a function defined inside it, it is.
    Recursing (Just MayDiverge) -> noteDivergence state "it calls a function that is declared ~"
    Recursing (Just clause) | Just variant <- variantOf (Just clause) ->
        case vLookupVar state entryVariantName of
            Just entry ->
                let smaller = smallerThan "variant of the call" entryVariantName clause variant
                 in mapResult (const ()) (variantFailure "Recursive call does not shrink the variant" smaller (valFunctInput state (varArgs ++ [entryVariantName]) (argIotas ++ [entry]) argProofs smaller))
            Nothing -> Error "A function can only call itself from its own body, not from a function defined inside it, unless both are declared ~"
    _ -> Ok ()
callTermination _ _ _ _ _ = Ok ()

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
                let allowedNames = nubOrd (args ++ ["return"] ++ concatMap valStmtDefinedVars inputValStmts ++ concatMap valStmtDefinedVars outputValStmts)
                 in let allowedBindings =
                            mapMaybe
                                (\var -> case vLookupVar outputState var of
                                    Just iota -> Just (var, iota)
                                    Nothing -> Nothing)
                                allowedNames
                    in let namedIotas = namedIotaMap allowedBindings
                       in let exportedProofs =
                                  nubOrd $
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
valFunctExprHelper :: VState -> Expression -> [Expression] -> Iota -> Result (VState, [IotaProof], [IotaProof], [Iota], [IotaProof]) String
valFunctExprHelper state@(VState scope iotaCtx proofCtx iotaseq ruleCtx) functionExpr argExprs resultIota =
    -- Get proofs from the function and arg expressions
    let exprsToVal = functionExpr : argExprs
     in let (freshIotas, iotaseq') = splitAt (length exprsToVal) iotaseq
         in let exprState = keepCache state (VState scope iotaCtx proofCtx iotaseq' ruleCtx)
             in case valExpressionSeq exprState exprsToVal freshIotas of
                    Error e -> Error e
                    Ok (exprValidatedState, inputProofGroups) ->
                        -- (the closure makes an input fact usable under the context's equalities, so the facts
                        -- are not rewritten through them here)
                        let flatInputProofs = concat inputProofGroups
                            -- (an argument that is a call has proved what its callee's output contract says about it)
                            nestedCallProofs = concat [group | (F _ _, group) <- zip argExprs (drop 1 inputProofGroups)]
                         in case freshIotas of
                                functionIota : inputIotas ->
                                    case valFunctCall exprValidatedState functionIota inputIotas flatInputProofs resultIota of
                                        Ok (callState, functionProofs) -> Ok (callState, flatInputProofs, functionProofs, freshIotas, nestedCallProofs)
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
evalFunctCall funct valCtx args = mapResult fst (evalFunctCallWithContext funct valCtx args)

-- Also returns the context after the call, which is the one place a call can change it: it carries
-- the fuel that is left (see fuelKey)
evalFunctCallWithContext :: Value -> Map Variable Value -> [Value] -> Result (Value, Map Variable Value) String
evalFunctCallWithContext (VFunct vars _ _ _ _) _ args
    | length vars /= length args = Error (arityMismatchMessage vars args)
evalFunctCallWithContext (VFunct _ _ _ (BuiltinFunct builtin) _) valCtx args =
    mapResult (\val -> (val, valCtx)) (evalBuiltinFunct builtin args)
evalFunctCallWithContext (VFunct vars _ _ (NativeFunct _ _ block) _) valCtx args =
    case zipMap vars args (,) of
        Ok (argVals, _) ->
            let varMap = foldl (\vm (var, val) -> insert var val vm) empty argVals
                scope = ScopeState varMap (Continuations block) (Just emptyScopeState)
             in case evalReturningBlock (State scope valCtx) of
                    Ok (State _ valCtx', Just val) -> Ok (val, valCtx')
                    Ok (_, Nothing) -> Error "Function did not return a value"
                    Error e -> Error e
        Error e -> Error e
evalFunctCallWithContext _ _ _ = Error "Object being called must be a function"

arityMismatchMessage :: [Variable] -> [a] -> String
arityMismatchMessage formals actuals =
    "Function expected " ++ show (length formals) ++ " arguments, got " ++ show (length actuals)


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
        Ok fnVal@(VFunct varArgs inputValStmts _ body exportedProofs) ->
            case valFunctInput state varArgs iiotas iproofs inputValStmts of
                Error e -> Error $ "Funct input validation failed: " ++ e
                Ok fnValState ->
                    callTermination (vInsertProofs state iproofs) varArgs iiotas iproofs body `bindResult` \_ ->
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
             in case evalFunctCall fnVal (Map.insert fuelKey (VInt validationFuel) (iotaMapToConcreteMap iotaCtx proofCtx)) argVals of
                    Ok functResult -> FApp eqProof [ATerm retiota, CTerm functResult] : instantiatedProofs
                    Error _ -> instantiatedProofs
        Nothing -> instantiatedProofs

-- Exported proof variables are rebound to fresh caller-side iotas before the callee's
-- proof templates are converted back into concrete caller-visible proofs.
instantiateFunctOutputProofs :: VState -> [Variable] -> [Iota] -> Iota -> [VariableProof] -> Result (VState, [IotaProof]) String
instantiateFunctOutputProofs state _ _ _ [] = Ok (state, [])
instantiateFunctOutputProofs state varArgs argIotas returnIota exportedProofs =
    let exportedNames = nubOrd (concatMap proofVars exportedProofs)
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
                        withFacts
                            state
                            argProofs
                            ( VState
                                (VScopeState (Data.Map.fromList argIotasMap) (argProofs ++ vGetProofs state) (Continuations stmts) Nothing)
                                iotaCtx
                                proofCtx
                                iotaseq
                                ruleCtx
                            )
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
