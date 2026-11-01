module Link
    ( linkPrograms
    , pruneProgram
    ) where

import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Mir as M
import Modules (ModuleId, renderModuleId)
import qualified TersusTypes
import TersusTypes (Name, Proof (..), Type (..), ValidationStatement (..), VariableProof, Value (..), instanceOf)
import Utils (Result (..), bindResult)

linkPrograms :: [(ModuleId, M.Program)] -> Result M.Program String
linkPrograms [] = Error "link error: no modules to link"
linkPrograms units =
    mergeAll "type" [(modu, name, decl) | (modu, program) <- normalized, (name, decl) <- Map.toList (M.progTypes program)] `bindResult` \types ->
        mergeFunctions normalized `bindResult` \functions ->
            mergeAll "generic struct" [(modu, name, decl) | (modu, program) <- normalized, (name, decl) <- Map.toList (M.progGenerics program)] `bindResult` \generics ->
                mergeAll "invariant" [(modu, name, decl) | (modu, program) <- normalized, (name, decl) <- Map.toList (M.progInvariants program)] `bindResult` \invariants ->
                    Ok (M.completeInstances (M.Program types functions linkedMain generics invariants))
  where
    normalized = [(modu, normalizeExterns program) | (modu, program) <- units]
    rootMain = M.progMain (snd (last normalized))
    depGhosts = concatMap unitGhosts (init normalized)
    linkedMain = prependGhosts depGhosts rootMain

unitGhosts :: (ModuleId, M.Program) -> [M.Statement]
unitGhosts (_, program) = [stmt | (_, block) <- Map.toAscList (M.fnBlocks (M.progMain program)), stmt@(M.Ghost _ _) <- M.blockStatements block]

prependGhosts :: [M.Statement] -> M.Function -> M.Function
prependGhosts [] fn = fn
prependGhosts ghosts fn = fn{M.fnBlocks = Map.adjust prepend (M.BlockId 0) (M.fnBlocks fn)}
  where
    prepend (M.BasicBlock stmts term) = M.BasicBlock (ghosts ++ stmts) term

mergeAll :: (Eq a) => String -> [(ModuleId, Name, a)] -> Result (Map.Map Name a) String
mergeAll what entries = go Map.empty Map.empty entries
  where
    go values _ [] = Ok values
    go values origins ((modu, name, value) : rest) = case Map.lookup name values of
        Nothing -> go (Map.insert name value values) (Map.insert name modu origins) rest
        Just existing
            | existing == value -> go values origins rest
            | otherwise -> Error ("link error: " ++ what ++ " " ++ name ++ " is defined by both module " ++ renderModuleId (origins Map.! name) ++ " and module " ++ renderModuleId modu ++ " with different definitions")

mergeFunctions :: [(ModuleId, M.Program)] -> Result (Map.Map Name M.Function) String
mergeFunctions units = go Map.empty Map.empty [(modu, fn) | (modu, program) <- units, fn <- Map.elems (M.progFunctions program)]
  where
    go functions _ [] = Ok functions
    go functions origins ((modu, fn) : rest) = case Map.lookup (M.fnName fn) functions of
        Nothing -> go (Map.insert (M.fnName fn) fn functions) (Map.insert (M.fnName fn) modu origins) rest
        Just existing
            | sameFunction existing fn -> go functions origins rest
            | otherwise -> Error ("link error: function " ++ displayName (M.fnName fn) ++ " is defined by both module " ++ renderModuleId (origins Map.! M.fnName fn) ++ " and module " ++ renderModuleId modu ++ " with different definitions")
    displayName name = case externLocal name of
        Just local -> "extern fn " ++ local
        Nothing -> name
    sameFunction a b
        | externLocal (M.fnName a) /= Nothing && externLocal (M.fnName b) /= Nothing = externSignature a == externSignature b
        | otherwise = comparable a == comparable b
    comparable fn = fn{M.fnSpec = (M.fnSpec fn){M.specEnv = Map.empty, M.specLoops = Map.map (\loop -> loop{M.loopEnv = Map.empty}) (M.specLoops (M.fnSpec fn))}}
    externSignature fn =
        ( [maybe "" (show . M.localType) (Map.lookup param (M.fnLocals fn)) | param <- M.fnParams fn]
        , M.fnReturns fn
        , M.fnSizeParams fn
        , M.fnTypeParams fn
        , M.specRequires (M.fnSpec fn)
        , M.specEnsures (M.fnSpec fn)
        , M.specTermination (M.fnSpec fn)
        , M.specMutParams (M.fnSpec fn)
        , M.specFrom (M.fnSpec fn)
        )

externLocal :: Name -> Maybe Name
externLocal name
    | "extern " `isPrefixOf` name = Just (afterLastDollar (drop 7 name))
    | otherwise = Nothing
  where
    afterLastDollar text = reverse (takeWhile (/= '$') (reverse text))

normalizeExterns :: M.Program -> M.Program
normalizeExterns program
    | Map.null renames = program
    | otherwise = renameFunctions renames program
  where
    renames = Map.fromList [(name, "extern " ++ local) | name <- Map.keys (M.progFunctions program), Just local <- [externLocal name], "extern " ++ local /= name]

renameFunctions :: Map.Map Name Name -> M.Program -> M.Program
renameFunctions renames program =
    program
        { M.progFunctions = Map.fromList [(rename name, renameFunction fn) | (name, fn) <- Map.toList (M.progFunctions program)]
        , M.progMain = renameFunction (M.progMain program)
        }
  where
    rename name = Map.findWithDefault name name renames
    renameFunction fn =
        fn
            { M.fnName = rename (M.fnName fn)
            , M.fnBlocks = Map.map renameBlock (M.fnBlocks fn)
            , M.fnSpec = (M.fnSpec fn){M.specEnv = Map.map renameOperand (M.specEnv (M.fnSpec fn)), M.specLoops = Map.map (\loop -> loop{M.loopEnv = Map.map renameOperand (M.loopEnv loop)}) (M.specLoops (M.fnSpec fn))}
            }
    renameBlock (M.BasicBlock stmts term) = M.BasicBlock (map renameStatement stmts) (renameTerminator term)
    renameStatement stmt = case stmt of
        M.Assign local rv -> M.Assign local (renameRvalue rv)
        M.Peek local rv -> M.Peek local (renameRvalue rv)
        M.AssignRef local steps rv -> M.AssignRef local (map renameStep steps) (renameRvalue rv)
        M.Ghost env ghost -> M.Ghost (Map.map renameOperand env) (renameGhost ghost)
        other -> other
    renameGhost ghost = case ghost of
        M.GhostFunction name source top -> M.GhostFunction (rename name) source top
        other -> other
    renameStep step = case step of
        M.RefIndex operand -> M.RefIndex (renameOperand operand)
        other -> other
    renameTerminator term = case term of
        M.Call callee args dest next -> M.Call (renameOperand callee) (map renameOperand args) dest next
        M.SwitchBool operand yes no -> M.SwitchBool (renameOperand operand) yes no
        other -> other
    renameRvalue rv = case rv of
        M.Use operand -> M.Use (renameOperand operand)
        M.BinaryOp op a b -> M.BinaryOp op (renameOperand a) (renameOperand b)
        M.ListOp op operands -> M.ListOp op (map renameOperand operands)
        M.MakeList operands -> M.MakeList (map renameOperand operands)
        M.MakeBox operand -> M.MakeBox (renameOperand operand)
        M.Unbox operand -> M.Unbox (renameOperand operand)
        M.Unsize operand -> M.Unsize (renameOperand operand)
        M.MakeData name fields -> M.MakeData name [(field, renameOperand operand) | (field, operand) <- fields]
        M.ReadField operand name field -> M.ReadField (renameOperand operand) name field
        M.IsVariant operand name -> M.IsVariant (renameOperand operand) name
        M.AsVariant operand name -> M.AsVariant (renameOperand operand) name
        M.CopyOf operand -> M.CopyOf (renameOperand operand)
        M.Borrow local steps mutable -> M.Borrow local (map renameStep steps) mutable
        M.Deref operand -> M.Deref (renameOperand operand)
        other -> other
    renameOperand operand = case operand of
        M.Const constant -> M.Const (renameConstant constant)
        other -> other
    renameConstant constant = case constant of
        M.CFn name -> M.CFn (rename name)
        M.CData name fields -> M.CData name [(field, renameConstant value) | (field, value) <- fields]
        M.CList values -> M.CList (map renameConstant values)
        M.CArray values -> M.CArray (map renameConstant values)
        other -> other

pruneProgram :: M.Program -> M.Program
pruneProgram program =
    let (keptFns, keptTypes) = fixpoint (functionRefs program (M.progMain program)) (typeRefsOfFunction program (M.progMain program))
     in program
            { M.progTypes = Map.filterWithKey (\name _ -> name `Set.member` keptTypes) (M.progTypes program)
            , M.progFunctions = Map.fromList [(name, scrubFunction keptFns fn) | (name, fn) <- Map.toList (M.progFunctions program), name `Set.member` keptFns]
            , M.progMain = scrubFunction keptFns (M.progMain program)
            , M.progInvariants = Map.filterWithKey (\name _ -> name `Set.member` keptTypes || any (\ty -> baseOf ty == name) (Set.toList keptTypes)) (M.progInvariants program)
            }
  where
    baseOf name = maybe name fst (instanceOf name)
    fixpoint fns types
        | fnsNext == fns && typesNext == types = (fns, types)
        | otherwise = fixpoint fnsNext typesNext
      where
        keptFnList = [fn | name <- Set.toList fns, Just fn <- [Map.lookup name (M.progFunctions program)]]
        fromFns = Set.unions (map (functionRefs program) keptFnList)
        fromTypes = Set.unions [implFunctions ty | ty <- Set.toList types]
        invariantRefs = Set.unions [Set.fromList (concatMap proofNames invariant) | name <- Set.toList types, Just invariant <- [Map.lookup name (M.progInvariants program)]]
        fnsNext = Set.union fns (Set.intersection (Map.keysSet (M.progFunctions program)) (Set.unions [fromFns, fromTypes, invariantRefs]))
        typesFromFns = Set.unions (map (typeRefsOfFunction program) keptFnList)
        typesFromTypes = Set.unions [declTypeRefs decl | name <- Set.toList types, Just decl <- [Map.lookup name (M.progTypes program)]]
        typesNext = Set.unions [types, typesFromFns, typesFromTypes]
    implFunctions ty =
        let dropFn = maybe Set.empty Set.singleton (M.dropFunction program ty)
            impls = Set.fromList [name | name <- Map.keys (M.progFunctions program), ("<" ++ ty ++ " as ") `isPrefixOf` name]
            baseImpls = Set.fromList [name | name <- Map.keys (M.progFunctions program), ("<" ++ baseOf ty ++ " as ") `isPrefixOf` name]
         in Set.unions [dropFn, impls, baseImpls]
    declTypeRefs decl = case decl of
        M.StructDecl fields -> Set.unions (map (typeNames . snd) fields)
        M.EnumDecl variants -> Set.unions [typeNames ty | (_, fields) <- variants, (_, ty) <- fields]

functionRefs :: M.Program -> M.Function -> Set.Set Name
functionRefs program fn =
    Set.intersection (Map.keysSet (M.progFunctions program)) $
        Set.fromList $
            concatMap statementRefs (concatMap M.blockStatements (Map.elems (M.fnBlocks fn)))
                ++ concatMap terminatorRefs (map M.blockTerminator (Map.elems (M.fnBlocks fn)))
                ++ concatMap proofNames (M.specRequires (M.fnSpec fn) ++ M.specEnsures (M.fnSpec fn))
                ++ concatMap (concatMap proofNames . M.loopInvariant) (Map.elems (M.specLoops (M.fnSpec fn)))
  where
    statementRefs stmt = case stmt of
        M.Assign _ rv -> rvalueRefs rv
        M.Peek _ rv -> rvalueRefs rv
        M.AssignRef _ steps rv -> concatMap stepRefs steps ++ rvalueRefs rv
        M.Ghost _ ghost -> ghostRefs ghost
        _ -> []
    ghostRefs ghost = case ghost of
        M.GhostValidation vs -> validationRefs vs
        M.GhostAxiom _ _ ins outs -> concatMap validationRefs (ins ++ outs)
        M.GhostProof _ _ ins outs body -> concatMap validationRefs (ins ++ outs ++ body)
        _ -> []
    validationRefs vs = case vs of
        ProofAssert proof -> proofTermNames proof
        Assume proof -> proofTermNames proof
        AssignProofVar _ expr -> exprRefs expr
        Rewrite rule -> ruleRefs rule
    exprRefs expr = case expr of
        TersusTypes.Var name -> [name]
        TersusTypes.F f args -> exprRefs f ++ concatMap exprRefs args
        TersusTypes.Val (VFnRef name) -> [name]
        _ -> []
    ruleRefs rule = case rule of
        TersusTypes.UserRewrite _ args -> concatMap proofTermNames args
        TersusTypes.Refl proof -> proofTermNames proof
        TersusTypes.CheckGtZero proof -> proofTermNames proof
        TersusTypes.CheckRel proof -> proofTermNames proof
        _ -> []
    terminatorRefs term = case term of
        M.Call callee args _ _ -> concatMap operandRefs (callee : args)
        M.SwitchBool operand _ _ -> operandRefs operand
        _ -> []
    stepRefs (M.RefIndex operand) = operandRefs operand
    stepRefs _ = []
    rvalueRefs rv = case rv of
        M.Use operand -> operandRefs operand
        M.BinaryOp _ a b -> operandRefs a ++ operandRefs b
        M.ListOp _ operands -> concatMap operandRefs operands
        M.MakeList operands -> concatMap operandRefs operands
        M.MakeBox operand -> operandRefs operand
        M.Unbox operand -> operandRefs operand
        M.Unsize operand -> operandRefs operand
        M.MakeData _ fields -> concatMap (operandRefs . snd) fields
        M.ReadField operand _ _ -> operandRefs operand
        M.IsVariant operand _ -> operandRefs operand
        M.AsVariant operand _ -> operandRefs operand
        M.CopyOf operand -> operandRefs operand
        M.Borrow _ steps _ -> concatMap stepRefs steps
        M.Deref operand -> operandRefs operand
        _ -> []
    operandRefs operand = case operand of
        M.Const constant -> constantRefs constant
        _ -> []
    constantRefs constant = case constant of
        M.CFn name -> [name]
        M.CData _ fields -> concatMap (constantRefs . snd) fields
        M.CList values -> concatMap constantRefs values
        M.CArray values -> concatMap constantRefs values
        _ -> []

proofNames :: ValidationStatement -> [Name]
proofNames vs = case vs of
    ProofAssert proof -> proofTermNames proof
    Assume proof -> proofTermNames proof
    _ -> []

proofTermNames :: VariableProof -> [Name]
proofTermNames proof = case proof of
    ATerm name -> [name]
    FApp fn args -> proofTermNames fn ++ concatMap proofTermNames args
    Forall _ guards body -> concatMap proofTermNames guards ++ proofTermNames body
    CTerm (VFnRef name) -> [name]
    _ -> []

typeRefsOfFunction :: M.Program -> M.Function -> Set.Set Name
typeRefsOfFunction program fn =
    Set.unions $
        [typeNames (M.localType decl) | decl <- Map.elems (M.fnLocals fn)]
            ++ [maybe Set.empty typeNames (M.fnReturns fn)]
            ++ [Set.fromList [owner | stmt <- concatMap M.blockStatements (Map.elems (M.fnBlocks fn)), name <- statementTypeNames stmt, owner <- ownerNames name]]
  where
    statementTypeNames stmt = case stmt of
        M.Assign _ rv -> rvalueNames rv
        M.Peek _ rv -> rvalueNames rv
        _ -> []
    rvalueNames rv = case rv of
        M.MakeData name _ -> [name]
        M.ReadField _ name _ -> [name]
        M.IsVariant _ name -> [name]
        M.AsVariant _ name -> [name]
        M.TakeField _ name _ -> [name]
        _ -> []
    ownerNames name
        | Map.member name (M.progTypes program) = [name]
        | otherwise = maybe [] pure (M.ownerOf program name)

typeNames :: Type -> Set.Set Name
typeNames ty = case ty of
    TNamed name -> Set.singleton name
    TVariant name -> Set.singleton name
    TList inner -> typeNames inner
    TArrayOf inner _ -> typeNames inner
    TBox inner -> typeNames inner
    TAddr inner -> typeNames inner
    TBlock inner -> typeNames inner
    TUninit inner -> typeNames inner
    TRef inner -> typeNames inner
    TMutRef inner -> typeNames inner
    TFn args ret -> Set.unions (map typeNames (ret : args))
    TForall _ _ inner -> typeNames inner
    _ -> Set.empty

scrubFunction :: Set.Set Name -> M.Function -> M.Function
scrubFunction kept fn =
    fn
        { M.fnBlocks = Map.map scrubBlock (M.fnBlocks fn)
        , M.fnSpec = (M.fnSpec fn){M.specEnv = scrubEnv (M.specEnv (M.fnSpec fn)), M.specLoops = Map.map (\loop -> loop{M.loopEnv = scrubEnv (M.loopEnv loop)}) (M.specLoops (M.fnSpec fn))}
        }
  where
    scrubEnv = Map.filter (\operand -> case operand of M.Const (M.CFn name) -> name `Set.member` kept; _ -> True)
    scrubBlock (M.BasicBlock stmts term) = M.BasicBlock (map scrubStmt (filter keepStmt stmts)) term
    keepStmt stmt = case stmt of
        M.Ghost _ (M.GhostFunction name _ _) -> name `Set.member` kept
        _ -> True
    scrubStmt stmt = case stmt of
        M.Ghost env ghost -> M.Ghost (scrubEnv env) ghost
        _ -> stmt
