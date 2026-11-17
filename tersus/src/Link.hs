{-# LANGUAGE PatternSynonyms #-}

module Link
    ( linkPrograms
    , linkWithLibraries
    , linkValidatedPrograms
    , pruneProgram
    , completeSpecEnvs
    ) where

import Data.List (isPrefixOf)
import Data.Maybe (isJust)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import PreludeSource (nativeStorageModules)
import qualified Mir as M
import PackageData (ModuleId (..), renderModuleId)
import MirCopies (groundType, isCopyName, makeCopiesWith)
import MirMono (namedTypesByName)
import qualified Syntax
import Syntax (Proof (..), ValidationStatement (..), VariableProof, Value (..))
import Types (Arg (..), Name, OwnershipFacts (..), Storage (..), Type (..), baseNameOf, instanceName)
import Utils (Result (..), bindResult)

-- Units are merged under the names their declarations were lowered with
-- (compiler-library units and the entry module keep bare names, the rest
-- are canonical). The same unit passed twice -- a compiler-library unit
-- selected by several modules of a package -- is deduplicated by unit
-- identity; a name defined by two different units with different
-- definitions is a duplicate-definition error, and only a definition
-- identical to the one already linked (a declaration an importing unit
-- carries seeded from the interface it was lowered against) merges.
linkPrograms :: [(ModuleId, M.Program)] -> Result M.Program String
linkPrograms = linkWithLibraries []

-- The compiler's library units linked ahead of the program's own: their functions with bounds are validated where the
-- program uses them (MirCopies.makeCopiesWith), every other unit's where they are defined
linkWithLibraries :: [(ModuleId, M.Program)] -> [(ModuleId, M.Program)] -> Result M.Program String
linkWithLibraries libraries own = linkWith (boundedOf libraries) True (libraries ++ own)

-- The units linked as a program that is validated and not owned or emitted itself (the native storage, all of it the
-- compiler's libraries): its types' facts are not made into copies no call names
linkValidatedPrograms :: [(ModuleId, M.Program)] -> Result M.Program String
linkValidatedPrograms units = linkWith (boundedOf units) False units

boundedOf :: [(ModuleId, M.Program)] -> Set.Set Name
boundedOf units = Set.fromList [name | (_, program) <- units, name <- Map.keys (M.progBounded program)]

linkWith :: Set.Set Name -> Bool -> [(ModuleId, M.Program)] -> Result M.Program String
linkWith _ _ [] = Error "link error: no modules to link"
linkWith library recording units = deduplicateUnits [(modu, normalizeExterns program) | (modu, program) <- units] `bindResult` linkNormalized library recording

linkNormalized :: Set.Set Name -> Bool -> [(ModuleId, M.Program)] -> Result M.Program String
linkNormalized library recording normalized =
    mergeAll "type" [(modu, name, decl) | (modu, program) <- normalized, (name, decl) <- Map.toList (M.progTypes program)] `bindResult` \types ->
        mergeFunctions functionEnv normalized `bindResult` \functions ->
            mergeAll "generic struct" [(modu, name, decl) | (modu, program) <- normalized, (name, decl) <- Map.toList (M.progGenerics program)] `bindResult` \generics ->
                mergeAll "invariant" [(modu, name, decl) | (modu, program) <- normalized, (name, decl) <- Map.toList (M.progInvariants program)] `bindResult` \invariants ->
                    mergeAll "function with bounds" [(modu, name, decl) | (modu, program) <- normalized, (name, decl) <- Map.toList (M.progBounded program)] `bindResult` \bounded ->
                        mergeAll "copy" [(modu, name, decl) | (modu, program) <- normalized, (name, decl) <- Map.toList (M.progInstances program)] `bindResult` \instances ->
                        mergeAll "provider" [(modu, role, provider) | (modu, program) <- normalized, (role, provider) <- Map.toList (M.progProtocols program)] `bindResult` \protocols ->
                        mergeOwnership normalized `bindResult` \ownership ->
                            -- (a copy the call cannot have is refused as the elaborator refuses a call)
                            let linked = M.completeInstances (M.Program types functions linkedMain generics invariants bounded instances protocols ownership)
                                -- (the facts' functions are made for the types the program keeps once the copies its calls
                                -- name are made, not for every instance a library declares)
                                kept p = Set.union (snd (reachable p)) (Map.keysSet (namedTypesByName (pruneProgram p)))
                                -- (a function a fact names can keep more types, whose facts' functions are made in turn)
                                withFacts owners = makeCopiesWith library (Just owners) linked `bindResult` \p ->
                                    if kept p `Set.isSubsetOf` owners then Ok p else withFacts (Set.union owners (kept p))
                                copied = makeCopiesWith library Nothing linked `bindResult` \plain ->
                                    if recording then withFacts (kept plain) else Ok plain
                             in case copied of
                                Error e -> Error ("Validation failed: " ++ e)
                                ok -> ok
  where
    functionEnv = Map.fromList [(name, M.Const (M.CFn name)) | (_, program) <- normalized, name <- Map.keys (M.progFunctions program)]
    rootMain = M.progMain (snd (last normalized))
    linkedMain = (completeFunctionEnvs functionEnv (prependGhosts (concatMap unitGhosts (init normalized)) rootMain)){M.fnSpec = M.fnSpec rootMain}

-- The units' checked ownership facts as one table: units with them agree on every type they share; a unit without them
-- (data written without its facts) makes the build's absent
mergeOwnership :: [(ModuleId, M.Program)] -> Result (Maybe (Map.Map Name OwnershipFacts)) String
mergeOwnership units = case mapM (M.progOwnership . snd) units of
    Nothing
        | any (isJust . M.progOwnership . snd) units -> Error "link error: some modules have checked ownership facts and others do not"
        | otherwise -> Ok Nothing
    Just tables -> mergeAll "ownership facts of a type" [(modu, name, facts) | ((modu, _), table) <- zip units tables, (name, facts) <- Map.toList table] `bindResult` (Ok . Just)

deduplicateUnits :: [(ModuleId, M.Program)] -> Result [(ModuleId, M.Program)] String
deduplicateUnits = go Map.empty []
  where
    go _ done [] = Ok (reverse done)
    go seen done (unit@(modu, program) : rest) = case Map.lookup modu seen of
        Nothing -> go (Map.insert modu program seen) (unit : done) rest
        Just existing
            | existing == program -> go seen done rest
            | otherwise -> Error ("link error: module " ++ renderModuleId modu ++ " has inconsistent units")

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

-- Linked functions need the complete program's ghost environment, not only the unit's.
completeSpecEnvs :: M.Program -> M.Program
completeSpecEnvs program = program
    { M.progFunctions = Map.map (completeFunctionEnvs functionEnv) (M.progFunctions program)
    , M.progMain = (completeFunctionEnvs functionEnv (M.progMain program)){M.fnSpec = M.fnSpec (M.progMain program)}
    }
  where
    functionEnv = Map.fromList [(name, M.Const (M.CFn name)) | name <- Map.keys (M.progFunctions program)]

completeFunctionEnvs :: M.Env -> M.Function -> M.Function
completeFunctionEnvs functionEnv fn = fn
    { M.fnSpec = completeSpec (M.fnSpec fn)
    , M.fnBlocks = Map.map completeBlock (M.fnBlocks fn)
    }
  where
    completeBlock (M.BasicBlock statements term) = M.BasicBlock (map completeStatement statements) term
    completeStatement (M.Ghost env ghost) = M.Ghost (completeEnv env) ghost
    completeStatement other = other
    completeSpec spec = spec{M.specEnv = completeEnv (M.specEnv spec), M.specLoops = Map.map (\loop -> loop{M.loopEnv = completeEnv (M.loopEnv loop)}) (M.specLoops spec)}
    completeEnv env = Map.union env functionEnv

mergeFunctions :: M.Env -> [(ModuleId, M.Program)] -> Result (Map.Map Name M.Function) String
mergeFunctions functionEnv units = go Map.empty Map.empty [(modu, completeFunctionEnvs functionEnv fn) | (modu, program) <- units, fn <- Map.elems (M.progFunctions program)]
  where
    go functions _ [] = Ok functions
    go functions origins ((modu, fn) : rest) = case Map.lookup (M.fnName fn) functions of
        Nothing -> go (Map.insert (M.fnName fn) fn functions) (Map.insert (M.fnName fn) modu origins) rest
        Just existing
            | sameFunction existing fn && compatibleOrigin (origins Map.! M.fnName fn) modu -> go functions origins rest
            | otherwise -> Error ("link error: function " ++ displayName (M.fnName fn) ++ " is defined by both module " ++ renderModuleId (origins Map.! M.fnName fn) ++ " and module " ++ renderModuleId modu ++ " with different definitions")
    displayName name = case externLocal name of
        Just local -> "extern fn " ++ local
        Nothing -> name
    sameFunction a b
        | externLocal (M.fnName a) /= Nothing && externLocal (M.fnName b) /= Nothing = externSignature a == externSignature b
        | otherwise = a == b
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

compatibleOrigin :: ModuleId -> ModuleId -> Bool
compatibleOrigin a b = not (private a || private b)
  where
    private (ModuleId "std" (Just name)) = name `elem` nativeStorageModules
    private _ = False

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
    let (keptFns, keptTypes) = reachable program
     in program
            { M.progTypes = Map.filterWithKey (\name _ -> name `Set.member` keptTypes) (M.progTypes program)
            , M.progFunctions = Map.fromList [(name, scrubFunction keptFns fn) | (name, fn) <- Map.toList (M.progFunctions program), name `Set.member` keptFns]
            , M.progMain = scrubFunction keptFns (M.progMain program)
            , M.progInvariants = Map.filterWithKey (\name _ -> name `Set.member` keptTypes || any (\ty -> baseNameOf ty == name) (Set.toList keptTypes)) (M.progInvariants program)
            }

-- The functions and the types the program's main reaches, through calls, its types' declarations and their checked facts
reachable :: M.Program -> (Set.Set Name, Set.Set Name)
reachable program = fixpoint (functionRefs program (M.progMain program)) (typeRefsOfFunction program (M.progMain program))
  where
    storage = M.progStorage program
    baseOf name = baseNameOf name
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
        -- (a Box of an array is a list of its elements in native code, MirLists)
        keptNamed = namedTypesByName program{M.progFunctions = Map.fromList [(M.fnName fn, fn) | fn <- keptFnList], M.progTypes = Map.filterWithKey (\name _ -> Set.member name types) (M.progTypes program), M.progGenerics = Map.empty}
        typesFromStorage = Set.fromList (concat [[storageList storage, instanceName (storageList storage) [ArgType e]] | TNamed b [ArgType (TArrayOf e _)] <- Map.elems keptNamed, b == storageBox storage])
        typesNext = Set.unions [types, typesFromFns, typesFromTypes, typesFromStorage]
    -- (a kept type keeps its impls, its base's impls that are not copies, and the functions its checked facts name: a copy
    -- of a base's impl for another instance is kept by what calls it, or by that instance's facts)
    implFunctions ty =
        let recorded = Set.fromList [f | Just facts <- [M.factsOf program ty], Just (_, f) <- [ownershipDrop facts, ownershipClone facts, ownershipDeref facts]]
            dropFn = maybe Set.empty Set.singleton (M.dropFunction program ty)
            impls = Set.fromList [name | name <- Map.keys (M.progFunctions program), ("<" ++ ty ++ " as ") `isPrefixOf` name]
            baseImpls = Set.fromList [name | name <- Map.keys (M.progFunctions program), ("<" ++ baseOf ty ++ " as ") `isPrefixOf` name, not (isCopyName name)]
         in Set.unions [recorded, dropFn, impls, baseImpls]
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
        Syntax.Var name -> [name]
        Syntax.F f args -> exprRefs f ++ concatMap exprRefs args
        Syntax.Val (VFnRef name) -> [name]
        _ -> []
    ruleRefs rule = case rule of
        Syntax.UserRewrite _ args -> concatMap proofTermNames args
        Syntax.Refl proof -> proofTermNames proof
        Syntax.CheckGtZero proof -> proofTermNames proof
        Syntax.CheckRel proof -> proofTermNames proof
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
        ++ [constantTypeNames]
  where
    -- (a list constant is a struct of the storage List once MirLists makes it, of the type the place it is put in says or,
    -- where nothing says it, its elements do (MirLists.materialize); no local may name it before)
    constantTypeNames = Set.fromList [n | (c, expected) <- constants, Just t <- [constantTypeIn expected c], n <- instanceNames t]
    storage = M.progStorage program
    localTy l = M.localType <$> Map.lookup l (M.fnLocals fn)
    constantTypeIn expected c = case (c, expected) of
        (M.CList _, Just ty@(TNamed b _)) | b == storageList storage, groundType ty -> Just ty
        _ -> M.constantType storage c
    constants = concat [concatMap statementConstants stmts ++ terminatorConstants term | M.BasicBlock stmts term <- Map.elems (M.fnBlocks fn)]
    statementConstants stmt = case stmt of
        M.Assign d rv -> rvalueConstants (localTy d) rv
        M.Peek d rv -> rvalueConstants (localTy d) rv
        _ -> []
    rvalueConstants destTy rv = case rv of
        M.Use (M.Const c) -> [(c, destTy)]
        M.ListOp op (M.Const c : rest)
            | op `elem` [M.Push, M.Set, M.Pop, M.UninitNew] -> (c, destTy) : others rest
            | op `elem` [M.First, M.Last, M.Get] -> (c, fmap (\t -> TNamed (storageList storage) [ArgType t]) destTy) : others rest
        M.MakeList os -> [(c, elementOf destTy) | M.Const c <- os]
        other -> others (M.operandsOfRvalue other)
    others os = [(c, Nothing) | M.Const c <- os]
    elementOf ty = case ty of
        Just (TNamed b [ArgType t]) | b == storageList storage -> Just t
        _ -> Nothing
    terminatorConstants term = case term of
        M.SwitchBool o _ _ -> others [o]
        M.Call (M.Const (M.CFn callee)) args _ _ | Just f <- Map.lookup callee (M.progFunctions program) -> [(c, M.localType <$> Map.lookup p (M.fnLocals f)) | (M.Const c, p) <- zip args (M.fnParams f)]
        M.Call callee args _ _ -> others (callee : args)
        _ -> []
    instanceNames ty = case ty of
        TNamed b a -> b : instanceName b a : concat [instanceNames u | ArgType u <- a]
        _ -> []
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

argNames :: Arg -> Set.Set Name
argNames (ArgType inner) = typeNames inner
argNames _ = Set.empty

typeNames :: Type -> Set.Set Name
typeNames ty = case ty of
    TNamed name args -> Set.singleton name <> foldMap argNames args
    TVariant name -> Set.singleton name
    TArrayOf inner _ -> typeNames inner
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
