{-# LANGUAGE PatternSynonyms #-}

module MirMono
    ( monomorphize
    , monomorphizeForValidation
    , monomorphizeProofCallsForValidation
    ) where

import Data.List (intercalate, nub)
import qualified Syntax as S
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Map.Strict (Map)

import Mir
import Pretty (renderType)
import Types (Arg (..), BuiltinFunct (Field), Name, Size (..), Type (..), pattern TList, pattern TBox, Variable, instanceName, mentionsParameter, substitute)

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
monomorphize = monoWith unspecifiedFunction completeErasedInstances

-- The copies a call decides, with the contracts and ghost statements
-- kept: what a validator is given, since it checks the copies by the
-- contracts the template declares (native code is given the copies
-- with them stripped, by monomorphize).
monomorphizeForValidation :: Program -> Program
monomorphizeForValidation = monoWith id completeInstances

monomorphizeProofCallsForValidation :: Program -> Either String Program
monomorphizeProofCallsForValidation original = do
    rejectProofCallCycles original
    close Map.empty original
  where
    templates = Map.filter (\fn -> not(null(fnTypeParams fn) && null(fnSizeParams fn))) (progFunctions original)
    close known working = do
        let mono = monomorphizeForValidation working
            context = mono{progFunctions = Map.union (progFunctions mono) templates}
        (mainFn, mainKeys) <- redirectProofCalls context (progMain context)
        converted <- traverse (redirectProofCalls context) (Map.elems(progFunctions mono))
        let demanded = nub(mainKeys ++ concatMap snd converted)
            freshKeys = filter (`Map.notMember` known) demanded
            rewritten = context{progMain=mainFn,progFunctions=Map.union (Map.fromList[(fnName fn,fn)|(fn,_)<-converted]) templates}
        if null freshKeys then Right rewritten else do
            let instances = build original freshKeys known
            if all (`Map.member` instances) freshKeys then Right () else Left "a proof call has no original declaration instance"
            close instances rewritten{progFunctions=Map.union (Map.fromList[(fnName fn,fn)|fn<-Map.elems instances]) (progFunctions rewritten)}

rejectProofCallCycles :: Program -> Either String ()
rejectProofCallCycles program = case [(name,target)| (name,edges)<-Map.toList graph,(target,unsafe)<-edges,unsafe,reachable Set.empty target name] of
    (name,_):_ -> Left("recursive proof declaration workload: "++name)
    [] -> Right()
  where
    graph=Map.fromList[(fnName fn,map(\target->(target,True))(dependencies fn)++runtimeEdges fn)|fn<-progMain program:Map.elems(progFunctions program)]
    reachable seen current goal
        | current==goal = True
        | Set.member current seen = False
        | otherwise = any (\(target,_)->reachable(Set.insert current seen)target goal) (Map.findWithDefault [] current graph)
    runtimeEdges caller=[(name,expansive caller target args dest)|BasicBlock _ (Call(Const(CFn name))args dest _)<-Map.elems(fnBlocks caller),Just target<-[Map.lookup name(progFunctions program)]]
    expansive caller target args dest
        | null(fnTypeParams target) = False
        | otherwise = any grows (fnTypeParams target)
      where
        explicit=take(length args-length(fnSizeParams target))args
        found=concat[match expected actual|(param,arg)<-zip(fnParams target)explicit,Just expected<-[localType<$>Map.lookup param(fnLocals target)],Just actual<-[argumentType caller arg]]++concat[match expected actual|Just expected<-[fnReturns target],Just actual<-[localType<$>Map.lookup dest(fnLocals caller)]]
        grows parameter=case nub[actual|(name,actual)<-found,name==parameter] of
            [actual] -> wrapped(fnTypeParams caller)False actual
            _ -> True
    argumentType caller (Copy local)=localType<$>Map.lookup local(fnLocals caller)
    argumentType caller (Move local)=localType<$>Map.lookup local(fnLocals caller)
    argumentType _ (Const(CInt _))=Just TInt
    argumentType _ (Const(CBool _))=Just TBool
    argumentType _ _=Nothing
    wrapped names deeper ty=case ty of
        TParam name -> deeper && name`elem`names
        TNamed _ args -> any(\arg->case arg of ArgType value->wrapped names True value;_->False)args
        TArrayOf value _ -> wrapped names True value
        TRef value -> wrapped names True value
        TMutRef value -> wrapped names True value
        TBox value -> wrapped names True value
        TAddr value -> wrapped names True value
        TBlock value -> wrapped names True value
        TUninit value -> wrapped names True value
        TFn args result -> any(wrapped names True)(result:args)
        TForall _ _ value -> wrapped names True value
        _ -> False
    dependencies fn =
        let spec0=fnSpec fn
            (inputs,inputEnv)=clauses(specEnv spec0)(specRequires spec0)
            (outputs,_)=clauses inputEnv(specEnsures spec0)
         in inputs++outputs++concat[fst(clauses(loopEnv loop)(loopInvariant loop))|loop<-Map.elems(specLoops spec0)]++concat[ghostRefs env ghost|BasicBlock ss _<-Map.elems(fnBlocks fn),Ghost env ghost<-ss]
    ghostRefs env (GhostValidation clause)=fst(clauses env[clause])
    ghostRefs env (GhostProof _ params ins outs body)=
        let scoped=foldr Map.delete env params
            (inputs,inputEnv)=clauses scoped ins
         in inputs++fst(clauses inputEnv outs)++fst(clauses inputEnv body)
    ghostRefs env (GhostAxiom _ params ins outs)=
        let (inputs,inputEnv)=clauses(foldr Map.delete env params)ins
         in inputs++fst(clauses inputEnv outs)
    ghostRefs _ _=[]
    clauses env []=([],env)
    clauses env (clause:rest)=
        let (refs,next)=case clause of
                S.ProofAssert proof -> (proofRefs env proof,env)
                S.Assume proof -> (proofRefs env proof,env)
                S.AssignProofVar name(S.Var source) -> ([],maybe(Map.delete name env)(\value->Map.insert name value env)(Map.lookup source env))
                S.AssignProofVar name(S.Val(S.VFnRef original)) | Map.member original(progFunctions program) -> ([],Map.insert name(Const(CFn original))env)
                S.AssignProofVar name expression -> (proofRefs env(S.exprToProof expression),Map.delete name env)
                S.Rewrite(S.CheckRel proof) -> (proofRefs env proof,env)
                S.Rewrite(S.UserRewrite _ arguments) -> (concatMap(proofRefs env)arguments,env)
                _ -> ([],env)
            (remaining,lastEnv)=clauses next rest
         in(refs++remaining,lastEnv)
    proofRefs env(S.Forall index guards body)=concatMap(proofRefs(Map.delete index env))(guards++[body])
    proofRefs env(S.FApp function arguments)=
        let callee=case function of
                S.ATerm name -> case Map.lookup name env of Just(Const(CFn original))->[original];_->[]
                S.CTerm(S.VFnRef original)->[original]
                _ -> proofRefs env function
         in callee++concatMap(proofRefs env)arguments
    proofRefs _ _=[]

redirectProofCalls :: Program -> Function -> Either String (Function,[Key])
redirectProofCalls program caller
    | not(null(fnTypeParams caller) && null(fnSizeParams caller)) = Right(caller,[])
    | otherwise = do
        (ins, inputEnv, k1) <- clauses (returnEnv(specEnv spec0)) (specRequires spec0)
        (outs, _, k2) <- clauses inputEnv (specEnsures spec0)
        loops <- traverse (\loop -> do
            (invariant,_,keys) <- clauses (loopEnv loop) (loopInvariant loop)
            Right(loop{loopInvariant=invariant},keys)) (specLoops spec0)
        blocks <- traverse block (fnBlocks caller)
        let spec1=spec0{specRequires=ins,specEnsures=outs,specLoops=Map.map fst loops}
        Right(caller{fnSpec=spec1,fnBlocks=Map.map fst blocks},k1++k2++concatMap snd(Map.elems loops)++concatMap snd(Map.elems blocks))
  where
    spec0=fnSpec caller
    returnEnv env = case (fnReturns caller,Map.lookup(Local 0)(fnLocals caller)) of
        (Just result,Just local) | localType local==result -> Map.insertWith (\_ original->original) "return" (Copy(Local 0)) env
        _ -> env
    clauses env []=Right([],env,[])
    clauses env (clause:rest)=do
        (converted,next,keys) <- validation env clause
        (tailClauses,lastEnv,more) <- clauses next rest
        Right(converted:tailClauses,lastEnv,keys++more)
    validation env (S.ProofAssert proof)=do
        (converted,keys) <- rewriteProof env [] proof
        Right(S.ProofAssert converted,env,keys)
    validation env (S.Assume proof)=do
        (converted,keys) <- rewriteProof env [] proof
        Right(S.Assume converted,env,keys)
    validation env clause@(S.AssignProofVar name (S.Var source)) =
        Right(clause,maybe (Map.delete name env) (\value->Map.insert name value env) (Map.lookup source env),[])
    validation env clause@(S.AssignProofVar name (S.Val(S.VFnRef source))) | Map.member source(progFunctions program) = Right(clause,Map.insert name(Const(CFn source))env,[])
    validation env clause@(S.AssignProofVar name (S.Val(S.VInt value))) = Right(clause,Map.insert name(Const(CInt value))env,[])
    validation env clause@(S.AssignProofVar name (S.Val(S.VBool value))) = Right(clause,Map.insert name(Const(CBool value))env,[])
    validation env clause@(S.AssignProofVar name _) = Right(clause,Map.delete name env,[])
    validation env (S.Rewrite (S.CheckRel proof))=do
        (converted,keys)<-rewriteProof env [] proof
        Right(S.Rewrite(S.CheckRel converted),env,keys)
    validation env (S.Rewrite (S.UserRewrite name args))=do
        changed<-traverse(rewriteProof env [])args
        Right(S.Rewrite(S.UserRewrite name(map fst changed)),env,concatMap snd changed)
    validation env other=Right(other,env,[])
    block (BasicBlock statements term)=do
        converted<-traverse statement statements
        Right(BasicBlock(map fst converted)term,concatMap snd converted)
    statement (Ghost env (GhostValidation clause))=do
        (converted,_,keys)<-validation env clause
        Right(Ghost env(GhostValidation converted),keys)
    statement (Ghost env (GhostProof name params ins outs body))=do
        let scoped=foldr Map.delete env params
        (inputs,inputEnv,k1)<-clauses scoped ins
        (outputs,_,k2)<-clauses inputEnv outs
        (proofBody,_,k3)<-clauses inputEnv body
        Right(Ghost env(GhostProof name params inputs outputs proofBody),k1++k2++k3)
    statement (Ghost env (GhostAxiom name params ins outs))=do
        let scoped=foldr Map.delete env params
        (inputs,inputEnv,k1)<-clauses scoped ins
        (outputs,_,k2)<-clauses inputEnv outs
        Right(Ghost env(GhostAxiom name params inputs outputs),k1++k2)
    statement other=Right(other,[])
    rewriteProof env bound (S.Forall index guards body)=do
        changed<-traverse(rewriteProof (Map.delete index env)(index:bound))(guards++[body])
        Right(S.Forall index(map fst(init changed))(fst(last changed)),concatMap snd changed)
    rewriteProof env bound proof@(S.FApp function args)=do
        changed<-traverse(rewriteProof env bound)args
        case target env function of
            Just name | Just fn<-Map.lookup name(progFunctions program), not(null(fnTypeParams fn)&&null(fnSizeParams fn)) -> do
                key@(_,tys,sizes)<-maybe (Left("proof call cannot select its declared type/size key: "++name)) Right (proofKey env bound fn args)
                Right(S.FApp(S.CTerm(S.VFnRef(fnInstanceName name tys sizes)))(map fst changed),key:concatMap snd changed)
            _ -> do
                (head',keys)<-rewriteProof env bound function
                Right(S.FApp head'(map fst changed),keys++concatMap snd changed)
    rewriteProof _ _ proof=Right(proof,[])
    target env (S.ATerm name)=case Map.lookup name env of Just(Const(CFn original))->Just original;_->Nothing
    target _ (S.CTerm(S.VFnRef name))=Just name
    target _ _=Nothing
    proofKey env bound fn args=do
        if null(fnSizeParams fn) && length args==length(fnParams fn) then Just() else Nothing
        actual<-traverse(proofType env bound)args
        declared<-traverse(\local->localType<$>Map.lookup local(fnLocals fn))(fnParams fn)
        let found=concat(zipWith match declared actual)
        types<-traverse(\parameter->case nub[value|(name,value)<-found,name==parameter] of [value]|not(mentionsParameter value)->Just value;_->Nothing)(fnTypeParams fn)
        if and(zipWith (\expected value->unlent(substitute [] (zip(fnTypeParams fn)types) expected)==unlent value) declared actual) then Just(fnName fn,types,[]) else Nothing
    proofType env _ (S.ATerm name)=Map.lookup name env >>= operandType
    proofType _ bound (S.BVar name)|name`elem`bound=Just TInt
    proofType _ _ (S.CTerm(S.VInt _))=Just TInt
    proofType _ _ (S.CTerm(S.VBool _))=Just TBool
    proofType env bound (S.FApp (S.CTerm (S.VFunct _ _ _ (S.BuiltinFunct (Field _ field)) _)) [object])=do
        owner<-proofType env bound object
        case unlent owner of
            TNamed name args | Just (params,fields)<-Map.lookup name(progGenerics program) -> do
                declared<-lookup field fields
                Just(substitute [(param,size)|(param,ArgSize size)<-zip params args] [(param,ty)|(param,ArgType ty)<-zip params args] declared)
            TNamed name [] | Just (StructDecl fields)<-Map.lookup name(progTypes program) -> lookup field fields
            _ -> Nothing
    proofType env bound (S.FApp function args)=do
        name<-target env function
        fn<-Map.lookup name(progFunctions program)
        if length args/=length(fnParams fn) then Nothing else Just()
        if null(fnTypeParams fn)&&null(fnSizeParams fn) then do
            actual<-traverse(proofType env bound)args
            expected<-traverse(\local->localType<$>Map.lookup local(fnLocals fn))(fnParams fn)
            if actual==expected then fnReturns fn else Nothing
        else do
            (_,types,sizes)<-proofKey env bound fn args
            fnReturns(instantiate fn types sizes)
    proofType _ _ _=Nothing
    unlent (TRef ty)=ty
    unlent (TMutRef ty)=ty
    unlent ty=ty
    operandType (Copy local)=localType<$>Map.lookup local(fnLocals caller)
    operandType (Move local)=localType<$>Map.lookup local(fnLocals caller)
    operandType (Const(CInt _))=Just TInt
    operandType (Const(CBool _))=Just TBool
    operandType _=Nothing

-- A function with its contracts and ghost statements stripped, as
-- native code is given a copy; the lifetimes of its references stay, which
-- native lowering frees by
unspecifiedFunction :: Function -> Function
unspecifiedFunction f = f{fnSpec = emptySpec, fnBlocks = Map.map (\(BasicBlock stmts term) -> BasicBlock [s | s <- stmts, not (isGhost s)] term) (fnBlocks f)}
  where
    isGhost s = case s of
        Ghost _ (GhostLifetime _ _) -> False
        Ghost _ _ -> True
        _ -> False

-- (native code is given its structs without their permissions, which the
-- validator reads)
monoWith :: (Function -> Function) -> (Program -> Program) -> Program -> Program
monoWith finish completeTypes program
    | not (any generic (Map.elems (progFunctions program))) = program
    | otherwise =
        withInstances
            program
                { progFunctions = Map.fromList [(fnName f, f) | f <- map finish (plain' ++ Map.elems instances)]
                , progMain = finish main'
                }
  where
    -- (the structs with sizes that the copies mention are declared, and those that only a function with sizes mentioned, whose sizes
    -- were names, are not there any more)
    withInstances p =
        let complete = completeTypes p
         in complete{progTypes = Map.filterWithKey (\name _ -> not (symbolic name)) (progTypes complete)}
    symbolic name = maybe False mentionsParameter (Map.lookup name (namedTypesByName program))
    -- (what the validator was told names functions that are not there any more; nothing after it needs it)
    unspecified f = f{fnSpec = emptySpec, fnBlocks = Map.map (\(BasicBlock stmts term) -> BasicBlock [s | s <- stmts, not (isGhost s)] term) (fnBlocks f)}
    isGhost s = case s of
        Ghost _ (GhostLifetime _ _) -> False
        Ghost _ _ -> True
        _ -> False
    generic f = not (null (fnSizeParams f) && null (fnTypeParams f))
    (main', mainNeeds) = redirect program (progMain program)
    redirected = [redirect program f | f <- Map.elems (progFunctions program), not (generic f)]
    plain' = map fst redirected
    -- (the drop of a struct with types is made for each instance of the struct that the program has, and named for it, `<Vec<Int> as Drop>::drop`:
    -- native code calls it where a value of that instance is freed, which no call in the program says)
    instances = Map.mapWithKey dropName (withDrops (build program (mainNeeds ++ concatMap snd redirected) Map.empty) (4 :: Int))
    withDrops done k =
        let p = withInstances program{progFunctions = Map.fromList [(fnName f, f) | f <- plain' ++ Map.elems done], progMain = main'}
            keys = [key | n <- Map.keys (progTypes p), not (symbolic n), Just key <- [dropKey n], Map.notMember key done]
         in if null keys || k <= 0 then done else withDrops (build program keys done) (k - 1)
    dropKey n = do
        base <- Just (takeWhile (/= '<') n)
        let name = "<" ++ base ++ " as Drop>::drop"
        f <- Map.lookup name (progFunctions program)
        self <- case fnParams f of
            p : _ -> Just p
            [] -> Nothing
        selfTy <- localType <$> Map.lookup self (fnLocals f)
        let bindings = match selfTy (namedTypeOf program n)
        tys <- mapM (`lookup` bindings) (fnTypeParams f)
        Just (name, tys, [])
    dropName (name, _, _) f
        | isDropFunction name, self : _ <- fnParams f, Just (TNamed base args) <- localType <$> Map.lookup self (fnLocals f) = f{fnName = "<" ++ instanceName base args ++ " as Drop>::drop"}
        | otherwise = f

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

fnInstanceName :: Name -> [Type] -> [Integer] -> Name
fnInstanceName name tys sizes = name ++ "<" ++ intercalate ", " (map renderType tys ++ map show sizes) ++ ">"

-- The function with its type and size parameters replaced by the types and the sizes
instantiate :: Function -> [Type] -> [Integer] -> Function
instantiate fn tys sizes =
    fn
        { fnName = fnInstanceName (fnName fn) tys sizes
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
    -- (the name of a struct with sizes names them, from the types this function has)
    named name = Map.findWithDefault name name renames
      where
        renames = Map.fromList [(instanceName b a, case types (TNamed b a) of TNamed b' a' -> instanceName b' a'; _ -> instanceName b a) | ty <- map localType (Map.elems (fnLocals fn)) ++ maybe [] (: []) (fnReturns fn), (b, a) <- namedSubs ty]
        namedSubs ty = case ty of
            TNamed b a -> (b, a) : concat [namedSubs u | ArgType u <- a]
            TList u -> namedSubs u
            TArrayOf u _ -> namedSubs u
            TBox u -> namedSubs u
            TAddr u -> namedSubs u
            TBlock u -> namedSubs u
            TUninit u -> namedSubs u
            TRef u -> namedSubs u
            TFn as r -> concatMap namedSubs (r : as)
            TForall _ _ u -> namedSubs u
            _ -> []
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
        AssignRef root steps rv -> AssignRef root (map refStep steps) (rvalue rv)
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
        CopyOf o -> CopyOf (operand o)
        Borrow root steps mutable -> Borrow root (map refStep steps) mutable
        Deref o -> Deref (operand o)
        TakeField l name field -> TakeField l (named name) field
    refStep (RefField name field) = RefField (named name) field
    refStep (RefIndex o) = RefIndex (operand o)
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
                (Call (Const (CFn (fnInstanceName callee tys sizes))) explicit dest next, [(callee, tys, sizes)])
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
    firstKnown cs = case [t | c <- cs, Just t <- [constantType c]] of
        t : _ -> t
        [] -> TInt
    constantType c = case c of
        CInt _ -> Just TInt
        CBool _ -> Just TBool
        -- (an empty array has the shape, and the element type that nothing decides is an Int, as it is everywhere)
        CArray cs -> Just (TArrayOf (firstKnown cs) (SizeConst (toInteger (length cs))))
        CData name _ -> Just (TNamed name [])
        _ -> Nothing

-- What the type parameters of a type are, given the type it stands for
match :: Type -> Type -> [(Variable, Type)]
match pat actual = case (pat, actual) of
    (TParam name, a) -> [(name, a)]
    (TBox p, TBox a) -> match p a
    (TAddr p, TAddr a) -> match p a
    (TUninit p, TUninit a) -> match p a
    (TBlock p, TBlock a) -> match p a
    (TRef p, a) -> match p a
    (p, TRef a) -> match p a
    (TMutRef p, a) -> match p a
    (p, TMutRef a) -> match p a
    (TArrayOf p _, TArrayOf a _) -> match p a
    (TNamed bp ps, TNamed ba as)
        | bp == ba, length ps == length as -> concat (zipWith matchArg ps as)
    (TFn ps p, TFn as a) -> concat (zipWith match (p : ps) (a : as))
    _ -> []

-- What the type parameters are, given what an instance of a struct is given
matchArg :: Arg -> Arg -> [(Variable, Type)]
matchArg (ArgType p) (ArgType a) = match p a
matchArg _ _ = []

-- The named types a program's functions and types mention, by rendered name
namedTypesByName :: Program -> Map Name Type
namedTypesByName program = Map.fromList [(instanceName b a, TNamed b a) | ty <- allTypes, (b, a) <- subs ty]
  where
    allTypes = [localType d | f <- progMain program : Map.elems (progFunctions program), d <- Map.elems (fnLocals f)] ++ [ty | f <- progMain program : Map.elems (progFunctions program), Just ty <- [fnReturns f]] ++ [ty | StructDecl fields <- Map.elems (progTypes program), (_, ty) <- fields] ++ [ty | EnumDecl variants <- Map.elems (progTypes program), (_, fields) <- variants, (_, ty) <- fields] ++ [ty | (_, fields) <- Map.elems (progGenerics program), (_, ty) <- fields]
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
        TForall _ _ u -> subs u
        _ -> []

namedTypeOf :: Program -> Name -> Type
namedTypeOf program name = Map.findWithDefault (TNamed name []) name (namedTypesByName program)
