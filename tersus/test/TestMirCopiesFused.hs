module TestMirCopiesFused (testMirCopiesFused) where

import Data.Char (chr)
import Data.Foldable (asum)
import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Environment (lookupEnv)

import ElaboratorTool (bootstrapLoader)
import LibPackage (libPackage)
import qualified Link
import qualified Mir as M
import MirCopiesOracle (coveredKey, makeCopiesWith)
import MirMoves (finishLowered)
import PackageCompile (compileModulesUsing, packageLinkInputs)
import PackageData (ModuleId (..), Snapshot (..), resolverFromFiles)
import qualified Syntax as S
import TestHarness (Test (..), TestResult, testAssertEq, testAssertTrue)
import TestMirCopiesFusedHarness
    ( compareBeforeWire, compareFused, fusedLink, fusedRequest, linkRequest, measureLink, oldLinkRequest
    , standaloneCopies
    )
import TestMirCopiesParity
    ( block, bounded, checkWideStatements, checkWitness, empty, function, growthRefusal
    , int, packSource, recursion, rootId, template, wideStatements, witnessSource
    )
import Types (Arg (..), Rel (..), Size (..), Type (..), instanceName)
import Utils (Result (..), bindResult, mapResult)

testMirCopiesFused :: Test
testMirCopiesFused = TestList "testMirCopiesFused"
    [ TestCase "real prefix and root: witness, lifted copy, and original tersuslib retention" $
        realCase True witnessSource checkWitness
    , TestCase "bound call gets its hidden size from the check witness and records that dispatch target" witnessOnlyHiddenOperand
    , TestCase "repeated bound calls keep one witness dispatch target and each hidden size" (witnessWithCalls 64)
    , TestCase "inline bound call closes the stub without an edge to an ordinary function reference" inlineDispatch
    , TestCase "lifted copy shadows outer type and size binders without blocking other substitutions" liftedBinderShadow
    , TestCase "real prefix and root: heterogeneous pack substitution preserves proofs" $
        realCase False packSource (const checkPack)
    , TestCase "fused merge requires Unicode name facts and uses them to complete nested instances" unicodeCompletion
    , TestCase "overwriting an aliased copy keeps coverage by final name" coveredAliasCollision
    , TestCase "wrapped tuple arity takes the inline Clone path despite an impl and check" tupleArityWrap
    , TestCase "check-contract companion overlay preserves local precedence and leaves ghosts alone" checkContractOverlay
    , TestCase "root environment sharing preserves local shadows, function aliases, and the entry binding" rootEnvironmentSharing
    , TestCase "first refusal follows lexicographic roots, then numeric blocks" orderedRefusal
    , TestCase "fused merge refusal order: wire, name profile, merge, then copies" refusalPrecedence
    , TestCase "standalone no-work does not force the library" noWork
    , TestCase "standalone work-bearing copies preserve runtime and proof data after finishLowered" standaloneWork
    ]

inspect :: Result a String -> (a -> TestResult) -> TestResult
inspect (Error e) _ = Just e
inspect (Ok value) check = check value

withResult :: Result a String -> (a -> IO TestResult) -> IO TestResult
withResult (Error e) _ = pure (Just e)
withResult (Ok value) check = check value

realUnits :: String -> Result [(ModuleId, M.Program)] String
realUnits source = compileModulesUsing bootstrapLoader libPackage snapshot `bindResult` \compiled ->
    packageLinkInputs compiled
  where
    entry = "app/main.tersus"
    files =
        [ ("app/package.tersus", "")
        , ("app/core/core.tersus", unlines
            [ "fn fusedPrefix(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return = x + 1; }] { affirm x >= 0; return x + 1; };"
            , "axiom fusedPrefixAxiom(x) [{ }] [{ affirm x = x; }];"
            , "trait FusedKeep { }; fn fusedUnused<T: FusedKeep>(x: T) -> T { return x; };"
            ])
        , (entry, "import app::core { fusedPrefix };\nprefixResult = fusedPrefix(7);\naffirm prefixResult >= 0;\n" ++ source)
        ]
    snapshot = Snapshot (resolverFromFiles files) entry False

realCase :: Bool -> String -> (Set.Set String -> M.Program -> TestResult) -> IO TestResult
realCase measure source check = withResult (realUnits source) $ \units -> do
    actual <- fusedLink units
    parity <- compareFused units
    beforeWire <- compareBeforeWire units
    let library = Set.fromList [n | (ModuleId pkg _, p) <- units, pkg `elem` ["tersuslib", "std"], n <- Map.keys (M.progBounded p)]
    case asum [parity, beforeWire, inspect actual (\p -> asum [checkPrefix units p, check library p])] of
        Nothing | measure -> do
            enabled <- lookupEnv "TERSUS_MEASURE_MIRCOPIES_FUSED"
            if enabled == Just "1" then measureLink units else pure Nothing
        result -> pure result

checkPrefix :: [(ModuleId, M.Program)] -> M.Program -> TestResult
checkPrefix units linked = case reverse units of
    (ModuleId "app" _, root) : _
        | [prefix] <- [p | (ModuleId "app" _, p) <- init units, any ("fusedPrefix" `isInfixOf`) (Map.keys (M.progFunctions p))]
        , [name] <- filter ("fusedPrefix" `isInfixOf`) (Map.keys (M.progFunctions prefix))
        , [unused] <- filter ("fusedUnused" `isInfixOf`) (Map.keys (M.progBounded prefix)) ->
            asum
                [ testAssertTrue (name `elem` calls (M.progMain root))
                , testAssertTrue (name `elem` calls (M.progMain linked))
                , testAssertTrue (Map.member unused (M.progFunctions linked))
                , case Map.lookup name (M.progFunctions linked) of
                    Just f -> testAssertTrue (not (null (M.specRequires (M.fnSpec f))))
                    Nothing -> Just "linked prefix function was lost"
                , case [e | M.Ghost e (M.GhostAxiom n _ _ _) <- blockZero, "fusedPrefixAxiom" `isInfixOf` n] of
                    [e] -> testAssertEq (Map.lookup name e) (Just (M.Const (M.CFn name)))
                    _ -> Just "expected the dependency's axiom payload once in linked entry block 0"
                , if any (rootGhostWithLocalAndFunction name) entryStatements then Nothing
                    else Just "expected a root proof with both local and shared entries"
                ]
    _ -> Just ("expected one prefix function and bounded template in separate units, got " ++ show
        [(mid, filter ("fused" `isInfixOf`) (Map.keys (M.progFunctions p)), filter ("fused" `isInfixOf`) (Map.keys (M.progBounded p))) | (mid, p) <- units])
  where
    entryBlocks = M.fnBlocks (M.progMain linked)
    blockZero = maybe [] M.blockStatements (Map.lookup (M.BlockId 0) entryBlocks)
    entryStatements = concatMap M.blockStatements (Map.elems entryBlocks)
    rootGhostWithLocalAndFunction name (M.Ghost env (M.GhostValidation _)) =
        Map.member "prefixResult" env && Map.lookup name env == Just (M.Const (M.CFn name))
    rootGhostWithLocalAndFunction _ _ = False

calls :: M.Function -> [String]
calls f = [n | M.BasicBlock _ (M.Call (M.Const (M.CFn n)) _ _ _) <- Map.elems (M.fnBlocks f)]

checkPack :: M.Program -> TestResult
checkPack p = case Map.lookup "forward[Int, Bool, Int]" (M.progFunctions p) of
    Just f -> asum
        [ testAssertEq (calls f) ["sink[Int, Bool, Int]"]
        , testAssertTrue (not (null (M.specRequires (M.fnSpec f))))
        ]
    Nothing -> Just "linked program has no heterogeneous forward copy"

unicodeCompletion :: IO TestResult
unicodeCompletion = withResult (linkRequest units) $ \plain -> do
    omitted <- fusedRequest (replaceMergeHeader "merge-copies 2" plain)
    actual <- fusedLink units
    parity <- compareFused units
    pure $ asum [expectRefusal invalidNameProfile omitted, parity, inspect actual check]
  where
    letters = ["a" ++ [chr 0x1e4d0], "a" ++ [chr 0xe9]]
    leaf letter = TNamed "Leaf" [ArgType (TNamed letter [])]
    wrapper letter = TNamed "Wrapper" [ArgType (leaf letter)]
    prefix = empty
        { M.progTypes = Map.fromList [(letter, M.StructDecl []) | letter <- letters]
        , M.progGenerics = Map.fromList
            [ ("Leaf", (["T"], [("permission", TBlock (TParam "T"))]))
            , ("Wrapper", (["T"], [("value", TParam "T")]))
            ]
        }
    mainFn = M.progMain empty
    root = empty{M.progMain = mainFn{M.fnLocals = Map.union (M.fnLocals mainFn) (Map.fromList
        [(M.Local i, M.LocalDecl (TRef (wrapper letter)) Nothing) | (i, letter) <- zip [1 ..] letters])}}
    units = [(ModuleId "app" (Just "prefix"), prefix), (rootId, root)]
    check p = testAssertEq (M.progTypes p) (Map.union (M.progTypes prefix) (Map.fromList (concatMap instances letters)))
    instances letter =
        [ (instanceName "Leaf" [ArgType (TNamed letter [])], M.StructDecl [("permission", TBlock (TNamed letter []))])
        , (instanceName "Wrapper" [ArgType (leaf letter)], M.StructDecl [("value", leaf letter)])
        ]

coveredAliasCollision :: IO TestResult
coveredAliasCollision = checkFused units $ \p -> case Map.lookup alias (M.progFunctions p) of
    Nothing -> Just "colliding check copy was not made"
    Just f -> asum
        [ testAssertEq (Map.findWithDefault [] (M.BlockId 0) (Map.map M.blockStatements (M.fnBlocks f)))
            [ M.Assign (M.Local 0) (M.CopyOf (int 22))
            , M.Assign (M.Local 0) (M.Use (int 33))
            ]
        , testAssertEq (Map.lookup coveredKey (M.specEnv (M.fnSpec f))) (Just (int 0))
        , testAssertTrue (Map.member retained (M.progFunctions p) && Map.notMember companion (M.progFunctions p))
        , testAssertEq (calls (M.progMain p)) [alias, implAlias]
        , testAssertEq [n | M.Ghost _ (M.GhostFunction n _ True) <- mainStatements p, n == alias] [alias]
        ]
  where
    retained = "keptTemplate"
    impl = "<S as Tr>::f"
    companion = "Tr for S::f"
    alias = "Tr for S::f[Int]"
    implAlias = "implAlias"
    body value = M.Assign (M.Local 0) (M.Use (int value))
    retainedFn = (template retained){M.fnBlocks = Map.singleton (M.BlockId 0) (block [body 11] M.Return)}
    companionFn = (template companion){M.fnBlocks = Map.fromList
        [ (M.BlockId 0, block [] (M.Call (M.Const (M.CFn "<$param T as Clone>::clone")) [int 22] (M.Local 0) (M.BlockId 1)))
        , (M.BlockId 1, block [body 33] M.Return)
        ]}
    prefix = empty
        { M.progFunctions = Map.fromList [(retained, retainedFn), (impl, template impl), (companion, companionFn)]
        , M.progBounded = Map.fromList [(name, bounded) | name <- [retained, impl, companion]]
        }
    root = empty
        { M.progInstances = Map.fromList [(name, (source, [ArgType TInt])) | (name, source) <- [(alias, retained), (implAlias, impl)]]
        , M.progMain = called (M.progMain empty) [(alias, []), (implAlias, [])]
        }
    units = [(ModuleId "app" (Just "prefix"), prefix), (rootId, root)]

tupleArityWrap :: IO TestResult
tupleArityWrap = checkFused units $ \p -> case Map.lookup alias (M.progFunctions p) of
    Nothing -> Just "tuple copy was not made"
    Just f -> asum
        [ testAssertEq (M.fnBlocks f) (M.fnBlocks copy)
        , testAssertEq (M.fnReturns f) (Just tuple)
        , testAssertEq (Map.lookup tupleName (M.progTypes p)) (Just (M.StructDecl [("0", TInt), ("1", TBool)]))
        , testAssertTrue (all (`Map.member` M.progFunctions p) [impl, companion])
        ]
  where
    base = "Tuple18446744073709551618"
    args = [ArgType TInt, ArgType TBool]
    tupleName = instanceName base args
    tuple = TNamed base args
    impl = "<" ++ base ++ " as Clone>::clone"
    companion = "Clone for " ++ base ++ "::clone"
    source = "copyTuple"
    alias = "tupleAlias"
    copy = (template source)
        { M.fnParams = [M.Local 1]
        , M.fnReturns = Just (TParam "T")
        , M.fnLocals = Map.fromList [(M.Local i, M.LocalDecl (TParam "T") Nothing) | i <- [0, 1]]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (block [M.Assign (M.Local 0) (M.CopyOf (M.Copy (M.Local 1)))] M.Return)
        }
    prefix = empty{M.progFunctions = Map.fromList [(impl, function impl), (companion, function companion)]}
    root = empty
        { M.progFunctions = Map.singleton source copy
        , M.progBounded = Map.singleton source bounded
        , M.progInstances = Map.singleton alias (source, [ArgType tuple])
        , M.progMain = called (M.progMain empty) [(alias, [M.Const (M.CData tupleName [("0", M.CInt 1), ("1", M.CBool True)])])]
        }
    units = [(ModuleId "app" (Just "prefix"), prefix), (rootId, root)]

witnessOnlyHiddenOperand :: IO TestResult
witnessOnlyHiddenOperand = witnessWithCalls 1

witnessWithCalls :: Int -> IO TestResult
witnessWithCalls count = checkFused [(rootId, root)] $ \p -> asum
    [ testAssertEq (M.fnBlocks <$> Map.lookup alias (M.progFunctions p))
        (Just (M.fnBlocks (called caller (replicate count (check, [emptyArray, int 3])))))
    , checkDispatch p stub [check]
    ]
  where
    source = "witnessCaller"
    alias = "witnessAlias"
    impl = "<Array as Witness>::measure"
    check = "Witness for Array::measure"
    stub = "Witness for $Self::measure"
    -- Neither the empty literal nor the Int destination supplies the inner extent.
    receiver extent = TArrayOf (TArrayOf TInt extent) (SizeConst 0)
    emptyArray = M.Const (M.CArray [])
    self = M.Local 1
    hidden = M.Local 2
    caller = called (template source) (replicate count ("<$param T as Witness>::measure", [emptyArray]))
    implFn = (function impl)
        { M.fnParams = [self]
        , M.fnLocals = Map.insert self (M.LocalDecl (receiver (SizeConst 3)) Nothing) (M.fnLocals (function impl))
        }
    checkFn = (function check)
        { M.fnParams = [self, hidden]
        , M.fnSizeParams = ["w"]
        , M.fnLocals = Map.fromList
            [(M.Local 0, M.LocalDecl TInt Nothing), (self, M.LocalDecl (receiver (SizeParam "w")) Nothing), (hidden, M.LocalDecl TInt (Just "w"))]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (block [M.Assign (M.Local 0) (M.Use (M.Copy hidden))] M.Return)
        }
    root = empty
        { M.progFunctions = Map.fromList [(source, caller), (impl, implFn), (check, checkFn), (stub, stubFn)]
        , M.progBounded = Map.fromList [(source, bounded), (stub, bounded)]
        , M.progInstances = Map.singleton alias (source, [ArgType (receiver (SizeConst 3))])
        , M.progMain = called (M.progMain empty) [(alias, [])]
        }
    stubFn = (template stub)
        { M.fnParams = [self]
        , M.fnLocals = Map.insert self (M.LocalDecl (TParam "T") Nothing) (M.fnLocals (template stub))
        }

inlineDispatch :: IO TestResult
inlineDispatch = checkFused [(rootId, root)] $ \p -> asum
    [ checkDispatch p stub []
    , testAssertEq (M.fnBlocks <$> Map.lookup alias (M.progFunctions p))
        (Just (body [saveReference, compareOperands]))
    ]
  where
    source = "compareViaBound"
    alias = "compareInts"
    stub = "Eq for $Self::eq"
    ordinary = "Eq for Int::eq"
    x = M.Local 1
    y = M.Local 2
    callback = M.Local 3
    ret = M.Local 0
    args = map M.Copy [x, y]
    body statements = Map.singleton (M.BlockId 0) (block statements M.Return)
    compareOperands = M.Assign ret (M.BinaryOp (M.Compare Eq) (M.Copy x) (M.Copy y))
    saveReference = M.Assign callback (M.Use (M.Const (M.CFn ordinary)))
    signature f = f{M.fnReturns = Just TBool, M.fnLocals = Map.singleton ret (M.LocalDecl TBool Nothing)}
    comparison f ty = (signature f)
        { M.fnParams = [x, y]
        , M.fnLocals = Map.fromList [(l, M.LocalDecl t Nothing) | (l, t) <- [(ret, TBool), (x, ty), (y, ty)]]
        }
    boundCaller = called (comparison (template source) (TParam "T")) [("<$param T as Eq>::eq", args)]
    caller = boundCaller
        { M.fnLocals = Map.insert callback (M.LocalDecl (TFn [TInt, TInt] TBool) (Just "callback")) (M.fnLocals boundCaller)
        , M.fnBlocks = Map.adjust (\b -> b{M.blockStatements = [saveReference]}) (M.BlockId 0) (M.fnBlocks boundCaller)
        }
    ordinaryFn = (comparison (function ordinary) TInt){M.fnBlocks = body [compareOperands]}
    stubFn = (comparison (template stub) (TParam "T"))
        {M.fnBlocks = body [M.Assign ret (M.Use (M.Const (M.CBool False)))]}
    root = empty
        { M.progFunctions = Map.fromList [(M.fnName f, f) | f <- [caller, ordinaryFn, stubFn, runner]]
        , M.progBounded = Map.fromList [(f, bounded) | f <- [source, stub]]
        , M.progInstances = Map.singleton alias (source, [ArgType TInt])
        }
    runner = called (signature (function "runEq")) [(alias, [int 1, int 2])]

checkDispatch :: M.Program -> String -> [String] -> TestResult
checkDispatch p stub targets = case Map.lookup stub (M.progFunctions p) of
    Nothing -> Just ("missing retained trait stub " ++ stub)
    Just f -> testAssertEq
        (Map.filterWithKey (\k _ -> k == "$dispatch" || "$dispatch " `isPrefixOf` k) (M.specEnv (M.fnSpec f)))
        (Map.fromList (("$dispatch", int 0) : [("$dispatch " ++ n, M.Const (M.CFn n)) | n <- targets]))

liftedBinderShadow :: IO TestResult
liftedBinderShadow = checkFused [(rootId, root)] $ \p -> case Map.lookup liftedCopy (M.progFunctions p) of
    Nothing -> Just "missing lifted copy with shadowing binders"
    Just f -> asum
        [ testAssertEq (M.fnTypeParams f, M.fnSizeParams f) (["T"], ["n"])
        , testAssertEq (Map.map M.localType (M.fnLocals f)) (Map.fromList
            [(M.Local 0, TInt), (shadowed, array (TParam "T") (SizeParam "n")), (captured, array TBool (SizeConst 2)), (n, TInt)])
        , testAssertEq (M.fnBlocks f) (M.fnBlocks inner)
        , testAssertEq (M.fnBlocks <$> Map.lookup alias (M.progFunctions p))
            (Just (M.fnBlocks (called outer [(liftedCopy, [M.Copy shadowed, M.Copy captured, int 3])])))
        ]
  where
    source = "shadowOuter"
    lifted = source ++ "::inner"
    alias = "shadowAlias"
    liftedCopy = alias ++ "::inner"
    shadowed = M.Local 1
    captured = M.Local 2
    n = M.Local 3
    m = M.Local 4
    array = TArrayOf
    locals = Map.fromList
        [ (M.Local 0, M.LocalDecl TInt Nothing)
        , (shadowed, M.LocalDecl (array (TParam "T") (SizeParam "n")) Nothing)
        , (captured, M.LocalDecl (array (TParam "U") (SizeParam "m")) Nothing)
        , (n, M.LocalDecl TInt (Just "n"))
        ]
    outer = (called (function source) [(lifted, map M.Copy [shadowed, captured, n])])
        { M.fnParams = [shadowed, captured, n, m]
        , M.fnTypeParams = ["T", "U"]
        , M.fnSizeParams = ["n", "m"]
        , M.fnLocals = Map.insert m (M.LocalDecl TInt (Just "m")) locals
        }
    inner = (template lifted)
        { M.fnParams = [shadowed, captured, n]
        , M.fnSizeParams = ["n"]
        , M.fnLocals = locals
        , M.fnBlocks = Map.singleton (M.BlockId 0) (block [M.Assign (M.Local 0) (M.Use (M.Copy n))] M.Return)
        }
    root = empty
        { M.progFunctions = Map.fromList [(source, outer), (lifted, inner)]
        , M.progBounded = Map.singleton source bounded{M.boundedSizes = ["n", "m"], M.boundedLifted = [lifted]}
        , M.progInstances = Map.singleton alias (source, [ArgType TInt, ArgType TBool, ArgSize (SizeConst 3), ArgSize (SizeConst 2)])
        , M.progMain = called (M.progMain empty)
            [(alias, [M.Const (M.CArray (replicate 3 (M.CInt 0))), M.Const (M.CArray (replicate 2 (M.CBool False))), int 3, int 2])]
        }

called :: M.Function -> [(String, [M.Operand])] -> M.Function
called f cs = f{M.fnBlocks = Map.fromList
    ([(M.BlockId i, block [] (M.Call (M.Const (M.CFn n)) args (M.Local 0) (M.BlockId (i + 1)))) | (i, (n, args)) <- zip [0 ..] cs]
    ++ [(M.BlockId (length cs), block [] M.Return)])}

mainStatements :: M.Program -> [M.Statement]
mainStatements = concatMap M.blockStatements . Map.elems . M.fnBlocks . M.progMain

checkFused :: [(ModuleId, M.Program)] -> (M.Program -> TestResult) -> IO TestResult
checkFused units check = do
    actual <- fusedLink units
    parity <- compareFused units
    pure $ asum [parity, inspect actual check]

checkContractOverlay :: IO TestResult
checkContractOverlay = checkFused units $ \p -> case Map.lookup consumer (M.progFunctions p) of
    Just f -> asum
        [ testAssertEq (Map.lookup "alias" (M.specEnv (M.fnSpec f))) (Just (fnRef checked))
        , testAssertEq (Map.lookup implementation (M.specEnv (M.fnSpec f))) (Just (int 17))
        , testAssertEq (Map.lookup otherImpl (M.specEnv (M.fnSpec f))) (Just (fnRef otherImpl))
        , case [e | b <- Map.elems (M.fnBlocks f), M.Ghost e _ <- M.blockStatements b] of
            [e] -> asum
                [ testAssertEq (Map.lookup "alias" e) (Just (fnRef implementation))
                , testAssertEq (Map.lookup implementation e) (Just (fnRef implementation))
                ]
            _ -> Just "expected exactly one ghost in the check function"
        ]
    Nothing -> Just "check function was lost"
  where
    consumer = "Tr for S::f"
    implementation = "<S as Tr>::g"
    checked = "Tr for S::g"
    otherImpl = "<T as Tr>::g"
    fnRef n = M.Const (M.CFn n)
    alias = Map.singleton "alias" (fnRef implementation)
    body = (function consumer)
        { M.fnSpec = M.emptySpec{M.specEnv = Map.insert implementation (int 17) alias}
        , M.fnBlocks = Map.singleton (M.BlockId 0) (block [M.Ghost alias
            (M.GhostValidation (S.AssignProofVar "probe" (S.Val (S.VInt 1))))] M.Return)
        }
    prefix = empty{M.progFunctions = Map.insert consumer body (Map.fromList
        [(n, function n) | n <- [implementation, checked, otherImpl, "Tr for T::g"]])}
    units = [(ModuleId "app" (Just "prefix"), prefix), (rootId, recursion False)]

rootEnvironmentSharing :: IO TestResult
rootEnvironmentSharing = checkFused units $ \p -> case Map.lookup "ordinary" (M.progFunctions p) of
    Just f -> asum
        [ testAssertEq (Map.lookup "ordinary" (M.specEnv (M.fnSpec f))) (Just (int 17))
        , testAssertEq (Map.lookup "ordinaryAlias" (M.specEnv (M.fnSpec f))) (Just (M.Const (M.CFn "ordinary")))
        , testAssertEq (Map.lookup entryName (M.specEnv (M.fnSpec f))) (Just (M.Const (M.CFn entryName)))
        ]
    Nothing -> Just "ordinary root was lost"
  where
    work = recursion False
    entryName = M.fnName (M.progMain work)
    env = Map.fromList [("ordinary", int 17), ("ordinaryAlias", M.Const (M.CFn "ordinary")), (entryName, M.Const (M.CFn entryName))]
    ordinary = (function "ordinary"){M.fnSpec = M.emptySpec{M.specEnv = env}}
    units = [(ModuleId "app" (Just "prefix"), empty{M.progFunctions = Map.singleton "ordinary" ordinary}), (rootId, work)]

orderedRefusal :: IO TestResult
orderedRefusal = do
    actual <- fusedLink units
    parity <- compareFused units
    pure $ asum [expectRefusal expected actual, parity]
  where
    expected = "Validation failed: internal compiler error: firstAlias gives firstTemplate 0 types and 0 sizes, and it has 1 and 0"
    units = [(ModuleId "app" (Just "prefix"), prefix), (rootId, root)]
    prefix = empty{M.progFunctions = Map.singleton "zRoot" (caller "zRoot" [(2, "prefixAlias")])}
    root = empty
        { M.progFunctions = Map.insert "aRoot" (caller "aRoot" [(2, "firstAlias"), (10, "laterAlias")]) (Map.fromList [(n, template n) | (_, n) <- aliases])
        , M.progBounded = Map.fromList [(n, bounded) | (_, n) <- aliases]
        , M.progInstances = Map.fromList [(a, (n, [])) | (a, n) <- aliases]
        }
    aliases = [("prefixAlias", "prefixTemplate"), ("firstAlias", "firstTemplate"), ("laterAlias", "laterTemplate")]
    caller n cs = (function n){M.fnBlocks = Map.fromList
        ((M.BlockId 0, block [] (M.Goto (M.BlockId 2))) :
            [(M.BlockId i, block [] (M.Call (M.Const (M.CFn a)) [] (M.Local 0) (M.BlockId j)))
            | ((i, a), j) <- zip cs (map fst (drop 1 cs) ++ [11])]
            ++ [(M.BlockId 11, block [] M.Return)])}

refusalPrecedence :: IO TestResult
refusalPrecedence = withResult (linkRequest growth) $ \valid ->
    withResult (linkRequest collisionUnits) $ \colliding -> do
        oldValid <- oldLinkRequest valid
        oldCollision <- oldLinkRequest colliding
        oldWire <- oldLinkRequest (badWire "merge 3" colliding)
        plain <- fusedRequest valid
        actualCopies <- fusedLink growth
        actualCollision <- fusedLink collisionUnits
        actualProfile <- fusedRequest (replaceMergeHeader "merge-copies 2" colliding ++ malformedProfile)
        actualWire <- fusedRequest (badWire "merge-copies 3" colliding ++ malformedProfile)
        pure $ asum
            [ inspect oldValid (\p -> asum
                [ testAssertEq plain (Ok p)
                , expectRefusal growthRefusal (makeCopiesWith Set.empty (M.completeInstances p))
                ])
            , expectRefusal collision oldCollision
            , expectRefusal wire oldWire
            , expectRefusal ("Validation failed: " ++ growthRefusal) actualCopies
            , expectRefusal collision actualCollision
            , expectRefusal invalidNameProfile actualProfile
            , expectRefusal wire actualWire
            ]
  where
    growth = [(rootId, recursion True)]
    collisionUnits = growth ++ [(rootId, empty)]
    collision = "link error: module app::main has inconsistent units"
    wire = "the linking request contains unreadable MIR3"
    malformedProfile = "name-classes 1\n233 233 8\n"
    badWire header request = replaceMergeHeader header request ++ "unit \"app\" some \"broken\" 1\nnot-mir\n"

replaceMergeHeader :: String -> String -> String
replaceMergeHeader header request = unlines (take 1 rows ++ [header] ++ drop 2 rows)
  where
    rows = lines request

invalidNameProfile :: String
invalidNameProfile = "the linking request has invalid or incomplete name classes"

expectRefusal :: String -> Result a String -> TestResult
expectRefusal expected (Error actual) = testAssertEq actual expected
expectRefusal expected (Ok _) = Just ("accepted; expected " ++ expected)

noWork :: IO TestResult
noWork = do
    let actual = Link.standaloneCopies (error "no-work forced its library") program
    pure $ testAssertEq actual (Ok program)
  where
    fun = M.progMain empty
    program = empty{M.progMain = fun{M.fnBlocks = Map.singleton (M.BlockId 0) (block
        [ M.Ghost Map.empty (M.GhostValidation (S.AssignProofVar "proofSentinel" (S.Val (S.VInt 17))))
        , M.Assign (M.Local 0) (M.Use (int 7))
        ] M.Return)}}

standaloneWork :: IO TestResult
standaloneWork = withResult (wideStatements `bindResult` finishLowered) $ \program ->
    withResult (makeCopiesWith Set.empty program) $ \expected -> do
        actual <- standaloneCopies Set.empty program
        pure $ asum [checkWideStatements expected, inspect actual checkWideStatements, testAssertEq actual (Ok expected)]
