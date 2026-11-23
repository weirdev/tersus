module TestMirPacks (testMirPacks) where

import Data.List (isPrefixOf, partition, sort)
import Data.Maybe (catMaybes, listToMaybe)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (ExitCode (..))

import DataCodec (quote)
import ElaboratorTool (bootstrapLoader)
import LibPackage (libPackage)
import qualified Mir as M
import MirData (readLowered, writeLowered)
import MirPacksOracle (Expanded (..), expandPack)
import qualified Native
import PackageCompile (compileModulesUsing, packageLinkInputs)
import PackageData (Snapshot (..), resolverFromFiles)
import StdLib (builtinFunct)
import qualified Syntax as S
import TestHarness
import TestMirCopiesParity (nativeCopiesProbe)
import TestVariadic (variadicPrograms)
import Types (BuiltinFunct (Rel), Rel (Eq, Lt), Type (TBool, TInt, TParam))
import Utils

asUnit :: M.Program -> M.Lowered
asUnit p = M.Lowered p Set.empty Set.empty Set.empty Set.empty Set.empty Set.empty []

packType :: String
packType = "..T"

compareExpansion :: Int -> String -> M.Program -> TestResult -> IO TestResult
compareExpansion count target program refusal = compareExpansionWith count target program refusal (const Nothing)

compareExpansionWith :: Int -> String -> M.Program -> TestResult -> (M.Function -> TestResult) -> IO TestResult
compareExpansionWith count target program refusal check =
    case (Map.lookup target (M.progBounded program), Map.lookup target (M.progFunctions program)) of
        (Just bounded, Just fun) | packType `elem` M.fnTypeParams fun ->
            case writeLowered (asUnit program) of
                Error e -> pure (Just e)
                Ok payload -> do
                    tool <- nativeCopiesProbe
                    case tool of
                        Error e -> pure (Just e)
                        Ok executable -> do
                            let request = "pack\n" ++ unwords [quote target, quote packType, show count] ++ "\n" ++ payload
                            (status, out, errors) <- Native.runWithInputFull executable request
                            pure $ firstFailure [testAssertEq status ExitSuccess, compareResult (expandPack bounded packType (toInteger count) fun) out (decodeUtf8 errors)]
        _ -> pure (Just ("not a retained variadic template: " ++ target))
  where
    compareResult (Left expected) out errors = firstFailure
        [testAssertEq (Just expected) refusal, testAssertEq out "1\n", testAssertEq errors (expected ++ "\n")]
    compareResult (Right expected) out errors = firstFailure
        [ testAssertEq refusal Nothing
        , testAssertEq errors ""
        , case break (== "tersus-mir 3") (lines out) of
            (records, mir@(_ : _)) -> firstFailure
                [ testAssertEq orders [envOrder expected]
                , testAssertEq (sort metadataRows) (sort (metadata expected))
                , case readLowered (unlines mir) of
                    Error e -> Just e
                    Ok result -> case Map.lookup target (M.progFunctions (M.lowProgram result)) of
                        Nothing -> Just ("the native result lost " ++ target)
                        Just actual -> firstFailure
                            [ testAssertEq actual (exFunction expected)
                            , testAssertEq (show actual) (show (exFunction expected))
                            , check actual
                            ]
                ]
              where
                (orders, metadataRows) = partition (\row -> row == "env-order" || "env-order " `isPrefixOf` row) records
            _ -> Just ("pack probe did not write MIR3: " ++ take 200 out)
        ]
    envOrder = unwords . ("env-order" :) . map quote . Map.keys . M.specEnv . M.fnSpec . exFunction

firstFailure :: [TestResult] -> TestResult
firstFailure = listToMaybe . catMaybes

metadata :: Expanded -> [String]
metadata expanded =
    indexes "block" (\(M.BlockId i) -> i) (exBlockIndexes expanded)
        ++ indexes "local" (\(M.Local i) -> i) (exLocalIndexes expanded)
        ++ [unwords ["spread", quote spread, quote callee, show lo, show hi] | (spread, (callee, lo, hi)) <- Map.toList (exSpreads expanded)]
  where
    indexes :: Ord a => String -> (a -> Int) -> Map.Map a (Map.Map String Integer) -> [String]
    indexes tag ident bindings = concat
        [ prefix : [unwords [prefix, quote ty, show ix] | (ty, ix) <- Map.toList values]
        | (k, values) <- Map.toList bindings, let prefix = unwords [tag, show (ident k)]
        ]

realTemplate :: String -> String -> Result M.Program String
realTemplate target source = compileModulesUsing bootstrapLoader libPackage snapshot `bindResult` packageLinkInputs `bindResult` \(_, units) ->
    case [p | (_, p) <- units, Map.member target (M.progBounded p)] of
        [p] -> Ok p
        _ -> Error ("expected one pre-copies package unit defining " ++ target)
  where
    entry = "app/main.tersus"
    snapshot = Snapshot (resolverFromFiles [("app/package.tersus", ""), (entry, source)]) entry False

testMirPacks :: Test
testMirPacks = TestList "testMirPacks"
    ([ realCase ("guard, forall and contracts at arity " ++ show count) "f" count guarded | count <- [0, 1, 3] ]
    ++ [ corpusCase "nested loops and indices" "grid" 3
       , corpusCase "validation statements and defines at loop indices" "f" 2
       , corpusCase "a function defined in a loop over the pack in a branch the copy drops" "f" 0
       , realCase "forwarding preserves the prefix and slice argument order" "forward" 3 forwarding
       , TestCase "signed multiword loop bound and block index" (compareExpansion 1 "fixture" wideIndex Nothing)
       , TestCase "nonconstant get index is refused exactly" (compareExpansion 1 "fixture" dynamicIndex (Just unfixedIndex))
       , TestCase "reassigned get index is not folded" (compareExpansion 1 "fixture" reassignedIndex (Just unfixedIndex))
       , TestCase "unknown spread bounds are refused before the pack-as-value check" $
           compareExpansion 1 "fixture" dynamicSpread (Just "internal compiler error: the part of the pack of fixture a call forwards is not fixed in a copy")
       , TestCase "the pack is not an ordinary value" $
           compareExpansion 1 "fixture" packValue (Just "internal compiler error: the pack args of fixture is used as a value in a copy")
       , TestCase "an assignment keeps an unbound element local live and is refused" $
           compareExpansion 1 "fixture" unboundLocal (Just "internal compiler error: a copy of fixture uses _2, of the type of an element no argument gives")
       , TestCase "spread environments are ordered before serialization and existing bindings win" $
           compareExpansionWith 2 "fixture" orderedEnv Nothing checkOrderedEnv
       , TestCase "lifted markers stay ordered and ordinary loops refer to their cloned defines" $
           compareExpansionWith 2 "fixture" liftedLoop Nothing checkLiftedLoop
       , TestCase "get at 2^64 produces the exact range ghosts, not element zero" $
           compareExpansionWith 1 "fixture" wrappedIndex Nothing checkWrappedIndex
       , TestCase "a later unfixed proof read wins over an earlier out-of-range read" $
           compareExpansion 1 "fixture" proofRefusal (Just unfixedProofIndex)
       ])
  where
    realCase label target count compiled = TestCase label $ case compiled of
        Error e -> pure (Just e)
        Ok p -> compareExpansion count target p Nothing
    corpusCase label target count = realCase label target count $ case lookup label variadicPrograms of
        Nothing -> Error ("no variadic fixture named " ++ label)
        Just source -> realTemplate target source

guarded :: Result M.Program String
guarded = realTemplate "f" $ unlines
    [ "trait Score { fn score(self: &Self) -> Int; };"
    , "impl Score for Int { fn score(self: &Self) -> Int { return self; }; };"
    , "fn f<..T: Score>(args: &..T) -> Int"
    , "  [{ affirm forall i in 0..size(args): Score::score(get(args, i)) >= 0; }]"
    , "  [{ affirm return >= 0; }] {"
    , "    if size(args) > 0 { return get(args, size(args) - 1).score(); }; return 0;"
    , "}; return f() + f(1) + f(1, 2, 3);"
    ]

forwarding :: Result M.Program String
forwarding = realTemplate "forward" $ unlines
    [ "fn sink<..U>(fixed: Int, rest: &..U) -> Int { return fixed + size(rest); };"
    , "fn forward<..T>(args: &..T) -> Int {"
    , "    n = 0; for i in 0..size(args) { n = n + sink(i, 9, slice(args, i, size(args))); };"
    , "    return n + sink(7, args);"
    , "}; return forward(1, true, 2);"
    ]

fixture :: [M.PackLoop] -> M.Function -> M.Program
fixture loops f = M.Program Map.empty (Map.singleton "fixture" f) entry Map.empty Map.empty
    (Map.singleton "fixture" (M.BoundedFn [] [] [] loops)) Map.empty
  where
    entry = M.Function "main" [] Nothing Map.empty (Map.singleton (M.BlockId 0) (M.BasicBlock [] M.Return)) [] [] [] [] [] M.emptySpec

function :: [M.Local] -> [(Type, Maybe String)] -> [(Int, M.BasicBlock)] -> M.Function
function params decls blocks = M.Function "fixture" params (Just TInt)
    (Map.fromList (zip (map M.Local [0 ..]) (map (uncurry M.LocalDecl) decls)))
    (Map.fromList [(M.BlockId i, b) | (i, b) <- blocks]) [] [packType] [] [] [] M.emptySpec

wideIndex :: M.Program
wideIndex = fixture [loop] $ function [pack]
    [(TInt, Nothing), (TParam packType, Just "args"), (TInt, Nothing), (TInt, Nothing), (TInt, Just "i"), (TParam "..T@0", Nothing), (TBool, Nothing)]
    [ (0, M.BasicBlock [M.Assign ret (M.Use (num 0)), M.Assign lo (M.BinaryOp M.Sub (num 0) (num (2 ^ (130 :: Int) + 1))), M.Assign hi (M.BinaryOp M.Add (M.Copy lo) (num 1)), M.Assign ix (M.Use (M.Copy lo))] (M.Goto header))
    , (1, M.BasicBlock [M.Assign test (M.BinaryOp (M.Compare Lt) (M.Copy ix) (M.Copy hi))] (M.SwitchBool (M.Copy test) body exit))
    , (2, M.BasicBlock [M.Assign ret (M.Use (M.Copy ix)), M.Assign ix (M.BinaryOp M.Add (M.Copy ix) (num 1))] (M.Goto header))
    , (3, M.BasicBlock [] M.Return)
    ]
  where
    (ret, pack, lo, hi, ix, element, test) = (M.Local 0, M.Local 1, M.Local 2, M.Local 3, M.Local 4, M.Local 5, M.Local 6)
    (header, body, exit) = (M.BlockId 1, M.BlockId 2, M.BlockId 3)
    loop = M.PackLoop header body exit [body] [] ix element "..T@0" lo hi Nothing
    num = M.Const . M.CInt

unfixedIndex :: String
unfixedIndex = "internal compiler error: an index of the pack of fixture is not fixed in a copy"

dynamicIndex :: M.Program
dynamicIndex = indexFixture [M.Local 1, M.Local 2] []

reassignedIndex :: M.Program
reassignedIndex = indexFixture [M.Local 2]
    [M.Assign (M.Local 1) (M.Use (M.Const (M.CInt k))) | k <- [0, 0]]

indexFixture :: [M.Local] -> [M.Statement] -> M.Program
indexFixture params before = fixture [] $ function params
    [(TInt, Nothing), (TInt, Just "i"), (TParam packType, Just "args"), (TParam "..T@0", Nothing)]
    [(0, M.BasicBlock (before ++ [M.Assign (M.Local 3) (M.ListOp M.Get [M.Copy (M.Local 2), M.Copy (M.Local 1)])]) M.Return)]

dynamicSpread :: M.Program
dynamicSpread = fixture [] $ function [M.Local 1, M.Local 2]
    [(TInt, Nothing), (TInt, Just "n"), (TParam packType, Just "args")]
    [(0, M.BasicBlock [] (M.Call (M.Const (M.CFn "sink")) [M.Copy (M.Local 2), M.Copy (M.Local 1), M.Const (M.CInt 1)] (M.Local 0) (M.BlockId 1))), (1, M.BasicBlock [] M.Return)]

packValue :: M.Program
packValue = fixture [] $ function [M.Local 1]
    [(TInt, Nothing), (TParam packType, Just "args")]
    [(0, M.BasicBlock [M.Drop (M.Local 1)] M.Return)]

unboundLocal :: M.Program
unboundLocal = fixture [] $ function [M.Local 1]
    [(TInt, Nothing), (TParam packType, Just "args"), (TParam "..T@0", Nothing)]
    [(0, M.BasicBlock [M.Assign (M.Local 2) (M.Use (M.Const (M.CInt 0)))] M.Return)]

orderedEnv :: M.Program
orderedEnv = fixture [] f{M.fnSpec = M.emptySpec{M.specEnv = Map.fromList entries}}
  where
    f = function [M.Local 1] [(TInt, Nothing), (TParam packType, Just "args")] [(0, M.BasicBlock [] M.Return)]
    entries = [("args", M.Move (M.Local 1)), ("args 1", int 99), ("z", int 9)]

checkOrderedEnv :: M.Function -> TestResult
checkOrderedEnv f = testAssertEq (Map.toList (M.specEnv (M.fnSpec f)))
    [("args 0", M.Copy (M.Local 2)), ("args 1", int 99), ("z", int 9)]

liftedLoop :: M.Program
liftedLoop = fixture [packLoop] f{M.fnSpec = M.emptySpec{M.specLoops = Map.singleton (M.BlockId 4) plainLoop}}
  where
    f = function [M.Local 1, M.Local 7]
        [(TInt, Nothing), (TParam packType, Just "args"), (TInt, Nothing), (TInt, Nothing), (TInt, Nothing), (TParam "..T@0", Nothing), (TBool, Nothing), (TBool, Just "again")]
        [ (0, M.BasicBlock [at 2 (int 0), at 3 (int 2), at 4 (int 0)] (go 1))
        , (1, M.BasicBlock [M.Assign (M.Local 6) (M.BinaryOp (M.Compare Lt) (ref 4) (ref 3))] (M.SwitchBool (ref 6) (M.BlockId 2) (M.BlockId 3)))
        , (2, M.BasicBlock (liftedMarkers ++ [ghost (S.AssignProofVar "limit" (S.Val (S.VInt 2)))]) (go 4))
        , (3, M.BasicBlock [] M.Return)
        , (4, M.BasicBlock [] (M.SwitchBool (ref 7) (M.BlockId 5) (M.BlockId 6)))
        , (5, M.BasicBlock [] (go 4))
        , (6, M.BasicBlock [M.Assign (M.Local 4) (M.BinaryOp M.Add (ref 4) (int 1))] (go 1))
        ]
    packLoop = M.PackLoop (M.BlockId 1) (M.BlockId 2) (M.BlockId 3) (map M.BlockId [2, 4, 5, 6]) []
        (M.Local 4) (M.Local 5) "..T@0" (M.Local 2) (M.Local 3) Nothing
    plainLoop = M.LoopSpec [limitFact "limit"] (Just (S.Shrinks (S.Var "limit"))) (Map.singleton "again" (ref 7)) (M.BlockId 5)
    ref = M.Copy . M.Local
    at n = M.Assign (M.Local n) . M.Use
    go = M.Goto . M.BlockId

liftedMarkers :: [M.Statement]
liftedMarkers =
    [ M.Ghost (Map.singleton "first captures" (int 10)) (M.GhostFunction "first lifted" "first" False)
    , M.Ghost (Map.singleton "second captures" (int 20)) (M.GhostFunction "second lifted" "second" False)
    ]

limitFact :: String -> S.ValidationStatement
limitFact n = S.ProofAssert (S.FApp (S.CTerm (builtinFunct (Rel Eq))) [S.ATerm n, S.CTerm (S.VInt 2)])

checkLiftedLoop :: M.Function -> TestResult
checkLiftedLoop f = firstFailure
    [ testAssertEq [s | b <- Map.elems (M.fnBlocks f), s@(M.Ghost _ M.GhostFunction{}) <- M.blockStatements b] liftedMarkers
    , testAssertEq (fmap (drop 3 . M.blockStatements) (Map.lookup (M.BlockId 0) (M.fnBlocks f))) (Just liftedMarkers)
    , testAssertEq (Map.toList (M.specLoops (M.fnSpec f)))
        [ (M.BlockId header, M.LoopSpec [limitFact n] (Just (S.Shrinks (S.Var n))) (Map.singleton "again" (M.Copy (M.Local 7))) (M.BlockId body))
        | (header, body, n) <- [(8, 9, "limit in iteration 0"), (12, 13, "limit in iteration 1")]
        ]
    ]

wrappedIndex :: M.Program
wrappedIndex = fixture [] $ function [M.Local 1] [(TInt, Nothing), (TParam packType, Just "args")]
    [(0, M.BasicBlock [ghost (S.AssignProofVar "$pack read at 17" (S.Val (S.VInt 0))), M.Assign (M.Local 0) (M.ListOp M.Get [M.Copy (M.Local 1), int wide]), M.Drop (M.Local 1)] M.Return)]

checkWrappedIndex :: M.Function -> TestResult
checkWrappedIndex f = testAssertEq (Map.lookup (M.BlockId 0) (M.fnBlocks f)) $ Just $ M.BasicBlock
    [ M.Ghost (Map.fromList [(ix, int wide), ("1 argument", int 1)])
        (M.GhostValidation (S.ProofAssert (S.FApp (S.CTerm (builtinFunct (Rel Lt))) [S.ATerm ix, S.ATerm "1 argument"])))
    , ghost (S.Assume (S.FApp (S.CTerm (builtinFunct (Rel Eq))) [S.CTerm (S.VInt 0), S.CTerm (S.VInt 1)]))
    ] M.Return
  where
    ix = "the index " ++ show wide ++ " of get(args, ...) at line 17"

proofRefusal :: M.Program
proofRefusal = fixture [] $ function [M.Local 1, M.Local 2] [(TInt, Nothing), (TParam packType, Just "args"), (TInt, Just "i")]
    [(0, M.BasicBlock [M.Ghost (Map.fromList [("args", M.Copy (M.Local 1)), ("i", M.Copy (M.Local 2))]) (M.GhostValidation (S.ProofAssert proof))] M.Return)]
  where
    proof = S.FApp (S.CTerm (builtinFunct (Rel Eq))) [getAt (S.CTerm (S.VInt wide)), getAt (S.ATerm "i")]
    getAt i = S.FApp (S.ATerm "get") [S.ATerm "args", i]

unfixedProofIndex :: String
unfixedProofIndex = "Type error: get(args, i) in a contract or a validation statement needs an index fixed in each copy (numbers, size(args), the index of a forall over args, and + - * of those)"

wide :: Integer
wide = 2 ^ (64 :: Int)

int :: Integer -> M.Operand
int = M.Const . M.CInt

ghost :: S.ValidationStatement -> M.Statement
ghost = M.Ghost Map.empty . M.GhostValidation
