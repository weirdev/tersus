module TestNativePaired (testNativePaired, pairedCases) where

import Control.Exception (evaluate)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import Compile (lowerSource)
import MirEval (MirValue(..))
import MirHousekeeping (verifyProgram)
import TestHarness (Test(..))
import Utils (Result(..))
import ValidatorNative (runValidator, serializeFunction, validateCompiled, validateCompiledUncached, validationCacheHits, verdicts)

type Verdict = (Int, Int, Int)
type PairCase = (String, MirValue, MirValue, [MirValue], Verdict)

record :: String -> [(String, MirValue)] -> MirValue
record = MData

missing :: MirValue
missing = record "ValueLookup::Missing" []

found :: Integer -> MirValue
found term = record "ValueLookup::Found" [("term", MInt term)]

binding :: Integer -> Maybe Integer -> MirValue
binding semantic storage = record "ValueBinding" [("semantic", MInt semantic), ("storage", maybe missing found storage)]

locals :: [(Integer, Integer, Maybe Integer)] -> MirValue
locals entries = MList [record "LocalBinding" [("local", MInt local), ("value", binding semantic storage)] | (local, semantic, storage) <- entries]

ref :: String -> Integer -> MirValue
ref kind identifier = record ("ValueRef::" ++ kind) [(if kind == "Term" then "term" else "local", MInt identifier)]

pairRef :: Integer -> Maybe Integer -> MirValue
pairRef semantic storage = record "ValueRef::Binding" [("value", binding semantic storage)]

step :: String -> [(String, MirValue)] -> MirValue
step name = record ("ExecutionStep::" ++ name)

assign :: Integer -> MirValue -> MirValue
assign local value = step "Assign" [("local", MInt local), ("value", value)]

check :: Integer -> MirValue -> MirValue -> MirValue
check relation left right = step "Check" [("relation", MInt relation), ("left", left), ("right", right)]

application :: Integer -> Integer -> [Integer] -> MirValue
application identifier function arguments = record "ApplicationTerm" [("id", MInt identifier), ("function", MInt function), ("arguments", MList (map MInt arguments))]

constant :: Integer -> Integer -> Integer -> MirValue
constant identifier kind value = record "ConstantTerm" [("id", MInt identifier), ("kind", MInt kind), ("value", MInt value)]

context :: [MirValue] -> [MirValue] -> [Integer] -> [Integer] -> [MirValue] -> MirValue
context applications constants fields constructors selections = record "ValidatorContext"
    [("equalities", MList []), ("applications", MList applications), ("constants", MList constants),
     ("orders", MList []), ("different", MList []), ("variants", MList []),
     ("fieldFunctions", MList (map MInt fields)), ("constructorFunctions", MList (map MInt constructors)),
     ("constructorFields", MList selections), ("differences", MList []), ("proofFunctions", MList [])]

baseContext :: MirValue
baseContext = context [] [constant 1000 1 1, constant 1001 1 0, constant 1002 0 0, constant 1003 0 1] [] [] []

block :: Integer -> [MirValue] -> MirValue -> MirValue
block identifier steps end = record "ExecutionBlock" [("id", MInt identifier), ("steps", MList steps), ("end", end)]

done :: MirValue
done = record "ExecutionEnd::Done" []

jump :: Integer -> MirValue
jump target = record "ExecutionEnd::Jump" [("target", MInt target)]

simple :: String -> MirValue -> MirValue -> [MirValue] -> Verdict -> PairCase
simple name bindings ctx steps expected = (name, bindings, ctx, [block 0 steps done], expected)

owners :: MirValue
owners = locals [(1, 1, Just 101), (2, 1, Just 102)]

project :: Integer -> Integer -> MirValue -> MirValue
project local function object = step "ProjectBinding" [("local", MInt local), ("function", MInt function), ("object", object)]

joinCase :: String -> MirValue -> [MirValue] -> [MirValue] -> [MirValue] -> Verdict -> PairCase
joinCase name bindings left right checks expected = (name, bindings, baseContext, blocks, expected)
  where
    branch = record "ExecutionEnd::BooleanBranch" [("yes", MInt 1), ("no", MInt 2), ("join", MInt 3),
        ("value", ref "Term" 500), ("trueValue", ref "Term" 1000), ("falseValue", ref "Term" 1001)]
    blocks = [block 0 [] branch, block 1 left (jump 3), block 2 right (jump 3), block 3 checks done]

pairedCases :: [PairCase]
pairedCases =
    ([simple "projection near minimum exhausts two-member allocation" (locals [(1,1,Just (-9223372036854775807))]) edgeContext [project 3 800 (ref "Local" 1)] (2,0,0)
     ,simple "projection can consume final two identifiers" (locals [(1,1,Just (-9223372036854775806))]) edgeContext [project 3 800 (ref "Local" 1),check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 3)] (0,-1,-1)
     ,simple "existing field applications need no new identifier" (locals [(1,1,Just (-9223372036854775808))]) reusedContext [project 3 800 (ref "Local" 1)] (0,-1,-1)
     ,simple "known equality remains valid at minimum" (locals [(1,1,Just (-9223372036854775808))]) baseContext [check 0 (ref "Local" 1) (ref "Local" 1)] (0,-1,-1)
     ,simple "nontrivial forall at minimum fails exhausted" (locals [(1,1,Just 101),(3,3,Just (-9223372036854775808))]) edgeTemplateContext edgeTemplateSteps (2,0,2)
     ,simple "nontrivial forall can consume and reuse final identifier" (locals [(1,1,Just 101),(3,3,Just (-9223372036854775807))]) edgeTemplateContext edgeTemplateSteps (0,-1,-1)
     ,simple "fallback read exhaustion is unsupported" (locals [(1,1,Just (-9223372036854775808))]) fallbackContext [check 0 (ref "Term" 200) (ref "Term" 1004)] (2,0,0)
     ,simple "fallback read consumes final identifier without trapping" (locals [(1,1,Just (-9223372036854775807))]) fallbackContext [check 0 (ref "Term" 200) (ref "Term" 1004)] (1,0,0)
     ,simple "fallback read reuses existing application at minimum" (locals [(1,1,Just (-9223372036854775808))]) fallbackReusedContext [check 0 (ref "Term" 200) (ref "Term" 1004)] (1,0,0)] ++
    [ simple "raw bound uses initialized length not spare capacity" (locals [(1,1,Just 101)]) boundsContext (boundsSteps 1003) (1,0,4)
    , simple "raw initialized index bound control" (locals [(1,1,Just 101)]) boundsContext (boundsSteps 1002) (0,-1,-1)
    , simple "forall storage observation uses paired capture" owners templateContext (templateSteps (-10)) (0,-1,-1)
    , simple "forall cannot substitute equal-content replacement storage" owners templateContext (templateSteps 1) (1,0,4)
    , simple "equal content distinct owner identities" owners baseContext [check 0 (ref "Local" 1) (ref "Local" 2)] (0,-1,-1)
    , simple "content equality cannot imply storage equality" owners baseContext [check 0 (ref "Local" 1) (ref "Local" 2), check 0 (ref "StorageLocal" 1) (ref "StorageLocal" 2)] (1,0,1)
    , simple "distinct symbolic owners do not assert allocation disequality" owners baseContext [check 1 (ref "StorageLocal" 1) (ref "StorageLocal" 2)] (1,0,0)
    , simple "equal content remains nonvacuous" owners baseContext [check 0 (ref "Local" 1) (ref "Local" 2), check 0 (ref "Term" 1000) (ref "Term" 1001)] (1,0,1)
    , simple "copy preserves allocation identity" owners baseContext [assign 3 (ref "Local" 1), check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 1)] (0,-1,-1)
    , simple "return local preserves pair" owners baseContext [assign 0 (ref "Local" 2), check 0 (ref "Local" 0) (ref "Local" 1), check 0 (ref "StorageLocal" 0) (ref "StorageLocal" 2)] (0,-1,-1)
    , simple "old and header snapshots preserve pair" owners baseContext [assign (-1000001) (ref "Local" 1), assign (-2000001) (ref "Local" 1), assign 1 (ref "Local" 2), check 0 (ref "StorageLocal" (-1000001)) (ref "StorageLocal" (-2000001))] (0,-1,-1)
    , simple "old storage is not replacement storage" owners baseContext [assign (-1000001) (ref "Local" 1), assign 1 (ref "Local" 2), check 0 (ref "StorageLocal" (-1000001)) (ref "StorageLocal" 1)] (1,0,2)
    , simple "unknown owner storage is unsupported" (locals [(1,1,Nothing)]) baseContext [check 0 (ref "StorageLocal" 1) (ref "StorageLocal" 1)] (2,0,0)
    , simple "copy of semantic-only binding stays semantic-only" (locals [(1,1,Nothing)]) baseContext [assign 2 (ref "Local" 1), check 0 (ref "StorageLocal" 2) (ref "StorageLocal" 2)] (2,0,1)
    , simple "unmodeled owning transition drops storage" owners baseContext [step "AssignSemantic" [("local",MInt 3),("value",ref "Local" 1)], check 0 (ref "Local" 3) (ref "Local" 1), check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 1)] (2,0,2)
    , simple "scalar constant is explicitly diagonal" (locals []) baseContext [assign 1 (ref "Term" 1003), check 0 (ref "StorageLocal" 1) (ref "Local" 1)] (0,-1,-1)
    , simple "unknown term is not diagonal" (locals []) baseContext [assign 1 (ref "Term" 999), check 0 (ref "StorageLocal" 1) (ref "Local" 1)] (2,0,1)
    , simple "pair reference captures known identities" owners baseContext [assign 3 (pairRef 1 (Just 101)), check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 1)] (0,-1,-1)
    , simple "pair reference rejects unknown semantic id" owners baseContext [assign 3 (pairRef 9999 (Just 101))] (2,0,0)
    , simple "pair reference rejects unknown storage id" owners baseContext [assign 3 (pairRef 1 (Just 9999))] (2,0,0)
    , simple "missing local cannot default to zero" (locals []) baseContext [check 0 (ref "Local" 0) (ref "Term" 0)] (2,0,0)
    , simple "unknown reference cannot default to Term" owners baseContext [assign 3 (record "ValueRef::Unknown" [("term",MInt 0)])] (2,0,0)
    , simple "missing storage local id is malformed" owners baseContext [assign 3 (record "ValueRef::StorageLocal" [])] (2,0,0)
    , simple "wrong storage local id type is malformed" owners baseContext [assign 3 (record "ValueRef::StorageLocal" [("local",MBool False)])] (2,0,0)
    , simple "malformed pair ref is rejected" owners baseContext [assign 3 (record "ValueRef::Binding" [("value",record "ValueBinding" [("semantic",MInt 1)])])] (2,0,0)
    , simple "unknown step cannot become harmless havoc" owners baseContext [step "Unknown" []] (2,0,0)
    , simple "missing assign destination is malformed" owners baseContext [step "Assign" [("value",ref "Local" 1)]] (2,0,0)
    , simple "malformed local pair is rejected" (MList [record "LocalBinding" [("local",MInt 1),("value",MInt 1)]]) baseContext [] (2,0,-1)
    , simple "missing pair storage field is rejected" (MList [record "LocalBinding" [("local",MInt 1),("value",record "ValueBinding" [("semantic",MInt 1)])]]) baseContext [] (2,0,-1)
    , simple "wrong pair semantic type is rejected" (MList [record "LocalBinding" [("local",MInt 1),("value",record "ValueBinding" [("semantic",MBool False),("storage",missing)])]]) baseContext [] (2,0,-1)
    , simple "unknown storage variant is rejected" (MList [record "LocalBinding" [("local",MInt 1),("value",record "ValueBinding" [("semantic",MInt 1),("storage",record "ValueLookup::Unknown" [])])]]) baseContext [] (2,0,-1)
    , simple "missing Found storage term is rejected" (MList [record "LocalBinding" [("local",MInt 1),("value",record "ValueBinding" [("semantic",MInt 1),("storage",record "ValueLookup::Found" [])])]]) baseContext [] (2,0,-1)
    , simple "duplicate local bindings fail closed" (locals [(1,1,Just 101),(1,1,Just 102)]) baseContext [] (2,0,-1)
    , simple "HashMap pair transport" hashOwners baseContext [check 0 (ref "StorageLocal" 1) (ref "StorageLocal" 1)] (0,-1,-1)
    , simple "HashMap count mismatch is rejected" (record "HashMap" [("buckets",MList []),("count",MInt 1)]) baseContext [] (2,0,-1)
    , simple "storage id participates in explicit freshness" (locals [(1,1,Just (-7000))]) baseContext [step "Apply" [("local",MInt 3),("result",MInt (-7000)),("function",MInt 900),("arguments",MList [])]] (2,0,0)
    , simple "storage minimum integer exhausts freshness closed" (locals [(1,1,Just (-9223372036854775808))]) baseContext [step "Havoc" [("local",MInt 3)]] (2,0,0)
    , simple "field wrapper retains content" wrapperLocals wrapperContext [project 3 800 (ref "Local" 1),project 4 800 (ref "Local" 2),check 0 (ref "Local" 3) (ref "Local" 4)] (0,-1,-1)
    , simple "field wrapper cannot recover storage from equal content" wrapperLocals wrapperContext [project 3 800 (ref "Local" 1),project 4 800 (ref "Local" 2),check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 4)] (1,0,2)
    , simple "field wrapper returns original child storage" wrapperLocals wrapperContext [project 3 800 (ref "Local" 1),check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 5)] (0,-1,-1)
    , simple "copied field view retains storage" wrapperLocals wrapperContext [project 3 800 (ref "Local" 1),assign 4 (ref "Local" 3),check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 4)] (0,-1,-1)
    , simple "unknown field operation is unsupported" owners baseContext [project 3 800 (ref "Local" 1)] (2,0,0)
    , simple "field of semantic-only wrapper cannot expose storage" (locals [(1,10,Nothing)]) wrapperContext [project 3 800 (ref "Local" 1),check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 3)] (2,0,1)
    , joinCase "mixed join preserves semantic equality" owners [assign 3 (ref "Local" 1)] [assign 3 (ref "Local" 2)] [check 0 (ref "Local" 3) (ref "Local" 1)] (0,-1,-1)
    , joinCase "mixed join does not inherit left storage" owners [assign 3 (ref "Local" 1)] [assign 3 (ref "Local" 2)] [check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 1)] (1,3,0)
    , joinCase "same-owner join preserves storage" owners [assign 3 (ref "Local" 1)] [assign 3 (ref "Local" 1)] [check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 1)] (0,-1,-1)
    , joinCase "join with missing storage loses storage" owners [assign 3 (ref "Local" 1)] [step "AssignSemantic" [("local",MInt 3),("value",ref "Local" 2)]] [check 0 (ref "StorageLocal" 3) (ref "StorageLocal" 3)] (2,3,0)
    , joinCase "mixed join preserves stable old snapshot" owners [assign 3 (ref "Local" 1),assign (-10) (ref "Local" 1)] [assign 3 (ref "Local" 2),assign (-10) (ref "Local" 1)] [check 0 (ref "StorageLocal" (-10)) (ref "StorageLocal" 1)] (0,-1,-1)
    , joinCase "joined pairs remain nonvacuous" owners [assign 3 (ref "Local" 1)] [assign 3 (ref "Local" 2)] [check 0 (ref "Term" 1000) (ref "Term" 1001)] (1,3,0)
    ])
  where
    edgeContext = context [] [] [800] [] []
    reusedContext = context [application 10 800 [1],application 20 800 [-9223372036854775808]] [] [800] [] []
    edgeTemplateContext = context [application 200 (-14) [101,1002]] [constant 1002 0 0,constant 1003 0 1,constant 1004 0 7] [] [] []
    edgeTemplate = record "ForallTemplate" [("id",MInt 2000),("nodes",MList [node 0 (ref "Term" 0) [],node 1 (ref "StorageLocal" (-10)) [],
        node 1 (ref "Term" 1002) [],node 1 (ref "Term" 1003) [],node 2 (ref "Term" 0) [1,0],node 1 (ref "Term" 1004) [],
        record "TemplateNode" [("kind",MInt 2),("function",MInt (-1)),("value",ref "Term" 0),("arguments",MList [MInt 4,MInt 2])]]),
        ("guards",MList [relation 3 2 0,relation 2 0 3]),("body",relation 0 6 5)]
    edgeTemplateSteps = [assign (-10) (ref "Local" 1),step "AssumeForall" [("template",edgeTemplate)],check 0 (ref "Term" 200) (ref "Term" 1004)]
    fallbackApplications = [application 10 (-17) [1,1002,1004],application 200 (-14) [10,500]]
    fallbackConstants = [constant 1002 0 0,constant 1004 0 7]
    fallbackContext = context fallbackApplications fallbackConstants [] [] []
    fallbackReusedContext = context (fallbackApplications ++ [application 201 (-14) [1,500]]) fallbackConstants [] [] []
    boundsContext = context [application 1 (-12) [1003],application 1003 (-13) [1],application 1004 900 [101]]
        [constant 1002 0 0,constant 1003 0 1,constant 1004 0 2] [] [] []
    boundsSteps index = [step "ApplyFresh" [("local",MInt 3),("function",MInt (-13)),("arguments",MList [ref "Local" 1])],
        step "ApplyFresh" [("local",MInt 4),("function",MInt 900),("arguments",MList [ref "StorageLocal" 1])],
        check 2 (ref "Term" 1002) (ref "Local" 4),check 2 (ref "Term" index) (ref "Local" 4),check 2 (ref "Term" index) (ref "Local" 3)]
    templateContext = context [] [constant 1002 0 0,constant 1003 0 1,constant 1004 0 7] [] [] []
    node kind value arguments = record "TemplateNode" [("kind",MInt kind),("function",MInt (-14)),("value",value),("arguments",MList (map MInt arguments))]
    relation kind left right = record "TemplateRelation" [("relation",MInt kind),("left",MInt left),("right",MInt right)]
    template = record "ForallTemplate" [("id",MInt 2000),("nodes",MList [node 0 (ref "Term" 0) [],node 1 (ref "StorageLocal" (-10)) [],
        node 1 (ref "Term" 1002) [],node 1 (ref "Term" 1003) [],node 2 (ref "Term" 0) [1,0],node 1 (ref "Term" 1004) []]),
        ("guards",MList [relation 3 2 0,relation 2 0 3]),("body",relation 0 4 5)]
    templateSteps target = [assign (-10) (ref "Local" 1),step "AssumeForall" [("template",template)],assign 1 (ref "Local" 2),
        step "ApplyFresh" [("local",MInt 3),("function",MInt (-14)),("arguments",MList [ref "StorageLocal" target,ref "Term" 1002])],
        check 0 (ref "Local" 3) (ref "Term" 1004)]
    hashOwners = record "HashMap" [("buckets",MList [MList [record "Entry" [("key",MInt 1),("value",binding 1 (Just 101))]]]),("count",MInt 1)]
    wrapperLocals = locals [(1,10,Just 110),(2,11,Just 111),(5,1,Just 101),(6,1,Just 102)]
    selection = record "ConstructorField" [("constructor",MInt 700),("field",MInt 800),("index",MInt 0)]
    wrapperContext = context [application 10 700 [1],application 11 700 [1],application 110 700 [101],application 111 700 [102]] [constant 1000 1 1,constant 1001 1 0] [800] [700] [selection]

encoded :: PairCase -> Either String String
encoded (_, bindings, ctx, blocks, _) = serializeFunction (MList blocks, record "ExecutionState" [("context",ctx),("locals",bindings),("templates",MList [])],0)

testNativePaired :: Test
testNativePaired = TestList "testNativePaired"
    ([TestCase name (protocol fixture) | fixture@(name,_,_,_,_) <- pairedCases] ++
     [TestCase name (sourceCase expected source) | (name,expected,source) <- sourceCases])
  where
    protocol fixture@(_,_,_,_,expected) = case encoded fixture of
        Left err -> pure (Just ("Serialization failed: " ++ err))
        Right text -> do
            cold <- runValidator [text]
            first <- verdicts True [text]
            before <- validationCacheHits
            repeated <- verdicts True [text]
            after <- validationCacheHits
            pure $ case (cold,first,repeated) of
                (Ok native,Ok cached,Ok again)
                    | Map.lookup 0 native == Just expected && cached == [Just expected] && again == cached && after > before -> Nothing
                _ -> Just ("Expected native/cached/repeated " ++ show expected ++ ", got " ++ show (cold,first,repeated))
    sourceCase expected source = case lowerSource True source of
        Error err -> pure (Just ("Source setup failed: " ++ err))
        Ok program -> case verifyProgram program of
            Error err -> pure (Just ("MIR setup failed: " ++ err))
            Ok () -> do
                results <- mapM (evaluate . ($ program)) [validateCompiledUncached,validateCompiled,validateCompiled]
                pure $ if all (matches expected) results then Nothing else Just ("Unexpected native source results: " ++ show results)
    matches True (Ok ()) = True
    matches False (Error err) = "Could not prove" `isInfixOf` err
    matches _ _ = False
    sourceCases =
        [("source default list semantics remain valid",True,"xs=[1,2]; ys=clone(xs); affirm xs=ys; affirm get(ys,1)=2; return 0;")
        ,("source false list claim is rejected",False,"xs=[1,2]; affirm get(xs,1)=3; return 0;")
        ,("source old/header semantic snapshots remain valid",True,"fn same(xs:&mut List<Int>)->Int [{ define entry=xs; }] [{ affirm xs=entry; affirm xs=old(xs); }] { *xs=clone(*xs); return 0; }; xs=[1,2]; same(&mut xs); affirm get(xs,1)=2; return 0;")
        ,("source scalar field wrapper remains valid",True,"struct W { xs:List<Int> }; a=W { xs:[1,2] }; define saved=a.xs; affirm get(saved,0)=1; return 0;")]
