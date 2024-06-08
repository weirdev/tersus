module TestTersus where

import Data.List (delete)
import Data.Map (Map, findWithDefault, fromList, insert, insertWith, lookup)

import Parse
import Proof
import TersusTypes

-- Core Test data structures
-- Test result is possible error output, else success
type TestResult = Maybe String
data Test = TestCase String TestResult | TestList String [Test] deriving (Show)

type IotaAssignments = Map Iota Iota
type IotaFailedAssignments = Map Iota [Iota]
type VarAssignedProof = Proof (Either Iota String)

-- (assignments: {expectedIota: validationIota},
-- failedAssignmens: {expectedIota: [validationIota]},
--  expectedProofsToCheck, validationProofs, prevStates)
newtype SATProofsState = SATProofsState (IotaAssignments, IotaFailedAssignments, [VarAssignedProof], [VarAssignedProof], [SATProofsState])

-- (assignments: {expectedIota: validationIota},
-- failedAssignmens: {expectedIota: [validationIota]},
-- availableIotasFromVal, prevState)
newtype SATProofState = SATProofState (IotaAssignments, IotaFailedAssignments, [Iota], Maybe SATProofState)

assignments :: SATProofsState -> IotaAssignments
assignments (SATProofsState (a, _, _, _, _)) = a

failedAssignments :: SATProofsState -> IotaFailedAssignments
failedAssignments (SATProofsState (_, a, _, _, _)) = a

expectedProofsToCheck :: SATProofsState -> [VarAssignedProof]
expectedProofsToCheck (SATProofsState (_, _, e, _, _)) = e

validationProofs :: SATProofsState -> [VarAssignedProof]
validationProofs (SATProofsState (_, _, _, v, _)) = v

prevStates :: SATProofsState -> [SATProofsState]
prevStates (SATProofsState (_, _, _, _, p)) = p

-- Core Test helper functions

testCaseSeq :: String -> [TestResult] -> Test
testCaseSeq s results = TestList s (zipWith (\ i r -> TestCase (s ++ show i) r) [0 ..] results)

runTest :: Test -> IO ()
runTest (TestCase s r) =
    putStrLn $
        s
            ++ " - "
            ++ ( case r of
                    Nothing -> "Pass"
                    Just e -> "Fail\n" ++ e
               )
runTest (TestList s ts) = do
    putStrLn $ "Running test list: " ++ s
    mapM_ runTest ts
    putStrLn ""

testAssertEq :: (Show a, Eq a) => a -> a -> TestResult
testAssertEq actual expected =
    if actual == expected
        then Nothing
        else Just $ "Expected: " ++ show expected ++ "\nGot: " ++ show actual

-- Tests
testParseSimpleAssign :: Test
testParseSimpleAssign =
    let parseOutput = parseStatementBlock "assign x = 5"
     in let result = case parseOutput of
                Left _ -> Nothing
                Right parsed -> testAssertEq parsed [Assign "x" (Val (VInt 5))]
         in TestCase "testParseSimpleAssign" result

testParseComplexAssign :: Test
testParseComplexAssign =
    let parseOutput = parseStatementBlock "assign x = size([5]); assign yy = 1 - 1;"
     in let result = case parseOutput of
                Left _ -> Nothing
                Right parsed -> testAssertEq parsed [Assign "x" (F Size [Val (VIntList [5])]), Assign "yy" (F Minus [Val (VInt 1), Val (VInt 1)])]
         in TestCase "testParseComplexAssign" result

testParse :: Test
testParse = TestList "testParse" [testParseSimpleAssign, testParseComplexAssign]

evalFCHelper :: [Statement] -> [(Variable, Value)] -> TestResult
evalFCHelper stmts expected =
    let (vals, _, _) = evaluate stmts
     in testAssertEq vals (Data.Map.fromList expected)

testEvaluateFullContext :: Test
testEvaluateFullContext =
    testCaseSeq
        "testEvaluateFullContext"
        [ evalFCHelper [Assign "x" (F Size [Val (VIntList [5])])] [("x", VInt 1)]
        , evalFCHelper [Assign "x" (F Size [Val (VIntList [5])]), Assign "y" (F Minus [Val (VInt 1), Val (VInt 1)])] [("x", VInt 1), ("y", VInt 0)]
        ]

-- ss :: SATProofsState -> SATProofsState
-- ss (a, fa, e, v, p) =

-- Assignment must be done prior to calling
subproofgraph :: VarAssignedProof -> [VarAssignedProof] -> Bool
subproofgraph _ [] = False
subproofgraph p (vp:vps) =
    let
     in if i == p then True else subproofgraph a p xs

-- assignments -> failedAssignments -> availableIotasFromVal ->
-- proofFromExpected -> (VarAssignedProof, assignments, failedAssignments, availableIotas)
assignIotas :: SATProofState -> VarAssignedProof -> (Maybe VarAssignedProof, SATProofState)
assignIotas state (CTerm v) = (Just (CTerm v), state)
assignIotas (SATProofState (as, fasm, ai, ps)) (ATerm ivar) = case ivar of
    Left i -> case Data.Map.lookup i as of
        Just i' -> (Just (ATerm (Left i')), SATProofState (as, fasm, ai, ps)) -- already assigned, replace with assigned iota
        -- Not assigned, pull next available validation iota
        Nothing -> case nextValidAssignment ai (multimapLookup fasm i) of
            Just i' -> (Just (ATerm (Left i')), (insert i i' as, fasm, delete i' ai, Just (SATProofState (as, fasm, ai, ps)))) -- add to map, remove from available
            -- TODO: The failed assignment must be added on backtrack, not here
            -- On failure pass the failure state
            Nothing -> (Nothing, Just (SATProofState (as, fasm, ai, ps)))
    var -> (Just (ATerm var), (as, fasm, ai, SATProofState (as, fasm, ai, ps)))
assignIotas state (FApp2 f args) = let (assignedArgs, state') = statefulMap state (map (flip assignIotas) ps) in
    case assignedArgs of
        Just args' -> (Just (FApp2 f args'), state')
        Nothing -> (Nothing, state)

-- TODO: This should probably be a monad
-- state -> [valuesToCalculateGivenState] -> (gen new state on failure) -> (Maybe [results], newState)
statefulMap :: s -> [s -> (Maybe b, s)] -> (s -> Maybe s) -> (Maybe [b], s)
statefulMap s [] _ = (Just [], s)
statefulMap s (f:fs) nsf = let (b, s') = f s in case b of
    Just b' -> let (bs, s'') = statefulMap s' nsf in case bs of
        Just bs' -> (Just (b' : bs'), s'')
        Nothing -> (Nothing, s'')
    Nothing -> (Nothing, s')

multimapLookup :: (Ord k, Ord v) => Map k [v] -> k -> [v]
multimapLookup m k = findWithDefault [] k m

multimapInsert :: (Ord k, Ord v) => Map k [v] -> k -> v -> Map k [v]
multimapInsert m k v = insertWith (++) k [v] m

-- availableIotasFromVal -> failedAssignmentsForExpectedIota -> newAssignment
nextValidAssignment :: [Iota] -> [Iota] -> Maybe Iota
nextValidAssignment [] _ = Nothing
nextValidAssignment (i : is) fas = if i `elem` fas then nextValidAssignment is fas else Just i

-- TODO: Can we check this without requiring a particular iota naming?
-- validateFCHelper :: [Statement] ->  -> TestResult
-- validateFCHelper stmts expected =
--     let (vals, _, _) = evaluate stmts
--      in testAssertEq vals (Data.Map.fromList expected)

testValidateFullContext :: Test
testValidateFullContext =
    testCaseSeq
        "testValidateFullContext"
        [ evalFCHelper [Assign "x" (F Size [Val (VIntList [5])])] [("x", VInt 1)]
        , evalFCHelper [Assign "x" (F Size [Val (VIntList [5])]), Assign "y" (F Minus [Val (VInt 1), Val (VInt 1)])] [("x", VInt 1), ("y", VInt 0)]
        ]

main :: IO ()
main = do
    runTest testParse
    runTest testEvaluateFullContext