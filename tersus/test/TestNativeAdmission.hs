module TestNativeAdmission (testNativeAdmission, admissionCases, encodedAdmission) where

import qualified Data.Map.Strict as Map
import Data.List (isPrefixOf, tails)
import MirEval (MirValue(..))
import TestHarness (Test(..))
import ValidatorNative (runValidator, serializeFunction)
import Utils (Result(..))

record :: String -> [(String, MirValue)] -> MirValue
record = MData

row :: Integer -> [Integer] -> Bool -> Bool -> Bool -> MirValue
row function dependencies io diverges unknown = record "ProofFunction"
    [("function", MInt function), ("dependencies", MList (map MInt dependencies)),
     ("io", MBool io), ("userMayDiverge", MBool diverges), ("unknown", MBool unknown)]

admit :: Integer -> MirValue
admit function = record "ExecutionStep::AdmitProofCall" [("function", MInt function)]

admissionCases :: [(String, [MirValue], [MirValue], [MirValue], (Int,Int,Int))]
admissionCases =
    [ ("pure complete invocation", [row 1 [2] False False False, row 2 [] False False False], [], [admit 1], (0,-1,-1))
    , ("direct IO", [row 1 [] True False False], [], [admit 1], (1,0,0))
    , ("transitive IO", [row 1 [2] False False False, row 2 [3] False False False, row 3 [] True False False], [], [admit 1], (1,0,0))
    , ("user divergence", [row 1 [] False True False], [], [admit 1], (1,0,0))
    , ("transitive user divergence", [row 1 [2] False False False, row 2 [] False True False], [], [admit 1], (1,0,0))
    , ("unknown root", [row 1 [] False False True], [], [admit 1], (2,0,0))
    , ("unknown dependency", [row 1 [2] False False False, row 2 [] False False True], [], [admit 1], (2,0,0))
    , ("missing root", [], [], [admit 1], (2,0,0))
    , ("missing dependency", [row 1 [2] False False False], [], [admit 1], (2,0,0))
    , ("duplicate root", [row 1 [] False False False, row 1 [] False False False], [], [admit 1], (2,0,0))
    , ("conflicting root", [row 1 [] False False False, row 1 [] True False False], [], [admit 1], (2,0,0))
    , ("pure cyclic graph", [row 1 [2] False False False, row 2 [1] False False False], [], [admit 1], (0,-1,-1))
    , ("unrelated cleanup is excluded", [row 1 [2] False False False, row 2 [] False False False, row 3 [] True False False], [], [admit 1], (0,-1,-1))
    , ("logical equality cannot admit IO identifier", [row 1 [] False False False, row 2 [] True False False], [record "EqualityFact" [("left",MInt 1),("right",MInt 2)]], [admit 2], (1,0,0))
    , ("malformed row flags", [record "ProofFunction" [("function",MInt 1),("dependencies",MList []),("io",MInt 0),("userMayDiverge",MBool False),("unknown",MBool False)]], [], [admit 1], (2,0,0))
    , ("malformed dependency type", [record "ProofFunction" [("function",MInt 1),("dependencies",MList [MBool False]),("io",MBool False),("userMayDiverge",MBool False),("unknown",MBool False)]], [], [admit 1], (2,0,0))
    , ("wrong row constructor", [record "NotProofFunction" [("function",MInt 1),("dependencies",MList []),("io",MBool False),("userMayDiverge",MBool False),("unknown",MBool False)]], [], [admit 1], (2,0,0))
    , ("missing admission id cannot default to zero", [row 0 [] False False False], [], [record "ExecutionStep::AdmitProofCall" []], (2,0,0))
    , ("malformed admission id", [row 0 [] False False False], [], [record "ExecutionStep::AdmitProofCall" [("function",MBool False)]], (2,0,0))
    , ("unknown step cannot become harmless havoc", [], [], [record "ExecutionStep::NotAdmit" []], (2,0,0))
    , ("metadata survives ordinary proof facts", [row 1 [2] False False False,row 2 [] False False False], [],
         [record "ExecutionStep::Proof" [("step",record "ProofStep::KnownEquality" [("left",MInt 10),("right",MInt 10)])],admit 1], (0,-1,-1))
    ]

encodedAdmission :: [MirValue] -> [MirValue] -> [MirValue] -> Either String String
encodedAdmission rows equalities firstSteps = serializeFunction (blocks, initial, 0)
  where
    context = record "ValidatorContext"
        [("equalities",MList equalities),("applications",MList []),("constants",MList []),
         ("orders",MList []),("different",MList []),("variants",MList []),("fieldFunctions",MList []),
         ("constructorFunctions",MList []),("constructorFields",MList []),("differences",MList []),
         ("proofFunctions",MList rows)]
    initial = record "ExecutionState" [("context",context),("locals",MList []),("templates",MList [])]
    apply = record "ExecutionStep::ApplyFresh" [("local",MInt 42),("function",MInt 2),("arguments",MList [])]
    defined = record "ExecutionStep::RequireDefined" [("value",record "ValueRef::Local" [("local",MInt 42)])]
    blocks = MList [record "ExecutionBlock" [("id",MInt 0),("steps",MList (firstSteps ++ [apply,defined])),("end",record "ExecutionEnd::Done" [])]]

testNativeAdmission :: Test
testNativeAdmission = TestList "testNativeAdmission"
    ([TestCase name (check rows equalities steps expected) | (name,rows,equalities,steps,expected) <- admissionCases]
        ++ [TestCase name (check [row identifier [] False False False] [] [admit identifier] (0,-1,-1))
           | (name,identifier) <- [("valid identifier zero",0), ("valid least integer identifier",-9223372036854775808), ("valid greatest integer identifier",9223372036854775807)]]
        ++ [TestCase name (wireCheck rows old new) | (name,rows,old,new) <- wireCases])
  where
    check rows equalities steps expected = case encodedAdmission rows equalities steps of
        Left err -> pure (Just ("Serialization failed: " ++ err))
        Right text -> nativeCheck text expected
    nativeCheck text expected = do
        outcome <- runValidator [text]
        pure $ case outcome of
            Error err -> Just ("Native setup/transport failed: " ++ err)
            Ok results | Map.lookup 0 results == Just expected -> Nothing
            Ok results -> Just ("Expected native status/block/step " ++ show expected ++ ", got " ++ show (Map.lookup 0 results))
    wireCheck rows old new = case encodedAdmission rows [] [admit 0] of
        Left err -> pure (Just ("Serialization failed: " ++ err))
        Right text -> case [i | (i,suffix) <- zip [0..] (tails text), old `isPrefixOf` suffix] of
            [at] -> nativeCheck (take at text ++ new ++ drop (at + length old) text) (2,-1,-1)
            found -> pure (Just ("Wire mutation must select exactly one token sequence, found " ++ show (length found)))
    wireCases =
        [ ("digitless admission payload", [row 0 [] False False False], "ExecutionStep::AdmitProofCall 1 i 0 ", "ExecutionStep::AdmitProofCall 1 i ")
        , ("sign-only admission payload", [row 0 [] False False False], "ExecutionStep::AdmitProofCall 1 i 0 ", "ExecutionStep::AdmitProofCall 1 i - ")
        , ("admission payload without delimiter", [row 0 [] False False False], "ExecutionStep::AdmitProofCall 1 i 0 ", "ExecutionStep::AdmitProofCall 1 i 0")
        , ("positive integer overflow", [row 0 [] False False False], "ExecutionStep::AdmitProofCall 1 i 0 ", "ExecutionStep::AdmitProofCall 1 i 9223372036854775808 ")
        , ("negative integer overflow", [row 0 [] False False False], "ExecutionStep::AdmitProofCall 1 i 0 ", "ExecutionStep::AdmitProofCall 1 i -9223372036854775809 ")
        , ("digitless row identifier", [row 0 [] False False False], "ProofFunction 5 i 0 l 0 ", "ProofFunction 5 i l 0 ")
        , ("digitless dependency identifier", [row 0 [0] False False False], "ProofFunction 5 i 0 l 1 i 0 ", "ProofFunction 5 i 0 l 1 i ")
        , ("digitless row flag", [row 0 [] False False False], "ProofFunction 5 i 0 l 0 b 0 ", "ProofFunction 5 i 0 l 0 b ")
        , ("nonboolean row flag", [row 0 [] False False False], "ProofFunction 5 i 0 l 0 b 0 ", "ProofFunction 5 i 0 l 0 b 2 ")
        , ("digitless admission field count", [row 0 [] False False False], "ExecutionStep::AdmitProofCall 1 i 0 ", "ExecutionStep::AdmitProofCall i 0 ")
        , ("negative admission field count", [row 0 [] False False False], "ExecutionStep::AdmitProofCall 1 i 0 ", "ExecutionStep::AdmitProofCall -1 i 0 ")
        , ("truncated final numeric payload", [row 0 [] False False False], "ExecutionEnd::Done 0 ", "ExecutionEnd::Done ")
        ]
