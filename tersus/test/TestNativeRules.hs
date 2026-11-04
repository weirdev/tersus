module TestNativeRules (testNativeRules, nativeRuleCases) where

import Control.Exception (evaluate)
import Data.List (isInfixOf)
import Compile (lowerSource)
import MirHousekeeping (verifyProgram)
import ValidatorNative (validateCompiled, validateCompiledUncached)
import TestHarness (Test(..))
import Utils (Result(..))

nativeRuleCases :: [(String, Bool, String)]
nativeRuleCases =
    [ ("forged lexical body", False, "fn helper(x:Int)->Int [{ }] [{ affirm return=x; }] { return x; }; proof forged(x) [{ }] [{ affirm x=0; }] { define y=helper(x); }; rewrite forged 1; affirm 1=0; return 0;")
    , ("pure global helper", True, "fn helper(x:Int)->Int [{ }] [{ affirm return=x; }] { return x; }; proof identity(x) [{ }] [{ affirm helper(x)=x; }] { define y=helper(x); affirm y=x; }; rewrite identity 7; affirm helper(7)=7; return 0;")
    , ("earlier header guard", False, "proof positive(x) [{ define a=x; affirm a>0; define a=1; }] [{ affirm x>0; }] {}; rewrite positive 0; affirm 0>0; return 0;")
    , ("sequential positive", True, "proof positive(x) [{ define a=x; affirm a>0; define a=1; }] [{ affirm x>0; }] {}; rewrite positive 2; affirm 2>0; return 0;")
    , ("final header version", True, "proof final(x) [{ define a=x; affirm a=x; define a=1; }] [{ affirm a=1; }] {}; rewrite final 9; return 0;")
    , ("body cannot replace header output", False, "proof wrong(x) [{ define a=x; }] [{ affirm a=0; }] { define a=0; }; rewrite wrong 1; affirm 1=0; return 0;")
    , ("own pending rule", False, "proof circular(x) [{ }] [{ affirm x=0; }] { rewrite circular x; }; rewrite circular 1; affirm 1=0; return 0;")
    , ("future pending rule", False, "proof first(x) [{ }] [{ affirm x=0; }] { rewrite second x; }; proof second(x) [{ }] [{ affirm x=0; }] { rewrite first x; }; rewrite first 1; affirm 1=0; return 0;")
    , ("earlier checked rule", True, "proof one(x) [{ affirm x=1; }] [{ affirm x=1; }] {}; proof two(x) [{ affirm x=1; }] [{ affirm x=1; }] { rewrite one x; }; rewrite two 1; affirm 1=1; return 0;")
    , ("duplicate rule", False, "proof same(x) [{ }] [{ affirm x=x; }] {}; proof same(x) [{ }] [{ affirm x=0; }] {}; rewrite same 1; affirm 1=0; return 0;")
    , ("caller private facts", False, "x=0; proof private(x) [{ }] [{ affirm x=0; }] {}; rewrite private x; affirm x=0; return 0;")
    , ("strong function-rule cycle", False, "fn helper(x:Int)->Int [{ }] [{ affirm return=x; affirm x=0; }] { rewrite circular x; return x; }; proof circular(x) [{ }] [{ affirm x=0; }] { define y=helper(x); }; rewrite circular 1; affirm 1=0; return 0;")
    , ("proof-only transitive cycle", False, "fn inner(x:Int)->Int [{ }] [{ affirm return=x; affirm x=0; }] { rewrite circular x; return x; }; fn helper(x:Int)->Int [{ }] [{ affirm return=x; affirm x=0; }] { define y=inner(x); return x; }; proof circular(x) [{ }] [{ affirm x=0; }] { define y=helper(x); }; rewrite circular 1; affirm 1=0; return 0;")
    , ("helper uses prior checked rule", True, "proof same(x) [{ }] [{ affirm x=x; }] {}; fn helper(x:Int)->Int [{ }] [{ affirm return=x; }] { rewrite same x; return x; }; proof identity(x) [{ }] [{ affirm helper(x)=x; }] { define y=helper(x); affirm y=x; }; rewrite identity 7; affirm helper(7)=7; return 0;")
    ]

testNativeRules :: Test
testNativeRules = TestList "testNativeRules" [TestCase name (check name expected source) | (name, expected, source) <- nativeRuleCases]
  where
    rejections =
        [ ("forged lexical body", "Could not prove: x = 0 (in rule forged)")
        , ("earlier header guard", "Could not prove: a > 0 (in main)")
        , ("body cannot replace header output", "Could not prove: a = 0 (in rule wrong)")
        , ("own pending rule", "does not model yet: the body of proof rule circular")
        , ("future pending rule", "does not model yet: the body of proof rule first")
        , ("duplicate rule", "does not model yet: an axiom or proof rule")
        , ("caller private facts", "Could not prove: x = 0 (in rule private)")
        , ("strong function-rule cycle", "does not model yet: the body of proof rule circular")
        , ("proof-only transitive cycle", "does not model yet: the body of proof rule circular")
        ]
    check name expected source = case lowerSource True source of
        Error err -> pure (Just ("Source guard not reached: " ++ err))
        Ok program -> do
            shape <- evaluate (verifyProgram program)
            case shape of
                Error err -> pure (Just ("MIR guard not reached: " ++ err))
                Ok () -> do
                    results <- mapM (\(label, validator) -> do
                        verdict <- evaluate (validator program)
                        pure $ case verdict of
                            Ok () | expected -> Nothing
                            Error err | not expected, Just fragment <- lookup name rejections, fragment `isInfixOf` err -> Nothing
                            _ -> Just (label ++ ": unexpected native verdict " ++ show verdict))
                        [("uncached", validateCompiledUncached), ("cached-first", validateCompiled), ("cached-repeat", validateCompiled)]
                    pure (case [err | Just err <- results] of err : _ -> Just err; [] -> Nothing)
