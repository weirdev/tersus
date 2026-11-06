module TestForallDomains (testForallDomains) where

import Compile (lowerSource)
import Control.Exception (evaluate)
import Data.List (isInfixOf)
import qualified MirHousekeeping as H
import MirEval (MirValue(..))
import qualified SelfHostedMir as S
import TestHarness (Test(..))
import Utils (Result(..))
import ValidatorNative (validateCompiled, validateCompiledUncached)

restricted guards index values = "fn verify(xs:&List<Int>)->Int[{affirm size(xs)=2;affirm forall j where " ++ guards ++ ":get(xs,j)=7;}][{affirm return=7;}] {return get(xs," ++ index ++ ");};return verify(" ++ values ++ ");"
frame guards index a b = "fn verify(a:&List<Int>,b:&List<Int>)->Int[{affirm size(a)=2;affirm size(b)=2;affirm forall j where " ++ guards ++ ":get(a,j)=get(b,j);}] [{affirm return=get(b," ++ index ++ ");}] {return get(a," ++ index ++ ");};return verify(" ++ a ++ "," ++ b ++ ");"
maximumEndpoint = "fn verify(a:&List<Int>,b:&List<Int>)->Int[{affirm forall j where j>=0,j<9223372036854775807,j!=9223372036854775807:get(a,j)=get(b,j);}] [{}] {return 0;};return 0;"

testForallDomains = TestList "testForallDomains"
    ([TestCase label (validate expected text) | (label,expected,text) <-
        [("an extra equality guard cannot promise another list element",Just "Could not prove",restricted "j>=0,j<size(xs),j=0" "1" "[7,0]")
        ,("the ordinary equality-guard template retains its valid element",Nothing,restricted "j>=0,j<size(xs),j=0" "0" "[7,0]")
        ,("reversed equality and bounds retain the restricted domain",Just "Could not prove",restricted "0<=j,size(xs)>j,0=j" "1" "[7,0]")
        ,("a strict reversed lower bound does not include its endpoint",Just "Could not prove",restricted "0<j,j<size(xs)" "0" "[0,7]")
        ,("a strict lower bound still proves an interior element",Nothing,restricted "0<j,j<size(xs)" "1" "[0,7]")
        ,("reversed inclusive lower bound retains the endpoint",Nothing,restricted "0<=j,j<size(xs)" "0" "[7,7]")
        ,("multiple upper bounds cannot widen an intersection",Just "Could not prove",restricted "j>=0,j<size(xs),j<1" "1" "[7,0]")
        ,("a multiple-bound template keeps its valid intersection",Nothing,restricted "j>=0,j<size(xs),j<1" "0" "[7,0]")
        ,("a plain full-range constant promise is retained",Nothing,restricted "j>=0,j<size(xs)" "1" "[7,7]")
        ,("an excluded lower endpoint retains the other slot",Nothing,frame "j>=0,j<2,j!=0" "1" "[0,7]" "[1,7]")
        ,("an excluded upper endpoint needs no successor",Nothing,frame "j>=0,j<2,j!=2" "1" "[7,7]" "[7,7]")
        ,("an out-of-range exclusion cannot widen a two-list fact",Just "Could not prove",frame "j>=0,j<1,j!=10" "1" "[7,0]" "[7,1]")
        ,("maximum Int endpoint has no successor arithmetic",Nothing,maximumEndpoint)
        ]]
    ++ [TestCase "maximum endpoint ledger contains one full frame and no plus" maximumLedger
       ,TestCase "restricted domain ledger has a guarded template, not a range shortcut" restrictedLedger])
  where
    validate expected text = case lowerSource True text of
        Error err -> pure (Just ("Earlier Source failure " ++ err))
        Ok program -> case H.verifyProgram program of
            Error err -> pure (Just ("Earlier MIR failure " ++ err))
            Ok () -> do
                verdicts <- mapM (evaluate . ($ program)) [validateCompiledUncached,validateCompiled,validateCompiled]
                pure $ if all (matches expected) verdicts then Nothing else Just ("Wrong quantified-domain verdict " ++ show verdicts)
    matches Nothing (Ok ()) = True
    matches (Just needle) (Error err) = needle `isInfixOf` err
    matches _ _ = False
    encoded text action = case lowerSource True text of
        Error err -> pure (Just err)
        Ok p -> case S.encode p of
            Left err -> pure (Just err)
            Right entries -> pure (action [blocks | ("verify",(blocks,_,_)) <- entries])
    stepsOf (MData _ fields) = [steps | Just (MList steps) <- [lookup "steps" fields]] ++ concatMap (stepsOf . snd) fields
    stepsOf (MList values) = concatMap stepsOf values
    stepsOf _ = []
    maximumLedger = encoded maximumEndpoint $ \blocks ->
        let apps = [f | block <- blocks, steps <- stepsOf block, MData "ExecutionStep::ApplyFresh" fields <- steps, Just (MInt f) <- [lookup "function" fields]]
         in if (-1) `notElem` apps && length (filter (==(-30)) apps)==1 then Nothing else Just "Upper endpoint emitted successor or extra split facts"
    restrictedLedger = encoded (restricted "j>=0,j<size(xs),j=0" "0" "[7,0]") $ \blocks ->
        let steps = concat [part | block <- blocks,part <- stepsOf block]
            shortcuts = [() | MData "ExecutionStep::ApplyFresh" fields <- steps,Just (MInt f) <- [lookup "function" fields],f `elem` [-30,-31,-32,-33]]
            templates = [() | MData "ExecutionStep::AssumeForall" _ <- steps]
         in if null shortcuts && not (null templates) then Nothing else Just "Restricted forall escaped into a full-range shortcut"
