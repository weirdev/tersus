module TestNativeProofGuards(testNativeProofGuards) where
import Compile(lowerSource)
import Control.Exception(evaluate)
import Data.List(isInfixOf)
import qualified MirHousekeeping as H
import TestHarness(Test(..))
import Utils(Result(..))
import ValidatorNative(validateCompiledUncached,validateCompiled)

count="fn count(xs:&List<Int>)->Int[{}][{affirm return=size(xs);}] {return size(xs);};"
positive="fn positive(xs:&List<Int>,i:Int)->Int[{affirm i>0;}][{affirm return=i;}] {return i;};"
guard i=positive++"fn check(xs:&List<Int>)->Int[{}][{affirm forall j where j>="++i++",j<size(xs),positive(xs,j)>0:j>=0;}]{return 0;};return check([7,7]);"
testNativeProofGuards=TestList "testNativeProofGuards" [TestCase name(test expected source)|(name,expected,source)<-
 [("concrete readonly CFn guard retains its declared size facts",Nothing,count++"fn check(xs:&List<Int>)->Int[{}][{affirm forall j where j>=0,j<count(xs):j<size(xs);}]{return 0;};return check([7,7]);")
 ,("a call-bearing guard cannot prove its own precondition",Just "Could not prove",guard "0")
 ,("independent range guards prove the actual call precondition",Nothing,guard "1")
 ,("guard callee ENS must validate against its own body",Just "Could not prove","fn count(xs:&List<Int>)->Int[{}][{affirm return=size(xs);}] {return 99;};fn check(xs:&List<Int>)->Int[{}][{affirm forall j where j>=0,j<count(xs):j<size(xs);}]{return 0;};return check([7,7]);")
 ,("an unadvertised callee body cannot supply a guard value",Just "Could not prove","fn count(xs:&List<Int>)->Int {return size(xs);};fn check(xs:&List<Int>)->Int[{}][{affirm forall j where j>=0,j<count(xs):j<size(xs);}]{return 0;};return check([7,7]);")
 ,("a writer guard is unavailable before claims",Just "validator does not model","fn write(i:Int)->Int{d=writeByte(65);return i;};fn check()->Int[{affirm forall j where j>=0,j<2,write(j)>=0:true;}][{}]{return 0;};return 0;")
 ,("a transitive writer guard is unavailable",Just "validator does not model","fn write(i:Int)->Int{d=writeByte(65);return i;};fn outer(i:Int)->Int{return write(i);};fn check()->Int[{}][{affirm forall j where j>=0,j<2:outer(j)=outer(j);}]{return 0;};return 0;")
 ,("a diverging guard is unavailable",Just "validator does not model","fn slow(i:Int)->Int ~ {return i;};fn check()->Int[{}][{affirm forall j where j>=0,j<2,slow(j)>=0:true;}]{return 0;};return 0;")
 ,("an unknown function target cannot become proof-pure",Just "validator does not model","fn outer(f:fn(Int)->Int,i:Int)->Int{return f(i);};fn check(f:fn(Int)->Int)->Int[{}][{affirm forall j where j>=0,j<2:outer(f,j)=outer(f,j);}]{return 0;};return 0;")
 ,("quantified guard facts do not escape the binder",Just "Could not prove: n > 0",count++"fn check(xs:&List<Int>,n:Int)->Int{affirm forall j where j>=0,j<count(xs),n>0:j<count(xs);affirm n>0;return 0;};return check([7],1);")
 ,("independent guard fact is usable only inside its forall",Nothing,"fn verify(n:Int)->Int{affirm forall j where j>=0,j<2,n>0:n>0;return 0;};return 0;")
 ,("forall exit preserves caller prior facts",Nothing,"fn verify(n:Int)->Int[{affirm n>0;}][{}]{affirm forall j where j>=0,j<2,n>1:n>1;affirm n>0;return 0;};return 0;")
 ,("sequential foralls cannot reuse earlier scoped guards",Just "Could not prove: n > 0","fn verify(n:Int)->Int{affirm forall j where j>=0,j<2,n>0:n>0;affirm forall k where k>=0,k<2:k>=0;affirm n>0;return 0;};return 0;")
 ,("actual String Growable conformance remains required",Nothing,"fn append(s:String,x:Byte)->String[{}][{affirm size(return)=size(s)+1;affirm forall j where j>=0,j<size(s):get(return,j)=get(s,j);}]{return push(s,x);};return append(\"ab\",99);")
 ,("direct unknown callback Requires is an explicit encoding refusal",Just "validator does not model","fn verify(f:fn(Int)->Int)->Int[{affirm forall j where j>=0,j<2:f(j)=f(j);}][{}]{return 0;};return 0;")
 ,("local writer alias in an unused input cannot disappear",Just "validator does not model","fn write(i:Int)->Int{d=writeByte(65);return i;};fn verify()->Int[{define f=write;affirm forall j where j>=0,j<2,f(j)>=0:true;}][{}]{return 0;};return 0;")
 ,("inline call contract does not silently skip unavailable forall work",Just "validator does not model","fn write(i:Int)->Int{d=writeByte(65);return i;};fn bad()->Int[{}][{affirm forall j where j>=0,j<2,write(j)>=0:true;}]{return 0;};fn verify()->Int[{affirm bad()=0;}][{}]{return 0;};return 0;")
 ]]
 where
 test expected source=case lowerSource True source of
  Error err->pure(Just("Earlier Source error "++err))
  Ok program->case H.verifyProgram program of
   Error err->pure(Just("Earlier MIR error "++err))
   Ok()->do
    results<-mapM(evaluate.($program))[validateCompiledUncached,validateCompiled,validateCompiled]
    pure$if all(matches expected)results then Nothing else Just("Wrong guard result "++show results)
 matches Nothing(Ok())=True
 matches(Just needle)(Error err)=needle`isInfixOf`err
 matches _ _=False
