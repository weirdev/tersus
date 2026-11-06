module TestCanonicalRuleReplay(testCanonicalRuleReplay) where

import Compile(lowerSource)
import Control.Exception(evaluate)
import Data.List(isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Mir as M
import qualified MirHousekeeping as H
import Syntax
import TestHarness(Test(..))
import Utils(Result(..))
import ValidatorNative(validateCompiled,validateCompiledUncached)

positive :: String
positive="fn positive(x:Int)->Int[{affirm x>0;}][{affirm return=x;}]{return x;};"

testCanonicalRuleReplay :: Test
testCanonicalRuleReplay=TestList "testCanonicalRuleReplay" $
 [TestCase (mode++" canonical alias "++show actual)(canonical (originally mode expected) expected(source actual))
 |(mode,source)<-modes
 ,(actual,expected)<-[("0",Just "Could not prove"),("1",Nothing)]] ++
 [TestCase name(checked expected source)|(name,source,expected)<-replayCases] ++
 [TestCase "canonicalization respects a contract-local function shadow" shadowCanonical]
 where
 shadowCanonical=case lowerSource True "fn f(x:Int)->Int[{}][{affirm return=0;}]{return 0;};fn g(x:Int)->Int[{}][{affirm return=1;}]{return 1;};fn verify()->Int[{}][{define f=g;affirm f(0)=1;}]{return 0;};return 0;" of
  Error err->pure(Just("Earlier Source error "++err))
  Ok program->do
   let (converted,targets)=canonicalCalls program
       intended=[name|M.BasicBlock statements _<-Map.elems(M.fnBlocks(M.progMain program)),M.Ghost _(M.GhostFunction name "g" _)<-statements]
   if not(any(`elem`targets)intended) then pure(Just "The shadowed application did not retain its actual g declaration") else do
    original<-verdict Nothing program
    case original of
     Just err->pure(Just("Original shadow fixture failed: "++err))
     Nothing->verdict Nothing converted
 modes=
  [("assumption",\x->positive++"assume positive("++x++")="++x++";return 0;")
  ,("promise",\x->positive++"fn verify()->Int[{}][{define alias=positive;affirm alias("++x++")="++x++";}]{return 0;};return 0;")
  ,("axiom output",\x->positive++"axiom ax()[{}][{define alias=positive;affirm alias("++x++")="++x++";}];rewrite ax;return 0;")
  ,("assumed CheckRel",\x->positive++"fn verify()->Int[{rewrite checkRel positive("++x++")="++x++";}][{}]{return 0;};return 0;")
  ,("checked rule output",\x->positive++"proof output(x)[{affirm x>0;}][{define alias=positive;affirm alias(x)=x;}]{ };rewrite output "++x++";return 0;")
  ]
 -- (the validator written in Tersus does not model a function alias defined in a checked rule's output, so it
 -- refuses that fixture before canonicalization; the canonical form is checked as the others are)
 originally mode expected=if mode=="checked rule output" then Just "does not model yet" else expected
 canonical originalExpected expected source=case lowerSource True source of
  Error err->pure(Just("Earlier Source error "++err))
  Ok program->let
   (canonicalProgram,targets)=canonicalCalls program
   intended=[target|M.BasicBlock statements _<-Map.elems(M.fnBlocks(M.progMain program)),M.Ghost _(M.GhostFunction target "positive" _)<-statements]
   in if not(any(`elem`targets)intended) then pure(Just "The intended checked application was not canonicalized") else do
    original<-verdict originalExpected program
    case original of
     Just err->pure(Just("Original fixture failed before canonicalization: "++err))
     Nothing->verdict expected canonicalProgram
 checked expected source=case lowerSource True source of
  Error err->pure(Just("Earlier Source error "++err))
  Ok program->verdict expected program
 verdict expected program=case H.verifyProgram program of
  Error err->pure(Just("Earlier MIR error "++err))
  Ok()->do
   results<-mapM(evaluate.($program))[validateCompiledUncached,validateCompiled,validateCompiled]
   pure$if all(matches expected)results then Nothing else Just("Wrong canonical/replay result "++show results)
 matches Nothing(Ok())=True
 matches(Just needle)(Error err)=needle`isInfixOf`err
 matches _ _=False

canonicalCalls :: M.Program -> (M.Program,[String])
canonicalCalls program=(program{M.progMain=mainFn,M.progFunctions=Map.fromList functions},mainTargets++concat functionTargets)
 where
 (mainFn,mainTargets)=function(M.progMain program)
 (functions,functionTargets)=unzip[( (name,converted),targets )|(name,fn)<-Map.toList(M.progFunctions program),let(converted,targets)=function fn]
 mapped f xs=let(results,targets)=unzip(map f xs) in(results,concat targets)
 target env name=do
  M.Const(M.CFn original)<-Map.lookup name env
  fn<-Map.lookup original(M.progFunctions program)
  if M.fnName fn==original && null(M.fnTypeParams fn) && null(M.fnSizeParams fn) && all(`Map.member`M.fnLocals fn)(M.fnParams fn) then Just(original,fn) else Nothing
 function fn=let
  s=M.fnSpec fn
  (ins,inputEnv,inTargets)=clauses(M.specEnv s)(M.specRequires s)
  (outs,_,outTargets)=clauses inputEnv(M.specEnsures s)
  (blocks,blockTargets)=mapped(\(key,b)->let(converted,t)=block b in((key,converted),t))(Map.toList(M.fnBlocks fn))
  in(fn{M.fnSpec=s{M.specRequires=ins,M.specEnsures=outs},M.fnBlocks=Map.fromList blocks},inTargets++outTargets++blockTargets)
 block(M.BasicBlock statements end)=let(converted,targets)=mapped statement statements in(M.BasicBlock converted end,targets)
 statement(M.Ghost env(M.GhostValidation value))=let([converted],_,targets)=clauses env[value] in(M.Ghost env(M.GhostValidation converted),targets)
 statement(M.Ghost env(M.GhostAxiom name args ins outs))=let
  scoped=foldr Map.delete env args
  (inputs,inputEnv,t1)=clauses scoped ins
  (outputs,_,t2)=clauses inputEnv outs
  in(M.Ghost env(M.GhostAxiom name args inputs outputs),t1++t2)
 statement(M.Ghost env(M.GhostProof name args ins outs body))=let
  scoped=foldr Map.delete env args
  (inputs,inputEnv,t1)=clauses scoped ins
  (outputs,_,t2)=clauses inputEnv outs
  (proofBody,_,t3)=clauses inputEnv body
  in(M.Ghost env(M.GhostProof name args inputs outputs proofBody),t1++t2++t3)
 statement other=(other,[])
 clauses env []=([],env,[])
 clauses env(value:rest)=let
  (converted,next,t1)=clause env value
  (tailClauses,lastEnv,t2)=clauses next rest
  in(converted:tailClauses,lastEnv,t1++t2)
 clause env(AssignProofVar name(Var source))|Just(original,_)<-target env source=(AssignProofVar name(Val(VFnRef original)),Map.insert name(M.Const(M.CFn original))env,[])
 clause env value@(AssignProofVar name _)=(value,Map.delete name env,[])
 clause env(ProofAssert proof)=let(converted,t)=normalize env proof in(ProofAssert converted,env,t)
 clause env(Assume proof)=let(converted,t)=normalize env proof in(Assume converted,env,t)
 clause env(Rewrite(CheckRel proof))=let(converted,t)=normalize env proof in(Rewrite(CheckRel converted),env,t)
 clause env(Rewrite(UserRewrite name args))=let(converted,t)=mapped(normalize env)args in(Rewrite(UserRewrite name converted),env,t)
 clause env other=(other,env,[])
 normalize env(FApp(ATerm name)args)|Just(original,fn)<-target env name,length args==length(M.fnParams fn)=let(converted,t)=mapped(normalize env)args in(FApp(CTerm(VFnRef original))converted,original:t)
 normalize env(FApp f args)=let(functionHead,t1)=normalize env f;(arguments,t2)=mapped(normalize env)args in(FApp functionHead arguments,t1++t2)
 normalize env(Forall index guards body)=let scoped=Map.delete index env;(conditions,t1)=mapped(normalize scoped)guards;(value,t2)=normalize scoped body in(Forall index conditions value,t1++t2)
 normalize _ other=(other,[])

replayCases :: [(String,String,Maybe String)]
replayCases=concat
 [[(mode++" lexical function survives caller shadow",lexical++body mode "observe=wrong;" "0",Nothing)
 ,(mode++" private input never overwrites caller actual",versioned++versionBody mode,Nothing)
 ,(mode++" output definitions never overwrite caller exports",outputOnly++outputBody mode,Nothing)]
 |mode<-["ordinary","assumed"]]
 where
 lexical="fn observe(x:Int)->Int[{}][{affirm return=0;}]{return 0;};fn wrong(x:Int)->Int[{}][{affirm return=100;}]{return 100;};proof fixed(x)[{affirm observe(x)=0;}][{affirm observe(x)=0;}]{ };"
 body "ordinary" prefix actual="define "++prefix++"rewrite fixed "++actual++";return 0;"
 body _ _ actual="fn verify(observe:Int)->Int[{rewrite fixed "++actual++";}][{}]{return observe;};return verify(100);"
 versioned="proof fixed(x)[{define i=1;define saved=x;}][{define i=0;affirm saved=x;}]{ };"
 versionBody "ordinary"="i=6;rewrite fixed i;affirm i=6;return 0;"
 versionBody _="fn verify(i:Int)->Int[{rewrite fixed i;}][{affirm return=i;}]{return i;};return verify(6);"
 outputOnly="proof fixed(x)[{}][{define n=0;affirm n=0;}]{ };"
 outputBody "ordinary"="define n=6;rewrite fixed 7;affirm n=6;return 0;"
 outputBody _="fn verify(n:Int)->Int[{rewrite fixed 7;}][{affirm return=n;}]{return n;};return verify(6);"
