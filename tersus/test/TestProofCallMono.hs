module TestProofCallMono(testProofCallMono) where

import Compile(lowerSource)
import Control.Exception(evaluate)
import qualified Data.Map.Strict as Map
import Data.List(isInfixOf)
import qualified Mir as M
import MirMono(monomorphizeProofCallsForValidation)
import Syntax
import TestHarness(Test(..))
import Types(Type(..),Arg(..))
import Utils(Result(..))
import ValidatorNative(validateCompiled,validateCompiledUncached)

maps :: String
maps="a=HashMap::new();a=a.insert(1,true);b=HashMap::new();b=b.insert(2,7);affirm size(a)>=0;affirm size(b)>=0;return 0;"

pick :: String
pick="fn pick<T>(x:T,n:Int)->Int[{}][{affirm return=n;}]{return n;};"

callOnly :: String
callOnly="fn verify(x:Bool)->Int[{}][{affirm return=pick(x,7);}]{return 7;};return 0;"

testProofCallMono :: Test
testProofCallMono=TestList "testProofCallMono"
 [TestCase "two actual HashMap keys are selected independently" mapKeys
 ,TestCase "proof-only demand validates its actual declaration instance" (checked Nothing(pick++callOnly))
 ,TestCase "a demanded instance cannot import a false callee promise" (checked(Just "Could not prove")("fn pick<T>(x:T,n:Int)->Int[{}][{affirm return=n;}]{return n+1;};"++callOnly))
 ,TestCase "a demanded callee body is not an unadvertised theorem" (checked(Just "Could not prove")("fn pick<T>(x:T,n:Int)->Int{return n;};"++callOnly))
 ,TestCase "missing type arguments are not defaulted" (unavailable "fn pick<T>(n:Int)->Int[{}][{affirm return=n;}]{return n;};fn verify()->Int[{}][{affirm return=pick(7);}]{return 7;};return 0;")
 ,TestCase "mismatched argument shape does not choose the only instance" mismatchedPlace
 ,TestCase "unrepresented hidden size argument is an explicit refusal" (unavailable "fn measure<n>(xs:Array<Int,n>)->Int[{}][{affirm return=size(xs);}]{return size(xs);};fn verify(xs:Array<Int,3>)->Int[{}][{affirm return=measure(xs);}]{return 3;};return 0;")
 ,TestCase "both HashMap specializations retain rejecting promises" (checked(Just "Could not prove")("a=HashMap::new();a=a.insert(1,true);b=HashMap::new();b=b.insert(2,7);affirm size(a)=99;return 0;"))
 ,TestCase "type-growing own proof demand is refused before materialization" (cycleRefused(lift++"fn q<T>(x:T)->Int[{}][{affirm return=q(lift(x));}]{return 0;};fn verify(x:Int)->Int[{}][{affirm return=q(x);}]{return 0;};return 0;"))
 ,TestCase "mutually type-growing proof demands are refused before materialization" (cycleRefused(lift++"fn q<T>(x:T)->Int[{}][{affirm return=r(lift(x));}]{return 0;};fn r<T>(x:T)->Int[{}][{affirm return=q(lift(x));}]{return 0;};fn verify(x:Int)->Int[{}][{affirm return=q(x);}]{return 0;};return 0;"))
 ,TestCase "nongrowing acyclic proof demand remains valid" (checked Nothing "fn q<T>(x:T)->Int[{}][{affirm return=0;}]{return 0;};fn verify(x:Bool)->Int[{}][{affirm return=q(x);}]{return 0;};return 0;")
 -- (the validator written in Tersus resolves q in the output contract to q itself, not to the input contract's alias)
 ,TestCase "header alias shadows do not invent a declaration cycle" (checked (Just "Could not prove: return = q(x)") "fn leaf(x:Int)->Int[{}][{affirm return=x;}]{return x;};fn q(x:Int)->Int[{define q=leaf;}][{affirm return=q(x);}]{return x;};return q(7);")
 ,TestCase "type-growing runtime edge is refused before a proof demand expands" listMutation
 ,TestCase "mixed proof/runtime growth is refused before expansion" mixedMutation
 ,TestCase "finite same-Key runtime recursion still materializes" (finiteRecursion "fn q<T>(x:T)->Int ~ {return q(x);};return q(7);")
 ,TestCase "finite constant-Key runtime recursion still materializes" (finiteRecursion "fn q<T>(x:T)->Int ~ {return q(7);};return q(true);")
 ,TestCase "reference wrappers retained in Keys cannot grow recursively" (wrappedMutation False)
 ,TestCase "mutable reference wrappers retained in Keys cannot grow recursively" (wrappedMutation True)
 ]
 where
 lift="fn lift<T>(x:T)->List<T>{return push([],x);};"
 listMutation=runtimeMutation "fn q<T>(x:T)->Int ~ {grown=push([],x);return q(7);};return q(7);" "q" "q"
 mixedMutation=runtimeMutation(lift++"fn stop(n:Int)->Int{return 0;};fn q<T>(x:T)->Int[{}][{affirm return=r(lift(x));}]{return 0;};fn r<T>(x:T)->Int ~ {grown=push([],x);return stop(0);};fn verify(x:Int)->Int[{}][{affirm return=q(x);}]{return 0;};return 0;") "r" "q"
 runtimeMutation source callerName targetName=case lowerSource True source of
  Error err->pure(Just("Earlier Source error "++err))
  Ok original->case monomorphizeProofCallsForValidation original of
   Left err->pure(Just("Unmutated runtime-growth fixture failed: "++err))
   Right _->case [(target,caller)|M.BasicBlock statements _<-Map.elems(M.fnBlocks(M.progMain original)),M.Ghost _(M.GhostFunction target sourceName _)<-statements,sourceName==targetName,caller<-Map.elems(M.progFunctions original),M.fnName caller==callerName] of
    [(target,caller)]->case [local|(local,decl)<-Map.toList(M.fnLocals caller),M.localName decl==Just "grown",case M.localType decl of TNamed "List" [ArgType(TParam _)]->True;_->False] of
     [grown]->do
      let change(M.BasicBlock statements(M.Call(M.Const(M.CFn _))_ dest next))=M.BasicBlock statements(M.Call(M.Const(M.CFn target))[M.Copy grown]dest next)
          change block=block
          blocks=Map.map change(M.fnBlocks caller)
          mutated=original{M.progFunctions=Map.insert(M.fnName caller)(caller{M.fnBlocks=blocks})(M.progFunctions original)}
      if blocks==M.fnBlocks caller then pure(Just "The actual call edge did not change") else pure$case monomorphizeProofCallsForValidation mutated of
       Left err|"recursive proof declaration workload"`isInfixOf`err->Nothing
       other->Just("No exact actual runtime-growth refusal "++show(fmap(const())other))
     _->pure(Just "Missing exactly one actual checked List<T> local")
    _->pure(Just "Missing actual checked source declarations for the mutation")
 wrappedMutation mutable=case lowerSource True ("fn q<T>(x:T)->Int ~ {r=&"++(if mutable then "mut " else "")++"x;return q(7);};return q(7);") of
  Error err->pure(Just("Earlier Source error "++err))
  Ok original->case monomorphizeProofCallsForValidation original of
   Left err->pure(Just("Unmutated wrapper fixture did not materialize: "++err))
   Right _->case [(name,fn,local)|(name,fn)<-Map.toList(M.progFunctions original),not(null(M.fnTypeParams fn)),(local,decl)<-Map.toList(M.fnLocals fn),case M.localType decl of TRef(TParam _)->not mutable;TMutRef(TParam _)->mutable;_->False] of
    [(name,fn,reference)]->do
     let change(M.BasicBlock statements(M.Call target@(M.Const(M.CFn same))[M.Const(M.CInt 7)]dest next))|same==name=M.BasicBlock statements(M.Call target[M.Copy reference]dest next)
         change block=block
         blocks=Map.map change(M.fnBlocks fn)
         mutated=original{M.progFunctions=Map.insert name(fn{M.fnBlocks=blocks})(M.progFunctions original)}
     if blocks==M.fnBlocks fn then pure(Just "Actual recursive call argument was not changed to the retained reference wrapper") else pure$case monomorphizeProofCallsForValidation mutated of
      Left err|"recursive proof declaration workload"`isInfixOf`err->Nothing
      other->Just("No exact retained-wrapper growth refusal "++show(fmap(const())other))
    _->pure(Just "Did not find exactly one actual checked generic reference local")
 finiteRecursion source=case lowerSource True source of
  Error err->pure(Just("Earlier Source error "++err))
  Ok original->pure$case monomorphizeProofCallsForValidation original of
   Right selected|or[null(M.fnTypeParams fn)&&null(M.fnSizeParams fn)|M.BasicBlock _(M.Call(M.Const(M.CFn target))_ _ _)<-Map.elems(M.fnBlocks(M.progMain selected)),Just fn<-[Map.lookup target(M.progFunctions selected)]]->Nothing
   other->Just("Finite same-Key recursion did not materialize "++show(fmap(const())other))
 cycleRefused source=case lowerSource True source of
  Error err|"calls itself with the type"`isInfixOf`err->pure Nothing
  Error err->pure(Just("Earlier Source error "++err))
  Ok original->pure$case monomorphizeProofCallsForValidation original of
   Left err|"recursive proof declaration workload"`isInfixOf`err->Nothing
   other->Just("No pre-materialization declaration-cycle refusal "++show(fmap(const())other))
 mismatchedPlace=case lowerSource True "fn measure<T>(xs:&List<T>)->Int[{}][{affirm return=size(xs);}]{return size(xs);};fn verify(xs:List<Int>,flag:Bool)->Int[{}][{affirm return=measure(xs);}]{return size(xs);};return 0;" of
  Error err->pure(Just("Earlier Source error "++err))
  Ok original->case [(name,fn)| (name,fn)<-Map.toList(M.progFunctions original),Just(M.Copy flag)<-[Map.lookup "flag"(M.specEnv(M.fnSpec fn))],Just local<-[Map.lookup flag(M.fnLocals fn)],M.localType local==TBool] of
   [(name,fn)]->do
    before<-verdict Nothing original
    case before of
     Just err->pure(Just("Unmutated place fixture failed: "++err))
     Nothing->do
      let spec=M.fnSpec fn
          declarations=[target|M.BasicBlock statements _<-Map.elems(M.fnBlocks(M.progMain original)),M.Ghost _(M.GhostFunction target "measure" _)<-statements]
          mutate(ProofAssert(FApp relation[left,FApp target@(ATerm callee)[ATerm "xs"]]))|Just(M.Const(M.CFn actual))<-Map.lookup callee(M.specEnv spec),actual`elem`declarations=ProofAssert(FApp relation[left,FApp target[ATerm "flag"]])
          mutate clause=clause
          changed=map mutate(M.specEnsures spec)
          mutated=original{M.progFunctions=Map.insert name(fn{M.fnSpec=spec{M.specEnsures=changed}})(M.progFunctions original)}
      if changed==M.specEnsures spec then pure(Just "The intended actual argument place did not change") else pure$case monomorphizeProofCallsForValidation mutated of
       Left err|"cannot select its declared type/size key"`isInfixOf`err->Nothing
       other->Just("No exact actual-place key refusal "++show(fmap(const())other))
   _->pure(Just "Did not find exactly one checked caller with the actual Bool flag local")
 mapKeys=case lowerSource True maps of
  Error err->pure(Just("Earlier Source error "++err))
  Ok original->case monomorphizeProofCallsForValidation original of
   Left err->pure(Just err)
   Right selected->do
    let called=concatMap callsFunction(M.progMain selected:Map.elems(M.progFunctions selected))
        shapes=[M.localType first|target<-called,Just fn<-[Map.lookup target(M.progFunctions selected)],M.fnTypeParams fn==[],M.fnSizeParams fn==[],M.fnReturns fn==Just TInt,param:_<-[M.fnParams fn],Just first<-[Map.lookup param(M.fnLocals fn)]]
        expected=[TNamed "HashMap" [ArgType TInt,ArgType TBool],TNamed "HashMap" [ArgType TInt,ArgType TInt]]
    if not(all(`elem`shapes)expected) then pure(Just("Missing actual selected HashMap parameter keys "++show shapes)) else verdict Nothing original
 unavailable source=case lowerSource True source of
  Error err->pure(Just("Earlier Source error "++err))
  Ok original->pure$case monomorphizeProofCallsForValidation original of
   Left err|"cannot select its declared type/size key"`isInfixOf`err->Nothing
   other->Just("No explicit key-selection refusal "++show(fmap(const())other))
 checked expected source=case lowerSource True source of
  Error err->pure(Just("Earlier Source error "++err))
  Ok program->verdict expected program
 verdict expected program=do
  results<-mapM(evaluate.($program))[validateCompiledUncached,validateCompiled,validateCompiled]
  pure$if all(matches expected)results then Nothing else Just("Wrong proof-only instance result "++show results)
 matches Nothing(Ok())=True
 matches(Just needle)(Error err)=needle`isInfixOf`err
 matches _ _=False

callsFunction :: M.Function -> [String]
callsFunction fn=concatMap callsClause(M.specRequires spec++M.specEnsures spec)++concat[case statement of M.Ghost _(M.GhostValidation clause)->callsClause clause;_->[]|M.BasicBlock statements _<-Map.elems(M.fnBlocks fn),statement<-statements]
 where spec=M.fnSpec fn
callsClause(ProofAssert proof)=calls proof
callsClause(Assume proof)=calls proof
callsClause _=[]
calls(FApp(CTerm(VFnRef target))args)=target:concatMap calls args
calls(FApp f args)=calls f++concatMap calls args
calls(Forall _ guards body)=concatMap calls(guards++[body])
calls _=[]
