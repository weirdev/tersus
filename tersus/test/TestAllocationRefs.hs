module TestAllocationRefs (testAllocationRefs, accepted, refused) where

import Control.Exception (finally)
import qualified Data.Map.Strict as Map
import Data.List (isInfixOf)
import System.Directory (removeFile)
import System.Exit (ExitCode(..))
import System.IO (hClose, openTempFile)

import Bootstrap (llvmOfOwned)
import Cli (Command(..), runSource)
import Compile (lowerSource, parseSource)
import MirLower (lowerModuleWith, lowerEntryWith)
import Interface (mergeInterfacesImportEnv)
import qualified Modules as Modules
import qualified Pipeline as Package
import TypeCheck (elaborate, emptyImportEnv)
import Types (Type (..))
import Mir
import MirData (forNative, readProgram, writeProgram)
import MirMono (monomorphize)
import qualified MirEval as Eval
import MirHousekeeping (eraseGhosts, verifyProgram)
import Native (buildExecutableFast)
import TestHarness
import TestNative (clangAvailable, runExecutableBytes)
import Utils

testAllocationRefs :: Test
testAllocationRefs = TestList "testAllocationRefs"
    [ TestList "checked reference and native parity" [TestCase name (if name `elem` notModeled then pure (unmodeled source) else parity source expected) | (name, source, expected) <- accepted]
    , TestList "static lifetime and primitive contracts" [testCase name (rejected source message) | (name, source, message) <- refused]
    , TestCase "permission erasure retains allocation and referent owners" retainedOwners
    , TestCase "pre-erasure and erased MIR round trip" roundTrips
    , testCase "unchecked raw targets detect free and resize, and reread the current slot" runtimeTargets
    , testCase "exited and cross-evaluation frame references are refused" expiredFrames
    , testCase "old non-raw carrier callbacks retain borrowed argument origins" (testAssertEq (lowerSource False legacyCallback `bindResult` Eval.runProgram) (Ok (Just (Eval.MInt 42))))
    , testCase "closed entry move errors retain source coordinates" (testAssertErrorContains "line 3:1" (lowerSource True "xs = [1];\nys = xs;\nreturn size(xs);\n"))
    , testCase "closed entry raw-loan errors retain source coordinates" (testAssertErrorContains "line 4:1" (lowerSource True "(p, b) = Addr::alloc(1);\nb = Addr::write(p, 0, 7, b);\nr = &Addr::get(p, 0, b);\nb = Addr::dropValue(p, 0, b);\nreturn *r + Addr::free(p, b);\n"))
    , testCase "successful closed-entry output has no position rows" noEntryPositions
    , testCase "closed entry checks the actual read-only imported body" (closedCallback False)
    , testCase "closed entry refuses a reference-storing imported body" (closedCallback True)
    , testCase "a genuinely exported raw getter remains unavailable without footprints" exportedRawModule
    , testCase "raw module exports require checked footprints" (testAssertErrorContains "exported checked footprints"
        (parseSource (standalone ++ "r=&Addr::get(p,0,b);n=*r;" ++ clear ++ "return n;") `bindResult` elaborate `bindResult` lowerModuleWith emptyImportEnv []))
    ]

noEntryPositions :: TestResult
noEntryPositions = case lowerSource True (standalone ++ "r = &Addr::get(p, 0, b); n = *r;" ++ clear ++ "return n;") of
    Error err -> Just err
    Ok program -> testAssertEq [() | fn <- progMain program : Map.elems (progFunctions program), block <- Map.elems (fnBlocks fn), Ghost _ GhostPosition{} <- blockStatements block] []

closedCallback :: Bool -> TestResult
closedCallback storing =
    let body = if storing then "struct Held { value: &Int }; fn read(value: &Int) -> Int { h = Held { value: &value }; return *h.value; };" else "fn read(value: &Int) -> Int { return *value; };"
        source = "import app::callback { read }; " ++ standalone ++ "r = &Addr::get(p, 0, b); n = read(r); " ++ clear ++ "return n;"
        files = [("app/package.tersus", ""), ("app/main.tersus", source), ("app/callback/callback.tersus", body)]
        loaded = case Modules.loadFromEntry (Modules.resolverFromFiles files) "app/main.tersus" of
            Left err -> Error err
            Right (Modules.PackageResult package) -> Ok package
            Right _ -> Error "Expected a package"
        lowered = loaded `bindResult` Package.compileModules `bindResult` \compiled ->
            case Package.compiledModules compiled of
                [dependency, entry] ->
                    let depIfaces = Package.compiledLibInterfaces dependency
                     in lowerModuleWith (mergeInterfacesImportEnv depIfaces) depIfaces (Package.compiledElaborated dependency) `bindResult` \dep ->
                        let ifaces = Package.compiledLibInterfaces entry ++ [Package.compiledInterface dependency]
                            units = Package.compiledLibUnits entry ++ Package.compiledLibUnits dependency ++ [(Package.compiledModuleId dependency, dep)]
                         in lowerEntryWith (mergeInterfacesImportEnv ifaces) ifaces units (Package.compiledElaborated entry)
                _ -> Error "Expected a dependency and one entry module"
     in if storing then testAssertErrorContains "reference-storing calls" lowered else case lowered of
        Error err -> Just err
        Ok _ -> Nothing

exportedRawModule :: TestResult
exportedRawModule =
    let source = "struct Buffer { addr: Addr<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 1; affirm filled(blk, 0); }]; fn read(o: &Buffer) -> &Int from o { return &Addr::get(o.addr, 0, o.blk); };"
        files = [("app/package.tersus", ""), ("app/main.tersus", "import app::raw { read }; return 0;"), ("app/raw/raw.tersus", source)]
        checked = case Modules.loadFromEntry (Modules.resolverFromFiles files) "app/main.tersus" of
            Left err -> Error err
            Right (Modules.PackageResult package) -> Package.compileModulesValidated package
            Right _ -> Error "Expected a package"
     in testAssertErrorContains "exported checked footprints" checked

owner :: String
owner = ownerFor "Int"

ownerFor :: String -> String
ownerFor payload = ownerStorage ++ rawGetter payload

ownerStorage :: String
ownerStorage = unlines
    [ "struct Owner<T> { addr: Addr<T>, ghost blk: Block<T> } invariant [{ affirm base(blk)=addr; affirm cap(blk)=1; affirm count(blk)=1; affirm whole(blk); affirm filled(blk,0)=true; }];"
    , "impl<T> Owner<T> { fn new(x:T) -> Self [{ }] [{ affirm at(return.blk,0)=x; }] { (p,b)=Addr::alloc(1); return Self { addr:p, blk:Addr::write(p,0,x,b) }; }; };"
    , "impl<T> Drop for Owner<T> { fn drop(self:Self) -> Int { return Addr::free(self.addr,Addr::dropValue(self.addr,0,self.blk)); }; };"
    ]

rawGetter :: String -> String
rawGetter payload = rawGetterNamed "rawRef" payload

rawGetterNamed :: String -> String -> String
rawGetterNamed name payload = "fn " ++ name ++ "(self:&Owner<" ++ payload ++ ">)->&" ++ payload ++ " from self [{ }] [{ affirm *return=at(self.blk,0); }] { return &Addr::get(self.addr,0,self.blk); }; "

standalone :: String
standalone = "(p,b)=Addr::alloc(1); b=Addr::write(p,0,7,b); "
clear :: String
clear = "b=Addr::dropValue(p,0,b); d=Addr::free(p,b); "

held :: String
held = ownerStorage ++ "struct Holder { r:&Int }; " ++ rawGetter "Holder" ++ "x=42; o=Owner::new(Holder { r:&x }); "

accepted :: [(String,String,String)]
accepted =
    [ ("standalone permission owner", standalone ++ "r=&Addr::get(p,0,b); n=*r; " ++ clear ++ "return n;", "7")
    , ("borrowed parameter reads contents", owner ++ "fn read(n:&Int)->Int { return n; }; o=Owner::new(42); r=rawRef(o); return read(r);", "42")
    , ("reference alias survives its call", owner ++ "fn again(o:&Owner<Int>)->&Int from o { r=rawRef(o); return r; }; o=Owner::new(42); r=again(o); s=r; return *s;", "42")
    , ("aggregate slot and field reborrow", "struct Point { x:Int, y:Int }; " ++ ownerFor "Point" ++ "fn field(p:&Point)->&Int from p { return &p.x; }; o=Owner::new(Point { x:19,y:7 }); r=rawRef(o); s=field(r); return *s;", "19")
    , ("reference index is captured", "(p,b)=Addr::alloc(2); b=Addr::write(p,0,7,b); b=Addr::write(p,1,42,b); i=0; r=&Addr::get(p,i,b); i=1; n=*r; b=Addr::dropRange(p,0,2,b); return n+Addr::free(p,b);", "7")
    , ("scalar copy permits later owner move", owner ++ "o=Owner::new(42); r=rawRef(o); n=*r; other=o; return n;", "42")
    , ("generic mutable field instantiation", "struct Pair<T> { x:T, y:T }; fn updatePair<T>(p:&mut Pair<T>, x:T)->Int { (*p).x=x; return 0; }; p=Pair<Int> { x:7,y:1 }; d=updatePair(&mut p,42); return p.x;", "42")
    , ("raw reread observes a rewritten allocation slot", standalone ++ "r=&Addr::get(p,0,b); n=*r; b=Addr::dropValue(p,0,b); b=Addr::write(p,0,42,b); s=&Addr::get(p,0,b); m=*s; " ++ clear ++ "return m;", "42")
    , ("two calls preserve distinct raw origins", owner ++ "fn either(a:&Owner<Int>,b:&Owner<Int>,c:Bool)->&Int from(a,b){if c{return rawRef(a);};return rawRef(b);}; a=Owner::new(7);b=Owner::new(42);r=either(a,b,true);s=either(a,b,false);return *r*100+*s;", "742")
    , ("a loop forwards a raw reference without storing it", owner ++ "a=Owner::new(7);b=Owner::new(42);r=rawRef(a);i=0;while i<1 [{ affirm i>=0; affirm i<=1; }] shrinks(1-i){r=rawRef(b);i=i+1;};return *r;", "42")
    , ("permission forwarding retains both possible runtime owners", permissionForward ++ "a=Owner::new(7);b=Owner::new(42);r=view(a,b);return *r;", "7")
    , ("two read reborrows do not inherit their parent's update mode", "struct Point{x:Int,y:Int};v=Point{x:7,y:42};p=&mut v;r=&(*p).x;s=&(*p).x;return *r+*s;", "14")
    , ("an existing borrowed holder can return its reference field", "struct Holder<T>{r:T};fn field(h:&Holder<&Int>)->&Int from h{return h.r;};x=42;h=Holder<&Int>{r:&x};r=field(h);return *r;", "42")
    , ("an existing logical List can return a held reference", "fn head(rs:&List<&Int>)->&Int from rs [{affirm size(rs)>0;}] [{ }] {return get(rs,0);};x=42;rs=push([],&x);r=head(rs);return *r;", "42")
    , ("a ghost permission relay retains its checked runtime anchor", "fn relay(b:&Block<Int>)->&Block<Int> from b [{ }] [{affirm base(*return)=base(b);affirm cap(*return)=cap(b);affirm filled(*return,0)=filled(b,0);}] {return b;};" ++ standalone ++ "q=relay(b);r=&Addr::get(p,0,*q);n=*r;" ++ clear ++ "return n;", "7")
    , ("a named raw getter function alias remains supported", owner ++ "o=Owner::new(42);g=rawRef;r=g(o);return*r;", "42")
    , ("an ordinary non-raw getter function value remains supported", "fn id(x:&Int)->&Int from x{return x;};fn pass(f:fn(&Int)->&Int)->Int{return 0;};return pass(id);", "0")
    , ("resolved associated Get preserves its declared other origin", associatedGet "b" ++ "x=Receiver{n:0};y=7;h=select(x,y);r=h.r;return*r;", "7")
    , ("cloning a carrier preserves an existing heap reference", cloneCarrier ++ "xs=[42];s=S{r:&get(xs,0)};t=clone(s);r=t.r;return*r;", "42")
    , ("borrowed carrier copies preserve the original heap referent", cloneCarrier ++ "fn copy(s:&S)->S from s{return S{r:s.r};};xs=[42];s=S{r:&get(xs,0)};t=copy(s);r=t.r;return*r;", "42")
    , ("ordinary frame references remain valid", "fn id(x:&Int)->&Int from x { return x; }; x=42; r=id(x); return *r;", "42")
    , ("array primitive remains unchanged", "a=#[7,42]; r=&get(a,1); return *r;", "42")
    ]

refused :: [(String,String,String)]
refused =
    [ ("free while raw reference is live", standalone ++ "r=&Addr::get(p,0,b); " ++ clear ++ "return *r;", "borrowed")
    , ("resize while raw reference is live", standalone ++ "r=&Addr::get(p,0,b); (q,b)=Addr::resize(p,2,b); n=*r; b=Addr::dropValue(q,0,b); return n+Addr::free(q,b);", "borrowed")
    , ("renamed resize result cannot bypass the raw permission loan", standalone ++ "r=&Addr::get(p,0,b);(q,c)=Addr::resize(p,2,b);n=*r;c=Addr::dropValue(q,0,c);return n+Addr::free(q,c);", "borrowed")
    , ("renamed write permission cannot bypass the raw loan", standalone ++ "r=&Addr::get(p,0,b);c=Addr::dropValue(p,0,b);n=*r;return n+Addr::free(p,c);", "borrowed")
    , ("consume owner while returned reference is live", owner ++ "o=Owner::new(7); r=rawRef(o); other=o; return *r;", "borrowed")
    , ("reference alias retains the permission loan", standalone ++ "r=&Addr::get(p,0,b); s=r; " ++ clear ++ "return *s;", "borrowed")
    , ("raw update borrow is forbidden", standalone ++ "r=&mut Addr::get(p,0,b); " ++ clear ++ "return 0;", "only be borrowed for reading")
    , ("read raw reference cannot yield a mutable field borrow", "struct Point { x:Int }; " ++ ownerFor "Point" ++ "o=Owner::new(Point { x:7 }); r=rawRef(o); s=&mut (*r).x; *s=42; return (*r).x;", "read reference")
    , ("raw index must be in range", standalone ++ "r=&Addr::get(p,1,b); n=*r; " ++ clear ++ "return n;", "does not model yet")
    , ("raw slot must be initialized", "(p,b)=Addr::alloc(1); r=&Addr::get(p,0,b); n=*r; return n+Addr::free(p,b);", "does not model yet")
    , ("fresh local owner cannot escape", owner ++ "fn bad(x:&Int)->&Int from x { o=Owner::new(7); return rawRef(o); }; return 0;", "not a reference from x")
    , ("ghost permission is not an escaping runtime owner", "fn bad(p:Addr<Int>, b:&Block<Int>)->&Int from b { return &Addr::get(p,0,b); }; return 0;", "ghost-only")
    , ("reference-bearing raw slot is temporarily refused", held ++ "r=rawRef(o); s=(*r).r; return *s;", "concrete reference-free payloads")
    , ("heap held owned referent requires the later footprint unit", ownerStorage ++ "struct Holder { r:&Owner<Int> }; " ++ rawGetter "Holder" ++ rawGetterNamed "scalarRef" "Int" ++ "x=Owner::new(42); o=Owner::new(Holder { r:&x }); r=rawRef(o); s=(*r).r; value=scalarRef(s); return *value;", "concrete reference-free payloads")
    , ("generic setter cannot export a raw reference while returning Int", mutableEscape, "raw-reference lifetime: raw-derived arguments")
    , ("raw reference cannot be stored in a local holder", owner ++ "struct Holder<T>{r:T}; x=42; h=Holder<&Int>{r:&x}; o=Owner::new(7); r=rawRef(o); q=&mut h; (*q).r=r; s=h.r; return *s;", "raw-reference lifetime")
    , ("raw reference cannot be stored through an array reference", owner ++ "struct Holder<T>{r:T};impl<T> Clone for Holder<T>{};x=42; a=array(1,Holder<&Int>{r:&x}); o=Owner::new(7); r=rawRef(o); q=&mut get(a,0); (*q).r=r; s=get(a,0).r; return *s;", "raw-reference lifetime")
    , ("raw reference cannot enter Uninit", owner ++ "o=Owner::new(7); r=rawRef(o); u=Uninit::new(r); s=Uninit::get(u); return *s;", "raw-reference lifetime")
    , ("forwarding cannot launder into a mutable call", owner ++ "struct Holder<T>{r:T}; fn forward(r:&Int)->&Int from r { return r; }; fn put<T>(h:&mut Holder<T>,r:T)->Int writes(h.r){(*h).r=r;return 0;}; x=42;h=Holder<&Int>{r:&x};o=Owner::new(7);r=forward(rawRef(o));d=put(&mut h,r);s=h.r;return *s;", "raw-reference lifetime")
    , ("both branch origins remain frozen", owner ++ "fn either(a:&Owner<Int>,b:&Owner<Int>,c:Bool)->&Int from(a,b){if c{return rawRef(a);};return rawRef(b);}; a=Owner::new(7);b=Owner::new(42);r=either(a,b,true);other=b;return *r;", "borrowed")
    , ("forged forwarding from is rejected by checked loans", "fn relay(a:&Int,b:&Int)->&Int from b { return a; }; x=42;y=7;r=relay(x,y);return *r;", "not a reference from")
    , ("raw reference cannot be embedded in a new holder", owner ++ "struct Holder<T>{r:T};o=Owner::new(7);r=rawRef(o);h=Holder<&Int>{r:r};s=h.r;return *s;", "raw-reference lifetime")
    , ("branch joins cannot hide a raw reference from a setter", owner ++ "struct Holder<T>{r:T};fn put<T>(h:&mut Holder<T>,r:T)->Int writes(h.r){(*h).r=r;return 0;};x=42;h=Holder<&Int>{r:&x};o=Owner::new(7);r=&x;if true{r=rawRef(o);};d=put(&mut h,r);s=h.r;return *s;", "raw-reference lifetime")
    , ("loop joins cannot hide a raw reference from a setter", owner ++ "struct Holder<T>{r:T};fn put<T>(h:&mut Holder<T>,r:T)->Int writes(h.r){(*h).r=r;return 0;};x=42;h=Holder<&Int>{r:&x};o=Owner::new(7);r=&x;i=0;while i<1 [{ affirm i>=0;affirm i<=1; }] shrinks(1-i){r=rawRef(o);i=i+1;};d=put(&mut h,r);s=h.r;return *s;", "raw-reference lifetime")
    , ("a raw argument cannot enter an Int-returning mutable call", owner ++ "fn mutate(n:&mut Int,r:&Int)->Int{*n=0;return r;};o=Owner::new(7);r=rawRef(o);x=42;return mutate(&mut x,r);", "raw-reference lifetime")
    , ("opaque callback transport of a raw getter is refused", owner ++ "fn pass(f:fn(&Owner<Int>)->&Int)->Int{return 0;};return pass(rawRef);", "raw-reference lifetime")
    , ("a last-use raw argument still freezes its consumed owner", owner ++ "fn consume(o:Owner<Int>,r:&Int)->Int{return r;};o=Owner::new(7);r=rawRef(o);return consume(o,r);", "borrowed")
    , ("named readonly raw-memory setters are not safe transports", owner ++ "fn put(r:&Int,p:Addr<&Int>,b:Block<&Int>)->Int [{affirm base(b)=p;affirm cap(b)>0;affirm whole(b);affirm count(b)=0;affirm filled(b,0)=false;}] [{ }] {b=Addr::write(p,0,&r,b);return Addr::free(p,Addr::dropValue(p,0,b));};o=Owner::new(7);r=rawRef(o);(p,b)=Addr::alloc(1);return put(r,p,b);", "raw-reference lifetime")
    , ("opaque calls with raw inputs require checked effects", owner ++ "struct H{r:&Int};fn make(x:&Int)->H from x{return H{r:&x};};fn apply(f:fn(&Int)->H,x:&Int)->Int{h=f(x);r=h.r;return*r;};o=Owner::new(7);r=rawRef(o);return apply(make,r);", "raw-reference lifetime")
    , ("owned mutable-reference carriers cannot hide raw write effects", owner ++ "struct H{r:&Int};struct HH{r:&mut H};fn put(h:HH,r:&Int)->Int{q=h.r;(*q).r=&r;return 0;};fn launder(h:HH)->Int{o=Owner::new(7);r=rawRef(o);return put(h,r);};x=42;h=H{r:&x};c=HH{r:&mut h};d=launder(c);r=h.r;return*r;", "raw-reference lifetime")
    , ("associated Get cannot forge a receiver origin", associatedGet "a" ++ "x=Receiver{n:0};y=7;h=select(x,y);y=42;r=h.r;return*r;", "not a reference from a")
    , ("cloned carriers keep their heap owner frozen", cloneCarrier ++ "xs=[42];s=S{r:&get(xs,0)};t=clone(s);other=xs;r=t.r;return*r;", "borrowed")
    , ("cloned carriers prevent mutation of their referent", cloneCarrier ++ "xs=[42];s=S{r:&get(xs,0)};t=clone(s);xs=set(xs,0,7);r=t.r;return*r;", "borrowed")
    , ("a clone cannot return a fresh local reference", "trait Clone{fn clone(self:&Self)->Self [{ }] [{affirm return=self;}];};struct S{r:&Int};impl Clone for S{fn clone(self:&Self)->Self{local=7;return Self{r:&local};};};x=42;s=S{r:&x};t=clone(s);return 0;", "not a reference from self")
    , ("reference-bearing target remains refused across a call", held ++ "fn bad(h:&Holder,x:&mut Int)->Int { r=h.r; *x=7; return *r; }; r=rawRef(o); return bad(r,&mut x);", "concrete reference-free payloads")
    , ("reference-bearing heap owner cannot escape its frame", owner ++ "struct Holder { r:&Int }; fn bad()->Owner<Holder> { x=7; return Owner::new(Holder { r:&x }); }; return 0;", "no parameter")
    ]


cloneCarrier :: String
cloneCarrier = "trait Clone{fn clone(self:&Self)->Self [{ }] [{affirm return=self;}];};struct S{r:&Int};impl Clone for S{};"

associatedGet :: String -> String
associatedGet origin = "struct H{r:&Int};struct Receiver{n:Int};impl Receiver{fn get(self:&Self,other:&Int)->H from other{return H{r:&other};};};fn select(a:&Receiver,b:&Int)->H from " ++ origin ++ " {return get(a,b);};"

legacyCallback :: String
legacyCallback = "struct H{r:&Int};fn make(x:&Int)->H from x{return H{r:&x};};fn apply(f:fn(&Int)->H,x:&Int)->Int{h=f(x);r=h.r;return*r;};x=42;return apply(make,x);"

permissionForward :: String
permissionForward = owner ++ "fn permission(a:&Owner<Int>,b:&Owner<Int>)->&Block<Int> from(a,b) [{ }] [{ affirm base(*return)=a.addr;affirm cap(*return)=1;affirm filled(*return,0)=true; }] { return &a.blk; }; fn view(a:&Owner<Int>,b:&Owner<Int>)->&Int from(a,b){q=permission(a,b);return &Addr::get(a.addr,0,*q);}; "

mutableEscape :: String
mutableEscape = owner ++ "struct Holder<T>{r:T};fn put<T>(h:&mut Holder<T>,r:T)->Int writes(h.r){(*h).r=r;return 0;};fn launder(h:&mut Holder<&Int>)->Int writes(h.r){o=Owner::new(7);r=rawRef(o);return put(h,r);};x=42;h=Holder<&Int>{r:&x};d=launder(&mut h);r=h.r;return *r;"

-- The validator written in Tersus does not model yet a reference into an allocation's slot (&Addr::get(p, i, b)):
-- it refuses these programs, which run as expected only unvalidated.
notModeled :: [String]
notModeled =
    [ "standalone permission owner", "borrowed parameter reads contents", "reference alias survives its call"
    , "aggregate slot and field reborrow", "reference index is captured", "scalar copy permits later owner move"
    , "raw reread observes a rewritten allocation slot", "two calls preserve distinct raw origins"
    , "a loop forwards a raw reference without storing it", "permission forwarding retains both possible runtime owners"
    , "a ghost permission relay retains its checked runtime anchor", "a named raw getter function alias remains supported"
    ]

unmodeled :: String -> TestResult
unmodeled source = case runSource Check source of
    Error failure | "does not model yet" `isInfixOf` failure -> Nothing
    other -> Just ("expected a refusal of what the validator does not model yet, got " ++ show other)

rejected :: String -> String -> TestResult
rejected source message = case lowerSource False source of
    Error failure -> if message `isInfixOf` failure then Nothing else Just failure
    Ok _ -> case runSource Check source of
        Error failure -> if message `isInfixOf` failure then Nothing else Just failure
        Ok _ -> Just "unsafe raw reference was accepted"

parity :: String -> String -> IO TestResult
parity source expected = do
    compiled <- compileOnce source
    case compiled of
        Error failure -> pure (Just failure)
        Ok _ -> case runSource Interpret source of
            Error failure -> pure (Just failure)
            Ok result | result /= expected -> pure (Just ("interpreter gave " ++ result ++ ", expected " ++ expected))
            Ok _ -> do
                available <- clangAvailable
                if not available then pure (Just "allocation-reference parity requires clang") else do
                    owned <- ownedOnce source
                    case owned of
                        Error failure -> pure (Just failure)
                        Ok code -> do
                            ir <- llvmOfOwned code
                            case ir of
                                Error failure -> pure (Just failure)
                                Ok text -> do
                                    (path, handle) <- openTempFile "/tmp" "allocation-reference-test"
                                    hClose handle
                                    flip finally (removeFile path) $ do
                                        built <- buildExecutableFast ["-DTERSUS_CHECK"] path text
                                        case built of
                                            Error failure -> pure (Just failure)
                                            Ok () -> runExecutableBytes path [] "" >>= \actual -> pure (testAssertEq actual (ExitSuccess, expected ++ "\n", ""))

retainedOwners :: IO TestResult
retainedOwners = case lowerSource False (owner ++ "o=Owner::new(42); r=rawRef(o); return *r;") of
    Error failure -> pure (Just failure)
    Ok program -> case eraseGhosts program of
        Error failure -> pure (Just failure)
        Ok erased ->
            let lifetimes p = [roots | fn <- progMain p : Map.elems (progFunctions p), block <- Map.elems (fnBlocks fn), Ghost _ (GhostLifetime _ roots) <- blockStatements block]
             in pure (testAssertTrue (not (null (lifetimes program)) && lifetimes program == lifetimes erased && not (null (lifetimes (monomorphize erased)))))

expiredFrames :: TestResult
expiredFrames = testAssertErrorContains "exited frame" (Eval.runProgram program)
    <> case Eval.runNamedFunction program "make" [] of
        Ok (Just reference) -> testAssertErrorContains "another evaluation" (Eval.runNamedFunction program "consume" [reference])
        result -> Just ("frame reference fixture failed: " ++ show result)
  where
    make = Function "make" [] (Just (TRef TInt))
        (Map.fromList [(Local 0, LocalDecl (TRef TInt) Nothing), (Local 1, LocalDecl TInt Nothing)])
        (Map.singleton (BlockId 0) (BasicBlock [Assign (Local 1) (Use (Const (CInt 42))), Assign (Local 0) (Borrow (Local 1) [] False)] Return))
        [] [] [] [] [] emptySpec
    consume = Function "consume" [Local 1] (Just TInt)
        (Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl (TRef TInt) Nothing)])
        (Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (Deref (Copy (Local 1)))] Return))
        [] [] [Local 1] [] [] emptySpec
    caller = Function "main" [] (Just TInt)
        (Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 2, LocalDecl (TRef TInt) Nothing)])
        (Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "make")) [] (Local 2) (BlockId 1))), (BlockId 1, BasicBlock [Assign (Local 0) (Deref (Copy (Local 2)))] Return)])
        [] [] [] [] [] emptySpec
    program = Program Map.empty (Map.fromList [("make", make), ("consume", consume)]) caller Map.empty Map.empty

runtimeTargets :: TestResult
runtimeTargets = testAssertEq (Eval.runProgram (program [])) (Ok (Just (Eval.MInt 7)))
    <> testAssertEq (Eval.runProgram (program rewrite)) (Ok (Just (Eval.MInt 42)))
    <> testAssertErrorContains "not allocated" (Eval.runProgram (program freed))
    <> testAssertErrorContains "not allocated" (Eval.runProgram (program resized))
  where
    number = Const . CInt
    address = Copy (Local 1)
    write value = Assign (Local 9) (ListOp AddrWrite [address, number 0, number value])
    dropValue = Assign (Local 9) (ListOp AddrDropValue [address, number 0])
    rewrite = [dropValue, write 42]
    freed = [dropValue, Assign (Local 9) (ListOp AddrFree [address])]
    resized = [Assign (Local 9) (ListOp AddrResize [address, number 2])]
    program changes = Program Map.empty Map.empty function Map.empty Map.empty
      where
        function = Function "main" [] (Just TInt)
            (Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl (TAddr TInt) Nothing), (Local 2, LocalDecl (TRef TInt) Nothing), (Local 9, LocalDecl TInt Nothing)])
            (Map.singleton (BlockId 0) (BasicBlock
                ([Assign (Local 1) (ListOp AddrAlloc [number 1]), write 7, Assign (Local 2) (ListOp AddrBorrow [address, number 0, address])]
                    ++ changes ++ [Assign (Local 0) (Deref (Copy (Local 2)))]) Return))
            [] [] [] [] [] emptySpec

roundTrips :: IO TestResult
roundTrips = case lowerSource False (standalone ++ "r=&Addr::get(p,0,b); n=*r; " ++ clear ++ "return n;") of
    Error failure -> pure (Just failure)
    Ok program -> case eraseGhosts program of
        Error failure -> pure (Just failure)
        Ok erased -> pure $ testAssertEq (readProgram (writeProgram program)) (Ok (forNative program))
            <> testAssertEq (readProgram (writeProgram erased)) (Ok (forNative erased))
            <> testAssertEq (verifyProgram erased) (Ok ())
