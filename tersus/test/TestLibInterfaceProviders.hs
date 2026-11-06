module TestLibInterfaceProviders (testLibInterfaceProviders, providerFixture) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Interface
import qualified LibPackage as L
import Link (linkPrograms)
import qualified Mir as M
import MirLower (lowerModuleWith)
import qualified ValidatorNative as V
import Modules (ModuleId(..))
import qualified ParsedFile as Parse
import qualified ParserSeed
import Syntax
import Types
import TypeCheck (elaborateWith, Elaborated(..), ImportEnv(..), emptyImportEnv)
import TestHarness
import Utils

compileUnit :: String -> [ModuleInterface] -> Parse.Decls -> String -> Result (ModuleInterface, M.Program, Parse.Decls) String
compileUnit name dependencies declarations source =
    case ParserSeed.parseFileWith declarations source of
        Left err -> Error (show err)
        Right (Parse.ParsedFile _ original, nextDecls) ->
            -- (a generic constructor owner is a compiler-only view, given to library modules as LibPackage does)
            let merged = mergeInterfacesImportEnv dependencies
                owners = Map.fromList [(owner, [ctor]) | iface <- dependencies, (ctor, (owner, _)) <- Map.toList (ifCtors iface), ctor == owner]
                imported = merged{ieTypes = Map.union (ieTypes merged) owners}
             in elaborateWith (predeclareOwnEnv imported) original `bindResult` \(typed@(Elaborated statements _), state) ->
                extractLibInterface (ModuleId "fixturelib" (Just name)) original statements state `bindResult` \iface ->
                    lowerModuleWith imported dependencies typed `bindResult` \program -> Ok (iface, program, nextDecls)

providerFixture :: Result (ModuleInterface, M.Program) String
providerFixture =
    compileUnit "types" [] Parse.emptyDecls genericType `bindResult` \(types, typeProgram, decls) ->
        compileUnit "provider" [types] decls inherent `bindResult` \(provider, providerProgram, decls') ->
            compileUnit "consumer" [types, provider] decls' "g = G::new(7); return g.measure();" `bindResult` \(_, consumer, _) ->
                linkPrograms [(ModuleId "fixturelib" (Just "types"), typeProgram), (ModuleId "fixturelib" (Just "provider"), providerProgram), (ModuleId "fixturelib" (Just "consumer"), consumer)] `bindResult` \linked -> Ok (provider, linked)

testLibInterfaceProviders :: Test
testLibInterfaceProviders = TestList "testLibInterfaceProviders"
    [ testCase "symbolic generic constructor owners have consistent type keys" $ case compileUnit "types" [] Parse.emptyDecls (genericType ++ "struct Sized<n> { cells: Array<Int, n> };") of
        Error err -> Just err
        Ok (iface, _, _) -> testAssertTrue (not (Map.null (ifCtors iface)) && all (\(ctor, (owner, _)) -> ctor == owner && Map.notMember owner (ifTypes iface)) (Map.toList (ifCtors iface)))
    , testCase "unused symbolic frontend seeds are not runtime declarations" unusedRuntimeSeeds
    , testCase "used symbolic and concrete generic instances are still completed" usedRuntimeInstances
    , testCase "provider constructs imported generic Self without redeclaration" $ case providerFixture of Error err -> Just err; Ok _ -> Nothing
    , testCase "an inherent provider exports only its own association origins" $ case providerFixture of
        Error err -> Just err
        Ok (iface, _) -> testAssertEq (Map.lookup ("G", "new") (ifAssoc iface), Map.lookup ("G", "measure") (ifAssoc iface)) (Just [Nothing], Just [Nothing])
    , testCase "linked generic provider contracts validate with and without cache" $ case providerFixture of
        Error err -> Just err
        Ok (_, program) -> pairedValidation program
    , testCase "a trait provider exports its checked implementation and arguments" traitMetadata
    , testCase "bounded providers export their primary and conformance templates" boundedMetadata
    , testCase "a bounded provider's actual scalar instance validates" (boundedUse "g = G::new(7); return Counted::count(g);" Nothing)
    , testCase "a bounded provider still rejects a failed Copy bound" (boundedUse "g = G<List<Int>> { value: [7] }; return Counted::count(g);" (Just "needs T to implement Copy"))
    , testCase "a Drop provider exports ownership without owning its type declaration" dropMetadata
    , testCase "a provider does not re-export an imported peer association" peerVisibility
    , testCase "a consumer cannot find a peer method through the other provider" peerConsumer
    , testCase "unprovided bounded peer templates and companions remain private" boundedPeerVisibility
    , testCase "an imported Drop provider is not re-exported by its consumer" peerDropVisibility
    , testCase "custom Clone selection receives no standard impls through a provider" cloneVisibility
    , testCase "nonlibrary generic interfaces retain their existing visibility" nonLibConsistency
    ]

unusedRuntimeSeeds :: TestResult
unusedRuntimeSeeds = case compileUnit "types" [] Parse.emptyDecls (genericType ++ "struct Fixed { value: Int };") `bindResult` \(types, _, decls) -> compileUnit "consumer" [types] decls "return 0;" of
    Error err -> Just err
    Ok (_, program, _) -> testAssertEq (Map.keys (M.progTypes program)) ["Fixed"]

usedRuntimeInstances :: TestResult
usedRuntimeInstances = case providerFixture of
    Error err -> Just err
    Ok (_, program) -> testAssertEq (Map.lookup "G<'T>" (M.progTypes program), Map.lookup "G<Int>" (M.progTypes program)) (Just (M.StructDecl [("value", TParam "T")]), Just (M.StructDecl [("value", TInt)]))

pairedValidation :: M.Program -> TestResult
pairedValidation program = case (V.validateCompiledUncached program, V.validateCompiled program) of
    (Ok (), Ok ()) -> Nothing
    other -> Just (show other)

traitFixture :: Bool -> Result (ModuleInterface, M.Program, ModuleInterface, M.Program, ModuleInterface, M.Program, Parse.Decls) String
traitFixture bounded =
    compileUnit "types" [] Parse.emptyDecls genericType `bindResult` \(types, typeProgram, decls) ->
        compileUnit "traits" [types] decls "trait Copy { }; trait Counted { fn count(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; };" `bindResult` \(traits, traitProgram, decls') ->
            compileUnit "provider" [types, traits] decls' (if bounded then boundedImpl else traitImpl) `bindResult` \(provider, providerProgram, decls'') ->
                Ok (types, typeProgram, traits, traitProgram, provider, providerProgram, decls'')

traitMetadata :: TestResult
traitMetadata = case traitFixture False of
    Error err -> Just err
    Ok (_, _, _, _, iface, _, _) -> testAssertTrue (Set.member ("Counted", "G") (ifImpls iface) && Map.member ("Counted", "G") (ifImplArgs iface) && Map.lookup ("G", "count") (ifAssoc iface) == Just [Just "Counted"])

boundedMetadata :: TestResult
boundedMetadata = case traitFixture True of
    Error err -> Just err
    Ok (_, _, _, _, iface, _, _) -> testAssertTrue (Map.member "<G as Counted>::count" (ifTemplates iface) && Map.member "Counted for G::count" (ifTemplates iface) && Map.lookup "<G as Counted>::count" (ifCompanions iface) == Just ["Counted for G::count"] && Map.lookup ("Counted", "G") (ifImplBounds iface) == Just [("T", "Copy", [])])

boundedUse :: String -> Maybe String -> TestResult
boundedUse body expected = case traitFixture True `bindResult` \(types, typeProgram, traits, traitProgram, provider, providerProgram, decls) ->
    compileUnit "consumer" [types, traits, provider] decls body `bindResult` \(_, consumer, _) ->
        linkPrograms [(ModuleId "fixturelib" (Just "types"), typeProgram), (ModuleId "fixturelib" (Just "traits"), traitProgram), (ModuleId "fixturelib" (Just "provider"), providerProgram), (ModuleId "fixturelib" (Just "consumer"), consumer)] of
    Error err | maybe False (`isInfixOf` err) expected -> Nothing
              | otherwise -> Just err
    Ok program | expected == Nothing -> pairedValidation program
               | otherwise -> Just "Failed bound was accepted"

dropMetadata :: TestResult
dropMetadata =
    let typesSource = "struct Buffer<T> { addr: Addr<T>, ghost blk: Block<T> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; }];"
        traitsSource = "trait Drop { fn drop(self: Self) -> Int [{ }] [{ }]; };"
        implementation = "impl<T> Drop for Buffer<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; };"
     in case compileUnit "types" [] Parse.emptyDecls typesSource `bindResult` \(types, _, decls) ->
        compileUnit "traits" [types] decls traitsSource `bindResult` \(traits, _, decls') ->
            compileUnit "provider" [types, traits] decls' implementation of
        Error err -> Just err
        Ok (iface, _, _) -> testAssertTrue (Set.member "Buffer" (ifDrops iface) && Set.member ("Drop", "Buffer") (ifImpls iface) && Map.lookup ("Buffer", "drop") (ifAssoc iface) == Just [Just "Drop"] && Map.member "<Buffer as Drop>::drop" (ifFunctions iface))

peerFixture :: Result (ModuleInterface, ModuleInterface, M.Program, Parse.Decls) String
peerFixture = compileUnit "types" [] Parse.emptyDecls genericType `bindResult` \(types, _, decls) ->
    compileUnit "peer" [types] decls "impl<T> G<T> { fn peer(self: &Self) -> Int { return 6; }; };" `bindResult` \(peer, _, decls') ->
        compileUnit "provider" [types, peer] decls' inherent `bindResult` \(provider, program, decls'') -> Ok (types, provider, program, decls'')

peerVisibility :: TestResult
peerVisibility = case peerFixture of
    Error err -> Just err
    Ok (_, iface, _, _) -> testAssertTrue (Map.notMember ("G", "peer") (ifAssoc iface) && Map.notMember "<G>::peer" (ifFunctions iface) && Map.member ("G", "measure") (ifAssoc iface))

peerConsumer :: TestResult
peerConsumer = case peerFixture `bindResult` \(types, provider, _, decls) -> compileUnit "consumer" [types, provider] decls "g = G::new(7); return g.peer();" of
    Error err | "G::peer is not defined" `isInfixOf` err -> Nothing
              | otherwise -> Just err
    Ok _ -> Just "Imported but unprovided peer association leaked"

boundedPeerVisibility :: TestResult
boundedPeerVisibility = case traitFixture True `bindResult` \(types, _, traits, _, peer, _, decls) ->
    compileUnit "other_provider" [types, traits, peer] decls "impl<T> G<T> { fn local(self: &Self) -> Int { return 3; }; };" of
    Error err -> Just err
    Ok (iface, _, _) -> testAssertTrue (Map.lookup ("G", "local") (ifAssoc iface) == Just [Nothing] && Map.notMember ("G", "count") (ifAssoc iface) && Set.notMember ("Counted", "G") (ifImpls iface) && Map.notMember ("Counted", "G") (ifImplBounds iface) && Map.null (ifTemplates iface) && Map.null (ifCompanions iface))

peerDropVisibility :: TestResult
peerDropVisibility =
    let source = "struct Buffer<T> { addr: Addr<T>, ghost blk: Block<T> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; }]; trait Drop { fn drop(self: Self) -> Int; };"
     in case compileUnit "types" [] Parse.emptyDecls source `bindResult` \(types, _, decls) ->
        compileUnit "peer" [types] decls "impl<T> Drop for Buffer<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; };" `bindResult` \(peer, _, decls') ->
            compileUnit "provider" [types, peer] decls' "fn local(n: Int) -> Int { return n; };" of
        Error err -> Just err
        Ok (iface, _, _) -> testAssertTrue (Map.member "local" (ifFunctions iface) && Set.null (ifDrops iface) && Set.notMember ("Drop", "Buffer") (ifImpls iface) && Map.notMember ("Buffer", "drop") (ifAssoc iface))

cloneVisibility :: TestResult
cloneVisibility = case L.libPackage of
    Error err -> Just err
    Ok libraries ->
        let types = L.libInterfaces libraries Map.! "types"
            clone = L.libInterfaces libraries Map.! "clone"
            source = "fn local(x: Int) -> Int { return x; };"
         in case compileUnit "provider" [types, clone] Parse.emptyDecls source of
            Error err -> Just err
            Ok (provider, _, decls) ->
                let forbidden = [pair | pair@(trait, _) <- Set.toList (ifImpls provider), trait == "Clone"]
                    caller = "trait Clone { fn clone(self: &Self) -> Self; }; fn copy(xs: &List<Int>) -> List<Int> { return clone(xs); };"
                 in case compileUnit "consumer" [types, provider] decls caller of
                    Error err | null forbidden && "List does not implement Clone" `isInfixOf` err -> Nothing
                              | otherwise -> Just err
                    Ok _ -> Just "Standard Clone implementation leaked through an internal dependency"

nonLibConsistency :: TestResult
nonLibConsistency =
    let original = [StructDef "app$types$G" ["T"] [("value", TParam "T")] []]
     in case elaborateWith (predeclareOwnEnv emptyImportEnv) original of
        Error err -> Just err
        Ok (Elaborated statements _, state) -> case extractInterface (ModuleId "app" (Just "types")) original statements state of
            Error err -> Just err
            Ok iface -> testAssertTrue (Map.member "app$types$G" (ifGenerics iface) && Map.notMember "app$types$G<'T>" (ifCtors iface))

genericType, inherent, traitImpl, boundedImpl :: String
genericType = "struct G<T> { value: T };"
inherent = "impl<T> G<T> { fn new(value: T) -> Self [{ }] [{ }] { return Self { value: value }; }; fn measure(self: &Self) -> Int [{ }] [{ affirm return = 7; }] { return 7; }; };"
traitImpl = "impl<T> Counted for G<T> { fn count(self: &Self) -> Int [{ }] [{ affirm return = 7; }] { return 7; }; };"
boundedImpl = inherent ++ "impl<T: Copy> Counted for G<T> { fn count(self: &Self) -> Int [{ }] [{ affirm return = 7; }] { return 7; }; };"
