module TestLibModules (testLibModules) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Interface (ModuleInterface (..))
import LibPackage (libInterfaces, libOrder, libPackage)
import TestHarness (Test (..), testAssertEq, testAssertTrue, testCase)
import Utils (Result (..))

-- The compiler libraries (lib/eq.tersus and the rest) compiled as modules
-- of the synthetic lib package: the package loads, each library checks
-- against the interfaces of the libraries it imports, and the interfaces
-- carry what an importer needs under the libraries' bare names.
testLibModules :: Test
testLibModules =
    TestList
        "testLibModules"
        [ TestList
            "the lib package standalone"
            [ testCase "it compiles" compiles
            , testCase "modules compile dependencies first" orderIsDependencyFirst
            , testCase "eq declares Eq and its impls" (interface "eq" (\iface -> Map.member "Eq" (ifTraits iface) && implsIn iface [("Eq", "List"), ("Eq", "Array"), ("Eq", "Box")]))
            , testCase "clone declares Clone and its impls" (interface "clone" (\iface -> Map.member "Clone" (ifTraits iface) && implsIn iface [("Clone", "List"), ("Clone", "Array"), ("Clone", "Box")]))
            , testCase "prelude declares its traits" (interface "prelude" (\iface -> allIn (Map.keys (ifTraits iface)) ["Sequence", "Growable", "Copy", "Drop", "Deref", "Hash"]))
            , testCase "prelude has the word Hash impls" (interface "prelude" (\iface -> implsIn iface [("Hash", "Int"), ("Hash", "Byte"), ("Hash", "Bool")] && allIn (Map.keys (ifFunctions iface)) ["hashCombine", "<Int as Hash>::hash"]))
            , testCase "prelude does not re-export Clone" (interface "prelude" (\iface -> not (implsIn iface [("Clone", "List")]) && Map.notMember "cloneBoxedArray" (ifTemplates iface)))
            , testCase "string declares String and its impls" (interface "string" (\iface -> Map.member "String" (ifTypes iface) && implsIn iface [("Clone", "String"), ("Eq", "String"), ("Hash", "String"), ("Sequence", "String")]))
            , testCase "map declares HashMap" (interface "map" (\iface -> allIn (Map.keys (ifGenerics iface)) ["HashMap", "Entry"] && implsIn iface [("Clone", "HashMap")]))
            , testCase "set declares HashSet" (interface "set" (\iface -> Map.member "HashSet" (ifGenerics iface) && implsIn iface [("Clone", "HashSet")]))
            , testCase "set reaches map's findNth as a function" (interface "map" (\iface -> Map.member "findNth" (ifFunctions iface)))
            , testCase "bounded helpers travel as templates" (both (interface "eq" (\iface -> Map.member "eqBoxedArrays" (ifTemplates iface))) (both (interface "clone" (\iface -> Map.member "cloneBoxedArray" (ifTemplates iface))) (interface "map" (\iface -> allIn (Map.keys (ifTemplates iface)) ["findIn", "indexFor", "<HashMap>::contains"]))))
            , testCase "generic impl methods travel as templates" (both (interface "eq" (\iface -> Map.member "<List as Eq>::eq" (ifTemplates iface))) (interface "clone" (\iface -> Map.member "<List as Clone>::clone" (ifTemplates iface))))
            ]
        ]
  where
    compiles = case libPackage of
        Error err -> Just err
        Ok _ -> Nothing
    orderIsDependencyFirst = case libPackage of
        Error err -> Just err
        Ok pkg -> testAssertEq (libOrder pkg) ["types", "eq", "clone", "prelude", "string", "map", "set"]
    allIn keys wanted = all (`elem` keys) wanted
    implsIn iface wanted = all (`Set.member` ifImpls iface) wanted
    both (Just err) _ = Just err
    both Nothing other = other
    interface name check = case libPackage of
        Error err -> Just err
        Ok pkg -> case Map.lookup name (libInterfaces pkg) of
            Nothing -> Just ("no interface for lib module " ++ name)
            Just iface -> testAssertTrue (check iface)
