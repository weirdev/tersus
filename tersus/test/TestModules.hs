module TestModules
    ( testModules
    ) where

import Control.Exception (bracket, evaluate, try, SomeException)
import Control.Monad (when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, removeDirectoryRecursive)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.FilePath ((</>))
import System.IO.Unsafe (unsafePerformIO)

import qualified AstData
import qualified Compile
import FileParserProtocol
import qualified FileParserProtocol as File
import Cli (Command (..), World (..), noWorld, runPackageFiles)
import Interface
import qualified Mir as M
import MirEval (renderMirValue, runProgram)
import Modules
import Parse
import qualified Parse as Oracle
import qualified TersusParser as NativeParser
import qualified Native
import Seed (emitterHash)
import PreludeSource (parserSource)
import LlvmRuntime (runtimeSource)
import Hash (fingerprint)
import System.Exit (ExitCode (..))
import Pipeline (CompiledModule (..), CompiledPackage (..), assumptionsOfPackage, compileModules, compileModulesToOwned, compileModulesToProgram, compileSource)
import Syntax
import Types
import TestHarness
import TypeCheck (elaborate)
import Utils (Result (..))

parsed :: String -> Either String [Statement]
parsed source = case parseStatementBlock source of
    Left err -> Left (show err)
    Right statements -> Right statements

showsPath :: String -> String -> TestResult
showsPath path source = case parsed source of
    Left err -> Just ("Parse failed: " ++ err ++ "\nProgram: " ++ source)
    Right statements ->
        if path `isInfixOf` show statements
            then Nothing
            else Just ("Expected path " ++ show path ++ " in parsed program, got: " ++ show statements)

testPaths :: Test
testPaths =
    testCaseSeq
        "paths"
        [ showsPath "a::b::Point" "fn f(x: a::b::Point) -> a::b::Point [{ }] [{ }] { return x; };"
        , case parseExpression "a::b::c::f(1)" of
            Left err -> Just ("Parse failed: " ++ show err)
            Right expr -> testAssertEq expr (F (Var "a::b::c::f") [Val (VInt 1)])
        , showsPath "geo::Point" "struct Point { x: Int }; p = geo::Point { x: 1 };"
        , showsPath "a::b::Shape::Circle" "enum Shape { Circle { r: Int }, Square { s: Int } }; p = a::b::Shape::Circle { r: 1 };"
        , showsPath "geo::Shape::Circle" "enum Shape { Circle { r: Int }, Square { s: Int } }; s = Shape::Circle { r: 1 }; match s { geo::Shape::Circle { r: r } => { y = r; }, geo::Shape::Square { s: q } => { y = q; } };"
        , showsPath "geo::Shape::Circle" "enum Shape { Circle { r: Int }, Square { s: Int } }; s = Shape::Circle { r: 1 }; y = s is geo::Shape::Circle; z = s as geo::Shape::Circle;"
        , showsPath "a::b::Seq" "fn f<S: a::b::Seq<Int>>(x: Int) -> Int [{ }] [{ }] { return x; };"
        , showsPath "a::b::Trait" "struct Point { x: Int }; impl a::b::Trait for geo::Point { fn get(self: &Self) -> Int [{ }] [{ }] { return 1; }; };"
        , showsPath "a::b::check" "fn f(x: Int) -> Int [{ affirm a::b::check(x); }] [{ }] { return x; };"
        , showsPath "geo::Vec" "struct Vec<T> { x: T }; fn f(v: geo::Vec<Int>) -> Int [{ }] [{ }] { return v.x; };"
        , showsPath "geo::types::Vec" "struct Vec<T> { x: T }; fn f(v: geo::types::Vec<Int>) -> Int [{ }] [{ }] { return v.x; };"
        ]

testMatchOverReference :: Test
testMatchOverReference =
    testCaseSeq
        "match-over-reference"
        [ case compileSource refProgram of
            Ok _ -> Nothing
            Error err -> Just ("Expected match over &RefStep to compile, got: " ++ err)
        , showsPath "geo::RefStep::Field" widenedProgram
        , case parsed otherArmProgram of
            Left err ->
                if "has an arm of another type" `isInfixOf` err
                    then Nothing
                    else Just ("Expected arm-of-another-type error, got: " ++ err)
            Right statements -> Just ("Expected arm-of-another-type failure, got: " ++ show statements)
        ]
  where
    decls = "struct Field { name: Int, ty: Int }; enum RefStep { Field { ctor: Int, field: Int }, Index { o: Int } }; "
    refProgram =
        decls
            ++ "fn pick(step: &RefStep) -> Int [{ }] [{ }] { n = 0; match step { RefStep::Field { ctor: c, field: f } => { n = c + f; }, RefStep::Index { o: o } => { n = o; }, }; return n; }; s = RefStep::Field { ctor: 1, field: 2 }; return pick(&s);"
    widenedProgram =
        decls
            ++ "fn pick(step: &RefStep) -> Int [{ }] [{ }] { n = 0; match step { geo::RefStep::Field { ctor: c, field: f } => { n = c + f; }, geo::RefStep::Index { o: o } => { n = o; }, }; return n; };"
    otherArmProgram =
        decls
            ++ "enum Other { Index { o: Int } }; fn pick(step: &RefStep) -> Int [{ }] [{ }] { n = 0; match step { RefStep::Field { ctor: c, field: f } => { n = c + f; }, Other::Index { o: o } => { n = o; }, }; return n; };"

testCanonical :: Test
testCanonical =
    testCaseSeq
        "canonical"
        [ case (parsed programA, parsed programB) of
            (Right a, Right b) ->
                let a' = canonicalizeDeclarations (fileModuleIdentity "pkg" "geo" "shapes.tersus") a
                    b' = canonicalizeDeclarations (fileModuleIdentity "pkg" "other" "shapes.tersus") b
                 in if declarationNames a' /= declarationNames b' && all ("pkg$geo$shapes$" `isInfixOf`) (declarationNames a')
                        then Nothing
                        else Just ("Expected distinct canonical names, got: " ++ show (declarationNames a', declarationNames b'))
            (Left err, _) -> Just ("Parse failed: " ++ err)
            (_, Left err) -> Just ("Parse failed: " ++ err)
        , case parsed programA of
            Left err -> Just ("Parse failed: " ++ err)
            Right a -> testAssertEq (canonicalizeDeclarations (rootModuleIdentity "pkg" "main.tersus") a) a
        , case parsed "enum Shape { Circle { r: Int } }; struct Point { x: Int };" of
            Left err -> Just ("Parse failed: " ++ err)
            Right a ->
                testAssertEq
                    (declarationNames (canonicalizeDeclarations (fileModuleIdentity "pkg" "geo" "shapes.tersus") a))
                    ["pkg$geo$shapes$Shape", "pkg$geo$shapes$Shape::Circle", "pkg$geo$shapes$Point"]
        , case parsed "struct Point { x: Int }; struct Point { y: Int };" of
            Left err -> Just ("Parse failed: " ++ err)
            Right a -> case elaborate (canonicalizeDeclarations (fileModuleIdentity "pkg" "geo" "shapes.tersus") a) of
                Error err ->
                    if "already defined" `isInfixOf` err
                        then Nothing
                        else Just ("Expected duplicate error, got: " ++ err)
                Ok _ -> Just "Expected duplicate declaration in one file to fail"
        ]
  where
    programA = "struct Point { x: Int }; fn area(p: Point) -> Int [{ }] [{ }] { return p.x; };"
    programB = programA

testImports :: Test
testImports =
    testCaseSeq
        "imports"
        [ case parseFile "import a::b::c; x = 1;" of
            Left err -> Just ("Parse failed: " ++ show err)
            Right parsed -> testAssertEq (fileImports parsed) [Import ["a", "b", "c"] Nothing Nothing 1 1]
        , case parseFile "import a::b::c as x; x = 1;" of
            Left err -> Just ("Parse failed: " ++ show err)
            Right parsed -> testAssertEq (fileImports parsed) [Import ["a", "b", "c"] (Just "x") Nothing 1 1]
        , case parseFile "import a::b::c { A, B }; x = 1;" of
            Left err -> Just ("Parse failed: " ++ show err)
            Right parsed -> testAssertEq (fileImports parsed) [Import ["a", "b", "c"] Nothing (Just ["A", "B"]) 1 1]
        , case parseFile "import a::b::c as x { A }; x = 1;" of
            Left err -> Just ("Parse failed: " ++ show err)
            Right parsed -> testAssertEq (fileImports parsed) [Import ["a", "b", "c"] (Just "x") (Just ["A"]) 1 1]
        , case parseFile "\nimport a::b;\nimport c::d as e { F };\nx = 1;" of
            Left err -> Just ("Parse failed: " ++ show err)
            Right parsed ->
                testAssertEq
                    (fileImports parsed)
                    [Import ["a", "b"] Nothing Nothing 2 1, Import ["c", "d"] (Just "e") (Just ["F"]) 3 1]
                    <> testAssertEq (length (fileBody parsed)) 1
        , case parseFile "x = 1; import a::b;" of
            Left err ->
                if "before any declaration" `isInfixOf` show err
                    then Nothing
                    else Just ("Expected import-after-declaration error, got: " ++ show err)
            Right parsed -> Just ("Expected parse failure, got: " ++ show parsed)
        , case parseFile "import a::b {};" of
            Left err ->
                if "must not be empty" `isInfixOf` show err
                    then Nothing
                    else Just ("Expected empty-list error, got: " ++ show err)
            Right parsed -> Just ("Expected parse failure, got: " ++ show parsed)
        , case parseFile "import a::b {  };" of
            Left err ->
                if "must not be empty" `isInfixOf` show err
                    then Nothing
                    else Just ("Expected empty-list error, got: " ++ show err)
            Right parsed -> Just ("Expected parse failure, got: " ++ show parsed)
        , case compileSource "import a::b::c; x = 1;" of
            Error err ->
                if "imports are not linked yet" `isInfixOf` err
                    then Nothing
                    else Just ("Expected not-linked error, got: " ++ err)
            Ok _ -> Just "Expected a file with imports to be rejected for now"
        , case compileSource "x = 1; return x;" of
            Ok _ -> Nothing
            Error err -> Just ("Expected existing single-file program to compile, got: " ++ err)
        ]

-- Loader tests (Phase 2): everything is in-memory through the resolver
-- except one filesystem case at the end.

type Files = [(FilePath, String)]

fnDecl :: String -> String
fnDecl name = "fn " ++ name ++ "(x: Int) -> Int [{ }] [{ }] { return x; };"

loadPkg :: Files -> FilePath -> Either String LoadedPackage
loadPkg files entry = case loadFromEntry (resolverFromFiles files) entry of
    Left err -> Left err
    Right (PackageResult pkg) -> Right pkg
    Right (StandaloneResult _ _) -> Left "expected a package, got a standalone program"

expectErr :: Files -> FilePath -> String -> TestResult
expectErr files entry needle = case loadPkg files entry of
    Left err ->
        if needle `isInfixOf` err
            then Nothing
            else Just ("Expected error containing " ++ show needle ++ ", got: " ++ err)
    Right pkg -> Just ("Expected load failure containing " ++ show needle ++ ", got: " ++ show (map (renderModuleId . loadedModuleId) (packageModules pkg)))

moduleOrder :: LoadedPackage -> [String]
moduleOrder pkg = map (renderModuleId . loadedModuleId) (packageModules pkg)

resolvedIn :: LoadedPackage -> String -> String -> [ResolvedImport]
resolvedIn pkg moduleName fileName =
    concat
        [ loadedImports file
        | modu <- packageModules pkg
        , renderModuleId (loadedModuleId modu) == moduleName
        , file <- loadedModuleFiles modu
        , loadedFileName file == fileName
        ]

basePkg :: Files
basePkg =
    [ ("app/package.tersus", "")
    , ("app/main.tersus", "import app::geo; x = 1;")
    , ("app/geo/geo.tersus", "struct Point { x: Int }; " ++ fnDecl "area")
    ]

collapsePkg :: Files
collapsePkg =
    [ ("app/package.tersus", "")
    , ("app/main.tersus", "import app::geo::Point; import app::geo::geo; import app::geo; import app::geo::geo::Point; x = 1;")
    , ("app/geo/geo.tersus", "struct Point { x: Int }; " ++ fnDecl "area")
    ]

multiFilePkg :: Files
multiFilePkg =
    [ ("app/package.tersus", "")
    , ("app/main.tersus", "import app::geo; x = 1;")
    , ("app/geo/shapes.tersus", "struct Point { x: Int };")
    , ("app/geo/extra.tersus", "import app::geo::shapes::Point; " ++ fnDecl "area")
    ]

testLoaderDiscovery :: Test
testLoaderDiscovery =
    testCaseSeq
        "loader-discovery"
        [ testAssertEq (discoverEntry (resolverFromFiles basePkg) "app/geo/geo.tersus") (InPackage "app" "app")
        , testAssertEq (discoverEntry (resolverFromFiles basePkg) "app/main.tersus") (InPackage "app" "app")
        , testAssertEq (discoverEntry (resolverFromFiles [("lonely/main.tersus", "x = 1;")]) "lonely/main.tersus") (Standalone "lonely/main.tersus")
        , case loadPkg basePkg "app/geo/geo.tersus" of
            Left err -> Just ("entry in module dir should load: " ++ err)
            Right pkg -> testAssertEq (packageEntryModule pkg) (ModuleId "app" (Just "geo"))
        , case loadPkg basePkg "app/main.tersus" of
            Left err -> Just ("entry in package root should load: " ++ err)
            Right pkg -> testAssertEq (packageEntryModule pkg) (ModuleId "app" Nothing)
        , case loadFromEntry (resolverFromFiles [("lonely/main.tersus", "x = 1;")]) "lonely/main.tersus" of
            Right (StandaloneResult _ _) -> Nothing
            other -> Just ("expected standalone result, got: " ++ show other)
        , case loadFromEntry (resolverFromFiles [("lonely/main.tersus", "import a::b; x = 1;")]) "lonely/main.tersus" of
            Left err ->
                if "standalone" `isInfixOf` err && "imports are not supported" `isInfixOf` err
                    then Nothing
                    else Just ("expected standalone-import error, got: " ++ err)
            Right result -> Just ("expected standalone import to fail, got: " ++ show result)
        ]

testLoaderGraph :: Test
testLoaderGraph =
    testCaseSeq
        "loader-graph"
        [ case loadPkg multiFilePkg "app/main.tersus" of
            Left err -> Just ("multi-file module should load: " ++ err)
            Right pkg ->
                let geo = [modu | modu <- packageModules pkg, loadedModuleId modu == ModuleId "app" (Just "geo")]
                 in case geo of
                        [modu] ->
                            testAssertEq (map loadedFileName (loadedModuleFiles modu)) ["extra.tersus", "shapes.tersus"]
                                <> testAssertTrue ("Point" `elem` loadedModuleDeclNames modu && "area" `elem` loadedModuleDeclNames modu)
                        _ -> Just ("expected exactly one geo module, got: " ++ show (moduleOrder pkg))
        , case loadPkg chainPkg "app/main.tersus" of
            Left err -> Just ("chain should load: " ++ err)
            Right pkg -> testAssertEq (moduleOrder pkg) ["app::b", "app::a", "app"]
        , case loadPkg diamondPkg "app/main.tersus" of
            Left err -> Just ("diamond should load: " ++ err)
            Right pkg -> testAssertEq (moduleOrder pkg) ["app::c", "app::a", "app::b", "app"]
        , expectErr cyclePkg "app/main.tersus" "module import cycle: app::a -> app::b -> app::a"
        , case loadPkg selfPkg "app/main.tersus" of
            Left err -> Just ("self-import should be ignored: " ++ err)
            Right pkg -> testAssertEq (moduleOrder pkg) ["app::geo", "app"]
        , case loadPkg
            [ ("pkgs/app/package.tersus", "")
            , ("pkgs/app/main.tersus", "import lib::geo; x = 1;")
            , ("pkgs/lib/package.tersus", "")
            , ("pkgs/lib/geo/geo.tersus", "struct Point { x: Int };")
            ]
            "pkgs/app/main.tersus" of
            Left err -> Just ("sibling package should load: " ++ err)
            Right pkg -> testAssertEq (moduleOrder pkg) ["lib::geo", "app"]
        , case loadPkg aliasPkg "app/main.tersus" of
            Left err -> Just ("different aliases in different files should load: " ++ err)
            Right pkg ->
                testAssertEq (map importAlias (map resolvedImport (resolvedIn pkg "app" "main.tersus"))) [Just "g"]
                    <> testAssertEq (map importAlias (map resolvedImport (resolvedIn pkg "app" "other.tersus"))) [Just "gg"]
        ]
  where
    chainPkg =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::a; x = 1;")
        , ("app/a/a.tersus", "import app::b; " ++ fnDecl "fa")
        , ("app/b/b.tersus", fnDecl "fb")
        ]
    diamondPkg =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::a; import app::b; x = 1;")
        , ("app/a/a.tersus", "import app::c; " ++ fnDecl "fa")
        , ("app/b/b.tersus", "import app::c; " ++ fnDecl "fb")
        , ("app/c/c.tersus", fnDecl "fc")
        ]
    cyclePkg =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::a; x = 1;")
        , ("app/a/a.tersus", "import app::b; " ++ fnDecl "fa")
        , ("app/b/b.tersus", "import app::a; " ++ fnDecl "fb")
        ]
    selfPkg =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; x = 1;")
        , ("app/geo/geo.tersus", "import app::geo; struct Point { x: Int };")
        ]
    aliasPkg =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo as g; x = 1;")
        , ("app/other.tersus", "import app::geo as gg; struct Local { x: Int };")
        , ("app/geo/geo.tersus", "struct Point { x: Int };")
        ]

testLoaderErrors :: Test
testLoaderErrors =
    testCaseSeq
        "loader-errors"
        [ expectErr
            [("app/package.tersus", ""), ("app/main.tersus", "import otherpkg::geo; x = 1;"), ("app/geo/geo.tersus", "struct Point { x: Int };")]
            "app/main.tersus"
            "package \"otherpkg\" not found"
        , expectErr
            [("app/package.tersus", ""), ("app/main.tersus", "import app::nope; x = 1;"), ("app/geo/geo.tersus", "struct Point { x: Int };")]
            "app/main.tersus"
            "\"nope\" is not a module of package app"
        , expectErr
            [("app/package.tersus", ""), ("app/main.tersus", "import app::nope; x = 1;"), ("app/geo/geo.tersus", "struct Point { x: Int };")]
            "app/main.tersus"
            "modules are: geo"
        , expectErr
            [("app/package.tersus", ""), ("app/main.tersus", "import app::geo::shapes::Nope; x = 1;"), ("app/geo/shapes.tersus", "struct Point { x: Int };")]
            "app/main.tersus"
            "symbol Nope is not declared in file shapes of module geo; it declares: Point"
        , expectErr
            [("app/package.tersus", ""), ("app/main.tersus", "import app::geo::shapes { Nope }; x = 1;"), ("app/geo/shapes.tersus", "struct Point { x: Int };")]
            "app/main.tersus"
            "name Nope is not declared there; it declares: Point"
        , expectErr
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; x = 1;")
            , ("app/geo/geo.tersus", "struct Point { x: Int };")
            , ("app/geo/bad.tersus", "struct Other { y: Int };\nx = 1;")
            ]
            "app/main.tersus"
            "modules declare, programs run"
        , expectErr
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; x = 1;")
            , ("app/geo/bad.tersus", "x = 1;")
            ]
            "app/main.tersus"
            "geo/bad.tersus"
        , expectErr
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; x = 1;")
            , ("app/geo/geo.tersus", "struct { x: Int };")
            ]
            "app/main.tersus"
            "parse error in module app::geo file app/geo/geo.tersus"
        , expectErr
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::Point; x = 1;")
            , ("app/geo.tersus", "struct Point { x: Int };")
            , ("app/geo/geo.tersus", "struct Point { x: Int };")
            ]
            "app/main.tersus"
            "ambiguous import"
        , expectErr
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::deep; x = 1;")
            , ("app/geo/geo.tersus", "struct Point { x: Int };")
            , ("app/geo/deep/deep.tersus", "struct Deep { x: Int };")
            ]
            "app/main.tersus"
            "deeper nesting is not a module"
        ]

testLoaderLevels :: Test
testLoaderLevels =
    testCaseSeq
        "loader-levels"
        [ case loadPkg collapsePkg "app/main.tersus" of
            Left err -> Just ("collapse package should load: " ++ err)
            Right pkg ->
                let resolved = resolvedIn pkg "app" "main.tersus"
                 in testAssertEq
                        (map resolvedLevel resolved)
                        [LevelSymbol, LevelFile, LevelModule, LevelSymbol]
                        <> testAssertEq (map resolvedTargetFile resolved) [Just "geo", Just "geo", Nothing, Just "geo"]
                        <> testAssertEq (map resolvedTargetSymbol resolved) [Just "Point", Nothing, Nothing, Just "Point"]
                        <> testAssertEq (map resolvedCanonical resolved) ["app$geo$geo$Point", "app$geo$geo", "app$geo", "app$geo$geo$Point"]
        , case loadPkg multiFilePkg "app/main.tersus" of
            Left err -> Just ("multi-file package should load: " ++ err)
            Right pkg ->
                let sibling = resolvedIn pkg "app::geo" "extra.tersus"
                 in testAssertEq (map resolvedLevel sibling) [LevelSymbol]
                        <> testAssertEq (map resolvedTargetModule sibling) [ModuleId "app" (Just "geo")]
        , case loadPkg
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::shapes; x = 1;")
            , ("app/geo/shapes.tersus", "struct Point { x: Int };")
            , ("app/geo/extra.tersus", fnDecl "area")
            ]
            "app/main.tersus" of
            Left err -> Just ("file-level import should load: " ++ err)
            Right pkg -> testAssertEq (map resolvedLevel (resolvedIn pkg "app" "main.tersus")) [LevelFile]
        , expectErr
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::Point; x = 1;")
            , ("app/geo/geo.tersus", "struct Point { x: Int };")
            , ("app/geo/extra.tersus", fnDecl "area")
            ]
            "app/main.tersus"
            "write app::geo::geo::Point instead of app::geo::Point"
        , expectErr
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::Point; x = 1;")
            , ("app/geo/geo.tersus", "struct Point { x: Int };")
            , ("app/geo/extra.tersus", fnDecl "area")
            ]
            "app/main.tersus"
            "has grown to 2 files"
        , expectErr
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::Point; x = 1;")
            , ("app/geo/shapes.tersus", "struct Point { x: Int };")
            , ("app/geo/extra.tersus", fnDecl "area")
            ]
            "app/main.tersus"
            "write app::geo::shapes::Point"
        ]

testLoaderFilesystem :: Test
testLoaderFilesystem = TestCase "loader-filesystem" $ do
    let root = "/tmp/tersus-modules-phase2-test"
        pkgDir = root </> "app"
    exists <- doesDirectoryExist root
    when exists (removeDirectoryRecursive root)
    result <- try (runFs root pkgDir) :: IO (Either SomeException TestResult)
    return (case result of
        Left ex -> Just ("filesystem loader crashed: " ++ show ex)
        Right value -> value)
  where
    runFs root pkgDir = do
        createDirectoryIfMissing True (pkgDir </> "geo")
        writeFile (pkgDir </> "package.tersus") ""
        writeFile (pkgDir </> "main.tersus") "import app::geo; x = 1;"
        writeFile (pkgDir </> "geo" </> "geo.tersus") "struct Point { x: Int };"
        loaded <- loadFromFilesystem (pkgDir </> "main.tersus")
        injected <- loadFromFilesystemWith injectedFileParser (pkgDir </> "main.tersus")
        return ((case loaded of
            Left err -> Just ("filesystem load failed: " ++ err)
            Right (PackageResult pkg) -> testAssertEq (moduleOrder pkg) ["app::geo", "app"]
            Right other -> Just ("expected a package result, got: " ++ show other))
            <> case injected of
                Left err -> testAssertTrue ("injected refusal sentinel" `isInfixOf` err)
                Right _ -> Just "filesystem loader did not use injected parser")
        `finallyRemove` root
    finallyRemove action dir = do
        value <- action
        removeDirectoryRecursive dir
        return value

-- Phase 3: per-module checking against interfaces.

compilePkg :: Files -> FilePath -> Either String CompiledPackage
compilePkg files entry = case loadPkg files entry of
    Left err -> Left err
    Right pkg -> case compileModules pkg of
        Error err -> Left err
        Ok compiled -> Right compiled

expectCompiles :: Files -> FilePath -> TestResult
expectCompiles files entry = case compilePkg files entry of
    Left err -> Just ("Expected modules to compile, got: " ++ err)
    Right _ -> Nothing

expectCompileError :: Files -> FilePath -> String -> TestResult
expectCompileError files entry needle = case compilePkg files entry of
    Left err ->
        if needle `isInfixOf` err
            then Nothing
            else Just ("Expected compile error containing " ++ show needle ++ ", got: " ++ err)
    Right compiled -> Just ("Expected compile failure containing " ++ show needle ++ ", got modules: " ++ show (map (renderModuleId . compiledModuleId) (compiledModules compiled)))

compiledNamed :: CompiledPackage -> String -> Maybe CompiledModule
compiledNamed compiled name = case [modu | modu <- compiledModules compiled, renderModuleId (compiledModuleId modu) == name] of
    modu : _ -> Just modu
    [] -> Nothing

geoFiles :: String -> Files
geoFiles mainSource =
    [ ("app/package.tersus", "")
    , ("app/main.tersus", mainSource)
    , ("app/geo/geo.tersus", "struct Point { x: Int }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; }; fn area(p: Point) -> Int [{ }] [{ }] { return p.x; };")
    ]

testModuleCheckBasic :: Test
testModuleCheckBasic =
    testCaseSeq
        "module-check-basic"
        [ expectCompiles (geoFiles "import app::geo; p = geo::make(3); return geo::area(p);") "app/main.tersus"
        , expectCompiles (geoFiles "import app::geo as g; p = g::make(3); return g::area(p);") "app/main.tersus"
        , expectCompiles (geoFiles "import app::geo; p = app::geo::geo::make(3); return app::geo::geo::area(p);") "app/main.tersus"
        , expectCompiles (geoFiles "import app::geo::geo::Point; import app::geo::geo::make; import app::geo::geo::area; p = make(3); return area(p);") "app/main.tersus"
        , expectCompiles (geoFiles "import app::geo { Point, make, area }; p = make(3); return area(p);") "app/main.tersus"
        , expectCompiles
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::shapes; p = shapes::make(4); return shapes::area(p);")
            , ("app/geo/shapes.tersus", "struct Point { x: Int }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; }; fn area(p: Point) -> Int [{ }] [{ }] { return p.x; };")
            , ("app/geo/extra.tersus", "fn extra(x: Int) -> Int [{ }] [{ }] { return x + 1; };")
            ]
            "app/main.tersus"
        , expectCompileError
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "p = geo::make(3); return p.x;")
            , ("app/other.tersus", "import app::geo; struct Local { x: Int };")
            , ("app/geo/geo.tersus", "struct Point { x: Int }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; };")
            ]
            "app/main.tersus"
            "covering import"
        , expectCompileError
            (geoFiles "import app::geo { Point }; struct Point { x: Int }; p = geo::make(3); return p.x;")
            "app/main.tersus"
            "ambiguous"
        , expectCompiles
            (geoFiles "import app::geo; struct Wrapper { p: geo::Point, n: Int }; fn get(w: Wrapper) -> Int [{ }] [{ }] { return w.p.x + w.n; }; p = geo::make(3); w = Wrapper { p: p, n: 1 }; return get(w);")
            "app/main.tersus"
        ]

testModuleCheckTraits :: Test
testModuleCheckTraits =
    testCaseSeq
        "module-check-traits"
        [ expectCompiles traitFiles "app/main.tersus"
        , case compilePkg traitFiles "app/main.tersus" of
            Left err -> Just ("trait package should compile: " ++ err)
            Right compiled -> case compiledNamed compiled "app::geo" of
                Just modu ->
                    testAssertTrue (("app$geo$geo$Scalable", "app$geo$geo$Point") `elem` foldr (:) [] (ifImpls (compiledInterface modu)))
                Nothing -> Just "expected a compiled app::geo module"
        , expectCompiles
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; fn use(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return >= 0; affirm geo::positive(return) = return; }] { return geo::positive(x); }; return use(1);")
            , ("app/geo/geo.tersus", "fn positive(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return >= 0; }] { return x; };")
            ]
            "app/main.tersus"
        , case compilePkg axiomFiles "app/main.tersus" of
            Left err -> Just ("axiom package should compile: " ++ err)
            Right compiled -> case compiledNamed compiled "app" of
                Just modu ->
                    if "app$geo$geo$nonnegAxiom" `isInfixOf` show (compiledStatements modu)
                        then Nothing
                        else Just ("expected the cross-module axiom name in elaborated root statements, got: " ++ show (compiledStatements modu))
                Nothing -> Just "expected a compiled root module"
        , expectCompileError boundedFiles "app/main.tersus" "bounded function"
        , expectCompileError boundedFiles "app/main.tersus" "cannot be exported"
        , expectCompileError orphanFiles "app/main.tersus" "orphan impl"
        , case compilePkg externFiles "app/main.tersus" of
            Left err -> Just ("extern package should compile: " ++ err)
            Right compiled -> case compiledNamed compiled "app::geo" of
                Just modu -> testAssertTrue ("app$geo$geo$cfunc" `elem` foldr (:) [] (ifExterns (compiledInterface modu)))
                Nothing -> Just "expected a compiled app::geo module"
        ]
  where
    traitFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; p = geo::make(3); return p.scale(4);")
        , ("app/geo/geo.tersus", "trait Scalable { fn scale(self: &Self, k: Int) -> Int [{ }] [{ }]; }; struct Point { x: Int }; impl Scalable for Point { fn scale(self: &Self, k: Int) -> Int [{ }] [{ }] { return self.x * k; }; }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; };")
        ]
    axiomFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo::geo::nonnegAxiom; fn use(x: Int) -> Int [{ }] [{ rewrite nonnegAxiom return; affirm return >= 0; }] { return x; }; return use(1);")
        , ("app/geo/geo.tersus", "axiom nonnegAxiom(x) [{ }] [{ affirm x >= 0; }];")
        ]
    boundedFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; return geo::marked(1);")
        , ("app/geo/geo.tersus", "trait Marker { }; fn marked<S: Marker>(x: Int) -> Int [{ }] [{ }] { return x; };")
        ]
    orphanFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::other; x = 1;")
        , ("app/other/other.tersus", "import app::geo; impl geo::Scalable for geo::Point { fn scale(self: &Self, k: Int) -> Int [{ }] [{ }] { return self.x * k; }; };")
        , ("app/geo/geo.tersus", "trait Scalable { fn scale(self: &Self, k: Int) -> Int [{ }] [{ }]; }; struct Point { x: Int }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; };")
        ]
    externFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; return geo::cfunc(1);")
        , ("app/geo/geo.tersus", "extern fn cfunc(x: Int) -> Int [{ }] [{ }];")
        ]

testModuleCheckWithin :: Test
testModuleCheckWithin =
    testCaseSeq
        "module-check-within"
        [ expectCompiles withinFiles "app/main.tersus"
        , expectCompileError
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; x = 1;")
            , ("app/geo/left.tersus", "import app::geo::right; struct Left { r: right::Right };")
            , ("app/geo/right.tersus", "import app::geo::left; struct Right { l: left::Left };")
            ]
            "app/main.tersus"
            "holds itself"
        ]
  where
    withinFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; a = geo::shapes::make(3); b = geo::extra::makeOther(4); return geo::extra::area(a) + geo::extra::getOther(b) + geo::use::areaFull(a) + geo::a::fa(1);")
        , ("app/geo/shapes.tersus", "struct Point { x: Int }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; };")
        , ("app/geo/extra.tersus", "import app::geo::shapes; struct Point { y: Int }; fn makeOther(y: Int) -> Point [{ }] [{ }] { return Point { y: y }; }; fn getOther(p: Point) -> Int [{ }] [{ }] { return p.y; }; fn area(p: shapes::Point) -> Int [{ }] [{ }] { return p.x; };")
        , ("app/geo/use.tersus", "import app::geo; fn areaFull(p: app::geo::shapes::Point) -> Int [{ }] [{ }] { return app::geo::extra::area(p); };")
        , ("app/geo/a.tersus", "import app::geo::b; fn fa(x: Int) -> Int [{ }] [{ }] { return b::fb(x); };")
        , ("app/geo/b.tersus", "import app::geo::a; fn fb(x: Int) -> Int [{ }] [{ }] { if x > 0 { return a::fa(0); }; return x; };")
        ]

-- Phase 4/5: per-module lowering, linking and the pipeline/CLI path.

programPkg :: Files -> FilePath -> Either String M.Program
programPkg files entry = case loadPkg files entry of
    Left err -> Left err
    Right pkg -> case compileModulesToProgram pkg of
        Error err -> Left err
        Ok program -> Right program

ownedPkg :: Files -> FilePath -> Either String M.Program
ownedPkg files entry = case loadPkg files entry of
    Left err -> Left err
    Right pkg -> case compileModulesToOwned pkg of
        Error err -> Left err
        Ok program -> Right program

expectRuns :: Files -> FilePath -> String -> TestResult
expectRuns files entry expected = case programPkg files entry of
    Left err -> Just ("Expected package to compile and run, got: " ++ err)
    Right program -> case runProgram program of
        Error err -> Just ("Expected package to run, got: " ++ err)
        Ok value -> testAssertEq (fmap renderMirValue value) (Just expected)

expectProgramError :: Files -> FilePath -> String -> TestResult
expectProgramError files entry needle = case programPkg files entry of
    Left err ->
        if needle `isInfixOf` err
            then Nothing
            else Just ("Expected program error containing " ++ show needle ++ ", got: " ++ err)
    Right program -> Just ("Expected program failure containing " ++ show needle ++ ", got functions: " ++ show (Map.keys (M.progFunctions program)))

linkGeo :: String
linkGeo = "struct Point { x: Int }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; }; fn area(p: Point) -> Int [{ }] [{ }] { return p.x; }; fn unrelated(x: Int) -> Int [{ }] [{ }] { return x * 2; };"

testModuleLinkEval :: Test
testModuleLinkEval =
    testCaseSeq
        "module-link-eval"
        [ expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; p = geo::Point { x: 3 }; q = geo::make(4); return geo::area(p) + geo::area(q);")
            , ("app/geo/geo.tersus", linkGeo)
            ]
            "app/main.tersus"
            "7"
        , expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; s = geo::Shape::Circle { r: 5 }; y = 0; match s { geo::Shape::Circle { r: r } => { y = r; }, geo::Shape::Square { s: q } => { y = q; } }; return y;")
            , ("app/geo/geo.tersus", "enum Shape { Circle { r: Int }, Square { s: Int } };")
            ]
            "app/main.tersus"
            "5"
        , expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::geo::Point; p = Point { x: 5 }; return p.x;")
            , ("app/geo/geo.tersus", linkGeo)
            ]
            "app/main.tersus"
            "5"
        ]

testModuleLinkPrune :: Test
testModuleLinkPrune =
    testCaseSeq
        "module-link-prune"
        [ case ownedPkg selectiveFiles "app/main.tersus" of
            Left err -> Just ("selective package should compile to owned MIR: " ++ err)
            Right program ->
                let rendered = M.renderProgram program
                 in testAssertTrue (not ("unrelated" `isInfixOf` rendered))
                        <> testAssertTrue (not ("make" `isInfixOf` rendered))
                        <> testAssertTrue ("Point" `isInfixOf` rendered)
        , case programPkg selectiveFiles "app/main.tersus" of
            Left err -> Just ("selective package should compile: " ++ err)
            Right program -> testAssertTrue (not ("unrelated" `isInfixOf` M.renderProgram program))
        ]
  where
    selectiveFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo::geo::Point; p = Point { x: 5 }; return p.x;")
        , ("app/geo/geo.tersus", linkGeo)
        ]

testModuleLinkGenerics :: Test
testModuleLinkGenerics =
    testCaseSeq
        "module-link-generics"
        [ expectRuns genericFiles "app/main.tersus" "9"
        , case ownedPkg genericFiles "app/main.tersus" of
            Left err -> Just ("generic package should compile to owned MIR: " ++ err)
            Right program -> testAssertTrue ("pick<" `isInfixOf` M.renderProgram program)
        ]
  where
    genericFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; struct Local { v: Int }; l = Local { v: 9 }; r = geo::pick(l); return r.v;")
        , ("app/geo/geo.tersus", "fn pick<T>(x: T) -> T [{ }] [{ }] { return x; };")
        ]

testModuleLinkDrop :: Test
testModuleLinkDrop =
    testCaseSeq
        "module-link-drop"
        [ expectRuns dropFiles "app/main.tersus" "2"
        , case ownedPkg dropFiles "app/main.tersus" of
            Left err -> Just ("drop package should compile to owned MIR: " ++ err)
            Right program ->
                let rendered = M.renderProgram program
                 in testAssertTrue ("<app$geo$geo$Token as Drop>::drop" `isInfixOf` rendered)
                        <> testAssertTrue ("drop " `isInfixOf` rendered)
        , expectRuns dropSuppressedPreludeFiles "app/main.tersus" "2"
        , case ownedPkg dropSuppressedPreludeFiles "app/main.tersus" of
            Left err -> Just ("drop with a suppressed prelude should compile to owned MIR: " ++ err)
            Right program -> testAssertTrue ("<app$geo$geo$Token as Drop>::drop" `isInfixOf` M.renderProgram program)
        ]
  where
    dropFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; t = geo::Token::new(2); return t.n;")
        , ("app/geo/geo.tersus", "struct Token { addr: Addr<Int>, n: Int, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = n; affirm count(blk) = 0; affirm n >= 0; }]; impl Token { fn new(n: Int) -> Self [{ affirm n >= 0; }] [{ }] { (a, b) = Addr::alloc(n); return Self { addr: a, n: n, blk: b }; }; }; impl Drop for Token { fn drop(self: Self) -> Int [{ }] [{ }] { return Addr::free(self.addr, self.blk); }; };")
        ]
    -- (the geo module declares a prelude trait of its own, so the prelude
    -- is not selected for it, but its impl Drop still sees the Drop trait)
    dropSuppressedPreludeFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; t = geo::Token::new(2); return t.n;")
        , ("app/geo/geo.tersus", "trait Sequence<E> { fn size(self: &Self) -> Int; }; struct Token { addr: Addr<Int>, n: Int, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = n; affirm count(blk) = 0; affirm n >= 0; }]; impl Token { fn new(n: Int) -> Self [{ affirm n >= 0; }] [{ }] { (a, b) = Addr::alloc(n); return Self { addr: a, n: n, blk: b }; }; }; impl Drop for Token { fn drop(self: Self) -> Int [{ }] [{ }] { return Addr::free(self.addr, self.blk); }; };")
        ]

testModuleLinkMutual :: Test
testModuleLinkMutual =
    testCaseSeq
        "module-link-mutual"
        [ expectRuns mutualFiles "app/main.tersus" "0"
        , expectErr cycleFiles "app/main.tersus" "module import cycle: app::a -> app::b -> app::a"
        ]
  where
    mutualFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; return geo::a::fa(1);")
        , ("app/geo/a.tersus", "import app::geo::b; fn fa(x: Int) -> Int [{ }] [{ }] ~ { if x > 0 { return b::fb(0); }; return x; };")
        , ("app/geo/b.tersus", "import app::geo::a; fn fb(x: Int) -> Int [{ }] [{ }] ~ { return a::fa(x); };")
        ]
    cycleFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::a; x = 1;")
        , ("app/a/a.tersus", "import app::b; " ++ fnDecl "fa")
        , ("app/b/b.tersus", "import app::a; " ++ fnDecl "fb")
        ]

testModuleLinkRoot :: Test
testModuleLinkRoot =
    testCaseSeq
        "module-link-root"
        [ case (programPkg rootFiles "app/main.tersus", compileSource rootSource) of
            (Left err, _) -> Just ("root package should compile: " ++ err)
            (_, Error err) -> Just ("single-file equivalent should compile: " ++ err)
            (Right packaged, Ok single) -> testAssertEq packaged single
        ]
  where
    rootSource = "fn add(a: Int, b: Int) -> Int [{ }] [{ }] { return a + b; }; return add(1, 2);"
    rootFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", rootSource)
        ]

testModuleLinkExtern :: Test
testModuleLinkExtern =
    testCaseSeq
        "module-link-extern"
        [ case programPkg externFiles "app/main.tersus" of
            Left err -> Just ("identical externs should link: " ++ err)
            Right program -> testAssertEq [name | name <- Map.keys (M.progFunctions program), name == "extern cfunc"] ["extern cfunc"]
        , expectProgramError conflictFiles "app/main.tersus" "extern fn cfunc"
        , expectProgramError conflictFiles "app/main.tersus" "app::geo"
        , expectProgramError conflictFiles "app/main.tersus" "app::other"
        ]
  where
    externDecl ret = "extern fn cfunc(x: Int) -> " ++ ret ++ " [{ }] [{ }]; fn use(x: Int) -> Int [{ }] [{ }] { return cfunc(x); };"
    externFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; import app::other; return geo::use(1) + other::use(1);")
        , ("app/geo/geo.tersus", externDecl "Int")
        , ("app/other/other.tersus", externDecl "Int")
        ]
    conflictFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; import app::other; return geo::use(1) + other::use(1);")
        , ("app/geo/geo.tersus", externDecl "Int")
        , ("app/other/other.tersus", "extern fn cfunc(x: Int) -> Bool [{ }] [{ }]; fn use(x: Int) -> Int [{ }] [{ }] { if cfunc(x) { return 1; }; return 0; };")
        ]

testModuleAssumptions :: Test
testModuleAssumptions =
    testCaseSeq
        "module-assumptions"
        [ case loadPkg assumptionFiles "app/main.tersus" of
            Left err -> Just ("assumption package should load: " ++ err)
            Right pkg -> case compileModules pkg of
                Error err -> Just ("assumption package should compile: " ++ err)
                Ok compiled ->
                    let found = assumptionsOfPackage compiled
                     in testAssertTrue (any ("in module app::geo: axiom nonnegAxiom" `isInfixOf`) found)
                            <> testAssertTrue (any ("in module app::geo: extern fn cfunc" `isInfixOf`) found)
        ]
  where
    assumptionFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; return geo::use(1);")
        , ("app/geo/geo.tersus", "axiom nonnegAxiom(x) [{ }] [{ affirm x >= 0; }]; extern fn cfunc(x: Int) -> Int [{ }] [{ }]; fn use(x: Int) -> Int [{ }] [{ }] { return x; };")
        ]

testModuleCliFilesystem :: Test
testModuleCliFilesystem = TestCase "module-cli-filesystem" $ do
    let root = "/tmp/tersus-modules-phase5-test"
        pkgDir = root </> "app"
    exists <- doesDirectoryExist root
    when exists (removeDirectoryRecursive root)
    result <- try (runFs root pkgDir) :: IO (Either SomeException TestResult)
    return (case result of
        Left ex -> Just ("CLI filesystem case crashed: " ++ show ex)
        Right value -> value)
  where
    runFs root pkgDir = do
        createDirectoryIfMissing True (pkgDir </> "geo")
        writeFile (pkgDir </> "package.tersus") ""
        writeFile (pkgDir </> "main.tersus") "import app::geo; p = geo::Point { x: 3 }; return geo::area(p);"
        writeFile (pkgDir </> "geo" </> "geo.tersus") "struct Point { x: Int }; fn area(p: Point) -> Int [{ }] [{ }] { return p.x; };"
        loaded <- loadFromFilesystem (pkgDir </> "main.tersus")
        value <- case loaded of
            Left err -> return (Just ("filesystem load failed: " ++ err))
            Right (PackageResult pkg) -> return (case runPackageFiles noWorld Interpret pkg of
                Error err -> Just ("package eval failed: " ++ err)
                Ok ((output, _), _) -> if output == "3" then Nothing else Just ("expected package eval to print 3, got: " ++ show output))
            Right other -> return (Just ("expected a package result, got: " ++ show other))
        removeDirectoryRecursive root
        return value

testModuleLibraries :: Test
testModuleLibraries =
    testCaseSeq
        "module-libraries"
        [ expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; return geo::greetingSize();")
            , ("app/geo/geo.tersus", "fn greetingSize() -> Int [{ }] [{ }] { s = \"hi\".concat(\"!\"); return size(s); };")
            ]
            "app/main.tersus"
            "3"
        , expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; import app::other; return geo::greetingSize() + other::wordSize();")
            , ("app/geo/geo.tersus", "fn greetingSize() -> Int [{ }] [{ }] { s = \"hi\".concat(\"!\"); return size(s); };")
            , ("app/other/other.tersus", "fn wordSize() -> Int [{ }] [{ }] { s = \"abcd\"; return size(s); };")
            ]
            "app/main.tersus"
            "7"
        , expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; m = geo::counts(); return m;")
            , ("app/geo/geo.tersus", "fn counts() -> Int [{ }] [{ }] { counts = HashMap::new(); counts = counts.insert(\"the\", 40); counts = counts.insert(\"cat\", 1); counts = counts.insert(\"the\", 41); return counts.lookup(\"the\", 0) + counts.size(); };")
            ]
            "app/main.tersus"
            "43"
        , expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; p = geo::make(21); return geo::twice(p);")
            , ("app/geo/geo.tersus", "struct Point { x: Int }; impl Clone for Point { }; impl Eq for Point { }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; }; fn twice(p: Point) -> Int [{ }] [{ }] { q = clone(p); if q = p { return p.x + q.x; }; return 0; };")
            ]
            "app/main.tersus"
            "42"
        , expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; a = geo::make(5); b = geo::make(5); if a = b { return 1; }; return 0;")
            , ("app/geo/geo.tersus", "struct Point { x: Int }; impl Clone for Point { }; impl Eq for Point { }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; };")
            ]
            "app/main.tersus"
            "1"
        , expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; s = geo::greeting(); return size(s);")
            , ("app/geo/geo.tersus", "fn greeting() -> String [{ }] [{ }] { return \"hi\".concat(\"!\"); };")
            ]
            "app/main.tersus"
            "3"
        ]

borrowGeo :: String
borrowGeo = "fn headOf(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); };"

testModuleLinkBorrow :: Test
testModuleLinkBorrow =
    testCaseSeq
        "module-link-borrow"
        [ expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; ys = [10, 20, 30]; r = geo::headOf(ys); return *r;")
            , ("app/geo/geo.tersus", borrowGeo)
            ]
            "app/main.tersus"
            "10"
        , expectProgramError
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; ys = [10, 20, 30]; r = geo::headOf(ys); ys = [40, 50]; return *r;")
            , ("app/geo/geo.tersus", borrowGeo)
            ]
            "app/main.tersus"
            "cannot be assigned while it is borrowed"
        ]

testModuleQualifiedGenerics :: Test
testModuleQualifiedGenerics =
    testCaseSeq
        "module-qualified-generics"
        [ expectRuns collapsedFiles "app/main.tersus" "9"
        , expectRuns filedFiles "app/main.tersus" "9"
        ]
  where
    collapsedFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; fn getX(v: geo::Vec<Int>) -> Int [{ }] [{ }] { return v.x; }; w = geo::makeVec(9); return getX(w);")
        , ("app/geo/geo.tersus", "struct Vec<T> { x: T }; fn makeVec(v: Int) -> Vec<Int> [{ }] [{ }] { return Vec<Int> { x: v }; };")
        ]
    filedFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; fn getY(v: geo::types::Boxed<Int>) -> Int [{ }] [{ }] { return v.y; }; b = geo::types::makeBoxed(9); return getY(b);")
        , ("app/geo/geo.tersus", "fn placeholder(x: Int) -> Int [{ }] [{ }] { return x; };")
        , ("app/geo/types.tersus", "struct Boxed<T> { y: T }; fn makeBoxed(v: Int) -> Boxed<Int> [{ }] [{ }] { return Boxed<Int> { y: v }; };")
        ]

sameDecls :: Decls -> Decls -> TestResult
sameDecls actual expected =
    testAssertEq (declCtors actual) (declCtors expected)
        <> testAssertEq (declTypes actual) (declTypes expected)
        <> testAssertEq (declSelf actual) (declSelf expected)
        <> testAssertEq (declSelfType actual) (declSelfType expected)
        <> testAssertEq (declTypeParams actual) (declTypeParams expected)
        <> testAssertEq (declGenerics actual) (declGenerics expected)
        <> testAssertEq (declImplParams actual) (declImplParams expected)
        <> testAssertEq (declOwnClone actual) (declOwnClone expected)
        <> testAssertEq (declLocate actual) (declLocate expected)
        <> testAssertEq (declFieldTypes actual) (declFieldTypes expected)

protocolDecls :: Decls
protocolDecls = Decls
    (Map.fromList [("pkg$geo$Shape::Circle", ["z", "a"]), ("Empty", [])])
    (Map.fromList [("pkg$geo$Shape", ["pkg$geo$Shape::Circle", "pkg$geo$Shape::Square"]), ("Empty", [])])
    (Just "pkg$geo$Self\"\\\nλ")
    (Just (TNamed "pkg$geo$Vec" [ArgSize (SizeParam "N"), ArgType (TParam "T")]))
    ["T", "U"]
    (Map.fromList [("pkg$geo$Vec", ["N", "T"]), ("Empty", [])])
    ["U", "M"]
    True
    True
    (Map.fromList [("pkg$geo$Vec", zip (map (\n -> "f" ++ show n) [0 :: Int ..]) fieldTypes), ("Empty", [])])
  where
    fieldTypes =
        [ TInt, TByte, TWord True 8, TWord True 16, TWord True 32, TWord False 16, TWord False 32, TBool
        , TList TInt, TArrayOf TByte (SizeConst 5), TArrayOf TInt SizeAny
        , TArrayOf TInt (SizeParam "N"), TArrayOf TInt (SizeVar 7)
        , TBox TInt, TAddr TInt, TUninit TInt, TBlock TInt
        , TFn [TRef (TParam "T"), TMutRef TByte] TBool
        , TNamed "pkg$geo$Vec" [ArgSize (SizeConst 2), ArgType (TList (TParam "T"))]
        , TVariant "pkg$geo$Shape::Circle", TVar 9
        , TForall ["N"] ["T"] (TArrayOf (TParam "T") (SizeParam "N")), TParam "T", TRef TInt, TMutRef TInt
        ]

emptyDeclRecords :: String
emptyDeclRecords = unlines
    [ "decls", "ctors 0", "types 0", "self none", "selfType none", "typeParams 0"
    , "generics 0", "implParams 0", "ownClone false", "locate false", "fieldTypes 0", "endDecls"
    ]

replaceRecord :: String -> String -> String -> String
replaceRecord old new = concatMap (\line -> if line == old then new ++ "\n" else line ++ "\n") . lines

protocolRefuses :: Result a String -> TestResult
protocolRefuses (Error _) = Nothing
protocolRefuses (Ok _) = Just "expected protocol refusal"

testFileProtocol :: Test
testFileProtocol = TestList "file-protocol"
    [ testCaseSeq "request-roundtrip"
        [ case writeFileRequest decls source of
            Error err -> Just ("request writer failed: " ++ err)
            Ok wire -> case readFileRequest wire of
                Error err -> Just ("request reader failed: " ++ err)
                Ok (actual, text) -> sameDecls actual decls <> testAssertEq text source
        | decls <- [emptyDecls, protocolDecls, protocolDecls{declSelf = Nothing}, protocolDecls{declSelfType = Nothing, declOwnClone = False, declLocate = False}]
        , source <- ["", "raw λ 🙂\nsource 0\n\"\\\NULtail", replicate 33000 'x', "no final newline"]
        ]
    , testCaseSeq "reply-roundtrip"
        [ case writeParsedFile parsedFile decls of
            Error err -> Just ("reply writer failed: " ++ err)
            Ok wire -> case readParsedFile wire of
                Error err -> Just ("reply reader failed: " ++ err)
                Ok (actual, ds) -> testAssertEq actual parsedFile <> sameDecls ds decls
        | decls <- [emptyDecls, protocolDecls]
        , parsedFile <- [ParsedFile [] [], ParsedFile imports [Mark 7 9, StructDef "pkg$geo$Vec" ["T"] [("x", TRef (TParam "T"))] [], Return (Val (VInt 77))]]
        ]
    , testCase "exact-request-wire" $ case writeFileRequest emptyDecls "λ" of
        Error err -> Just err
        Ok wire -> testAssertEq wire ("tersus-file-parse 1\n" ++ emptyDeclRecords ++ "source 2\n\xCE\xBB")
    , testCase "exact-reply-wire" $ case (writeParsedFile (ParsedFile [Import ["app", "geo"] (Just "g") (Just ["Point"]) 2 3] []) emptyDecls, AstData.writeParsed []) of
        (Ok wire, Ok ast) -> testAssertEq wire ("tersus-file 1\nimports 1\nimport 2 3 2 \"app\" \"geo\" some \"g\" some 1 \"Point\"\n" ++ emptyDeclRecords ++ "ast\n" ++ ast)
        _ -> Just "reply or AST writer failed"
    , testCaseSeq "strict-declarations"
        [ protocolRefuses (readFileRequest ("tersus-file-parse 1\n" ++ replaceRecord old new emptyDeclRecords ++ "source 0\n"))
        | (old, new) <-
            [ ("ctors 0", "ctors -1"), ("ctors 0", "ctors 9223372036854775808"), ("ctors 0", "ctors 9223372036854775807")
            , ("ctors 0", "ctors 2\nctor \"T\" 0\nctor \"T\" 0")
            , ("types 0", "types 2\ntype \"T\" 0\ntype \"T\" 0")
            , ("generics 0", "generics 2\ngeneric \"T\" 0\ngeneric \"T\" 0")
            , ("fieldTypes 0", "fieldTypes 2\nfields \"T\" 0\nfields \"T\" 0")
            , ("ctors 0", "ctors 1\nctor \"T\" 2 \"a\"")
            , ("ctors 0", "ctors 1\nctor \"\\xFF\" 0")
            , ("ctors 0", "ctors 1\nctor \"λ\" 0")
            , ("typeParams 0", "typeParams -1"), ("typeParams 0", "typeParams 999999999 \"T\"")
            , ("self none", "self other"), ("self none", "self some"), ("self none", "self some \"bad\\q\"")
            , ("selfType none", "selfType some fn -1 int")
            , ("selfType none", "selfType some named \"T\" -1")
            , ("selfType none", "selfType some forall -1 0 int")
            , ("selfType none", "selfType some var -1")
            , ("selfType none", "selfType some array int v -1")
            , ("selfType none", "selfType some u64")
            , ("fieldTypes 0", "fieldTypes 1\nfields \"T\" 1 \"x\" named \"Vec\" 1 type")
            , ("ownClone false", "ownClone 1"), ("locate false", "locate maybe")
            , ("endDecls", "unknown"), ("endDecls", "endDecls extra"), ("self none", "self none\r")
            , ("self none", ""), ("self none", "self none\ntypes 0")
            , ("self none", "self some \"" ++ replicate 1000001 'x' ++ "\"")
            ]
        ]
    , testCaseSeq "strict-source-frame"
        [ protocolRefuses (readFileRequest wire)
        | wire <-
            [ "tersus-file-parse 2\n" ++ emptyDeclRecords ++ "source 0\n"
            , "tersus-file-parse 1\r\n" ++ emptyDeclRecords ++ "source 0\n"
            , "tersus-file-parse 1\n" ++ emptyDeclRecords ++ "source -1\n"
            , "tersus-file-parse 1\n" ++ emptyDeclRecords ++ "source 2\nx"
            , "tersus-file-parse 1\n" ++ emptyDeclRecords ++ "source 0\nx"
            , "tersus-file-parse 1\n" ++ emptyDeclRecords ++ "source 1\n\xFF"
            , "tersus-file-parse 1\n" ++ emptyDeclRecords ++ "source 1\nλ"
            , "tersus-file-parse 1\n" ++ emptyDeclRecords ++ "source 0"
            ]
        ]
    , testCase "strict-import-control" $ case readParsedFile (replyWithImport "import 1 1 1 \"app\" none none") of
        Ok (pf, decls) -> testAssertEq (fileImports pf) [Import ["app"] Nothing Nothing 1 1] <> sameDecls decls emptyDecls
        Error err -> Just ("valid import control failed: " ++ err)
    , testCaseSeq "strict-imports"
        [ protocolRefuses (readParsedFile (replyWithImport imp))
        | imp <-
            [ "import 0 1 1 \"app\" none none", "import 1 -1 1 \"app\" none none"
            , "import 1 1 0 none none", "import 1 1 1 \"app\" none some 0"
            , "import 1 1 1 \"app\" some none", "import 1 1 1 \"app\" none some 2 \"A\""
            , "import 1 1 1 \"app\" none none extra", "import 1 1 1 \"app\" none none\r"
            ]
        ]
    , testCase "strict-ast-control" $ case readParsedFile (replyWithAst "tersus-ast 1 parsed\nStatementsEnd\nMark 1 1\nStatementsCons 1 0\nroot 2\n") of
        Ok (pf, _) -> testAssertEq (fileBody pf) [Mark 1 1]
        Error err -> Just ("valid AST control failed: " ++ err)
    , testCaseSeq "strict-ast"
        [ protocolRefuses (readParsedFile (replyWithAst ast))
        | ast <-
            [ "tersus-ast 1 elaborated\nStatementsEnd\nroot 0\n"
            , "tersus-ast 2 parsed\nStatementsEnd\nroot 0\n"
            , "tersus-ast 1 parsed\nStatementsEnd\nroot 0\ntrailing\n"
            , "tersus-ast 1 parsed\nStatementsEnd\nStatementsEnd\nroot 1\n"
            , "tersus-ast 1 parsed\nBlock 0\nStatementsCons 0 0\nroot 1\n"
            , "tersus-ast 1 parsed\nStatementsEnd\nMark 1 1\nStatementsCons 1 0\nBlock 2\nStatementsCons 3 2\nroot 4\n"
            , "tersus-ast 1 parsed\nStatementsEnd\nStatementsCons -1 0\nroot 1\n"
            ]
        ]
    , testCase "reply-wrong-header" (protocolRefuses (readParsedFile (replaceRecord "tersus-file 1" "tersus-file 2" (replyWithAst "tersus-ast 1 parsed\nStatementsEnd\nroot 0\n"))))
    , testCase "reply-negative-import-count" (protocolRefuses (readParsedFile (replaceRecord "imports 0" "imports -1" (replyWithAst "tersus-ast 1 parsed\nStatementsEnd\nroot 0\n"))))
    , testCase "reply-extra-ast-marker-token" (protocolRefuses (readParsedFile (replaceRecord "ast" "ast -1" (replyWithAst "tersus-ast 1 parsed\nStatementsEnd\nroot 0\n"))))
    , testCase "reply-trailing-byte" (protocolRefuses (readParsedFile (replyWithAst "tersus-ast 1 parsed\nStatementsEnd\nroot 0\n" ++ "x")))
    , testCase "reply-truncated-ast" (protocolRefuses (readParsedFile (replyWithAst "tersus-ast 1 parsed\nStatementsEnd\nroot\n")))
    , testCase "writer-rejects-negative-type-count" (protocolRefuses (writeFileRequest emptyDecls{declSelfType = Just (TVar (-1))} ""))
    , testCase "writer-rejects-empty-import-path" (protocolRefuses (writeParsedFile (ParsedFile [Import [] Nothing Nothing 1 1] []) emptyDecls))
    ]
  where
    imports =
        [ Import ["app", "geo", "shapes"] Nothing Nothing 2 3
        , Import ["pkg$geo", "λ\"\\\n"] (Just "g") Nothing 4 5
        , Import ["app", "geo"] Nothing (Just ["z", "a"]) 6 7
        , Import ["app", "geo"] (Just "alias") (Just ["Point"]) 8 9
        ]
    replyWithImport imp =
        let ast = "tersus-ast 1 parsed\nStatementsEnd\nroot 0\n"
         in "tersus-file 1\nimports 1\n" ++ imp ++ "\n" ++ emptyDeclRecords ++ "ast\n" ++ ast
    replyWithAst ast = "tersus-file 1\nimports 0\n" ++ emptyDeclRecords ++ "ast\n" ++ ast

injectedFileParser :: FileParser
injectedFileParser decls source
    | not (declLocate decls) = Left "injected parser requires source positions"
    | source == "@native-entry@" =
        if Map.member "NativePoint" (declCtors decls)
            then Right (ParsedFile [Import ["app", "geo", "NativePoint"] (Just "p") Nothing 2 3] [Mark 7 9, Return (Val (VInt 77))], decls)
            else Left "native seed missing"
    | source == "@native-type@" = Right (ParsedFile [] [Mark 11 13, StructDef "NativePoint" [] [] []], decls{declCtors = Map.insert "NativePoint" [] (declCtors decls)})
    | source == "@need-final@" =
        if Map.member "finalGate" (declCtors decls)
            then Right (ParsedFile [] [Return (Val (VInt 88))], decls)
            else Left "iterative callback state missing"
    | source == "@promote@" =
        let key = if Map.member "seedGate" (declCtors decls) then "finalGate" else "seedGate"
         in Right (ParsedFile [] [StructDef "Gate" [] [] []], decls{declCtors = Map.insert key [] (declCtors decls)})
    | otherwise = Left "injected refusal sentinel"

testLoaderInjection :: Test
testLoaderInjection = testCaseSeq "loader-injection"
    [ case loadFromEntryWith injectedFileParser (resolverFromFiles [("solo.tersus", "@need-final@")]) "solo.tersus" of
        Left err -> testAssertTrue ("iterative callback state missing" `isInfixOf` err)
        Right _ -> Just "standalone loader did not use injected parser"
    , case loadFromEntryWith (\d _ -> Right (ParsedFile [] [Return (Val (VInt 99))], d)) (resolverFromFiles [("solo.tersus", "not Haskell syntax")]) "solo.tersus" of
        Right (StandaloneResult path pf) -> testAssertEq path "solo.tersus" <> testAssertEq (fileBody pf) [Return (Val (VInt 99))]
        other -> Just ("standalone AST substitution failed: " ++ show other)
    , case loadFromEntryWith injectedFileParser (resolverFromFiles nativeFiles) "app/main.tersus" of
        Left err -> Just ("native-only files should load through callback: " ++ err)
        Right (PackageResult pkg) ->
            let files = concatMap loadedModuleFiles (packageModules pkg)
                mainFiles = [file | file <- files, loadedFileName file == "main.tersus"]
             in testAssertEq (moduleOrder pkg) ["app::geo", "app"]
                <> case mainFiles of
                    [file] -> testAssertEq (loadedFileSource file) "@native-entry@"
                        <> testAssertEq (loadedFilePath file) "app/main.tersus"
                        <> testAssertEq (fileBody (loadedParsed file)) [Mark 7 9, Return (Val (VInt 77))]
                        <> testAssertEq (map resolvedImport (loadedImports file)) [Import ["app", "geo", "NativePoint"] (Just "p") Nothing 2 3]
                        <> testAssertEq (map resolvedCanonical (loadedImports file)) ["app$geo$geo$NativePoint"]
                        <> case compileModulesToProgram pkg of
                            Error err -> Just ("substituted AST should compile without reparsing source: " ++ err)
                            Ok program -> case runProgram program of
                                Error err -> Just err
                                Ok returned -> testAssertEq (fmap renderMirValue returned) (Just "77")
                    _ -> Just "expected one substituted main file"
        Right _ -> Just "expected injected package result"
    , case loadFromEntryWith injectedFileParser (resolverFromFiles [("app/package.tersus", ""), ("app/a.tersus", "@need-final@"), ("app/z.tersus", "@promote@")]) "app/a.tersus" of
        Right (PackageResult pkg) -> testAssertEq [fileBody (loadedParsed file) | modu <- packageModules pkg, file <- loadedModuleFiles modu, loadedFileName file == "a.tersus"] [[Return (Val (VInt 88))]]
        other -> Just ("iterative passes must use callback and its final Decls: " ++ show other)
    , case loadFromEntryWith injectedFileParser (resolverFromFiles [("app/package.tersus", ""), ("app/main.tersus", "@never@")]) "app/main.tersus" of
        Left err -> testAssertTrue ("injected refusal sentinel" `isInfixOf` err)
        Right _ -> Just "diagnostic parse bypassed callback"
    ]
  where
    nativeFiles = [("app/package.tersus", ""), ("app/main.tersus", "@native-entry@"), ("app/geo/geo.tersus", "@native-type@")]

canonicalDeclsEqual :: Decls -> Decls -> TestResult
canonicalDeclsEqual actual expected = case (File.writeFileRequest actual "", File.writeFileRequest expected "") of
    (Ok actualWire, Ok expectedWire) -> testAssertEq actualWire expectedWire
    (Error err, _) -> Just ("native final declarations could not be encoded: " ++ err)
    (_, Error err) -> Just ("oracle final declarations could not be encoded: " ++ err)

nativeFileVerdict :: Bool -> Decls -> String -> Either String (ParsedFile, Decls) -> TestResult
nativeFileVerdict accepted decls source actual = case actual of
    Left err | "Parser tool failure:" `isInfixOf` err -> Just err
    _ -> case Oracle.parseFileWith decls source of
        Left err
            | accepted -> Just ("oracle rejected accepted file control: " ++ show err)
            | otherwise -> case actual of
                Left _ -> Nothing
                Right _ -> Just "native parser accepted rejected file control"
        Right (expectedFile, expectedDecls)
            | not accepted -> Just "oracle accepted rejected file control"
            | otherwise -> case actual of
                Left err -> Just ("native parser rejected accepted file control: " ++ err)
                Right (actualFile, actualDecls) -> testAssertEq actualFile expectedFile <> canonicalDeclsEqual actualDecls expectedDecls

nativeFileCase :: String -> Bool -> Decls -> String -> Test
nativeFileCase label accepted decls source = TestCase label $ do
    actual <- NativeParser.parseFileNative decls source
    pure (nativeFileVerdict accepted decls source actual)

nativeFileSequence :: String -> [(Bool, String)] -> Test
nativeFileSequence label = TestCase label . go (locating emptyDecls) (locating emptyDecls)
  where
    go _ _ [] = pure Nothing
    go nativeDecls oracleDecls ((accepted, source) : rest) = do
        actual <- NativeParser.parseFileNative nativeDecls source
        case nativeFileVerdict accepted oracleDecls source actual of
            Just err -> pure (Just err)
            Nothing -> case (actual, Oracle.parseFileWith oracleDecls source) of
                (Right (_, nativeNext), Right (_, oracleNext)) -> go nativeNext oracleNext rest
                (Left _, Left _) -> go nativeDecls oracleDecls rest
                _ -> pure (Just "file sequence lost its accepted/rejected control")

withNativeBackend :: IO TestResult -> IO TestResult
withNativeBackend action = bracket (lookupEnv "TERSUS_PARSER") restore $ \_ -> do
    setEnv "TERSUS_PARSER" "native"
    result <- action
    _ <- evaluate (forceTestResult result)
    pure result
  where
    restore Nothing = unsetEnv "TERSUS_PARSER"
    restore (Just backend) = setEnv "TERSUS_PARSER" backend

nativeSourceRecordLf :: IO TestResult
nativeSourceRecordLf = do
    ready <- NativeParser.runParserTool False ["return 1;"]
    directory <- Native.cacheDirectory
    case (ready, directory, File.writeFileRequest emptyDecls "") of
        (Left err, _, _) -> pure (Just err)
        (_, Error err, _) -> pure (Just err)
        (_, _, Error err) -> pure (Just err)
        (Right _, Ok home, Ok request) -> do
            let exe = home </> ("tersus-parser-" ++ fingerprint [emitterHash, parserSource, runtimeSource])
                unterminated = take (length request - 1) request
            (code, out, err) <- Native.runWithInputFull exe unterminated
            pure $ case File.readFileRequest unterminated of
                Ok _ -> Just "the malformed request control was unexpectedly valid"
                Error _ -> if code == ExitSuccess && out == "1\n" && not (null err)
                    then Nothing
                    else Just ("native parser did not refuse unterminated source record: " ++ show (code, take 80 out, take 80 err))

testNativeFiles :: Test
testNativeFiles = TestList "native-file-transport"
    [ TestList "metadata-and-imports"
        [ nativeFileCase label accepted decls source
        | (label, accepted, decls, source) <-
            [ ("empty", True, emptyDecls, "")
            , ("all ten seeded fields", True, protocolDecls, "")
            , ("independent optional fields and flags", True, protocolDecls{declSelf = Nothing, declLocate = False}, "")
            , ("bare import", True, locating emptyDecls, "import app::geo; return 1;")
            , ("alias", True, locating emptyDecls, "import app::geo::shapes as g; return 1;")
            , ("selected names", True, locating emptyDecls, "import app::geo { Point, area }; return 1;")
            , ("alias and selected names", True, locating emptyDecls, "import app::geo::shapes as g { Point, area }; return 1;")
            , ("line and tab columns", True, locating emptyDecls, "// λ header\n\timport app::geo as g;\n  import app::other { A, B };\nreturn 1;")
            , ("unlocated body retains import positions", True, emptyDecls, "\n  import app::geo;\nreturn 1;")
            , ("full library declarations and UTF-8 source", True, locating Compile.probeDecls, "// String in a comment is not a declaration\ns = \"λ🙂\"; return size(s.bytes);")
            , ("generic and impl scope restoration", True, locating emptyDecls, "struct Vec<T, n> { x: T, bytes: Array<Byte, n> }; impl<T, n> Vec<T, n> { fn get(self: &Self) -> &T from self [{ }] [{ }] { return &self.x; }; };")
            , ("empty selected names", False, locating emptyDecls, "import app::geo {};")
            , ("whitespace-only selected names", False, locating emptyDecls, "import app::geo { };")
            , ("trailing selected-name comma", False, locating emptyDecls, "import app::geo { Point, };")
            , ("missing alias", False, locating emptyDecls, "import app::geo as ;")
            , ("seeded Unicode nested type constructor name", True, locating (emptyDecls{declSelfType = Just (TNamed "Wrap" [ArgType (TNamed "é" [])])}), "struct Holder<T> { x: T }; h = Holder<Self> { x: 0 }; return 0;")
            , ("seeded numeric nested type constructor name", True, locating (emptyDecls{declSelfType = Just (TNamed "Wrap" [ArgType (TNamed "a١" [])])}), "struct Holder<T> { x: T }; h = Holder<Self> { x: 0 }; return 0;")
            , ("seeded underscore nested type constructor name", True, locating (emptyDecls{declSelfType = Just (TNamed "Wrap" [ArgType (TNamed "a_b" [])])}), "struct Holder<T> { x: T }; h = Holder<Self> { x: 0 }; return 0;")
            , ("seeded backtick nested type constructor name", True, locating (emptyDecls{declSelfType = Just (TNamed "Wrap" [ArgType (TNamed "`a" [])])}), "struct Holder<T> { x: T }; h = Holder<Self> { x: 0 }; return 0;")
            , ("Unicode letter alias", True, locating emptyDecls, "import app::geo as é中; return 0;")
            , ("Unicode symbol alias rejected", False, locating emptyDecls, "import app::geo as 🙂; return 0;")
            , ("Unicode letter path", True, locating emptyDecls, "import app::中文; return 0;")
            , ("Unicode symbol path rejected", False, locating emptyDecls, "import app::🙂; return 0;")
            , ("emoji source identifier rejected", False, locating emptyDecls, "🙂 = 1; return 🙂;")
            , ("comment immediately after import keyword", True, locating emptyDecls, "import// header\napp::geo; return 0;")
            , ("seeded impl clears Self and impl parameters", True, (locating emptyDecls){declSelf = Just "Seed", declSelfType = Just (TNamed "Seed" []), declImplParams = ["T"]}, "struct S {}; impl S {};")
            , ("malformed function field type rejected", False, locating emptyDecls, "struct S { f: fn Int }; return 0;")
            , ("malformed borrowed function type rejected", False, locating emptyDecls, "fn f(x: &fn Int) -> Int ~ { return 0; };")
            , ("misplaced import", False, locating emptyDecls, "return 0; import app::geo;")
            , ("malformed path", False, locating emptyDecls, "import app:::geo;")
            ]
        ]
    , TestList "per-run-declaration-shadowing"
        [ nativeFileSequence "struct field order"
            [ (True, "struct S { x: Int, y: Int };")
            , (True, "struct S { y: Int, x: Int }; s = S { x: 1, y: 2 }; return s.x;")
            ]
        , nativeFileSequence "seeded enum preserves re-registered same variants"
            [ (True, "enum E { A { n: Int }, B };")
            , (True, "enum E { A { n: Int }, B }; e = E::A { n: 1 }; return e.n;")
            ]
        , nativeFileSequence "seeded enum supports generated Clone on same variants"
            [ (True, "enum E { A { n: Int }, B };")
            , (True, "enum E { A { n: Int }, B }; impl Clone for E { }; e = E::A { n: 1 }; return 0;")
            ]
        , nativeFileSequence "enum shadows enum"
            [ (True, "enum E { A { old: Int }, B };")
            , (True, "enum E { C { fresh: Int } }; e = E::C { fresh: 2 }; return match e { E::C { fresh: n } => n, };")
            ]
        , nativeFileSequence "struct shadows enum"
            [ (True, "enum E { A { old: Int }, B };")
            , (True, "struct E { fresh: Int }; e = E { fresh: 2 }; return e.fresh;")
            ]
        , nativeFileSequence "enum shadows struct"
            [ (True, "struct E { old: Int };")
            , (True, "enum E { C { fresh: Int } }; e = E::C { fresh: 2 }; return 0;")
            ]
        , nativeFileSequence "plain struct removes generic parameters"
            [ (True, "struct Vec<T> { x: T };")
            , (True, "struct Vec { fresh: Int }; v = Vec { fresh: 3 }; return v.fresh;")
            ]
        , nativeFileSequence "enum removes generic parameters"
            [ (True, "struct Vec<T, n> { x: T, bytes: Array<Byte, n> };")
            , (True, "enum Vec { Empty, Some { fresh: Int } }; v = Vec::Some { fresh: 3 }; return 0;")
            ]
        , nativeFileSequence "generic struct shadows enum"
            [ (True, "enum Vec { Empty, Some { old: Int } };")
            , (True, "struct Vec<T> { fresh: T }; v = Vec<Int> { fresh: 3 }; return v.fresh;")
            ]
        , nativeFileSequence "own clone survives file boundary and refusal"
            [ (True, "fn clone(x: Int) -> Int [{ }] [{ }] { return x; };")
            , (False, "import app::geo { };")
            , (True, "return clone(3);")
            ]
        ]
    , TestCase "selected parseFileWith is native" $ withNativeBackend $
        pure (nativeFileVerdict True (locating emptyDecls) source (NativeParser.parseFileWith (locating emptyDecls) source))
    , TestCase "native source record requires terminal LF" nativeSourceRecordLf
    , testCase "tool failure is not a matching parser rejection" $
        testAssertEq (nativeFileVerdict False emptyDecls "import app { };" (Left "Parser tool failure: sentinel")) (Just "Parser tool failure: sentinel")
    ]
  where
    source = "\nimport app::geo as g { Point };\nstruct Local { z: Int, a: Bool }; return 1;"

{-# NOINLINE nativeLoaderParser #-}
nativeLoaderParser :: IORef [String] -> FileParser
nativeLoaderParser failures decls source = unsafePerformIO $ do
    actual <- NativeParser.parseFileNative decls source
    case actual of
        Left err | "Parser tool failure:" `isInfixOf` err -> modifyIORef' failures (err :)
        _ -> pure ()
    pure actual

loadedParity :: LoadResult -> LoadResult -> TestResult
loadedParity (StandaloneResult actualPath actualFile) (StandaloneResult expectedPath expectedFile) =
    testAssertEq actualPath expectedPath <> testAssertEq actualFile expectedFile
loadedParity (PackageResult actual) (PackageResult expected) =
    testAssertEq (packageRootDir actual, packagePackageName actual, packageEntryFile actual, packageEntryModule actual)
        (packageRootDir expected, packagePackageName expected, packageEntryFile expected, packageEntryModule expected)
        <> testAssertEq (map moduleView (packageModules actual)) (map moduleView (packageModules expected))
        <> testAssertEq (map fileView (concatMap loadedModuleFiles (packageModules actual))) (map fileView (concatMap loadedModuleFiles (packageModules expected)))
  where
    moduleView modu = (loadedModuleId modu, loadedModuleDeclNames modu, loadedDependencies modu)
    fileView file = (loadedFileModule file, loadedFileName file, loadedFileStem file, loadedFilePath file, loadedParsed file, loadedDeclNames file, loadedImports file, loadedFileSource file)
loadedParity _ _ = Just "native and oracle loaders disagreed on standalone/package discovery"

nativeLoadVerdict :: Bool -> Either String LoadResult -> Either String LoadResult -> TestResult
nativeLoadVerdict accepted actual expected = case actual of
    Left err | "Parser tool failure:" `isInfixOf` err -> Just err
    _ -> case (expected, actual) of
        (Right expectedLoad, Right actualLoad)
            | accepted -> loadedParity actualLoad expectedLoad
            | otherwise -> Just "oracle and native loaders accepted rejected control"
        (Left oracleError, Left nativeError)
            | not accepted -> Nothing
            | otherwise -> Just ("both loaders rejected accepted control; oracle: " ++ oracleError ++ "; native: " ++ nativeError)
        (Left err, Right _) -> Just ("native loader accepted what oracle rejected: " ++ err)
        (Right _, Left err) -> Just ("native loader rejected accepted control: " ++ err)

nativeLoadCase :: String -> Bool -> IO (Either String LoadResult) -> (FileParser -> IO (Either String LoadResult)) -> Maybe String -> Test
nativeLoadCase label accepted oracleAction nativeAction expectedOutput = TestCase label $ do
    failures <- newIORef []
    expected <- oracleAction
    actual <- nativeAction (nativeLoaderParser failures)
    let verdict = nativeLoadVerdict accepted actual expected <> case (actual, expectedOutput) of
            (Right (PackageResult pkg), Just output) -> case compileModulesToProgram pkg of
                Error err -> Just ("native-loaded AST did not compile directly: " ++ err)
                Ok program -> case runProgram program of
                    Error err -> Just err
                    Ok returned -> testAssertEq (fmap renderMirValue returned) (Just output)
            (_, Nothing) -> Nothing
            _ -> Just "expected native-loaded package for execution control"
    _ <- evaluate (forceTestResult verdict)
    toolFailures <- readIORef failures
    pure (case toolFailures of
        err : _ -> Just err
        [] -> verdict)

testNativeModuleLoader :: Test
testNativeModuleLoader = TestList "native-module-loader"
    [ TestList "existing module controls"
        [ nativeLoadCase label accepted (pure (loadFromEntry resolver entry)) (\parser -> pure (loadFromEntryWith parser resolver entry)) output
        | (label, accepted, files, entry, output) <-
            [ ("base package", True, basePkg, "app/main.tersus", Nothing)
            , ("collapse and symbol imports", True, collapsePkg, "app/main.tersus", Nothing)
            , ("multiple files and same-module imports", True, multiFilePkg, "app/main.tersus", Nothing)
            , ("module directory entry", True, basePkg, "app/geo/geo.tersus", Nothing)
            , ("qualified constructors", True, geoFiles "import app::geo; p = geo::Point { x: 3 }; return geo::area(p);", "app/main.tersus", Nothing)
            , ("aliases and selected imports", True, geoFiles "import app::geo as g { Point, make }; p = make(3); return g::area(p);", "app/main.tersus", Nothing)
            , ("dependency-derived String", True, stringFiles, "app/main.tersus", Just "3")
            , ("dependency Eq and Clone", True, cloneFiles, "app/main.tersus", Just "42")
            , ("missing selected symbol", False, geoFiles "import app::geo { Missing }; return 0;", "app/main.tersus", Nothing)
            , ("non-entry executable statement", False, [("app/package.tersus", ""), ("app/main.tersus", "import app::geo; return 0;"), ("app/geo/geo.tersus", "x = 1;")], "app/main.tersus", Nothing)
            , ("standalone", True, [("solo/main.tersus", "return 7;")], "solo/main.tersus", Nothing)
            , ("standalone import rejected", False, [("solo/main.tersus", "import app::geo; return 7;")], "solo/main.tersus", Nothing)
            ]
        , let resolver = resolverFromFiles files
        ]
    , TestList "actual MIR package entries"
        [ nativeLoadCase path True (loadFromFilesystem path) (\parser -> loadFromFilesystemWith parser path) Nothing
        | path <-
            [ "examples/mir/emit/emit.tersus", "examples/mir/mir_reader/mir_reader.tersus"
            , "examples/mir/mir_verify/mir_verify.tersus", "examples/mir/mir_erase/mir_erase.tersus"
            , "examples/mir/reader/reader.tersus"
            ]
        ]
    , testCase "loader tool failure is not a matching rejection" $
        testAssertEq (nativeLoadVerdict False (Left "parse error: Parser tool failure: sentinel") (Left "unknown import")) (Just "parse error: Parser tool failure: sentinel")
    ]
  where
    stringFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; s = geo::greeting(); return size(s);")
        , ("app/geo/geo.tersus", "fn greeting() -> String [{ }] [{ }] { return \"hi\".concat(\"!\"); };")
        ]
    cloneFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; p = geo::make(21); q = clone(p); if q = p { return p.x + q.x; }; return 0;")
        , ("app/geo/geo.tersus", "struct Point { x: Int }; impl Clone for Point { }; impl Eq for Point { }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; };")
        ]

testModules :: Test
testModules = TestList "testModules" [testNativeFiles, testNativeModuleLoader, testFileProtocol, testLoaderInjection, testPaths, testMatchOverReference, testCanonical, testImports, testLoaderDiscovery, testLoaderGraph, testLoaderErrors, testLoaderLevels, testLoaderFilesystem, testModuleCheckBasic, testModuleCheckTraits, testModuleCheckWithin, testModuleLinkEval, testModuleLinkPrune, testModuleLinkGenerics, testModuleLinkDrop, testModuleLinkMutual, testModuleLinkRoot, testModuleLinkExtern, testModuleLinkBorrow, testModuleQualifiedGenerics, testModuleAssumptions, testModuleCliFilesystem, testModuleLibraries]
