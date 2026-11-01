module TestModules
    ( testModules
    ) where

import Control.Exception (try, SomeException)
import Control.Monad (when)
import Data.List (isInfixOf)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, removeDirectoryRecursive)
import System.FilePath ((</>))

import Interface
import Modules
import Parse
import Pipeline (CompiledModule (..), CompiledPackage (..), compileModules, compileSource)
import TersusTypes
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
        return (case loaded of
            Left err -> Just ("filesystem load failed: " ++ err)
            Right (PackageResult pkg) -> testAssertEq (moduleOrder pkg) ["app::geo", "app"]
            Right other -> Just ("expected a package result, got: " ++ show other))
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

testModules :: Test
testModules = TestList "testModules" [testPaths, testMatchOverReference, testCanonical, testImports, testLoaderDiscovery, testLoaderGraph, testLoaderErrors, testLoaderLevels, testLoaderFilesystem, testModuleCheckBasic, testModuleCheckTraits, testModuleCheckWithin]
