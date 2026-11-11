module TestModules
    ( testModules
    , testPhase1Packages
    , testPhase2Packages
    , validatorMetadataFingerprint
    ) where

import Control.Exception (bracket, evaluate, finally, try, SomeException)
import Control.Monad (when)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf)
import qualified Data.Map.Strict as Map
import System.Directory (createDirectoryIfMissing, createDirectoryLink, doesDirectoryExist, getTemporaryDirectory, listDirectory, removeDirectoryRecursive, removeFile, withCurrentDirectory)
import System.IO (hClose, openTempFile)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import System.FilePath (takeDirectory, (</>))
import System.IO.Unsafe (unsafePerformIO)

import qualified Bootstrap
import qualified AstData
import qualified PackageCompile
import PreludeSource (parserPackageFiles, astReaderPackageFiles, toolPackageFiles, validationPackageFiles)
import qualified MirHousekeeping
import qualified Compile
import FileParserProtocol
import qualified FileParserProtocol as File
import qualified Cli
import Cli (Command (..), World (..), noWorld, runPackageFiles)
import qualified ElaborateRequest as Elaboration
import InterfaceData (readInterface, writeInterface)
import Interface
import qualified Mir as M
import MirEval (renderMirValue, runProgram, runNamedFunction, MirValue (..))
import qualified Pipeline
import qualified SourceParse
import Modules
import TestParserFragments
import ParsedFile
import qualified ParserSeed as Oracle
import qualified TersusParser as NativeParser
import qualified Native
import Seed (compilerSnapshotHash)
import LlvmRuntime (runtimeSource)
import Hash (fingerprint)
import System.Exit (ExitCode (..))
import Pipeline (CompiledModule (..), CompiledPackage (..), assumptionsOfPackage, compileModules, compileModulesToOwned, compileModulesToProgram, compileModulesValidated, compileSource)
import Syntax
import Types
import TestHarness
import Compile (elaborateStatements)
import ElaboratorTool (noVerdict, sourceElaborator)
import Utils (Result (..), bindResult)

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

-- Canonical names come from the elaborator, which resolves each package module it is sent
testCanonical :: Test
testCanonical =
    testCaseSeq
        "canonical"
        [ inspectModules [("pkg/geo/shapes.tersus", programA), ("pkg/other/shapes.tersus", programA)] $ \modules ->
            let geo = namesIn (ModuleId "pkg" (Just "geo")) modules
                other = namesIn (ModuleId "pkg" (Just "other")) modules
             in if geo /= other && not (null geo) && all ("pkg$geo$shapes$" `isInfixOf`) geo
                    then Nothing
                    else Just ("Expected distinct canonical names, got: " ++ show (geo, other))
        , inspectModules [] $ \modules -> testAssertEq (filter (`elem` ["Point", "area"]) (namesIn (ModuleId "pkg" Nothing) modules)) ["Point", "area"]
        , inspectModules [("pkg/geo/shapes.tersus", "enum Shape { Circle { r: Int } }; struct Point { x: Int };")] $ \modules ->
            testAssertEq (namesIn (ModuleId "pkg" (Just "geo")) modules) ["pkg$geo$shapes$Shape", "pkg$geo$shapes$Shape::Circle", "pkg$geo$shapes$Point"]
        , case compiledWith [("pkg/geo/shapes.tersus", "struct Point { x: Int }; struct Point { y: Int };")] of
            Error err ->
                if "already defined" `isInfixOf` err
                    then Nothing
                    else Just ("Expected duplicate error, got: " ++ err)
            Ok _ -> Just "Expected duplicate declaration in one file to fail"
        ]
  where
    programA = "struct Point { x: Int }; fn area(p: Point) -> Int [{ }] [{ }] { return p.x; };"
    -- (the entry module imports each module, and declares programA's names itself)
    compiledWith files =
        let imports = concat ["import pkg::" ++ takeWhile (/= '/') (drop 4 path) ++ "; " | (path, _) <- files]
         in case loadFromEntry (resolverFromFiles ([("pkg/package.tersus", ""), ("pkg/main.tersus", imports ++ programA ++ " return 0;")] ++ files)) "pkg/main.tersus" of
                Left err -> Error err
                Right (PackageResult pkg) -> compileModules pkg
                Right _ -> Error "fixture did not load as a package"
    inspectModules files check = case compiledWith files of
        Error err -> Just err
        Ok compiled -> check (compiledModules compiled)
    namesIn modu modules = concat [declarationNames (compiledStatements m) | m <- modules, compiledModuleId m == modu]

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
expectErr files entry needle = expectErrAll files entry [needle]

-- One evaluation, every needle asserted against that single result.
expectErrAll :: Files -> FilePath -> [String] -> TestResult
expectErrAll files entry needles = case loadPkg files entry of
    Left err -> foldr (\needle acc -> (if needle `isInfixOf` err then Nothing else Just ("Expected error containing " ++ show needle ++ ", got: " ++ err)) <> acc) Nothing needles
    Right pkg -> Just ("Expected load failure containing " ++ show needles ++ ", got: " ++ show (map (renderModuleId . loadedModuleId) (packageModules pkg)))

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
        , expectErrAll
            [("app/package.tersus", ""), ("app/main.tersus", "import app::nope; x = 1;"), ("app/geo/geo.tersus", "struct Point { x: Int };")]
            "app/main.tersus"
            ["\"nope\" is not a module of package app", "modules are: geo"]
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
        , expectErrAll
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::Point; x = 1;")
            , ("app/geo/geo.tersus", "struct Point { x: Int };")
            , ("app/geo/extra.tersus", fnDecl "area")
            ]
            "app/main.tersus"
            ["write app::geo::geo::Point instead of app::geo::Point", "has grown to 2 files"]
        , expectErr
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo::Point; x = 1;")
            , ("app/geo/shapes.tersus", "struct Point { x: Int };")
            , ("app/geo/extra.tersus", fnDecl "area")
            ]
            "app/main.tersus"
            "write app::geo::shapes::Point"
        ]

-- One on-disk geo-package fixture for both filesystem cases; each case
-- keeps its own assertions about what loading that package proves.
writeGeoPackageFs :: FilePath -> String -> String -> IO FilePath
writeGeoPackageFs pkgDir mainSource geoSource = do
    createDirectoryIfMissing True (pkgDir </> "geo")
    writeFile (pkgDir </> "package.tersus") ""
    writeFile (pkgDir </> "main.tersus") mainSource
    writeFile (pkgDir </> "geo" </> "geo.tersus") geoSource
    return (pkgDir </> "main.tersus")

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
        entry <- writeGeoPackageFs pkgDir "import app::geo; x = 1;" "struct Point { x: Int };"
        loaded <- loadFromFilesystem entry
        injected <- loadFromFilesystemWith injectedFileParser entry
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

testSnapshotToolFailure :: Test
testSnapshotToolFailure = TestCase "snapshot capture refuses a parser tool failure" $ do
    tmp <- getTemporaryDirectory
    (home, handle) <- openTempFile tmp "tersus-snapshot-tool"
    hClose handle
    removeFile home
    let seeds = ["TERSUS_PARSER_SEED_FILE", "TERSUS_SEED_FILE", "TERSUS_FRONTEND_SEED_FILE"]
        variables = "XDG_CACHE_HOME" : seeds
        badSeed = home </> "bad.ll"
    saved <- mapM lookupEnv variables
    entry <- writeGeoPackageFs (home </> "app") "import app::geo; x = 1;" "struct Point { x: Int };"
    writeFile badSeed "not a seed"
    captured <- (do
        setEnv "XDG_CACHE_HOME" (home </> "cache")
        mapM_ (`setEnv` badSeed) seeds
        captureFilesystemInput defaultLoadOptions entry Nothing)
        `finally` (sequence_ (zipWith (\name value -> maybe (unsetEnv name) (setEnv name) value) variables saved) >> removeDirectoryRecursive home)
    pure $ case captured of
        Left err | "Parser tool failure" `isInfixOf` err -> Nothing
                 | otherwise -> Just ("snapshot refused without the tool failure: " ++ err)
        Right _ -> Just "snapshot skipped the imports of a file the parser tool did not read"

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
expectCompileError files entry needle = expectCompileErrorAll files entry [needle]

expectCompileErrorAll :: Files -> FilePath -> [String] -> TestResult
expectCompileErrorAll files entry needles = case compilePkg files entry of
    Left err -> foldr (\needle acc -> (if needle `isInfixOf` err then Nothing else Just ("Expected compile error containing " ++ show needle ++ ", got: " ++ err)) <> acc) Nothing needles
    Right compiled -> Just ("Expected compile failure containing " ++ show needles ++ ", got modules: " ++ show (map (renderModuleId . compiledModuleId) (compiledModules compiled)))

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
    TestList
        "module-check-basic"
        ( [ testCase name (expectCompiles (geoFiles mainSource) "app/main.tersus")
          | (name, mainSource, _expected) <-
                [ ("module import", "import app::geo; p = geo::make(3); return geo::area(p);", "compiles")
                , ("aliased module import", "import app::geo as g; p = g::make(3); return g::area(p);", "compiles")
                , ("fully qualified names", "import app::geo; p = app::geo::geo::make(3); return app::geo::geo::area(p);", "compiles")
                , ("selected symbol imports", "import app::geo::geo::Point; import app::geo::geo::make; import app::geo::geo::area; p = make(3); return area(p);", "compiles")
                , ("selected name list", "import app::geo { Point, make, area }; p = make(3); return area(p);", "compiles")
                ]
          ]
            ++ [ testCase "file-level shapes import" $ expectCompiles
                    [ ("app/package.tersus", "")
                    , ("app/main.tersus", "import app::geo::shapes; p = shapes::make(4); return shapes::area(p);")
                    , ("app/geo/shapes.tersus", "struct Point { x: Int }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; }; fn area(p: Point) -> Int [{ }] [{ }] { return p.x; };")
                    , ("app/geo/extra.tersus", "fn extra(x: Int) -> Int [{ }] [{ }] { return x + 1; };")
                    ]
                    "app/main.tersus"
               , testCase "missing covering import" $ expectCompileError
                    [ ("app/package.tersus", "")
                    , ("app/main.tersus", "p = geo::make(3); return p.x;")
                    , ("app/other.tersus", "import app::geo; struct Local { x: Int };")
                    , ("app/geo/geo.tersus", "struct Point { x: Int }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; };")
                    ]
                    "app/main.tersus"
                    "covering import"
               , testCase "local declaration shadows selected import" $ expectCompileError
                    (geoFiles "import app::geo { Point }; struct Point { x: Int }; p = geo::make(3); return p.x;")
                    "app/main.tersus"
                    "ambiguous"
               , testCase "imported type in local struct" $ expectCompiles
                    (geoFiles "import app::geo; struct Wrapper { p: geo::Point, n: Int }; fn get(w: Wrapper) -> Int [{ }] [{ }] { return w.p.x + w.n; }; p = geo::make(3); w = Wrapper { p: p, n: 1 }; return get(w);")
                    "app/main.tersus"
               ]
        )

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
        , expectCompileErrorAll boundedFiles "app/main.tersus" ["type S", "cannot be worked out"]
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
        , case compilePkg entryBoundedFiles "app/main.tersus" of
            Left err -> Just ("entry-local bounded helper should compile: " ++ err)
            Right compiled -> case compiledNamed compiled "app" of
                Nothing -> Just "missing entry module"
                Just modu ->
                    let iface = compiledInterface modu in
                    foldr (<>) Nothing
                        [ testAssertTrue (Map.member "home" (ifTemplates iface))
                        , testAssertTrue (not (null (ifAxioms iface)))
                        , testAssertTrue ("unused" `elem` foldr (:) [] (ifExterns iface))
                        ]
        , expectCompiles
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; return geo::core::answer(7);")
            , ("app/geo/core.tersus", "trait Mark { }; impl Mark for Int { }; fn home<T: Mark>(x: T) -> T { return x; }; fn answer(x: Int) -> Int { return home(x); };")
            ]
            "app/main.tersus"
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
    entryBoundedFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::core { answer }; return answer(7);")
        , ("app/core.tersus", "trait Mark { }; impl Mark for Int { }; fn home<T: Mark>(x: T) -> T { return x; }; fn answer(x: Int) -> Int { return home(x); }; axiom origin(x) [{ }] [{ affirm x = x; }]; extern fn unused(x: Int) -> Int [{ }] [{ }];")
        ]
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
expectProgramError files entry needle = expectProgramErrorAll files entry [needle]

expectProgramErrorAll :: Files -> FilePath -> [String] -> TestResult
expectProgramErrorAll files entry needles = case programPkg files entry of
    Left err -> foldr (\needle acc -> (if needle `isInfixOf` err then Nothing else Just ("Expected program error containing " ++ show needle ++ ", got: " ++ err)) <> acc) Nothing needles
    Right program -> Just ("Expected program failure containing " ++ show needles ++ ", got functions: " ++ show (Map.keys (M.progFunctions program)))

linkGeo :: String
linkGeo = "struct Point { x: Int }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; }; fn area(p: Point) -> Int [{ }] [{ }] { return p.x; }; fn unrelated(x: Int) -> Int [{ }] [{ }] { return x * 2; };"

linkFiles :: String -> String -> Files
linkFiles mainSource geoSource =
    [ ("app/package.tersus", "")
    , ("app/main.tersus", mainSource)
    , ("app/geo/geo.tersus", geoSource)
    ]

testModuleLinkEval :: Test
testModuleLinkEval =
    TestList
        "module-link-eval"
        [ testCase name (expectRuns (linkFiles mainSource geoSource) "app/main.tersus" expected)
        | (name, mainSource, geoSource, expected) <-
            [ ("point construction and area", "import app::geo; p = geo::Point { x: 3 }; q = geo::make(4); return geo::area(p) + geo::area(q);", linkGeo, "7")
            , ("enum match", "import app::geo; s = geo::Shape::Circle { r: 5 }; y = 0; match s { geo::Shape::Circle { r: r } => { y = r; }, geo::Shape::Square { s: q } => { y = q; } }; return y;", "enum Shape { Circle { r: Int }, Square { s: Int } };", "5")
            , ("selected point import", "import app::geo::geo::Point; p = Point { x: 5 }; return p.x;", linkGeo, "5")
            ]
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
        , testAssertErrorContains "Type error: unknown trait Drop" (compileSource (suppressedPreludeDrop ++ " t = Token::new(2); return t.n;"))
        ]
  where
    dropFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; t = geo::Token::new(2); return t.n;")
        , ("app/geo/geo.tersus", "struct Token { addr: Addr<Int>, n: Int, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = n; affirm count(blk) = 0; affirm n >= 0; }]; impl Token { fn new(n: Int) -> Self [{ affirm n >= 0; }] [{ }] { (a, b) = Addr::alloc(n); return Self { addr: a, n: n, blk: b }; }; }; impl Drop for Token { fn drop(self: Self) -> Int [{ }] [{ }] { return Addr::free(self.addr, self.blk); }; };")
        ]
    -- (the geo module declares a prelude trait of its own, so the prelude
    -- is not selected for it, but its impl Drop still sees the Drop trait;
    -- a single file that does the same does not)
    dropSuppressedPreludeFiles =
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; t = geo::Token::new(2); return t.n;")
        , ("app/geo/geo.tersus", suppressedPreludeDrop)
        ]
    suppressedPreludeDrop = "trait Sequence<E> { fn size(self: &Self) -> Int; }; struct Token { addr: Addr<Int>, n: Int, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = n; affirm count(blk) = 0; affirm n >= 0; }]; impl Token { fn new(n: Int) -> Self [{ affirm n >= 0; }] [{ }] { (a, b) = Addr::alloc(n); return Self { addr: a, n: n, blk: b }; }; }; impl Drop for Token { fn drop(self: Self) -> Int [{ }] [{ }] { return Addr::free(self.addr, self.blk); }; };"

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
        , expectProgramErrorAll conflictFiles "app/main.tersus" ["extern fn cfunc", "app::geo", "app::other"]
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
        entry <- writeGeoPackageFs pkgDir "import app::geo; p = geo::Point { x: 3 }; return geo::area(p);" "struct Point { x: Int }; fn area(p: Point) -> Int [{ }] [{ }] { return p.x; };"
        loaded <- loadFromFilesystem entry
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
    TestList
        "module-libraries"
        [ testCase name (expectRuns (linkFilesWith mainSource extraFiles) "app/main.tersus" expected)
        | (name, mainSource, extraFiles, expected) <-
            [ ("string in geo", "import app::geo; return geo::greetingSize();", [("app/geo/geo.tersus", "fn greetingSize() -> Int [{ }] [{ }] { s = \"hi\".concat(\"!\"); return size(s); };")], "3")
            , ("strings in two modules", "import app::geo; import app::other; return geo::greetingSize() + other::wordSize();", [("app/geo/geo.tersus", "fn greetingSize() -> Int [{ }] [{ }] { s = \"hi\".concat(\"!\"); return size(s); };"), ("app/other/other.tersus", "fn wordSize() -> Int [{ }] [{ }] { s = \"abcd\"; return size(s); };")], "7")
            , ("hash map in geo", "import app::geo; m = geo::counts(); return m;", [("app/geo/geo.tersus", "fn counts() -> Int [{ }] [{ }] { counts = HashMap::new(); counts = counts.insert(\"the\", 40); counts = counts.insert(\"cat\", 1); counts = counts.insert(\"the\", 41); return counts.lookup(\"the\", 0) + counts.size(); };")], "43")
            , ("clone and eq in geo", "import app::geo; p = geo::make(21); return geo::twice(p);", [("app/geo/geo.tersus", "struct Point { x: Int }; impl Clone for Point { }; impl Eq for Point { }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; }; fn twice(p: Point) -> Int [{ }] [{ }] { q = clone(p); if q = p { return p.x + q.x; }; return 0; };")], "42")
            , ("eq comparison in main", "import app::geo; a = geo::make(5); b = geo::make(5); if a = b { return 1; }; return 0;", [("app/geo/geo.tersus", "struct Point { x: Int }; impl Clone for Point { }; impl Eq for Point { }; fn make(x: Int) -> Point [{ }] [{ }] { return Point { x: x }; };")], "1")
            , ("string return from geo", "import app::geo; s = geo::greeting(); return size(s);", [("app/geo/geo.tersus", "fn greeting() -> String [{ }] [{ }] { return \"hi\".concat(\"!\"); };")], "3")
            ]
        ]
  where
    linkFilesWith mainSource extraFiles = [("app/package.tersus", ""), ("app/main.tersus", mainSource)] ++ extraFiles

testModuleLinkLibCollision :: Test
testModuleLinkLibCollision =
    testCaseSeq
        "module-link-lib-collision"
        [ expectProgramErrorAll
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; struct Entry<K, V> { k: K }; e = Entry<Int, Int> { k: 3 }; return e.k + geo::counts();")
            , ("app/geo/geo.tersus", "fn counts() -> Int [{ }] [{ }] { counts = HashMap::new(); counts = counts.insert(\"the\", 40); return counts.lookup(\"the\", 0); };")
            ]
            "app/main.tersus"
            ["link error:", "Entry", "tersuslib::map", "module app", "different definitions"]
        , expectProgramError
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; fn findNth(x: Int) -> Int [{ }] [{ }] { return x + 1; }; return findNth(1) + geo::setSize();")
            , ("app/geo/geo.tersus", "fn setSize() -> Int [{ }] [{ }] { s = HashSet::new().insert(1).insert(2); return s.size(); };")
            ]
            "app/main.tersus"
            "link error: function findNth is defined by both module tersuslib::map and module app"
        , expectRuns
            [ ("app/package.tersus", "")
            , ("app/main.tersus", "import app::geo; struct Entry { x: Int }; e = Entry { x: 3 }; return e.x + geo::counts();")
            , ("app/geo/geo.tersus", "fn counts() -> Int [{ }] [{ }] { counts = HashMap::new(); counts = counts.insert(\"the\", 40); return counts.lookup(\"the\", 0); };")
            ]
            "app/main.tersus"
            "43"
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
    , testCaseSeq "metadata-request-headers"
        [ case writer "λ" of
            Error err -> Just err
            Ok wire -> testAssertEq wire (tag ++ "\n" ++ emptyDeclRecords ++ "source 2\n\xCE\xBB")
        | (writer, tag) <- [(writeImportPrefixRequest, "tersus-import-prefix 1"), (writeDeclarationNamesRequest, "tersus-declaration-names 1")]
        ]
    , testCase "metadata-import-reply" $ testAssertEq
        (readImportPrefix "tersus-imports 1\nimports 1\nimport 2 9 2 \"data\" \"codec\" some \"c\" some 1 \"Size\"\n")
        (Ok [Import ["data", "codec"] (Just "c") (Just ["Size"]) 2 9])
    , testCase "metadata-name-reply" $ testAssertEq
        (readDeclarationNames "tersus-names 1\nnames 2\nname \"E\"\nname \"E::A\"\n") (Ok ["E", "E::A"])
    , testCaseSeq "metadata-name-refusals"
        [ protocolRefuses (readDeclarationNames wire)
        | wire <-
            [ "tersus-names 2\nnames 0\n", "tersus-names 1\nnames -1\n"
            , "tersus-names 1\nnames 9223372036854775808\n", "tersus-names 1\nnames 1\n"
            , "tersus-names 1\nnames 0\nname \"extra\"\n", "tersus-names 1\nnames 1\nname bare\n"
            , "tersus-names 1\nnames 1\nname \"X\" extra\n", "tersus-names 1\nnames 1\nname \"X\""
            , "tersus-names 1\nnames 1\nname \"\xFF\"\n"
            ]
        ]
    , testCaseSeq "metadata-import-refusals"
        [ protocolRefuses (readImportPrefix wire)
        | wire <-
            [ "tersus-imports 1\nimports -1\n", "tersus-imports 1\nimports 1\n"
            , "tersus-imports 1\nimports 0\nextra\n"
            , "tersus-imports 1\nimports 1\nimport 0 1 1 \"x\" none none\n"
            , "tersus-imports 1\nimports 1\nimport 1 1 0 none none\n"
            , "tersus-imports 1\nimports 1\nimport 1 1 1 \"x\" none some 0\n"
            ]
        ]
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

nativeEntrySource :: String
nativeEntrySource = "\n  import app::geo::NativePoint as p;\n@native-entry@"

injectedFileParser :: FileParser
injectedFileParser decls source
    | not (declLocate decls) = Left "injected parser requires source positions"
    | source == nativeEntrySource =
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
    [ testAssertEq (Oracle.parseImportPrefix nativeEntrySource) (Right [Import ["app", "geo", "NativePoint"] (Just "p") Nothing 2 3])
    , case loadFromEntryWith injectedFileParser (resolverFromFiles [("solo.tersus", "@need-final@")]) "solo.tersus" of
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
                    [file] -> testAssertEq (loadedFileSource file) nativeEntrySource
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
    , case loadFromEntryWith injectedFileParser (resolverFromFiles nativeFiles){resolverOptions = defaultLoadOptions{noPrelude = True}} "app/main.tersus" of
        Right (PackageResult pkg) -> testAssertEq (map loadedNoPrelude (packageModules pkg)) [True, True]
            <> testAssertEq [fileBody (loadedParsed file) | modu <- packageModules pkg, file <- loadedModuleFiles modu, loadedFileName file == "main.tersus"] [[Mark 7 9, Return (Val (VInt 77))]]
        other -> Just ("noPrelude callback must receive explicit dependency seed and preserve substituted body: " ++ show other)
    , foldr (<>) Nothing
        [ case loadFromEntryWith (\decls source -> injectedFileParser decls (if source == "@hidden-import@" then nativeEntrySource else source))
            (resolverFromFiles [(path, if path == "app/main.tersus" then "@hidden-import@" else source) | (path,source) <- nativeFiles]){resolverOptions = defaultLoadOptions{noPrelude = enabled}}
            "app/main.tersus" of
                Left err -> testAssertTrue ("native seed missing" `isInfixOf` err)
                Right _ -> Just "callback received a constructor without a source import"
        | enabled <- [False, True]
        ]
    , case loadFromEntryWith injectedFileParser (resolverFromFiles [("app/package.tersus", ""), ("app/a.tersus", "@need-final@"), ("app/z.tersus", "@promote@")]) "app/a.tersus" of
        Right (PackageResult pkg) -> testAssertEq [fileBody (loadedParsed file) | modu <- packageModules pkg, file <- loadedModuleFiles modu, loadedFileName file == "a.tersus"] [[Return (Val (VInt 88))]]
        other -> Just ("iterative passes must use callback and its final Decls: " ++ show other)
    , case loadFromEntryWith injectedFileParser (resolverFromFiles [("app/package.tersus", ""), ("app/main.tersus", "@never@")]) "app/main.tersus" of
        Left err -> testAssertTrue ("injected refusal sentinel" `isInfixOf` err)
        Right _ -> Just "diagnostic parse bypassed callback"
    ]
  where
    nativeFiles = [("app/package.tersus", ""), ("app/main.tersus", nativeEntrySource), ("app/geo/geo.tersus", "@native-type@")]

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
            identity <- NativeParser.parserKey >>= \result -> case result of Error e -> fail e; Ok key -> pure key
            let exe = home </> ("tersus-parser-" ++ identity)
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
        ([ nativeFileCase label accepted decls source
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
        ] ++ [TestCase "full library declarations and UTF-8 source" $ case Compile.probeDecls of
            Left e -> pure (Just e)
            Right declared -> do
                let source = "// String in a comment is not a declaration\ns = \"λ🙂\"; return size(s.bytes);"
                actual <- NativeParser.parseFileNative (locating declared) source
                pure (nativeFileVerdict True (locating declared) source actual)])
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
    [ TestList "cross-package codec prerequisites"
        [ nativeLoadCase label accepted (pure (loadFromEntry resolver "pkgs/app/main.tersus")) (\parser -> pure (loadFromEntryWith parser resolver "pkgs/app/main.tersus")) Nothing
        | (label, accepted, source) <- crossPackageSyntax
        , let resolver = resolverFromFiles (crossPackageFiles source)
        ]
    , TestList "existing module controls"
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
            [ "lib/mir/emit/emit.tersus", "lib/mir/mir_reader/mir_reader.tersus"
            , "lib/mir/mir_verify/mir_verify.tersus", "lib/mir/mir_erase/mir_erase.tersus"
            , "lib/mir/reader/reader.tersus"
            ]
        ]
    , TestList "compiler tool packages beside the validator and the libraries"
        [ TestCase path (toolPackageIsolation path)
        | path <- ["lib/mir/emit/emit.tersus", "lib/mir/mir_reader/mir_reader.tersus", "lib/mir/mir_verify/mir_verify.tersus", "lib/mir/mir_erase/mir_erase.tersus", "lib/parser/parser.tersus", "lib/ast_reader/ast_reader.tersus"]
        ]
    , TestList "AST tool package snapshots"
        [ nativeLoadCase path True (pure (loadFromEntry resolver path)) (\parser -> pure (loadFromEntryWith parser resolver path)) Nothing
        | (path, files) <- [("lib/ast_reader/ast_reader.tersus", astReaderPackageFiles), ("lib/parser/parser.tersus", parserPackageFiles)]
        , let resolver = resolverFromFiles files
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

-- A compiler tool under lib/ loads its own package and the data package only: with the validator package and the top-level
-- library files beside it, it loads exactly what its embedded snapshot alone gives
toolPackageIsolation :: FilePath -> IO TestResult
toolPackageIsolation entry = do
    names <- listDirectory "lib"
    libFiles <- mapM (\name -> (,) ("lib/" ++ name) <$> readFile ("lib/" ++ name)) [name | name <- names, ".tersus" `isSuffixOf` name]
    onDisk <- findPackageRootIO entry
    let besideFiles = resolverFromFiles (toolPackageFiles ++ validationPackageFiles ++ libFiles)
        alone = loadFromEntry (resolverFromFiles toolPackageFiles) entry
        beside = loadFromEntry besideFiles entry
        pkg = takeWhile (/= '/') (drop 4 entry)
        root = "lib/" ++ pkg ++ "/"
    pure $ case (alone, beside) of
        (Right (PackageResult a), Right (PackageResult b)) -> mconcat
            [ testAssertEq (show b) (show a)
            , testAssertEq (packageRootDir b, onDisk) ("lib/" ++ pkg, Just ("lib/" ++ pkg))
            , case discoverEntry besideFiles entry of
                InPackage r name -> testAssertEq (r, name) ("lib/" ++ pkg, pkg)
                _ -> Just (entry ++ " is not found in its own package")
            , testAssertEq [path | modu <- packageModules b, file <- loadedModuleFiles modu, let path = loadedFilePath file, not (root `isPrefixOf` path || "lib/data/" `isPrefixOf` path)] []
            ]
        (Left e, _) -> Just e
        (_, Left e) -> Just e
        _ -> Just (entry ++ " is not a package")

crossPackageFiles :: String -> Files
crossPackageFiles source =
    [ ("pkgs/app/package.tersus", ""), ("pkgs/app/main.tersus", source)
    , ("pkgs/left/package.tersus", ""), ("pkgs/left/a/a.tersus", "enum E { A, B };")
    , ("pkgs/left/generic/generic.tersus", "struct Packet<T> { value: T }; struct Empty { };")
    , ("pkgs/left/model.tersus", "struct Twin { value: Int };")
    , ("pkgs/right/package.tersus", ""), ("pkgs/right/right.tersus", "enum E { A, B, C };")
    , ("pkgs/right/model.tersus", "struct Twin { value: Int };")
    , ("pkgs/unrelated/package.tersus", ""), ("pkgs/unrelated/a/a.tersus", "enum E { A { incompatible: Bool } };")
    ]

crossPackageSyntax :: [(String, Bool, String)]
crossPackageSyntax =
    [ ("qualified generic struct", True, "import left::generic as l; p = l::Packet<Int> { value: 12 }; return p.value;")
    , ("qualified empty struct", True, "import left::generic as l; p = l::Empty { }; return 1;")
    , ("unknown qualified single struct arm", False, "import left::generic { Empty }; p = Empty { }; return match p { bogus::Empty { } => 1, };")
    , ("qualified struct still requires braces", False, "import left::generic as l; p = l::Empty; return 1;")
    , ("imported enum Clone generation uses source names", True, "import left::a as p; trait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; }; impl Clone for p::E { }; return 0;")
    , ("selected enum keeps its owner", True, "import left::a { E }; import right; s = E::B; return match s { E::A => 1, E::B => 2, };")
    , ("foreign fieldless final arm", False, "import left::a { E }; import right as q; s = E::B; return match s { E::A => 1, q::right::E::B => 2, };")
    , ("unknown qualified final arm", False, "import left::a { E }; s = E::B; return match s { E::A => 1, bogus::E::B => 2, };")
    , ("alias duplicate variant", False, "import left::a as l { E }; s = E::A; return match s { E::A => 1, l::E::A => 2, E::B => 3, };")
    , ("unimported qualified literal", False, "s = left::a::E::A; return 0;")
    , ("unimported qualified type", True, "fn f(s: left::a::E) -> Int { return 0; }; return 0;")
    ]

testCrossPackageBoundaries :: Test
testCrossPackageBoundaries = TestList "cross-package-boundaries"
    ([testCase label (case loadPkg (crossPackageFiles source) "pkgs/app/main.tersus" of
        Left err -> if accepted then Just err else Nothing
        Right _ -> if accepted then Nothing else Just "invalid imported constructor accepted")
      | (label, accepted, source) <- crossPackageSyntax]
    ++ [ testCase "owning package preserves nominal identity" $ case loadPkg (crossPackageFiles "import left as l; import right as r; fn bad(x: l::model::Twin) -> r::model::Twin { return x; }; return 0;") "pkgs/app/main.tersus" of
            Left err -> Just err
            Right pkg -> testAssertErrorContains "right$model$Twin" (compileModulesValidated pkg)
       , testCase "unimported type cannot compile" $ case loadPkg (crossPackageFiles "fn f(s: left::a::E) -> Int { return 0; }; return 0;") "pkgs/app/main.tersus" of
            Left _ -> Nothing
            Right pkg -> testAssertErrorContains "unknown type" (compileModulesValidated pkg)
       , testCase "unused dependency root cannot introduce a cycle" $ case loadPkg
            [ ("pkgs/app/package.tersus", ""), ("pkgs/app/main.tersus", "import dep::core { Point }; p = Point { x: 1 }; return p.x;")
            , ("pkgs/dep/package.tersus", ""), ("pkgs/dep/dep.tersus", "import dep::unused;")
            , ("pkgs/dep/unused/unused.tersus", "import dep;")
            , ("pkgs/dep/core/core.tersus", "struct Point { x: Int };")
            ] "pkgs/app/main.tersus" of
                Left err -> Just err
                Right pkg -> testAssertEq (moduleOrder pkg) ["dep::core", "app"]
       , testCase "unused root bodies do not need foreign constructors" $ case loadPkg
            [ ("pkgs/app/package.tersus", ""), ("pkgs/app/main.tersus", "import dep::core { Point }; p = Point { x: 1 }; return p.x;")
            , ("pkgs/dep/package.tersus", ""), ("pkgs/dep/dep.tersus", "import common::e as c; fn unused() -> Int ~ { x = c::E::A; return 0; };")
            , ("pkgs/dep/core/core.tersus", "struct Point { x: Int };")
            , ("pkgs/common/package.tersus", ""), ("pkgs/common/e/e.tersus", "enum E { A };")
            ] "pkgs/app/main.tersus" of
                Left err -> Just err
                Right pkg -> testAssertEq (moduleOrder pkg) ["dep::core", "app"]
       , testCase "declaration scan ignores comments and quoted bodies" $ case Oracle.parseDeclarationNames "// fn hidden() {};\nfn core() -> Int { s = \"{ fn fake; }\"; return 0; }; enum E { A { x: Int }, B }; struct S { x: Int };" of
            Left err -> Just (show err)
            Right names -> testAssertEq names ["core", "E", "E::A", "E::B", "S"]
       , testCase "callback deletion of an overlapped seed is retained" $ case loadFromEntryWith deleteCallback (resolverFromFiles
            [ ("pkgs/app/package.tersus", ""), ("pkgs/app/a.tersus", "@deleted@"), ("pkgs/app/gate.tersus", "@gate@"), ("pkgs/app/z.tersus", "import dep { Gate };\n@delete@")
            , ("pkgs/dep/package.tersus", ""), ("pkgs/dep/dep.tersus", "@incoming@")
            ]) "pkgs/app/a.tersus" of
                Left err -> Just err
                Right (PackageResult _) -> Nothing
                Right _ -> Just "expected callback package"
       , testCase "callback delta survives without imported seed leakage" $ case loadFromEntryWith callback (resolverFromFiles
            [ ("pkgs/app/package.tersus", ""), ("pkgs/app/a.tersus", "@need-final@"), ("pkgs/app/z.tersus", "import dep;\n@promote@")
            , ("pkgs/dep/package.tersus", ""), ("pkgs/dep/dep.tersus", "@seed@")
            ]) "pkgs/app/a.tersus" of
                Left err -> Just err
                Right (PackageResult pkg) -> testAssertTrue (any (elem (Return (Val (VInt 88))) . fileBody . loadedParsed) [file | modu <- packageModules pkg, file <- loadedModuleFiles modu, loadedFileName file == "a.tersus"])
                Right _ -> Just "expected callback package"
       ])
  where
    deleteCallback decls source
        | source == "@incoming@" = Right (ParsedFile [] [StructDef "Gate" [] [("new", TBool)] []], decls{declCtors = Map.insert "Gate" ["new"] (declCtors decls)})
        | source == "@gate@" = Right (ParsedFile [] [StructDef "Gate" [] [("old", TInt)] []], decls{declCtors = Map.insert "Gate" ["old"] (declCtors decls)})
        | source == "import dep { Gate };\n@delete@" = Right (ParsedFile [Import ["dep"] Nothing (Just ["Gate"]) 1 1] [], decls{declCtors = Map.insert "deleted" [] (Map.delete "Gate" (declCtors decls))})
        | source == "@deleted@", Map.member "deleted" (declCtors decls), Map.notMember "Gate" (declCtors decls) = Right (ParsedFile [] [Return (Val (VInt 88))], decls)
        | otherwise = Left "callback deletion was not preserved"
    callback decls source
        | source == "@seed@" = Right (ParsedFile [] [StructDef "Seed" [] [] []], decls)
        | source == "import dep;\n@promote@" = do
            (parsedFile, returned) <- injectedFileParser decls "@promote@"
            Right (parsedFile{fileImports = [Import ["dep"] Nothing Nothing 1 1]}, returned)
        | source == "@need-final@", any (`Map.member` declCtors decls) ["dep::Seed", "dep::dep::Seed"] = Left "imported seed leaked between files"
        | otherwise = injectedFileParser decls source

testCrossPackageConstructors :: Test
testCrossPackageConstructors = testCaseSeq "cross-package-constructor-seeds"
    [ accepts "import provider::shapes as p; s = p::Shape::A { value: 7 }; return match s { p::Shape::A { value: v } => v, p::Shape::B => 0, };" 7
    , accepts "import provider::shapes::shapes { Shape }; s = Shape::A { value: 8 }; return match s { Shape::A { value: v } => v, Shape::B => 0, };" 8
    , accepts "import provider::shapes::Shape; s = Shape::A { value: 9 }; return match s { Shape::A { value: v } => v, Shape::B => 0, };" 9
    , accepts "import provider::shapes as p; enum Shape { Local }; s = p::Shape::A { value: 10 }; return match s { p::Shape::A { value: v } => v, p::Shape::B => 0, };" 10
    , accepts "import provider::shapes as p; import other as q; a = p::Shape::A { value: 11 }; b = q::other::Shape::Other { flag: true }; return match a { p::Shape::A { value: v } => v, p::Shape::B => 0, };" 11
    , refuses "s = provider::shapes::Shape::A { value: 7 }; return 0;"
    , refuses "fn f(s: provider::shapes::Shape) -> Int { return 0; }; return 0;"
    , refuses "import provider::shapes as p; fn f(s: other::shapes::Shape) -> Int { return 0; }; return 0;"
    , refuses "import provider::shapes as p; s = other::shapes::Shape::Other { flag: true }; return 0;"
    ]
  where
    files source =
        [ ("pkgs/app/package.tersus", ""), ("pkgs/app/main.tersus", source)
        , ("pkgs/provider/package.tersus", ""), ("pkgs/provider/shapes/shapes.tersus", "enum Shape { A { value: Int }, B };")
        , ("pkgs/other/package.tersus", ""), ("pkgs/other/other.tersus", "enum Shape { Other { flag: Bool } };")
        ]
    checked source = case loadPkg (files source) "pkgs/app/main.tersus" of
        Left err -> Error err
        Right pkg -> compileModulesValidated pkg
    accepts source expected = case checked source of
        Error err -> Just err
        Ok program -> case runProgram program of
            Error err -> Just err
            Ok result -> testAssertEq (fmap renderMirValue result) (Just (show expected))
    refuses source = case checked source of
        Error e | noVerdict e -> Just e
        Error _ -> Nothing
        Ok _ -> Just "unimported qualified constructor/type became visible"

testModuleLateDeclarations :: Test
testModuleLateDeclarations = testCaseSeq "late top-level definitions consume expression types once"
    ([ case loadPkg (files entry helper) ("app/" ++ entry ++ ".tersus") of
        Left e -> Just e
        Right pkg -> case PackageCompile.compileModulesLinked pkg of
            Error e -> Just e
            Ok program -> foldr (<>) Nothing
                [ testAssertEq (runProgram program) (Ok (Just (MInt 42)))
                , testAssertTrue (Map.member "uncalled" (M.progFunctions program))
                , testAssertTrue (not (any (isInfixOf "hiddenAfterReturn") (Map.keys (M.progFunctions program))))
                , testAssertTrue (not (any ((== Just "dead") . M.localName) (Map.elems (M.fnLocals (M.progMain program)))))
                , testAssertEq [name | M.Ghost _ (M.GhostFunction name "uncalled" True) <- concatMap M.blockStatements (Map.elems (M.fnBlocks (M.progMain program)))] ["uncalled"]
                ]
     | (entry,helper) <- [("a","z"),("z","a")]
     ] ++
     [ case loadPkg [("app/package.tersus", ""), ("app/main.tersus", "return sameName(7); fn sameName(sameName: Int) -> Int { return sameName; };")] "app/main.tersus" of
        Left e -> Just e
        Right pkg -> case PackageCompile.compileModulesLinked pkg of
            Error e -> Just e
            Ok p -> case Map.lookup "sameName" (M.progFunctions p) of
                Nothing -> Just "missing sameName"
                Just fn -> testAssertEq (Map.lookup "sameName" (M.specEnv (M.fnSpec fn))) (Just (M.Copy (M.Local 1)))
     , case loadPkg [("app/package.tersus", ""), ("app/main.tersus", "fn globalKey() -> Int { return 0; }; fn localLoop(globalKey: Int) -> Int { while globalKey > 0 [{ affirm globalKey >= 0; }] shrinks globalKey { globalKey = globalKey - 1; }; return globalKey; }; return 0;")] "app/main.tersus" of
        Left e -> Just e
        Right pkg -> case PackageCompile.compileModulesLinked pkg of
            Error e -> Just e
            Ok p -> case Map.lookup "localLoop" (M.progFunctions p) of
                Nothing -> Just "missing localLoop"
                Just fn -> testAssertTrue (not (Map.null (M.specLoops (M.fnSpec fn))) &&
                    all ((== Just (M.Copy (M.Local 1))) . Map.lookup "globalKey" . M.loopEnv) (Map.elems (M.specLoops (M.fnSpec fn))))
     , case loadPkg
        [("app/package.tersus", ""), ("app/a.tersus", "import app::z { bad }; return 0;"),
         ("app/z.tersus", "fn bad(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { return n; };")]
        "app/a.tersus" of
        Left e -> Just e
        Right pkg -> testAssertErrorContains "Could not prove" (compileModulesValidated pkg)
     , case Compile.lowerSource True "return answer(); dead = 1 + 2; { fn hiddenAfterReturn() -> Int { return 91; }; }; fn answer() -> Int { return 42; }; fn uncalled() -> Int { return 99; };" of
        Error e -> Just e
        Ok p -> testAssertEq (runProgram p) (Ok (Just (MInt 42)))
     ])
  where
    files entry helper =
        [ ("app/package.tersus", "")
        , ("app/" ++ entry ++ ".tersus", "import app::" ++ helper ++ " { answer }; return answer(); dead = 1 + 2; { fn hiddenAfterReturn() -> Int { return 91; }; };")
        , ("app/" ++ helper ++ ".tersus", "fn answer() -> Int { return 42; }; fn uncalled() -> Int { return 99; };")
        ]

testValidatorPackage :: Test
testValidatorPackage = TestCase "validator package keeps bare helpers and reference calls never run driver main" $ do
    disk <- mapM (\(path, _) -> do source <- readFile path; pure (path, source)) validationPackageFiles
    reference <- bootstrapFromFile MirHousekeeping.validationEntry
    replay <- bootstrapFromFile MirHousekeeping.validationEntry
    let changed = [(path, if path == MirHousekeeping.validationEntry
            then unlines (concatMap (\line -> ["affirm false;" | line == "bytes = driverReadAll();"] ++ [line]) (lines source))
            else source) | (path,source) <- validationPackageFiles]
    refused <- programFromFiles MirHousekeeping.validationEntry changed
    pure $ case loadPkg validationPackageFiles MirHousekeeping.validationEntry of
        Left e -> Just e
        Right pkg -> case PackageCompile.compileModules pkg of
            Error e -> Just e
            Ok compiled -> case PackageCompile.lowerCompiledPackage pkg compiled of
                Error e -> Just e
                Ok raw -> case MirHousekeeping.eraseGhosts raw of
                    Error e -> Just e
                    Ok checker ->
                        let files = concatMap loadedModuleFiles (packageModules pkg)
                            declared = [name | modu <- PackageCompile.compiledModules compiled, Assign name (Val VFunct{}) <- PackageCompile.compiledStatements modu]
                            typeNames = [name | modu <- PackageCompile.compiledModules compiled, stmt <- PackageCompile.compiledStatements modu, name <- case stmt of StructDef n _ _ _ -> [n]; EnumDef n _ -> [n]; _ -> []]
                            markers = [(name, source, top) | block <- Map.elems (M.fnBlocks (M.progMain raw)), M.Ghost _ (M.GhostFunction name source top) <- M.blockStatements block]
                            trapped = checker{M.progMain = (M.progMain checker){M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [] M.Unreachable)}}
                         in foldr (<>) Nothing
                            [ case reference of
                                Error e -> Just e
                                Ok cached -> testAssertEq (Map.keys (M.progFunctions cached)) (Map.keys (M.progFunctions raw))
                            , case replay of
                                Error e -> Just e
                                Ok cached -> testAssertEq (Map.keys (M.progFunctions cached)) (Map.keys (M.progFunctions raw))
                            , case refused of Error _ -> Nothing; Ok _ -> Just "changed same-path validator bypassed validation"
                            , testAssertEq (length markers) (Map.size (Map.fromList [(marker, ()) | marker <- markers]))
                            , testAssertEq (validatorMetadataFingerprint raw) "7d1bad137ad13ae1"
                            , testAssertEq (validatorMetadataFingerprint (Compile.completeSpecEnvs raw)) (validatorMetadataFingerprint raw)
                            , testAssertTrue (all ((/= validatorMetadataFingerprint raw) . validatorMetadataFingerprint) (metadataMutations raw))
                            , testAssertTrue (all (\name -> case Map.lookup name (M.progFunctions raw) of
                                Nothing -> False
                                Just fn -> let env = M.specEnv (M.fnSpec fn) in
                                    all (`Map.member` env) (Map.keys (M.progFunctions raw)) && not (Map.member "countParsed" env))
                                ["containsValue", "commonContext", "driverReadAll"])
                            , testAssertEq (Map.size (M.progFunctions raw)) 860
                            , testAssertEq (Map.keys (M.progFunctions checker)) (Map.keys (M.progFunctions raw))
                            , testAssertTrue (all (`Map.member` M.progFunctions raw) declared)
                            , testAssertTrue (all (`Map.member` M.progFunctions checker) declared)
                            , testAssertTrue (all (\n -> Map.member n (M.progTypes raw) || Map.member n (M.progGenerics raw)) typeNames)
                            , testAssertEq disk validationPackageFiles
                            , testAssertEq (map loadedFileStem files) ["context", "differences", "driver", "evaluation", "execution", "flow", "joins", "linear", "loopInference", "model", "relations", "saturation", "sequenceFacts", "state", "validation"]
                            , testAssertEq (length (packageModules pkg)) 1
                            , testAssertTrue (all ((== packageEntryModule pkg) . loadedFileModule) files)
                            , testAssertTrue (all (\file -> all ((== packageEntryModule pkg) . resolvedTargetModule) (loadedImports file)) files)
                            , testAssertEq [loadedFileStem file | file <- files, "JoinedFact" `elem` loadedDeclNames file] ["joins"]
                            , testAssertEq [loadedFileStem file | file <- files, "commonFacts" `elem` loadedDeclNames file] ["joins"]
                            , testAssertEq [loadedFileStem file | file <- files, "commonContext" `elem` loadedDeclNames file] ["joins"]
                            , testAssertEq (sum [definitions stmt | file <- files, stmt <- fileBody (loadedParsed file)]) 461
                            , testAssertTrue (all (`Map.member` M.progFunctions checker) ["validateExecution", "noTemplates", "commonContext", "driverReadAll"])
                            , testAssertTrue (all (not . isInfixOf "validation$") (Map.keys (M.progFunctions checker)))
                            , testAssertEq (runNamedFunction trapped "noTemplates" []) (Ok (Just (MList [])))
                            , case runProgram trapped of Error _ -> Nothing; Ok _ -> Just "driver-main trap did not fail"
                            ]
  where
    definitions (Assign _ (Val VFunct{})) = 1 :: Int
    definitions (BoundedDef _ statement) = definitions statement
    definitions _ = 0

validatorMetadataFingerprint :: M.Program -> String
validatorMetadataFingerprint program = fingerprint
    [ show (M.progTypes program, M.progGenerics program, M.progInvariants program)
    , show (metadata (M.progMain program))
    , show [(name, metadata fn) | (name,fn) <- Map.toAscList (M.progFunctions program)]
    ]
  where
    metadata fn = (M.fnName fn, M.fnParams fn, M.fnReturns fn, M.fnLocals fn,
        M.fnSizeParams fn, M.fnTypeParams fn, M.fnBorrowed fn, M.fnMutBorrowed fn, M.fnFrom fn, M.fnSpec fn,
        [(block, [ghost | ghost@M.Ghost{} <- M.blockStatements body]) | (block,body) <- Map.toAscList (M.fnBlocks fn)])

metadataMutations :: M.Program -> [M.Program]
metadataMutations program =
    [ program{M.progMain = main{M.fnLocals = Map.adjust (\d -> d{M.localType = TBool}) (M.Local 0) (M.fnLocals main)}}
    , program{M.progMain = main{M.fnBlocks = Map.adjust (\(M.BasicBlock ss t) -> M.BasicBlock (M.Ghost Map.empty (M.GhostValidation (ProofAssert (ATerm "metadata-probe"))) : ss) t) (M.BlockId 0) (M.fnBlocks main)}}
    , program{M.progInvariants = Map.insert "metadata-probe" [ProofAssert (ATerm "metadata-probe")] (M.progInvariants program)}
    , program{M.progFunctions = Map.adjust changeLoop loopFunction (M.progFunctions program)}
    ]
  where
    main = M.progMain program
    loopFunction = head [name | (name,fn) <- Map.toAscList (M.progFunctions program), not (Map.null (M.specLoops (M.fnSpec fn)))]
    changeLoop fn = fn{M.fnSpec = spec{M.specLoops = Map.adjust (\loop -> loop{M.loopEnv = Map.insert "metadata-probe" (M.Const (M.CInt 0)) (M.loopEnv loop)}) (fst (Map.findMin (M.specLoops spec))) (M.specLoops spec)}}
      where spec = M.fnSpec fn

phase1Entry :: FilePath
phase1Entry = "unrelated/app/main.tersus"

phase1Root :: FilePath
phase1Root = "installed/vendor-v1"

phase1Options :: LoadOptions
phase1Options = defaultLoadOptions{packageRoots = Map.singleton "vendor" phase1Root, noPrelude = True}

phase1Files :: String -> Files
phase1Files source =
    [ ("unrelated/app/package.tersus", "")
    , (phase1Entry, source)
    , (phase1Root ++ "/package.tersus", "noPrelude = true;")
    , (phase1Root ++ "/model/model.tersus", "enum Choice { Value { n: Int }, Empty }; fn read(c: Choice) -> Int { return match c { Choice::Value { n: n } => n, Choice::Empty => 0, }; };")
    ]

phase1Program :: String
phase1Program = "import vendor::model { Choice, read }; c = Choice::Value { n: 42 }; return read(c);"

phase1Load :: LoadOptions -> Files -> Either String LoadedPackage
phase1Load options files = case Pipeline.loadFromEntry (resolverFromFiles files){resolverOptions = options} phase1Entry of
    Right (PackageResult pkg) -> Right pkg
    Left err -> Left err
    Right _ -> Left "expected package"

phase1Refusal :: String -> Either String a -> TestResult
phase1Refusal expected result = case result of
    Left err | expected `isInfixOf` err && not (Oracle.toolFailure err) -> Nothing
             | otherwise -> Just ("wrong refusal: " ++ err)
    Right _ -> Just ("expected refusal: " ++ expected)

phase1ResultRefusal :: String -> Utils.Result a String -> TestResult
phase1ResultRefusal expected result = case result of
    Error err | expected `isInfixOf` err -> Nothing
              | otherwise -> Just ("wrong refusal: " ++ err)
    Ok _ -> Just ("expected refusal: " ++ expected)

phase1Filesystem :: IO TestResult
phase1Filesystem = bracket create removeDirectoryRecursive $ \root -> do
    let file = root </> phase1Entry
        options = phase1Options{packageRoots = Map.singleton "vendor" (root </> phase1Root)}
    mapM_ (\(path, text) -> createDirectoryIfMissing True (root </> takeDirectory path) >> writeFile (root </> path) text) (phase1Files phase1Program)
    loaded <- Pipeline.loadFromFilesystemWithOptions options file
    stdinSource <- Pipeline.loadFromSource options phase1Program
    let evaluated result = case result of
            Left err -> Error err
            Right (PackageResult pkg) -> runPackageFiles noWorld Interpret pkg
            Right _ -> Error "configured source did not use the normal package loader"
    pure (testAssertEq (evaluated loaded) (Ok ((("42", "")), []))
        <> testAssertEq (evaluated stdinSource) (evaluated loaded))
  where
    create = do
        tmp <- getTemporaryDirectory
        (path, handle) <- openTempFile tmp "tersus-phase1-files"
        hClose handle
        removeFile path
        createDirectoryIfMissing True path
        pure path

withPhase1Directory :: (FilePath -> IO a) -> IO a
withPhase1Directory = bracket create removeDirectoryRecursive
  where
    create = do
        tmp <- getTemporaryDirectory
        (path, handle) <- openTempFile tmp "tersus-phase1-files"
        hClose handle
        removeFile path
        createDirectoryIfMissing True path
        pure path

phase1StandaloneRoots :: Test
phase1StandaloneRoots = TestCase "standalone and stdin units resolve only configured roots, never cwd or sibling packages" $ withPhase1Directory $ \root -> do
    let proj = root </> "proj"
        entry = proj </> "main.tersus"
        vendor = root </> "vendor"
        files source =
            [ (entry, source)
            , (vendor </> "package.tersus", "noPrelude = true;")
            , (vendor </> "api/api.tersus", "import foo::api; fn answer() -> Int { return 42; };")
            , (root </> "foo/package.tersus", "noPrelude = true;")
            , (root </> "foo/api/api.tersus", "fn answer() -> Int { return 99; };")
            , (root </> "main/package.tersus", "noPrelude = true;")
            , (root </> "main/main.tersus", "fn answer() -> Int { return 99; };")
            , (proj </> "unused.tersus", "not a valid program")
            ]
        options = defaultLoadOptions{packageRoots = Map.singleton "vendor" vendor, noPrelude = True}
        writeFiles source = mapM_ (\(path,text) -> createDirectoryIfMissing True (takeDirectory path) >> writeFile path text) (files source)
        value loaded = case loaded of
            Left err -> Error err
            Right (PackageResult pkg) -> compileModulesToProgram pkg `bindResult` runProgram
            Right _ -> Error "expected configured standalone package"
        unconfigured source = do
            writeFiles source
            disk <- Pipeline.loadFromFilesystemWithOptions options entry
            stdinResult <- withCurrentDirectory proj (Pipeline.loadFromSource options source)
            let memory = Pipeline.loadFromEntry (resolverFromFiles (files source)){resolverOptions = options} entry
            pure (phase1Refusal "not configured for standalone source" disk
                <> phase1Refusal "not configured for standalone source" stdinResult
                <> phase1Refusal "not configured for standalone source" memory)
    refusals <- mapM unconfigured ["import foo::api; return 0;", "import main; return 0;", "import vendor::api; import foo::api; return 0;"]
    let good = "import vendor::api { answer }; return answer();"
    writeFiles good
    disk <- Pipeline.loadFromFilesystemWithOptions options entry
    stdinResult <- withCurrentDirectory proj (Pipeline.loadFromSource options good)
    let memory = Pipeline.loadFromEntry (resolverFromFiles (files good)){resolverOptions = options} entry
    let cwdRoot = root </> "X"
    createDirectoryIfMissing True cwdRoot
    writeFile (cwdRoot </> "package.tersus") "noPrelude = true;"
    writeFile (cwdRoot </> "provider.tersus") "fn answer() -> Int { return 42; };"
    cwdPackage <- withCurrentDirectory cwdRoot (Pipeline.loadFromSource options{packageRoots = Map.singleton "X" cwdRoot} "import X::provider { answer }; return answer();")
    pure (foldr (<>) Nothing refusals
        <> testAssertEq (value disk) (Ok (Just (MInt 42)))
        <> testAssertEq (value stdinResult) (Ok (Just (MInt 42)))
        <> testAssertEq (value memory) (Ok (Just (MInt 42)))
        <> testAssertEq (value cwdPackage) (Ok (Just (MInt 42)))
        <> case disk of Right (PackageResult pkg) -> testAssertTrue (proj </> "unused.tersus" `notElem` map fst (packageSources pkg)); _ -> Just "standalone load failed")

phase1CurrentImporterRoots :: Test
phase1CurrentImporterRoots = TestCase "real packages discover roots from the current importer, not previously loaded dependencies" $ withPhase1Directory $ \root -> do
    let app = root </> "client/app"
        vendor = root </> "installed/vendor"
        util = root </> "installed/util"
        entry = app </> "main.tersus"
        common =
            [ (app </> "package.tersus", "")
            , (vendor </> "package.tersus", "noPrelude = true;")
            , (vendor </> "api/api.tersus", "import util::api as u; fn answer() -> Int { return u::value(); };")
            , (util </> "package.tersus", "noPrelude = true;")
            , (util </> "api/api.tersus", "fn value() -> Int { return 42; };")
            ]
        options = defaultLoadOptions{packageRoots = Map.singleton "vendor" vendor}
        orders = ["import vendor::api; import util::api as u; return u::value();", "import util::api as u; import vendor::api; return u::value();"]
        write files = mapM_ (\(path, text) -> createDirectoryIfMissing True (takeDirectory path) >> writeFile path text) files
        memory config files = Pipeline.loadFromEntry (resolverFromFiles files){resolverOptions = config} entry
        output loaded = case loaded of
            Left err -> Error err
            Right (PackageResult pkg) -> compileModulesToProgram pkg `bindResult` runProgram
            Right _ -> Error "expected package"
    refused <- mapM (\source -> do
        let files = (entry, source) : common
        write files
        disk <- Pipeline.loadFromFilesystemWithOptions options entry
        pure (phase1Refusal ("no package.tersus in " ++ (root </> "client/util")) disk
            <> phase1Refusal ("no package.tersus in " ++ (root </> "client/util")) (memory options files))) orders
    accepted <- mapM (\source -> do
        let files = (entry, source) : common
            configured = options{packageRoots = Map.insert "util" util (packageRoots options)}
        write files
        disk <- Pipeline.loadFromFilesystemWithOptions configured entry
        pure (testAssertEq (output disk) (Ok (Just (MInt 42)))
            <> testAssertEq (output (memory configured files)) (Ok (Just (MInt 42))))) orders
    let transit = "import vendor::api { answer }; return answer();"
    write ((entry, transit) : common)
    transitive <- Pipeline.loadFromFilesystemWithOptions options entry
    let local = root </> "client/util"
        conflicting source = (entry, source) : common ++ [(local </> "package.tersus", "noPrelude = true;"), (local </> "api/api.tersus", "fn value() -> Int { return 99; };")]
    conflicts <- mapM (\source -> do
        let files = conflicting source
        write files
        disk <- Pipeline.loadFromFilesystemWithOptions options entry
        pure (phase1Refusal "conflicting roots for package \"util\"" disk
            <> phase1Refusal "conflicting roots for package \"util\"" (memory options files))) orders
    pure (foldr (<>) Nothing (refused ++ accepted ++ conflicts)
        <> testAssertEq (output transitive) (Ok (Just (MInt 42))))

phase1SymlinkRoots :: Test
phase1SymlinkRoots = TestCase "physical root aliases deduplicate one name and refuse two logical package names" $ withPhase1Directory $ \root -> do
    let pkg = root </> "pkg"
        alias = root </> "linked"
        source = "import pkg::api { answer }; return answer();"
        paths = [(pkg </> "package.tersus", "noPrelude = true;"), (pkg </> "main.tersus", source), (pkg </> "api/api.tersus", "fn answer() -> Int { return 42; };")]
    mapM_ (\(path,text) -> createDirectoryIfMissing True (takeDirectory path) >> writeFile path text) paths
    createDirectoryLink pkg alias
    let opts = defaultLoadOptions{packageRoots = Map.singleton "pkg" alias, noPrelude = True}
    direct <- Pipeline.loadFromFilesystemWithOptions opts (pkg </> "main.tersus")
    throughAlias <- Pipeline.loadFromFilesystemWithOptions opts (alias </> "main.tersus")
    let app = root </> "app"
    createDirectoryIfMissing True app
    writeFile (app </> "package.tersus") "noPrelude = true;"
    writeFile (app </> "main.tersus") "import linked::api { answer }; return answer();"
    mappedSibling <- Pipeline.loadFromFilesystemWithOptions opts{packageRoots = Map.singleton "linked" pkg} (app </> "main.tersus")
    let solo = root </> "solo/main.tersus"
    createDirectoryIfMissing True (takeDirectory solo)
    writeFile solo "import first::api; import second::api; return 0;"
    duplicate <- Pipeline.loadFromFilesystemWithOptions opts{packageRoots = Map.fromList [("first",pkg),("second",alias)]} solo
    pure (testAssertEq (fmap loadedIdentity direct) (fmap loadedIdentity throughAlias)
        <> (case direct of
            Right (PackageResult loaded) -> testAssertEq (compileModulesToProgram loaded `bindResult` runProgram) (Ok (Just (MInt 42)))
            other -> Just (show other))
        <> (case mappedSibling of
            Right (PackageResult loaded) -> testAssertEq (compileModulesToProgram loaded `bindResult` runProgram) (Ok (Just (MInt 42)))
            other -> Just ("canonical mapped sibling disagreed: " ++ show other))
        <> phase1Refusal "conflicting package identities" duplicate)
  where
    loadedIdentity (PackageResult pkg) = packageInputIdentity pkg
    loadedIdentity _ = "standalone"

phase1UnimportedParsing :: Test
phase1UnimportedParsing = TestCase "default and no-prelude parsing never seed an unimported declaration" $ do
    seen <- newIORef []
    let unrelated = "enum Unimported { A { hidden: Bool }, B };"
        files = phase1Files phase1Program ++ [("unrelated/app/unused/unused.tersus", unrelated)]
        observing decls source = unsafePerformIO $ do
            modifyIORef' seen (source :)
            pure (NativeParser.parseFileWith decls source)
        check options = case loadFromEntryWith observing (resolverFromFiles files){resolverOptions = options} phase1Entry of
            Left err -> Just err
            Right (PackageResult pkg) -> case PackageCompile.compileModulesLinked pkg of
                Error err -> Just err
                Ok program -> testAssertEq (runProgram program) (Ok (Just (MInt 42)))
            Right _ -> Just "expected package"
    let results = [check phase1Options{noPrelude = enabled} | enabled <- [False, True]]
    _ <- evaluate (forceTestResult (foldr (<>) Nothing results))
    observed <- readIORef seen
    pure (foldr (<>) Nothing results <> testAssertTrue (unrelated `notElem` observed))

testPhase1RootAvailability :: Test
testPhase1RootAvailability = TestList "root declaration availability is independent of import order"
    ([ testCase (show (enabled, prefix, "extern/module ambiguity")) $
        phase1Refusal "ambiguous import: \"child\"" (loadFromEntryWith NativeParser.parseFileWith (resolver enabled
            (prefix ++ "import vendor::child; return 0;") rootSource True) "pkgs/app/main.tersus")
    | enabled <- [False, True], prefix <- ["", "import vendor; "]
    ] ++
    [ testCase (show (enabled, prefix, "explicit extern")) $ case loadFromEntryWith NativeParser.parseFileWith
        (resolver enabled (prefix ++ "import vendor::vendor::child; return 0;") rootSource False) "pkgs/app/main.tersus" of
            Left err -> Just err
            Right (PackageResult pkg) -> testAssertEq
                [resolvedLevel ri | modu <- packageModules pkg, file <- loadedModuleFiles modu, ri <- loadedImports file, importPath (resolvedImport ri) == ["vendor", "vendor", "child"]]
                [LevelSymbol]
            Right _ -> Just "expected package"
    | enabled <- [False, True], prefix <- ["", "import vendor; "]
    ] ++
    [ testCase (show (enabled, prefix, "missing name")) $ case loadFromEntryWith NativeParser.parseFileWith
        (resolver enabled (prefix ++ "import vendor::vendor::Missing; return 0;") rootSource False) "pkgs/app/main.tersus" of
            Left err -> testAssertTrue ("it declares: child, Point" `isInfixOf` err && not ("<Point>::answer" `isInfixOf` err))
            Right _ -> Just "missing name became importable"
    | enabled <- [False, True], prefix <- ["", "import vendor; "]
    ] ++
    [ testCase (show (enabled, "associated method through type import")) $ case loadFromEntryWith NativeParser.parseFileWith
        (resolver enabled "import vendor::vendor { Point }; p = Point { n: 42 }; return p.answer();" methodSource False) "pkgs/app/main.tersus" of
            Left err -> Just err
            Right (PackageResult pkg) -> case compileModulesToProgram pkg of
                Error err -> Just err
                Ok program -> testAssertEq (runProgram program) (Ok (Just (MInt 42)))
                    <> testAssertTrue (any (elem "<Point>::answer" . loadedDeclNames) [file | modu <- packageModules pkg, modulePackage (loadedModuleId modu) == "vendor", file <- loadedModuleFiles modu])
            Right _ -> Just "expected package"
    | enabled <- [False, True]
    ] ++
    [ testCase "native metadata names agree with importable parsed declarations" $ case Oracle.parseFileWith (locating emptyDecls) rootSource of
        Left err -> Just err
        Right (parsed, _) -> testAssertEq (Oracle.parseDeclarationNames rootSource)
            (Right (filter (notElem '<') (declarationNames (fileBody parsed))))
    ])
  where
    methodSource = "struct Point { n: Int }; impl Point { fn answer(self: &Self) -> Int { return self.n; }; };"
    rootSource = "extern fn child() -> Int [{ }] [{ }]; " ++ methodSource
    resolver enabled source body child = (resolverFromFiles
        ([ ("pkgs/app/package.tersus", "")
         , ("pkgs/app/main.tersus", source)
         , ("pkgs/vendor/package.tersus", "noPrelude = true;")
         , ("pkgs/vendor/vendor.tersus", body)
         ] ++ [("pkgs/vendor/child/child.tersus", "fn answer() -> Int { return 42; };") | child]))
        {resolverOptions = defaultLoadOptions{noPrelude = enabled}}

testPhase1Packages :: Test
testPhase1Packages = TestList "testPhase1Packages"
    [ TestCase "filesystem packages and standalone stdin sources use the same configured resolver" phase1Filesystem
    , phase1StandaloneRoots
    , phase1CurrentImporterRoots
    , phase1SymlinkRoots
    , phase1UnimportedParsing
    , testPhase1RootAvailability
    , testCase "external roots seed imported enums and check link evaluate normally" $ case phase1Load phase1Options (phase1Files phase1Program) of
        Left err -> Just err
        Right pkg -> case compileModulesToProgram pkg of
            Error err -> Just err
            Ok program -> testAssertEq (runProgram program) (Ok (Just (MInt 42)))
                <> testAssertEq (moduleOrder pkg) ["vendor::model", "app"]
                <> testAssertTrue (all loadedNoPrelude (packageModules pkg))
    , testCase "installed standard root is a normal root input without source relocation" $
        let source = "import std::model { Choice, read }; c = Choice::Value { n: 42 }; return read(c);"
            options = defaultLoadOptions{installedStdRoot = Just phase1Root, noPrelude = True}
         in case phase1Load options (phase1Files source) of
                Left err -> Just err
                Right pkg -> case compileModulesToProgram pkg of
                    Error err -> Just err
                    Ok program -> testAssertEq (runProgram program) (Ok (Just (MInt 42)))
    , testCase "installed dependency opts out while default importing user does not" $ case phase1Load phase1Options{noPrelude = False} (phase1Files phase1Program) of
        Left err -> Just err
        Right pkg -> case compileModules pkg of
            Error err -> Just err
            Ok compiled -> testAssertEq (map loadedNoPrelude (packageModules pkg)) [True, False]
                <> testAssertTrue (case compiledModules compiled of
                    dependency : user : [] -> null (compiledLibInterfaces dependency) && null (compiledLibUnits dependency)
                        && not (null (compiledLibInterfaces user)) && not (null (compiledLibUnits user))
                    _ -> False)
    , testCase "no-prelude source files receive no implicit library declaration seed" $
        let guarded declarations source
                | any (`Map.member` declTypes declarations) ["List", "Box", "String", "HashMap"] = Left "implicit library seed reached no-prelude source"
                | otherwise = Oracle.parseFileWith declarations source
         in case loadFromEntryWith guarded (resolverFromFiles (phase1Files phase1Program)){resolverOptions = phase1Options} phase1Entry of
                Left err -> Just err
                Right (PackageResult pkg) -> case compileModules pkg of
                    Error err -> Just err
                    Ok compiled -> testAssertTrue (all (\modu -> null (compiledLibInterfaces modu) && null (compiledLibUnits modu)) (compiledModules compiled))
                Right _ -> Just "expected package"
    , testCase "standalone no-prelude parsing never probes implicit source declarations" $
        let guarded declarations source
                | declarations /= locating emptyDecls = Left "nonempty source declaration seed"
                | otherwise = Oracle.parseFileWith declarations source
         in case SourceParse.parseSourcePartsWith guarded True True "return 17 + 25;" of
                Error err -> Just err
                Ok (names, library, _) -> testAssertEq names [] <> testAssertEq library []
    , testCase "empty-library source lowering has no implicit package dependency" $ case Compile.lowerSourceParts True ([], [], [Return (Val (VInt 42))]) of
        Error err -> Just err
        Ok program -> testAssertEq (runProgram program) (Ok (Just (MInt 42)))
            <> testAssertTrue (Map.null (M.progFunctions program) && Map.null (M.progTypes program))
    , testCase "no-prelude still validates scalar machine-core statements" $
        phase1ResultRefusal "Could not prove:" (Pipeline.compileSourceNoPrelude True "affirm 1 = 2; return 42;")
    , testCase "no-prelude packages still validate their source bodies" $ case phase1Load phase1Options (phase1Files "affirm 1 = 2; return 42;") of
        Left err -> Just err
        Right pkg -> phase1ResultRefusal "Could not prove:" (compileModulesToProgram pkg)
    , testCase "a missing requested root fails even when a sibling exists" $
        phase1Refusal "requested root" (phase1Load phase1Options{packageRoots = Map.singleton "vendor" "absent/vendor"}
            (phase1Files phase1Program ++ [("unrelated/vendor/package.tersus", ""), ("unrelated/vendor/model/model.tersus", "struct Choice { n: Int };")]))
    , testCase "explicit and sibling roots conflict rather than silently shadow" $
        phase1Refusal "conflicting roots" (phase1Load phase1Options
            (phase1Files phase1Program ++ [("unrelated/vendor/package.tersus", ""), ("unrelated/vendor/model/model.tersus", "struct Choice { n: Int };")]))
    , testCase "installed and mapped standard roots conflict" $
        phase1Refusal "conflicting roots" (phase1Load defaultLoadOptions{packageRoots = Map.singleton "std" "another/std", installedStdRoot = Just phase1Root}
            (phase1Files "import std::model; return 0;" ++ [("another/std/package.tersus", "")]))
    , testCase "cross-root cycles are refused" $
        let files = [(path, if path == phase1Root ++ "/model/model.tersus" then "import app; " ++ source else source) | (path, source) <- phase1Files phase1Program]
            options = phase1Options{packageRoots = Map.fromList [("vendor", phase1Root), ("app", "unrelated/app")]}
         in phase1Refusal "module import cycle:" (phase1Load options files)
    , testCase "unimported qualified enum name is not globally seeded" $
        phase1Refusal "parse error" (phase1Load phase1Options (phase1Files "c = vendor::model::Choice::Value { n: 42 }; return 0;"))
    , testCase "missing listed import has a declaration diagnostic" $
        phase1Refusal "name Missing is not declared" (phase1Load phase1Options (phase1Files "import vendor::model { Missing }; return 0;"))
    , testCase "invalid package boolean is rejected without body-parser configuration" $
        phase1Refusal "package configuration:" (phase1Load phase1Options [(path, if path == phase1Root ++ "/package.tersus" then "noPrelude = maybe;" else text) | (path,text) <- phase1Files phase1Program])
    , testCase "package markers accept line comments without changing unit policy" $ case phase1Load phase1Options
        [(path, if path == phase1Root ++ "/package.tersus" then "// opt out\nnoPrelude = true; // all files\n" else text) | (path,text) <- phase1Files phase1Program] of
            Left err -> Just err
            Right pkg -> testAssertTrue (all loadedNoPrelude (packageModules pkg))
    , testCase "package markers reject block comments like source files" $
        phase1Refusal "package configuration:" (phase1Load phase1Options
            [(path, if path == phase1Root ++ "/package.tersus" then "/* opt out */ noPrelude = true;" else text) | (path,text) <- phase1Files phase1Program])
    , testCase "same-module declaration contexts survive no-prelude" $ case phase1Load phase1Options
        (phase1Files "import app::late { Local }; c = Local::Value { n: 42 }; return match c { Local::Value { n: n } => n, };" ++ [("unrelated/app/late.tersus", "enum Local { Value { n: Int } };")]) of
            Left err -> Just err
            Right pkg -> case compileModulesToProgram pkg of
                Error err -> Just err
                Ok program -> testAssertEq (runProgram program) (Ok (Just (MInt 42)))
    , testCase "package CLI options do not consume program arguments" $
        testAssertEq (Cli.parseCompilerOptions ["--no-prelude", "--package-root", "vendor=installed/vendor-v1", "eval", "file", "--no-prelude"])
            (Just (phase1Options, ["eval", "file", "--no-prelude"]))
    , testCase "conflicting and malformed CLI root declarations are refused" $
        testAssertTrue (all ((== Nothing) . Cli.parseCompilerOptions)
            [["--package-root", "vendor=a", "--package-root", "vendor=b", "check", "file"], ["--package-root", "=a"], ["--package-root", "a="], ["--std-root"], ["--std-root", "a", "--std-root", "b"]])
    ]

phase2Entry :: FilePath
phase2Entry = "unrelated/app/main.tersus"

phase2Files :: String -> String -> Files -> Files
phase2Files source api extra =
    [ ("unrelated/app/package.tersus", "noPrelude = true;")
    , (phase2Entry, source)
    , ("installed/vendor/package.tersus", "noPrelude = true;")
    , ("installed/vendor/api/api.tersus", api)
    ] ++ extra

phase2Load :: Files -> Either String LoadedPackage
phase2Load files = case Pipeline.loadFromEntry
    (resolverFromFiles files){resolverOptions = defaultLoadOptions{packageRoots = Map.singleton "vendor" "installed/vendor"}} phase2Entry of
        Right (PackageResult pkg) -> Right pkg
        Right _ -> Left "expected an ordinary external package"
        Left err -> Left err

phase2Runs :: Files -> Int -> TestResult
phase2Runs files expected = case phase2Load files of
    Left err -> Just err
    Right pkg -> case compileModulesToProgram pkg `bindResult` runProgram of
        Error err -> Just err
        Ok value -> testAssertEq value (Just (MInt (toInteger expected)))

phase2Rejects :: Files -> [String] -> TestResult
phase2Rejects files needles = case phase2Load files of
    Left err -> check err
    Right pkg -> case compileModulesToProgram pkg of
        Error err -> check err
        Ok _ -> Just ("accepted instead of refusing " ++ show needles)
  where
    check err = foldr (<>) Nothing [if needle `isInfixOf` err then Nothing else Just ("expected " ++ show needle ++ ", got: " ++ err) | needle <- needles]

phase2Identity :: String
phase2Identity = "trait Mark { }; impl Mark for Int { }; fn value<T: Mark>(x: T) -> T { return x; };"

phase2Impl :: String -> String
phase2Impl body = "trait Mark { }; impl Mark for Int { }; struct Wrap<T> { value: T }; trait Read<E> { fn read(self: &Self) -> E; }; impl<T: Mark + Clone> Read<T> for Wrap<T> { fn read(self: &Self) -> T { " ++ body ++ " }; };"

-- (the provider has the prelude for the Clone bound its clone of a T needs)
phase2ImplFiles :: String -> Files
phase2ImplFiles source = [(path, if path == "installed/vendor/package.tersus" then "" else text) | (path, text) <- phase2Files source (phase2Impl "return clone(self.value);") []]

phase2WriteFiles :: String -> Files
phase2WriteFiles field = phase2Files
    "import vendor::api { Pair, value }; p = Pair<Int> { x: 1, y: 2 }; value(&mut p, 42); return p.x;"
    ("trait Mark { }; impl Mark for Int { }; struct Pair<T> { x: T, y: T }; fn value<T: Mark>(p: &mut Pair<T>, x: T) -> Int writes(p.x) [{ }] [{ }] { (*p)." ++ field ++ " = x; return 0; };") []

phase2PrivateResultFiles :: Files
phase2PrivateResultFiles = phase2Files
    "import vendor::api { value }; p = value(1); return p.value;"
    "import vendor::helpers as h; trait Mark { }; impl Mark for Int { }; fn value<T: Mark>(x: T) -> h::Hidden { return h::make(42); };"
    [("installed/vendor/helpers/helpers.tersus", "struct Hidden { value: Int } invariant [{ affirm value >= 0; }]; fn make(n: Int) -> Hidden [{ affirm n >= 0; }] [{ affirm return.value = n; }] { return Hidden { value: n }; };")]

phase2ForeignImplFiles :: Files
phase2ForeignImplFiles = phase2Files
    "import vendor::model { Wrap }; import vendor::api { Read }; p = Wrap<Int> { value: 1 }; return Read::read(p);"
    "import vendor::model { Wrap }; trait Mark { }; impl Mark for Int { }; trait Read { fn read(self: &Self) -> Int; }; impl<T: Mark> Read for Wrap<T> { fn read(self: &Self) -> Int [{ }] [{ affirm return = 42; }] { return 42; }; };"
    [("installed/vendor/model/model.tersus", "struct Wrap<T> { value: T };")]

phase2ConflictingFiles :: Files
phase2ConflictingFiles = phase2Files
    "import app::left { a }; import app::right { b }; return a() + b();"
    "import vendor::model { Mark }; fn value<T: Mark>(x: &T) -> Int { return x.read(); };"
    [ ("installed/vendor/model/model.tersus", "trait Mark { }; struct Item { }; impl Mark for Item { };")
    , ("unrelated/app/left/left.tersus", consumer "a" "1")
    , ("unrelated/app/right/right.tersus", consumer "b" "2")
    ]
  where
    consumer name result = "import vendor::api { value }; import vendor::model { Item }; trait Read { fn read(self: &Self) -> Int; }; impl Read for Item { fn read(self: &Self) -> Int { return " ++ result ++ "; }; }; fn " ++ name ++ "() -> Int { return value(Item { }); };"

phase2CallerOnlyTrait :: Files
phase2CallerOnlyTrait = [(path, if path == phase2Entry then "import app::left { a }; return a();" else text) | (path, text) <- phase2ConflictingFiles]

phase2CallerOnlyFunction :: Files
phase2CallerOnlyFunction = phase2Files
    "import vendor::api { value }; fn secret(x: Int) -> Int { return 42; }; return value(1);"
    "trait Mark { }; impl Mark for Int { }; fn value<T: Mark>(x: T) -> Int { return secret(x); };" []

phase2NoPreludeHashFiles :: Files
phase2NoPreludeHashFiles = [(path, if path == "unrelated/app/package.tersus" then "" else text) | (path, text) <- phase2Files
    "import vendor::api { Mark, value }; struct Local { n: Int }; impl Mark for Local { }; impl Hash for Local { fn hash(self: &Self) -> Int [{ }] [{ affirm return = 1; }] { return 1; }; }; p = Local { n: 1 }; return value(p);"
    "trait Mark { }; fn value<T: Mark>(x: &T) -> Int { return Hash::hash(x); };" []]

phase2CallerTypeFiles :: Bool -> Files
phase2CallerTypeFiles implementation = phase2Files
    ("import vendor::api { Mark, Wrap, value, Read }; struct Local { n: Int } invariant [{ affirm n >= 0; }]; impl Mark for Local { fn marked(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return self.n; }; }; p = Local { n: 42 }; " ++ (if implementation then "w = Wrap<Local> { value: p }; return Read::read(w);" else "return value(p);"))
    "trait Mark { fn marked(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; fn value<T: Mark>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return Mark::marked(x); }; struct Wrap<T> { value: T }; trait Read { fn read(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl<T: Mark> Read for Wrap<T> { fn read(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return Mark::marked(self.value); }; };" []

phase2ConflictingContracts :: Files
phase2ConflictingContracts = phase2Files
    "import app::left; import app::right; return 0;"
    phase2Identity
    [ ("unrelated/app/left/left.tersus", "extern fn shared(x: Int) -> Int [{ }] [{ affirm return = 1; }];")
    , ("unrelated/app/right/right.tersus", "extern fn shared(x: Int) -> Int [{ }] [{ affirm return = 2; }];")
    ]

phase2Private :: Files
phase2Private = phase2Files
    "import vendor::api { value }; fn pass(x: Bool) -> Bool { return x; }; return value(42);"
    "import vendor::helpers { Good, pass }; trait Mark { }; impl Mark for Int { }; fn value<T: Mark + Good>(x: T) -> T { return pass(x); };"
    [("installed/vendor/helpers/helpers.tersus", "trait Good { }; impl Good for Int { }; struct Hidden<T> { value: T }; fn pack<T: Good>(x: T) -> Hidden<T> { return Hidden { value: x }; }; fn pass<T: Good>(x: T) -> T { h = pack(x); return h.value; };")]

testPhase2Packages :: Test
testPhase2Packages = TestList "testPhase2Packages"
    [ TestCase "external private templates run identically from disk in reference and native code" phase2Filesystem
    , TestCase "caller-owned visible-trait implementations run in reference and native code" (phase2FilesystemWith (phase2CallerTypeFiles True))
    , testCase "entry and external bounded helpers share checking rules" $
        case Pipeline.compileSourceNoPrelude True (phase2Identity ++ " return value(42);") `bindResult` runProgram of
            Error err -> Just err
            Ok value -> testAssertEq value (Just (MInt 42))
    , testCase "external bounded function uses ordinary checked exports" $
        phase2Runs (phase2Files "import vendor::api { value }; return value(42);" phase2Identity []) 42
    , testCase "bounded return signatures preserve current implicit library selection" $
        phase2Runs [(path, if "package.tersus" `isSuffixOf` path then "" else text) | (path, text) <- phase2Files
            "import vendor::api { value }; return size(value(1));"
            "trait Mark { }; impl Mark for Int { }; fn value<T: Mark>(x: T) -> String { return \"hi\"; };" []] 2
    , testCase "external bounded implementation and trait companion instantiate" $
        phase2Runs (phase2ImplFiles "import vendor::api { Wrap }; v = Wrap<Int> { value: 42 }; return v.read();") 42
    , testCase "nested private generic constructors and helpers keep defining context" $ phase2Runs phase2Private 42
    , testCase "explicit private generic constructor arguments specialize with their template" $
        phase2Runs [(path, if "helpers.tersus" `isSuffixOf` path then "trait Good { }; impl Good for Int { }; struct Hidden<T> { value: T }; fn pack<T: Good>(x: T) -> Hidden<T> { return Hidden<T> { value: x }; }; fn pass<T: Good>(x: T) -> T { h = pack(x); return h.value; };" else text) | (path, text) <- phase2Private] 42
    , testCase "private nominal result metadata remains usable without naming its provider" $ phase2Runs phase2PrivateResultFiles 42
    , testCase "trait-owning modules export bounded implementations for imported types" $ phase2Runs phase2ForeignImplFiles 42
    , testCase "caller-only traits cannot satisfy defining-site method visibility" $ phase2Rejects phase2CallerOnlyTrait ["in module vendor::api", "value calls read on a T, and no bound of it has a function read"]
    , testCase "a no-prelude provider cannot inherit the caller's selected Hash trait" $ phase2Rejects phase2NoPreludeHashFiles ["in module vendor::api", "Undefined variable: Hash::hash"]
    , testCase "caller-owned types satisfy visible vendor bounds" $ phase2Runs (phase2CallerTypeFiles False) 42
    , testCase "bounded vendor implementations use caller implementations of visible traits" $ phase2Runs (phase2CallerTypeFiles True) 42
    , testCase "caller-only bare functions are not template defining dependencies" $ phase2Rejects phase2CallerOnlyFunction ["in module vendor::api", "Undefined variable: secret"]
    , testCase "different checked function bodies remain a link conflict" $ expectProgramErrorAll
        [ ("app/package.tersus", "")
        , ("app/main.tersus", "import app::geo; fn findNth(x: Int) -> Int { return x + 1; }; return findNth(1) + geo::setSize();")
        , ("app/geo/geo.tersus", "fn setSize() -> Int { s = HashSet::new().insert(1).insert(2); return s.size(); };")
        ] "app/main.tersus" ["link error: function findNth", "tersuslib::map", "module app", "different definitions"]
    , testCase "different linked contracts remain a link conflict" $ phase2Rejects phase2ConflictingContracts ["link error: function extern fn shared", "different definitions"]
    , testCase "private template closure does not expose a bare helper" $
        phase2Rejects [(path, if path == phase2Entry then "import vendor::api { value }; x = value(42); return pass(x);" else text) | (path, text) <- phase2Private] ["Undefined variable: pass"]
    , testCase "private template closure does not expose a qualified helper" $
        phase2Rejects [(path, if path == phase2Entry then "import vendor::api { value }; x = value(42); return vendor::helpers::pass(x);" else text) | (path, text) <- phase2Private] ["covering import"]
    , testCase "bounded function refuses an unsatisfied ordinary trait" $
        phase2Rejects (phase2Files "import vendor::api { value }; return value(true);" phase2Identity []) ["needs T to implement", "Mark", "Bool does not"]
    , testCase "bounded implementation refuses an unsatisfied ordinary trait" $
        phase2Rejects (phase2ImplFiles "import vendor::api { Wrap }; v = Wrap<Bool> { value: true }; return v.read();") ["needs T to implement", "Mark", "Bool does not"]
    , testCase "bounded calls retain their requires contract" $
        phase2Rejects (phase2Files "import vendor::api { value }; return value(1, -1);"
            "trait Mark { }; impl Mark for Int { }; fn value<T: Mark>(x: T, n: Int) -> T [{ affirm n >= 0; }] [{ }] { return x; };" []) ["Could not prove:", "n >= 0"]
    , testCase "bounded write footprints retain permitted field updates" $
        phase2Runs (phase2WriteFiles "x") 42
    , testCase "bounded write footprints reject an unlisted field update" $
        phase2Rejects (phase2WriteFiles "y") ["in module vendor::api", "writes clause of the function does not allow"]
    , testCase "bounded implementation companion checks the trait contract" $
        phase2Rejects (phase2Files "import vendor::api { Wrap }; return Wrap<Int> { value: 1 }.read();"
            "trait Mark { }; impl Mark for Int { }; struct Wrap<T> { value: T }; trait Read { fn read(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl<T: Mark> Read for Wrap<T> { fn read(self: &Self) -> Int { return -1; }; };" []) ["does not meet what", "could not prove return >= 0"]
    , testCase "private struct invariants survive template lowering" $
        phase2Rejects (phase2Files "import vendor::api { value }; return value(1, -1);"
            "trait Mark { }; impl Mark for Int { }; struct Positive { value: Int } invariant [{ affirm value >= 0; }]; fn value<T: Mark>(x: T, n: Int) -> Int { p = Positive { value: n }; return p.value; };" []) ["Could not prove:"]
    , testCase "invalid bound declarations are refused normally" $
        phase2Rejects (phase2Files "import vendor::api { value }; return value(1);"
            "fn value<T: Missing>(x: T) -> T { return x; };" []) ["unknown trait", "Missing", "bound"]
    , testCase "unused bounded signatures are checked before export" $
        phase2Rejects (phase2Files "import vendor::api; return 0;"
            "trait Mark { }; fn value<T: Mark>(x: T) -> Missing { return x; };" []) ["unknown type Missing"]
    , testCase "ordinary import ambiguity is not hidden by templates" $
        phase2Rejects (phase2Files "import vendor::api { value }; import vendor::other { value }; return value(1);" phase2Identity
            [("installed/vendor/other/other.tersus", phase2Identity)]) ["ambiguous", "value"]
    , testCase "external orphan implementations remain refused" $
        phase2Rejects (phase2Files "import vendor::other; return 0;"
            "trait Read { fn read(self: &Self) -> Int; }; struct Wrap<T> { value: T };"
            [("installed/vendor/other/other.tersus", "import vendor::api { Read, Wrap }; trait Mark { }; impl Mark for Int { }; impl<T: Mark> Read for Wrap<T> { fn read(self: &Self) -> Int { return 1; }; };")]) ["orphan impl", "neither a trait nor a type"]
    , testCase "inferred generic constructor identities survive template substitution" phase2InferredConstructor
    , testCase "inferred generic constructors validate in an external bounded body" $ phase2Runs phase2InferredFiles 42
    , testCase "implementation bounds match their trait argument types" $ phase2Runs (phase2ArgumentFiles "Int" "return 7;") 1
    , testCase "implementation bounds refuse a different trait argument type" $
        phase2Rejects (phase2ArgumentFiles "Bool" "return true;") ["needs U to implement", "Label", "does not"]
    , testCase "caller implementation prerequisites use their defining scope" $ phase2Runs (phase2PrerequisiteFiles False False) 42
    , TestCase "private caller prerequisites validate in reference and native code" $ phase2FilesystemWith (phase2PrerequisiteFiles False False)
    , testCase "implementation-private traits do not enter provider method scope" $ phase2Rejects (phase2PrerequisiteFiles True False) ["in module vendor::api", "value calls good on a T, and no bound of it has a function good"]
    , testCase "private caller implementation companions retain provider contracts" $ phase2Rejects (phase2PrerequisiteFiles False True) ["does not meet what", "could not prove return >= 0"]
    , testCase "implementation bounds substitute matched array sizes" $ phase2Runs (phase2SizeArgumentFiles "3" "#[1, 2, 3]") 42
    , TestCase "matched size bounds run from disk in reference and native code" $ phase2FilesystemWith (phase2SizeArgumentFiles "3" "#[1, 2, 3]")
    , testCase "implementation bounds refuse a different array size" $
        phase2Rejects (phase2SizeArgumentFiles "4" "#[1, 2, 3, 4]") ["needs U to implement", "Label", "does not"]
    , testCase "outer size binders specialize array constructor and return types" $ phase2Runs (phase2SizedReturnFiles "return array(n, 1);" "return size(make(p, a)) + 39;") 42
    , TestCase "sized array returns validate and run in reference and native code" $ phase2FilesystemWith (phase2SizedReturnFiles "return array(n, 1);" "return size(make(p, a)) + 39;")
    , testCase "inner function size parameters shadow outer size specialization" $ phase2CheckedShadow (phase2SizedReturnFiles "fn f<n>(a: &Array<Int, n>) -> Array<Int, n> { return array(n, 2); }; b = #[1, 2, 3, 4]; c = f(b); return array(n, size(c));" "return get(make(p, a), 0) + 38;")
    , testCase "inner local values shadow outer size specialization" $ phase2CheckedShadow (phase2SizedReturnFiles "fn f(x: Int) -> Int { n = 5; return n; }; return array(n, f(0));" "return get(make(p, a), 0) + 37;")
    , testCase "size-specialized array returns refuse a different concrete size" $ phase2Rejects (phase2SizedReturnFiles "return array(4, 1);" "return size(make(p, a));") ["in module vendor::api", "returned value:", "expected Array<Int, n>", "got Array<Int, 4>"]
    , testCase "repeated aliases and cross-module uses link one canonical instance" phase2Dedup
    , testCase "ghost-bearing cross-module templates deduplicate without losing proof context" $
        phase2DedupWith "trait Mark { }; impl Mark for Int { }; fn value<T: Mark>(x: T) -> T { affirm 1 = 1; return x; };"
    , testCase "checked defining closure survives request and interface round trips" phase2RoundTrip
    ]

phase2Filesystem :: IO TestResult
phase2Filesystem = phase2FilesystemWith phase2Private

phase2FilesystemWith :: Files -> IO TestResult
phase2FilesystemWith files = withPhase1Directory $ \root -> do
    let entry = root </> phase2Entry
        options = defaultLoadOptions{packageRoots = Map.singleton "vendor" (root </> "installed/vendor")}
    mapM_ (\(path, text) -> createDirectoryIfMissing True (takeDirectory (root </> path)) >> writeFile (root </> path) text) files
    loaded <- Pipeline.loadFromFilesystemWithOptions options entry
    case loaded of
        Left err -> pure (Just err)
        Right (PackageResult pkg) -> case compileModulesToProgram pkg of
            Error err -> pure (Just err)
            Ok reference -> case compileModulesToOwned pkg of
                Error err -> pure (Just err)
                Ok owned -> do
                    emitted <- Bootstrap.llvmOfOwned owned
                    case emitted of
                        Error err -> pure (Just err)
                        Ok llvm -> do
                            let executable = root </> "external-generics"
                            built <- Native.buildExecutable executable llvm
                            case built of
                                Error err -> pure (Just err)
                                Ok () -> do
                                    (code, out, err) <- Native.runWithInputFull executable ""
                                    pure (testAssertEq (runProgram reference) (Ok (Just (MInt 42)))
                                        <> testAssertEq (code, out, err) (ExitSuccess, "42\n", ""))
        Right _ -> pure (Just "expected package")

phase2InferredFiles :: Files
phase2InferredFiles =
    [(path, if path == "installed/vendor/package.tersus" then "" else text) | (path, text) <- phase2Files
        "import vendor::api { value }; return value(1);"
        "trait Mark { }; impl Mark for Int { }; fn value<T: Mark>(x: T) -> Int { m = HashMap::new().insert(1, 42); return m.lookup(1, 0); };" []]

phase2InferredConstructor :: TestResult
phase2InferredConstructor = case loadFromEntry
    (resolverFromFiles phase2InferredFiles){resolverOptions = defaultLoadOptions{packageRoots = Map.singleton "vendor" "installed/vendor"}} phase2Entry of
        Left err -> Just err
        Right (PackageResult pkg) -> case PackageCompile.compileModulesLinked pkg of
            Error err -> Just err
            Ok raw -> testAssertTrue (Map.member "vendor$api$api$value[Int]" (M.progFunctions raw))
        Right _ -> Just "expected package"

phase2ArgumentFiles :: String -> String -> Files
phase2ArgumentFiles argument body = phase2Files
    "import vendor::api { Holder, Item, inspect }; h = Holder<Item> { value: Item { } }; return inspect(h);"
    ("trait Feed<E> { fn feed(self: &Self) -> E; }; struct Item { }; impl Feed<" ++ argument ++ "> for Item { fn feed(self: &Self) -> " ++ argument ++ " { " ++ body ++ " }; }; trait Label { fn label(self: &Self) -> Int; }; struct Holder<T> { value: T }; impl<T: Feed<Int>> Label for Holder<T> { fn label(self: &Self) -> Int { return 1; }; }; fn inspect<U: Label>(x: &U) -> Int { return 1; };") []

phase2PrerequisiteFiles :: Bool -> Bool -> Files
phase2PrerequisiteFiles leak badContract = phase2Files
    ("import vendor::api { Mark, value }; trait Good { fn good(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Good for Int { fn good(self: &Self) -> Int [{ }] [{ affirm return = 42; }] { return 42; }; }; struct Wrap<T> { value: T }; impl<U: Good> Mark for Wrap<U> { fn marked(self: &Self) -> Int [{ }] [{ " ++ (if badContract then "" else "affirm return >= 0;") ++ " }] { return " ++ (if badContract then "-1" else "self.value.good()") ++ "; }; }; p = Wrap<Int> { value: 1 }; return value(p);")
    ("trait Mark { fn marked(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; fn value<T: Mark>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return " ++ (if leak then "x.good()" else "Mark::marked(x)") ++ "; };") []

phase2SizeArgumentFiles :: String -> String -> Files
phase2SizeArgumentFiles size body = phase2Files
    "import vendor::api { Holder, Item, inspect }; h = Holder<Item, 3> { value: Item { }, cells: #[1, 2, 3] }; return inspect(h);"
    ("trait Feed<E> { fn feed(self: &Self) -> E; }; struct Item { }; impl Feed<Array<Int, " ++ size ++ ">> for Item { fn feed(self: &Self) -> Array<Int, " ++ size ++ "> { return " ++ body ++ "; }; }; trait Label { fn label(self: &Self) -> Int; }; struct Holder<T, n> { value: T, cells: Array<Int, n> }; impl<T: Feed<Array<Int, n>>, n> Label for Holder<T, n> { fn label(self: &Self) -> Int [{ }] [{ affirm return = n + 39; }] { return n + 39; }; }; fn inspect<U: Label>(x: &U) -> Int { return x.label(); };") []

phase2CheckedShadow :: Files -> TestResult
phase2CheckedShadow files =
    (case phase2Load files of
        Left err -> Just err
        Right pkg -> case PackageCompile.compileModulesLinked pkg `bindResult` runProgram of
            Error err -> Just err
            Ok value -> testAssertEq value (Just (MInt 42)))
    <> phase2Rejects files ["does not model yet: two functions with one name"]

phase2SizedReturnFiles :: String -> String -> Files
phase2SizedReturnFiles body consumer = phase2Files
    ("import vendor::api { Item, make }; p = Item { }; a = #[1, 2, 3]; " ++ consumer)
    ("trait Feed<E> { fn feed(self: &Self) -> E; }; struct Item { }; impl Feed<Array<Int, 3>> for Item { fn feed(self: &Self) -> Array<Int, 3> { return #[1, 2, 3]; }; }; fn make<T: Feed<Array<Int, n>>, n>(x: &T, a: &Array<Int, n>) -> Array<Int, n> { " ++ body ++ " };") []

phase2Dedup :: TestResult
phase2Dedup = phase2DedupWith phase2Identity

phase2DedupWith :: String -> TestResult
phase2DedupWith api = case phase2Load files of
    Left err -> Just err
    Right pkg -> case PackageCompile.compileModulesLinked pkg of
        Error err -> Just err
        Ok raw -> testAssertTrue (all (`elem` map (renderModuleId . loadedModuleId) (packageModules pkg)) ["app::left", "app::right"])
            <> foldr (<>) Nothing [testAssertEq [name | name <- Map.keys (M.progFunctions raw), name == expected] [expected] | expected <- ["vendor$api$api$value[Int]", method, companion]]
            <> (case Map.lookup companion (M.progFunctions raw) of
                Nothing -> Just "missing required checked companion"
                Just fn -> testAssertEq (length (M.specEnsures (M.fnSpec fn))) 1)
            <> (if "affirm" `isInfixOf` api then case Map.lookup "vendor$api$api$value[Int]" (M.progFunctions raw) of
                Nothing -> Just "missing canonical ghost-bearing instance"
                Just fn -> testAssertTrue (any (proofContext raw) (concatMap M.blockStatements (Map.elems (M.fnBlocks fn))))
                else Nothing)
            <> phase2Runs files 94
  where
    method = "<vendor$api$api$Wrap as vendor$api$api$Read>::read[Int]"
    companion = "vendor$api$api$Read for vendor$api$api$Wrap::read[Int]"
    proofContext raw (M.Ghost env (M.GhostValidation (ProofAssert _))) = all (`Map.member` env) (Map.keys (M.progFunctions raw))
    proofContext _ _ = False
    files = phase2Files
        "import app::left { a }; import app::right { b }; import vendor::api as v; import vendor::api as again; return a() + b() + v::value(3) + again::value(4);"
        (api ++ " struct Wrap<T> { value: T }; trait Read { fn read(self: &Self) -> Int [{ }] [{ affirm return = 42; }]; }; impl<T: Mark> Read for Wrap<T> { fn read(self: &Self) -> Int [{ }] [{ affirm return = 42; }] { return 42; }; };")
        [ ("unrelated/app/left/left.tersus", "import vendor::api { value, Wrap }; fn a() -> Int { w = Wrap<Int> { value: 1 }; return w.read() + value(1); };")
        , ("unrelated/app/right/right.tersus", "import vendor::api as v; fn b() -> Int { w = v::Wrap<Int> { value: 2 }; return w.read() + v::value(2); };")
        ]

phase2RoundTrip :: TestResult
phase2RoundTrip = case phase2Load phase2Private of
    Left err -> Just err
    Right pkg -> case PackageCompile.compileModulesWith throughWire pkg of
        Error err -> Just err
        Ok compiled -> foldr (<>) Nothing (map roundTrip (compiledModules compiled))
            <> case PackageCompile.lowerCompiledPackage pkg compiled `bindResult` runProgram of
                Error err -> Just err
                Ok value -> testAssertEq value (Just (MInt 42))
  where
    throughWire request = case Elaboration.writeRequest request `bindResult` checkedRequest request of
        Error err -> Elaboration.Refused err
        Ok decoded | decoded /= request -> Elaboration.Refused "defining context changed during request round trip"
        Ok decoded -> case Elaboration.writeResponse (sourceElaborator decoded) `bindResult` Elaboration.readResponse of
            Error err -> Elaboration.Refused err
            Ok response -> response
    checkedRequest request encoded
        | not (null (Elaboration.rqDefinitions request)) = case Elaboration.readRequest (unlines (filter (not . isPrefixOf "definition ") (lines encoded))) of
            Ok _ -> Error "accepted a legacy flat defining context"
            Error _ -> Elaboration.readRequest encoded
        | otherwise = case Elaboration.readRequest (unlines (filter (/= "definitions 0") (lines encoded))) of
            Ok _ -> Error "accepted a request without defining contexts"
            Error _ -> Elaboration.readRequest encoded
    roundTrip modu = case writeInterface (compiledInterface modu) `bindResult` readInterface of
        Error err -> Just err
        Ok decoded -> testAssertEq decoded (compiledInterface modu)

testModules :: Test
testModules = TestList "testModules" [testModuleLateDeclarations, testValidatorPackage, testCrossPackageBoundaries, testCrossPackageConstructors, testNativeFiles, testNativeModuleLoader, testFileProtocol, testLoaderInjection, testPaths, testMatchOverReference, testCanonical, testImports, testLoaderDiscovery, testLoaderGraph, testLoaderErrors, testLoaderLevels, testLoaderFilesystem, testSnapshotToolFailure, testModuleCheckBasic, testModuleCheckTraits, testModuleCheckWithin, testModuleLinkEval, testModuleLinkPrune, testModuleLinkGenerics, testModuleLinkDrop, testModuleLinkMutual, testModuleLinkRoot, testModuleLinkExtern, testModuleLinkBorrow, testModuleQualifiedGenerics, testModuleAssumptions, testModuleCliFilesystem, testModuleLibraries, testModuleLinkLibCollision]
