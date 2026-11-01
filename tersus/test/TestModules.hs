module TestModules
    ( testModules
    ) where

import Data.List (isInfixOf)

import Modules
import Parse
import Pipeline (compileSource)
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

testModules :: Test
testModules = TestList "testModules" [testPaths, testCanonical, testImports]
