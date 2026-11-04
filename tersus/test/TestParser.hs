module TestParser (testParser) where

import Control.Monad (forM)
import Control.Exception (evaluate)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import System.IO.Unsafe (unsafePerformIO)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, sort)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>), takeFileName)
import System.Exit (ExitCode (..))

import qualified AstData as A
import qualified Mir as M
import qualified Data.Map as Map
import qualified Compile
import qualified TersusParser
import MirHousekeeping (cachedEmitter)
import ParsedFile (Decls, ParsedFile, emptyDecls, fileBody, locating)
import qualified FileParserProtocol as File
import PreludeSource (toolPackageFiles)
import qualified Modules
import qualified SourceParse
import qualified ParserSeed
import Syntax (Expression (..), Statement (..), Value (..))
import Types (Type (..))
import qualified TestParserFragments as Fragment
import TestHarness
import Utils

seedParsed :: String -> Either String [Statement]
seedParsed source = case Compile.parseSource source of
    Ok statements -> Right statements
    Error e -> Left e

seedPlainParsed :: String -> Either String [Statement]
seedPlainParsed source = case ParserSeed.parseFileWith emptyDecls source of
    Left e -> Left e
    Right (parsed, _) -> Right (fileBody parsed)

writeData :: Either String [Statement] -> Either String String
writeData (Left e) = Left e
writeData (Right statements) = case A.writeParsed statements of
    Ok text -> Right text
    Error e -> Left e

seedData :: String -> Either String String
seedData = writeData . seedParsed

seedPlainData :: String -> Either String String
seedPlainData = writeData . seedPlainParsed

-- The same program as the pipeline parses it: the probe, the libraries it chooses, then the
-- source located, all through the tool
tersusData :: String -> IO (Either String String)
tersusData = TersusParser.toolParseSource

-- The source alone, unlocated, through the interpreted tool: the shape of the generated snippets
tersusPlain :: String -> IO (Either String String)
tersusPlain source = TersusParser.runParserTool False [source]


compareWith :: (String -> Either String String) -> (String -> IO (Either String String)) -> String -> IO TestResult
compareWith seed tool source = do
    tersus <- tool source
    pure $ case (seed source, tersus) of
        (Left e, _) | "Parser tool failure:" `isPrefixOf` e -> Just e
        (_, Left e) | "Parser tool failure:" `isPrefixOf` e -> Just e
        (Right expected, Right actual) -> case A.readParsed actual of
            Error e -> Just ("native stdout is invalid AstData: " ++ e)
            Ok parsed -> case A.writeParsed parsed of
                Error e -> Just e
                Ok canonical -> firstFailure [sameData "noncanonical native stdout" canonical actual, sameData "P0/P1 AST mismatch" expected actual]
        (Left message, Left tersusMessage) ->
            case [s | s <- knownSubstrings, s `isInfixOf` message] of
                [] -> Nothing
                s : _
                    | s `isInfixOf` tersusMessage -> Nothing
                    | otherwise -> Just ("the Tersus parser's message does not name the reason: " ++ take 200 tersusMessage)
        (Right _, Left e) -> Just ("the Tersus parser refused what P0 accepts: " ++ take 200 e)
        (Left e, Right _) -> Just ("the Tersus parser accepted what P0 refuses: " ++ take 200 e)

sameData :: String -> String -> String -> TestResult
sameData label expected actual
    | expected == actual = Nothing
    | otherwise = case [(n, want, got) | (n, want, got) <- zip3 [1 :: Int ..] (lines expected) (lines actual), want /= got] of
        (n, want, got) : _ -> Just (label ++ " at record " ++ show n ++ ": expected " ++ take 200 want ++ "; got " ++ take 200 got)
        [] -> Just (label ++ ": record counts " ++ show (length (lines expected), length (lines actual)))

compareSource :: (String -> IO (Either String String)) -> String -> IO TestResult
compareSource = compareWith seedData

knownSubstring :: String
knownSubstring = "The body of a for loop cannot assign its loop variable"

knownSubstrings :: [String]
knownSubstrings =
    [ knownSubstring
    , "import statements must come before any declaration in a file"
    ]

corpusPaths :: IO [FilePath]
corpusPaths = (++) <$> files "examples" <*> files "lib"
  where
    files dir = do
        entries <- sort <$> listDirectory dir
        fmap concat $ forM entries $ \entry -> do
            let path = dir </> entry
            directory <- doesDirectoryExist path
            if directory then files path else pure [path | ".tersus" `isSuffixOf` entry]

corpusParity :: IO TestResult
corpusParity = do
    paths <- corpusPaths
    sources <- forM paths $ \path -> do source <- readFile path; pure (path, source)
    let resolver = Modules.resolverFromFiles (sources ++ toolPackageFiles)
    emitter <- comparePreparedPackage resolver emitterCorpusEntry
    results <- forM sources $ \(path, source) -> do
        putStrLn ("Native corpus file: " ++ path)
        result <- case Modules.discoverEntry resolver path of
            Modules.InPackage _ _ | takeFileName path /= "package.tersus" ->
                if path `elem` emitterCorpusFiles
                    then pure (observedSource source emitter)
                    else observedSource source <$> comparePreparedPackage resolver path
            _ -> do
                ast <- compareSource tersusData source
                wire <- compareFileRecords source
                pure (firstFailure [ast, wire])
        pure (fmap ((path ++ ": ") ++) result)
    putStrLn ("Native corpus parity: " ++ show (length paths) ++ " files, " ++ show (length [e | Just e <- results]) ++ " failures")
    pure (firstFailure results)

emitterCorpusEntry :: FilePath
emitterCorpusEntry = "examples/mir/emit/emit.tersus"

emitterCorpusFiles :: [FilePath]
emitterCorpusFiles = ["examples/mir/emit/" ++ name ++ ".tersus" | name <- ["emit", "types", "values", "operations", "functions", "helpers"]]

observedSource :: String -> ([String], TestResult) -> TestResult
observedSource source (observations, result) = firstFailure
    [ result
    , if source `elem` observations then Nothing else Just "requested corpus source was not observed by the paired P0/P1 parsers"
    ]

comparePreparedPackage :: Modules.Resolver -> FilePath -> IO ([String], TestResult)
comparePreparedPackage resolver path = do
    observations <- newIORef []
    let paired declared source = unsafePerformIO $ do
            seed <- ParserSeed.parseFileNative declared source
            current <- TersusParser.parseFileNative declared source
            let result = case (seed, current) of
                    (Right (a, da), Right (b, db)) -> testAssertEq a b <> testAssertEq (File.writeParsedFile a da) (File.writeParsedFile b db)
                    (Left a, Left b) | not (ParserSeed.toolFailure a || ParserSeed.toolFailure b) -> Nothing
                    (Left e, _) -> Just ("P0 prepared package file: " ++ e)
                    (_, Left e) -> Just ("P1 prepared package file: " ++ e)
            modifyIORef' observations ((source, result) :)
            pure current
        loaded = Modules.loadFromEntryWith paired resolver path
    _ <- evaluate (length (show loaded))
    records <- readIORef observations
    let results = map snd records
    pure (map fst records, firstFailure (case loaded of
        Left e -> Just e : results
        Right (Modules.PackageResult _) -> testAssertTrue (not (null results)) : results
        Right _ -> Just "expected a prepared package" : results))

preparedEmitterHelper :: IO TestResult
preparedEmitterHelper = do
    let helper = "examples/mir/emit/functions.tersus"
        source = "fn answer() -> Int [{ }] [{ }] { return 42; };"
        resolver = Modules.resolverFromFiles
            [ ("examples/mir/package.tersus", "")
            , (emitterCorpusEntry, "import mir::emit::functions { answer }; return answer();")
            , (helper, source)
            ]
    report <- comparePreparedPackage resolver emitterCorpusEntry
    pure $ firstFailure
        [ testAssertTrue (helper `elem` emitterCorpusFiles)
        , observedSource source report
        , testAssertEq (observedSource "fn unseen() -> Int { return 0; };" report)
            (Just "requested corpus source was not observed by the paired P0/P1 parsers")
        ]

{-# NOINLINE recordedFile #-}
recordedFile :: IORef [Either String String] -> (Decls -> String -> IO (Either String (ParsedFile, Decls))) -> Decls -> String -> Either String (ParsedFile, Decls)
recordedFile history parser declared source = unsafePerformIO $ do
    answer <- parser declared source
    let record = case answer of
            Left e -> Left e
            Right (parsed, final) -> case File.writeParsedFile parsed final of
                Error e -> Left (ParserSeed.failure e)
                Ok wire -> Right wire
    modifyIORef' history (record :)
    pure answer

fileRecords :: (Decls -> String -> IO (Either String (ParsedFile, Decls))) -> String -> IO [Either String String]
fileRecords parser source = do
    history <- newIORef []
    let result = SourceParse.parseSourcePartsWith (recordedFile history parser) True source
    _ <- evaluate (length (show result))
    reverse <$> readIORef history

compareFileRecords :: String -> IO TestResult
compareFileRecords source = do
    seed <- fileRecords ParserSeed.parseFileNative source
    current <- fileRecords TersusParser.parseFileNative source
    pure $ firstFailure
        ([Just e | Left e <- seed ++ current, ParserSeed.toolFailure e]
        ++ [testAssertTrue (not (null seed)), testAssertEq current seed])

interpretedSmoke :: IO TestResult
interpretedSmoke = do
    let sources = ["return 1 + 2;", "struct Point { x: Int }; p = Point { x: 2 }; return p.x;", "for i in 0..3 { i = 4; }; return 0;"]
    results <- forM sources $ \source -> compareWith seedPlainData (TersusParser.runParserToolInterpreted False . pure) source
    pure (firstFailure results)

snippets :: [(String, String)]
snippets =
    [ ("integer and arithmetic", "x = 1 + 2 * 3 - 4 / 2 % 3; return x;")
    , ("negative literal", "return -5;")
    , ("maximum integer", "return 9223372036854775807;")
    , ("boolean connectives", "a = true; b = false; return a && !b || a;")
    , ("relations", "return 1 < 2 && 3 >= 4 || 5 = 6 && 7 != 8;")
    , ("list and array literals", "xs = [1, 2, 3]; ys = #[4, 5]; return size(xs);")
    , ("string literal", "s = \"a\\n\\u{e9}\"; return size(s.bytes);")
    , ("tuple literal and destructuring", "(a, b) = (1, 2); return a + b;")
    , ("struct definition and literal", "struct Point { x: Int, y: Int }; p = Point { x: 1, y: 2 }; return p.x;")
    , ("struct update", "struct Point { x: Int, y: Int }; p = Point { x: 1, y: 2 }; q = Point { x: 9, ..p }; return q.y;")
    , ("struct destructuring", "struct Point { x: Int, y: Int }; p = Point { x: 1, y: 2 }; Point { x: a, y: b } = p; return a;")
    , ("enum and match statement", "enum Shape { Circle { r: Int }, Dot }; s = Shape::Circle { r: 3 }; x = 0; match s { Shape::Circle { r: r } => { x = r; }, Shape::Dot => { x = 1; }, }; return x;")
    , ("match assignment", "enum Shape { Circle { r: Int }, Dot }; s = Shape::Dot; x = match s { Shape::Circle { r: r } => r, Shape::Dot => 7, }; return x;")
    , ("match return", "enum Shape { Circle { r: Int }, Dot }; fn area(s: Shape) -> Int { return match s { Shape::Circle { r: r } => r, Shape::Dot => 0, }; }; return area(Shape::Dot);")
    , ("for range", "total = 0; for i in 0..10 { total = total + i; }; return total;")
    , ("for elements", "xs = [1, 2]; total = 0; for x in xs { total = total + x; }; return total;")
    , ("for indexed elements", "xs = [1, 2]; total = 0; for i, x in xs { total = total + i + x; }; return total;")
    , ("for assigns its variable", "for i in 0..3 { i = 9; }; return 0;")
    , ("while with invariant and shrinks", "i = 0; while i < 3 [{ affirm i >= 0; }] shrinks 3 - i { i = i + 1; }; return i;")
    , ("while may diverge", "while true ~ { return 1; }; return 0;")
    , ("if else if", "x = 1; if x = 1 { x = 2; } else if x = 2 { x = 3; } else { x = 4; }; return x;")
    , ("function with contract", "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= 0; }] shrinks n { return n; }; return f(1);")
    , ("generic function with bound", "trait Seq { fn size(self: &Self) -> Int [{ }] [{ }]; }; fn g<S: Seq>(x: S) -> Int { return 0; }; return 0;")
    , ("sized generic struct", "struct Packet<n> { body: Array<Int, n> }; p = Packet<3> { body: #[1, 2, 3] }; return 0;")
    , ("trait and impl", "trait T { fn get(self: &Self) -> Int [{ }] [{ }]; }; struct S { x: Int }; impl T for S { fn get(self: &Self) -> Int [{ }] [{ }] { return self.x; }; }; return 0;")
    , ("standard Eq impl", "struct S { x: Int }; impl Eq for S { }; return 0;")
    , ("standard Clone impl", "struct S { x: Int }; impl Clone for S { }; return 0;")
    , ("standard Eq enum impl", "enum E { A { x: Int }, B }; impl Eq for E { }; return 0;")
    , ("method call and field", "struct S { x: Int }; fn get(s: S) -> Int { return s.x; }; s = S { x: 4 }; return get(s);")
    , ("references", "x = 1; r = &x; return *r;")
    , ("deref assignment", "x = 1; r = &mut x; *r = 2; return x;")
    , ("proof statements", "affirm 1 < 2 && 2 < 3; define p = 1; rewrite evalAll; return 0;")
    , ("forall proof", "affirm forall j in 0..3: j >= 0; return 0;")
    , ("axiom and proof definitions", "axiom ax(x) [{ }] [{ affirm x = x; }]; proof pr(x) [{ }] [{ }] { affirm x = x; }; return 0;")
    , ("extern function", "extern fn write(b: Byte) -> Int [{ }] [{ }]; return 0;")
    , ("linear struct", "linear struct Token { x: Int }; return 0;")
    , ("assume statement", "assume 1 < 2; return 0;")
    , ("nested blocks and marks off", "{ x = 1; { y = 2; }; }; return 0;")
    , ("cast and is", "enum E { A { x: Int }, B }; e = E::A { x: 1 }; if e is E::A { return (e as E::A).x; }; return 0;")
    , ("accented and mixed-letter identifier", "éπ中 = 3; return éπ中;")
    , ("CJK identifier", "中文 = 4; return 中文;")
    , ("Unicode letter continuation", "aé9 = 5; return aé9;")
    , ("emoji identifier rejected", "🙂 = 1; return 🙂;")
    , ("Unicode punctuation identifier rejected", "。x = 1; return 。x;")
    , ("combining start rejected", "́x = 1; return 0;")
    , ("combining continuation rejected", "á = 1; return 0;")
    , ("non-ASCII digit continuation rejected", "a١ = 1; return 0;")
    , ("Unicode lower generic constructor name", "struct é { x: Int }; struct Wrap<T> { x: T }; w = Wrap<é> { x: é { x: 1 } }; return 0;")
    , ("Unicode continuation generic constructor name", "struct aé { x: Int }; struct Wrap<T> { x: T }; w = Wrap<aé> { x: aé { x: 1 } }; return 0;")
    , ("underscore identifier rejected", "a_b = 1; return 0;")
    , ("backtick identifier rejected", "`a = 1; return 0;")
    , ("Unicode uppercase type parameter", "fn id<Δ>(x: Δ) -> Δ ~ { return x; }; return id(1);")
    , ("lowercase Unicode escape", "return \"\\u{e9}\\u{1f642}\";")
    , ("uppercase Unicode escape", "return \"\\u{E9}\\u{1F642}\";")
    , ("malformed function field type", "struct S { f: fn Int }; return 0;")
    , ("malformed borrowed function type", "fn f(x: &fn Int) -> Int ~ { return 0; };")
    , ("function type with malformed return", "struct S { f: fn(Int) -> fn Int }; return 0;")
    , ("function value type", "fn apply(f: fn(Int) -> Int, x: Int) -> Int { return f(x); }; return 0;")
    , ("qualified impl call", "struct S { x: Int }; impl S { fn get(self: &Self) -> Int [{ }] [{ }] { return self.x; }; }; s = S { x: 1 }; return <S>::get(s);")
    , ("misplaced import", "x = 1; import geo; return x;")
    , ("path literal by suffix", "struct Point { x: Int }; p = geo::Point { x: 1 }; return p.x;")
    , ("two segment type is a variant", "fn f(x: geo::Point) -> Int [{ }] [{ }] { return 1; }; return 0;")
    , ("three segment type is named", "fn f(x: a::b::Point) -> Int [{ }] [{ }] { return 1; }; return 0;")
    , ("generic arguments on a path", "struct Vec<T> { x: T }; fn f(v: geo::Vec<Int>) -> Int [{ }] [{ }] { return 1; }; return 0;")
    , ("match arms written with a path", "enum Shape { Circle { r: Int }, Dot }; s = Shape::Circle { r: 3 }; x = 0; match s { geo::Shape::Circle { r: r } => { x = r; }, geo::Shape::Dot => { x = 1; }, }; return x;")
    , ("bound written with a path", "trait Seq { fn size(self: &Self) -> Int [{ }] [{ }]; }; fn g<S: geo::Seq>(x: S) -> Int [{ }] [{ }] { return 0; }; return 0;")
    , ("qualified call with a path", "struct S { x: Int }; impl S { fn get(self: &Self) -> Int [{ }] [{ }] { return self.x; }; }; s = S { x: 1 }; return <geo::S>::get(s);")
    , ("enum shadowed by an enum", "enum E { A, B }; enum E { C }; e = E::C; return 0;")
    , ("struct shadowed by a struct", "struct S { x: Int }; struct S { y: Int }; s = S { y: 2 }; return s.y;")
    ]

snippetParity :: IO TestResult
snippetParity = do
    results <- forM snippets $ \(name, source) -> do
        plain <- compareWith seedPlainData tersusPlain source
        pure (fmap ((name ++ ": ") ++) plain)
    located <- forM locatedSnippets $ \(name, source) -> do
        result <- compareSource tersusData source
        pure (fmap ((name ++ " (located): ") ++) result)
    pure (firstFailure (results ++ located))

-- The snippets also read with the libraries in front and statement places kept, as the pipeline
-- reads a program: the located readings are the expensive ones for the interpreted tool, so a
-- subset with several statements (where Marks fall) stands for the rest; the whole corpus below
-- is located throughout.
locatedSnippets :: [(String, String)]
locatedSnippets =
    [ ("integer and arithmetic", "x = 1 + 2 * 3 - 4 / 2 % 3; return x;")
    , ("struct definition and literal", "struct Point { x: Int, y: Int }; p = Point { x: 1, y: 2 }; return p.x;")
    , ("enum and match statement", "enum Shape { Circle { r: Int }, Dot }; s = Shape::Circle { r: 3 }; x = 0; match s { Shape::Circle { r: r } => { x = r; }, Shape::Dot => { x = 1; }, }; return x;")
    , ("for range", "total = 0; for i in 0..10 { total = total + i; }; return total;")
    , ("function with contract", "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= 0; }] shrinks n { return n; }; return f(1);")
    , ("trait and impl", "trait T { fn get(self: &Self) -> Int [{ }] [{ }]; }; struct S { x: Int }; impl T for S { fn get(self: &Self) -> Int [{ }] [{ }] { return self.x; }; }; return 0;")
    , ("standard Eq impl", "struct S { x: Int }; impl Eq for S { }; return 0;")
    , ("proof statements", "affirm 1 < 2 && 2 < 3; define p = 1; rewrite evalAll; return 0;")
    , ("generated recursive Eq source positions", "enum Tree { Many { xs: List<Tree> }, Leaf }; impl Eq for Tree { }; return 0;")
    , ("generated recursive Clone source positions", "enum Tree { Many { xs: List<Tree> }, One { child: Box<Tree> }, Leaf }; impl Clone for Tree { }; return 0;")
    , ("import is not linked", "import geo; return 0;")
    , ("imports with alias and names are not linked", "import geo::shapes as G { Circle }; import units; return 0;")
    , ("empty import name list", "import geo { }; return 0;")
    ]

-- A file with imports is parsed whole and then refused as the P0 reading refuses it, in
-- the same words (Compile.parseSourceParts), not by falling back to the P0 parser
importsVerdict :: IO TestResult
importsVerdict = do
    tersus <- TersusParser.toolParseSource "import geo; import geo::Point as P { x }; return 0;"
    pure $ firstFailure
        [ testAssertEq tersus (Left "imports are not linked yet: geo, geo::Point")
        , testAssertEq (seedData "import geo; import geo::Point as P { x }; return 0;") (Left "imports are not linked yet: geo, geo::Point")
        ]


firstFailure :: [TestResult] -> TestResult
firstFailure [] = Nothing
firstFailure (Nothing : xs) = firstFailure xs
firstFailure (e : _) = e

responseVerdicts :: IO TestResult
responseVerdicts = pure $ case A.writeParsed [] of
    Error e -> Just e
    Ok ast -> firstFailure
        [ testAssertEq (TersusParser.parserResponse ExitSuccess ast "") (Right ast)
        , testAssertEq (failed (TersusParser.parserResponse (ExitFailure 9) ast "process failure")) True
        , testAssertEq (failed (TersusParser.parserResponse ExitSuccess (ast ++ "0\n") "")) True
        , testAssertEq (failed (TersusParser.parserResponse ExitSuccess "" "")) True
        , testAssertEq (TersusParser.parserResponse ExitSuccess "1\n" "refused\n") (Left "refused")
        ]
  where
    failed (Left _) = True
    failed _ = False

fragmentEnds :: IO TestResult
fragmentEnds = pure $ firstFailure
    [ testAssertEq (Fragment.parseExpression "1") (Right (Val (VInt 1)))
    , testAssertEq (Fragment.parseExpression "1 // comment") (Right (Val (VInt 1)))
    , testAssertEq (Fragment.parseStatement "return 1") (Right (Return (Val (VInt 1))))
    , testAssertEq (Fragment.parseStatement "return 1 // comment") (Right (Return (Val (VInt 1))))
    , rejectedAt "line 1:2:" (Fragment.parseExpression "1;")
    , rejectedAt "line 1:2:" (Fragment.parseExpression "1; // comment")
    , rejectedAt "line 1:2:" (Fragment.parseExpression "1; 2")
    , rejectedAt "line 1:9:" (Fragment.parseStatement "return 1;")
    , rejectedAt "line 1:9:" (Fragment.parseStatement "return 1; return 2")
    , rejectedAt "line 1:4:" (Fragment.parseExpression "1 +")
    , rejectedAt "line 2:4:" (Fragment.parseExpression "\n1 +")
    ]
  where
    rejectedAt position result = case result of
        Left e | ParserSeed.toolFailure e -> Just e
               | otherwise -> testAssertTrue (position `isPrefixOf` e)
        Right _ -> Just "a strict native fragment accepted trailing input"

constructorConditions :: IO TestResult
constructorConditions = pure $ firstFailure
    [ testAssertEq (Fragment.parseStatementBlock "struct P { x: Int }; if P { }; while P { };")
        (Right [StructDef "P" [] [("x", TInt)] [], If (Var "P") [] [], While (Var "P") [] Nothing []])
    , case Fragment.parseStatementBlock "struct P { x: Int }; if P { }; x =;" of
        Left e | ParserSeed.toolFailure e -> Just e
               | otherwise -> testAssertTrue ("expected a name" `isInfixOf` e && not ("lacks field" `isInfixOf` e))
        Right _ -> Just "a later malformed assignment was accepted"
    ]

noArenaCopies :: IO TestResult
noArenaCopies = do
    emitter <- cachedEmitter
    pure $ case emitter of
        Error e -> Just e
        Ok _ -> case TersusParser.ownedParserProgram of
            Error e -> Just e
            Ok program -> case Map.lookup "nameLedExpr" (M.progFunctions program) of
                Nothing -> Just "nameLedExpr is missing"
                Just fn -> testAssertEq
                    [operand | body <- Map.elems (M.fnBlocks fn), M.Assign _ (M.CopyOf operand) <- M.blockStatements body, operandType fn operand == Just (TNamed "St" [])]
                    []
  where
    operandType fn operand = case operand of
        M.Copy local -> M.localType <$> Map.lookup local (M.fnLocals fn)
        M.Move local -> M.localType <$> Map.lookup local (M.fnLocals fn)
        _ -> Nothing

largeConstructorFallback :: IO TestResult
largeConstructorFallback = pure $ testAssertEq
    (Fragment.parseStatementBlock ("struct P { x: Int };\n" ++ concat ["x" ++ show i ++ " = P;\n" | i <- [0 :: Int .. 1023]]))
    (Right (StructDef "P" [] [("x", TInt)] [] : [Assign ("x" ++ show i) (Var "P") | i <- [0 :: Int .. 1023]]))

testParser :: Test
testParser = TestList "testParser"
    [ TestCase "native stdout roundtrip and exact equality" (compareWith seedPlainData tersusPlain "return 1;\n")
    , TestCase "large located arena exceeds former recursive stack limit" (compareWith seedData tersusData (concat ["x" ++ show i ++ " = " ++ show i ++ ";\n" | i <- [0 :: Int .. 4095]] ++ "return 0;\n"))
    , TestCase "many function-body arenas retain canonical order" (compareWith seedData tersusData (concat ["fn f" ++ show i ++ "() -> Int ~ { return " ++ show i ++ "; };\n" | i <- [0 :: Int .. 255]] ++ "return 0;\n"))
    , TestCase "native response framing and OS failures" responseVerdicts
    , TestCase "native fragments preserve strict ends and original source coordinates" fragmentEnds
    , TestCase "constructor-name conditions retain variable ASTs and later errors" constructorConditions
    , TestCase "diagnostic observation borrows the parser state without copying its arena" noArenaCopies
    , TestCase "many known-constructor variables preserve exact fallback ASTs" largeConstructorFallback
    , TestCase "imports are not linked yet" importsVerdict
    , TestCase "generated snippet parity" snippetParity
    , TestCase "three interpreted smoke programs" interpretedSmoke
    , TestCase "emitter helper corpus uses its program entry and proves requested source observation" preparedEmitterHelper
    , TestCase "whole corpus parity" corpusParity
    ]
