module TestAstData (testAstData, testAstReader) where

import Control.Monad (forM)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, sort)
import System.Directory (listDirectory)
import System.Exit (ExitCode (..))

import qualified Modules as Mod
import qualified PackageCompile as Package
import Parse (fileBody)
import PreludeSource (toolPackageFiles)
import qualified AstData as A
import BuiltinRegistry (builtinRegistry, entryInstances, builtinSymbol)
import Cli (World (..), noWorld, runProgramIn)
import Compile (parseSource)
import Hash (fingerprint)
import qualified Mir as M
import MirData (writeProgram)
import MirOwnership (insertOwnership)
import Native (buildExecutable, cachedProgram, runWithInput)
import Parse (emptyDecls, locating, parseStatementBlockWith)
import Pipeline (nativeProgram, runStatements)
import Seed (cachedSeed, seedHash)
import MirEval (fromMirValue)
import StdLibDefs (stdlibBuiltin)
import Syntax
import TestDataCodec (testDataCodec)
import TestHarness
import TestNative (clangAvailable, runExecutableBytes)
import TypeCheck (Elaborated (..), elaborate)
import Types
import Utils

readerPath :: FilePath
readerPath = "examples/ast_reader/ast_reader.tersus"

corpus :: IO [(String, Result [Statement] String)]
corpus = do
    paths <- concat <$> mapM files ["examples", "examples/rejected", "lib"]
    fromFiles <- mapM (\p -> (,) p <$> readFile p) paths
    let packages = ["examples/parser/parser.tersus", readerPath]
        packageTrees entry = case Mod.loadFromEntry (Mod.resolverFromFiles toolPackageFiles) entry of
            Left err -> [(entry, Error err)]
            Right (Mod.PackageResult pkg) -> [(Mod.loadedFilePath file, Ok (fileBody (Mod.loadedParsed file))) | modu <- Mod.packageModules pkg, file <- Mod.loadedModuleFiles modu]
            Right _ -> [(entry, Error "AST corpus tool is not a package")]
    pure ([(path, parsed source) | (path, source) <- fromFiles ++ generated] ++ concatMap packageTrees packages)
  where
    files dir = map ((dir ++ "/") ++) . filter (isSuffixOf ".tersus") . sort <$> listDirectory dir
    generated =
        [ ("generated forward call", "fn a(n: Int) -> Int { return b(n); }; fn b(n: Int) -> Int { return n; }; return a(5);")
        , ("generated validation refusal", "affirm false; return 2;")
        , ("generated UTF-8", "naïve = 3; café = naïve + 1; return café;")
        , ("generated maximum integer literal", "return 9223372036854775807;")
        ]

parsed :: String -> Result [Statement] String
parsed source = case parseSource source of
    Ok ss -> Ok ss
    Error _ -> case parseStatementBlockWith (locating emptyDecls) source of
        Left e -> Error (show e)
        Right (ss, _) -> Ok ss

dataParsed :: [Statement] -> String
dataParsed ss = case A.writeParsed ss of
    Ok text -> text
    Error e -> error e

dataElaborated :: Elaborated -> String
dataElaborated tree = case A.writeElaborated tree of
    Ok text -> text
    Error e -> error e

writerLimits :: TestResult
writerLimits = firstFailure
    [ rejected (A.writeParsed [StructDef "TooBig" [] [("x", TArrayOf TInt (SizeConst (2 ^ (63 :: Int))))] []])
    , rejected (A.writeParsed [StructDef "TooSmall" [] [("x", TArrayOf TInt (SizeConst (negate (2 ^ (63 :: Int)) - 1)))] []])
    , rejected (A.writeElaborated (Elaborated [] [TWord True 64]))
    , rejected (A.writeParsed [StructDef "TooLong" [] [("x", TNamed (replicate 1000000 'a') [])] []])
    ]
  where
    rejected (Error _) = Nothing
    rejected (Ok _) = Just "writer silently accepted unsupported type data"

roundTrip :: [Statement] -> TestResult
roundTrip ss = case A.readParsed (dataParsed ss) of
    Error e -> Just e
    Ok back
        | show ss /= show back -> Just "syntax or builtin metadata changed"
        | dataParsed ss /= dataParsed back -> Just "reserialization changed"
        | otherwise -> Nothing

elaboratedRoundTrip :: Elaborated -> TestResult
elaboratedRoundTrip e = case A.readElaborated (dataElaborated e) of
    Error err -> Just err
    Ok back
        | show e /= show back -> Just "elaborated syntax, occurrence types or builtin metadata changed"
        | dataElaborated e /= dataElaborated back -> Just "elaborated reserialization changed"
        | otherwise -> Nothing

knownParserRejection :: String -> String -> Bool
knownParserRejection path message =
    path == "examples/rejected/for_assigns_counter.tersus"
        && "The body of a for loop cannot assign its loop variable i" `isInfixOf` message

corpusHaskell :: IO TestResult
corpusHaskell = do
    sources <- corpus
    pure $ firstFailure
        [ prefix name $ case tree of
            Error e -> if knownParserRejection name e then Nothing else Just e
            Ok ss -> firstFailure [roundTrip ss, case elaborate ss of
                Error _ -> Nothing
                Ok e -> elaboratedRoundTrip e]
        | (name, tree) <- sources
        ]

toolElaborated :: FilePath -> Result [Elaborated] String
toolElaborated entry = case Mod.loadFromEntry (Mod.resolverFromFiles toolPackageFiles) entry of
    Left err -> Error err
    Right (Mod.PackageResult pkg) -> Package.compileModules pkg `bindResult` \compiled ->
        Ok (map Package.compiledElaborated (Package.compiledModules compiled))
    Right _ -> Error "AST corpus tool is not a package"

packageElaboratedRoundTrips :: IO TestResult
packageElaboratedRoundTrips = pure $ firstFailure
    [case toolElaborated entry of
        Error err -> Just err
        Ok modules -> firstFailure (map elaboratedRoundTrip modules)
    | entry <- [readerPath, "examples/parser/parser.tersus"]]

nativeElaboratedPackages :: IO TestResult
nativeElaboratedPackages = withAstReader $ \exe -> do
    results <- forM [readerPath, "examples/parser/parser.tersus"] $ \entry -> case toolElaborated entry of
        Error err -> pure (Just err)
        Ok modules -> firstFailure <$> mapM (nativeText exe . dataElaborated) modules
    pure (firstFailure results)

firstFailure :: [TestResult] -> TestResult
firstFailure [] = Nothing
firstFailure (Nothing : xs) = firstFailure xs
firstFailure (e : _) = e

prefix :: String -> TestResult -> TestResult
prefix n = fmap ((n ++ ": ") ++)

proofs :: [VariableProof]
proofs = [ATerm "a", CTerm (VInt 8), FApp (ATerm "f") [ATerm "x", BVar "i"], Forall "i" [ATerm "guard"] (BVar "i"), BVar "i"]

validations :: [ValidationStatement]
validations = [ProofAssert (head proofs), AssignProofVar "proof" (Var "a"), Assume (last proofs)] ++ map Rewrite rules

rules :: [RwRule]
rules = [Refl (head proofs), Eval "x", EvalAll, CheckGtZero (head proofs), CheckRel (head proofs), UserRewrite "rule" proofs]

types :: [Type]
types =
    [ TInt, TByte, TBool, TList TBool, TArrayOf TInt (SizeConst 3), TBox (TArrayOf TByte SizeAny)
    , TFn [TRef TInt, TMutRef TByte] TBool, TNamed "Packet" [ArgType (TList (TParam "T")), ArgSize (SizeParam "n")]
    , TVariant "E::V", TVar 9, TForall ["n"] ["T"] (TNamed "Pair" [ArgType (TParam "T"), ArgSize (SizeVar 7)])
    , TParam "T", TAddr TByte, TBlock TInt, TUninit (TList TInt), TRef TBool, TMutRef TInt
    ] ++ [TWord s b | (s, b) <- [(True, 8), (True, 16), (True, 32), (False, 16), (False, 32)]]

signature :: Signature
signature = Signature types (TRef TInt) ["n"] ["T"] ["out"] ["input"]

builtins :: [BuiltinFunct]
builtins = concatMap entryInstances builtinRegistry ++
    [ Ctor "Packet" [ArgType (TNamed "Inner" [ArgType TInt]), ArgSize (SizeConst 4), ArgSize SizeAny, ArgSize (SizeParam "n"), ArgSize (SizeVar 7)] ["field"]
    , Field Nothing "field", Field (Just "Packet") "field", Is "E::V", Project "E::V" "field", Cast "E::V"
    ] ++ map Rel [Eq, NotEq, Lt, Gt, LtEq, GtEq]

functionValue :: FunctBody -> Value
functionValue body = VFunct ["input", "other"] validations (reverse validations) body proofs

values :: [Value]
values =
    [ VInt (-9223372036854775808), VInt 9223372036854775807, VInt (10 ^ (1200 :: Int)), VList [VInt 1, VBool False]
    , VBool True, VBool False, VData "D" [("field", VList [VInt 3])], VFnRef "function"
    , functionValue (NativeFunct signature (Just (Recursing (Just (Counting (Var "n"))))) [Return (Var "input")])
    ] ++ map (functionValue . BuiltinFunct) builtins ++ map stdlibBuiltin builtins

fixtures :: [Statement]
fixtures =
    [ Assign "x" (Val (VInt 1)), AssignDeref (Var "p") (Val (VInt 2)), Let "y" (Var "x"), Return (F (Var "f") [Var "x"])
    , StructDef "Packet" ["T", "n"] [("field", t) | t <- types] validations
    , EnumDef "E" [("E::V", [("field", TInt)]), ("E::Empty", [])]
    , AxiomDef "axiom" ["x"] validations validations, ProofDef "proof" ["x"] validations validations validations
    , Block [Mark 4 8, Dissolve "x"], If (Val (VBool True)) [] [Return (Val (VInt 1))]
    , TraitDef "Trait" ["T"] [TraitFn "method" ["self"] signature validations validations]
    , ImplDef Nothing [] "Packet" TInt [] [], ImplDef (Just "Trait") [ArgType TBool] "Packet" (head types) [("T", "Trait", types)] [Return (Var "self")]
    , BoundedDef [("T", "Trait", types)] (Assign "f" (Val (functionValue (NativeFunct signature Nothing []))))
    , Mark (-1) 9223372036854775807, CopyDef "Packet", LinearDef "Permit", ExternDef "write", DropDef "Packet", Dissolve "p"
    ] ++ map (Return . Val) values ++ map ValidationStatement validations ++
    [While (Val (VBool True)) validations t [] | t <- Nothing : map Just [Shrinks (Var "n"), Counting (Var "n"), Parts (Var "tree"), MayDiverge, Recursing Nothing, Recursing (Just MayDiverge)]]

metadata :: TestResult
metadata =
    let a = VFunct ["x"] [ProofAssert (ATerm "kept")] [] (BuiltinFunct Plus) [ATerm "export"]
        b = VFunct [] [] [] (BuiltinFunct Plus) []
     in if a /= b || show a == show b then Just "fixture does not exercise hidden metadata" else roundTrip [Return (Val a)]

small :: [Statement]
small = [Mark 2 3, Return (F (Val (builtinSymbol Plus)) [Val (VInt 7), Val (VInt 2)])]

deep :: [Statement]
deep =
    [ Return (foldr (\_ e -> F (Var "f") [e]) (Val (VInt 0)) [1 .. 2048 :: Int])
    , ValidationStatement (ProofAssert (foldr (\_ p -> FApp (ATerm "f") [p]) (ATerm "x") [1 .. 2048 :: Int]))
    ]

longNames :: [Statement]
longNames = [Assign (concat (replicate 3000 "café\NUL\n\"\\𐀀")) (Var ""), Return (Val (VFnRef "λ☃"))]

refusals :: [(String, String, String)]
refusals = structural ++ mutations
  where
    header = "tersus-ast 1 parsed\n"
    empty = dataParsed []
    named = dataParsed [Return (Var "NAME")]
    marked = dataParsed [Mark 1 2]
    typed = dataParsed [StructDef "Holder" [] [("x", TFn [TInt] TInt)] []]
    zeroArgs = dataParsed [StructDef "Holder" [] [("x", TFn [] TInt)] []]
    sized = dataParsed [Return (Val (builtinSymbol (Ctor "C" [ArgSize (SizeConst 4)] [])))]
    integerValue = dataParsed [Return (Val (VInt 7))]
    booleanValue = dataParsed [Return (Val (VBool True))]
    relationValue = dataParsed [Return (Val (builtinSymbol (Rel Eq)))]
    primitiveValue = dataParsed [Return (Val (builtinSymbol Plus))]
    ifControl = header ++ "VBool true\nVal 0\nStatementsEnd\nStatementsEnd\nIf 1 2 3\nStatementsEnd\nStatementsCons 4 5\nroot 6\n"
    ifAlias = header ++ "VBool true\nVal 0\nStatementsEnd\nIf 1 2 2\nStatementsEnd\nStatementsCons 3 4\nroot 5\n"
    structural =
        [ ("missing header", empty, "")
        , ("unknown version", empty, change "tersus-ast 1" "tersus-ast 2" empty)
        , ("unknown stage", empty, change "parsed" "unknown" empty)
        , ("missing root", empty, unlines (init (lines empty)))
        , ("unknown node", empty, change "StatementsEnd" "Unknown" empty)
        , ("blank record", empty, change "StatementsEnd" "\nStatementsEnd" empty)
        , ("trailing record", empty, empty ++ "NameEnd\n")
        , ("trailing blank", empty, empty ++ "\n")
        , ("extra root token", empty, change "root 0" "root 0 extra" empty)
        , ("extra node token", empty, change "StatementsEnd" "StatementsEnd 0" empty)
        , ("dangling root", empty, change "root 0" "root 9" empty)
        , ("wrong root kind", empty, change "StatementsEnd" "NameEnd" empty)
        , ("unreachable record", empty, header ++ "NameEnd\nStatementsEnd\nroot 1\n")
        , ("If same-node branch alias without orphan", ifControl, ifAlias)
        ]
    mutations =
        [ fault "parenthesized root" empty "root 0" "root (0)"
        , fault "parenthesized overflowing root" empty "root 0" "root (18446744073709551616)"
        , fault "parenthesized number" marked "Mark 1 2" "Mark (1) 2"
        , fault "malformed integer" marked "Mark 1 2" "Mark 1e2 2"
        , fault "overflow" marked "Mark 1 2" "Mark 9223372036854775808 2"
        , fault "parenthesized reference" named "Var 2" "Var (2)"
        , fault "parenthesized overflowing reference" named "Var 2" "Var (18446744073709551618)"
        , fault "dangling reference" named "Var 2" "Var 99"
        , fault "forward reference" named "Var 2" "Var 4"
        , fault "wrong reference kind" named "Var 2" "Var 0"
        , fault "cycle" named "NamePart \"NAME\" 1" "NamePart \"NAME\" 2"
        , fault "bad escape" named "\"NAME\"" "\"\\q\""
        , fault "short escape" named "\"NAME\"" "\"\\xA\""
        , fault "invalid UTF-8" named "\"NAME\"" "\"\\xFF\""
        , fault "overlong UTF-8" named "\"NAME\"" "\"\\xC0\\xAF\""
        , fault "surrogate UTF-8" named "\"NAME\"" "\"\\xED\\xA0\\x80\""
        , fault "truncated UTF-8" named "\"NAME\"" "\"\\xF0\\x90\""
        , fault "missing quote" named "\"NAME\"" "\"NAME"
        , fault "missing separator" named "\"NAME\" 1" "\"NAME\"1"
        , fault "parenthesized count" typed "Type fn 1 int int" "Type fn (1) int int"
        , fault "parenthesized overflowing count" typed "Type fn 1 int int" "Type fn (18446744073709551617) int int"
        , fault "negative count" zeroArgs "Type fn 0 int" "Type fn -1 int"
        , fault "truncated type" typed "Type fn 1 int int" "Type fn 2 int int"
        , fault "unknown type" typed "Type fn 1 int int" "Type fn 1 text int"
        , fault "parenthesized size" sized "Size c 4" "Size c (4)"
        , fault "size overflow" sized "Size c 4" "Size c 9223372036854775808"
        , fault "malformed size" sized "Size c 4" "Size c 4x"
        , fault "unknown size" sized "Size c 4" "Size unknown"
        , fault "literal is not decimal" integerValue "\"7\"" "\"1x\""
        , fault "unknown builtin" primitiveValue "Primitive \"Plus\"" "Primitive \"bogus\""
        , fault "bad boolean" booleanValue "VBool true" "VBool yes"
        , fault "bad relation" relationValue "Rel Eq" "Rel bogus"
        , fault "record over limit" named "\"NAME\"" ('"' : replicate 1000000 'a' ++ "\"")
        ]
    fault label control old new = (label, control, change old new control)

change :: String -> String -> String -> String
change old new = go
  where
    go text | old `isPrefixOf` text = new ++ drop (length old) text
    go (c : cs) = c : go cs
    go [] = error ("missing mutation target: " ++ old)

haskellAccepted :: String -> TestResult
haskellAccepted s = case A.readParsed s of
    Error e -> Just ("control rejected: " ++ e)
    Ok _ -> Nothing

haskellRefused :: String -> TestResult
haskellRefused s = case A.readParsed s of
    Error _ -> Nothing
    Ok _ -> Just "accepted malformed AST"


interpreted :: [Statement] -> [String] -> IO TestResult
interpreted ss args = do
    compiled <- programFromFile readerPath
    pure $ case compiled `bindResult` runProgramIn noWorld{worldInput = dataParsed ss, worldArgs = args} of
        Error e -> Just e
        Ok ((out, err), _) ->
            let output = if args == ["count"] then out ++ "\n" else out
             in if null err then checkOutput ss args output else Just err

checkOutput :: [Statement] -> [String] -> String -> TestResult
checkOutput ss [] out = case A.readParsed out of
    Error e -> Just e
    Ok back -> firstFailure [testAssertEq (show back) (show ss), testAssertEq out (dataParsed ss)]
checkOutput ss ["count"] out =
    let text = dataParsed ss
     in testAssertEq out (text ++ show (length text) ++ "\n")
checkOutput _ _ out = case A.readParsed out of
    Error e -> Just e
    Ok back -> case runStatements back of
        Error e -> Just e
        Ok result -> testAssertEq (fmap fromMirValue result) (Just (VInt 5))

withAstReader :: (FilePath -> IO TestResult) -> IO TestResult
withAstReader use = do
    available <- clangAvailable
    if not available
        then putStrLn "[SKIP] native AST reader: clang is unavailable" >> pure Nothing
        else do
            files <- Mod.snapshotFromFilesystem readerPath
            checked <- programFromFiles readerPath files
            seed <- cachedSeed
            case (checked, seed) of
                (Error e, _) -> pure (Just e)
                (_, Error e) -> pure (Just e)
                (Ok program, Ok compiler) -> do
                    let native = insertOwnership (nativeProgram program)
                        dataText = writeProgram native
                        build output = do
                            ir <- runWithInput compiler dataText
                            case ir of
                                Error e -> pure (Error e)
                                Ok text -> buildExecutable output text
                    built <- cachedProgram "test-ast-reader" (fingerprint [packageCacheInput readerPath files, dataText, seedHash]) "the validated AST reader" build
                    case built of
                        Error e -> pure (Just e)
                        Ok exe -> use exe

nativeText :: FilePath -> String -> IO TestResult
nativeText exe text = do
    (code, out, err) <- runExecutableBytes exe [] text
    pure $ if code == ExitSuccess && null err && out == text then Nothing else Just ("exit " ++ show code ++ ", " ++ take 200 err ++ ", wrote " ++ show (length out) ++ " for " ++ show (length text))

nativeCorpus :: IO TestResult
nativeCorpus = withAstReader $ \exe -> do
    sources <- corpus
    results <- forM sources $ \(name, tree) -> case tree of
        Error e -> pure (if knownParserRejection name e then Nothing else Just (name ++ ": " ++ e), 0 :: Int, 0 :: Int)
        Ok ss -> do
            p <- nativeText exe (dataParsed ss)
            (e, count) <- case elaborate ss of
                Error _ -> pure (Nothing, 0)
                Ok tree -> do
                    result <- nativeText exe (dataElaborated tree)
                    pure (result, 1)
            pure (prefix name (firstFailure [p, e]), count, 1)
    extra <- mapM (nativeText exe . dataParsed) [small, fixtures, deep, longNames]
    let parsedCount = sum [n | (_, _, n) <- results]
    putStrLn ("AST native corpus: " ++ show (length sources) ++ " sources, " ++ show parsedCount ++ " parsed, " ++ show (sum [n | (_, n, _) <- results]) ++ " elaborated wrappers, " ++ show (length sources - parsedCount) ++ " parser-rejected, 4 constructor/depth/name fixtures")
    pure (firstFailure ([result | (result, _, _) <- results] ++ extra))

nativeRefusals :: IO TestResult
nativeRefusals = withAstReader $ \exe -> do
    results <- forM refusals $ \(name, control, text) -> do
        accepted <- nativeText exe control
        (code, out, err) <- runExecutableBytes exe [] text
        let rejected = if code == ExitSuccess && out == "1\n" && not (null err) then Nothing else Just ("did not refuse: " ++ show (code, take 200 out, take 200 err))
        pure (prefix name (firstFailure [accepted, rejected]))
    pure (firstFailure results)

nativeCount :: IO TestResult
nativeCount = withAstReader $ \exe -> do
    results <- forM [small, fixtures, deep, longNames] $ \ss -> do
        (code, out, err) <- runExecutableBytes exe ["count"] (dataParsed ss)
        pure $ if code == ExitSuccess && null err then checkOutput ss ["count"] out else Just ("count failed: " ++ show (code, take 200 err))
    pure (firstFailure results)

nativeMutation :: IO TestResult
nativeMutation = withAstReader $ \exe -> do
    (code, out, err) <- runExecutableBytes exe ["mutate"] (dataParsed small)
    pure $ if code == ExitSuccess && null err && out /= dataParsed small then checkOutput small ["mutate"] out else Just ("mutation failed: " ++ show (code, take 200 err))

testAstData :: Test
testAstData = TestList "testAstData"
    [ testDataCodec
    , testCase "checked writer refuses unsupported numeric and record sizes" writerLimits
    , testCase "all syntax constructors and builtins" (roundTrip fixtures)
    , testCase "builtin Eq hides metadata but serialization preserves it" metadata
    , testCase "elaborated wrapper preserves occurrence types" (elaboratedRoundTrip (Elaborated fixtures types))
    , testCase "deep expression arena" (roundTrip deep)
    , testCase "long UTF-8 names are chunked" (firstFailure [roundTrip longNames, testAssertTrue (all ((< 10000) . length) (lines (dataParsed longNames)))])
    , TestList "malformed protocol" [testCase n (firstFailure [haskellAccepted control, haskellRefused bad]) | (n, control, bad) <- refusals]
    , TestCase "packaged tools retain elaborated AST and occurrence types" packageElaboratedRoundTrips
    , TestCase "whole parsed and elaborated source corpus" corpusHaskell
    ]

testAstReader :: Test
testAstReader = TestList "testAstReader"
    [ TestCase "interpreted round trip" (interpreted small [])
    , TestCase "interpreted UTF-8 names" (interpreted [Assign "café" (Var "λ\NUL\n\\\"")] [])
    , TestCase "interpreted exact printed byte count" (interpreted small ["count"])
    , TestCase "interpreted semantic mutation" (interpreted small ["mutate"])
    , TestCase "native exact printed byte counts" nativeCount
    , TestCase "native malformed protocol" nativeRefusals
    , TestCase "native semantic mutation" nativeMutation
    , TestCase "packaged elaborated tools native round trip" nativeElaboratedPackages
    , TestCase "whole corpus native round trip" nativeCorpus
    ]
