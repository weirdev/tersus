module TestCanonicalAst (testCanonicalAst, canonicalSources) where

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified AstData as A
import qualified Parse
import Syntax
import Types
import Utils
import TestHarness
import TypeCheck (Elaborated(..), elaborate, elaborateWith, emptyImportEnv)
import qualified MirLower
import qualified Interface
import Modules (ModuleId(..))
import qualified ValidatorNative as V
import qualified TersusParser
import qualified MirHousekeeping as H
import qualified Native
import MirData (writeProgram)
import Seed (emitterHash)
import Hash (fingerprint)
import System.Exit (ExitCode(..))

canonicalSources :: [String]
canonicalSources =
    [ "struct G { n: Int }; fn field(g: &G) -> Int borrowed from g { return g.n; };"
    , "struct G { n: Int }; trait Field { fn field(self: &Self) -> Int borrowed from self; };"
    , "fn choose<T>(a: &T, b: &T, first: Bool) -> T borrowed from (a, b) { if first { return a; }; return b; };"
    ]

testCanonicalAst :: Test
testCanonicalAst = TestList "testCanonicalAst" $
    [ testCase ("source origin roundtrip " ++ show i) $ parsed source `bindTest` \body -> roundtrip body
    | (i, source) <- zip [0 :: Int ..] canonicalSources
    ] ++
    [ testCase "one AST schema transports projection and borrowed origins together" (roundtrip projected)
    , testCase "elaborated envelope retains StructSpec metadata" $ case A.writeElaborated (Elaborated projected [TInt]) `bindResult` A.readElaborated of
        Error err -> Just err
        Ok back -> testAssertEq (show back) (show (Elaborated projected [TInt]))
    , testCase "ordinary authored declarations do not acquire projection metadata" $ parsed "struct List { n: Int }; struct Box { n: Int };" `bindTest` \body ->
        testAssertEq [structProjection spec | StructDef _ _ _ spec <- body] [Nothing, Nothing]
    , testCase "unsupported projection on an unused generic declaration is not ignored by native validation" $ case elaborate projected `bindResult` MirLower.lowerElaborated `bindResult` V.validateCompiledUncached of
        Error err | "checked declaration-backed value projection" `isInfixOf` err -> Nothing
        other -> Just ("Expected projection rejection, got " ++ show other)
    , testCase "unsupported projection survives the checked module interface" $ case elaborateWith emptyImportEnv projected of
        Error err -> Just err
        Ok (Elaborated typed _, state) -> case Interface.extractLibInterface (ModuleId "tersuslib" (Just "fixture")) projected typed state of
            Error err -> Just err
            Ok iface -> testAssertTrue (maybe False ((/= Nothing) . structProjection) (Map.lookup "Prefix" (Interface.ifInvariants iface)))
    ] ++
    [ testCase label $ case A.readParsed bytes of Error _ -> Nothing; Ok _ -> Just "malformed canonical AST accepted"
    | (label, bytes) <- malformed
    ] ++
    [ TestCase ("native/bootstrap exact origin AST " ++ show i) $ do
        actual <- TersusParser.runParserTool False [source]
        pure $ case parsed source `bindResult` A.writeParsed of
            Error err -> Just err
            Ok expected -> case actual of
                Left err -> Just err
                Right bytes -> testAssertEq bytes expected
    | (i, source) <- zip [0 :: Int ..] canonicalSources
    ] ++ [TestCase "native AST reader preserves both metadata channels and rejects malformed layouts" $ case H.toolOwnedProgram "examples/ast_reader/ast_reader.tersus" of
        Error err -> pure (Just err)
        Ok program -> do
            let input = writeProgram program
            executable <- Native.cachedProgram "canonical-ast-reader" (fingerprint [emitterHash, input]) "canonical AST reader" $ \path -> do
                emitter <- H.cachedEmitter
                case emitter of
                    Error err -> pure (Error err)
                    Ok compiler -> do
                        ir <- Native.runWithInput compiler input
                        case ir of Error err -> pure (Error err); Ok bytes -> Native.buildExecutable path bytes
            case executable of
                Error err -> pure (Just err)
                Ok path -> do
                    good <- Native.runWithInputFull path encoded
                    bad <- mapM (Native.runWithInputFull path . snd) malformed
                    pure (testAssertEq good (ExitSuccess, encoded, "") <> mconcat [if "not the AST as data" `isInfixOf` errors && output /= encoded then Nothing else Just "native reader did not reject malformed schema" | (_, output, errors) <- bad])
    ]
  where
    projected =
        [ StructDef "Prefix" ["T"] [("blk", TBlock (TParam "T")), ("len", TInt)] (StructSpec [] (Just (InitializedPrefix "blk" "len")))
        , StructDef "Payload" ["T"] [("blk", TBlock (TParam "T"))] (StructSpec [] (Just (StoredPayload "blk")))
        , Assign "borrowed" (Val (VFunct ["x"] [] [] (NativeFunct (Signature [TRef TInt] TInt [] [] [] [BorrowedOrigin "x"]) Nothing [Return (Var "x")]) []))
        ]
    parsed source = case Parse.parseStatementBlock source of Left err -> Error (show err); Right body -> Ok body
    bindTest (Error err) _ = Just err
    bindTest (Ok value) use = use value
    roundtrip body = case A.writeParsed body `bindResult` A.readParsed of Error err -> Just err; Ok back -> testAssertEq back body
    encoded = case A.writeParsed projected of Error err -> error err; Ok bytes -> bytes
    mixedOrigins = case A.writeParsed [Assign "f" (Val (VFunct ["a", "b"] [] [] (NativeFunct (Signature [TRef TInt, TRef TInt] TInt [] [] [] [BorrowedOrigin "a", ReferenceOrigin "b"]) Nothing [Return (Var "a")]) []))] of
        Error err -> error err
        Ok bytes -> bytes
    malformed =
        [ ("old header rejected", replace "tersus-ast 2 parsed" "tersus-ast 1 parsed" encoded)
        , ("future header rejected", replace "tersus-ast 2 parsed" "tersus-ast 3 parsed" encoded)
        , ("unknown projection tag rejected", replace "\"prefix\"" "\"unknown\"" encoded)
        , ("projection arity rejected", replace "\"prefix\"" "\"payload\"" encoded)
        , ("mixed result origin modes rejected", mixedOrigins)
        , ("unknown origin tag rejected", replace "BorrowedOriginsCons" "UnknownOriginsCons" encoded)
        , ("origin list cannot be substituted by a Names list", replace "OriginsEnd" "NamesEnd" encoded)
        , ("old four-reference struct layout rejected", unlines [if "StructDef " `isPrefixOf` line then unwords (init (words line)) else line | line <- lines encoded])
        ]
    replace old new text
        | old `isPrefixOf` text = new ++ drop (length old) text
        | otherwise = case text of c : rest -> c : replace old new rest; [] -> error ("missing mutation target " ++ old)
