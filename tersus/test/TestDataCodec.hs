module TestDataCodec (testDataCodec) where

import Data.List (sort)
import qualified Modules as Mod
import ParsedFile (fileBody)
import ModuleResolve (canonicalForFile, rewriteFileReferences)
import qualified PackageCompile
import PreludeSource (toolPackageFiles, parserPackageFiles)
import qualified TersusParser
import qualified MirHousekeeping
import MirData (writeProgram)
import Seed (compilerSnapshotHash)
import LlvmRuntime (runtimeSource)
import Hash (fingerprint)
import MirEval (fromMirValue, runProgramEnv, RunEnv (..), Outcome (..))
import Syntax (Value (..))
import TestHarness
import Utils

entries :: [FilePath]
entries =
    [ "lib/ast_reader/ast_reader.tersus"
    , "lib/parser/parser.tersus"
    , "lib/mir/reader/reader.tersus"
    , "lib/mir/mir_reader/mir_reader.tersus"
    , "lib/mir/emit/emit.tersus"
    , "lib/mir/mir_verify/mir_verify.tersus"
    , "lib/mir/mir_erase/mir_erase.tersus"
    ]

sharing :: FilePath -> TestResult
sharing entry = case Mod.loadFromEntry (Mod.resolverFromFiles toolPackageFiles) entry of
    Left err -> Just err
    Right (Mod.PackageResult pkg) ->
        let codecs = [file | modu <- Mod.packageModules pkg, Mod.loadedModuleId modu == Mod.ModuleId "data" (Just "codec"), file <- Mod.loadedModuleFiles modu]
            imported = [ri | modu <- Mod.packageModules pkg, file <- Mod.loadedModuleFiles modu, ri <- Mod.loadedImports file, Mod.resolvedTargetModule ri == Mod.ModuleId "data" (Just "codec")]
            canonical = [canonicalForFile pkg file name | file <- codecs, name <- Mod.loadedDeclNames file, name `elem` ["Token", "Parsed", "Size", "Type"]]
         in if length codecs /= 1 || null imported || sort canonical /= sort ["data$codec$codec$" ++ name | name <- ["Token", "Parsed", "Size", "Type"]]
                then Just "consumer does not use one canonical shared codec"
                else firstFailure [either Just (const Nothing) (rewriteFileReferences pkg file (fileBody (Mod.loadedParsed file))) | modu <- Mod.packageModules pkg, file <- Mod.loadedModuleFiles modu]
    Right _ -> Just "codec consumer is standalone"

codecRun :: String -> (Outcome -> TestResult) -> IO TestResult
codecRun source check = pure $ case Mod.loadFromEntry (Mod.resolverFromFiles (toolPackageFiles ++ [("lib/codec_test/package.tersus", ""), ("lib/codec_test/main.tersus", source)])) "lib/codec_test/main.tersus" of
    Left err -> Just err
    Right (Mod.PackageResult pkg) -> -- (the codec is the compiler's own code, built as the host builds it, not validated)
        case PackageCompile.compileModulesLinked pkg `bindResult` runProgramEnv RunEnv{envArgs = [], envInput = "", envFile = const Nothing} of
        Error err -> Just err
        Ok outcome -> check outcome
    Right _ -> Just "codec fixture is standalone"

readerBounds :: IO TestResult
readerBounds = codecRun (unlines
    [ "import data::codec::codec { parseInt, tokenize, typeAt };"
    , "good = parseInt(\"-9223372036854775808\"); hi = parseInt(\"9223372036854775807\");"
    , "over = parseInt(\"9223372036854775808\"); under = parseInt(\"-9223372036854775809\"); paren = parseInt(\"(1)\");"
    , "escape = tokenize(\"\\\"\\\\x41\\\"\"); bad = tokenize(\"\\\"\\\\xAF\"); lower = tokenize(\"\\\"\\\\xaf\\\"\");"
    , "truncated = tokenize(\"fn 2 int\"); if !truncated.ok || size(truncated.value) <= 0 { return false; }; ty = typeAt(truncated.value, 0);"
    , "return good.ok && good.value = 0 - 9223372036854775807 - 1 && hi.ok && hi.value = 9223372036854775807 && !over.ok && !under.ok && !paren.ok && escape.ok && !bad.ok && !lower.ok && !ty.ok;"
    ]) (\outcome -> testAssertEq (fmap fromMirValue (outValue outcome)) (Just (VBool True)))

writerMetadata :: IO TestResult
writerMetadata = codecRun (unlines
    [ "import data::codec::codec { tokenize, typeAt, printType, printName, printSize, Size };"
    , "tokens = tokenize(\"named \\\"Packet\\\" 2 size p \\\"n\\\" type array byte c 3\");"
    , "if !tokens.ok || size(tokens.value) <= 0 { return 1; }; ty = typeAt(tokens.value, 0); n = printType(ty.value);"
    , "n = printName(\"\\\"\\\\\\n\"); n = printSize(Size::SVar { n: -7 });"
    ]) (\outcome -> firstFailure
        [ testAssertEq (outStdout outcome) " named \"Packet\" 2 size p \"n\" type array byte c 3 \"\\x22\\x5C\\x0A\" v -7"
        , testAssertEq (outStderr outcome) ""
        ])

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [err | Just err <- results] of
    err : _ -> Just err
    [] -> Nothing

testDataCodec :: Test
testDataCodec = TestList "testDataCodec"
    [ TestList "canonical shared imports" [testCase entry (sharing entry) | entry <- entries]
    , TestCase "parser cache covers the complete package snapshot" $ do
        producer <- MirHousekeeping.emitterKey
        actual <- TersusParser.parserKey
        let hash files = fingerprint ([compilerSnapshotHash] ++ concatMap (\(path, source) -> [path, source]) files ++ [runtimeSource])
            original = hash parserPackageFiles
            changed target = [(path, source ++ if path == target then "\n" else "") | (path, source) <- parserPackageFiles]
            manifest = testAssertTrue (all (\(path, _) -> hash (changed path) /= original) parserPackageFiles)
        pure $ case (producer, actual, TersusParser.ownedParserProgram) of
            (Ok emitter, Ok key, Ok program) -> firstFailure
                [testAssertEq key (MirHousekeeping.ownedContentKey emitter (writeProgram program) []), manifest]
            (Error e, _, _) -> Just e
            (_, Error e, _) -> Just e
            (_, _, Error e) -> Just e
    , TestCase "numeric, escaping and truncated-type refusals" readerBounds
    , TestCase "named type tokens and escaped bytes remain exact" writerMetadata
    ]
