module TestParserBootstrap (testParserBootstrap) where

import Control.Concurrent (MVar, forkIO, newEmptyMVar, newMVar, putMVar, takeMVar)
import Control.Concurrent.MVar (modifyMVar)
import Control.Exception (SomeAsyncException, SomeException, bracket, displayException, evaluate, fromException, throwIO, try)
import Control.Monad (forM)
import Data.List (isPrefixOf, sort)
import GHC.Clock (getMonotonicTime)
import System.Directory (createDirectory, createFileLink, doesFileExist, findExecutable, getTemporaryDirectory, getModificationTime, listDirectory, removeDirectoryRecursive, removeFile, renameFile)
import System.Environment (getEnvironment, getExecutablePath, getEnv, lookupEnv, setEnv, unsetEnv)
import System.Exit (ExitCode (..))
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode)
import System.IO (hClose, openTempFile)
import System.FilePath ((</>))
import System.IO.Unsafe (unsafePerformIO)

import qualified AstData
import qualified Bootstrap
import qualified Compile
import qualified FileParserProtocol as File
import MirData (writeProgram)
import MirEval (runProgram, MirValue (..))
import Modules (LoadResult (..), resolverFromFiles)
import qualified Modules
import qualified PackageCompile
import MirHousekeeping (listLibrary)
import qualified MirHousekeeping as Housekeeping
import MirLists (lowerLists)
import MirOwnership (expandRefWrites, insertOwnership)
import Native (buildExecutable, cacheDirectory)
import Syntax (Expression (..), Statement (..), Value (..))
import ParsedFile
import qualified ParserSeed
import qualified Pipeline
import PreludeSource (compilerSourceHash, libPackageFiles, stdlibSource, toolPackageFiles, mirPackageFiles)
import Hash (fingerprint)
import Seed (cachedParserSeed, parserSeedHash, seedHash, emitterHash)
import qualified SourceParse
import qualified TersusParser
import TestHarness
import Utils

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [err | Just err <- results] of
    err : _ -> Just err
    [] -> Nothing

withDirectory :: (FilePath -> IO a) -> IO a
withDirectory use = bracket make removeDirectoryRecursive use
  where
    make = do
        tmp <- getTemporaryDirectory
        (home, handle) <- openTempFile tmp "tersus-parser-bootstrap-test"
        hClose handle
        removeFile home
        createDirectory home
        pure home

worker :: String -> FilePath -> [(String, String)] -> IO (ExitCode, String, String)
worker mode home overrides = do
    self <- getExecutablePath
    inherited <- getEnvironment
    let changed = ("TERSUS_PARSER_BOOTSTRAP_WORKER", mode) : ("XDG_CACHE_HOME", home) : overrides
        environment = changed ++ [(key, value) | (key, value) <- inherited, key `notElem` map fst changed, key /= "TERSUS_PARSER"]
    readCreateProcessWithExitCode (proc self ["testParserBootstrap", "--child", "+RTS", "-N1", "-RTS"]){env = Just environment} ""

inFreshWorker :: String -> (FilePath -> IO [(String, String)]) -> IO TestResult -> IO TestResult
inFreshWorker mode setup action = do
    selected <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case selected of
        Just active | active == mode -> action
                    | otherwise -> pure Nothing
        Nothing -> withDirectory $ \home -> do
            overrides <- setup home
            (status, out, err) <- worker mode home overrides
            pure $ case status of
                ExitSuccess -> Nothing
                _ -> Just ("fresh " ++ mode ++ " worker: " ++ out ++ err)

wrongSeed :: String -> FilePath -> IO [(String, String)]
wrongSeed variable home = do
    let path = home </> "wrong-seed.ll"
    writeFile path "not a pinned seed\n"
    pure [(variable, path)]

failureCase :: String -> String -> IO TestResult
failureCase mode expected = inFreshWorker mode setup $ do
    result <- evaluate (Pipeline.compileSource "return 17;")
    pure $ case result of
        Error err -> firstFailure
            [ testAssertErrorContains expected (Error err :: Result () String)
            , testAssertTrue ("Parser tool failure:" `isPrefixOf` err || "Unknown TERSUS_PARSER" `isPrefixOf` err)
            ]
        Ok _ -> Just "a failed bootstrap was hidden by another parser"
  where
    setup home = case mode of
        "emitter-corrupt" -> wrongSeed "TERSUS_SEED_FILE" home
        "parser-corrupt" -> wrongSeed "TERSUS_PARSER_SEED_FILE" home
        "parser-missing" -> pure [("TERSUS_PARSER_SEED_FILE", home </> "missing.ll")]
        "interpreted-corrupt" -> (++ [("TERSUS_PARSER", "interpreted")]) <$> wrongSeed "TERSUS_PARSER_SEED_FILE" home
        "haskell-refused" -> pure [("TERSUS_PARSER", "haskell")]
        "clang-missing" -> do
            let bin = home </> "bin"
            createDirectory bin
            mapM_ (\name -> do
                path <- findExecutable name
                case path of
                    Just executable -> createFileLink executable (bin </> name)
                    Nothing -> pure ()) ["sha256sum", "shasum", "curl"]
            pure [("PATH", bin)]
        _ -> fail ("unknown bootstrap control: " ++ mode)

withSetting :: String -> Maybe String -> IO a -> IO a
withSetting name value action = bracket (lookupEnv name) restore $ \_ -> do
    restore value
    action >>= evaluate
  where
    restore Nothing = unsetEnv name
    restore (Just text) = setEnv name text

retryStages :: IO TestResult
retryStages = inFreshWorker "repair" (const (pure [])) $ do
    directory <- cacheDirectory
    case directory of
        Error e -> pure (Just e)
        Ok cache -> withDirectory $ \home -> do
            let missing = home </> "missing-parser.ll"
                bin = home </> "bin"
                sourceValue answer = case answer of
                    Left e -> Just e
                    Right wire -> case AstData.readParsed wire of
                        Error e -> Just e
                        Ok body -> testAssertTrue (not (null body)) <> testAssertEq (last body) (Return (Val (VInt 43)))
                refused label answer = case answer of
                    Left e -> testAssertTrue (ParserSeed.toolFailure e)
                    Right _ -> Just (label ++ ": transient bootstrap error was not refused")
                parsed answer = testAssertEq (fmap fst answer) (Right (ParsedFile [] [Return (Val (VInt 42))]))
            createDirectory bin
            mapM_ (\name -> do
                found <- findExecutable name
                case found of
                    Nothing -> pure ()
                    Just path -> createFileLink path (bin </> name)) ["sha256sum", "shasum"]
            sourceFailed <- withSetting "TERSUS_PARSER_SEED_FILE" (Just missing) (TersusParser.toolParseSource "return 41;")
            nativeFailed <- withSetting "TERSUS_PARSER_SEED_FILE" (Just missing) (TersusParser.parseFileNative emptyDecls "return 42;")
            clangFailed <- withSetting "PATH" (Just bin) (TersusParser.parseFileNative emptyDecls "return 42;")
            emitterFailed <- withSetting "TERSUS_SEED_FILE" (Just (home </> "missing-emitter.ll")) (TersusParser.parseFileNative emptyDecls "return 42;")
            nativeReady <- TersusParser.parseFileNative emptyDecls "return 42;"
            sourceReady <- TersusParser.toolParseSource "return 43;"
            case firstFailure [refused "source P0" sourceFailed, refused "native P0" nativeFailed, refused "clang" clangFailed, refused "emitter E0" emitterFailed, parsed nativeReady, sourceValue sourceReady] of
                Just e -> pure (Just e)
                Nothing -> do
                    executable <- TersusParser.parserExecutable
                    case executable of
                        Error e -> pure (Just e)
                        Ok path -> do
                            removeFile path
                            rebuilt <- TersusParser.parseFileNative emptyDecls "return 42;"
                            present <- doesFileExist path
                            let p0 = cache </> ("parser-seed-" ++ parserSeedHash)
                            interpretedFailed <- bracket (renameFile p0 (p0 ++ ".held"))
                                (\_ -> renameFile (p0 ++ ".held") p0)
                                (\_ -> withSetting "TERSUS_PARSER_SEED_FILE" (Just missing) (TersusParser.parseFileInterpreted emptyDecls "return 42;"))
                            interpretedReady <- TersusParser.parseFileInterpreted emptyDecls "return 42;"
                            pure (firstFailure [parsed rebuilt, testAssertTrue present, refused "interpreted P0" interpretedFailed, parsed interpretedReady])

emitterRetryStages :: IO TestResult
emitterRetryStages = inFreshWorker "emitter-repair" (const (pure [])) $ withDirectory $ \home -> do
    let bin = home </> "bin"
        refused label result = case result of
            Error _ -> Nothing
            Ok _ -> Just (label ++ ": direct emitter bootstrap error was not refused")
    createDirectory bin
    mapM_ (\name -> do
        found <- findExecutable name
        case found of
            Nothing -> pure ()
            Just path -> createFileLink path (bin </> name)) ["sha256sum", "shasum"]
    parserFailed <- withSetting "TERSUS_PARSER_SEED_FILE" (Just (home </> "missing-parser.ll")) Bootstrap.cachedEmitter
    clangFailed <- withSetting "PATH" (Just bin) Bootstrap.cachedEmitter
    emitterFailed <- withSetting "TERSUS_SEED_FILE" (Just (home </> "missing-emitter.ll")) Bootstrap.cachedEmitter
    ready <- Bootstrap.cachedEmitter
    case firstFailure [refused "P0" parserFailed, refused "clang" clangFailed, refused "E0" emitterFailed] of
        Just e -> pure (Just e)
        Nothing -> case ready of
            Error e -> pure (Just e)
            Ok _ -> do
                let checked = Compile.lowerSource True "return 42;" `bindResult` \program ->
                        Housekeeping.verifyProgram program `bindResult` \_ -> Housekeeping.eraseGhosts program
                case checked of
                    Error e -> pure (Just e)
                    Ok program -> do
                        _ <- evaluate listLibrary
                        pure (testAssertEq (runProgram program) (Ok (Just (MInt 42))))

bootstrapLibraryHash :: IO TestResult
bootstrapLibraryHash = pure $ testAssertEq emitterHash
    (fingerprint ([seedHash, parserSeedHash] ++ concatMap (\(path, text) -> [path, text]) (mirPackageFiles ++ libPackageFiles)
        ++ [stdlibSource, compilerSourceHash]))

timed :: String -> IO a -> IO a
timed name action = do
    start <- getMonotonicTime
    value <- action
    end <- getMonotonicTime
    putStrLn ("[BOOT] " ++ name ++ " " ++ show (end - start) ++ "s")
    pure value

coldStages :: IO TestResult
coldStages = do
    directory <- cacheDirectory
    case directory of
        Error e -> pure (Just e)
        Ok home -> do
            before <- listDirectory home
            seed <- timed "P0" cachedParserSeed
            case ParserSeed.parseImportPrefix userMain of
                Right [Import ["bootstrapprobe", "math"] Nothing (Just ["twice"]) 1 1] -> pure ()
                Left e -> fail e
                Right imports -> fail ("unexpected user-package import metadata: " ++ show imports)
            emitter <- timed "E1+checker+eraser+ListBox" Bootstrap.cachedEmitter
            parser <- timed "P1" (TersusParser.parseFileNative emptyDecls "return 42;")
            source <- timed "source" (evaluate (Pipeline.compileSource "return 42;"))
            package <- timed "user package" $ evaluate $ case Pipeline.loadFromEntry (resolver userPackage) "bootstrapprobe/main.tersus" of
                Left e -> Error e
                Right (PackageResult pkg) -> Pipeline.compileModulesValidated pkg
                Right _ -> Error "the importing user program is not a package"
            entries <- listDirectory home
            pure $ firstFailure
                [ if null before then Nothing else Just ("cold worker started with " ++ show before)
                , case seed of Error e -> Just e; Ok _ -> Nothing
                , case emitter of Error e -> Just e; Ok _ -> Nothing
                , case parser of Left e -> Just e; Right (parsed, _) -> testAssertEq (fileBody parsed) [Return (Val (VInt 42))]
                , case source `bindResult` runProgram of Error e -> Just e; Ok answer -> testAssertEq answer (Just (MInt 42))
                , case package `bindResult` runProgram of Error e -> Just e; Ok answer -> testAssertEq answer (Just (MInt 42))
                , testAssertTrue (all (`elem` entries) ["parser-seed-" ++ parserSeedHash, "seed-" ++ seedHash, "emitter-" ++ emitterHash, "tersus-parser-" ++ TersusParser.parserHash])
                , testAssertTrue (all (\prefix -> any (prefix `isPrefixOf`) entries) ["mir-verify-", "mir-erase-", "tersus_rt_"])
                ]
  where
    resolver = resolverFromFiles
    userMain = "import bootstrapprobe::math { twice }; return twice(21);"
    userPackage =
        [ ("bootstrapprobe/package.tersus", "")
        , ("bootstrapprobe/main.tersus", userMain)
        , ("bootstrapprobe/math/math.tersus", "fn twice(x: Int) -> Int ~ { return x + x; };")
        ]

warmStages :: IO TestResult
warmStages = do
    answer <- TersusParser.parseFileNative emptyDecls "return 42;"
    ir <- Bootstrap.tersusLlvm "return 42;"
    pure $ firstFailure [either Just (const Nothing) answer, case ir of Error e -> Just e; Ok _ -> Nothing]

{-# NOINLINE coldReuseResults #-}
coldReuseResults :: MVar (Maybe (TestResult, TestResult))
coldReuseResults = unsafePerformIO (newMVar Nothing)

coldAndReuse :: IO (TestResult, TestResult)
coldAndReuse = modifyMVar coldReuseResults $ \saved -> case saved of
    Just results -> pure (saved, results)
    Nothing -> do
        results <- withDirectory $ \home -> do
            first <- try (worker "cold" home []) :: IO (Either SomeException (ExitCode, String, String))
            cold <- case first of
                Left ex -> synchronousFailure ex
                Right (ExitSuccess, _, _) -> pure Nothing
                Right (_, out, err) -> pure (Just ("fresh cold worker: " ++ out ++ err))
            case cold of
                Just err -> pure (cold, Just ("cache reuse requires a successful cold worker: " ++ err))
                Nothing -> do
                    reused <- try (reuse home) :: IO (Either SomeException TestResult)
                    result <- either synchronousFailure pure reused
                    pure (Nothing, result)
        pure (Just results, results)
  where
    reuse home = do
        let cache = home </> "tersus"
        names <- sort <$> listDirectory cache
        before <- mapM (getModificationTime . (cache </>)) names
        second <- worker "reuse" home []
        afterNames <- sort <$> listDirectory cache
        after <- mapM (getModificationTime . (cache </>)) names
        pure $ case second of
            (ExitSuccess, _, _) -> testAssertEq (afterNames, after) (names, before)
            (_, out, err) -> Just (out ++ err)
    synchronousFailure ex = case fromException ex :: Maybe SomeAsyncException of
        Just _ -> throwIO ex
        Nothing -> pure (Just (displayException ex))

coldProcess :: IO TestResult
coldProcess = do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just "cold" -> coldStages
        Just _ -> pure Nothing
        Nothing -> fst <$> coldAndReuse

cacheReuse :: IO TestResult
cacheReuse = do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just "reuse" -> warmStages
        Just _ -> pure Nothing
        Nothing -> snd <$> coldAndReuse

concurrentCold :: IO TestResult
concurrentCold = do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just "concurrent" -> warmStages
        Just _ -> pure Nothing
        Nothing -> withDirectory $ \home -> do
            variables <- forM [1 :: Int, 2] $ \_ -> do
                result <- newEmptyMVar
                _ <- forkIO (worker "concurrent" home [] >>= putMVar result)
                pure result
            results <- mapM takeMVar variables
            names <- listDirectory (home </> "tersus")
            pure $ firstFailure
                ([case result of (ExitSuccess, _, _) -> Nothing; (_, out, err) -> Just (out ++ err) | result <- results]
                ++ [testAssertTrue (all (`elem` names) ["parser-seed-" ++ parserSeedHash, "emitter-" ++ emitterHash, "tersus-parser-" ++ TersusParser.parserHash])])

parserFixpoint :: IO TestResult
parserFixpoint = do
    mode <- lookupEnv "TERSUS_PARSER_BOOTSTRAP_WORKER"
    case mode of
        Just _ -> pure Nothing
        Nothing -> do
            emitter <- Bootstrap.cachedEmitter
            let zeroPackage = loadPackage ParserSeed.parseFileWith
                onePackage = loadPackage (checkedParser TersusParser.parseFileNative)
                zeroOwned = zeroPackage `bindResult` ownPackage
                oneOwned = onePackage `bindResult` ownPackage
            case (emitter, zeroPackage, onePackage, zeroOwned, oneOwned) of
                (Ok exe, Ok a, Ok b, Ok zero, Ok one)
                    | show a /= show b -> pure (Just "P0/P1 prepared current PACKAGE AST/imports/Marks/identities differ")
                    | writeProgram zero /= writeProgram one -> pure (Just "P0/P1 current checking/lowering/MIR differs")
                    | otherwise -> do
                        first <- Bootstrap.emitWith exe (writeProgram zero)
                        second <- Bootstrap.emitWith exe (writeProgram one)
                        case (first, second) of
                            (Ok ir0, Ok ir1) | ir0 == ir1 -> withDirectory $ \home -> do
                                let two = home </> "parser-two"
                                built <- buildExecutable two ir1
                                case built of
                                    Error e -> pure (Just e)
                                    Ok () -> do
                                        let twoParser = ParserSeed.parseFileWithTool (pure (Ok two))
                                            twoPackage = loadPackage (checkedParser twoParser)
                                        case twoPackage of
                                            Error e -> pure (Just e)
                                            Ok c | show b /= show c -> pure (Just "P1/P2 prepared current PACKAGE differs")
                                            Ok _ -> case SourceParse.probeDecls of
                                                Left e -> pure (Just e)
                                                Right decls -> do
                                                    results <- forM ["return 42;", "s = \"λ🙂\"; return size(s.bytes);", "enum E { A, B }; enum E { C }; return E::C;", "import app::geo as g { Point }; return 0;"] $ \source -> do
                                                        p0 <- ParserSeed.parseFileNative (locating decls) source
                                                        p1 <- TersusParser.parseFileNative (locating decls) source
                                                        p2 <- twoParser (locating decls) source
                                                        pure (sameFile p0 p1 <> sameFile p1 p2)
                                                    pure (firstFailure results)
                            (Error e, _) -> pure (Just e)
                            (_, Error e) -> pure (Just e)
                            _ -> pure (Just "regenerated current P1/P2 IR differs")
                (Error e, _, _, _, _) -> pure (Just e)
                (_, Error e, _, _, _) -> pure (Just e)
                (_, _, Error e, _, _) -> pure (Just e)
                (_, _, _, Error e, _) -> pure (Just e)
                (_, _, _, _, Error e) -> pure (Just e)
  where
    loadPackage parser = case Modules.loadFromEntryWith parser (resolverFromFiles toolPackageFiles) "examples/parser/parser.tersus" of
        Left e -> Error e
        Right (PackageResult pkg) -> Ok pkg
        Right _ -> Error "parser was not loaded as its current package"
    ownPackage pkg = PackageCompile.compileModulesLinked pkg `bindResult` \program ->
        mapResult insertOwnership (Housekeeping.nativeProgram program)
    checkedParser current decls source = unsafePerformIO $ do
        p0 <- ParserSeed.parseFileNative decls source
        pn <- current decls source
        pure $ case (p0, pn) of
            (Left e, Left _) | not (ParserSeed.toolFailure e) -> pn
            _ -> case sameFile p0 pn of
                Nothing -> pn
                Just e -> Left (ParserSeed.failure ("prepared package file parity: " ++ e))
    sameFile (Right (a, da)) (Right (b, db)) = testAssertEq a b <> testAssertEq (File.writeParsedFile a da) (File.writeParsedFile b db)
    sameFile (Left e) _ = Just e
    sameFile _ (Left e) = Just e

testParserBootstrap :: Test
testParserBootstrap = TestList "testParserBootstrap"
    [ TestCase "default whole Pipeline refuses failed native bootstrap" (failureCase "emitter-corrupt" "bootstrap/emitter.sha256")
    , TestCase "corrupt parser seed is an explicit tool failure" (failureCase "parser-corrupt" "bootstrap/parser.sha256")
    , TestCase "missing parser override is an explicit tool failure" (failureCase "parser-missing" "verify the parser bootstrap seed")
    , TestCase "interpreted parser still requires verified native P0" (failureCase "interpreted-corrupt" "bootstrap/parser.sha256")
    , TestCase "no clang is an explicit P0 tool failure" (failureCase "clang-missing" "Could not run clang")
    , TestCase "retired haskell backend is refused" (failureCase "haskell-refused" "expected native or interpreted")
    , TestCase "cold process reaches P0 E1 P1 source and package" coldProcess
    , TestCase "fresh processes reuse every bootstrap cache entry without writes" cacheReuse
    , TestCase "concurrent empty-cache processes converge" concurrentCold
    , TestCase "same-process transient failures repair without stale library or executable caches" retryStages
    , TestCase "public emitter bootstrap failures repair before tool and library CAF initialization" emitterRetryStages
    , TestCase "bootstrap fingerprints cover the complete compiler library manifest" bootstrapLibraryHash
    , TestCase "P0 P1 current-source fixpoint regenerates identical IR and P2 behavior" parserFixpoint
    ]
