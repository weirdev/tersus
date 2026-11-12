{-# LANGUAGE PatternSynonyms #-}
module TestOwnershipCodec (testOwnershipCodec) where

import qualified Data.Map.Strict as Map
import Control.Monad (forM)
import Data.List (isInfixOf, nubBy)
import Link (linkPrograms)
import MirMoves (finishLowered)
import System.Exit (ExitCode (..))
import TestAstData (withAstReader)
import TestNative (runExecutableBytes)
import ValidatorNative (validateCompiled)
import Seed (cachedFrontendSeed)
import Native (runWithInputFull)
import qualified ParserSeed
import qualified ParsedFile
import AstData
import ElaborateRequest
import Interface (ModuleInterface (..))
import InterfaceData
import Syntax
import Types
import TestHarness
import ElaboratorNative (frontendStage)
import ElaboratorTool (Loader, nativeElaborator, nativeLoader, runElaboratorText, runLoader)
import LibPackage (LibPackage (..), compileLibPackageWith)
import Compile (lowerStatementsWith, parseSource, sourceRequest)
import PackageData (ModuleId (..), Snapshot (..), resolverFromFiles)
import qualified PackageCompile as Package
import qualified Mir as M
import PreludeSource (elaboratePackageFiles)
import Utils

transport :: OwnershipTransport
transport = OwnershipTransport (Map.singleton "Clone" ["vendor$Clone"])
    (Map.singleton "Cell" (OwnershipFacts Nothing Nothing (Just ("vendor$Clone", "actualClone")) Nothing))

legacy :: Elaborated
legacy = Elaborated [StructDef "Cell" [] [("n", TInt)] [], Return (Val (VInt 0))] []

versioned :: Elaborated
versioned = legacy{elaboratedOwnership = Just transport}

request :: Request
request = Request (ModuleId "main" Nothing) False False NoInterface [] [] [] [elaboratedStatements legacy]

iface :: InterfaceRecord
iface = InterfaceRecord "vendor" Nothing [("Cell",["Cell"])] [("Cell",("Cell",[("n",TInt)]))] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] Nothing

testOwnershipCodec :: Test
testOwnershipCodec = TestList "testOwnershipCodec"
    [ testCase "legacy elaboration retains legacy provenance" $
        testAssertEq (writeElaborated legacy `bindResult` readElaborated) (Ok legacy)
    , testCase "legacy writer retains its exact version and root" $
        case writeElaboratedLines legacy of
            Error e -> Just e
            Ok ls -> testAssertEq (head ls) "tersus-ast 1 elaborated" <>
                testAssertTrue (any (\l -> take 11 l == "Elaborated ") ls)
    , testCase "new elaboration preserves selected provider and callee" $
        testAssertEq (writeElaborated versioned `bindResult` readElaborated) (Ok versioned)
    , testCase "new ownership cannot be relabelled legacy" $
        case writeElaboratedLines versioned of
            Error e -> Just e
            Ok (_:ls) -> testAssertErrorContains "version mismatch" (readElaboratedLines ("tersus-ast 1 elaborated":ls))
            _ -> Just "no transport"
    , testCase "legacy ownership absence cannot be relabelled new" $
        case writeElaboratedLines legacy of
            Error e -> Just e
            Ok (_:ls) -> testAssertErrorContains "version mismatch" (readElaboratedLines ("tersus-ast 2 elaborated":ls))
            _ -> Just "no transport"
    , testCase "new metadata must cover actual declared types" $
        testAssertErrorContains "missing required" (writeElaborated versioned{elaboratedOwnership = Just transport{transportOwnership = Map.empty}})
    , testCase "half-selected ownership target is malformed" $
        let bad = transport{transportOwnership = Map.singleton "Cell" (OwnershipFacts Nothing Nothing (Just ("vendor$Clone", "")) Nothing)}
         in testAssertErrorContains "incomplete" (writeElaborated versioned{elaboratedOwnership = Just bad})
    , testCase "new interface preserves metadata and legacy payload" $
        let checked = iface{irOwnershipTransport = Just transport}
         in testAssertEq (writeInterfaceRecord checked `bindResult` readInterfaceRecord) (Ok checked)
    , testCase "legacy interface is not a checked empty transport" $
        testAssertEq (writeInterfaceRecord iface `bindResult` readInterfaceRecord) (Ok iface)
    , testCase "new interface rejects omitted declaration facts" $
        testAssertErrorContains "missing required" (writeInterfaceRecord iface{irOwnershipTransport = Just transport{transportOwnership = Map.empty}})
    , testCase "request writer keeps legacy defaults" $
        testAssertEq (writeRequest request `bindResult` readRequest) (Ok request)
    , testCase "explicit request version preserves role providers" $
        let new = request{rqProtocols = Just (transportProtocols transport)}
         in testAssertEq (writeRequest new `bindResult` readRequest) (Ok new)
    , testCase "unknown request version is refused" $
        testAssertErrorContains "not an elaboration request" (readRequest "tersus-elaborate 3\n")
    , testCase "new request cannot omit protocol transport" $
        testAssertErrorContains "not an elaboration request" (readRequest "tersus-elaborate 2\n")
    , testCase "new request rejects empty provider identities" $
        testAssertErrorContains "malformed protocol" (writeRequest request{rqProtocols = Just (Map.singleton "Clone" [""])})
    , testCase "shared vocabulary admits exactly the native wire roles" roleVocabulary
    , TestList "host version 2 transport refusals"
        [testCase name (testAssertErrorContains cause (readElaborated text)) | (name, cause, text) <- badTransports]
    , TestList "host version 2 request provider ordering"
        [testCase name (testAssertErrorContains cause (readRequest text)) | (name, cause, text) <- badRequests]
    , TestCase "native version 2 requests refuse malformed explicit provider records" nativeRequestRefusals
    , TestCase "native version 2 loads give checked facts and refuse malformed explicit provider records" nativeLoadRefusals
    , TestCase "native version 2 transport ordering and seven-name arity refusals" nativeTransportRefusals
    , TestCase "old and transition seed retain exact RQ1 checking and response metadata" nativeLegacyParity
    , TestCase "transition stage one issues facts for real libraries and next frontend" nativeBootstrapSmoke
    , TestCase "transition stage one checks eligible and ineligible conditional Clone" nativeDefiningSmoke
    , TestCase "private defining Clone remains checked without becoming a consumer role" nativePrivateSmoke
    , TestCase "copies of one bounded Clone for different bounded sizes are distinct callees" nativeSizedSmoke
    , TestCase "visible provider ambiguity is refused before deriving capabilities" nativeAmbiguitySmoke
    , TestCase "own and imported List Box declarations bind roles in unrelated packages" nativeStorageRoles
    , TestList "Clone/Drop source and marker semantics"
        [ TestCase "RQ1 expanded source marker retains Drop refusal" (nativeCloneDrop "source-marker" 1)
        , TestCase "RQ2 expanded source marker cannot copy its Block permission" (nativeCloneDrop "source-marker" 2)
        , TestCase "RQ1 no-function marker role refuses Drop" (nativeCloneDrop "empty-marker" 1)
        , TestCase "RQ2 no-function marker role refuses Drop" (nativeCloneDrop "empty-marker" 2)
        , TestCase "RQ1 explicit body retains legacy Drop refusal" (nativeCloneDrop "body" 1)
        , TestCase "RQ2 explicit body proves independent ownership and its postcondition" (nativeCloneDrop "body" 2)
        , TestCase "RQ2 wrong body postcondition is refused by normal validation" (nativeCloneDrop "bad-body" 2)
        , TestCase "a nested dropped field does not expose a Block to an outer Drop" (nativeCloneDrop "nested" 2)
        ]
    ]

nativeLegacyParity :: IO TestResult
nativeLegacyParity = withTransition $ \exe -> do
    old <- cachedFrontendSeed
    case old of
        Error e -> pure (Just e)
        Ok oldExe -> do
            let source = "trait Clone { fn clone(self: &Self) -> Self; }; fn bad<T>(x: &T) -> T { return clone(*x); }; return 0;"
                bounded = case ParserSeed.parseFileWith ParsedFile.emptyDecls source of
                    Left e -> Error e
                    Right (file, _) -> Ok (ParsedFile.fileBody file)
                samples = [Ok (elaboratedStatements legacy), Ok [Return (Val (VInt 0))], Ok [Return (Var "unknown")], bounded]
            results <- forM samples $ \sample -> case sample `bindResult` \ss -> writeRequest request{rqStatements = [ss]} of
                Error e -> pure (Just e)
                Ok text -> do
                    before <- runWithInputFull oldExe text
                    after <- runWithInputFull exe text
                    pure (testAssertEq after before)
            pure (firstFailure results)

nativeBootstrapSmoke :: IO TestResult
nativeBootstrapSmoke = do
    built <- frontendStage 1
    pure $ case built of
        Error e -> Just e
        Ok (exe, _) ->
            let loader = checkedLoader exe
             in case compileLibPackageWith loader of
                Error e -> Just e
                Ok pkg ->
                    let interfaces = Map.elems (libInterfaces pkg)
                        missing = [ifModule iface | iface <- interfaces, ifOwnershipTransport iface == Nothing]
                     in if not (null missing) then Just ("new library facts are absent: " ++ show missing) else
                        case Package.compileModulesUsing loader (Ok pkg) (Snapshot (resolverFromFiles elaboratePackageFiles) "lib/elaborate/elaborate.tersus" False) of
                            Error e -> Just e
                            Ok compiled ->
                                let checked = [elaboratedOwnership (Package.compiledElaborated unit) | unit <- Package.compiledModules compiled]
                                 in testAssertTrue (not (null checked) && all (/= Nothing) checked)

nativeDefiningSmoke :: IO TestResult
nativeDefiningSmoke = do
    built <- frontendStage 1
    pure $ case built of
        Error e -> Just e
        Ok (exe, _) ->
            let facts compiled = Map.unions [transportOwnership t | unit <- Package.compiledModules compiled, Just t <- [elaboratedOwnership (Package.compiledElaborated unit)]]
                selected compiled = Map.lookup "vendor$api$api$Vessel<vendor$api$api$Cell>" (facts compiled) >>= ownershipClone
             in case (compileFixture "vendor/main.tersus" (definingFiles "" "") (checkedLoader exe), compileFixture "vendor/main.tersus" (definingFiles "fn dup(v: &Vessel<Cell>) -> Vessel<Cell> { return clone(*v); };" "y = api::dup(&x); ") (checkedLoader exe)) of
                (Error e, _) -> Just e
                (_, Error e) -> Just ("the called fixture: " ++ e)
                (Ok uncalled, Ok called) ->
                    let applicable = [pair | f <- Map.elems (facts uncalled), Just pair <- [ownershipClone f]]
                        ineligible = Map.lookup "vendor$api$api$Vessel<Missing>" (facts uncalled)
                     in testAssertTrue (not (null applicable)) <>
                        testAssertTrue (maybe False (hasSelectedBody uncalled) (selected uncalled)) <>
                        testAssertEq (linkedCallee uncalled <$> selected uncalled) (Just False) <>
                        testAssertEq (selected called) (selected uncalled) <>
                        testAssertEq (linkedCallee called <$> selected called) (Just True) <>
                        (case Package.lowerCompiledPackage called `bindResult` validateCompiled of Error e -> Just ("the called copy does not validate: " ++ e); Ok _ -> Nothing) <>
                        testAssertEq (ownershipClone <$> ineligible) (Just Nothing) <>
                        testAssertTrue (any (\(provider, callee) -> provider == "vendor$api$api$Clone" && not (null callee)) applicable)

definingFiles :: String -> String -> [(FilePath, String)]
definingFiles api call =
    [ ("vendor/package.tersus", "noPrelude = true;")
    , ("vendor/api/api.tersus", "trait Clone { fn clone(self: &Self) -> Self; }; struct Cell { value: Int }; impl Clone for Cell { fn clone(self: &Self) -> Self { return Cell { value: self.value }; }; }; struct Vessel<T> { value: T }; impl<T: Clone> Clone for Vessel<T> { fn clone(self: &Self) -> Self { return Vessel<T> { value: clone(self.value) }; }; }; " ++ api)
    , ("vendor/main.tersus", "import vendor::api; struct Missing { value: Int }; fn keep(x: &api::Vessel<Missing>) -> Int { return 0; }; x = api::Vessel<api::Cell> { value: api::Cell { value: 1 } }; " ++ call ++ "return 0;")
    ]

roleVocabulary :: TestResult
roleVocabulary =
    let roles = ["Box", "Clone", "Copy", "Deref", "Drop", "Eq", "List"]
        valid = OwnershipTransport (Map.fromList [(r, ["provider$" ++ r]) | r <- roles]) Map.empty
        encoded = writeElaborated (CheckedElaborated [] [] (Just valid))
     in testAssertEq protocolRoles roles <>
        testAssertTrue (all (\r -> validProtocolProviders r ["a", "b"]) roles) <>
        testAssertTrue (all (\r -> not (validProtocolProviders r ["a"])) ["Hash", "Sequence", "Growable", "Unknown"]) <>
        testAssertEq (encoded `bindResult` readElaborated) (Ok (CheckedElaborated [] [] (Just valid)))

rawOwnership :: [(String, [String])] -> [String] -> String
rawOwnership roles facts =
    let (root, nodes) = build []
     in unlines ("tersus-ast 2 elaborated" : reverse nodes ++ ["root " ++ show root])
  where
    node :: String -> [String] -> (Int, [String])
    node text nodes = (length nodes, text : nodes)
    name text nodes =
        let (end, nodes') = node "NameEnd" nodes
         in node ("NamePart " ++ show text ++ " " ++ show end) nodes'
    names [] nodes = node "NamesEnd" nodes
    names (text:rest) nodes =
        let (headId, nodes1) = name text nodes
            (tailId, nodes2) = names rest nodes1
         in node ("NamesCons " ++ show headId ++ " " ++ show tailId) nodes2
    entries [] nodes = node "EntriesEnd" nodes
    entries ((key, values):rest) nodes =
        let (keyId, nodes1) = name key nodes
            (valuesId, nodes2) = names values nodes1
            (entry, nodes3) = node ("NamesEntry " ++ show keyId ++ " " ++ show valuesId) nodes2
            (tailId, nodes4) = entries rest nodes3
         in node ("EntriesCons " ++ show entry ++ " " ++ show tailId) nodes4
    build nodes =
        let (statements, nodes1) = node "StatementsEnd" nodes
            (types, nodes2) = node "TypesEnd" nodes1
            (protocols, nodes3) = entries roles nodes2
            (ownership, nodes4) = entries [("Cell", facts)] nodes3
         in node (unwords ["OwnershipElaborated", show statements, show types, show protocols, show ownership]) nodes4

badTransports :: [(String, String, String)]
badTransports =
    [ ("out-of-order role keys", "out-of-order", rawOwnership [("Copy", ["p"]), ("Clone", ["p"])] absent)
    , ("duplicate role keys", "repeated", rawOwnership [("Clone", ["p"]), ("Clone", ["p"])] absent)
    , ("out-of-order providers", "malformed protocol", rawOwnership [("Clone", ["b", "a"])] absent)
    , ("duplicate providers", "malformed protocol", rawOwnership [("Clone", ["a", "a"])] absent)
    , ("six ownership names", "seven names", rawOwnership [] (replicate 6 ""))
    , ("eight ownership names", "seven names", rawOwnership [] (replicate 8 ""))
    ]
  where absent = replicate 7 ""

badRequests :: [(String, String, String)]
badRequests =
    [ ("out-of-order role records", "out of order", rows ["protocol \"Copy\" 1 \"p\"", "protocol \"Clone\" 1 \"p\""])
    , ("duplicate role records", "repeated", rows ["protocol \"Clone\" 1 \"p\"", "protocol \"Clone\" 1 \"p\""])
    , ("out-of-order provider records", "malformed protocol", rows ["protocol \"Clone\" 2 \"b\" \"a\""])
    , ("duplicate provider records", "malformed protocol", rows ["protocol \"Clone\" 2 \"a\" \"a\""])
    ]
  where
    rows protocols = case writeRequest request{rqProtocols = Just Map.empty} of
        Error e -> error e
        Ok text -> unlines (concatMap (\line -> if line == "protocols 0" then ("protocols " ++ show (length protocols)) : protocols else [line]) (lines text))

nativeRequestRefusals :: IO TestResult
nativeRequestRefusals = withTransition $ \exe -> do
    valid <- case writeRequest request{rqProtocols = Just Map.empty} of
        Error e -> pure (Just e)
        Ok text -> do
            result <- runElaboratorText exe text
            pure $ case result of
                Ok (Accepted elaborated _ _) -> testAssertTrue (elaboratedOwnership elaborated /= Nothing)
                other -> Just ("valid RQ2 control did not return checked facts: " ++ show other)
    results <- forM badRequests $ \(name, cause, text) -> do
        native <- runWithInputFull exe text
        pure $ fmap ((name ++ ": ") ++) (testAssertErrorContains cause (readRequest text) <>
            testAssertEq native (ExitSuccess, "1\n", "not an elaboration request\n"))
    pure (valid <> firstFailure results)

-- (the same protocol records in a load request, where they follow its kind)
nativeLoadRefusals :: IO TestResult
nativeLoadRefusals = withTransition $ \exe -> do
    let load = (sourceRequest LoadProgram False False [] "struct Cell { n: Int }; return 0;"){lrProtocols = Just Map.empty}
    valid <- runLoader exe load
    let positive = case valid of
            Ok (LoadedProgram (Accepted elaborated _ _)) -> testAssertTrue (elaboratedOwnership elaborated /= Nothing)
            other -> Just ("valid version 2 load did not return checked facts: " ++ show other)
    legacyAnswer <- runLoader exe load{lrProtocols = Nothing}
    let unchecked = case legacyAnswer of
            Ok (LoadedProgram (Accepted elaborated _ _)) -> testAssertEq (elaboratedOwnership elaborated) Nothing
            other -> Just ("legacy load did not elaborate: " ++ show other)
    results <- case writeLoadRequest load of
        Error e -> pure [Just e]
        Ok text -> forM badLoadRows $ \(name, protocols) -> do
            native <- runWithInputFull exe (unlines (concatMap (\line -> if line == "protocols 0" then ("protocols " ++ show (length protocols)) : protocols else [line]) (lines text)))
            pure $ fmap ((name ++ ": ") ++) (testAssertEq native (ExitSuccess, "1\n", "not an elaboration request\n"))
    pure (positive <> unchecked <> firstFailure results)
  where
    badLoadRows =
        [ ("out-of-order role records", ["protocol \"Copy\" 1 \"p\"", "protocol \"Clone\" 1 \"p\""])
        , ("duplicate role records", ["protocol \"Clone\" 1 \"p\"", "protocol \"Clone\" 1 \"p\""])
        , ("out-of-order provider records", ["protocol \"Clone\" 2 \"b\" \"a\""])
        , ("duplicate provider records", ["protocol \"Clone\" 2 \"a\" \"a\""])
        , ("unknown role", ["protocol \"Hash\" 1 \"p\""])
        ]

nativeTransportRefusals :: IO TestResult
nativeTransportRefusals = withAstReader $ \exe -> do
    let control = rawOwnership [(r, ["provider$" ++ r]) | r <- protocolRoles] (replicate 7 "")
    accepted <- runExecutableBytes exe [] control
    let positive = case accepted of
            (ExitSuccess, output, "") -> testAssertEq output control <>
                case readElaborated output of
                    Error e -> Just e
                    Ok elaborated -> testAssertEq (Map.keys . transportProtocols <$> elaboratedOwnership elaborated) (Just protocolRoles)
            other -> Just ("valid explicit version 2 control was not read: " ++ show other)
    rejected <- forM badTransports $ \(name, cause, text) -> do
        (code, output, errors) <- runExecutableBytes exe [] text
        pure $ fmap ((name ++ ": ") ++) (testAssertErrorContains cause (readElaborated text) <>
            testAssertEq (code, output, errors) (ExitSuccess, "1\n", "not the AST as data\n"))
    pure (positive <> firstFailure rejected)

firstFailure :: [TestResult] -> TestResult
firstFailure [] = Nothing
firstFailure (Nothing:rest) = firstFailure rest
firstFailure (failure:_) = failure

emptyLibraries :: Result LibPackage String
emptyLibraries = Ok (LibPackage Map.empty Map.empty [] Map.empty)

compileFixture :: FilePath -> [(FilePath, String)] -> Loader -> Result Package.CompiledPackage String
compileFixture entry files loader = Package.compileModulesUsing loader emptyLibraries (Snapshot (resolverFromFiles files) entry False)

withTransition :: (FilePath -> IO TestResult) -> IO TestResult
withTransition use = do
    built <- frontendStage 1
    case built of
        Error e -> pure (Just e)
        Ok (exe, _) -> use exe

checkedAnswer :: FilePath -> Elaborator
checkedAnswer exe rq = nativeElaborator exe rq{rqProtocols = Just Map.empty}

checkedLoader :: FilePath -> Loader
checkedLoader exe rq = nativeLoader exe rq{lrProtocols = Just Map.empty}

mainTransport :: Package.CompiledPackage -> Maybe OwnershipTransport
mainTransport pkg = case [elaboratedOwnership (Package.compiledElaborated m) | m <- Package.compiledModules pkg, Package.compiledModuleId m == Package.compiledEntryModule pkg] of
    [transport] -> transport
    _ -> Nothing

-- The selected callee is a function the package defines, or the copy an Instance record names of a function with
-- bounds whose checked generic body the package carries (which the copy step makes when a call names it)
hasSelectedBody :: Package.CompiledPackage -> (Name, Name) -> Bool
hasSelectedBody pkg (_, callee) = callee `elem` functions False statements || any copyOfChecked [(n, f) | Instance n f _ _ _ <- statements]
  where
    statements = concatMap (elaboratedStatements . Package.compiledElaborated) (Package.compiledModules pkg)
    copyOfChecked (n, f) = n == callee && f `elem` functions True statements
    functions bounded = concatMap (defined bounded)
    defined bounded (Assign name (Val VFunct{})) = [name | not bounded]
    defined _ (BoundedDef _ statement) = defined False statement
    defined bounded (ImplDef _ _ _ _ _ body) = functions bounded body
    defined bounded (Block body) = functions bounded body
    defined _ _ = []

-- The callee as a function of the linked program: the copy step made it, because a call names it
linkedCallee :: Package.CompiledPackage -> (Name, Name) -> Bool
linkedCallee pkg (_, callee) = case Package.lowerCompiledPackage pkg of
    Ok program -> Map.member callee (M.progFunctions program)
    Error _ -> False

nativePrivateSmoke :: IO TestResult
nativePrivateSmoke = withTransition $ \exe -> pure $
    case compileFixture "vendor/main.tersus" (privateFiles "x = api::make(3); return 0;") (checkedLoader exe) of
        Error e -> Just e
        Ok compiled ->
            let main = mainTransport compiled
                actual = main >>= Map.lookup "vendor$hidden$hidden$Vessel<Int>" . transportOwnership
                provider = "vendor$hidden$hidden$Clone"
                privateCaps = testAssertTrue (maybe False (maybe False (\pair@(p, _) -> p == provider && hasSelectedBody compiled pair) . ownershipClone) actual)
                privateRole = testAssertEq (main >>= Map.lookup "Clone" . transportProtocols) Nothing
                refused = case compileFixture "vendor/main.tersus" (privateFiles "x = clone(api::make(3)); return 0;") (checkedLoader exe) of
                    Error e | not ("fixture parse" `isInfixOf` e) && "clone" `isInfixOf` e -> Nothing
                    Error e -> Just ("wrong reason for private Clone syntax refusal: " ++ e)
                    Ok _ -> Just "private defining Clone became a consumer role"
                linked = case selectedOf main of
                    Nothing -> Just "no private Clone callee"
                    Just pair@(_, callee) -> case (consumerLinked compiled callee id, consumerLinked compiled callee (withoutBounded compiled callee)) of
                        (Error e, _) -> Just ("a consumer call of the private callee did not link: " ++ e)
                        (Ok program, missing) ->
                            testAssertTrue (not (linkedCallee compiled pair)) <>
                            testAssertTrue (Map.member callee (M.progFunctions program)) <>
                            (case missing of
                                Error e | callee `isInfixOf` e && "which is not a function with bounds of the program" `isInfixOf` e -> Nothing
                                Error e -> Just ("the copy without its generic body was refused for another reason: " ++ e)
                                Ok _ -> Just "the copy was made without its checked generic body")
                selectedOf transport = transport >>= Map.lookup "vendor$hidden$hidden$Vessel<Int>" . transportOwnership >>= ownershipClone
                provided = case compileFixture "vendor/main.tersus" providerCallFiles (checkedLoader exe) of
                    Error e -> Just ("the provider's own clone call: " ++ e)
                    Ok called -> case selectedOf (mainTransport called) of
                        Nothing -> Just "no private Clone callee with the provider's own call"
                        Just pair@(_, callee) ->
                            testAssertEq (Just callee) (snd <$> selectedOf main) <>
                            testAssertTrue (linkedCallee called pair) <>
                            (case Package.lowerCompiledPackage called `bindResult` validateCompiled of Error e -> Just ("the provider's copy does not validate: " ++ e); Ok _ -> Nothing)
             in privateCaps <> privateRole <> refused <> linked <> provided

-- The package linked with a function of the entry module that calls the callee, as a consumer of the facts would call
-- it before the copy step; the units are first changed by `change`
consumerLinked :: Package.CompiledPackage -> Name -> ([(ModuleId, M.Program)] -> [(ModuleId, M.Program)]) -> Result M.Program String
consumerLinked pkg callee change =
    let lowerOne m = mapResult (\p -> (Package.compiledModuleId m, p)) (Package.compiledLowered m `bindResult` finishLowered)
        libUnits = nubBy (\(a, _) (b, _) -> a == b) (concatMap Package.compiledLibUnits (Package.compiledModules pkg))
        entry = Package.compiledEntryModule pkg
     in flatResultMap lowerOne (Package.compiledModules pkg) `bindResult` \units ->
            linkPrograms (libUnits ++ change [(m, if m == entry then withConsumer p else p) | (m, p) <- units])
  where
    withConsumer p =
        let ty = case [M.localType d | d <- Map.elems (M.fnLocals (M.progMain p)), M.localName d == Just "x"] of t : _ -> t; [] -> TInt
            consumer = (M.progMain p)
                { M.fnName = "consumer", M.fnParams = [M.Local 1], M.fnReturns = Just ty
                , M.fnLocals = Map.fromList [(M.Local 0, M.LocalDecl ty Nothing), (M.Local 1, M.LocalDecl (TRef ty) (Just "v"))]
                , M.fnBlocks = Map.fromList [(M.BlockId 0, M.BasicBlock [] (M.Call (M.Const (M.CFn callee)) [M.Copy (M.Local 1)] (M.Local 0) (M.BlockId 1))), (M.BlockId 1, M.BasicBlock [] M.Return)]
                , M.fnSizeParams = [], M.fnTypeParams = [], M.fnBorrowed = [M.Local 1], M.fnMutBorrowed = [], M.fnFrom = [], M.fnSpec = M.emptySpec
                }
         in p{M.progFunctions = Map.insert "consumer" consumer (M.progFunctions p)}

-- The units with the function the callee is a copy of no longer a function with bounds
withoutBounded :: Package.CompiledPackage -> Name -> [(ModuleId, M.Program)] -> [(ModuleId, M.Program)]
withoutBounded pkg callee units =
    let generic = [f | m <- Package.compiledModules pkg, Instance n f _ _ _ <- elaboratedStatements (Package.compiledElaborated m), n == callee]
     in [(m, p{M.progBounded = foldr Map.delete (M.progBounded p) generic}) | (m, p) <- units]

nativeSizedSmoke :: IO TestResult
nativeSizedSmoke = withTransition $ \exe -> pure $
    case Package.compileModulesUsing (checkedLoader exe) (compileLibPackageWith (checkedLoader exe)) (Snapshot (resolverFromFiles sizedFiles) "sized/main.tersus" False) of
        Error e -> Just e
        Ok compiled ->
            let facts = Map.unions [transportOwnership t | m <- Package.compiledModules compiled, Just t <- [elaboratedOwnership (Package.compiledElaborated m)]]
                callees = [(owner, pair) | (owner, f) <- Map.toList facts, "Holder<" `isInfixOf` owner, Just pair <- [ownershipClone f]]
                instances = Map.fromList [(n, (f, args)) | m <- Package.compiledModules compiled, Instance n f args _ _ <- elaboratedStatements (Package.compiledElaborated m)]
                keys = [Map.lookup callee instances | (_, (_, callee)) <- callees]
                typesOf args = [t | ArgType t <- args]
                sizesOf args = [s | ArgSize s <- args]
             in testAssertEq (length callees) 2 <>
                (case keys of
                    [Just (f2, a2), Just (f3, a3)] ->
                        testAssertEq f2 f3 <> testAssertTrue (sizesOf a2 /= sizesOf a3 && all (`elem` [[SizeConst 2], [SizeConst 3]]) [sizesOf a2, sizesOf a3]) <> testAssertTrue (typesOf a2 /= typesOf a3)
                    other -> Just ("the selected callees are not the copies Instance records name: " ++ show other)) <>
                testAssertTrue (length (nubBy (\(_, (_, a)) (_, (_, b)) -> a == b) callees) == 2) <>
                testAssertTrue (all (linkedCallee compiled . snd) callees) <>
                (case Package.lowerCompiledPackage compiled `bindResult` validateCompiled of Error e -> Just ("the sized copies do not validate: " ++ e); Ok _ -> Nothing)

sizedFiles :: [(FilePath, String)]
sizedFiles =
    [ ("sized/package.tersus", "")
    , ("sized/main.tersus", "trait Clone { fn clone(self: &Self) -> Self; }; trait Feed<E> { fn feed(self: &Self) -> E; }; struct Two { }; struct Three { }; impl Clone for Two { fn clone(self: &Self) -> Self { return Two { }; }; }; impl Clone for Three { fn clone(self: &Self) -> Self { return Three { }; }; }; impl Feed<Array<Int, 2>> for Two { fn feed(self: &Self) -> Array<Int, 2> { return #[1, 2]; }; }; impl Feed<Array<Int, 3>> for Three { fn feed(self: &Self) -> Array<Int, 3> { return #[1, 2, 3]; }; }; struct Holder<T, n> { value: T, cells: Array<Int, n> }; impl<T: Clone + Feed<Array<Int, n>>, n> Clone for Holder<T, n> { fn clone(self: &Self) -> Self { return Holder<T, n> { value: clone(self.value), cells: self.cells }; }; }; a = Holder<Two, 2> { value: Two { }, cells: #[1, 2] }; b = Holder<Three, 3> { value: Three { }, cells: #[1, 2, 3] }; c = clone(a); d = clone(b); return 0;")
    ]

-- The provider clones its own Vessel<Int> (with its own Clone role) in a function main calls through api
providerCallFiles :: [(FilePath, String)]
providerCallFiles =
    [ (path, text ++ extra) | (path, text) <- privateFiles "x = api::make(3); y = api::dupv(&x); return 0;", let extra = providerExtra path ]
  where
    providerExtra "vendor/hidden/hidden.tersus" = " fn copyVessel(v: &Vessel<Int>) -> Vessel<Int> { return clone(*v); };"
    providerExtra "vendor/api/api.tersus" = " fn dupv(v: &hidden::Vessel<Int>) -> hidden::Vessel<Int> { return hidden::copyVessel(v); };"
    providerExtra _ = ""

privateFiles :: String -> [(FilePath, String)]
privateFiles main =
    [ ("vendor/package.tersus", "noPrelude = true;")
    , ("vendor/hidden/hidden.tersus", "trait Clone { fn clone(self: &Self) -> Self; }; struct Vessel<T> { value: T }; impl<T: Clone> Clone for Vessel<T> { fn clone(self: &Self) -> Self { return Vessel<T> { value: clone(self.value) }; }; }; fn vessel(n: Int) -> Vessel<Int> { return Vessel<Int> { value: n }; };")
    , ("vendor/api/api.tersus", "import vendor::hidden; fn make(n: Int) -> hidden::Vessel<Int> { return hidden::vessel(n); };")
    , ("vendor/main.tersus", "import vendor::api { make }; " ++ main)
    ]

nativeAmbiguitySmoke :: IO TestResult
nativeAmbiguitySmoke = withTransition $ \exe -> pure $
    let result = compileFixture "vendor/main.tersus" providerFiles (checkedLoader exe)
     in testAssertErrorContains "conflicting Clone providers" result <>
        testAssertErrorContains "vendor$one$one$Clone" result <>
        testAssertErrorContains "vendor$two$two$Clone" result
  where
    providerFiles =
        [ ("vendor/package.tersus", "noPrelude = true;")
        , ("vendor/one/one.tersus", "trait Clone { fn clone(self: &Self) -> Self; };")
        , ("vendor/two/two.tersus", "trait Clone { fn clone(self: &Self) -> Self; };")
        , ("vendor/main.tersus", "import vendor::one; import vendor::two; return 0;")
        ]

nativeStorageRoles :: IO TestResult
nativeStorageRoles = withTransition $ \exe -> pure $
    let imported = firstFailure
            [ case compileFixture "unrelated/main.tersus" files (if version == 1 then nativeLoader exe else checkedLoader exe) of
                Error e -> Just e
                Ok compiled -> if version == 1 then testAssertEq (mainTransport compiled) Nothing else
                    let protocols = transportProtocols <$> mainTransport compiled
                     in testAssertEq (protocols >>= Map.lookup "List") (Just ["unrelated$model$model$List"]) <>
                        testAssertEq (protocols >>= Map.lookup "Box") (Just ["unrelated$model$model$Box"])
            | version <- [1 :: Int, 2]]
        own = case compileFixture "unrelated/main.tersus" ownFiles (checkedLoader exe) of
            Error e -> Just e
            Ok compiled ->
                let protocols = transportProtocols <$> mainTransport compiled
                 in testAssertEq (protocols >>= Map.lookup "List") (Just ["List"]) <>
                    testAssertEq (protocols >>= Map.lookup "Box") (Just ["Box"])
        conflict = compileFixture "unrelated/main.tersus" conflictFiles (checkedLoader exe)
     in imported <> own <> testAssertErrorContains "conflicting List providers" conflict <>
        testAssertErrorContains "unrelated$model$model$List" conflict <>
        testAssertErrorContains "unrelated$other$other$List" conflict
  where
    files =
        [ ("unrelated/package.tersus", "noPrelude = true;")
        , ("unrelated/model/model.tersus", "struct List<T> { value: T }; struct Box<T> { value: T };")
        , ("unrelated/main.tersus", "import unrelated::model as names; x = names::List<Int> { value: 1 }; y = names::Box<Int> { value: 2 }; return 0;")
        ]
    ownFiles =
        [ ("unrelated/package.tersus", "noPrelude = true;")
        , ("unrelated/main.tersus", "struct List<T> { value: T }; struct Box<T> { value: T }; x = List<Int> { value: 1 }; y = Box<Int> { value: 2 }; return 0;")
        ]
    conflictFiles =
        [ ("unrelated/package.tersus", "noPrelude = true;")
        , ("unrelated/model/model.tersus", "struct List<T> { value: T };")
        , ("unrelated/other/other.tersus", "struct List<T> { value: T };")
        , ("unrelated/main.tersus", "import unrelated::model; import unrelated::other; return 0;")
        ]

nativeCloneDrop :: String -> Int -> IO TestResult
nativeCloneDrop kind version = withTransition $ \exe -> pure $
    let marker = cloneDropFiles "impl Clone for Owned { };" "return 0;"
        body = cloneDropFiles (cloneBody "self.n") "a = Owned::new(3); b = clone(a); return a.n + b.n;"
        invalid = cloneDropFiles (cloneBody "self.n + 1") "return 0;"
        markerTrait files = [(path, unlines [if take 12 line == "trait Clone " then "trait Clone { };" else line | line <- lines text]) | (path, text) <- files]
        emptyMarker (ImplDef (Just "Clone") args "Owned" ty bounds _) = ImplDef (Just "Clone") args "Owned" ty bounds []
        emptyMarker statement = statement
        loader = if version == 1 then nativeLoader exe else checkedLoader exe
        libraries = compileLibPackageWith loader
        packaged files = mapResult (const ()) (compileFixtureWith libraries files)
        compileFixtureWith libs files = Package.compileModulesUsing loader libs (Snapshot (resolverFromFiles files) "owned/main.tersus" False)
        -- (no source spells a marker impl without the function the parser writes for it, so the program's statements
        -- are given as a module request with that function removed)
        answer rq = (if version == 1 then nativeElaborator exe else checkedAnswer exe) rq{rqStatements = map (map emptyMarker) (rqStatements rq)}
        program files = case lookup "owned/main.tersus" files of
            Nothing -> Error "the fixture has no main file"
            Just text -> mapResult (const ()) (parseSource text `bindResult` lowerStatementsWith answer)
        compile files = if kind == "empty-marker" then program files else packaged files
        control = if kind == "empty-marker" then markerTrait (cloneDropFiles "" "return 0;") else cloneDropFiles "" "return 0;"
        setup = case compile control of Error e -> Just ("complete Clone/Drop control did not type check: " ++ e); Ok _ -> Nothing
        validated files = compileFixtureWith libraries files `bindResult` Package.lowerCompiledPackage `bindResult` validateCompiled
        outcome = case kind of
            "source-marker" -> testAssertErrorContains (if version == 1 then "has a drop" else "Block<Int> is a permission, which is never copied") (compile marker)
            "empty-marker" -> testAssertErrorContains "has a drop" (compile (markerTrait marker))
            "body" | version == 1 -> testAssertErrorContains "has a drop" (compile body)
                   | otherwise -> case validated body of Error e -> Just e; Ok _ -> Nothing
            "bad-body" -> case compile invalid of
                Error e -> Just ("bad contract fixture did not reach normal validation: " ++ e)
                Ok _ -> testAssertErrorContains "return.n = self.n" (validated invalid)
            "nested" ->
                let source = "struct Outer { u: Owned }; impl Drop for Outer { fn drop(self: Self) -> Int { Self { u: value } = self; return value.n; }; }; impl Clone for Outer { }; return 0;"
                 in testAssertErrorContains "Outer holds no permission (Block<T>)" (compile (cloneDropFiles (cloneBody "self.n") source))
            _ -> Just "unknown Clone/Drop matrix case"
     in setup <> outcome
  where
    cloneBody value = "impl Clone for Owned { fn clone(self: &Self) -> Self [{ }] [{ affirm return.n = self.n; }] { return Owned::new(" ++ value ++ "); }; };"

cloneDropFiles :: String -> String -> [(FilePath, String)]
cloneDropFiles cloneImpl main =
    [ ("owned/package.tersus", "")
    , ("owned/main.tersus", unlines
        [ "trait Clone { fn clone(self: &Self) -> Self; };"
        , "trait Drop { fn drop(self: Self) -> Int; };"
        , "struct Owned { addr: Addr<Int>, n: Int, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 1; affirm filled(blk, 0) = true; }];"
        , "impl Owned { fn new(n: Int) -> Self [{ }] [{ affirm return.n = n; }] { (a, b) = Addr::alloc(1); return Self { addr: a, n: n, blk: Addr::write(a, 0, n, b) }; }; };"
        , "impl Drop for Owned { fn drop(self: Self) -> Int { return Addr::free(self.addr, Addr::dropValue(self.addr, 0, self.blk)); }; };"
        , cloneImpl
        , main
        ])
    ]
