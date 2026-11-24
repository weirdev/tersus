module TestDifferential (testDifferential, ergonomicsUnits) where

import AstData (writeBuiltinTable)
import BuiltinTable (builtinTable)
import CacheLock (openTempFileCloexec)
import Compile (lowerSourceUsing, parseWithEquality, sourceRequest)
import Control.Exception (bracket, evaluate)
import Data.Char (ord)
import Data.List (find, isInfixOf, isPrefixOf, isSuffixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import DataCodec (typeTokens)
import LibPackage (LibPackage (..), compileLibPackageWith, libCatalog, libModuleId, libPackage, stripDeclaredFromUnits)
import Lowering (lowerAccepted)
import qualified Mir as M
import MirEval (Outcome (..), RunEnv (..), runProgramEnv)
import Modules (ModuleId (..))
import qualified Modules as Mod
import Numeric (showHex)
import System.Directory (getTemporaryDirectory, removeFile)
import System.IO (hClose)
import System.Posix.Files (setFileMode)
import qualified PackageCompile as Package
import Pretty (renderType)
import PreludeSource (elaboratePackageFiles)
import qualified Syntax as S
import Types
import Differential
import ElaborateRequest
import TestData (typeCheckSources)
import TestHarness
import qualified Data.ByteString.Char8 as B
import ElaboratorTool (bootstrapLoader, frontendToolFailure, nativeLoader, runElaboratorRaw, sourceElaborator, sourceElaboratorExecutable)
import Utils

ergonomicsUnits :: [Unit]
ergonomicsUnits =
    [ SourceText "if expression protocol" "x = if true { 3 } else { 4 }; return x;"
    , SourceText "block expression protocol" "return if true { let x = 3; x + 1 } else { 5 };"
    , SourceText "ascribed declaration protocol" "let x: Int = 3; return x;"
    , SourceText "generic template expression protocol" "fn choose<T>(c: Bool, a: T, b: T) -> T { let result: T = if c { a } else { b }; return result; }; return choose(true, 1, 2);"
    ]

-- The compiler's elaborator behind the text protocol agrees with itself on the requests of a package, of the compiler
-- libraries, of the smallest compiler package (whose interfaces have every kind of entry), of a refused program and of
-- the programs of testTypeCheck
protocolAgreement :: IO TestResult
protocolAgreement = do
    let units = [FilePackage "examples/modules/app/main.tersus", Libraries, EmbeddedPackage "lib/mir/mir_erase/mir_erase.tersus", SourceFile "examples/rejected/type_argument_mismatch.tersus"] ++ [SourceText name source | (name, source) <- typeCheckSources] ++ ergonomicsUnits
    results <- runDifferential throughText units
    let (agree, wording, disagree, unmodelled, failed) = tally [o | (_, _, o) <- results]
    putStrLn ("differential: " ++ show (length units) ++ " units, " ++ show agree ++ " agree, " ++ show wording ++ " wording, " ++ show disagree ++ " disagree, " ++ show unmodelled ++ " not modelled, " ++ show failed ++ " failed")
    pure $ case [(unit, modu, o) | (unit, modu, o) <- results, o /= Agree] of
        [] | agree > 0 -> Nothing
        [] -> Just "no requests"
        (unit, modu, o) : _ -> Just (show unit ++ " " ++ modu ++ ": " ++ show o)

-- A candidate that gives a local of the MIR another type, or a refusal other words, or does not handle the program,
-- is not counted as agreeing
mutationControls :: IO TestResult
mutationControls = do
    let units = [SourceFile "examples/arithmetic.tersus", SourceFile "examples/rejected/type_argument_mismatch.tersus"]
    retyped <- runDifferential (perturbed retype) units
    reworded <- runDifferential (perturbed reword) units
    unmodelled <- runDifferential (\asked -> mapResult (mapAnswers (const (NotModelled "everything"))) <$> throughText asked) units
    pure $ firstFailure
        [ expect "retyped" retyped (\o -> case o of Disagree _ -> True; _ -> o == Agree)
        , atLeastOne "retyped" retyped (\o -> case o of Disagree _ -> True; _ -> False)
        , expect "reworded" reworded (\o -> case o of Wording _ _ -> True; _ -> o == Agree)
        , atLeastOne "reworded" reworded (\o -> case o of Wording _ _ -> True; _ -> False)
        , expect "not modelled" unmodelled (\o -> case o of NotModelledBy _ -> True; _ -> False)
        ]
  where
    perturbed change asked = mapResult (mapAnswers change) <$> throughText asked
    mapAnswers change answer = answer{responses = map (fmap change) (responses answer)}
    retype response = case response of
        Accepted i ls (MirLowered unit) -> Accepted i ls (MirLowered (retypeFirst unit))
        other -> other
    retypeFirst unit = case break (\l -> B.pack "local " `B.isPrefixOf` l && B.pack " int" `B.isSuffixOf` l) unit of
        (before, l : after) -> before ++ B.take (B.length l - 3) l <> B.pack "bool" : after
        _ -> unit
    reword response = case response of
        Refused m -> Refused (m ++ "!")
        other -> other
    expect name results ok = case [o | (_, _, o) <- results, not (ok o)] of
        [] -> Nothing
        o : _ -> Just (name ++ ": " ++ show o)
    atLeastOne name results ok = if any (\(_, _, o) -> ok o) results then Nothing else Just (name ++ ": no request was caught")

-- A module's request and response read back as written, and malformed ones are refused
protocolRoundTrip :: IO TestResult
protocolRoundTrip = do
    requests <- mapM (unitRequests compilerFrontend) [SourceText name source | (name, source) <- take 8 typeCheckSources]
    case sequence (map resultList requests) of
        Left e -> pure (Just e)
        Right exchanges -> case [(rq, r) | (AskedModule rq, answers) <- concat exchanges, (_, r) <- responses answers] of
            [] -> pure (Just "no requests")
            answered -> pure $ firstFailure (map (one . fst) answered ++ [malformed (fst (last answered))] ++ map verdict ([Refused "a \"refusal\"", RefusedInterface "in module p::m: no interface", Unresolved "in module p::m: unknown name q", NotModelled "what"] ++ withLibraries (map snd answered)))
  where
    resultList r = case r of
        Ok a -> Right a
        Error e -> Left e
    withLibraries answers = take 1 [Accepted i ["types", "clone"] m | Accepted i _ m <- answers]
    malformed rq = case (writeRequest rq, writeResponse (sourceElaborator rq)) of
        (Ok request, Ok response) ->
            let refused name r = case r of
                    Error _ -> Nothing
                    Ok _ -> Just ("accepted " ++ name)
                swapLine old new text = unlines [if l == old then new else l | l <- lines text]
                firstData text = head [l | l <- lines text, take 5 l == "data "]
                withTable table text =
                    let (before, rest) = break (\l -> take 8 l == "builtins") (lines text)
                        after = drop 1 (dropWhile (\l -> take 11 l /= "interfaces ") rest)
                        interfacesLine = head [l | l <- rest, take 11 l == "interfaces "]
                     in unlines (before ++ take 1 rest ++ ["data " ++ show (length (lines table))] ++ lines table ++ [interfacesLine] ++ after)
             in firstFailure
                    [ refused "a request with another header" (readRequest (swapLine "tersus-elaborate 1" "tersus-elaborate 2" request))
                    , refused "an unknown extraction" (readRequest (unlines [if take 8 l == "extract " then "extract all" else l | l <- lines request]))
                    , refused "a count with a leading zero" (readRequest (swapLine (firstData request) ("data 0" ++ drop 5 (firstData request)) request))
                    , refused "a block cut short" (readRequest (unlines (init (lines request))))
                    , refused "a line after the syntax" (readRequest (request ++ "more\n"))
                    , refused "two spaces after a key" (readRequest (unlines [if take 11 l == "predeclare " then "predeclare  " ++ drop 11 l else l | l <- lines request]))
                    , case (writeBuiltinTable builtinTable, writeBuiltinTable (take 1 builtinTable)) of
                        (Ok same, Ok other) -> firstFailure
                            [ either (Just . ("the same table put back: " ++)) (const Nothing) (resultEither (readRequest (withTable same request)))
                            , refused "another builtin table" (readRequest (withTable other request))
                            ]
                        (Error e, _) -> Just e
                        (_, Error e) -> Just e
                    , refused "a response with no interface line" (readResponse (unlines (takeWhile (\l -> take 9 l /= "interface") (lines response))))
                    , case [(i, m) | Accepted i _ m <- [sourceElaborator rq]] of
                        [] -> Just "the request was not accepted"
                        (i, m) : _ -> case writeResponse (Accepted i ["types", "clone"] m) of
                            Error err -> Just err
                            Ok text -> refused "a libraries line with a wrong count" (readResponse (swapLine "libraries 2 \"types\" \"clone\"" "libraries 3 \"types\" \"clone\"" text))
                    , refused "a response with another header" (readResponse (swapLine "tersus-elaborated 1" "tersus-elaborated 2" response))
                    ]
        (Error e, _) -> Just e
        (_, Error e) -> Just e
    -- (every verdict reads back as it was written)
    verdict response = case writeResponse response `bindResult` readResponse of
        Error e -> Just e
        Ok back -> testAssertEq (show back) (show response)
    one rq = case writeRequest rq `bindResult` readRequest of
        Error e -> Just e
        Ok rq' | rq' /= rq -> Just "request changed"
        Ok _ -> case writeResponse (sourceElaborator rq) of
            Error e -> Just e
            Ok text -> case readResponse text `bindResult` writeResponse of
                Error e -> Just e
                Ok text' -> testAssertEq text' text

-- A refusal, and a section whose count runs past the response, read back as written; a unit that does not read is
-- the elaborator's failure as a tool, while a refusal to lower is the lowering's error in its words
mirSection :: TestResult
mirSection = case sourceElaborator (Request (ModuleId "main" Nothing) False False NoInterface [] [] [] [[S.Return (S.Val (S.VInt 0))]]) of
    Accepted iface libs _ ->
        let refusal = "a \"quoted\" refusal"
         in case writeResponse (Accepted iface libs (MirRefused refusal)) of
                Error err -> Just err
                Ok text -> firstFailure
                    [ case readResponse text of
                        Ok (Accepted _ _ (MirRefused m)) | m == refusal -> Nothing
                        other -> Just ("a refusal read back as " ++ take 400 (show other))
                    , case readResponse (unlines (map overlong (lines text))) of
                        Error err | "malformed mir section" `isInfixOf` err -> Nothing
                        other -> Just ("an overlong mir section read as " ++ take 400 (show other))
                    , testAssertEq (lowerAccepted (Accepted iface libs (MirRefused refusal))) (Error refusal)
                    , case lowerAccepted (Accepted iface libs (MirLowered [B.pack "garbage"])) of
                        Error err | frontendToolFailure err -> Nothing
                        other -> Just ("a unit that does not read gave " ++ take 400 (show other))
                    ]
    other -> Just ("expected an accepted answer, got " ++ take 400 (show other))
  where
    overlong line
        | "mir refused " `isPrefixOf` line = "mir 1000"
        | otherwise = line

-- The elaborator's own functions, run with a table as its program: the lowering's refusal words for types
-- (Pretty.renderType) and for the names and types in a builtin (Haskell's show); arenas the lowering refuses (a reference
-- out of its own arena, which joining would make another arena's record, a root of another kind, and an interface map
-- holding entries of another kind) and one it reads; and a builtin's scheme renumbered
elaboratorChecks :: IO TestResult
elaboratorChecks = pure $ case Mod.loadFromEntry (Mod.resolverFromFiles files) entry of
    _ | length [() | (path, text) <- elaboratePackageFiles, path == entry, marker `elem` lines text] /= 1 -> Just "the elaborator's program does not start where expected"
    Left err -> Just err
    Right (Mod.PackageResult pkg) -> case Package.compileModulesLinked (Mod.packageSnapshot pkg) `bindResult` runProgramEnv RunEnv{envArgs = [], envInput = "", envFile = const Nothing} of
        Error err -> Just err
        Ok outcome ->
            let expected = [line | ty <- types, line <- [show ty, renderType ty]] ++ map show strings ++ arenaLines
             in firstFailure [if a == e then Nothing else Just ("expected " ++ e ++ ", got " ++ a) | (e, a) <- zip expected (lines (decodeUtf8 (outStdout outcome)) ++ repeat "(nothing)")]
    Right _ -> Just "the fixture is standalone"
  where
    entry = "lib/elaborate/elaborate.tersus"
    marker = "header = readLine();"
    files = [(path, if path == entry then unlines (map imported (takeWhile (/= marker) (lines text))) ++ source else text) | (path, text) <- elaboratePackageFiles]
    imported l
        | "import data::codec::codec { " `isPrefixOf` l = "import data::codec::codec { typeAt, " ++ drop (length "import data::codec::codec { ") l
        | "import elaborate::lowerout " `isPrefixOf` l = l ++ "\nimport elaborate::lowerbuild { lwShow, hsShowType };\nimport elaborate::lowerstate { fromCodecTy, newLowSt, renderTy };"
        | "import data::ast::ast { " `isPrefixOf` l = "import data::ast::ast { AstEntries, AstInterface, AstName, AstNames, AstScheme, AstStatements, AstTypes, AstValue, AstValues, " ++ drop (length "import data::ast::ast { ") l
        | otherwise = l
    types =
        [ TNamed "item" []
        , TList (TParam "T")
        , TFn [TNamed "item" []] TInt
        , TArrayOf (TNamed "Pair" [ArgType TInt, ArgSize (SizeConst 3)]) (SizeParam "n")
        , TBox (TNamed "caf\233" [])
        , TForall ["n"] ["T"] (TFn [TParam "T"] (TArrayOf TInt (SizeParam "n")))
        , TNamed "Map" [ArgType (TList (TWord True 8)), ArgSize SizeAny, ArgSize (SizeConst (-2))]
        , TRef (TMutRef (TVar (-3)))
        , TVariant "Some"
        ]
    strings = ["plain", "a\"b\\c", "caf\233", "\233" ++ "1", "\SO" ++ "H", "\DEL\t\1" ++ "2", "\128\2047"]
    source =
        unlines $
            [ "fn wordsLine(s: String) -> Int { n = s.print(); return n + \"\\n\".print(); };"
            , "fn wordsShown(data: String) -> Int ~ {"
            , "    tokens = tokenize(&data);"
            , "    if !tokens.ok || size(tokens.value) = 0 { return wordsLine(\"(no tokens)\"); };"
            , "    ty = typeAt(&tokens.value, 0);"
            , "    if !ty.ok { return wordsLine(\"(no type)\"); };"
            , "    n = wordsLine(hsShowType(clone(ty.value), 0));"
            , "    ls = fromCodecTy(newLowSt(0, \"differential\"), &ty.value);"
            , "    return n + wordsLine(renderTy(&ls, ls.ty));"
            , "};"
            , "words = 0;"
            ]
                ++ ["words = words + wordsShown(" ++ literal (unwords (typeTokens ty)) ++ ");" | ty <- types]
                ++ ["text = " ++ literal text ++ "; words = words + wordsLine(lwShow(&text));" | text <- strings]
                ++ arenaSource
                ++ ["return 0;"]
    -- (the module's arena: an empty program; record 1 and 2 are a Value and a Values)
    arenaSource =
        [ "fn arenaOf(stage: String, nodes: List<AstNode>, root: Int) -> AstProgram ~ { return AstProgram { stage: stage, nodes: nodes, root: root }; };"
        , "fn lowered(ifaces: List<AstProgram>) -> Int ~ {"
        , "    nodes = push(push(push([], AstNode::Name { value: AstName::End }), AstNode::Value { value: AstValue::VBool { b: true } }), AstNode::Values { value: AstValues::End });"
        , "    nodes = push(push(push(nodes, AstNode::Statements { value: AstStatements::End }), AstNode::Types { value: AstTypes::End }), AstNode::Elaborated { value: AstElaborated { statements: 3, types: 4 } });"
        , "    storage = push(push(push([], \"List\"), \"Box\"), \"Copy\");"
        , "    m = lowerUnit(arenaOf(\"elaborated\", nodes, 5), &ifaces, arenaOf(\"builtins\", push([], AstNode::Entries { value: AstEntries::End }), 0), &storage, \"differential\");"
        , "    if m.ok { return wordsLine(\"lowered\"); };"
        , "    return wordsLine(clone(m.msg));"
        , "};"
        , "fn interfaceWithTypes(pair: Bool) -> AstProgram ~ {"
        , "    nodes = push(push(push([], AstNode::Name { value: AstName::End }), AstNode::OptName { value: AstOptName::NoName }), AstNode::Entries { value: AstEntries::End });"
        , "    nodes = push(push(push(nodes, AstNode::Names { value: AstNames::End }), AstNode::Statements { value: AstStatements::End }), AstNode::Entry { value: AstEntry::PairEntry { a: 0, b: 0 } });"
        , "    nodes = push(nodes, AstNode::Entries { value: AstEntries::Cons { head: 5, tail: 2 } });"
        , "    types = 2;"
        , "    if pair { types = 6; };"
        , "    nodes = push(nodes, AstNode::Interface { value: AstInterface { pkg: 0, modu: 1, types: types, ctors: 2, generics: 2, invariants: 2, traits: 2, traitParams: 2, functions: 2, impls: 2, assoc: 2, implArgs: 2, implBounds: 2, copies: 3, linear: 3, drops: 3, axioms: 4, proofs: 4, externs: 3, templates: 2, companions: 2 } });"
        , "    return arenaOf(\"interface\", nodes, 7);"
        , "};"
        , "words = words + lowered(push([], arenaOf(\"interface\", push([], AstNode::Values { value: AstValues::Cons { head: 1, tail: 2 } }), 0)));"
        , "words = words + lowered(push([], arenaOf(\"interface\", push([], AstNode::Name { value: AstName::End }), 0)));"
        , "words = words + lowered(push([], interfaceWithTypes(true)));"
        , "words = words + lowered(push([], interfaceWithTypes(false)));"
        , "scheme = remapNode(AstNode::Scheme { value: AstScheme::SigFn { ts: 0, ret: 1 } }, push(push([], 5), 6));"
        , "if scheme is AstNode::Scheme && (scheme as AstNode::Scheme).value is AstScheme::SigFn { f = (scheme as AstNode::Scheme).value as AstScheme::SigFn; words = words + wordsLine(catStrings(catStrings(intText(f.ts), \" \"), intText(f.ret))); };"
        ]
    arenaLines =
        [ "Lowering: an interface is malformed at record 0"
        , "Lowering: an interface has a root of another kind"
        , "Lowering: an interface has a map or set that is out of order or holds entries of another kind"
        , "lowered"
        , "5 6"
        ]
    literal text = "\"" ++ concatMap escape text ++ "\""
    escape c
        | c == '"' = "\\\""
        | c == '\\' = "\\\\"
        | ord c >= 32 && ord c < 127 = [c]
        | otherwise = "\\u{" ++ showHex (ord c) "" ++ "}"

-- A load request with a section malformed gets no answer: the executable exits saying it is not a request
malformedLoads :: IO TestResult
malformedLoads = case writeLoadRequest (sourceRequest LoadParse False False [] "return 1;") of
    Error e -> pure (Just e)
    Ok request -> do
        exe <- sourceElaboratorExecutable
        case exe of
            Error e -> pure (Just e)
            Ok path -> do
                let cases =
                        [ ("a file with a wrong byte count", replaceLine (\l -> take 16 l == "file \"<source>\" ") (\l -> unwords (init (words l) ++ [show (read (last (words l)) + 1 :: Int)])) request)
                        , ("a count of files that is not the files given", replaceLine (== "files 1") (const "files 2") request)
                        , ("no builtins", replaceLine (== "builtins") (const "") request)
                        , ("a record after the request", request ++ "more\n")
                        , ("an unknown kind of load", replaceLine (== "load parse") (const "load everything") request)
                        ]
                asWritten <- runElaboratorRaw path request
                answers <- mapM (runElaboratorRaw path . snd) cases
                pure $ firstFailure $
                    [ case asWritten of
                        Ok (header : _) | B.unpack header == "tersus-elaborated 1" -> Nothing
                        other -> Just ("the request as written was not answered: " ++ take 200 (show other))
                    ]
                        ++ [if text == request then Just (name ++ " changed nothing") else Nothing | (name, text) <- cases]
                        ++ [ case answer of
                            Ok (header : _) | B.unpack header == "tersus-elaborated 1" -> Just ("the elaborator answered " ++ name)
                            _ -> Nothing
                           | ((name, _), answer) <- zip cases answers
                           ]
  where
    replaceLine matches change text = unlines [if matches l then change l else l | l <- lines text]

-- Every function with bounds of a program is checked against its bounds, the compiler libraries put in front of it
-- included (their checked bodies are what the copy step makes their copies from), and a request names no checked prefix
checkedStatements :: TestResult
checkedStatements = case parseWithEquality "trait Show { fn show(self: &Self) -> Int; }; fn same<T: Show>(a: T, b: T) -> Bool { return a = b; }; return 0;" of
    Left e -> Just e
    Right stmts ->
        let request = Request (ModuleId "main" Nothing) False False NoInterface [] [] [] [stmts]
         in firstFailure
                [ case sourceElaborator request of
                    Refused m | "T is compared with =" `isInfixOf` m -> Nothing
                    other -> Just ("the definition was not refused: " ++ show other)
                , case writeRequest request of
                    Error e -> Just e
                    Ok text -> case readRequest (unlines [if take 8 l == "builtins" then "builtins checked 3" else l | l <- lines text]) of
                        Error _ -> Nothing
                        Ok _ -> Just "accepted a checked count"
                ]

assemblyContract :: IO TestResult
assemblyContract = sourceElaboratorExecutable >>= \exe -> case (exe, libPackage) of
    (Error e, _) -> pure (Just e)
    (_, Error e) -> pure (Just e)
    (Ok path, Ok pkg) -> do
        let program bare = sourceRequest LoadProgram bare False (if bare then [] else libCatalog pkg)
        malformed <- malformedAssemblyRequests path (program False "return 1;") (program True "return 1;")
        wire <- runAssembly path packageRequest{lrLibraries = libCatalog pkg}
        checked <- checkedPackageAssembly
        pure $ firstFailure
            [ check (packageAssembly pkg)
            , checked
            , check packageDecoderRefusals
            , check (standaloneAssembly pkg)
            , check (assemblyRefusals pkg)
            , check (checkMalformedAssembly packageRequest{lrLibraries = libCatalog pkg} wire)
            , malformed
            ]

assemblyFiles :: [(FilePath, String)]
assemblyFiles =
    [ ("assembly/package.tersus", "")
    , ("assembly/main.tersus", "import assembly::left { leftValue }; import assembly::right { rightValue }; import vendor::api { vendorValue }; struct Box { n: Int }; s = \"root\"; return size(s.bytes) + leftValue() + rightValue() + vendorValue();")
    , ("assembly/left/left.tersus", "import assembly::leaf { leafValue }; fn leftValue() -> Int { return leafValue(); };")
    , ("assembly/right/right.tersus", "import assembly::leaf { leafValue }; fn rightValue() -> Int { return leafValue(); };")
    , ("assembly/leaf/leaf.tersus", "struct LeafShadow { n: Int }; fn leafValue() -> Int { s = \"leaf\"; return size(s.bytes) + LeafShadow { n: 1 }.n; };")
    , ("vendor/package.tersus", "noPrelude = true;")
    , ("vendor/api/api.tersus", "fn vendorValue() -> Int { return 2; };")
    ]

assemblySnapshot :: Mod.Snapshot
assemblySnapshot = Mod.Snapshot (Mod.resolverFromFiles assemblyFiles) "assembly/main.tersus" False

packageRequest :: LoadRequest
packageRequest = Mod.loadRequest (LoadPackageAssembly (Mod.entryModuleOf assemblySnapshot)) assemblySnapshot

packageAssembly :: LibPackage -> Either String ()
packageAssembly pkg = do
    let root = ModuleId "assembly" Nothing
        leaf = ModuleId "assembly" (Just "leaf")
        vendor = ModuleId "vendor" (Just "api")
        names = ["types", "clone", "eq", "prelude", "string"]
        request = packageRequest{lrLibraries = libCatalog pkg}
        answer = bootstrapLoader request
    case answer of
        AssembledPackage entry rows answers -> do
            require (entry == root && rows == [(name, leaf) | name <- names]) ("unexpected package recipe: " ++ show (entry, rows))
            require ([selected | (m, _, Accepted _ selected _) <- answers, m == vendor] == [[]]) "the noPrelude dependency selected implicit libraries"
        other -> Left ("expected package assembly: " ++ take 250 (show other))
    let capture rq
            | rq == request = answer
            | otherwise = NotLoaded "wrong request for the stage catalog"
    compiled <- resultEither (Package.compileModulesUsing capture (Ok pkg) assemblySnapshot)
    leafLowered <- case [Package.compiledLowered m | m <- Package.compiledModules compiled, Package.compiledModuleId m == leaf] of
        [found] -> resultEither found
        _ -> Left "missing leaf"
    private <- maybe (Left "missing canonical LeafShadow") Right (find ("$LeafShadow" `isSuffixOf`) (Set.toList (M.lowDeclared leafLowered)))
    cached <- lookupOr "cached string unit" "string" (libPrograms pkg)
    let sentinel = M.StructDecl []
        withRootShadow = cached{M.progTypes = Map.insert "Box" sentinel (M.progTypes cached)}
        withBoth = withRootShadow{M.progTypes = Map.insert private sentinel (M.progTypes withRootShadow)}
        injected = pkg{libPrograms = Map.insert "string" withBoth (libPrograms pkg)}
    cutover <- resultEither (Package.compileModulesUsing capture (Ok injected) assemblySnapshot)
    (libraries, units) <- resultEither (Package.packageLinkInputs cutover)
    types <- lookupOr "cached types unit" "types" (libPrograms pkg)
    let storage = Map.restrictKeys (M.progGenerics types) (Set.fromList ["List", "Box"])
        expectedUnit name = (,) (libModuleId name) <$> case name of
            "types" -> Right types{M.progCaptureStorage = storage}
            "string" -> Right withRootShadow
            _ -> lookupOr "cached unit" name (libPrograms pkg)
    expected <- traverse expectedUnit names
    require (libraries == expected) "library units did not keep only the first contributor's exclusions"
    require (Map.keysSet storage == Set.fromList ["List", "Box"] && Map.null (M.progCaptureStorage types)) "only the selected types unit should gain compiler storage provenance"
    let stripped = stripDeclaredFromUnits ["Box"] libraries
    require (map (Map.keys . M.progCaptureStorage . snd) stripped == [["List"], [], [], [], []]) "shadowing Box must also remove its storage provenance"
    require (map fst units == [leaf, ModuleId "assembly" (Just "left"), ModuleId "assembly" (Just "right"), vendor, root]) ("unexpected Link unit order: " ++ show (map fst units))

packageDecoderRefusals :: Either String ()
packageDecoderRefusals = do
    let dep = ["module \"assembly\" \"leaf\"", "lowering 0"]
        entry = ["module \"assembly\" none", "lowering 0", "refused \"later module refused\"", "end"]
        refused = map B.pack (responseHeader : dep ++ ["refused \"earlier module refused\""] ++ entry)
    case readLoadResponseBytes packageRequest refused of
        Error "ElaborateRequest: expected end after a module refusal" -> pure ()
        _ -> Left "the package decoder accepted another module after a terminal refusal"
    earlier <- responseRecords (Accepted Nothing [] (MirRefused "deliberate lowering refusal"))
    case readLoadResponseBytes packageRequest (map B.pack (responseHeader : dep ++ earlier ++ entry)) of
        Ok (LoadedModules [(_, _, Accepted _ _ (MirRefused "deliberate lowering refusal")), (_, _, Refused "later module refused")]) -> pure ()
        _ -> Left "the package decoder stopped at an accepted lowering refusal"

checkedPackageAssembly :: IO TestResult
checkedPackageAssembly = case fixture of
    Left e -> pure (Just e)
    Right (pkg, request, malformed) -> do
        tmp <- getTemporaryDirectory
        bracket (openTempFileCloexec tmp "tersus-assembly-reply") (removeFile . fst) $ \(exe, handle) -> do
            B.hPutStr handle (B.unlines (map B.pack ["#!/bin/sh", "cat >/dev/null", "cat <<'ASSEMBLY_REPLY'"] ++ malformed ++ [B.pack "ASSEMBLY_REPLY"]))
            hClose handle
            setFileMode exe 0o700
            evaluate $ case Package.compileModulesUsing (\rq -> nativeLoader exe rq{lrProtocols = lrProtocols request}) (Ok pkg) snapshot of
                Error "Elaborator tool failure: AstData: unknown header" -> Nothing
                other -> Just ("expected malformed checked ownership to fail as a tool: " ++ take 250 (show other))
  where
    loader rq = bootstrapLoader rq{lrProtocols = Just Map.empty}
    snapshot = Mod.Snapshot (Mod.resolverFromFiles
        [ ("checked/package.tersus", "")
        , ("checked/dep/dep.tersus", "fn seed() -> Int { return 2; };")
        , ("checked/main.tersus", "import checked::dep { seed }; struct Cell { n: Int }; c = Cell { n: seed() }; xs = [c.n]; return size(xs);")
        ]) "checked/main.tersus" False
    fixture = do
        pkg <- resultEither (compileLibPackageWith loader)
        let request = (Mod.loadRequest (LoadPackageAssembly (Mod.entryModuleOf snapshot)) snapshot){lrLibraries = libCatalog pkg, lrProtocols = Just Map.empty}
        compiled <- resultEither (Package.compileModulesUsing loader (Ok pkg) snapshot)
        (libraries, _) <- resultEither (Package.packageLinkInputs compiled)
        require (not (null libraries) && all ((/= Nothing) . Package.compiledOwnership) (Package.compiledModules compiled))
            "checked assembly discarded ownership facts or library units"
        case loader request of
            AssembledPackage _ _ [(_, _, AcceptedData depIface depLibs _ (Just depFacts)), (_, _, AcceptedData iface names mir (Just facts))] -> do
                require (Map.member "Cell" (transportOwnership facts)) "checked fixture lacks a Cell ownership row"
                dep <- responseRecords (AcceptedData depIface depLibs (MirRefused "earlier lowering refusal") (Just depFacts))
                body <- responseRecords (AcceptedData iface names mir (Just facts{transportOwnership = Map.delete "Cell" (transportOwnership facts)}))
                let start = [responseHeader, "module \"checked\" \"dep\"", "lowering 0"] ++ dep ++ ["module \"checked\" none", "lowering 1 \"checked\" \"dep\""]
                    wire rows = map B.pack (start ++ rows ++ ["end"])
                decoded <- resultEither (readLoadResponseBytes request (wire body) `bindResult` loadTransportMatches True)
                case Package.compileModulesUsing (const decoded) (Ok pkg) snapshot `bindResult` Package.lowerCompiledPackage of
                    Error "in module checked: the ownership facts omit the declared types Cell" -> pure ()
                    other -> Left ("expected missing ownership to beat deferred lowering: " ++ take 250 (show other))
                let header = "tersus-ast 2 ownership"
                    malformed = wire [if line == header then "malformed ownership header" else line | line <- body]
                case readLoadResponseBytes request malformed of
                    Error "AstData: unknown header" -> Right (pkg, request, malformed)
                    _ -> Left "the package decoder did not reject malformed ownership"
            other -> Left ("expected two checked module answers: " ++ take 250 (show other))

responseRecords :: Response -> Either String [String]
responseRecords = fmap (drop 1 . lines) . resultEither . writeResponse

standaloneAssembly :: LibPackage -> Either String ()
standaloneAssembly pkg = do
    mapM_ checkNames
        [ ("xs = [1]; return size(xs);", ["types", "clone", "eq"])
        , ("struct Box { n: Int }; b = Box { n: 2 }; s = \"hi\"; return b.n + size(s.bytes);", ["clone", "eq", "prelude", "string"])
        , ("trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; }; s = \"hi\"; return size(s.bytes);", ["types", "clone", "eq", "prelude", "string"])
        ]
    cached <- lookupOr "cached string unit" "string" (libPrograms pkg)
    let source = "fn f() -> Int { struct Shape { n: Int }; return 3; }; s = \"hi\"; return f() + size(s.bytes);"
        marker = "AssemblyFixtureType"
        sentinel = M.StructDecl []
        conflicting = cached{M.progTypes = Map.insert marker sentinel (Map.insert "Shape" sentinel (M.progTypes cached))}
        fixture = pkg{libPrograms = Map.insert "string" conflicting (libPrograms pkg)}
        answer = bootstrapLoader (request source)
    case answer of
        AssembledProgram names response -> do
            l <- resultEither (lowerAccepted response)
            require ("string" `elem` names && Set.member "Shape" (M.lowNested l) && Set.notMember "Shape" (M.lowDeclared l)) "the standalone fixture needs a nested library shadow"
        other -> Left ("expected standalone assembly: " ++ take 250 (show other))
    base <- resultEither (lowerSourceUsing (const answer) (Ok pkg) False False source)
    got <- resultEither (lowerSourceUsing (const answer) (Ok fixture) False False source)
    require (got == base{M.progTypes = Map.insert marker sentinel (M.progTypes base)}) "standalone Link did not apply the nested shadow to the supplied cache"
  where
    request = sourceRequest LoadProgramAssembly False False (libCatalog pkg)
    checkNames (source, expected) = case bootstrapLoader (request source) of
        AssembledProgram names _ -> require (names == expected) ("unexpected standalone assembly: " ++ show names)
        other -> Left ("expected standalone assembly: " ++ take 250 (show other))

assemblyRefusals :: LibPackage -> Either String ()
assemblyRefusals pkg = do
    let broken = Mod.Snapshot (Mod.resolverFromFiles [(file, if file == "assembly/main.tersus" then "import assembly::leaf; return wrongName;" else source) | (file, source) <- assemblyFiles]) "assembly/main.tersus" False
        err = Error "deliberate library failure"
        noGraph rq | lrKind rq == LoadGraph = NotLoaded "graph unavailable"
                   | otherwise = bootstrapLoader rq
        refuse r expected = require (message r == Just expected) ("expected " ++ show expected ++ ", got " ++ show (message r))
    refuse (Package.compileModulesUsing bootstrapLoader (Ok pkg) broken) "in module assembly: Undefined variable: wrongName"
    refuse (Package.compileModulesUsing bootstrapLoader err broken) "in module assembly::leaf: deliberate library failure"
    refuse (Package.compileModulesUsing noGraph err broken) "in module assembly::leaf: deliberate library failure"
    let vendorFirst = Mod.Snapshot (Mod.resolverFromFiles [(file, if file == "assembly/main.tersus" then "import vendor::api; return wrongName;" else source) | (file, source) <- assemblyFiles]) "assembly/main.tersus" False
    refuse (Package.compileModulesUsing bootstrapLoader err vendorFirst) "in module assembly: deliberate library failure"
    refuse (Package.compileModulesUsing noGraph err vendorFirst) "in module vendor::api: deliberate library failure"
    refuse (Package.compileModulesUsing bootstrapLoader err (assemblySnapshot{Mod.snapshotEntry = "unrelated/missing.tersus"})) "file not found: unrelated/missing.tersus"
    let denied = "return unknownVariable;"
    refuse (lowerSourceUsing bootstrapLoader err True False denied) "Validation failed: Undefined variable: unknownVariable"
    case bootstrapLoader packageRequest{lrLibraries = libCatalog pkg} of
        AssembledPackage root _ ((m, deps, Accepted iface selected _) : rest) -> do
            let refused = (m, deps, Accepted iface selected (MirRefused "deliberate lowering refusal"))
                lower answers = Package.compileModulesUsing (const (LoadedModules answers)) (Ok pkg) assemblySnapshot `bindResult` Package.lowerCompiledPackage
            refuse (lower (refused : rest)) "Lowering failed: deliberate lowering refusal"
            refuse (lower [refused, (root, [], Refused "later module refused")]) "in module assembly: later module refused"
            refuse (lower [refused, (root, [], Accepted Nothing [] (MirRefused "unused"))]) "in module assembly: the elaborator gave no interface"
        other -> Left ("expected complete package to mutate: " ++ take 250 (show other))
  where
    message (Error e) = Just e
    message Ok{} = Nothing

runAssembly :: FilePath -> LoadRequest -> IO (Result [B.ByteString] String)
runAssembly path request = case writeLoadRequest request of
    Error e -> pure (Error e)
    Ok text -> runElaboratorRaw path text

checkMalformedAssembly :: LoadRequest -> Result [B.ByteString] String -> Either String ()
checkMalformedAssembly request wire = do
    records <- resultEither wire
    let (prefix, trailer) = break (B.pack "assembly " `B.isPrefixOf`) records
        legacy = request{lrKind = LoadPackage}
    case map B.unpack trailer of
        header : a : b : more -> do
            let mutateRow name p m = unwords ["library", show name, show p, m]
                malformed =
                    [ ("missing", [])
                    , ("leading zero", unwords (init (words header) ++ ["0" ++ last (words header)]) : a : b : more)
                    , ("overlong", header : a : b : more ++ ["extra"])
                    , ("duplicate library", header : a : a : more)
                    , ("catalog order", header : b : a : more)
                    , ("unknown entry", ["assembly \"someone\" none 0"])
                    , ("overlarge count", unwords (init (words header) ++ [show (toInteger (maxBound :: Int) + 1)]) : a : b : more)
                    , ("unknown library", header : mutateRow "missing" "assembly" "\"leaf\"" : b : more)
                    , ("unknown contributor", header : mutateRow "types" "missing" "none" : b : more)
                    , ("contributor order", header : unwords (take 2 (words a) ++ ["\"assembly\"", "none"]) : b : more)
                    ]
            require (isError (readLoadResponseBytes legacy records)) "ordinary loader accepted an unsolicited recipe"
            mapM_ (\(what, rows) -> require (isError (readLoadResponseBytes request (prefix ++ map B.pack rows))) ("accepted " ++ what ++ " assembly")) malformed
        _ -> Left "assembly fixture did not give enough library rows"
  where
    isError Error{} = True
    isError _ = False

malformedAssemblyRequests :: FilePath -> LoadRequest -> LoadRequest -> IO TestResult
malformedAssemblyRequests path full bare = case traverse (resultEither . writeLoadRequest) [full, bare, full{lrLibraries = take 1 (lrLibraries full) ++ lrLibraries full}] of
    Right [withCatalog, noCatalog, duplicate] -> do
        let opt text = case break (== '\n') text of
                (header, rest) -> header ++ "\nload program assembly" ++ drop (length "\nload program") rest
            cases = [("duplicate catalog name", opt duplicate)]
                ++ [(label ++ suffix, opt request ++ invalid)
                   | (label, invalid) <- [("unterminated quote", "\"unterminated\n"), ("non-record byte", "\x01\n"), ("empty record", "\n")]
                   , (suffix, request) <- [(" after catalog", withCatalog), (" without catalog", noCatalog)]]
        failures <- traverse (\(label, request) -> do
            answer <- runElaboratorRaw path request
            pure $ case answer of
                Error e | "not an elaboration request" `isInfixOf` e -> Nothing
                _ -> Just (label ++ " was not rejected as a malformed request: " ++ take 200 (show answer))) cases
        pure (firstFailure failures)
    Left e -> pure (Just e)
    _ -> pure (Just "missing malformed assembly request fixtures")

lookupOr :: Ord k => String -> k -> Map.Map k a -> Either String a
lookupOr label key = maybe (Left ("missing " ++ label)) Right . Map.lookup key

resultEither :: Result a String -> Either String a
resultEither (Ok a) = Right a
resultEither (Error e) = Left e

require :: Bool -> String -> Either String ()
require True _ = Right ()
require False e = Left e

check :: Either String () -> TestResult
check = either Just (const Nothing)

firstFailure :: [TestResult] -> TestResult
firstFailure = foldr (\r rest -> maybe rest Just r) Nothing

testDifferential :: Test
testDifferential = TestList "testDifferential"
    [ TestCase "requests and responses read back as written" protocolRoundTrip
    , TestCase "a candidate's mistakes are not agreements" mutationControls
    , TestCase "the text protocol loses nothing" protocolAgreement
    , testCase "functions with bounds of the libraries in front of a program are checked too" checkedStatements
    , TestCase "assembly preserves ordered Link inputs and refusals" assemblyContract
    , TestCase "malformed load requests are not answered" malformedLoads
    , testCase "the mir section reads back, and a unit that does not read is a tool failure" mirSection
    , TestCase "the elaborator's refusal words, arena checks and renumbering" elaboratorChecks
    ]
