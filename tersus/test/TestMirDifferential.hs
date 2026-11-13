-- The differential of the lowering written in Tersus (REPLACING_HASKELL.md, "MIR lowering in Tersus"): for every
-- unit the compiler lowers from the corpus, the MIR the elaborator gives with its answer is the unit the Haskell
-- lowering makes of the same answer (compareLowered), and a refusal is worded the same. A unit that is
-- changed after the elaborator gave it is caught.
module TestMirDifferential (testMirDifferential) where

import qualified Data.ByteString.Char8 as B
import Data.Char (ord)
import Data.List (isInfixOf, isPrefixOf, sort)
import qualified Data.Map.Strict as Map
import Numeric (showHex)

import Compile (sourceRequest)
import Differential (Unit (..), suiteUnits, toolPackages)

import ElaborateRequest (LibraryAnswer (..), LoadKind (..), LoadRequest (..), LoadResponse (..), MirAnswer (..), Response (..), readResponse, responseMir, writeResponse)
import DataCodec (typeTokens)
import ElaboratorTool (noVerdict, sourceLoader)
import LibPackage (libCatalog, libPackage, libSelection, withoutReplacedEq)
import Lowering (lowerAccepted)
import Mir
import MirData (readLoweredBytes, writeLowered)
import MirEval (Outcome (..), RunEnv (..), runProgramEnv)
import MirHousekeeping (validationEntry)
import qualified Modules as Mod
import qualified PackageCompile as Package
import qualified ParserSeed
import Pretty (renderType)
import PreludeSource (elaboratePackageFiles, nativeStorageModules, toolPackageFiles, validationPackageFiles)
import qualified Syntax as S
import Types
import TestHarness
import TestVariadic (variadicPrograms)
import Utils

testMirDifferential :: Test
testMirDifferential =
    TestList
        "testMirDifferential"
        [ TestParallel
            "corpus"
            ( TestCase "examples" (unitsAgree =<< suiteUnits)
                : [TestCase entry (unitsAgree [EmbeddedPackage entry]) | entry <- toolPackages]
            )
        , TestCase "a lowercase Unicode type argument" (unitsAgree [SourceText "unicode" "struct caf\233 { x: Int };\nv = (caf\233 { x: 1 }, 0);\nreturn 0;\n"])
        , TestCase "functions of an impl with bounds of their own" (unitsAgree [SourceText ("impl bounds " ++ show i) (showSize ++ body) | (i, body) <- zip [1 :: Int ..] implBounds])
        , TestCase "variadic functions" (unitsAgree [SourceText ("variadic: " ++ name) source | (name, source) <- variadicPrograms ++ variadicLowering])
        , TestCase "a changed unit is caught" changedUnitsDiffer
        , TestCase "the mir section reads back" mirSectionFraming
        , TestCase "a tool failure or a missing library is not a refusal" incompleteAnswersFail
        , TestCase "refusals name types and strings as Haskell does" refusalWords
        ]

-- How the elaborator's MIR compares with the Haskell lowering of the same response
data LoweringComparison = Same | Differs String | Absent
    deriving (Show, Eq)

-- (Lowered's Eq ignores the metadata of builtins, so the units are compared by show as well)
compareLowered :: Result Lowered String -> Maybe MirAnswer -> LoweringComparison
compareLowered _ Nothing = Absent
compareLowered haskell (Just mir) = case (haskell, tersus) of
    (Ok a, Ok b)
        | a == b && show a == show b -> Same
        | otherwise -> Differs ("the units differ\n--- haskell\n" ++ either' (writeLowered a) ++ "\n--- tersus\n" ++ tersusText)
    (Error a, Error b)
        | a == b -> Same
        | otherwise -> Differs ("the refusals differ\n--- haskell\n" ++ a ++ "\n--- tersus\n" ++ b)
    (Ok a, Error b) -> Differs ("only the elaborator refuses\n--- haskell\n" ++ either' (writeLowered a) ++ "\n--- tersus\n" ++ b)
    (Error a, Ok _) -> Differs ("only the Haskell lowering refuses\n--- haskell\n" ++ a ++ "\n--- tersus\n" ++ tersusText)
  where
    tersus = case mir of
        MirLowered ls -> readLoweredBytes ls
        MirRefused message -> Error message
    tersusText = case mir of
        MirLowered ls -> B.unpack (B.unlines ls)
        MirRefused message -> message
    either' r = case r of
        Ok t -> t
        Error e -> "(not written: " ++ e ++ ")"

-- One lowering the compiler makes of a unit: its module, the Haskell lowering, and the elaborator's MIR
type Compared = (String, Result Lowered String, Maybe MirAnswer)

unitsAgree :: [Unit] -> IO TestResult
unitsAgree units = do
    found <- mapM unitComparisons units
    pure $ case sequence [resultEither r | r <- found] of
        Left e -> Just e
        Right lists ->
            let all' = concat lists
                outcomes = [(label, compareLowered haskell mir) | (label, haskell, mir) <- all']
                same = length [() | (_, Same) <- outcomes]
             in case [(label, o) | (label, o) <- outcomes, o /= Same] of
                    (label, o) : _ -> Just (label ++ ": " ++ take 4000 (show o))
                    [] | same > 0 -> Nothing
                    [] -> Just "no unit was compared"
  where
    resultEither r = case r of
        Ok a -> Right a
        Error e -> Left e

unitComparisons :: Unit -> IO (Result [Compared] String)
unitComparisons unit = case unit of
    SourceFile path -> sourceComparison path <$> readFile path
    SourceText label source -> pure (sourceComparison label source)
    EmbeddedPackage entry -> pure (packageComparisons (if entry == validationEntry then validationPackageFiles else toolPackageFiles) entry)
    FilePackage entry -> (`packageComparisons` entry) <$> Mod.snapshotFromFilesystem entry
    Libraries -> pure libraryComparisons
  where
    -- (as Compile.lowerSourceUsing asks and lowers)
    sourceComparison path source = libPackage `bindResult` \pkg -> case sourceLoader (sourceRequest LoadProgram False True (libCatalog pkg) source) of
        LoadedProgram response@(Accepted (S.Elaborated stmts _) _ selected) ->
            let ifaces = withoutReplacedEq stmts (if null selected then [] else fst (libSelection pkg selected))
             in Ok [(path, lowerAccepted ifaces response, responseMir response)]
        -- (only the examples under examples/rejected may be refused; a refusal that is no verdict fails)
        LoadedProgram (Refused message) | refusable path message -> Ok []
        NotLoaded message | refusable path message -> Ok []
        Unparsed message | refusable path message -> Ok []
        other -> Error (path ++ ": not accepted: " ++ take 2000 (show other))

    packageComparisons files entry =
        mapResult
            (\compiled -> [(Mod.renderModuleId (Package.compiledModuleId m), Package.compiledLowered m, Package.compiledMir m) | m <- Package.compiledModules compiled])
            (Package.compileModulesUsing sourceLoader libPackage (Mod.Snapshot (Mod.resolverFromFiles files) entry False))
    -- (as LibPackage lowers each library against the interfaces of the libraries it imports)
    libraryComparisons = libraryOutcome (sourceLoader librariesRequest)

showSize :: String
showSize = "trait Show { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; trait Size { fn measure(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; struct Cell { v: Int }; impl Show for Cell { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; impl Size for Cell { fn measure(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 2; }; }; "

-- (TestTraits's programs)
implBounds :: [String]
implBounds =
    [ "struct Acc { total: Int }; impl Acc { fn add<T: Size>(self: &Acc, t: &T) -> Acc { return Acc { total: self.total + t.measure() }; }; fn of<T: Size>(t: &T) -> Acc { return Acc { total: t.measure() }; }; fn plain(self: &Acc) -> Int { return self.total; }; }; a = Acc::of(Cell { v: 0 }); b = a.add(Cell { v: 0 }); c = Acc::add(b, Cell { v: 0 }); return c.plain();"
    , "struct Pair<T> { a: T, b: T }; impl<T: Show> Pair<T> { fn both(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return self.a.show() + self.b.show(); }; fn with<U: Size>(self: &Self, u: &U) -> Int [{ }] [{ affirm return >= 0; }] { return self.both() + u.measure(); }; fn take<U: Size>(self: Self, u: U) -> Int [{ }] [{ affirm return >= 0; }] { fn inner(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return >= 0; }] { return x + 1; }; return inner(self.a.show() + u.measure()); }; fn make<U: Size>(a: T, b: T, u: &U) -> Self { return Self { a: a, b: b }; }; }; p = Pair::make(Cell { v: 0 }, Cell { v: 1 }, Cell { v: 2 }); x = p.with(Cell { v: 3 }); y = Pair::with(p, Cell { v: 4 }); z = p.take(Cell { v: 5 }); return x * 100 + y * 10 + z;"
    , "struct Counter { n: Int }; impl Counter { fn bump<U: Size>(self: &mut Self, u: &U) -> Int writes(self.n) [{ }] [{ }] { (*self).n = (*self).n + u.measure(); return 0; }; }; c = Counter { n: 1 }; Counter::bump(&mut c, Cell { v: 0 }); Counter::bump(&mut c, Cell { v: 0 }); return c.n;"
    ]

-- Only the examples under examples/rejected may be refused, and not by a tool that failed
refusable :: FilePath -> String -> Bool
refusable path message = "examples/rejected/" `isPrefixOf` path && not (noVerdict message || ParserSeed.toolFailure message)

librariesRequest :: LoadRequest
librariesRequest = LoadRequest LoadLibraries False (Mod.resolverFromFiles []) Nothing Mod.librarySources []

-- Every compiler library asked for, each accepted, compared
libraryOutcome :: LoadResponse -> Result [Compared] String
libraryOutcome response = case response of
    LoadedLibraries answers Nothing
        | sort [laName a | a <- answers] /= sort [name | (name, _, _) <- Mod.librarySources] -> Error ("the compiler libraries answered are " ++ show [laName a | a <- answers])
        | otherwise -> libraries Map.empty answers
    LoadedLibraries _ (Just failure) -> Error ("the compiler libraries do not load: " ++ show failure)
    _ -> Error "the loader did not answer with the compiler libraries"
  where
    libraries _ [] = Ok []
    libraries known (LibraryAnswer label imports _ response : rest) = case response of
        Accepted _ (Just iface) _ ->
            let known' = if label `elem` nativeStorageModules then known else Map.insert label iface known
             in mapResult (("tersuslib::" ++ label, lowerAccepted [i | dep <- imports, Just i <- [Map.lookup dep known]] response, responseMir response) :) (libraries known' rest)
        other -> Error ("tersuslib::" ++ label ++ ": not accepted: " ++ take 2000 (show other))

incompleteAnswersFail :: IO TestResult
incompleteAnswersFail = pure $ firstFailure
    [ if refusable "examples/rejected/x.tersus" "Parser tool failure: the seed does not build" then Just "a parser tool failure is taken for a refusal" else Nothing
    , if refusable "examples/rejected/x.tersus" "Elaborator tool failure: it stopped" then Just "an elaborator tool failure is taken for a refusal" else Nothing
    , if refusable "examples/x.tersus" "Type error: no" then Just "an example outside examples/rejected may be refused" else Nothing
    , case sourceLoader librariesRequest of
        LoadedLibraries answers Nothing | not (null answers) -> case libraryOutcome (LoadedLibraries (init answers) Nothing) of
            Error _ -> Nothing
            Ok _ -> Just "an answer missing a library is taken as whole"
        other -> Just ("the libraries did not load: " ++ take 400 (show other))
    ]

-- The lowering's refusal words for types (Pretty.renderType) and for the names and types in a builtin (Haskell's show),
-- from the elaborator's own functions run on a table of types and strings (the elaborator with this table as its program)
refusalWords :: IO TestResult
refusalWords = pure $ case Mod.loadFromEntry (Mod.resolverFromFiles files) entry of
    _ | length [() | (path, text) <- elaboratePackageFiles, path == entry, marker `elem` lines text] /= 1 -> Just "the elaborator's program does not start where expected"
    Left err -> Just err
    Right (Mod.PackageResult pkg) -> case Package.compileModulesLinked (Mod.packageSnapshot pkg) `bindResult` runProgramEnv RunEnv{envArgs = [], envInput = "", envFile = const Nothing} of
        Error err -> Just err
        Ok outcome ->
            let expected = [line | ty <- types, line <- [show ty, renderType ty]] ++ map show strings
             in firstFailure [if a == e then Nothing else Just ("expected " ++ e ++ ", got " ++ a) | (e, a) <- zip expected (lines (decodeUtf8 (outStdout outcome)) ++ repeat "(nothing)")]
    Right _ -> Just "the fixture is standalone"
  where
    entry = "lib/elaborate/elaborate.tersus"
    marker = "header = readLine();"
    files = [(path, if path == entry then unlines (map imported (takeWhile (/= marker) (lines text))) ++ source else text) | (path, text) <- elaboratePackageFiles]
    imported l
        | "import data::codec::codec { " `isPrefixOf` l = "import data::codec::codec { typeAt, " ++ drop (length "import data::codec::codec { ") l
        | "import elaborate::lowerout " `isPrefixOf` l = l ++ "\nimport elaborate::lowerbuild { lwShow, hsShowType };\nimport elaborate::lowerstate { fromCodecTy, newLowSt, renderTy };"
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
            , "    ls = fromCodecTy(newLowSt(0), &ty.value);"
            , "    return n + wordsLine(renderTy(&ls, ls.ty));"
            , "};"
            , "words = 0;"
            ]
                ++ ["words = words + wordsShown(" ++ literal (unwords (typeTokens ty)) ++ ");" | ty <- types]
                ++ ["text = " ++ literal text ++ "; words = words + wordsLine(lwShow(&text));" | text <- strings]
                ++ ["return 0;"]
    literal text = "\"" ++ concatMap escape text ++ "\""
    escape c
        | c == '"' = "\\\""
        | c == '\\' = "\\\\"
        | ord c >= 32 && ord c < 127 = [c]
        | otherwise = "\\u{" ++ showHex (ord c) "" ++ "}"

-- A refusal, and a section whose count runs past the response, read back as written
mirSectionFraming :: IO TestResult
mirSectionFraming = pure $ case sourceLoader (sourceRequest LoadProgram False True [] "return 1;\n") of
        LoadedProgram (AcceptedWith e iface libs _) ->
            let refusal = "a \"quoted\" refusal"
             in case writeResponse (AcceptedWith e iface libs (Just (MirRefused refusal))) of
                    Error err -> Just err
                    Ok text -> firstFailure
                        [ case readResponse text of
                            Ok r | Just (MirRefused m) <- responseMir r, m == refusal -> Nothing
                            other -> Just ("a refusal read back as " ++ take 400 (show other))
                        , case readResponse (unlines (map overlong (lines text))) of
                            Error err | "malformed mir section" `isInfixOf` err -> Nothing
                            other -> Just ("an overlong mir section read as " ++ take 400 (show other))
                        ]
        other -> Just ("expected an accepted answer, got " ++ take 400 (show other))
  where
    overlong line
        | "mir refused " `isPrefixOf` line = "mir 1000"
        | otherwise = line

-- A unit of the elaborator's with a SwitchBool's targets swapped, and one with a ghost statement dropped, is not the
-- Haskell lowering's
changedUnitsDiffer :: IO TestResult
changedUnitsDiffer = do
    found <- unitComparisons (SourceFile "examples/branching.tersus")
    pure $ case found of
        Error e -> Just e
        Ok [(_, haskell, Just (MirLowered ls))] -> case readLoweredBytes ls of
            Error e -> Just ("the elaborator's unit does not read: " ++ e)
            Ok unit ->
                firstFailure
                    [ if compareLowered haskell (Just (MirLowered ls)) == Same then Nothing else Just "the unit itself is not the Haskell lowering's"
                    , changed "a swapped switch" (mapBlocks swapFirstSwitch unit)
                    , changed "a dropped ghost" (mapBlocks dropFirstGhost unit)
                    ]
              where
                changed label mutated
                    | mutated == unit = Just (label ++ ": the program has nothing to change")
                    | otherwise = case writeLowered mutated of
                        Error e -> Just (label ++ ": not written: " ++ e)
                        Ok text -> case compareLowered haskell (Just (MirLowered (B.lines (B.pack text)))) of
                            Differs _ -> Nothing
                            other -> Just (label ++ ": compared as " ++ show other)
        Ok other -> Just ("expected one lowering with MIR, got " ++ show (length other))

-- The first function (main last) whose blocks the change changes, changed
mapBlocks :: ([BasicBlock] -> Maybe [BasicBlock]) -> Lowered -> Lowered
mapBlocks change unit =
    let program = lowProgram unit
        fns = Map.elems (progFunctions program) ++ [progMain program]
        changedFn f = fmap (\bs -> f{fnBlocks = Map.fromList (zip (Map.keys (fnBlocks f)) bs)}) (change (Map.elems (fnBlocks f)))
     in case [(f, f') | f <- fns, Just f' <- [changedFn f]] of
            (f, f') : _
                | fnName f == fnName (progMain program) && Map.notMember (fnName f) (progFunctions program) -> unit{lowProgram = program{progMain = f'}}
                | otherwise -> unit{lowProgram = program{progFunctions = Map.insert (fnName f) f' (progFunctions program)}}
            [] -> unit

swapFirstSwitch :: [BasicBlock] -> Maybe [BasicBlock]
swapFirstSwitch blocks = case break isSwitch blocks of
    (before, BasicBlock stmts (SwitchBool o yes no) : after) | yes /= no -> Just (before ++ BasicBlock stmts (SwitchBool o no yes) : after)
    _ -> Nothing
  where
    isSwitch (BasicBlock _ t) = case t of
        SwitchBool _ yes no -> yes /= no
        _ -> False

dropFirstGhost :: [BasicBlock] -> Maybe [BasicBlock]
dropFirstGhost blocks = case break hasGhost blocks of
    (before, BasicBlock stmts t : after) -> Just (before ++ BasicBlock (dropGhost stmts) t : after)
    _ -> Nothing
  where
    hasGhost (BasicBlock stmts _) = any isGhost stmts
    isGhost s = case s of
        Ghost _ _ -> True
        _ -> False
    dropGhost stmts = let (a, b) = break isGhost stmts in a ++ drop 1 b

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [e | Just e <- results] of
    e : _ -> Just e
    [] -> Nothing

-- Variadic functions whose lowering the programs of TestVariadic do not reach: a borrow of an element at a number, a range
-- loop past the pack, validation statements that read the pack, and a pack loop after a return
variadicLowering :: [(String, String)]
variadicLowering =
    [ ("a borrow of an element at a number", "fn sz<T>(r: &T) -> Int { return 1; }; fn f<..T>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] {\n    r = &get(args, 0);\n    return sz(r);\n};\nreturn f(1, true);")
    , ("a range loop past the pack", "fn f<..T>(args: &..T) -> Int {\n    t = 0;\n    for i in 0..size(args) + 1 { t = t + i; };\n    return t;\n};\nreturn f(1, true);")
    , ("validation statements that read the pack", "fn f<..T>(args: &..T) -> Int {\n    affirm size(args) >= 0;\n    define n = size(args);\n    return n;\n};\nreturn f(1, true);")
    , ("a loop over the pack after a return", "fn f<..T>(args: &..T) -> Int {\n    return 0;\n    for a in args { };\n};\nreturn f(1);")
    , ("a slice forwarded after a fixed argument", "fn g<..U>(k: Int, rest: &..U) -> Int { return k + size(rest); };\nfn f<..T>(args: &..T) -> Int [{ affirm size(args) >= 2; }] [{ }] {\n    return g(10, slice(args, 1, 2));\n};\nreturn f(1, true);")
    , ("the head and the rest forwarded by value in one call", "fn eat<T>(x: T) -> Int { return 1; };\nfn g<A, ..U>(x: A, rest: ..U) -> Int { n = eat(x); for a in rest { n = n + eat(a); }; return n; };\nfn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] {\n    return g(get(args, 0), slice(args, 1, size(args)));\n};\nreturn f(push([], 1), push([], 2));")
    , ("a forward in a loop over the pack", "fn g<..U>(rest: &..U) -> Int { return size(rest); };\nfn f<..T>(args: &..T) -> Int {\n    t = 0;\n    for i in 0..size(args) { t = t + g(slice(args, i, size(args))); };\n    return t;\n};\nreturn f(1, 2, 3);")
    ]
