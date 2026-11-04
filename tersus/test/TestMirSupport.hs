module TestMirSupport (testMirSupport) where

import Data.Char (ord)
import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Interface as I
import Link (linkPrograms)
import qualified Mir as M
import MirEval (MirValue (..), runNamedFunction)
import MirLower (lowerModuleWith)
import qualified Modules as Mod
import qualified PackageCompile as Package
import PreludeSource (mirPackageFiles)
import TestHarness (Test (..), TestResult, testAssertEq, testAssertErrorContains, testCase)
import Types (Type (..), Arg (..), Signature (..))
import Utils (Result (..), bindResult, mapResult)

testMirSupport :: Test
testMirSupport = TestList "testMirSupport"
    [ TestList "actual tool snapshots"
        [ TestList name
            [ testCase "one loaded and compiled support dependency" (inspect snapshot dependencyGraph)
            , testCase "shared definitions and Clone implementations have one owner" (inspect snapshot definitionOwners)
            , testCase "canonical codec and reader types cross the interface" (inspect snapshot canonicalTypes)
            , testCase "borrowed inputs and owned results survive lowering" (inspect snapshot borrowedMetadata)
            , testCase "phase layout calls shared symbols directly without forwarding" (inspect snapshot directCalls)
            , testCase "support unit identity deduplicates only identical units" (inspect snapshot supportUnitIdentity)
            ]
        | (name, snapshot) <- toolSnapshots
        ]
    , TestList "rendering matches pre-extraction outputs"
        ([ testCase ("size " ++ label) (callSupport "renderSize" [value] (text expected))
         | (label, value, expected) <- sizeCases
         ] ++
         [ testCase ("type " ++ label) (callSupport "renderType" [value] (text expected))
         | (label, value, expected) <- typeCases
         ] ++
         [ testCase ("escaped " ++ label) (callSupport "escaped" [value] (text expected))
         | (label, value, expected) <- escapedCases
         ] ++
         [ testCase "noStrings empty" (callSupport "noStrings" [] (MList []))
         , testCase "local String.then concatenates" (call (snd (head toolSnapshots)) "<String>::then" [text "a", text "b"] (text "ab"))
         , testCase "showInt zero" (callSupport "showInt" [MInt 0] (text "0"))
         , testCase "showInt minimum signed word" (callSupport "showInt" [MInt (-9223372036854775808)] (text "-9223372036854775808"))
         , testCase "join empty" (callSupport "joinWith" [text ", ", MList []] (text ""))
         , testCase "join preserves empty elements" (callSupport "joinWith" [text ", ", MList [text "", text "x", text ""]] (text ", x, "))
         , testCase "beforeAngle empty" (callSupport "beforeAngle" [text ""] (text ""))
         , testCase "beforeAngle generic" (callSupport "beforeAngle" [text "Vec<List<Int>, 3>"] (text "Vec"))
         , testCase "beforeAngle plain" (callSupport "beforeAngle" [text "Vec"] (text "Vec"))
         , testCase "withoutBackticks removes every backtick" (callSupport "withoutBackticks" [text "`Vec`<`Int`, 3>"] (text "Vec<Int, 3>"))
         ] ++
         [ testCase ("hex " ++ show n) (callSupport "hexUpper" [MInt n] (MInt (toInteger (ord digit))))
         | (n, digit) <- zip [0..15] "0123456789ABCDEF"
         ] ++
         [ testCase (name ++ " local LLVM global escaping") (call snapshot "global" [text "fn.", bytes [34, 92, 0, 195, 169]] (text "@\"fn.\\22\\5C\\00\\C3\\A9\""))
         | (name, snapshot) <- take 2 toolSnapshots
         ])
    , TestList "shared declaration and array helpers"
        [ testCase "lookup missing and empty declarations" (firstFailure
            [ callSupport "lookupDecl" [declarations, text "missing"] (MInt (-1))
            , callSupport "lookupDecl" [MList [], text ""] (MInt (-1))
            ])
        , testCase "borrowed declaration names and indices" (firstFailure
            [ callSupport "declName" [decl] (text name)
            | (name, decl) <- namedDeclarations
            ] `orFailure` firstFailure
            [ callSupport "lookupDecl" [declarations, text name] (MInt index)
            | (index, (name, _)) <- zip [0..] namedDeclarations
            ])
        , testCase "variant owner and struct constructor aliases" (firstFailure
            [ callSupport "ownerOf" [declarations, text "Choice::Wide"] (res True "Choice")
            , callSupport "ownerOf" [declarations, text "Pair"] (res True "Pair")
            , callSupport "ownerOf" [declarations, text "missing"] (res False "")
            , callSupport "canonical" [declarations, variant "Choice::Wide"] (named "Choice")
            , callSupport "canonical" [declarations, variant "Pair"] (named "Pair")
            , callSupport "canonical" [declarations, variant "missing"] (variant "missing")
            , callSupport "canonical" [declarations, named "Pair"] (named "Pair")
            ])
        , testCase "variants of structs, enums and missing names" (firstFailure
            [ callSupport "variantsOf" [declarations, text "Pair"] (MList [reader "Variant" [("name", text "Pair"), ("fields", pairFields)]])
            , callSupport "variantsOf" [declarations, text "Choice"] choiceVariants
            , callSupport "variantsOf" [declarations, text "missing"] (MList [])
            , callSupport "variantNamed" [choiceVariants, text "Choice::Wide"] (MBool True)
            , callSupport "variantNamed" [choiceVariants, text "missing"] (MBool False)
            , callSupport "isEnum" [declarations, text "Choice"] (MBool True)
            , callSupport "isEnum" [declarations, text "Pair"] (MBool False)
            , callSupport "isEnum" [declarations, text "missing"] (MBool False)
            ])
        , testCase "declared names retain named instances and resolve variants" (firstFailure
            [ callSupport "declaredName" [declarations, named "Vec<Int, 3>"] (res True "Vec<Int, 3>")
            , callSupport "declaredName" [declarations, variant "Choice::Wide"] (res True "Choice")
            , callSupport "declaredName" [declarations, intType] (res False "")
            ])
        , TestList "array classification"
            [ testCase label (firstFailure
                [ callSupport "sizedArray" [ty] (arrayInfo sized count (if sized then elemType else intType))
                , callSupport "isSizedArray" [ty] (MBool sized)
                , callSupport "isAggregate" [ty] (MBool aggregate)
                ])
            | (label, ty, elemType, sized, count, aggregate) <- arrayCases
            ]
        , testCase "notArray sentinel" (callSupport "notArray" [] (arrayInfo False 0 intType))
        , testCase "simpleLayout fixed-width and fallback" (firstFailure
            [ callSupport "simpleLayout" [byteType] (simple True 1 1)
            , callSupport "simpleLayout" [boolType] (simple True 1 1)
            , callSupport "simpleLayout" [word False 32] (simple True 4 4)
            , callSupport "simpleLayout" [named "Pair"] (simple False 8 8)
            , callSupport "wordLayout" [] (layout 8 8)
            ])
        , testCase "roundUp zero, aligned and nonaligned" (firstFailure
            [ callSupport "roundUp" [MInt n, MInt a] (MInt expected)
            | (n, a, expected) <- [(0, 8, 0), (8, 8, 8), (9, 8, 16), (3, 1, 3), (3, 0, 3)]
            ])
        ]
    , TestList "real phase-local layout controls"
        [ TestList name
            ([ testCase label (call snapshot "layoutOf" [declarations, ty] (layout size align))
             | (label, ty, outcomes) <- layoutCases
             , let (size, align) = outcomes !! phase
             ] ++
             [ testCase "fieldsLayout padding" (call snapshot "fieldsLayout" [declarations, pairFields] (layout 12 4))
             , testCase "fieldsLayout empty" (call snapshot "fieldsLayout" [declarations, MList []] (layout 0 1))
             , testCase "fieldsLayout follows this phase's Block rule" (call snapshot "fieldsLayout" [declarations, MList [field "flag" byteType, field "permission" (unary "TBlock" intType), field "tail" byteType]] (if phase == 1 then layout 24 8 else layout 2 1))
             ])
        | (phase, (name, snapshot)) <- zip [0..] toolSnapshots
        ]
    ]

supportId :: Mod.ModuleId
supportId = Mod.ModuleId "mir" (Just "support")

supportName :: String -> String
supportName = ("mir$support$support$" ++)

sharedRecords :: [String]
sharedRecords = ["Res", "ArrayInfo", "Layout", "Simple"]

sharedFunctions :: [String]
sharedFunctions =
    [ "noStrings", "showInt", "joinWith", "beforeAngle", "withoutBackticks", "hexUpper", "escaped"
    , "renderSize", "renderType", "declName", "lookupDecl", "variantNamed", "ownerOf"
    , "canonical", "variantsOf", "isEnum", "notArray", "sizedArray"
    , "isSizedArray", "isAggregate", "declaredName", "roundUp", "wordLayout", "simpleLayout"
    ]

toolSnapshots :: [(String, Result (Mod.LoadedPackage, Package.CompiledPackage, M.Program) String)]
toolSnapshots = [(name, snapshot name) | name <- ["emit", "mir_verify", "mir_erase"]]
  where
    snapshot name = case Mod.loadFromEntry (Mod.resolverFromFiles mirPackageFiles) ("examples/mir/" ++ name ++ "/" ++ name ++ ".tersus") of
        Left err -> Error err
        Right (Mod.PackageResult loaded) -> Package.compileModules loaded `bindResult` \compiled ->
            mapResult (\program -> (loaded, compiled, program)) (Package.lowerCompiledPackage loaded compiled)
        Right _ -> Error "MIR tool snapshot did not load as a package"

inspect :: Result a String -> (a -> TestResult) -> TestResult
inspect (Error err) _ = Just err
inspect (Ok value) check = check value

firstFailure :: [TestResult] -> TestResult
firstFailure results = case [err | Just err <- results] of
    err : _ -> Just err
    [] -> Nothing

orFailure :: TestResult -> TestResult -> TestResult
orFailure Nothing other = other
orFailure failure _ = failure

dependencyGraph :: (Mod.LoadedPackage, Package.CompiledPackage, M.Program) -> TestResult
dependencyGraph (loaded, compiled, _) = firstFailure
    [ testAssertEq (length [() | modu <- Mod.packageModules loaded, Mod.loadedModuleId modu == supportId]) 1
    , testAssertEq (length [() | modu <- Package.compiledModules compiled, Package.compiledModuleId modu == supportId]) 1
    , testAssertEq (deps supportId) (Just (Set.fromList [Mod.ModuleId "data" (Just "codec"), Mod.ModuleId "mir" (Just "reader")]))
    , testAssertEq (deps (Mod.ModuleId "mir" (Just "reader"))) (Just (Set.singleton (Mod.ModuleId "data" (Just "codec"))))
    , testAssertEq (fmap (Set.member supportId) (deps (Mod.packageEntryModule loaded))) (Just True)
    , testAssertEq [Mod.loadedFilePath file | modu <- Mod.packageModules loaded, Mod.loadedModuleId modu == supportId, file <- Mod.loadedModuleFiles modu] ["examples/mir/support/support.tersus"]
    ]
  where
    deps id0 = case [Set.fromList (Mod.loadedDependencies modu) | modu <- Mod.packageModules loaded, Mod.loadedModuleId modu == id0] of
        [dependencies] -> Just dependencies
        _ -> Nothing

definitionOwners :: (Mod.LoadedPackage, Package.CompiledPackage, M.Program) -> TestResult
definitionOwners (loaded, compiled, program) = firstFailure
    ([ testAssertEq [Package.compiledModuleId modu | modu <- modules, Map.member (supportName name) (I.ifTypes (Package.compiledInterface modu))] [supportId]
     | name <- sharedRecords
     ] ++
     [ testAssertEq [Package.compiledModuleId modu | modu <- modules, Map.member (supportName name) (I.ifFunctions (Package.compiledInterface modu))] [supportId]
     | name <- sharedFunctions
     ] ++
     [ testAssertEq [Package.compiledModuleId modu | modu <- modules, Set.member ("Clone", supportName name) (I.ifImpls (Package.compiledInterface modu))] [supportId]
     | name <- sharedRecords
     ] ++
     [ testAssertEq (Map.keysSet (I.ifTypes support)) (Set.fromList (map supportName sharedRecords))
     , testAssertEq (filter (`Map.member` M.progTypes program) (sharedRecords ++ ["Type", "Size", "TypeDecl", "Variant"])) []
     , testAssertEq (filter (`Map.member` M.progFunctions program) sharedFunctions) []
     , testAssertEq (filter (`Map.member` I.ifTypes entry) sharedRecords) []
     , testAssertEq (Map.member "Held" (M.progTypes program)) (Mod.moduleName (Mod.packageEntryModule loaded) == Just "emit")
     , testAssertEq (Map.member "Held" (I.ifTypes entry)) (Mod.moduleName (Mod.packageEntryModule loaded) == Just "emit")
     , testAssertEq (filter (`Map.member` I.ifFunctions support) [supportName "layoutOf", supportName "fieldsLayout", supportName "slotsOf", supportName "global"]) []
     , testAssertEq (all (`Map.member` I.ifFunctions entry) ["layoutOf", "fieldsLayout"]) True
     , testAssertEq (Map.member "slotsOf" (I.ifFunctions entry)) (Mod.moduleName (Mod.packageEntryModule loaded) /= Just "mir_erase")
     , testAssertEq [Package.compiledModuleId modu | modu <- modules, Map.member "<String>::then" (I.ifFunctions (Package.compiledInterface modu))] [Mod.packageEntryModule loaded]
     , testAssertEq (all (\name -> Map.member ("<" ++ supportName name ++ " as Clone>::clone") (M.progFunctions program)) sharedRecords) True
     ])
  where
    modules = Package.compiledModules compiled
    support = interfaceOf supportId compiled
    entry = interfaceOf (Mod.packageEntryModule loaded) compiled

interfaceOf :: Mod.ModuleId -> Package.CompiledPackage -> I.ModuleInterface
interfaceOf id0 compiled = case [Package.compiledInterface modu | modu <- Package.compiledModules compiled, Package.compiledModuleId modu == id0] of
    [iface] -> iface
    _ -> error ("missing compiled interface " ++ show id0)

canonicalTypes :: (Mod.LoadedPackage, Package.CompiledPackage, M.Program) -> TestResult
canonicalTypes (_, compiled, program) = firstFailure
    [ testAssertEq (Map.lookup (supportName "Res") (M.progTypes program)) (Just (M.StructDecl [("ok", TBool), ("text", TNamed "String" [])]))
    , testAssertEq (Map.lookup (supportName "Layout") (M.progTypes program)) (Just (M.StructDecl [("size", TInt), ("align", TInt)]))
    , testAssertEq (Map.lookup (supportName "ArrayInfo") (M.progTypes program)) (Just (M.StructDecl [("ok", TBool), ("length", TInt), ("elem", TNamed "data$codec$codec$Type" [])]))
    , testAssertEq (Map.lookup (supportName "Simple") (M.progTypes program)) (Just (M.StructDecl [("ok", TBool), ("layout", TNamed (supportName "Layout") [])]))
    , testAssertEq (Map.lookup "data$codec$codec$Type" (I.ifTypes (interfaceOf (Mod.ModuleId "data" (Just "codec")) compiled)) /= Nothing) True
    , testAssertEq (Map.lookup "data$codec$codec$Size" (I.ifTypes (interfaceOf (Mod.ModuleId "data" (Just "codec")) compiled)) /= Nothing) True
    , testAssertEq (Map.lookup "mir$reader$reader$TypeDecl" (I.ifTypes (interfaceOf (Mod.ModuleId "mir" (Just "reader")) compiled)) /= Nothing) True
    , testAssertEq (Map.lookup "mir$reader$reader$Variant" (I.ifTypes (interfaceOf (Mod.ModuleId "mir" (Just "reader")) compiled)) /= Nothing) True
    ]

borrowedMetadata :: (Mod.LoadedPackage, Package.CompiledPackage, M.Program) -> TestResult
borrowedMetadata (loaded, compiled, program) = firstFailure
    [ testAssertEq (Map.member "<String>::then" (I.ifFunctions support)) False
    , case Map.lookup "<String>::then" (I.ifFunctions (interfaceOf (Mod.packageEntryModule loaded) compiled)) of
        Nothing -> Just "consumer does not own String.then"
        Just method -> firstFailure
            [ testAssertEq (I.fnSignature method) (Signature [string, TRef string] string [] [] [] [])
            , testAssertEq (I.fnRequires method, I.fnEnsures method) ([], [])
            ]
    ] `orFailure` firstFailure
    [ case (Map.lookup symbol (I.ifFunctions support), Map.lookup symbol (M.progFunctions program)) of
        (Just exported, Just lowered) -> firstFailure
            [ testAssertEq (I.fnSignature exported) (Signature params result [] [] [] [])
            , testAssertEq (M.fnBorrowed lowered) (M.fnParams lowered)
            , testAssertEq (M.fnMutBorrowed lowered, M.fnFrom lowered) ([], [])
            , testAssertEq (M.fnReturns lowered) (Just result)
            ]
        _ -> Just ("missing shared function " ++ symbol)
    | (name, params, result) <-
        [ ("declName", [TRef decl], string)
        , ("lookupDecl", [TRef (list decl), TRef string], TInt)
        , ("renderType", [TRef ty], string)
        , ("renderSize", [TRef (TNamed "data$codec$codec$Size" [])], string)
        , ("variantNamed", [TRef (list (TNamed "mir$reader$reader$Variant" [])), TRef string], TBool)
        , ("sizedArray", [TRef ty], TNamed (supportName "ArrayInfo") [])
        ]
    , let symbol = supportName name
    ]
  where
    support = interfaceOf supportId compiled
    string = TNamed "String" []
    decl = TNamed "mir$reader$reader$TypeDecl" []
    ty = TNamed "data$codec$codec$Type" []
    list inner = TNamed "List" [ArgType inner]

directCalls :: (Mod.LoadedPackage, Package.CompiledPackage, M.Program) -> TestResult
directCalls (loaded, compiled, program) = firstFailure
    [ case Map.lookup (supportName "lookupDecl") (M.progFunctions program) of
        Nothing -> Just "support lookupDecl was not lowered"
        Just fn -> testAssertEq
            [(M.localType local) | local <- Map.elems (M.fnLocals fn), M.localName local == Just "d"]
            [TRef (TNamed "mir$reader$reader$TypeDecl" [])]
    , testAssertEq (Set.fromList (map supportName ["simpleLayout", "sizedArray", "declaredName", "lookupDecl", "wordLayout", "roundUp"]) `Set.isSubsetOf` calls "layoutOf") True
    , testAssertEq (Set.member (supportName "roundUp") (calls "fieldsLayout")) True
    , testAssertEq (Set.member "layoutOf" (calls "fieldsLayout")) True
    , testAssertEq (Set.member (supportName "declName") (calls (supportName "lookupDecl"))) True
    , testAssertEq (Set.member "<String>::concat" (calls (supportName "joinWith"))) True
    , testAssertEq (Set.member "data$codec$codec$catStrings" (calls (supportName "joinWith"))) False
    , testAssertEq (Set.member "data$codec$codec$catStrings" (calls (supportName "renderType"))) True
    , testAssertEq (Set.member "data$codec$codec$catStrings" (calls (supportName "renderSize"))) True
    , testAssertEq (Set.member "<String>::then" (calls "global")) (Mod.moduleName (Mod.packageEntryModule loaded) /= Just "mir_erase")
    , testAssertEq [name | name <- Map.keys (I.ifFunctions entry), name `elem` sharedFunctions || any (\local -> ("$" ++ local) `isInfixOf` name && not ("<" `isPrefixOf` name)) sharedFunctions] []
    ]
  where
    entry = interfaceOf (Mod.packageEntryModule loaded) compiled
    calls name = case Map.lookup name (M.progFunctions program) of
        Nothing -> Set.empty
        Just fn -> Set.fromList [callee | block <- Map.elems (M.fnBlocks fn), M.Call (M.Const (M.CFn callee)) _ _ _ <- [M.blockTerminator block]]

supportUnitIdentity :: (Mod.LoadedPackage, Package.CompiledPackage, M.Program) -> TestResult
supportUnitIdentity (loaded, compiled, _) = inspect (lowerSupportUnit loaded compiled) $ \unit@(_, program) -> firstFailure
    [ case (linkPrograms [unit], linkPrograms [unit, unit]) of
        (Ok once, Ok twice) -> testAssertEq twice once
        (Error err, _) -> Just err
        (_, Error err) -> Just err
    , testAssertErrorContains "inconsistent units" (linkPrograms [unit, (supportId, program{M.progFunctions = Map.delete (supportName "lookupDecl") (M.progFunctions program)})])
    ]

lowerSupportUnit :: Mod.LoadedPackage -> Package.CompiledPackage -> Result (Mod.ModuleId, M.Program) String
lowerSupportUnit loaded compiled =
    case ([m | m <- Mod.packageModules loaded, Mod.loadedModuleId m == supportId], [m | m <- Package.compiledModules compiled, Package.compiledModuleId m == supportId]) of
        ([source], [modu]) ->
            let ifaces = Package.compiledLibInterfaces modu ++ map (`interfaceOf` compiled) (Mod.loadedDependencies source)
             in mapResult ((,) supportId) (lowerModuleWith (I.mergeInterfacesImportEnv ifaces) ifaces (Package.compiledElaborated modu))
        _ -> Error "expected one loaded and compiled support unit"

call :: Result (Mod.LoadedPackage, Package.CompiledPackage, M.Program) String -> String -> [MirValue] -> MirValue -> TestResult
call snapshot name args expected = inspect snapshot $ \(_, _, program) ->
    case runNamedFunction program name args of
        Error err -> Just (name ++ ": " ++ err)
        Ok actual -> testAssertEq actual (Just expected)

callSupport :: String -> [MirValue] -> MirValue -> TestResult
callSupport name = call (snd (head toolSnapshots)) (supportName name)

text :: String -> MirValue
text = bytes . map ord

bytes :: [Int] -> MirValue
bytes values = MData "String" [("bytes", MList (map (MInt . toInteger) values))]

codec :: String -> [(String, MirValue)] -> MirValue
codec name = MData ("data$codec$codec$" ++ name)

reader :: String -> [(String, MirValue)] -> MirValue
reader name = MData ("mir$reader$reader$" ++ name)

intType, byteType, boolType :: MirValue
intType = codec "Type::TInt" []
byteType = codec "Type::TByte" []
boolType = codec "Type::TBool" []

unary :: String -> MirValue -> MirValue
unary tag inner = codec ("Type::" ++ tag) [(if tag == "TList" then "elem" else "inner", inner)]

word :: Bool -> Integer -> MirValue
word signed bits = codec "Type::TWord" [("signed", MBool signed), ("bits", MInt bits)]

named :: String -> MirValue
named name = codec "Type::TNamed" [("name", text name), ("base", text name), ("argc", MInt 0), ("argTokens", MList [])]

variant :: String -> MirValue
variant name = codec "Type::TVariant" [("name", text name)]

array :: MirValue -> MirValue -> MirValue
array elemType size = codec "Type::TArray" [("elem", elemType), ("size", size)]

constantSize :: Integer -> MirValue
constantSize n = codec "Size::SConst" [("n", MInt n)]

anySize :: MirValue
anySize = codec "Size::SAny" []

parameterSize :: MirValue
parameterSize = codec "Size::SParam" [("name", text "n")]

layout :: Integer -> Integer -> MirValue
layout size align = MData (supportName "Layout") [("size", MInt size), ("align", MInt align)]

res :: Bool -> String -> MirValue
res ok value = MData (supportName "Res") [("ok", MBool ok), ("text", text value)]

arrayInfo :: Bool -> Integer -> MirValue -> MirValue
arrayInfo ok count elemType = MData (supportName "ArrayInfo") [("ok", MBool ok), ("length", MInt count), ("elem", elemType)]

simple :: Bool -> Integer -> Integer -> MirValue
simple ok size align = MData (supportName "Simple") [("ok", MBool ok), ("layout", layout size align)]

field :: String -> MirValue -> MirValue
field name ty = reader "Field" [("name", text name), ("ty", ty)]

pairFields, choiceVariants, declarations :: MirValue
pairFields = MList [field "byte" byteType, field "wide" (word True 32), field "flag" boolType]
choiceVariants = MList
    [ reader "Variant" [("name", text "Choice::Empty"), ("fields", MList [])]
    , reader "Variant" [("name", text "Choice::Wide"), ("fields", MList [field "wide" intType, field "flag" byteType])]
    ]
declarations = MList (map snd namedDeclarations)

namedDeclarations :: [(String, MirValue)]
namedDeclarations =
    [ ("Empty", struct "Empty" (MList []))
    , ("Pair", struct "Pair" pairFields)
    , ("Choice", reader "TypeDecl::DEnum" [("name", text "Choice"), ("variants", choiceVariants)])
    , ("Vec<Int, 3>", struct "Vec<Int, 3>" (MList [field "items" (array intType (constantSize 3))]))
    , ("List<Int>", struct "List<Int>" (MList [field "addr" (unary "TAddr" intType), field "len" intType, field "cap" intType]))
    , ("Box<Int>", struct "Box<Int>" (MList [field "addr" (unary "TAddr" intType)]))
    ]
  where
    struct name fields = reader "TypeDecl::DStruct" [("name", text name), ("fields", fields)]

sizeCases :: [(String, MirValue, String)]
sizeCases =
    [ ("constant", constantSize 0, "0")
    , ("any", anySize, "?")
    , ("parameter", parameterSize, "n")
    , ("variable", codec "Size::SVar" [("n", MInt 17)], "_17")
    ]

typeCases :: [(String, MirValue, String)]
typeCases =
    [ ("Int", intType, "Int")
    , ("Byte", byteType, "Byte")
    , ("Bool", boolType, "Bool")
    , ("list", unary "TList" byteType, "List<Byte>")
    , ("box", unary "TBox" intType, "Box<Int>")
    , ("array", array boolType (constantSize 3), "Array<Bool, 3>")
    , ("unsized array", array intType anySize, "Array<Int, ?>")
    , ("size parameter", array intType parameterSize, "Array<Int, n>")
    , ("borrow", unary "TRef" intType, "&Int")
    , ("update borrow", unary "TMutRef" intType, "&mut Int")
    , ("address", unary "TAddr" byteType, "Addr<Byte>")
    , ("permission", unary "TBlock" intType, "Block<Int>")
    , ("uninitialized", unary "TUninit" byteType, "Uninit<Byte>")
    , ("signed word", word True 16, "I16")
    , ("unsigned word", word False 32, "U32")
    , ("type parameter", codec "Type::TParam" [("name", text "T")], "T")
    , ("forall types before sizes", codec "Type::TForall" [("sizes", MList [text "n"]), ("types", MList [text "T", text "U"]), ("body", intType)], "<T, U, n>Int")
    , ("empty forall", codec "Type::TForall" [("sizes", MList []), ("types", MList []), ("body", intType)], "<>Int")
    , ("function", codec "Type::TFn" [("args", MList [intType, unary "TRef" byteType]), ("ret", boolType)], "fn(Int, &Byte) -> Bool")
    , ("nullary function", codec "Type::TFn" [("args", MList []), ("ret", intType)], "fn() -> Int")
    , ("named generic strips backticks only", codec "Type::TNamed" [("name", text "`Vec`<`Int`, 3>"), ("base", text "deliberatelyDifferent"), ("argc", MInt 9), ("argTokens", MList [])], "Vec<Int, 3>")
    , ("empty named", named "", "")
    , ("variant retains backticks", variant "`Choice`::Wide", "`Choice`::Wide")
    , ("unknown variable", codec "Type::TVar" [("n", MInt 12)], "?")
    ]

escapedCases :: [(String, MirValue, String)]
escapedCases =
    [ ("empty", text "", "")
    , ("ASCII generic", text "Vec<Int, 3>::make", "Vec<Int, 3>::make")
    , ("LLVM delimiters", bytes [34, 92], "\\22\\5C")
    , ("control and ASCII boundaries", bytes [0, 9, 10, 31, 32, 126, 127, 255], "\\00\\09\\0A\\1F ~\\7F\\FF")
    , ("UTF-8 bytes", bytes [195, 169, 228, 184, 173], "\\C3\\A9\\E4\\B8\\AD")
    ]

arrayCases :: [(String, MirValue, MirValue, Bool, Integer, Bool)]
arrayCases =
    [ ("zero sized", array byteType (constantSize 0), byteType, True, 0, True)
    , ("sized", array byteType (constantSize 3), byteType, True, 3, True)
    , ("unsized", array byteType anySize, byteType, False, 0, False)
    , ("parameter sized is not constant or unsized", array byteType parameterSize, byteType, False, 0, False)
    , ("variable sized is not constant or unsized", array byteType (codec "Size::SVar" [("n", MInt 2)]), byteType, False, 0, False)
    , ("legacy list is not array", unary "TList" byteType, byteType, False, 0, False)
    , ("boxed array is not inline", unary "TBox" (array byteType (constantSize 3)), byteType, False, 0, False)
    , ("named container is aggregate", named "List<Int>", intType, False, 0, True)
    , ("variant is aggregate", variant "Choice::Wide", intType, False, 0, True)
    ]

layoutCases :: [(String, MirValue, [(Integer, Integer)])]
layoutCases =
    [ ("Int", intType, same (8, 8))
    , ("Bool", boolType, same (1, 1))
    , ("Byte", byteType, same (1, 1))
    , ("I16", word True 16, same (2, 2))
    , ("U32", word False 32, same (4, 4))
    , ("Block stays phase local", unary "TBlock" intType, [(0, 1), (8, 8), (0, 1)])
    , ("Uninit stays phase local", unary "TUninit" byteType, [(1, 1), (8, 8), (1, 1)])
    , ("legacy TList stays phase local", unary "TList" intType, [(8, 8), (24, 8), (24, 8)])
    , ("legacy boxed sized array stays phase local", unary "TBox" (array intType (constantSize 3)), [(8, 8), (24, 8), (24, 8)])
    , ("legacy boxed unsized array stays phase local", unary "TBox" (array intType anySize), [(8, 8), (24, 8), (24, 8)])
    , ("scalar legacy Box", unary "TBox" intType, same (8, 8))
    , ("named List follows declaration", named "List<Int>", same (24, 8))
    , ("named Box follows declaration", named "Box<Int>", same (8, 8))
    , ("empty struct", named "Empty", same (0, 1))
    , ("padded struct", named "Pair", same (12, 4))
    , ("enum tag and widest payload", named "Choice", same (24, 8))
    , ("enum variant alias", variant "Choice::Wide", same (24, 8))
    , ("struct constructor alias", variant "Pair", same (12, 4))
    , ("named generic instance", named "Vec<Int, 3>", same (24, 8))
    , ("missing declaration fallback", named "missing", same (8, 8))
    , ("zero array retains element alignment", array (word True 32) (constantSize 0), same (0, 4))
    , ("sized inline array", array byteType (constantSize 3), same (3, 1))
    , ("nested inline array", array (array byteType (constantSize 3)) (constantSize 2), same (6, 1))
    , ("array of padded structs", array (named "Pair") (constantSize 2), same (24, 4))
    , ("unsized inline array fallback", array intType anySize, same (8, 8))
    , ("parameter sized array fallback", array byteType parameterSize, same (8, 8))
    ]
  where
    same result = replicate 3 result
