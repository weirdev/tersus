module Pipeline
    ( parseSource
    , parseWithEquality
    , validatedSource
    , compileSource
    , CompiledModule (..)
    , CompiledPackage (..)
    , compileModules
    , compileModulesValidated
    , compileModulesToProgram
    , compileModulesToOwned
    , assumptionsOfPackage
    , ownedSource
    , nativeProgram
    , validateStatements
    , runStatements
    , assumptionsOf
    ) where

import Data.List (sortBy)
import Data.Ord (comparing)
import qualified Data.Map as Map
import qualified Mir as M
import Interface (InterfaceFunction (..), ModuleInterface (..), extractInterface, mergeInterfacesImportEnv, nameInModule, predeclareOwnEnv)
import Link (linkPrograms, pruneProgram)
import ModuleResolve (rewriteFileReferences)
import qualified Modules as Mod
import MirOwnership (expandRefWrites, insertOwnership)
import MirVerify (verifyProgram)
import MirEval (MirValue, runProgram)
import MirGhost (eraseGhosts, withoutUninit)
import MirLower (lowerElaborated, lowerLibrary, lowerModuleWith)
import MirValidate (Validated, validateProgram)
import Data.Char (isAlphaNum)
import Data.List (intercalate)
import Parse (ParsedFile (..), emptyDecls, importPath, locating, parseFileWith, parseStatementBlockWith, renderPath)
import MirLists (lowerLists)
import PreludeSource (cloneSource, eqSource, boxSource, listsSource, mapSource, preludeSource, setSource, stringSource)
import Pretty (renderVarProof)
import TersusTypes (Expression (..), FunctBody (..), Signature (..), Size (..), Statement (..), Type (..), ValidationStatement (..), Value (..), exprToProof, instanceOf)
import TypeCheck (elaborate, elaborateWith)
import Utils

-- The stages a program goes through, each built on the one before and each giving back what the next needs:
--
--   source -> AST (parseSource) -> checked AST (elaborate: types checked, each `shrinks` resolved)
--          -> MIR (lowerElaborated) -> validated MIR (validateProgram) -> executed (runProgram)
--                                                                    or -> owned MIR (ownedSource) -> LLVM IR (the emitter written in Tersus, see Bootstrap)
--
-- The validated MIR has its permissions (ghost values, POINTERS.md) taken out by `eraseGhosts` before anything runs it or makes native code of it.
--
-- The program is type checked once, by `elaborate`; the lowering takes its result and the validator the MIR. Errors name
-- the stage that refused the program, as the command line prints them.

parseSource :: String -> Result [Statement] String
parseSource source = parseSourceWith True source

-- A program with the equality library in front of it (unless it declares a trait Eq), as `=` on any type but a word needs, and with no
-- other library: how the tests of the language read a program
parseWithEquality :: String -> Either String [Statement]
parseWithEquality source = case [text | (name, text) <- libraries source, name `elem` ["the clone library", "the equality library"]] of
    [] -> either (Left . show) (Right . fst) (parseStatementBlockWith emptyDecls source)
    texts -> case readLibs emptyDecls texts of
        Left err -> Left err
        Right (library, declared) -> either (Left . show) (Right . (library ++) . fst) (parseStatementBlockWith declared source)
  where
    readLibs declared [] = Right ([], declared)
    readLibs declared (text : more) = case parseStatementBlockWith declared text of
        Left err -> Left ("Parse error in a library: " ++ show err)
        Right (library, declared') -> case readLibs declared' more of
            Left err -> Left err
            Right (rest, final) -> Right (library ++ rest, final)

-- (the library of lists is the one program that may use the names that a program may not)
parseSourceWith :: Bool -> String -> Result [Statement] String
parseSourceWith reserving source = case libraries source of
    [] -> case parseFileWith (locating emptyDecls) source of
        Left err -> Error ("Parse error: " ++ show err)
        Right (ParsedFile imports stmts, _) -> notLinked imports stmts
    texts -> case readLibraries texts emptyDecls of
        Left err -> Error err
        Right (library, declared) -> case parseFileWith (locating declared) source of
            Left err -> Error ("Parse error: " ++ show err)
            Right (ParsedFile imports stmts, _) -> case notLinked imports stmts of
                Error err -> Error err
                Ok stmts' -> Ok (library ++ stmts')
  where
    notLinked imports stmts
        | null imports = checked stmts
        | otherwise = Error ("imports are not linked yet: " ++ intercalate ", " (map (renderPath . importPath) imports))
    readLibraries [] declared = Right ([], declared)
    readLibraries ((name, text) : more) declared = case parseStatementBlockWith declared text of
        Left err -> Left ("Parse error in " ++ name ++ ": " ++ show err)
        Right (stmts, declared') -> fmap (\(rest, final) -> (stmts ++ rest, final)) (readLibraries more declared')
    checked stmts = if reserving then maybe (Ok stmts) (\name -> Error ("Type error: " ++ name ++ " is reserved: native code makes a list of the struct StdList and the functions stdList... of lib/lists.tersus, and a Box of the struct StdBox and the functions stdBox... of lib/box.tersus, so a program does not declare names like them")) (reservedName stmts) else Ok stmts

-- A name the program declares that native code uses for lists (see MirLists)
reservedName :: [Statement] -> Maybe String
reservedName stmts = case [name | stmt <- stmts, name <- declared stmt, reserved name] of
    name : _ -> Just name
    [] -> Nothing
  where
    declared stmt = case stmt of
        Assign name (Val VFunct{}) -> [name]
        StructDef name _ _ _ -> [name]
        EnumDef name _ -> [name]
        TraitDef name _ _ -> [name]
        BoundedDef _ (Assign name _) -> [name]
        _ -> []
    reserved name = name `elem` ["StdList", "StdBox"] || take 7 name == "stdList" || take 6 name == "stdBox"

-- The libraries that a program has in front of it, in order, unless it declares their names itself, so a program that has a `Vec` of its own is
-- unchanged: lib/eq.tersus (the trait `Eq` that `=` calls, whose impls are made only for the types a program compares), lib/prelude.tersus (the traits `Sequence`, `Growable`, `Clone`, `Copy`, `Drop`, `Deref` and `Hash`) if it mentions any of them (or
-- `hashCombine`), lib/string.tersus (the struct `String` that a string literal is a value of, which needs the traits) if it mentions `String` or
-- has a literal, lib/map.tersus (the struct `HashMap`) if it mentions `HashMap`, and lib/set.tersus (the struct `HashSet`,
-- which is made of a map) if it mentions `HashSet`
libraries :: String -> [(String, String)]
libraries source = [("the clone library", cloneSource) | not (declares ["Clone"])] ++ [("the equality library", eqSource) | not (declares ["Eq"])] ++ [("the prelude", preludeSource) | prelude] ++ [("the string library", stringSource) | strings] ++ [("the map library", mapSource) | maps] ++ [("the set library", setSource) | sets]
  where
    code = withoutText source
    ws = names code
    ws' = zip ws (drop 1 ws)
    declares candidates = any (\(keyword, name) -> keyword `elem` ["struct", "enum", "trait"] && name `elem` candidates) ws'
    preludeFree = not (declares ["Sequence", "Growable", "Clone", "Copy", "Drop", "Deref", "Hash"])
    strings = preludeFree && not (declares ["String"]) && ("String" `elem` ws || '"' `elem` code)
    maps = preludeFree && not (declares ["HashMap"]) && ("HashMap" `elem` ws || sets)
    sets = preludeFree && not (declares ["HashSet"]) && "HashSet" `elem` ws
    prelude = preludeFree && (strings || maps || sets || any (`elem` ws) ["Sequence", "Growable", "Clone", "Copy", "Drop", "Deref", "Hash", "hashCombine"])
    -- (the names in a text: runs of letters, digits and underscores)
    names text = case dropWhile (not . isNameChar) text of
        "" -> []
        rest -> let (w, more) = span isNameChar rest in w : names more
    isNameChar c = isAlphaNum c || c == '_'
    -- (the program without its comments and the text of its literals, which are `""`: what a name there says is not the program's)
    withoutText text = case text of
        '/' : '/' : more -> withoutText (dropWhile (/= '\n') more)
        '"' : more -> '"' : '"' : withoutText (afterString more)
        c : more -> c : withoutText more
        [] -> []
    afterString text = case text of
        '\\' : _ : more -> afterString more
        '"' : more -> more
        '\n' : more -> '\n' : more
        _ : more -> afterString more
        [] -> []

-- What a program takes on trust (POINTERS.md, Assumptions): each `assume e;`, each `Block::assume(p, n)` (the permission to memory it did not
-- allocate), each `extern fn` (whose contract is assumed) and each `axiom`, in the program and the libraries in front of it, with the place it is written at (a library's have none). The
-- validator proves everything else, so this is the list to read to know what a program's proofs rest on.
assumptionsOf :: String -> Result [String] String
assumptionsOf source = mapResult (snd . statements Nothing) (parseSource source)
  where
    statements place = foldl (\(p, found) stmt -> let (p', more) = statement p stmt in (p', found ++ more)) (place, [])
    statement place stmt = case stmt of
        Mark line column -> (Just (line, column), [])
        ValidationStatement (Assume p) -> (place, [at place ("assume " ++ renderVarProof p)])
        AxiomDef name args _ _ -> (place, [at place ("axiom " ++ name ++ "(" ++ commas args ++ ")")])
        ExternDef name -> (place, [at place ("extern fn " ++ name)])
        Assign _ (Val (VFunct _ _ _ (NativeFunct _ _ body) _)) -> (place, snd (statements place body))
        Assign _ e -> (place, expression place e)
        Let _ e -> (place, expression place e)
        Return e -> (place, expression place e)
        Block body -> (place, snd (statements place body))
        If c yes no -> (place, expression place c ++ snd (statements place yes) ++ snd (statements place no))
        While c _ _ body -> (place, expression place c ++ snd (statements place body))
        ImplDef _ _ _ _ _ body -> (place, snd (statements place body))
        BoundedDef _ s -> (place, snd (statement place s))
        _ -> (place, [])
    expression place e = case e of
        F (Var "Block::assume") args -> at place (renderVarProof (exprToProof e)) : concatMap (expression place) args
        F f args -> concatMap (expression place) (f : args)
        _ -> []
    at place text = maybe "in a library: " (\(line, column) -> "line " ++ show line ++ ":" ++ show column ++ ": ") place ++ text
    commas = foldr1' (\a b -> a ++ ", " ++ b)
    foldr1' _ [] = ""
    foldr1' f xs = foldr1 f xs

-- The MIR of a program that passes every check, before its ghosts are erased: what the eraser written in Tersus
-- (examples/mir_erase.tersus) is given, as `tersus mir --ghost-data` writes it
validatedSource :: String -> Result M.Program String
validatedSource source =
    parseSourceWith True source `bindResult` \stmts ->
        stage "Validation failed: " (elaborate stmts) `bindResult` \elaborated ->
            stage "Lowering failed: " (lowerElaborated elaborated) `bindResult` \program ->
                stage "Validation failed: " (validateProgram program) `bindResult` \_ ->
                    Ok program

-- The MIR of a program that passes every check
compileSource :: String -> Result M.Program String
compileSource = compileWith True

compileWith :: Bool -> String -> Result M.Program String
compileWith reserving source =
    parseSourceWith reserving source `bindResult` \stmts ->
        stage "Validation failed: " (elaborate stmts) `bindResult` \elaborated ->
            stage "Lowering failed: " ((if reserving then lowerElaborated else lowerLibrary) elaborated) `bindResult` \program ->
                stage "Validation failed: " (validateProgram program) `bindResult` \_ ->
                    eraseGhosts program

-- The MIR of a program that passes every check, with who owns each value made explicit (MirOwnership), for native code
ownedSource :: String -> Result M.Program String
ownedSource source = compileSource source `bindResult` ownedOfProgram

ownedOfProgram :: M.Program -> Result M.Program String
ownedOfProgram program =
    -- (a reference to an unsized value is a pointer and a size together, which the emitter does not
    -- carry yet, so it is refused here rather than miscompiled)
    if any unsizedRef (M.progMain program : Map.elems (M.progFunctions program))
        then Error "a reference to an unsized value (&Array<T>) is not in native code yet: run it with eval, or check it"
        else
            let owned = insertOwnership (nativeProgram program)
             in stage "Ownership failed: " (verifyProgram owned) `bindResult` \_ -> Ok owned
  where
    unsizedRef fn = any (\d -> hasUnsizedRef (M.localType d)) (Map.elems (M.fnLocals fn)) || maybe False hasUnsizedRef (M.fnReturns fn)
    hasUnsizedRef ty = case ty of
        TRef inner -> isUnsized inner
        TMutRef inner -> isUnsized inner
        _ -> False
    isUnsized (TArrayOf _ SizeAny) = True
    isUnsized _ = False

-- The program that native code is made of: a validated program with each list and Box made of the library's structs (see MirLists), and each
-- Uninit<T> a T (it is laid out as one: an empty one is the words of a T cleared, which own nothing)
nativeProgram :: M.Program -> M.Program
nativeProgram = lowerLists listLibrary . withoutUninit . expandRefWrites

-- The library of lists and Boxes (lib/lists.tersus and lib/box.tersus), compiled and validated once
listLibrary :: M.Program
listLibrary = case compileWith False (listsSource ++ "\n" ++ boxSource) of
    Ok program -> program
    Error e -> error ("lib/lists.tersus and lib/box.tersus do not compile: " ++ e)

-- Checks and validates a program given as statements
validateStatements :: [Statement] -> Result Validated String
validateStatements stmts =
    elaborate stmts `bindResult` \elaborated ->
        lowerElaborated elaborated `bindResult` validateProgram

-- Runs a program given as statements, once it type checks, without validating it
runStatements :: [Statement] -> Result (Maybe MirValue) String
runStatements stmts =
    elaborate stmts `bindResult` \elaborated ->
        lowerElaborated elaborated `bindResult` eraseGhosts `bindResult` runProgram

data CompiledModule = CompiledModule
    { compiledModuleId :: Mod.ModuleId
    , compiledStatements :: [Statement]
    , compiledInterface :: ModuleInterface
    }
    deriving (Show)

data CompiledPackage = CompiledPackage
    { compiledEntryModule :: Mod.ModuleId
    , compiledModules :: [CompiledModule]
    }
    deriving (Show)

compileModules :: Mod.LoadedPackage -> Result CompiledPackage String
compileModules pkg = go (Mod.packageModules pkg) Map.empty []
  where
    go [] _ done = Ok (CompiledPackage (Mod.packageEntryModule pkg) (reverse done))
    go (modu : rest) interfaces done =
        case compileOne interfaces modu of
            Error err -> Error err
            Ok compiled -> go rest (Map.insert (Mod.loadedModuleId modu) (compiledInterface compiled) interfaces) (compiled : done)
    compileOne interfaces modu =
        let moduId = Mod.loadedModuleId modu
            depInterfaces = [interfaces Map.! dep | dep <- Mod.loadedDependencies modu, Map.member dep interfaces]
            missing = [dep | dep <- Mod.loadedDependencies modu, not (Map.member dep interfaces)]
         in if not (null missing)
                then Error ("in module " ++ Mod.renderModuleId moduId ++ ": dependency " ++ Mod.renderModuleId (head missing) ++ " was not compiled before it (the loader gives modules dependencies first)")
                else
                    let env = predeclareOwnEnv (mergeInterfacesImportEnv depInterfaces)
                     in case prepareModule pkg modu of
                            Left err -> Error err
                            Right prepared -> case orphanCheck moduId prepared of
                                Left err -> Error err
                                Right () -> case moduleLibraryStatements depInterfaces modu of
                                    Left err -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": " ++ err)
                                    Right libraryStmts ->
                                        let withLibraries = libraryStmts ++ prepared
                                            augmented = if needsDropTrait withLibraries then dropTraitStatements ++ withLibraries else withLibraries
                                         in case elaborateWith env augmented of
                                                Error err -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": " ++ err)
                                                Ok (elaborated, state) -> case extractInterface moduId prepared elaborated state of
                                                    Error err -> Error err
                                                    Ok iface -> Ok (CompiledModule moduId elaborated iface)

moduleLibraryStatements :: [ModuleInterface] -> Mod.LoadedModule -> Either String [Statement]
moduleLibraryStatements depInterfaces modu = readLibraries (libraries moduleText) emptyDecls
  where
    moduleText = intercalate "\n" ([Mod.loadedFileSource file | file <- Mod.loadedModuleFiles modu] ++ [libraryTriggers])
    libraryTriggers = intercalate " " [name | name <- ["String", "HashMap", "HashSet"], name `elem` dependencyTypeNames]
    dependencyTypeNames = concatMap interfaceTypeNames depInterfaces
    interfaceTypeNames iface =
        Map.keys (ifTypes iface)
            ++ Map.keys (ifGenerics iface)
            ++ concatMap (concatMap (typeNames . snd) . snd) (Map.elems (ifCtors iface))
            ++ concatMap (concatMap (typeNames . snd) . snd) (Map.elems (ifGenerics iface))
            ++ concatMap signatureTypeNames (Map.elems (ifFunctions iface))
    signatureTypeNames fn = let Signature params ret _ _ _ _ = fnSignature fn in concatMap typeNames (ret : params)
    typeNames ty = case ty of
        TNamed name -> [name]
        TVariant name -> [name]
        TList inner -> typeNames inner
        TArrayOf inner _ -> typeNames inner
        TBox inner -> typeNames inner
        TAddr inner -> typeNames inner
        TBlock inner -> typeNames inner
        TUninit inner -> typeNames inner
        TRef inner -> typeNames inner
        TMutRef inner -> typeNames inner
        TFn args ret -> concatMap typeNames (ret : args)
        TForall _ _ inner -> typeNames inner
        _ -> []
    readLibraries [] _ = Right []
    readLibraries ((name, text) : more) declared = case parseStatementBlockWith declared text of
        Left err -> Left ("Parse error in " ++ name ++ ": " ++ show err)
        Right (stmts, declared') -> fmap (stmts ++) (readLibraries more declared')

needsDropTrait :: [Statement] -> Bool
needsDropTrait prepared = any implsDrop prepared && not (any declaresDrop prepared)
  where
    implsDrop stmt = case stmt of
        ImplDef (Just trait) _ _ _ _ _ -> localName trait == "Drop"
        _ -> False
    declaresDrop stmt = case stmt of
        TraitDef name _ _ -> localName name == "Drop"
        _ -> False
    localName name = reverse (takeWhile (/= '$') (reverse name))

dropTraitStatements :: [Statement]
dropTraitStatements = case parseStatementBlockWith emptyDecls preludeSource of
    Right (stmts, _) -> [stmt | stmt@(TraitDef name _ _) <- stmts, name == "Drop"]
    Left _ -> []

prepareModule :: Mod.LoadedPackage -> Mod.LoadedModule -> Either String [Statement]
prepareModule pkg modu = do
    perFile <- mapM prepareFile (Mod.loadedModuleFiles modu)
    Right (reorderModuleStatements (concat perFile))
  where
    prepareFile file =
        let identity
                | Mod.loadedModuleId modu == Mod.packageEntryModule pkg = Mod.rootModuleIdentity (Mod.packagePackageName pkg) (Mod.loadedFileStem file ++ ".tersus")
                | otherwise = Mod.fileModuleIdentity (Mod.packagePackageName pkg) (maybe "" id (Mod.moduleName (Mod.loadedFileModule file))) (Mod.loadedFileStem file ++ ".tersus")
            canonical = Mod.canonicalizeDeclarations identity (fileBody (Mod.loadedParsed file))
         in case rewriteFileReferences pkg file canonical of
                Left err -> Left ("in module " ++ Mod.renderModuleId (Mod.loadedModuleId modu) ++ " file " ++ Mod.loadedFileName file ++ ": " ++ err)
                Right rewritten -> Right rewritten

reorderModuleStatements :: [Statement] -> [Statement]
reorderModuleStatements = sortBy (comparing category)
  where
    category :: Statement -> Int
    category stmt = case stmt of
        StructDef{} -> 0
        EnumDef{} -> 0
        TraitDef{} -> 0
        ImplDef{} -> 1
        _ -> 2

orphanCheck :: Mod.ModuleId -> [Statement] -> Either String ()
orphanCheck modu statements = case [message | ImplDef (Just trait) _ typeName _ _ _ <- statements, Just message <- [orphanMessage trait typeName]] of
    message : _ -> Left message
    [] -> Right ()
  where
    orphanMessage trait typeName
        | nameInModule modu trait || nameInModule modu (baseOf typeName) = Nothing
        | otherwise = Just ("in module " ++ Mod.renderModuleId modu ++ ": orphan impl: impl " ++ trait ++ " for " ++ typeName ++ " defines neither a trait nor a type of this module; an impl must live in the module of its trait or of its type")
    baseOf name = maybe name fst (instanceOf name)

compileModulesValidated :: Mod.LoadedPackage -> Result M.Program String
compileModulesValidated pkg =
    compileModules pkg `bindResult` \compiled ->
        let ifaceMap = Map.fromList [(compiledModuleId modu, compiledInterface modu) | modu <- compiledModules compiled]
            loadedMap = Map.fromList [(Mod.loadedModuleId modu, modu) | modu <- Mod.packageModules pkg]
            lowerOne modu = case Map.lookup (compiledModuleId modu) loadedMap of
                Nothing -> Error ("internal: compiled module " ++ Mod.renderModuleId (compiledModuleId modu) ++ " is not in the loaded package")
                Just loaded ->
                    let depIfaces = [ifaceMap Map.! dep | dep <- Mod.loadedDependencies loaded, Map.member dep ifaceMap]
                     in mapResult (\program -> (compiledModuleId modu, program)) (stage "Lowering failed: " (lowerModuleWith (mergeInterfacesImportEnv depIfaces) depIfaces (compiledStatements modu)))
         in flatResultMap lowerOne (compiledModules compiled) `bindResult` \units ->
                linkPrograms units `bindResult` \linked ->
                    stage "Validation failed: " (validateProgram linked) `bindResult` \_ -> Ok linked

compileModulesToProgram :: Mod.LoadedPackage -> Result M.Program String
compileModulesToProgram pkg = mapResult pruneProgram (compileModulesValidated pkg `bindResult` eraseGhosts)

compileModulesToOwned :: Mod.LoadedPackage -> Result M.Program String
compileModulesToOwned pkg =
    compileModulesToProgram pkg `bindResult` \program ->
        if any unsizedRef (M.progMain program : Map.elems (M.progFunctions program))
            then Error "a reference to an unsized value (&Array<T>) is not in native code yet: run it with eval, or check it"
            else
                let owned = pruneProgram (insertOwnership (nativeProgram program))
                 in stage "Ownership failed: " (verifyProgram owned) `bindResult` \_ -> Ok owned
  where
    unsizedRef fn = any (\d -> hasUnsizedRef (M.localType d)) (Map.elems (M.fnLocals fn)) || maybe False hasUnsizedRef (M.fnReturns fn)
    hasUnsizedRef ty = case ty of
        TRef inner -> isUnsized inner
        TMutRef inner -> isUnsized inner
        _ -> False
    isUnsized (TArrayOf _ SizeAny) = True
    isUnsized _ = False

assumptionsOfPackage :: CompiledPackage -> [String]
assumptionsOfPackage compiled = concatMap perModule (compiledModules compiled)
  where
    perModule modu =
        let prefix = "in module " ++ Mod.renderModuleId (compiledModuleId modu) ++ ": "
            iface = compiledInterface modu
            axioms = [prefix ++ "axiom " ++ localName name ++ "(" ++ commas args ++ ")" | AxiomDef name args _ _ <- ifAxioms iface]
            externs = [prefix ++ "extern fn " ++ localName name | name <- foldr (:) [] (ifExterns iface)]
            assumes = [prefix ++ "assume " ++ renderVarProof proof | proof <- concatMap assumesIn (compiledStatements modu)]
         in axioms ++ externs ++ assumes
    localName name = reverse (takeWhile (/= '$') (reverse name))
    commas = foldr (\a b -> if null b then a else a ++ ", " ++ b) ""
    assumesIn stmt = case stmt of
        ValidationStatement (Assume proof) -> [proof]
        Assign _ (Val (VFunct _ _ _ (NativeFunct _ _ body) _)) -> concatMap assumesIn body
        Block body -> concatMap assumesIn body
        If _ yes no -> concatMap assumesIn (yes ++ no)
        While _ _ _ body -> concatMap assumesIn body
        ImplDef _ _ _ _ _ body -> concatMap assumesIn body
        BoundedDef _ inner -> assumesIn inner
        _ -> []

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
