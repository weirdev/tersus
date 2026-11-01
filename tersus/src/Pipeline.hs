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
import Compile (lowerSource, lowerStatements, parseSource, parseWithEquality)
import Interface (ModuleInterface, extractInterface, mergeInterfacesImportEnv, nameInModule, predeclareOwnEnv)
import Link (linkPrograms, pruneProgram)
import ModuleResolve (rewriteFileReferences)
import qualified Modules as Mod
import Parse (ParsedFile (..), emptyDecls, parseStatementBlockWith)
import PreludeSource (preludeSource)
import MirOwnership (expandRefWrites, insertOwnership)
import MirHousekeeping (eraseGhosts, verifyProgram, validatedListLibrary)
import qualified MirHousekeeping as Housekeeping
import MirEval (MirValue, runProgram)
import MirLower (lowerModuleWith)
import MirValidate (Validated, validateProgram)
import MirLists (lowerLists)
import Pretty (renderVarProof)
import Syntax (Expression (..), FunctBody (..), Statement (..), ValidationStatement (..), Value (..), exprToProof)
import TypeCheck (Elaborated (..), elaborateWith)
import Types (Size (..), Type (..), baseNameOf)
import Utils

-- The stages a program goes through, each built on the one before and each giving back what the next needs:
--
--   source -> AST (parseSource, in Compile) -> checked AST (elaborate: types checked, each `shrinks` resolved)
--          -> MIR (lowering, in Compile) -> checked MIR (verifyProgram) -> validated MIR (validateProgram) -> executed (runProgram)
--                                                                    or -> owned MIR (ownedSource) -> LLVM IR (the emitter written in Tersus, see Bootstrap)
--
-- The validated MIR has its permissions (ghost values, POINTERS.md) taken out by `eraseGhosts` before anything runs it or makes native code of it.
-- The check of the MIR and the erasure are the programs written in Tersus for them, run by MirHousekeeping.
--
-- The program is type checked once, by `elaborate`; the lowering takes its result and the validator the MIR. Errors name
-- the stage that refused the program, as the command line prints them.

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
    lowerSource True source `bindResult` \program ->
        checkedLowered program `bindResult` \checked ->
            stage "Validation failed: " (validateProgram checked) `bindResult` \_ ->
                Ok checked

-- The MIR of a program that passes every check
compileSource :: String -> Result M.Program String
compileSource source =
    lowerSource True source `bindResult` \program ->
        checkedLowered program `bindResult` \checked ->
            stage "Validation failed: " (validateProgram checked) `bindResult` \_ ->
                eraseGhosts checked

-- A lowered program that the checker written in Tersus (MirHousekeeping) accepts; a refusal is the
-- lowering's, as it was when the lowering checked its own work
checkedLowered :: M.Program -> Result M.Program String
checkedLowered program = case verifyProgram program of
    Ok () -> Ok program
    Error e -> Error ("Lowering failed: Lowering produced a malformed program: " ++ e)

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

-- The program that native code is made of: a validated program with each list and Box made of the library's structs (see MirLists).
-- Each Uninit<T> is already a T in it: the erasure makes it one (it is laid out as one: an empty one is the words of a T cleared, which own nothing)
nativeProgram :: M.Program -> M.Program
nativeProgram = lowerLists listLibrary . expandRefWrites

-- The library of lists and Boxes (lib/lists.tersus and lib/box.tersus), compiled and validated once
listLibrary :: M.Program
listLibrary = case checkedLowered validatedListLibrary of
    Ok _ -> Housekeeping.listLibrary
    Error e -> error ("lib/lists.tersus and lib/box.tersus do not compile: " ++ e)

-- Checks and validates a program given as statements
validateStatements :: [Statement] -> Result Validated String
validateStatements stmts =
    lowerStatements stmts `bindResult` \program ->
        (case verifyProgram program of
            Ok () -> Ok program
            Error e -> Error ("Lowering produced a malformed program: " ++ e))
            `bindResult` validateProgram

-- Runs a program given as statements, once it type checks, without validating it
runStatements :: [Statement] -> Result (Maybe MirValue) String
runStatements stmts =
    lowerStatements stmts `bindResult` \program ->
        (case verifyProgram program of
            Ok () -> Ok program
            Error e -> Error ("Lowering produced a malformed program: " ++ e))
            `bindResult` eraseGhosts `bindResult` runProgram

data CompiledModule = CompiledModule
    { compiledModuleId :: Mod.ModuleId
    , compiledStatements :: [Statement]
    , compiledElaborated :: Elaborated
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
                                Right () ->
                                    let augmented = if needsDropTrait prepared then dropTraitStatements ++ prepared else prepared
                                     in case elaborateWith env augmented of
                                            Error err -> Error ("in module " ++ Mod.renderModuleId moduId ++ ": " ++ err)
                                            Ok (elaborated@(Elaborated elaboratedStmts _), state) -> case extractInterface moduId augmented elaboratedStmts state of
                                                Error err -> Error err
                                                Ok iface -> Ok (CompiledModule moduId elaboratedStmts elaborated iface)

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
    baseOf name = baseNameOf name

compileModulesValidated :: Mod.LoadedPackage -> Result M.Program String
compileModulesValidated pkg =
    compileModules pkg `bindResult` \compiled ->
        let ifaceMap = Map.fromList [(compiledModuleId modu, compiledInterface modu) | modu <- compiledModules compiled]
            loadedMap = Map.fromList [(Mod.loadedModuleId modu, modu) | modu <- Mod.packageModules pkg]
            lowerOne modu = case Map.lookup (compiledModuleId modu) loadedMap of
                Nothing -> Error ("internal: compiled module " ++ Mod.renderModuleId (compiledModuleId modu) ++ " is not in the loaded package")
                Just loaded ->
                    let depIfaces = [ifaceMap Map.! dep | dep <- Mod.loadedDependencies loaded, Map.member dep ifaceMap]
                     in mapResult (\program -> (compiledModuleId modu, program)) (stage "Lowering failed: " (lowerModuleWith (mergeInterfacesImportEnv depIfaces) depIfaces (compiledElaborated modu)))
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
