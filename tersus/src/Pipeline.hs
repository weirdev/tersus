{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}

module Pipeline
    ( parseSource
    , parseWithEquality
    , validatedSource
    , compileSource
    , validatedSourceWith
    , compileSourceWith
    , loadFromEntry
    , loadFromFilesystem
    , CompiledModule (..)
    , CompiledPackage (..)
    , compileModules
    , compileModulesValidated
    , compileModulesBootstrap
    , compileModulesToProgram
    , compileModulesToOwned
    , erasedModuleProgram
    , ownedModuleProgram
    , assumptionsOfPackage
    , ownedSource
    , ownedOfProgram
    , nativeProgram
    , validateStatements
    , runStatements
    , assumptionsOf
    ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Mir as M
import Compile (SourceParts, lowerSourceParts, lowerStatements)
import TersusParser (parseSource, parseWithEquality)
import qualified TersusParser
import PackageCompile (CompiledModule (..), CompiledPackage (..), assumptionsOfPackage, compileModules, compileModulesLinked)
import Link (pruneProgram)
import qualified Modules as Mod
import MirOwnership (expandRefWrites, insertOwnership)
import MirHousekeeping (eraseGhosts, verifyProgram)
import qualified MirHousekeeping as Housekeeping
import MirEval (MirValue, runProgram)
import ValidatorNative (validateCompiled)
import MirLists (hasLists, lowerLists)
import System.IO.Unsafe (unsafePerformIO)
import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Pretty (renderVarProof)
import Syntax (Expression (..), FunctBody (..), Statement (..), ValidationStatement (..), Value (..), exprToProof)
import Types (Size (..), Type (..))
import Utils

-- The stages a program goes through, each built on the one before and each giving back what the next needs:
--
--   source -> AST (TersusParser.parseSourceParts; Compile stays the explicit Haskell oracle/bootstrap)
--          -> checked AST (elaborate) -> MIR (lowering, in Compile) -> checked MIR (verifyProgram) -> validated MIR (validateCompiled: the validator written in Tersus, compiled to native code) -> executed (runProgram)
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
-- (examples/mir/mir_erase/mir_erase.tersus) is given, as `tersus mir --ghost-data` writes it
validatedSource :: String -> Result M.Program String
validatedSource = validatedSourceWith TersusParser.parseSourceParts

validatedSourceWith :: (Bool -> String -> Result SourceParts String) -> String -> Result M.Program String
validatedSourceWith readSource source =
    readSource True source `bindResult` lowerSourceParts True `bindResult` \program ->
        checkedLowered program `bindResult` \checked ->
            stage "Validation failed: " (validateCompiled checked) `bindResult` \_ ->
                Ok checked

-- The MIR of a program that passes every check
compileSource :: String -> Result M.Program String
compileSource = compileSourceWith TersusParser.parseSourceParts

compileSourceWith :: (Bool -> String -> Result SourceParts String) -> String -> Result M.Program String
compileSourceWith readSource source = validatedSourceWith readSource source `bindResult` eraseGhosts

-- The production file boundary; the default Modules loaders remain the isolated bootstrap path.
loadFromEntry :: Mod.Resolver -> FilePath -> Either String Mod.LoadResult
loadFromEntry = Mod.loadFromEntryWith TersusParser.parseFileWith

loadFromFilesystem :: FilePath -> IO (Either String Mod.LoadResult)
loadFromFilesystem = Mod.loadFromFilesystemWith TersusParser.parseFileWith

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
        else nativeProgram program `bindResult` \native ->
            let owned = insertOwnership native
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
{-# NOINLINE nativeProgram #-}
nativeProgram :: M.Program -> Result M.Program String
nativeProgram program = unsafePerformIO $ do
    ready <- Housekeeping.prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok () -> do
            let expanded = expandRefWrites program
            if not (hasLists expanded) then pure (Ok expanded) else do
                library <- listLibrary
                pure (lowerLists library expanded)

{-# NOINLINE checkedStorageBox #-}
checkedStorageBox :: MVar (Maybe [(Mod.ModuleId, M.Program)])
checkedStorageBox = unsafePerformIO (newMVar Nothing)

listLibrary :: IO (Result [(Mod.ModuleId, M.Program)] String)
listLibrary = do
    ready <- Housekeeping.prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok () -> modifyMVar checkedStorageBox $ \saved -> case saved of
            Just units -> pure (saved, Ok units)
            Nothing -> do
                result <- case Housekeeping.nativeStorage `bindResult` \(_, program) -> checkedLowered program of
                    Error e -> pure (Error e)
                    Ok _ -> Housekeeping.listLibrary
                let keep = case result of Ok units -> Just units; Error _ -> Nothing
                pure (keep, result)

-- Checks and validates a program given as statements, with the validator written in Tersus
validateStatements :: [Statement] -> Result () String
validateStatements stmts =
    lowerStatements stmts `bindResult` \program ->
        (case verifyProgram program of
            Ok () -> Ok program
            Error e -> Error ("Lowering produced a malformed program: " ++ e))
            `bindResult` validateCompiled

-- Runs a program given as statements, once it type checks, without validating it
runStatements :: [Statement] -> Result (Maybe MirValue) String
runStatements stmts =
    lowerStatements stmts `bindResult` \program ->
        (case verifyProgram program of
            Ok () -> Ok program
            Error e -> Error ("Lowering produced a malformed program: " ++ e))
            `bindResult` eraseGhosts `bindResult` runProgram


-- A package's modules lowered, linked and validated (by the validator
-- written in Tersus, as a single-file program is)
compileModulesValidated :: Mod.LoadedPackage -> Result M.Program String
compileModulesValidated pkg =
    compileModulesLinked pkg `bindResult` \linked ->
        stage "Validation failed: " (validateCompiled (oneMarkerEach linked)) `bindResult` \_ -> Ok linked

-- Linking makes one function of a definition several modules make alike (a
-- library each module is given, an identical extern), and each module's
-- marker of that definition stays: one of each is kept for the validator,
-- which would take two for two definitions of one function.
oneMarkerEach :: M.Program -> M.Program
oneMarkerEach program =
    let (seen, main') = dedupeFunction Set.empty (M.progMain program)
        (_, functions') = Map.mapAccum dedupeFunction seen (M.progFunctions program)
     in program{M.progMain = main', M.progFunctions = functions'}
  where
    dedupeFunction seen fn =
        let (seen', blocks') = Map.mapAccum dedupeBlock seen (M.fnBlocks fn)
         in (seen', fn{M.fnBlocks = blocks'})
    dedupeBlock seen block =
        let (kept, seen') = foldl keep ([], seen) (M.blockStatements block)
         in (seen', block{M.blockStatements = reverse kept})
    keep (acc, seen) statement = case statement of
        M.Ghost _ (M.GhostFunction name _ _)
            | Set.member name seen -> (acc, seen)
            | otherwise -> (statement : acc, Set.insert name seen)
        _ -> (statement : acc, seen)

-- A package of the compiler's own programs as the host builds it: linked,
-- its ghosts erased, not validated (see MirHousekeeping.toolProgram)
compileModulesBootstrap :: Mod.LoadedPackage -> Result M.Program String
compileModulesBootstrap pkg = mapResult pruneProgram (compileModulesLinked pkg `bindResult` eraseGhosts)

compileModulesToProgram :: Mod.LoadedPackage -> Result M.Program String
compileModulesToProgram pkg = compileModulesValidated pkg `bindResult` erasedModuleProgram

erasedModuleProgram :: M.Program -> Result M.Program String
erasedModuleProgram = mapResult pruneProgram . eraseGhosts

compileModulesToOwned :: Mod.LoadedPackage -> Result M.Program String
compileModulesToOwned pkg = compileModulesToProgram pkg `bindResult` ownedModuleProgram

ownedModuleProgram :: M.Program -> Result M.Program String
ownedModuleProgram program =
    if any unsizedRef (M.progMain program : Map.elems (M.progFunctions program))
        then Error "a reference to an unsized value (&Array<T>) is not in native code yet: run it with eval, or check it"
        else nativeProgram program `bindResult` \native ->
            let owned = pruneProgram (insertOwnership native)
             in stage "Ownership failed: " (verifyProgram owned) `bindResult` \_ -> Ok owned
  where
    unsizedRef fn = any (\d -> hasUnsizedRef (M.localType d)) (Map.elems (M.fnLocals fn)) || maybe False hasUnsizedRef (M.fnReturns fn)
    hasUnsizedRef ty = case ty of
        TRef inner -> isUnsized inner
        TMutRef inner -> isUnsized inner
        _ -> False
    isUnsized (TArrayOf _ SizeAny) = True
    isUnsized _ = False


stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
