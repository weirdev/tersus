module Pipeline
    ( parseSource
    , parseWithEquality
    , validatedSource
    , compileSource
    , ownedSource
    , nativeProgram
    , validateStatements
    , runStatements
    , assumptionsOf
    ) where

import qualified Data.Map as Map
import qualified Mir as M
import MirOwnership (expandRefWrites, insertOwnership)
import MirVerify (verifyProgram)
import MirEval (MirValue, runProgram)
import MirGhost (eraseGhosts, withoutUninit)
import MirLower (lowerElaborated, lowerLibrary)
import ValidatorNative (validateCompiled)
import Libraries (parseSource, parseSourceWith, parseWithEquality)
import MirLists (lowerLists)
import PreludeSource (boxSource, listsSource)
import Pretty (renderVarProof)
import TersusTypes (Expression (..), FunctBody (..), Size (..), Statement (..), Type (..), ValidationStatement (..), Value (..), exprToProof)
import TypeCheck (elaborate)
import Utils

-- The stages a program goes through, each built on the one before and each giving back what the next needs:
--
--   source -> AST (parseSource) -> checked AST (elaborate: types checked, each `shrinks` resolved)
--          -> MIR (lowerElaborated) -> validated MIR (validateCompiled: the validator written in Tersus, compiled to native code) -> executed (runProgram)
--                                                                    or -> owned MIR (ownedSource) -> LLVM IR (the emitter written in Tersus, see Bootstrap)
--
-- The validated MIR has its permissions (ghost values, POINTERS.md) taken out by `eraseGhosts` before anything runs it or makes native code of it.
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
    parseSourceWith True source `bindResult` \stmts ->
        stage "Validation failed: " (elaborate stmts) `bindResult` \elaborated ->
            stage "Lowering failed: " (lowerElaborated elaborated) `bindResult` \program ->
                stage "Validation failed: " (validateCompiled program) `bindResult` \_ ->
                    Ok program

-- The MIR of a program that passes every check
compileSource :: String -> Result M.Program String
compileSource = compileWith True

compileWith :: Bool -> String -> Result M.Program String
compileWith reserving source =
    parseSourceWith reserving source `bindResult` \stmts ->
        stage "Validation failed: " (elaborate stmts) `bindResult` \elaborated ->
            stage "Lowering failed: " ((if reserving then lowerElaborated else lowerLibrary) elaborated) `bindResult` \program ->
                stage "Validation failed: " (validateCompiled program) `bindResult` \_ ->
                    eraseGhosts program

-- The MIR of a program that passes every check, with who owns each value made explicit (MirOwnership), for native code
ownedSource :: String -> Result M.Program String
ownedSource source =
    compileSource source `bindResult` \program ->
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

-- Checks and validates a program given as statements, with the validator
-- written in Tersus
validateStatements :: [Statement] -> Result () String
validateStatements stmts =
    elaborate stmts `bindResult` \elaborated ->
        lowerElaborated elaborated `bindResult` validateCompiled

-- Runs a program given as statements, once it type checks, without validating it
runStatements :: [Statement] -> Result (Maybe MirValue) String
runStatements stmts =
    elaborate stmts `bindResult` \elaborated ->
        lowerElaborated elaborated `bindResult` eraseGhosts `bindResult` runProgram

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
