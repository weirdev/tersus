module MirHousekeeping
    ( verifyProgram
    , eraseGhosts
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar, withMVar)
import Control.Exception (finally)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Directory (doesFileExist, removeFile, renameFile)
import System.FilePath ((</>))
import System.IO (hClose, hPutStrLn, openTempFile, stderr)
import System.IO.Unsafe (unsafePerformIO)

import Compile (lowerSource)
import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import Mir
import MirData (readProgram, writeProgram, writeProgramWithGhosts)
import MirEval (MirValue (..), Outcome (..), RunEnv (..), runProgramEnv)
import MirLists (lowerLists)
import MirOwnership (expandRefWrites, insertOwnership)
import MirValidate (validateProgram)
import Native (buildExecutable, cachedProgram, runWithInput, runWithInputFull)
import Seed (cachedSeed, emitterHash)
import PreludeSource (boxSource, emitterSource, listsSource, mirEraseSource, mirVerifySource)
import TersusTypes (Type (..))
import Utils

-- The housekeeping of the MIR (REPLACING_HASKELL.md target 3) is done by the programs written in Tersus for
-- it: examples/mir_verify.tersus checks that a program is well formed, and examples/mir_erase.tersus takes
-- its ghosts out. This module is the host that runs them, as Bootstrap runs the emitter written in Tersus:
-- each is built with clang from the seed when it is first needed and kept in the cache of the user, and a
-- program is given to it as data (MirData) and read back from what it writes. Where an executable cannot be
-- built (there is no clang), the same program is run by the executor of the MIR instead, which needs no
-- compiler; the answers are the same, and slower.
--
-- The data the two programs read and write does not carry everything a program holds (see MirData): a
-- function's specification, the structs with sizes (progGenerics) and the invariants are not in it, and a
-- ghost statement is written with no contents. The erasure only scrubs those (a name of a specification
-- that stands for a permission is dropped, a field of a struct with sizes that is a permission is dropped),
-- so the host puts them back on the program the eraser writes, with the ghost statements among the
-- statements they stood among. What is a permission is read off the declarations here, as the eraser in
-- Tersus reads it off the data: a Block<T>, or a struct whose fields all are.

-- Whether the program is a well formed MIR: the shape (every block a jump names is there, every local and
-- function used is declared), and the types (every operation is applied to operands of the types it takes,
-- and gives the type of the local that receives it), as examples/mir_verify.tersus checks it over the data
-- of the program. The check of a specification that only the program itself holds (that a loop is at a
-- block that is there, that a name of a specification stands for a declared local) is not in the data, and
-- is the validator's (MirValidate), which runs after this in the pipeline.
verifyProgram :: Program -> Result () String
verifyProgram program = unsafePerformIO (verifyIO program)

-- The program with its permissions taken out (POINTERS.md): what examples/mir_erase.tersus writes for the
-- program as data before the erasure (MirData.writeProgramWithGhosts), read back, with the parts the data
-- does not carry put back as the head of this module says. A Block::cast whose slots are not the same size
-- is refused, with the eraser's reason.
eraseGhosts :: Program -> Result Program String
eraseGhosts program = unsafePerformIO (eraseIO program)

verifyIO :: Program -> IO (Result () String)
verifyIO program = do
    tools <- housekeepingTools
    case checkerOf tools of
        ToolFailed e -> pure (Error e)
        ToolNative exe -> do
            (_, out, errors) <- runWithInputFull exe (writeProgram program)
            pure
                ( if trim out == "OK"
                    then Ok ()
                    else
                        if trim out == "1"
                            then Error (trimEnd errors)
                            else Error ("the checker written in Tersus answered " ++ show (take 40 out) ++ ", which is not a verdict")
                )
        ToolInterpreted checker -> pure $ case runInterpreted checker (writeProgram program) of
            Error e -> Error e
            Ok (out, errors, value)
                | value == Just (MInt 1) -> Error (trimEnd errors)
                | trim out == "OK" -> Ok ()
                | otherwise -> Error "the checker written in Tersus gave no verdict"

eraseIO :: Program -> IO (Result Program String)
eraseIO program = do
    tools <- housekeepingTools
    erased <- case eraserOf tools of
        ToolFailed e -> pure (Error e)
        ToolNative exe -> do
            (_, out, errors) <- runWithInputFull exe (writeProgramWithGhosts program)
            pure (if trim out == "1" then Error ("Validation failed: " ++ trimEnd errors) else Ok out)
        ToolInterpreted eraser -> pure $ case runInterpreted eraser (writeProgramWithGhosts program) of
            Error e -> Error e
            Ok (out, errors, value)
                | value == Just (MInt 1) -> Error ("Validation failed: " ++ trimEnd errors)
                | otherwise -> Ok out
    pure $ case erased of
        Error e -> Error e
        Ok text -> case readProgram text of
            Error e -> Error ("the eraser written in Tersus wrote what cannot be read back: " ++ e)
            Ok dataProgram -> Ok (mergeErased program dataProgram)

-- A tool of the housekeeping: an executable of the program in the cache, or the program itself for the executor
data Tool
    = ToolNative FilePath
    | ToolInterpreted Program
    | ToolFailed String

data Tools = Tools
    { checkerOf :: Tool
    , eraserOf :: Tool
    }

-- The tools, made once in this process. One making at a time: callers that reach a cold cache together
-- would otherwise each make them.
{-# NOINLINE toolsBox #-}
toolsBox :: MVar (Maybe Tools)
toolsBox = unsafePerformIO (newMVar Nothing)

-- Whether the tools are being made: making them erases the programs they are made from (with the eraser
-- itself, run by the executor), so a call that comes while they are made is answered by the executor too
{-# NOINLINE buildingRef #-}
buildingRef :: IORef Bool
buildingRef = unsafePerformIO (newIORef False)

housekeepingTools :: IO Tools
housekeepingTools = do
    building <- readIORef buildingRef
    if building
        then interpretedToolsOnce
        else modifyMVar toolsBox $ \made ->
            case made of
                Just tools -> pure (made, tools)
                Nothing -> do
                    writeIORef buildingRef True
                    tools <- nativeTools `finally` writeIORef buildingRef False
                    pure (Just tools, tools)

-- The tools run by the executor, made once in this process (they are also what a call is answered with
-- while the executables are being made, when making them erases a program itself)
{-# NOINLINE interpretedBox #-}
interpretedBox :: MVar (Maybe Tools)
interpretedBox = unsafePerformIO (newMVar Nothing)

interpretedToolsOnce :: IO Tools
interpretedToolsOnce = modifyMVar interpretedBox $ \made ->
    case made of
        Just tools -> pure (made, tools)
        Nothing -> do
            tools <- interpretedTools
            pure (Just tools, tools)

-- The executables of the checker and the eraser, built from the seed as Bootstrap builds the emitter and
-- kept beside it in the cache; the programs run by the executor when an executable cannot be built
nativeTools :: IO Tools
nativeTools = do
    checker <- cachedTool "mir-verify" mirVerifyHash
    eraser <- cachedTool "mir-erase" mirEraseHash
    case (checker, eraser) of
        (Right checkerExe, Right eraserExe) -> pure (Tools (ToolNative checkerExe) (ToolNative eraserExe))
        _ -> interpretedToolsOnce

interpretedTools :: IO Tools
interpretedTools = pure $ case (interpretedTool mirVerifySource, interpretedTool mirEraseSource) of
    (Error e, _) -> Tools (ToolFailed e) (ToolFailed e)
    (_, Error e) -> Tools (ToolFailed e) (ToolFailed e)
    (Ok checker, Ok eraser) -> Tools (ToolInterpreted checker) (ToolInterpreted eraser)

interpretedTool :: String -> Result Program String
interpretedTool source =
    lowerSource True source `bindResult` \program ->
        stage "Validation failed: " (validateProgram program) `bindResult` \_ ->
            Ok program

-- An executable of a program written in Tersus, in the cache: made by the stage 1 emitter if it is not there
cachedTool :: String -> String -> IO (Either String FilePath)
cachedTool kind hash = do
    made <- cachedProgram kind hash "the housekeeping written in Tersus" (\output -> buildTool output (if kind == "mir-verify" then mirVerifySource else mirEraseSource))
    pure $ case made of
        Error e -> Left e
        Ok exe -> Right exe

-- Stage 1 (the emitter as it is now) in the cache, made from stage 0 in the cache as Bootstrap makes it, and under the
-- same name, so the two hosts keep one emitter between them: the program it is made from is this module's own way of
-- making native code of a host program, which is the pipeline's with no erasure first (see ownedProgramOf)
cachedEmitterExe :: IO (Result FilePath String)
cachedEmitterExe = cachedProgram "emitter" emitterHash "the emitter written in Tersus" $ \output -> do
    zero <- cachedSeed
    case zero of
        Error e -> pure (Error e)
        Ok compiler -> do
            owned <- pure (ownedProgramOf emitterSource)
            case owned of
                Error e -> pure (Error e)
                Ok program -> do
                    ir <- runWithInput compiler (writeProgram program)
                    case ir of
                        Error e -> pure (Error e)
                        Ok text -> buildExecutable output text

buildTool :: FilePath -> String -> IO (Result () String)
buildTool output source = do
    emitter <- cachedEmitterExe
    case emitter of
        Error e -> pure (Error e)
        Ok exe -> do
            owned <- pure (ownedProgramOf source)
            case owned of
                Error e -> pure (Error e)
                Ok program -> do
                    ir <- runWithInput exe (writeProgram program)
                    case ir of
                        Error e -> pure (Error e)
                        Ok text -> buildExecutable output text

mirVerifyHash :: String
mirVerifyHash = fingerprint [emitterHash, mirVerifySource, runtimeSource]

mirEraseHash :: String
mirEraseHash = fingerprint [emitterHash, mirEraseSource, runtimeSource]

-- The program that native code is made of, for a source the host compiles itself (the emitter, the checker,
-- the eraser): lowered and validated, with the lists of the library, ready for insertOwnership. It is not
-- erased first: the host's own programs hold no permission at runtime (their ghosts are the statements of
-- their proofs, which the executor and the data writer alike pass over), and erasing one to make the eraser
-- would need the eraser made already. The pipeline's ownedSource is this with the erasure of a user's
-- program and the refusals of one that runs natively, which do not apply here.
ownedProgramOf :: String -> Result Program String
ownedProgramOf source =
    lowerSource True source `bindResult` \program ->
        stage "Validation failed: " (validateProgram program) `bindResult` \_ ->
            Ok (insertOwnership (lowerLists listLibrary (expandRefWrites program)))

-- The library of lists and Boxes (lib/lists.tersus and lib/box.tersus), compiled and validated once, its
-- ghosts erased with the eraser itself (it holds a permission, in a contract's ghost local)
listLibrary :: Program
listLibrary = case lowerSource False (listsSource ++ "\n" ++ boxSource) of
    Error e -> error ("lib/lists.tersus and lib/box.tersus do not lower: " ++ e)
    Ok program -> case validateProgram program of
        Error e -> error ("lib/lists.tersus and lib/box.tersus do not validate: " ++ e)
        Ok _ -> case eraseGhosts program of
            Error e -> error ("lib/lists.tersus and lib/box.tersus are not erased: " ++ e)
            Ok erased -> erased

-- Runs a program of the housekeeping with what a user of it gives on the standard input: what it wrote, what
-- it wrote to the standard error, and its value. The interpreter reads the world the program is not given, so
-- it is given none.
runInterpreted :: Program -> String -> Result (String, String, Maybe MirValue) String
runInterpreted program input = case runProgramEnv RunEnv{envArgs = [], envInput = input, envFile = const Nothing} program of
    Error e -> Error ("Evaluation failed: " ++ e)
    Ok outcome -> Ok (outStdout outcome, outStderr outcome, outValue outcome)

-- The erased program and the program it was erased from, joined: the types and the functions are the
-- eraser's, and what the data does not carry is the program's own, scrubbed of its permissions
mergeErased :: Program -> Program -> Program
mergeErased original erased =
    erased
        { progGenerics = Map.map scrubGeneric (progGenerics original)
        , progFunctions = Map.mapWithKey mergeFunction (progFunctions erased)
        , progMain = mergeFn original (progMain original) (progMain erased)
        }
  where
    scrubGeneric (params, fields) = (params, [(f, t) | (f, t) <- fields, not (ghostType original t)])
    mergeFunction name erasedFn = case Map.lookup name (progFunctions original) of
        Nothing -> erasedFn
        Just originalFn -> mergeFn original originalFn erasedFn

mergeFn :: Program -> Function -> Function -> Function
mergeFn program originalFn erasedFn =
    erasedFn
        { fnSpec = scrubbedSpec
        , fnBlocks = Map.mapWithKey mergeBlock (fnBlocks erasedFn)
        }
  where
    ghosts = Set.fromList [l | (l, d) <- Map.toList (fnLocals originalFn), ghostType program (localType d)]
    ghost l = l `Set.member` ghosts
    scrub = Map.filter (not . ghostOperand)
    ghostOperand o = case o of
        Copy l -> ghost l
        Move l -> ghost l
        Const _ -> False
    scrubbedSpec =
        (fnSpec originalFn)
            { specEnv = scrub (specEnv (fnSpec originalFn))
            , specLoops = Map.map (\ls -> ls{loopEnv = scrub (loopEnv ls)}) (specLoops (fnSpec originalFn))
            }
    mergeBlock b erasedBlock = case Map.lookup b (fnBlocks originalFn) of
        Nothing -> erasedBlock
        Just (BasicBlock originalStmts _) ->
            erasedBlock{blockStatements = mergeStatements originalStmts (blockStatements erasedBlock)}
    -- The statements the eraser wrote are the runtime statements of the original, in its order; the ghost
    -- statements go back among them where they stood, and a dissolve is the statement it became
    mergeStatements [] rest = rest
    mergeStatements (stmt : more) rest = case stmt of
        Ghost _ (GhostDissolve l)
            | ghost l -> mergeStatements more rest
            | otherwise -> takeNext rest $ \next -> next : mergeStatements more (dropNext rest)
        Ghost env g -> Ghost (scrub env) g : mergeStatements more rest
        Assign d rv
            | ghost d && d /= Local 0 -> case rv of
                ListOp op _ | not (ghostOp op) -> takeNext rest $ \next -> next : mergeStatements more (dropNext rest)
                _ -> mergeStatements more rest
        _ -> takeNext rest $ \next -> next : mergeStatements more (dropNext rest)
    takeNext [] _ = []
    takeNext (next : _) use = use next
    dropNext [] = []
    dropNext (_ : rest) = rest

-- Whether a value of the type exists only for the validator: a permission, or a struct whose fields all
-- are (and that has some), read off the declarations of the program
ghostType :: Program -> Type -> Bool
ghostType program = go (0 :: Int)
  where
    go depth ty
        | depth > 16 = False
        | otherwise = case ty of
            TBlock _ -> True
            TNamed n _ -> case Map.lookup n (progTypes program) of
                Just (StructDecl fields@(_ : _)) -> all (go (depth + 1) . snd) fields
                _ -> False
            _ -> False

trim :: String -> String
trim = dropWhileEnd . dropWhile (== '\n')
  where
    dropWhileEnd = reverse . dropWhile (== '\n') . reverse

trimEnd :: String -> String
trimEnd = reverse . dropWhile (== '\n') . reverse

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
