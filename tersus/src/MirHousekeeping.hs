{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
module MirHousekeeping
    ( verifyProgram
    , eraseGhosts
    , storageProgram
    , nativeStorage
    , cachedEmitter
    , listLibrary
    , nativeProgram
    , emitterEntry
    , mirVerifyEntry
    , mirEraseEntry
    , toolProgram
    , toolOwnedProgram
    , emitterOwnedProgram
    , ownedProgramOf
    , cachedParser
    , parserInput
    , parserIr
    , emitterKey
    , parserKey
    , validationEntry
    , prepareValidator
    , ownedContentKey
    , cachedPreparedInput
    , cachedContentKey
    , cachedUncheckedValidator
    , prepareBootstrap
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar, readMVar, withMVar)
import Control.Exception (IOException, bracket, bracket_, evaluate, finally, try)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Directory (doesFileExist, getFileSize, getModificationTime, removeFile, renameFile)
import Data.Char (isHexDigit, isSpace)
import System.FilePath (takeDirectory, takeFileName, (</>))
import System.IO (Handle, IOMode (ReadMode), hClose, hGetLine, hPutStr, hPutStrLn, stderr, withFile)
import GHC.IO.Handle.Lock (LockMode (..), hLock)
import CacheLock (openLockHandle, openTempFileCloexec, withExecutableTempFile)
import System.IO.Unsafe (unsafePerformIO)
import System.Info (os, arch)
import System.Exit (ExitCode (..))

import Hash (fingerprint)
import LibPackage (nativeStorageUnits)
import Link (linkPrograms)
import LlvmRuntime (runtimeSource)
import Mir
import MirData (readProgram, writeProgram, writeProgramWithGhosts)
import MirEval (MirValue (..), Outcome (..), RunEnv (..), runProgramEnv)
import MirLists (hasLists, lowerLists)
import MirOwnership (expandRefWrites, insertOwnership)
import Native (buildExecutable, buildExecutableWith, cacheDirectory, cacheLock, cachedProgram, cachedProgramWithArtifacts, cachedProgramIfPresent, cachedProgramIfPresentWithArtifacts, parallelBuilds, runWithInput, runWithInputFull)
import Seed (cachedSeed, cachedParserSeed, seedHash, parserSeedHash)
import Compile (lowerSource)
import Modules (ModuleId, LoadResult (..), loadFromEntry, resolverFromFiles)
import PackageCompile (compileModulesLinked)
import PreludeSource (compilerSourceHash, libPackageFiles, stdlibSource, boxSource, listsSource, mirPackageFiles, parserPackageFiles, toolPackageFiles, validationPackageFiles)
import Types (Type (..))
import Utils

-- MIR checking and ghost erasure use the programs written in Tersus. Native
-- builds are cached; recursive erasure during their bootstrap uses the MIR executor.
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
-- and gives the type of the local that receives it), as examples/mir/mir_verify/mir_verify.tersus checks it over the data
-- of the program. The check of a specification that only the program itself holds (that a loop is at a
-- block that is there, that a name of a specification stands for a declared local) is not in the data, and
-- is the validator's (the validator written in Tersus), which runs after this in the pipeline.
verifyProgram :: Program -> Result () String
verifyProgram program = unsafePerformIO (verifyIO program)

-- The program with its permissions taken out (POINTERS.md): what examples/mir/mir_erase/mir_erase.tersus writes for the
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
            let input = writeProgramWithGhosts program
            (code, out, errors) <- runWithInputFull exe input
            pure $ case code of
                ExitFailure n -> Error ("native eraser exited " ++ show n ++ ": " ++ trimEnd errors ++ "; input: " ++ show (take 80 input) ++ "; stdout: " ++ show (take 80 out))
                ExitSuccess -> if trim out == "1" then Error ("Validation failed: " ++ trimEnd errors) else Ok out
        ToolInterpreted eraser -> pure $ case runInterpreted eraser (writeProgramWithGhosts program) of
            Error e -> Error e
            Ok (out, errors, value)
                | value == Just (MInt 1) -> Error ("Validation failed: " ++ trimEnd errors)
                | otherwise -> Ok out
    pure $ case erased of
        Error e -> Error e
        Ok text -> case readProgram text of
            Error e -> Error ("the eraser written in Tersus wrote what cannot be read back: " ++ e ++ "; stdout: " ++ show (take 80 text))
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

-- Whether recursive storage erasure is initializing the tools' common library.
-- That bootstrap reentry uses the interpreter, before taking any emitter lock.
{-# NOINLINE buildingRef #-}
buildingRef :: IORef Bool
buildingRef = unsafePerformIO (newIORef False)

-- Fail before forcing or memoizing any library/tool CAF on invalid seeds.
housekeepingTools :: IO Tools
housekeepingTools = do
    parser <- cachedParserSeed
    zero <- case parser of
        Error e -> pure (Error e)
        Ok _ -> cachedSeed
    case zero of
        Error e -> pure (Tools (ToolFailed e) (ToolFailed e))
        Ok _ -> do
            building <- readIORef buildingRef
            if building
                then interpretedToolsOnce
                else modifyMVar toolsBox $ \made -> do
                    live <- case made of
                        Just tools@(Tools (ToolNative checker) (ToolNative eraser)) -> do
                            checkerPresent <- doesFileExist checker
                            eraserPresent <- doesFileExist eraser
                            pure (if checkerPresent && eraserPresent then Just tools else Nothing)
                        _ -> pure Nothing
                    tools <- case live of
                        Just ready -> pure ready
                        Nothing -> nativeTools
                    let keep = case tools of
                            Tools (ToolNative _) (ToolNative _) -> Just tools
                            _ -> Nothing
                    pure (keep, tools)

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
            let keep = case tools of
                    Tools (ToolInterpreted _) (ToolInterpreted _) -> Just tools
                    _ -> Nothing
            pure (keep, tools)

-- Storage erasure must use bootstrap reentry even when prepared tool inputs are cached.
{-# NOINLINE storageBox #-}
storageBox :: MVar (Maybe [(ModuleId, Program)])
storageBox = unsafePerformIO (newMVar Nothing)

prepareBootstrap :: IO (Result () String)
prepareBootstrap = do
    parser <- cachedParserSeed
    zero <- case parser of Error e -> pure (Error e); Ok _ -> cachedSeed
    case zero of
        Error e -> pure (Error e)
        Ok _ -> pure (Ok ())

nativeTools :: IO Tools
nativeTools = do
    initialized <- prepareBootstrap
    case initialized of
        Error e -> pure (Tools (ToolFailed e) (ToolFailed e))
        Ok () -> do
            built <- parallelBuilds [cachedEmitterExe, cachedTool "mir-verify" mirVerifyEntry,
                cachedTool "mir-erase" mirEraseEntry, cachedParserExe, cachedUncheckedValidatorExe]
            pure $ case built of
                [Ok _, Ok checker, Ok eraser, Ok _, Ok _] -> Tools (ToolNative checker) (ToolNative eraser)
                _ -> case [e | Error e <- built] of
                    e : _ -> Tools (ToolFailed e) (ToolFailed e)
                    [] -> Tools (ToolFailed "incomplete native tool build") (ToolFailed "incomplete native tool build")

interpretedTools :: IO Tools
interpretedTools = pure $ case (interpretedTool mirVerifyEntry, interpretedTool mirEraseEntry) of
    (Error e, _) -> Tools (ToolFailed e) (ToolFailed e)
    (_, Error e) -> Tools (ToolFailed e) (ToolFailed e)
    (Ok checker, Ok eraser) -> Tools (ToolInterpreted checker) (ToolInterpreted eraser)

interpretedTool :: FilePath -> Result Program String
interpretedTool = toolProgram

-- An executable of a program written in Tersus, in the cache: made by the stage 1 emitter if it is not there
cachedTool :: String -> FilePath -> IO (Result FilePath String)
cachedTool kind entry = do
    key <- derivedKey entry (toolProgram entry) []
    case key of
        Error e -> pure (Error e)
        Ok identity -> do
            existing <- cachedProgramIfPresent kind identity
            case existing of
                Error e -> pure (Error e)
                Ok (Just exe) -> pure (Ok exe)
                Ok Nothing -> do
                    prepared <- preparedDerived entry (toolProgram entry) []
                    case prepared of
                        Error e -> pure (Error e)
                        Ok (actual, _, input) -> cachedProgram kind actual "the housekeeping written in Tersus"
                            (\output -> buildPrepared [] output input)

cachedParser :: IO (Result FilePath String)
cachedParser = do
    ready <- cachedEmitter
    case ready of
        Error e -> pure (Error e)
        Ok _ -> cachedParserExe

cachedParserExe :: IO (Result FilePath String)
cachedParserExe = do
    key <- parserKey
    case key of
        Error e -> pure (Error e)
        Ok identity -> do
            existing <- cachedProgramIfPresentWithArtifacts [".ll"] "tersus-parser" identity
            case existing of
                Error e -> pure (Error e)
                Ok (Just exe) -> pure (Ok exe)
                Ok Nothing -> do
                    prepared <- preparedDerived "examples/parser/parser.tersus" (toolProgram "examples/parser/parser.tersus") []
                    case prepared of
                        Error e -> pure (Error e)
                        Ok (actual, _, input) -> cachedProgramWithArtifacts [".ll"] "tersus-parser" actual "the parser written in Tersus" $ \output -> do
                            emitter <- cachedEmitterExe
                            case emitter of
                                Error e -> pure (Error e)
                                Ok exe -> do
                                    emitted <- runWithInput exe input
                                    case emitted of
                                        Error e -> pure (Error e)
                                        Ok ir -> do
                                            built <- buildExecutable output ir
                                            case built of
                                                Error e -> pure (Error e)
                                                Ok () -> do
                                                    let path = takeDirectory output </> ("tersus-parser-" ++ actual ++ ".ll")
                                                    withExecutableTempFile (takeDirectory output) "parser-ir.tmp" $ \(temporary, handle) -> do
                                                        hPutStr handle ir
                                                        hClose handle
                                                        renameFile temporary path
                                                    pure (Ok ())

parserInput :: IO (Result String String)
parserInput = do
    ready <- prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok () -> fmap (mapResult snd) (prepareProgram "examples/parser/parser.tersus" (toolProgram "examples/parser/parser.tersus"))

parserIr :: IO (Result String String)
parserIr = do
    parser <- cachedParser
    case parser of
        Error e -> pure (Error e)
        Ok executable -> do
            stored <- try (do text <- readFile (executable ++ ".ll"); _ <- evaluate (length text); pure text) :: IO (Either IOException String)
            pure $ either (\e -> Error ("Could not read the successfully built parser IR: " ++ show e)) Ok stored

cachedUncheckedValidator :: IO (Result FilePath String)
cachedUncheckedValidator = do
    ready <- prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok _ -> cachedUncheckedValidatorExe

cachedUncheckedValidatorExe :: IO (Result FilePath String)
cachedUncheckedValidatorExe = do
    key <- derivedKey "validator" (toolProgram validationEntry) ["-O2"]
    case key of
        Error e -> pure (Error e)
        Ok identity -> do
            existing <- cachedProgramIfPresent "validator-unchecked" identity
            case existing of
                Error e -> pure (Error e)
                Ok (Just exe) -> pure (Ok exe)
                Ok Nothing -> do
                    prepared <- prepareValidator
                    case prepared of
                        Error e -> pure (Error e)
                        Ok (actual, _, input) -> cachedProgram "validator-unchecked" actual "the validator written in Tersus"
                            (\output -> buildPrepared ["-O2"] output input)

{-# NOINLINE preparationSnapshot #-}
preparationSnapshot :: String
preparationSnapshot = fingerprint [show (compilerSourceHash, seedHash, parserSeedHash,
    toolPackageFiles, libPackageFiles, stdlibSource, validationPackageFiles, runtimeSource)]

preparedInputPath :: FilePath -> FilePath -> [String] -> FilePath
preparedInputPath dir entry flags = dir </> ("prepared-" ++ fingerprint [show (preparationSnapshot, entry, flags)])

type InputStamp = (FilePath, Integer, String, String)

{-# NOINLINE preparedStamps #-}
preparedStamps :: MVar (Map.Map FilePath InputStamp)
preparedStamps = unsafePerformIO (newMVar Map.empty)

inputStamp :: FilePath -> IO InputStamp
inputStamp path = do
    size <- getFileSize path
    modified <- getModificationTime path
    header <- withFile path ReadMode hGetLine
    pure (takeFileName path, size, take 19 (show modified), header)

rememberInput :: FilePath -> String -> IO (Result String String)
rememberInput path input = do
    stamp <- inputStamp path
    modifyMVar preparedStamps $ \known -> pure (Map.insert path stamp known, Ok input)

cachedContentKey :: FilePath -> [String] -> [(FilePath, [String])] -> IO (Result String String) -> IO (Result String String)
cachedContentKey entry flags dependencies make = do
    cache <- cacheDirectory
    case cache of
        Error e -> pure (Error e)
        Ok dir -> do
            let identity = fingerprint [show (preparationSnapshot, entry, flags, os, arch)]
                path = dir </> ("content-key-" ++ identity)
                inputs = [preparedInputPath dir dependency options | (dependency, options) <- dependencies]
                decode body = case break (== '\n') body of
                    (header, '\n' : record) | header == fingerprint [identity, record] -> case reads record of
                        [((key, stamps), rest)] | all isSpace rest && length key == 16 && all isHexDigit key
                            && [file | (file, _, _, _) <- stamps] == map takeFileName inputs -> Just (key, stamps)
                        _ -> Nothing
                    _ -> Nothing
            stored <- try (do body <- readFile path; _ <- evaluate (length body); pure body) :: IO (Either IOException String)
            current <- try (mapM inputStamp inputs) :: IO (Either IOException [InputStamp])
            case (stored, current) of
                (Right body, Right stamps) | Just (key, expected) <- decode body, stamps == expected -> pure (Ok key)
                _ -> do
                    result <- make
                    case result of
                        Error e -> pure (Error e)
                        Ok key -> do
                            known <- readMVar preparedStamps
                            case traverse (`Map.lookup` known) inputs of
                                Nothing -> pure (Ok key)
                                Just stamps -> do
                                    let record = show (key, stamps)
                                    mutex <- cacheLock ("content key " ++ path)
                                    _ <- try (withMVar mutex $ \_ -> bracket (openLockHandle (path ++ ".lock")) hClose $ \lock -> do
                                        hLock lock ExclusiveLock
                                        bracket (openTempFileCloexec dir "content-key.tmp") cleanupPrepared $ \(temporary, handle) -> do
                                            hPutStr handle (fingerprint [identity, record] ++ "\n" ++ record)
                                            hClose handle
                                            renameFile temporary path) :: IO (Either IOException ())
                                    pure (Ok key)

cleanupPrepared :: (FilePath, Handle) -> IO ()
cleanupPrepared (path, handle) = do
    _ <- try (hClose handle) :: IO (Either IOException ())
    _ <- try (removeFile path) :: IO (Either IOException ())
    pure ()

cachedPreparedInput :: FilePath -> [String] -> (String -> Bool) -> IO (Result String String) -> IO (Result String String)
cachedPreparedInput entry flags valid build = do
    cache <- cacheDirectory
    case cache of
        Error e -> pure (Error e)
        Ok dir -> do
            let key = fingerprint [show (preparationSnapshot, entry, flags)]
                path = preparedInputPath dir entry flags
            mutex <- cacheLock ("prepared " ++ path)
            withMVar mutex $ \_ -> bracket (openLockHandle (path ++ ".lock")) hClose $ \handle -> do
                hLock handle ExclusiveLock
                stored <- try (do body <- readFile path; _ <- evaluate (length body); pure body) :: IO (Either IOException String)
                let payload = case stored of
                        Right body -> case break (== '\n') body of
                            (header, '\n' : input)
                                | header == fingerprint [key, input] && valid input -> Just input
                            _ -> Nothing
                        Left _ -> Nothing
                case payload of
                    Just input -> rememberInput path input
                    Nothing -> do
                        result <- build
                        case result of
                            Error e -> pure (Error e)
                            Ok input -> do
                                _ <- evaluate (length input)
                                if not (valid input) then pure (Error "invalid prepared input") else do
                                    bracket (openTempFileCloexec dir "prepared.tmp") cleanupPrepared $ \(temporary, output) -> do
                                        hPutStr output (fingerprint [key, input] ++ "\n" ++ input)
                                        hClose output
                                        renameFile temporary path
                                    rememberInput path input

{-# NOINLINE preparedPrograms #-}
preparedPrograms :: MVar (Map.Map FilePath (MVar (Maybe (Program, String))))
preparedPrograms = unsafePerformIO (newMVar Map.empty)

prepareProgram :: FilePath -> Result Program String -> IO (Result (Program, String) String)
prepareProgram entry raw = do
    slot <- modifyMVar preparedPrograms $ \made -> case Map.lookup entry made of
        Just box -> pure (made, box)
        Nothing -> do
            box <- newMVar Nothing
            pure (Map.insert entry box made, box)
    modifyMVar slot $ \made -> case made of
        Just ready -> pure (made, Ok ready)
        Nothing -> do
            input <- cachedPreparedInput entry [] valid $ pure $ raw `bindResult` \program ->
                mapResult (writeProgram . insertOwnership) (nativeProgram program)
            case input of
                Error e -> pure (Nothing, Error e)
                Ok text -> do
                    let program = case raw of Ok value -> value; Error e -> error e
                        ready = (program, text)
                    pure (Just ready, Ok ready)
  where
    valid input = case readProgram input of Ok _ -> True; Error _ -> False

ownedContentKey :: String -> String -> [String] -> String
ownedContentKey producer input flags = fingerprint [show
    (producer, input, runtimeSource, os, arch, ["-O2", "-Wno-override-module"] ++ flags)]

{-# NOINLINE preparedKeys #-}
preparedKeys :: MVar (Map.Map (FilePath, String, [String]) String)
preparedKeys = unsafePerformIO (newMVar Map.empty)

preparedContentKey :: FilePath -> String -> String -> [String] -> IO String
preparedContentKey entry producer input flags = modifyMVar preparedKeys $ \known ->
    case Map.lookup (entry, producer, flags) known of
        Just key -> pure (known, key)
        Nothing -> do
            let key = ownedContentKey producer input flags
            _ <- evaluate (length key)
            pure (Map.insert (entry, producer, flags) key known, key)

prepareEmitterInput :: IO (Result (Program, String) String)
prepareEmitterInput = prepareProgram emitterEntry (toolProgram emitterEntry)

derivedKey :: FilePath -> Result Program String -> [String] -> IO (Result String String)
derivedKey entry raw flags = cachedContentKey entry flags [(emitterEntry, []), (entry, [])] $
    fmap (mapResult (\(key, _, _) -> key)) (preparedDerived entry raw flags)

preparedDerived :: FilePath -> Result Program String -> [String] -> IO (Result (String, Program, String) String)
preparedDerived entry raw flags = do
    parts <- parallelBuilds [prepareEmitterInput, prepareProgram entry raw]
    case parts of
        [Ok (_, emitterInput), Ok (program, input)] -> do
            producer <- preparedContentKey emitterEntry seedHash emitterInput []
            key <- preparedContentKey entry producer input flags
            pure (Ok (key, program, input))
        [Error e, _] -> pure (Error e)
        [_, Error e] -> pure (Error e)
        _ -> pure (Error "incomplete native input preparation")

emitterKey :: IO (Result String String)
emitterKey = do
    ready <- prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok () -> cachedContentKey emitterEntry [] [(emitterEntry, [])] $ do
            prepared <- prepareEmitterInput
            case prepared of
                Error e -> pure (Error e)
                Ok (_, input) -> Ok <$> preparedContentKey emitterEntry seedHash input []

parserKey :: IO (Result String String)
parserKey = do
    ready <- prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok () -> derivedKey "examples/parser/parser.tersus" (toolProgram "examples/parser/parser.tersus") []

validationEntry :: FilePath
validationEntry = "lib/validation/driver.tersus"

prepareValidator :: IO (Result (String, Program, String) String)
prepareValidator = do
    ready <- prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok () -> preparedDerived "validator" (toolProgram validationEntry) ["-O2"]

-- Stage 1 (the emitter as it is now) in the cache, made from stage 0 in the cache as Bootstrap makes it, and under the
-- same name, so the two hosts keep one emitter between them: the program it is made from is this module's own way of
-- making native code of a host program, which is the pipeline's with no erasure first (see toolOwnedProgram)
-- Making the emitter's list library needs the eraser; initialize the tools before taking the emitter lock.
cachedEmitter :: IO (Result FilePath String)
cachedEmitter = do
    tools <- housekeepingTools
    case (checkerOf tools, eraserOf tools) of
        (ToolFailed e, _) -> pure (Error e)
        (_, ToolFailed e) -> pure (Error e)
        _ -> cachedEmitterExe

cachedEmitterExe :: IO (Result FilePath String)
cachedEmitterExe = do
    key <- emitterKey
    case key of
        Error e -> pure (Error e)
        Ok identity -> do
            existing <- cachedProgramIfPresent "emitter" identity
            case existing of
                Error e -> pure (Error e)
                Ok (Just exe) -> pure (Ok exe)
                Ok Nothing -> do
                    prepared <- prepareEmitterInput
                    case prepared of
                        Error e -> pure (Error e)
                        Ok (_, input) -> do
                            actual <- preparedContentKey emitterEntry seedHash input []
                            cachedProgram "emitter" actual "the emitter written in Tersus" $ \output -> do
                                zero <- cachedSeed
                                case zero of
                                    Error e -> pure (Error e)
                                    Ok compiler -> do
                                        ir <- runWithInput compiler input
                                        case ir of
                                            Error e -> pure (Error e)
                                            Ok text -> buildExecutable output text

buildPrepared :: [String] -> FilePath -> String -> IO (Result () String)
buildPrepared flags output input = do
    emitter <- cachedEmitterExe
    case emitter of
        Error e -> pure (Error e)
        Ok exe -> do
            ir <- runWithInput exe input
            case ir of
                Error e -> pure (Error e)
                Ok text -> buildExecutableWith flags output text

-- The entry files of the programs the host compiles itself, inside the mir package
emitterEntry :: FilePath
emitterEntry = "examples/mir/emit/emit.tersus"

mirVerifyEntry :: FilePath
mirVerifyEntry = "examples/mir/mir_verify/mir_verify.tersus"

mirEraseEntry :: FilePath
mirEraseEntry = "examples/mir/mir_erase/mir_erase.tersus"

-- A program of the mir package compiled through the module pipeline from the
-- embedded package files: linked, and not validated. The validator is itself
-- one of the programs the host makes (ValidatorNative), so the host's programs
-- are the bootstrap, each validated as any program is by its own tests
-- (testHostValidation). It is not erased first: the host's own programs hold
-- no permission at runtime (their ghosts are the statements of their proofs,
-- which the executor and the data writer alike pass over), and erasing one to
-- make the eraser would need the eraser made already.
{-# NOINLINE linkedPrograms #-}
linkedPrograms :: MVar (Map.Map FilePath (MVar (Maybe Program)))
linkedPrograms = unsafePerformIO (newMVar Map.empty)

{-# NOINLINE toolProgram #-}
toolProgram :: FilePath -> Result Program String
toolProgram entry = unsafePerformIO $ do
    slot <- modifyMVar linkedPrograms $ \made -> case Map.lookup entry made of
        Just box -> pure (made, box)
        Nothing -> do
            box <- newMVar Nothing
            pure (Map.insert entry box made, box)
    modifyMVar slot $ \made -> case made of
        Just program -> pure (made, Ok program)
        Nothing -> case compileToolProgram entry of
            Error e -> pure (made, Error e)
            Ok program -> pure (Just program, Ok program)

compileToolProgram :: FilePath -> Result Program String
compileToolProgram entry = case loadFromEntry (resolverFromFiles files) entry of
    Left e -> Error e
    Right (PackageResult pkg) -> compileModulesLinked pkg
    Right (StandaloneResult _ _) -> Error ("internal: " ++ entry ++ " is not in an embedded tool package")
  where
    files = if entry == validationEntry then validationPackageFiles else toolPackageFiles

-- The program that native code is made of, for a program of the mir package
-- the host compiles itself (the emitter, the checker, the eraser): with the
-- lists of the library, ready for insertOwnership.
toolOwnedProgram :: FilePath -> Result Program String
toolOwnedProgram entry =
    toolProgram entry `bindResult` \program ->
        mapResult insertOwnership (nativeProgram program)

-- The same for a single source the host compiles itself (the validator, with
-- its driver): lowered, not validated, with the lists of the library.
ownedProgramOf :: String -> Result Program String
ownedProgramOf source =
    lowerSource True source `bindResult` \program ->
        mapResult insertOwnership (nativeProgram program)

{-# NOINLINE nativeProgram #-}
nativeProgram :: Program -> Result Program String
nativeProgram program = unsafePerformIO $ do
    ready <- prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok () -> do
            let expanded = expandRefWrites program
            if not (hasLists expanded) then pure (Ok expanded) else do
                library <- listLibrary
                pure (lowerLists library expanded)

emitterOwnedProgram :: Result Program String
emitterOwnedProgram = toolOwnedProgram emitterEntry

-- The library of lists and Boxes (lib/lists.tersus and lib/box.tersus): its
-- units as native code is linked with them, and the program they link to.
-- Native code of every program, the validator's included, is made with it,
-- so it is built here without being validated; the validator, once built,
-- validates it before it is used (ValidatorNative.validatorExecutable).
nativeStorage :: Result ([(ModuleId, Program)], Program) String
nativeStorage = nativeStorageUnits `bindResult` \modules ->
    let units = [(modu, program) | (modu, _, program) <- modules]
     in linkPrograms units `bindResult` \program -> Ok (units, program)

storageProgram :: Program
storageProgram = case nativeStorage of
    Error e -> error e
    Ok (_, program) -> program

listLibrary :: IO (Result [(ModuleId, Program)] String)
listLibrary = do
    ready <- prepareBootstrap
    case ready of
        Error e -> pure (Error e)
        Ok () -> modifyMVar storageBox $ \saved -> case saved of
            Just units -> pure (saved, Ok units)
            Nothing -> do
                result <- bracket_ (writeIORef buildingRef True) (writeIORef buildingRef False) $
                    case nativeStorage `bindResult` \(units, _) -> flatResultMap eraseUnit units of
                        Error e -> pure (Error e)
                        Ok units -> do
                            _ <- evaluate (sum [length (writeProgram program) | (_, program) <- units])
                            pure (Ok units)
                let keep = case result of Ok units -> Just units; Error _ -> Nothing
                pure (keep, result)
  where
    eraseUnit (modu, program) = mapResult ((,) modu) (eraseGhosts program)

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
