-- REPLACING_HASKELL.md, "The frontend seed"
module ElaboratorNative
    ( frontendStage
    , frontendStageIr
    , productionTools
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Control.Exception (IOException, evaluate, try)
import qualified Data.Map.Strict as Map
import GHC.IO.Encoding (char8)
import System.Directory (renameFile)
import System.FilePath (takeDirectory, (</>))
import System.IO (IOMode (..), hClose, hGetContents, hPutStr, hSetEncoding, openFile)
import System.IO.Unsafe (unsafePerformIO)

import Bootstrap (llvmOfOwned)
import CacheLock (openTempFileCloexec)
import ElaboratorTool (Loader, nativeLoader)
import Hash (fingerprint)
import qualified Mir as M
import MirData (writeProgram)
import qualified Modules as Mod
import Native (buildExecutable, cacheDirectory, cachedProgramWithArtifacts)
import LibPackage (compileLibPackageWith)
import Link (pruneProgram)
import MirHousekeeping (eraseGhosts)
import PackageCompile (compileModulesUsing, lowerCompiledPackage)
import Pipeline (ownedModuleProgram)
import PreludeSource (elaboratePackageFiles)
import Seed (cachedFrontendSeed, compilerSnapshotHash, frontendSeedHash)
import Utils
import ValidatorNative (cachedBootstrapEmitter)

-- What reading a program the compiler is given leads to: the emitter and the checked validator, made side by side
-- (ValidatorNative.cachedBootstrapEmitter) before the first load, as the production parser's bootstrap made them
productionTools :: IO (Result () String)
productionTools = mapResult (const ()) <$> cachedBootstrapEmitter

-- The elaborator as it is now, its modules and the compiler libraries loaded and elaborated by the given loader, linked and
-- erased as the host makes its own programs
elaboratorProgramWith :: Loader -> Result M.Program String
elaboratorProgramWith loader =
    mapResult pruneProgram (compileModulesUsing loader (compileLibPackageWith loader) (Mod.Snapshot (Mod.resolverFromFiles elaboratePackageFiles) "lib/elaborate/elaborate.tersus" False)
        `bindResult` lowerCompiledPackage `bindResult` eraseGhosts)

irOf :: Result M.Program String -> IO (Result String String)
irOf program = case program `bindResult` ownedModuleProgram of
    Error e -> pure (Error e)
    Ok owned -> llvmOfOwned owned

-- Stage n of the frontend in the cache, and the key it is kept under. A stage after the seed is kept under the program
-- its executable is made of (the native part of what its elaboration gives), so stage 2 having stage 1's key is the
-- fixpoint, and then stage 2 is stage 1's executable. Each keeps the IR it was built from beside it.
frontendStage :: Int -> IO (Result (FilePath, String) String)
frontendStage n = do
    directory <- cacheDirectory
    let key = (either' directory, n)
    slot <- modifyMVar stages $ \made -> case Map.lookup key made of
        Just slot -> pure (made, slot)
        Nothing -> do
            slot <- newMVar Nothing
            pure (Map.insert key slot made, slot)
    modifyMVar slot $ \done -> case done of
        Just ready -> pure (done, ready)
        Nothing -> do
            ready <- makeStage n
            pure (Just ready, ready)

either' :: Result String String -> String
either' (Ok path) = path
either' (Error e) = e

{-# NOINLINE stages #-}
stages :: MVar (Map.Map (String, Int) (MVar (Maybe (Result (FilePath, String) String))))
stages = unsafePerformIO (newMVar Map.empty)

makeStage :: Int -> IO (Result (FilePath, String) String)
makeStage n
    | n <= 0 = mapResult (\exe -> (exe, frontendSeedHash)) <$> cachedFrontendSeed
    | otherwise = do
        before <- frontendStage (n - 1)
        case before of
            Error e -> pure (Error e)
            Ok (exe, _) -> case elaboratorProgramWith (nativeLoader exe) of
                Error e -> pure (Error ("the elaborator elaborated by stage " ++ show (n - 1) ++ ": " ++ e))
                Ok program -> do
                    let hash = fingerprint ["frontend", writeProgram program, compilerSnapshotHash]
                    built <- cachedProgramWithArtifacts [".ll"] "frontend" hash "the elaborator written in Tersus" $ \output ->
                        buildStage program (takeDirectory output </> ("frontend-" ++ hash ++ ".ll")) output
                    pure (mapResult (\path -> (path, hash)) built)

buildStage :: M.Program -> FilePath -> FilePath -> IO (Result () String)
buildStage program sidecar out = do
    ir <- irOf (Ok program)
    case ir of
        Error e -> pure (Error e)
        Ok text -> do
            built <- buildExecutable out text
            case built of
                Error e -> pure (Error e)
                Ok () -> do
                    (temporary, handle) <- openTempFileCloexec (takeDirectory out) "frontend-ir.tmp"
                    hSetEncoding handle char8
                    hPutStr handle text
                    hClose handle
                    renameFile temporary sidecar
                    pure (Ok ())

-- The IR stage n was built from
frontendStageIr :: Int -> IO (Result String String)
frontendStageIr n
    | n <= 0 = pure (Error "the seed is built from the pinned IR, not kept with it")
    | otherwise = do
        stage <- frontendStage n
        case stage of
            Error e -> pure (Error e)
            Ok (exe, _) -> do
                read' <- try (do
                    handle <- openFile (exe ++ ".ll") ReadMode
                    hSetEncoding handle char8
                    text <- hGetContents handle
                    _ <- evaluate (length text)
                    hClose handle
                    pure text) :: IO (Either IOException String)
                pure (either (\e -> Error ("the IR of stage " ++ show n ++ ": " ++ show e)) Ok read')
