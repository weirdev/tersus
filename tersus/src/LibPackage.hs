module LibPackage
    ( LibPackage (..)
    , libPackage
    , compileLibPackageWith
    , nativeStorageUnits
    , nativeStorageUnitsWith
    , libModuleNames
    , libModuleId
    , libUnit
    , libCatalog
    , libraryBoundedNames
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar, tryReadMVar)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

import ElaborateRequest (Library (..), LoadKind (..), LoadRequest (..), LoadResponse (..), Response (..), acceptedOwnership)
import ElaboratorTool (Loader, bootstrapLoader)
import Interface (ModuleInterface (..))
import qualified Mir as M
import Lowering (lowerAccepted)
import MirMoves (finishLowered)
import Modules (Snapshot (..), loadRequest)
import PackageData (ModuleId (..), defaultLoadOptions, renderModuleId, resolverFromFiles, resolverOptions, noPrelude)
import PreludeSource (libModuleOf, libModules, nativeStorageModules, stdName)
import Types (OwnershipTransport)
import Utils (Result (..), bindResult)

-- Installed std package compilation cache: every std module and native storage helper compiles through the ordinary
-- LoadPackage path over the embedded std package with noPrelude = true. Native storage units never enter the prelude.

libModuleNames :: [String]
libModuleNames = nub [libModuleOf name | (name, _, _) <- libModules, libModuleOf name `notElem` nativeStorageModules]

libModuleId :: String -> ModuleId
libModuleId name = ModuleId "std" (Just name)

data LibPackage = LibPackage
    { libInterfaces :: Map.Map String ModuleInterface
    , libLowered :: Map.Map String (Result M.Lowered String)
    , libOwnership :: Map.Map String (Maybe OwnershipTransport)
    , libPrograms :: Map.Map String M.Program
    , libOrder :: [String]
    , libImports :: Map.Map String [String]
    }
    deriving (Show)

type NativeUnits = [(ModuleId, ModuleInterface, M.Program)]

driverSnapshot :: [String] -> Snapshot
driverSnapshot modules =
    Snapshot
        ((resolverFromFiles
            [ ("driver/package.tersus", "noPrelude = true;")
            , ("driver/main.tersus", unlines (["import std::" ++ m ++ ";" | m <- modules] ++ ["return 0;"]))
            ]){resolverOptions = defaultLoadOptions{noPrelude = True}})
        "driver/main.tersus"
        False

compiledLibraries :: Loader -> (Result LibPackage String, Result NativeUnits String)
compiledLibraries loader = case loader (loadRequest LoadPackage (driverSnapshot libModuleNames)) of
    NotLoaded e -> (Error e, Error e)
    LoadedModules answers -> case collectStd answers (LibPackage Map.empty Map.empty Map.empty Map.empty [] Map.empty) of
        Error e -> (Error e, Error e)
        Ok pkg ->
            let natives = case loader ((loadRequest LoadPackage (driverSnapshot nativeStorageModules)){lrLibraries = libCatalog pkg}) of
                    NotLoaded e -> Error e
                    LoadedModules nAnswers -> collectNatives nAnswers []
                    _ -> Error "internal: the loader did not answer with the std native storage modules"
             in (Ok pkg, natives)
    _ -> let e = "internal: the loader did not answer with the installed std package" in (Error e, Error e)
  where
    collectStd [] pkg = Ok pkg{libOrder = reverse (libOrder pkg)}
    collectStd ((ModuleId "driver" Nothing, _, Accepted{}) : rest) pkg = collectStd rest pkg
    collectStd ((moduId@(ModuleId "std" (Just name)), deps, response) : rest) pkg =
        let inModule err = "in std module " ++ renderModuleId moduId ++ ": " ++ err
            stdDeps = [m | ModuleId "std" (Just m) <- deps]
         in case response of
                Accepted (Just iface) _ _ ->
                    let lowered = lowerAccepted response
                        facts = acceptedOwnership response
                     in case lowered `bindResult` finishLowered of
                            Error err -> Error (inModule err)
                            Ok program -> collectStd rest pkg
                                { libInterfaces = Map.insert name iface (libInterfaces pkg)
                                , libLowered = Map.insert name lowered (libLowered pkg)
                                , libOwnership = Map.insert name facts (libOwnership pkg)
                                , libPrograms = Map.insert name program (libPrograms pkg)
                                , libOrder = name : libOrder pkg
                                , libImports = Map.insert name stdDeps (libImports pkg)
                                }
                Accepted Nothing _ _ -> Error (inModule "the elaborator gave no interface")
                Refused err -> Error (inModule err)
                RefusedInterface err -> Error err
                Unresolved err -> Error err
                NotModelled what -> Error (inModule ("the elaborator does not handle this module yet: " ++ what))
    collectStd ((moduId, _, response) : _) _ = Error ("in module " ++ renderModuleId moduId ++ ": " ++ show response)

    collectNatives [] done = Ok (reverse done)
    collectNatives ((ModuleId "driver" Nothing, _, Accepted{}) : rest) done = collectNatives rest done
    collectNatives ((moduId@(ModuleId "std" (Just name)), _, response) : rest) done
        | name `elem` nativeStorageModules =
            let inModule err = "in std module " ++ renderModuleId moduId ++ ": " ++ err
             in case response of
                    Accepted (Just iface) _ _ -> case lowerAccepted response `bindResult` finishLowered of
                        Error err -> Error (inModule err)
                        Ok program -> collectNatives rest ((moduId, iface, program) : done)
                    Accepted Nothing _ _ -> Error (inModule "the elaborator gave no interface")
                    Refused err -> Error (inModule err)
                    RefusedInterface err -> Error err
                    Unresolved err -> Error err
                    NotModelled what -> Error (inModule ("the elaborator does not handle this module yet: " ++ what))
        | otherwise = collectNatives rest done
    collectNatives ((moduId, _, response) : _) _ = Error ("in module " ++ renderModuleId moduId ++ ": " ++ show response)

compileLibPackageWith :: Loader -> Result LibPackage String
compileLibPackageWith loader = fst (compiledLibraries loader)

nativeStorageUnitsWith :: Loader -> Result NativeUnits String
nativeStorageUnitsWith loader = snd (compiledLibraries loader)

{-# NOINLINE libraryCache #-}
libraryCache :: MVar (Maybe (Result LibPackage String, Result NativeUnits String))
libraryCache = unsafePerformIO (newMVar Nothing)

bootstrapLibraries :: (Result LibPackage String, Result NativeUnits String)
bootstrapLibraries = unsafePerformIO $ modifyMVar libraryCache $ \cached -> case cached of
    Just result -> pure (cached, result)
    Nothing ->
        let result@(libraries, natives) = compiledLibraries bootstrapLoader
            forced = either' (Map.size . libInterfaces) libraries `seq` either' length natives `seq` result
         in pure (Just forced, forced)
  where
    either' f (Ok a) = f a
    either' _ (Error e) = length e

libPackage :: Result LibPackage String
libPackage = fst bootstrapLibraries

{-# NOINLINE libraryBoundedNames #-}
libraryBoundedNames :: Int -> Set.Set String
libraryBoundedNames for = for `seq` unsafePerformIO (do
    state <- tryReadMVar libraryCache
    pure $ case state of
        Nothing -> Set.empty
        Just Nothing -> names libPackage
        Just (Just (libraries, _)) -> names libraries)
  where
    names (Ok pkg) = Set.fromList [name | library <- libOrder pkg, name <- Map.keys (M.progBounded (libPrograms pkg Map.! library))]
    names (Error _) = Set.empty

nativeStorageUnits :: Result NativeUnits String
nativeStorageUnits = snd bootstrapLibraries

libCatalog :: LibPackage -> [Library]
libCatalog pkg = [Library name (Map.findWithDefault [] name (libImports pkg)) iface | name <- libOrder pkg, Just iface <- [Map.lookup name (libInterfaces pkg)]]

libUnit :: LibPackage -> String -> Result (ModuleId, M.Program) String
libUnit pkg name = case Map.lookup name (libPrograms pkg) of
    Just program
        | name == "core" -> Ok (libModuleId name, program{M.progCaptureStorage = Map.restrictKeys (M.progGenerics program) (Set.fromList [stdName "core/types" "List", stdName "core/types" "Box"])})
        | otherwise -> Ok (libModuleId name, program)
    Nothing -> Error ("internal: no compiled unit for std module " ++ name)
