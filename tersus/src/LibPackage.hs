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
    , stripDeclaredFromUnit
    , stripDeclaredFromUnits
    , libraryBoundedNames
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar, tryReadMVar)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

import ElaborateRequest (Library (..), LibraryAnswer (..), LoadKind (..), LoadRequest (..), LoadResponse (..), Response (..))
import ElaboratorTool (Loader, bootstrapLoader)
import Interface (ModuleInterface (..))
import qualified Mir as M
import Lowering (lowerAccepted)
import MirMoves (finishLowered)
import Modules (libraryRequest)
import PackageData (ModuleId (..), renderModuleId)
import PreludeSource (libModuleOf, libModules, nativeStorageModules, stdName)
import Utils (Result (..), bindResult)

-- The implicit libraries and native storage helpers are the modules of the std package (lib/std), read and elaborated by
-- the loader written in Tersus in one load; the host lowers them. Native units never enter user-facing selection.

libModuleNames :: [String]
libModuleNames = nub [libModuleOf name | (name, _, _) <- libModules, libModuleOf name `notElem` nativeStorageModules]

libModuleId :: String -> ModuleId
libModuleId name = ModuleId "std" (Just name)

data LibPackage = LibPackage
    { libInterfaces :: Map.Map String ModuleInterface
    , libPrograms :: Map.Map String M.Program
    , libOrder :: [String]
    , libImports :: Map.Map String [String]
    }
    deriving (Show)

type NativeUnits = [(ModuleId, ModuleInterface, M.Program)]

-- Every library and native helper, lowered: the libraries in order, then the helpers, each against the interfaces of
-- the libraries it imports. A helper that fails fails the helpers alone.
compiledLibraries :: Loader -> (Result LibPackage String, Result NativeUnits String)
compiledLibraries loader = case loader libraryRequest of
    LoadedLibraries answers failure -> go answers (LibPackage Map.empty Map.empty [] Map.empty) [] failure
    NotLoaded e -> (Error e, Error e)
    _ -> let e = "internal: the loader did not answer with the compiler libraries" in (Error e, Error e)
  where
    complete pkg = pkg{libOrder = reverse (libOrder pkg)}
    failed pkg e
        | length (libOrder pkg) == length libModuleNames = (Ok (complete pkg), Error e)
        | otherwise = (Error e, Error e)
    go [] pkg natives failure = case failure of
        Just e -> failed pkg e
        Nothing -> (Ok (complete pkg), Ok (reverse natives))
    go (LibraryAnswer name imports _ response : rest) pkg natives failure =
        let moduId = libModuleId name
            inModule err = "in lib module " ++ renderModuleId moduId ++ ": " ++ err
         in case response of
                Accepted (Just iface) _ _ -> case lowerAccepted response `bindResult` finishLowered of
                    Error err -> failed pkg (inModule err)
                    Ok program
                        | name `elem` nativeStorageModules -> go rest pkg ((moduId, iface, program) : natives) failure
                        | otherwise -> go rest pkg
                            { libInterfaces = Map.insert name iface (libInterfaces pkg)
                            , libPrograms = Map.insert name program (libPrograms pkg)
                            , libOrder = name : libOrder pkg
                            , libImports = Map.insert name imports (libImports pkg)
                            } natives failure
                Accepted Nothing _ _ -> failed pkg (inModule "the elaborator gave no interface")
                Refused err -> failed pkg (inModule err)
                RefusedInterface err -> failed pkg err
                Unresolved err -> failed pkg err
                NotModelled what -> failed pkg (inModule ("the elaborator does not handle this module yet: " ++ what))

compileLibPackageWith :: Loader -> Result LibPackage String
compileLibPackageWith loader = fst (compiledLibraries loader)

nativeStorageUnitsWith :: Loader -> Result NativeUnits String
nativeStorageUnitsWith loader = snd (compiledLibraries loader)

{-# NOINLINE libraryCache #-}
libraryCache :: MVar (Maybe (Result LibPackage String, Result NativeUnits String))
libraryCache = unsafePerformIO (newMVar Nothing)

-- The libraries the seed elaborates, made on first use and kept for the process
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

-- The functions with bounds of the compiler's libraries, for a program given as statements that may carry them among
-- its own (Compile.lowerStatementsWith). It does not take the cache's lock: while the libraries are being made (the
-- cache is taken, by this thread through a loader that lowers statements, or by another) there are none, and every
-- function with bounds is the program's own. Otherwise reading them makes them, or waits for another thread to finish
-- evaluating them. The argument, which it ignores, keeps each use its own (a program's statements).
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

-- A library unit lowered against the types its fellow libraries declare
-- carries those types' declarations and invariants seeded from their
-- interfaces; where the program being linked declares such a name itself
-- (which kept the declaring library out of its selection), the program's
-- own declaration is the one the link must see, as it is the one the
-- elaborator gave the program (lib/elaborate/libraries.tersus).
stripDeclaredFromUnits :: [String] -> [(ModuleId, M.Program)] -> [(ModuleId, M.Program)]
stripDeclaredFromUnits declared = map (stripDeclaredFromUnit (Set.fromList declared))

stripDeclaredFromUnit :: Set.Set String -> (ModuleId, M.Program) -> (ModuleId, M.Program)
stripDeclaredFromUnit declared (moduId, program) =
    ( moduId
    , program
        { M.progTypes = Map.withoutKeys (M.progTypes program) declared
        , M.progGenerics = Map.withoutKeys (M.progGenerics program) declared
        , M.progInvariants = Map.withoutKeys (M.progInvariants program) declared
        , M.progCaptureStorage = Map.withoutKeys (M.progCaptureStorage program) declared
        , M.progFunctions = Map.withoutKeys (M.progFunctions program) replacedBounded
        , M.progBounded = Map.withoutKeys (M.progBounded program) declared
        }
    )
  where
    -- (a function with bounds of the library that the module defines itself, as a replacement Eq's impls do, is the
    -- module's: a library's function with bounds is in its unit only to be copied, and the module's copies are of its own)
    replacedBounded =
        Set.fromList (concat [name : M.boundedLifted bounded | (name, bounded) <- Map.toList (M.progBounded program), name `Set.member` declared])

libCatalog :: LibPackage -> [Library]
libCatalog pkg = [Library name (Map.findWithDefault [] name (libImports pkg)) iface | name <- libOrder pkg, Just iface <- [Map.lookup name (libInterfaces pkg)]]

libUnit :: LibPackage -> String -> Result (ModuleId, M.Program) String
libUnit pkg name = case Map.lookup name (libPrograms pkg) of
    Just program
        | name == "core" -> Ok (libModuleId name, program{M.progCaptureStorage = Map.restrictKeys (M.progGenerics program) (Set.fromList [stdName "core/types" "List", stdName "core/types" "Box"])})
        | otherwise -> Ok (libModuleId name, program)
    Nothing -> Error ("internal: no compiled unit for assembly library " ++ name)

