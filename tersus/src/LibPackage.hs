module LibPackage
    ( LibPackage (..)
    , libPackage
    , compileLibPackageWith
    , nativeStorageUnits
    , nativeStorageUnitsWith
    , libModuleNames
    , libModuleId
    , libSelection
    , libCatalog
    , stripDeclaredFromUnits
    , withoutReplacedEq
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

import ElaborateRequest (Library (..), LibraryAnswer (..), LoadKind (..), LoadRequest (..), LoadResponse (..), Response (..))
import ElaboratorTool (Loader, bootstrapLoader)
import Interface (ModuleInterface (..))
import qualified Mir as M
import MirLower (lowerModuleWith)
import Modules (librarySources)
import PackageData (ModuleId (..), renderModuleId, resolverFromFiles)
import PreludeSource (libModules, nativeStorageModules)
import Syntax (Statement (..))
import Utils (Result (..))

-- The implicit libraries and native storage helpers share one compiler-owned package, read and elaborated by the
-- loader written in Tersus in one load; the host lowers them. Native units never enter user-facing selection.

libModuleNames :: [String]
libModuleNames = [name | (name, _, _) <- libModules, name `notElem` nativeStorageModules]

libModuleId :: String -> ModuleId
libModuleId name = ModuleId "tersuslib" (Just name)

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
compiledLibraries loader = case loader (LoadRequest LoadLibraries False (resolverFromFiles []) Nothing librarySources []) of
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
            depIfaces = [libInterfaces pkg Map.! dep | dep <- imports, Map.member dep (libInterfaces pkg)]
         in case response of
                Accepted elaborated (Just iface) _ -> case lowerModuleWith depIfaces elaborated of
                    Error err -> failed pkg (inModule err)
                    Ok program
                        | name `elem` nativeStorageModules -> go rest pkg ((moduId, iface, program) : natives) failure
                        | otherwise -> go rest pkg
                            { libInterfaces = Map.insert name iface (libInterfaces pkg)
                            , libPrograms = Map.insert name program (libPrograms pkg)
                            , libOrder = name : libOrder pkg
                            , libImports = Map.insert name imports (libImports pkg)
                            } natives failure
                Accepted _ Nothing _ -> failed pkg (inModule "the elaborator gave no interface")
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

nativeStorageUnits :: Result NativeUnits String
nativeStorageUnits = snd bootstrapLibraries

-- A library unit lowered against the types its fellow libraries declare
-- carries those types' declarations and invariants seeded from their
-- interfaces; where the program being linked declares such a name itself
-- (which kept the declaring library out of its selection), the program's
-- own declaration is the one the link must see, as it is the one the
-- elaborator gave the program (lib/elaborate/libraries.tersus).
stripDeclaredFromUnits :: [String] -> [(ModuleId, M.Program)] -> [(ModuleId, M.Program)]
stripDeclaredFromUnits declared units = map strip units
  where
    declaredSet = Set.fromList declared
    strip (moduId, program) =
        ( moduId
        , program
            { M.progTypes = Map.withoutKeys (M.progTypes program) declaredSet
            , M.progGenerics = Map.withoutKeys (M.progGenerics program) declaredSet
            , M.progInvariants = Map.withoutKeys (M.progInvariants program) declaredSet
            , M.progFunctions = Map.withoutKeys (M.progFunctions program) (replacedBounded program)
            , M.progBounded = Map.withoutKeys (M.progBounded program) declaredSet
            }
        )
    -- (a function with bounds of the library that the module defines itself, as a replacement Eq's impls do, is the
    -- module's: a library's function with bounds is in its unit only to be copied, and the module's copies are of its own)
    replacedBounded program =
        Set.fromList (concat [name : M.boundedLifted bounded | (name, bounded) <- Map.toList (M.progBounded program), name `Set.member` declaredSet])

libCatalog :: LibPackage -> [Library]
libCatalog pkg = [Library name (Map.findWithDefault [] name (libImports pkg)) iface | name <- libOrder pkg, Just iface <- [Map.lookup name (libInterfaces pkg)]]

withoutReplacedEq :: [Statement] -> [ModuleInterface] -> [ModuleInterface]
withoutReplacedEq statements ifaces
    | any declaresEq statements = filter ((/= libModuleId "eq") . ifModule) ifaces
    | otherwise = ifaces
  where
    declaresEq stmt = case stmt of
        TraitDef "Eq" _ _ -> True
        _ -> False

libDependencyClosure :: LibPackage -> [String] -> [String]
libDependencyClosure pkg pending = go pending []
  where
    go [] done = done
    go (name : rest) done
        | name `elem` done = go rest done
        | otherwise = go (Map.findWithDefault [] name (libImports pkg) ++ rest) (done ++ [name])

-- The interfaces and lowered units of the libraries selected for a module, closed over what they import (the list and
-- Box types only when selected), in the libraries' order, which the linked program's ghost statements follow
libSelection :: LibPackage -> [String] -> ([ModuleInterface], [(ModuleId, M.Program)])
libSelection pkg names =
    let wanted = [name | name <- libDependencyClosure pkg names, name /= "types" || "types" `elem` names]
        ordered = [name | name <- libOrder pkg, name `elem` wanted]
     in ( [libInterfaces pkg Map.! name | name <- ordered]
        , [(libModuleId name, libPrograms pkg Map.! name) | name <- ordered]
        )

