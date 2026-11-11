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
    , libDefinitionContexts
    , stripDeclaredFromUnits
    , withoutReplacedEq
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

import ElaborateRequest (Elaborator, Extraction (..), Library (..), Request (..), Response (..))
import ElaboratorTool (bootstrapElaborator)
import Interface (ModuleInterface (..))
import Syntax (Statement (..))
import LibParsed (LibParsed (..), libParsed)
import qualified LibParsed
import qualified Mir as M
import MirLower (lowerModuleWith)
import Modules (ModuleId (..), renderModuleId)
import Utils (Result (..), bindResult, flatResultMap)

-- The implicit libraries and native storage helpers share one compiler-owned
-- package and one parse. Native units never enter user-facing selection.

libModuleNames :: [String]
libModuleNames = LibParsed.libModuleNames

libDependencies :: String -> [String]
libDependencies name = case libParsed of
    Right parsed -> Map.findWithDefault [] name (lpDependencies parsed)
    Left _ -> []

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
            }
        )

libModuleId :: String -> ModuleId
libModuleId name = ModuleId "tersuslib" (Just name)

data LibPackage = LibPackage
    { libInterfaces :: Map.Map String ModuleInterface
    , libPrograms :: Map.Map String M.Program
    , libOrder :: [String]
    }
    deriving (Show)

compileLibPackage :: Result LibPackage String
compileLibPackage = compileLibPackageWith bootstrapElaborator

compileLibPackageWith :: Elaborator -> Result LibPackage String
compileLibPackageWith elaborator = case libParsed of
    Left err -> Error ("the lib package does not parse: " ++ err)
    Right parsed -> go (lpOrder parsed) (lpStatements parsed) Map.empty Map.empty []
  where
    go [] _ ifaces programs done = Ok (LibPackage ifaces programs (reverse done))
    go (name : rest) statements ifaces programs done = case compileLibModule elaborator ifaces (libDependencies name) name (Map.findWithDefault [] name statements) of
        Error err -> Error err
        Ok (iface, program) -> go rest statements (Map.insert name iface ifaces) (Map.insert name program programs) (name : done)

compileLibModule :: Elaborator -> Map.Map String ModuleInterface -> [String] -> String -> [Statement] -> Result (ModuleInterface, M.Program) String
compileLibModule elaborator ifaces deps name statements =
    let moduId = libModuleId name
        depIfaces = [ifaces Map.! dep | dep <- deps]
     in case elaborator (Request moduId True True LibInterfaceOf depIfaces (definitionContexts ifaces (Map.keys ifaces) deps) [] Nothing [statements]) of
            Accepted elaborated (Just iface) _ -> case lowerModuleWith depIfaces elaborated of
                Error err -> Error ("in lib module " ++ renderModuleId moduId ++ ": " ++ err)
                Ok program -> Ok (iface, program)
            Accepted _ Nothing _ -> Error ("in lib module " ++ renderModuleId moduId ++ ": the elaborator gave no interface")
            Refused err -> Error ("in lib module " ++ renderModuleId moduId ++ ": " ++ err)
            RefusedInterface err -> Error err
            Unresolved err -> Error err
            NotModelled what -> Error ("in lib module " ++ renderModuleId moduId ++ ": the elaborator does not handle this module yet: " ++ what)

nativeStorageUnits :: Result [(ModuleId, ModuleInterface, M.Program)] String
nativeStorageUnits = nativeStorageUnitsWith bootstrapElaborator

nativeStorageUnitsWith :: Elaborator -> Result [(ModuleId, ModuleInterface, M.Program)] String
nativeStorageUnitsWith elaborator = libPackage `bindResult` \pkg -> case LibParsed.nativeLibParsed of
    Left err -> Error err
    Right parsed -> flatResultMap (compileNative pkg parsed) LibParsed.nativeStorageModules
  where
    compileNative pkg parsed name =
        compileLibModule elaborator (libInterfaces pkg) (Map.findWithDefault [] name (lpDependencies parsed)) name (lpStatements parsed Map.! name)
            `bindResult` \(iface, program) -> Ok (libModuleId name, iface, program)

{-# NOINLINE libPackageCache #-}
libPackageCache :: MVar (Maybe (Result LibPackage String))
libPackageCache = unsafePerformIO (newMVar Nothing)

-- The lib package, compiled on first use and kept for the process.
libPackage :: Result LibPackage String
libPackage = unsafePerformIO $ modifyMVar libPackageCache $ \cached -> case cached of
    Just result -> pure (cached, result)
    Nothing ->
        let result = compileLibPackage
            forced = case result of
                Ok pkg -> Map.size (libInterfaces pkg) `seq` result
                Error _ -> result
         in pure (Just forced, forced)

libCatalog :: LibPackage -> [Library]
libCatalog pkg = [Library name (libDependencies name) iface | name <- libOrder pkg, Just iface <- [Map.lookup name (libInterfaces pkg)]]

withoutReplacedEq :: [Statement] -> [ModuleInterface] -> [ModuleInterface]
withoutReplacedEq statements ifaces
    | any declaresEq statements = filter ((/= libModuleId "eq") . ifModule) ifaces
    | otherwise = ifaces
  where
    declaresEq stmt = case stmt of
        TraitDef "Eq" _ _ -> True
        _ -> False

libDefinitionContexts :: LibPackage -> [String] -> [[ModuleInterface]]
libDefinitionContexts pkg = definitionContexts (libInterfaces pkg) (libOrder pkg)

definitionContexts :: Map.Map String ModuleInterface -> [String] -> [String] -> [[ModuleInterface]]
definitionContexts ifaces order names =
    [ iface : [ifaces Map.! dependency | dependency <- order, dependency `elem` libDependencyClosure (libDependencies name)]
    | name <- order, name `elem` libDependencyClosure names
    , Just iface <- [Map.lookup name ifaces]
    ]

libDependencyClosure :: [String] -> [String]
libDependencyClosure pending = go pending []
  where
    go [] done = done
    go (name : rest) done
        | name `elem` done = go rest done
        | otherwise = go (libDependencies name ++ rest) (done ++ [name])

-- The interfaces and lowered units of the libraries selected for a module, closed over what they import (the list and
-- Box types only when selected), in the libraries' order, which the linked program's ghost statements follow
libSelection :: LibPackage -> [String] -> ([ModuleInterface], [(ModuleId, M.Program)])
libSelection pkg names =
    let wanted = [name | name <- libDependencyClosure names, name /= "types" || "types" `elem` names]
        ordered = [name | name <- libOrder pkg, name `elem` wanted]
     in ( [libInterfaces pkg Map.! name | name <- ordered]
        , [(libModuleId name, libPrograms pkg Map.! name) | name <- ordered]
        )
