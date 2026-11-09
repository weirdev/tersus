module LibPackage
    ( LibPackage (..)
    , libPackage
    , compileLibPackageWith
    , nativeStorageUnits
    , nativeStorageUnitsWith
    , libModuleNames
    , libModuleId
    , libModuleOfDisplay
    , libSelection
    , libSelectionFor
    , libDefinitionContexts
    , stripDeclaredFromUnits
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

import ElaborateRequest (Elaborator, Extraction (..), Request (..), Response (..), respond)
import Interface (ModuleInterface (..), mergeInterfacesImportEnv)
import Syntax (Statement (..))
import LibParsed (LibParsed (..), libModules, libParsed)
import qualified LibParsed
import qualified Mir as M
import MirLower (lowerModuleWith)
import Modules (ModuleId (..), renderModuleId)
import Utils (Result (..), bindResult, flatResultMap)

-- The implicit libraries and native storage helpers share one compiler-owned
-- package and one parse. Native units never enter user-facing selection.

libModuleNames :: [String]
libModuleNames = LibParsed.libModuleNames

-- The display names Compile.librariesFor selects by.
libModuleOfDisplay :: String -> Maybe String
libModuleOfDisplay display = lookup display [(shown, name) | (name, shown, _) <- libModules, name `elem` libModuleNames]

libDependencies :: String -> [String]
libDependencies name = case libParsed of
    Right parsed -> Map.findWithDefault [] name (lpDependencies parsed)
    Left _ -> []

-- A library unit lowered against the types its fellow libraries declare
-- carries those types' declarations and invariants seeded from their
-- interfaces; where the program being linked declares such a name itself
-- (which kept the declaring library out of its selection), the program's
-- own declaration is the one the link must see, as with the interfaces
-- (see Interface.withoutDeclaredNames).
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
compileLibPackage = compileLibPackageWith respond

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
     in case elaborator (Request moduId True True LibInterfaceOf depIfaces (definitionContexts ifaces (Map.keys ifaces) deps) statements) of
            Accepted elaborated (Just iface) -> case lowerModuleWith (mergeInterfacesImportEnv depIfaces) depIfaces elaborated of
                Error err -> Error ("in lib module " ++ renderModuleId moduId ++ ": " ++ err)
                Ok program -> Ok (iface, program)
            Accepted _ Nothing -> Error ("in lib module " ++ renderModuleId moduId ++ ": the elaborator gave no interface")
            Refused err -> Error ("in lib module " ++ renderModuleId moduId ++ ": " ++ err)
            RefusedInterface err -> Error err
            NotModelled what -> Error ("in lib module " ++ renderModuleId moduId ++ ": the elaborator does not handle this module yet: " ++ what)

nativeStorageUnits :: Result [(ModuleId, ModuleInterface, M.Program)] String
nativeStorageUnits = nativeStorageUnitsWith respond

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

-- The interfaces and lowered units of the named library modules, closed
-- over their dependencies. The units are in the order librariesFor puts
-- the libraries in front of a program, as the linked program's ghost
-- statements follow that order.
-- Suppression governs the user-facing imports, not the units needed by
-- library-internal calls. A replacement Eq does not receive the eq module's
-- helpers or implementation registry through String's dependency closure.
-- A retained cached implementation (String's Eq today) was checked against
-- the library trait: require exact trait AST identity before exposing it.
-- This intentionally rejects even logically equivalent differently written
-- contracts; programs with no retained cached Eq impl remain unrestricted.
libSelectionFor :: LibPackage -> [String] -> [Statement] -> Either String ([ModuleInterface], [(ModuleId, M.Program)])
libSelectionFor pkg names statements =
    let (ifaces, units) = libSelection pkg names
     in case [(params, functions) | TraitDef "Eq" params functions <- statements] of
            [] -> Right (ifaces, units)
            replacement : _ ->
                let visible = filter ((/= libModuleId "eq") . ifModule) ifaces
                    retainsEq = any (any ((== "Eq") . fst) . Set.toList . ifImpls) visible
                    original = do
                        iface <- Map.lookup "eq" (libInterfaces pkg)
                        params <- Map.lookup "Eq" (ifTraitParams iface)
                        functions <- Map.lookup "Eq" (ifTraits iface)
                        pure (params, functions)
                 in if retainsEq && Just replacement /= original
                        then Left "Type error: a replacement Eq used with cached library implementations must have exactly the library Eq's parameters, method signatures and contracts"
                        else Right (visible, units)

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

libSelection :: LibPackage -> [String] -> ([ModuleInterface], [(ModuleId, M.Program)])
libSelection pkg names =
    let wanted = [name | name <- libDependencyClosure names, name /= "types" || "types" `elem` names]
        ordered = [name | name <- libOrder pkg, name `elem` wanted]
     in ( [libInterfaces pkg Map.! name | name <- ordered]
        , [(libModuleId name, libPrograms pkg Map.! name) | name <- ordered]
        )
