module LibPackage
    ( LibPackage (..)
    , libPackage
    , libModuleNames
    , libModuleId
    , libModuleOfDisplay
    , libSelection
    , libSelectionFor
    , stripDeclaredFromUnits
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

import Interface (ModuleInterface (..), extractLibInterface, mergeInterfacesImportEnv, predeclareOwnEnv)
import Syntax (Statement (..))
import LibParsed (LibParsed (..), libModules, libParsed)
import qualified LibParsed
import qualified Mir as M
import MirLower (lowerModuleWith)
import Modules (ModuleId (..), renderModuleId)
import TypeCheck (Elaborated (..), elaborateWith)
import Utils (Result (..))

-- The libraries of Compile.librariesFor as a synthetic package: one
-- module per lib file, built in memory from the PreludeSource texts (the
-- import lines exist only in the in-memory copies LibParsed parses, so
-- the embedded texts, and with them emitterHash, are unchanged). A
-- library module's declarations keep their bare names, as the entry
-- module's do: the checker, the parser, MIR and the emitter all match
-- those names as strings. The package is compiled once per process from
-- the libraries' one parse (LibParsed).

libModuleNames :: [String]
libModuleNames = LibParsed.libModuleNames

-- The display names Compile.librariesFor selects by.
libModuleOfDisplay :: String -> Maybe String
libModuleOfDisplay display = lookup display [(shown, name) | (name, shown, _, _) <- libModules]

libDependencies :: String -> [String]
libDependencies name = case [deps | (candidate, _, _, deps) <- libModules, candidate == name] of
    deps : _ -> deps
    [] -> []

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
compileLibPackage = case libParsed of
    Left err -> Error ("the lib package does not parse: " ++ err)
    Right parsed -> go libCompileOrder (lpStatements parsed) Map.empty Map.empty []
  where
    libCompileOrder = ["types", "eq", "clone", "prelude", "string", "map", "set"]
    go [] _ ifaces programs done = Ok (LibPackage ifaces programs (reverse done))
    go (name : rest) statements ifaces programs done = case compileOne ifaces name (Map.findWithDefault [] name statements) of
        Error err -> Error err
        Ok (iface, program) -> go rest statements (Map.insert name iface ifaces) (Map.insert name program programs) (name : done)
    compileOne ifaces name statements =
        let moduId = libModuleId name
            -- (every library module is compiled with the List and Box types in
            -- front of it, as the texts are read together on the old path; the
            -- types module itself is only linked where librariesFor selects it)
            depNames = (if name == "types" then [] else ["types"]) ++ [dep | dep <- libDependencies name, dep /= "types"]
            depIfaces = [ifaces Map.! dep | dep <- depNames]
            importEnv = mergeInterfacesImportEnv depIfaces
            env = predeclareOwnEnv importEnv
         in case elaborateWith env statements of
                Error err -> Error ("in lib module " ++ renderModuleId moduId ++ ": " ++ err)
                Ok (elaborated@(Elaborated elaboratedStatements _), state) -> case extractLibInterface moduId statements elaboratedStatements state of
                    Error err -> Error err
                    Ok iface -> case lowerModuleWith importEnv depIfaces elaborated of
                        Error err -> Error ("in lib module " ++ renderModuleId moduId ++ ": " ++ err)
                        Ok program -> Ok (iface, program)

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

libSelection :: LibPackage -> [String] -> ([ModuleInterface], [(ModuleId, M.Program)])
libSelection pkg names =
    let wanted = closure names
        ordered = [name | name <- ["types", "clone", "eq", "prelude", "string", "map", "set"], name `elem` wanted]
     in ( [libInterfaces pkg Map.! name | name <- ordered]
        , [(libModuleId name, libPrograms pkg Map.! name) | name <- ordered]
        )
  where
    closure pending = go pending []
    go [] done = done
    go (name : rest) done
        | name `elem` done = go rest done
        | otherwise = go (libDependencies name ++ rest) (done ++ [name])
