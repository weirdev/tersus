{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
module Link
    ( linkPrograms
    , linkWithLibraries
    , linkValidatedPrograms
    , pruneProgram
    , completeSpecEnvs
    , standaloneCopies
    ) where

import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import DataCodec (quote)
import qualified Mir as M
import MirCopiesNameProfile (nameProfilePrefix)
import MirMoves (checkSpawns)
import MirPass (programData, runPassWith)
import PackageData (ModuleId (..))
import Seed (cachedSeed)
import System.IO.Unsafe (unsafePerformIO)
import Types (Name)
import Utils

linkPrograms :: [(ModuleId, M.Program)] -> Result M.Program String
linkPrograms = linkWithLibraries []

linkWithLibraries :: [(ModuleId, M.Program)] -> [(ModuleId, M.Program)] -> Result M.Program String
linkWithLibraries libraries own = linkWith True libraries own

linkValidatedPrograms :: [(ModuleId, M.Program)] -> Result M.Program String
linkValidatedPrograms libraries = linkWith False libraries []

-- The selected library prefix is explicit; a user's package name does not confer library status.
linkWith :: Bool -> [(ModuleId, M.Program)] -> [(ModuleId, M.Program)] -> Result M.Program String
linkWith _ [] [] = Error "link error: no modules to link"
linkWith recording libraries own = flatResultMap unitData units `bindResult` \parts ->
    profiledLinkPass (unwords ["merge-copies", show (length units), show (length libraries), policy] ++ "\n" ++ concat parts)
        `bindResult` checkedReceipt programs `bindResult` \linked ->
            checkSpawns threadLibrary linked{M.progCaptureStorage = captureStorage linked}
  where
    captureStorage program
        | any packs (M.progMain program : Map.elems (M.progFunctions program)) = Map.fromList
            [ (name, declaration)
            | (ModuleId "std" (Just "core"), storage) <- libraries
            , (name, declaration) <- Map.toList (M.progCaptureStorage storage)
            , Just invariant <- [Map.lookup name (M.progInvariants storage)]
            , Map.lookup name (M.progGenerics program) == Just declaration
            , Map.lookup name (M.progInvariants program) == Just invariant
            ]
        | otherwise = Map.empty
    packs fn = or [True | block <- Map.elems (M.fnBlocks fn), M.Assign _ M.PackClosure{} <- M.blockStatements block]
    units = libraries ++ own
    programs = map snd units
    policy = if recording then "record" else "validate"
    threadLibrary = Set.fromList [n | (ModuleId "std" (Just "thread"), p) <- libraries, n <- Map.keys (M.progBounded p)]
    unitData (ModuleId pkg modu, program) = programData program `bindResult` \text ->
        Ok ("unit " ++ quote pkg ++ " " ++ maybe "none" (\n -> "some " ++ quote n) modu
            ++ " " ++ show (length (lines text)) ++ "\n" ++ text)

standaloneCopies :: Set.Set Name -> M.Program -> Result M.Program String
standaloneCopies library program
    | Map.null (M.progBounded program) && Map.null (M.progInstances program) = Ok program
    | otherwise = programData program `bindResult` \text ->
        let header = unwords (["copies", show (length (lines text)), "record"] ++ map quote (Set.toList library))
         in profiledLinkPass (header ++ "\n" ++ text) `bindResult` checkedReceipt [program]

checkedReceipt :: [M.Program] -> M.Program -> Result M.Program String
checkedReceipt inputs output
    | isJust (M.progOwnership output) /= any (isJust . M.progOwnership) inputs = Error "the linker changed checked ownership transport"
    | M.progProtocols output /= Map.unions (map M.progProtocols inputs) = Error "the linker changed checked protocol providers"
    | otherwise = Ok output

profiledLinkPass :: String -> Result M.Program String
profiledLinkPass request = linkPass (request ++ nameProfilePrefix [request])

{-# NOINLINE pruneProgram #-}
pruneProgram :: M.Program -> Result M.Program String
pruneProgram program = programData program `bindResult` \text -> linkPass ("prune\n" ++ text)

{-# NOINLINE completeSpecEnvs #-}
completeSpecEnvs :: M.Program -> Result M.Program String
completeSpecEnvs program = programData program `bindResult` \text -> linkPass ("environments\n" ++ text)

{-# NOINLINE linkPass #-}
linkPass :: String -> Result M.Program String
linkPass request = unsafePerformIO (runPassWith cachedSeed "the linker written in Tersus" ("pass link\n" ++ request))
