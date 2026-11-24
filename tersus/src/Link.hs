{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
module Link
    ( linkPrograms
    , pruneProgram
    , completeSpecEnvs
    , standaloneCopies
    ) where

import qualified Data.Map.Strict as Map
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

-- Linking runs in the pinned emitter seed (lib/mir/link), not stage 1: stage 1 is made from programs this module links.
{-# NOINLINE linkPrograms #-}
linkPrograms :: [(ModuleId, M.Program)] -> Result M.Program String
linkPrograms [] = Error "link error: no modules to link"
linkPrograms units = flatResultMap unitData units `bindResult` \parts ->
    profiledLinkPass ("merge-copies " ++ show (length units) ++ "\n" ++ concat parts) `bindResult` \linked ->
        checkSpawns library linked{M.progCaptureStorage = captureStorage linked}
  where
    captureStorage program
        | any packs (M.progMain program : Map.elems (M.progFunctions program)) = Map.fromList
            [ (name, declaration)
            | (ModuleId "tersuslib" (Just "types"), storage) <- units
            , (name, declaration) <- Map.toList (M.progCaptureStorage storage)
            , Just invariant <- [Map.lookup name (M.progInvariants storage)]
            , Map.lookup name (M.progGenerics program) == Just declaration
            , Map.lookup name (M.progInvariants program) == Just invariant
            ]
        | otherwise = Map.empty
    packs fn = or [True | block <- Map.elems (M.fnBlocks fn), M.Assign _ M.PackClosure{} <- M.blockStatements block]
    library = Set.fromList [name | (ModuleId "tersuslib" _, program) <- units, name <- Map.keys (M.progBounded program)]
    unitData (ModuleId pkg modu, program) = programData program `bindResult` \text ->
        Ok ("unit " ++ quote pkg ++ " " ++ maybe "none" (\name -> "some " ++ quote name) modu
            ++ " " ++ show (length (lines text)) ++ "\n" ++ text)

standaloneCopies :: Set.Set Name -> M.Program -> Result M.Program String
standaloneCopies library program
    | Map.null (M.progBounded program) && Map.null (M.progInstances program) = Ok program
    | otherwise = programData program `bindResult` \text ->
        let header = unwords ("copies" : show (length (lines text)) : map quote (Set.toList library))
         in profiledLinkPass (header ++ "\n" ++ text)

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
