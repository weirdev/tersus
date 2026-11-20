{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
module Link
    ( linkPrograms
    , pruneProgram
    , completeSpecEnvs
    ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import DataCodec (quote)
import qualified Mir as M
import MirCopies (makeCopiesWith)
import MirMoves (checkSpawns)
import MirPass (programData, runPassWith)
import PackageData (ModuleId (..))
import Seed (cachedSeed)
import System.IO.Unsafe (unsafePerformIO)
import Utils

-- Linking runs in the pinned emitter seed (lib/mir/link), not stage 1: stage 1 is made from programs this module links.
{-# NOINLINE linkPrograms #-}
linkPrograms :: [(ModuleId, M.Program)] -> Result M.Program String
linkPrograms [] = Error "link error: no modules to link"
linkPrograms units = flatResultMap unitData units `bindResult` \parts ->
    linkPass ("merge " ++ show (length units) ++ "\n" ++ concat parts) `bindResult` \program ->
        -- (a copy the call cannot have is refused as the elaborator refuses a call)
        case makeCopiesWith library (M.completeInstances program) of
            Error e -> Error ("Validation failed: " ++ e)
            Ok copied -> checkSpawns library copied
  where
    library = Set.fromList [name | (ModuleId "tersuslib" _, program) <- units, name <- Map.keys (M.progBounded program)]
    unitData (ModuleId pkg modu, program) = programData program `bindResult` \text ->
        Ok ("unit " ++ quote pkg ++ " " ++ maybe "none" (\name -> "some " ++ quote name) modu
            ++ " " ++ show (length (lines text)) ++ "\n" ++ text)

{-# NOINLINE pruneProgram #-}
pruneProgram :: M.Program -> Result M.Program String
pruneProgram program = programData program `bindResult` \text -> linkPass ("prune\n" ++ text)

{-# NOINLINE completeSpecEnvs #-}
completeSpecEnvs :: M.Program -> Result M.Program String
completeSpecEnvs program = programData program `bindResult` \text -> linkPass ("environments\n" ++ text)

{-# NOINLINE linkPass #-}
linkPass :: String -> Result M.Program String
linkPass request = unsafePerformIO (runPassWith cachedSeed "the linker written in Tersus" ("pass link\n" ++ request))
