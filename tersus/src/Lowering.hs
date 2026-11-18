-- Where every production lowering starts: the unit the elaborator lowered a module it accepted to (Mir.Lowered), read
-- from its answer, which MirMoves.finishLowered finishes
module Lowering (lowerAccepted, finishProgram, finishProgramWith) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import ElaborateRequest (MirAnswer (..), Response (..), acceptedOwnership, acceptedResponse)
import ElaboratorTool (toolFailurePrefix)
import Mir (Lowered (..), Program (..))
import MirCopies (makeCopies, makeCopiesWith)
import Types (Name)
import MirData (readLoweredBytes)
import MirMoves (checkSpawns, finishLowered)
import Types (OwnershipTransport (..))
import Utils

-- (the elaborator's refusal to lower is the lowering's error, in its words; a unit that does not read is the tool's
-- failure, not a verdict on the program)
lowerAccepted :: Response -> Result Lowered String
lowerAccepted response = acceptedResponse response `bindResult` \accepted -> case accepted of
    Accepted _ _ (MirLowered ls) -> case readLoweredBytes ls of
        Error e -> Error (toolFailurePrefix ++ "the elaborator's MIR does not read: " ++ e)
        Ok lowered -> withFacts response lowered
    Accepted _ _ (MirRefused message) -> Error message
    _ -> Error "internal: not an accepted answer"

-- The unit with the checked ownership facts the elaborator answered with: the provider of each role (one, or the unit is
-- refused as the build is, PackageCompile) and each type's facts, as they are
withFacts :: Response -> Lowered -> Result Lowered String
withFacts response lowered = case acceptedOwnership response of
    Nothing -> Ok lowered
    Just transport -> case [role | (role, providers) <- Map.toList (transportProtocols transport), length providers > 1] of
        role : _ -> Error ("Type error: the protocol " ++ role ++ " has more than one provider")
        [] -> Ok lowered{lowProgram = (lowProgram lowered){progProtocols = Map.mapMaybe safeHead (transportProtocols transport), progOwnership = Just (Map.filterWithKey (\owner _ -> definedHere owner) (transportOwnership transport))}}
  where
    -- (a declaration's facts are its own module's: another module's row for a declaration it imports is that module's
    -- reading of the interface, which may not see the impl's bounds, so the linked program takes the declaring module's;
    -- the rows of instances are each module's own selections)
    definedHere owner = '<' `elem` owner || Set.member owner (lowDeclared lowered) || Set.member owner (lowNested lowered)
    safeHead xs = case xs of
        x : _ -> Just x
        [] -> Nothing

-- A program lowered on its own is the whole program, so the copies of its functions with bounds are made when it is
-- finished; a module's are made when the program it is part of is linked (Link)
finishProgram :: Lowered -> Result Program String
finishProgram lowered = finishLowered lowered `bindResult` makeCopies

-- The same for a program given with the compiler's libraries among its statements: their functions with bounds are
-- validated where the program uses them (MirCopies.makeCopiesWith)
finishProgramWith :: Set.Set Name -> Lowered -> Result Program String
finishProgramWith library lowered =
    finishLowered lowered `bindResult` \program ->
        makeCopiesWith library (Just (Map.keysSet (progTypes program))) program `bindResult`
            checkSpawns (Set.intersection library (Map.keysSet (progBounded program)))
