-- Where every production lowering starts: the unit the elaborator lowered a module it accepted to (Mir.Lowered), read
-- from its answer, which MirMoves.finishLowered finishes
module Lowering (lowerAccepted, finishProgram) where

import ElaborateRequest (MirAnswer (..), Response (..), acceptedResponse)
import ElaboratorTool (toolFailurePrefix)
import Mir (Lowered, Program)
import MirCopies (makeCopies)
import MirData (readLoweredBytes)
import MirMoves (finishLowered)
import Utils

-- (the elaborator's refusal to lower is the lowering's error, in its words; a unit that does not read is the tool's
-- failure, not a verdict on the program)
lowerAccepted :: Response -> Result Lowered String
lowerAccepted response = acceptedResponse response `bindResult` \accepted -> case accepted of
    Accepted _ _ (MirLowered ls) -> case readLoweredBytes ls of
        Error e -> Error (toolFailurePrefix ++ "the elaborator's MIR does not read: " ++ e)
        ok -> ok
    Accepted _ _ (MirRefused message) -> Error message
    _ -> Error "internal: not an accepted answer"

-- A program lowered on its own is the whole program, so the copies of its functions with bounds are made when it is
-- finished; a module's are made when the program it is part of is linked (Link)
finishProgram :: Lowered -> Result Program String
finishProgram lowered = finishLowered lowered `bindResult` makeCopies
