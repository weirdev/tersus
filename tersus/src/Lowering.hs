-- Where every production lowering starts: an elaborator's accepted answer for a module, lowered against the interfaces
-- the module is lowered with, to the raw unit (Mir.Lowered) that MirMoves.finishLowered finishes
module Lowering (lowerAccepted, finishProgram) where

import ElaborateRequest (Response, acceptedElaboration)
import Interface (ModuleInterface)
import Mir (Lowered, Program)
import MirCopies (makeCopies)
import MirLower (lowerRaw)
import MirMoves (finishLowered)
import Utils

lowerAccepted :: [ModuleInterface] -> Response -> Result Lowered String
lowerAccepted ifaces response = acceptedElaboration response `bindResult` lowerRaw ifaces

-- A program lowered on its own is the whole program, so the copies of its functions with bounds are made when it is
-- finished; a module's are made when the program it is part of is linked (Link)
finishProgram :: Lowered -> Result Program String
finishProgram lowered = finishLowered lowered `bindResult` makeCopies
