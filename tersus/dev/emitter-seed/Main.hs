module Main (main) where

import System.Directory (canonicalizePath, doesFileExist)
import System.Environment (getArgs, lookupEnv)

import Bootstrap (cachedEmitter, cachedSeed, emitWith)
import MirData (writeProgram)
import MirHousekeeping (emitterEntry, emitterOwnedProgram, ownedToolWith)
import Utils

-- `advance <output.ll>` is for a change to what ownership writes: stage 1 (built from the pinned seed) owns and emits the
-- emitter. Its output is a candidate only; it is the seed when `emit` from it gives the same bytes.
-- `emit <output.ll>` builds stage 0 from $TERSUS_SEED_FILE (or the pinned seed) and stage 1 from it, has each expand
-- and own the emitter, checks that both give the same owned MIR and the same IR, and writes stage 1's IR. The output is
-- the seed when emitting again from it gives the same bytes.
main :: IO ()
main = do
    args <- getArgs
    case args of
        ["advance", output] -> do
            one <- cachedEmitter
            case one of
                Error e -> fail ("stage 1: " ++ e)
                Ok stageOne -> do
                    owned <- ownedToolWith stageOne emitterEntry
                    case owned of
                        Error e -> fail ("stage 1 owning the emitter: " ++ e)
                        Ok program -> emitWith stageOne (writeProgram program) >>= written output
        ["emit", output] -> do
            zero <- cachedSeed
            one <- cachedEmitter
            case (zero, one) of
                (Error e, _) -> fail ("stage 0: " ++ e)
                (_, Error e) -> fail ("stage 1: " ++ e)
                (Ok stageZero, Ok stageOne) -> do
                    owned0 <- ownedToolWith stageZero emitterEntry
                    owned1 <- ownedToolWith stageOne emitterEntry
                    case (owned0, owned1, emitterOwnedProgram) of
                        (Ok a, Ok b, Ok c)
                            | a /= b -> fail "stage 0 and stage 1 own the emitter differently"
                            | b /= c -> fail "the owned emitter of the pipeline is not stage 1's"
                            | otherwise -> do
                                ir0 <- emitWith stageZero (writeProgram a)
                                ir1 <- emitWith stageOne (writeProgram b)
                                case (ir0, ir1) of
                                    (Error e, _) -> fail ("stage 0 emitting the emitter: " ++ e)
                                    (_, Error e) -> fail ("stage 1 emitting the emitter: " ++ e)
                                    (Ok x, Ok y)
                                        | x /= y -> fail "stage 0 and stage 1 write different IR for the emitter"
                                        | otherwise -> written output ir1
                        (Error e, _, _) -> fail ("stage 0 owning the emitter: " ++ e)
                        (_, Error e, _) -> fail ("stage 1 owning the emitter: " ++ e)
                        (_, _, Error e) -> fail ("the owned emitter: " ++ e)
        _ -> fail "usage: emitter-seed advance <output.ll> | emitter-seed emit <output.ll>"
  where
    -- (the output is written only once everything succeeded, and never over the seed the run was built from)
    written _ (Error e) = fail e
    written output (Ok text) = do
        seed <- lookupEnv "TERSUS_SEED_FILE"
        same <- case seed of
            Just path -> (&&) <$> doesFileExist output <*> ((==) <$> canonicalizePath path <*> canonicalizePath output)
            Nothing -> pure False
        if same then fail "the output is $TERSUS_SEED_FILE: write the new seed to another file" else writeFile output text
