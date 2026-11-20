module Main (main) where

import System.Environment (getArgs)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)

import Bootstrap (cachedSourceEmitter, cachedSeed, emitWith, seedSha256)
import EmitterProvenance (ordinaryBuildProfile, emitterBuildDescription, emitterSourcesMatch, checkEmitterOutputs)
import Seed (emitterSeedFile)
import PreludeSource (emitterSourceFiles)
import MirData (writeProgram)
import MirHousekeeping (emitterConstruction, emitterEntry, emitterOwnedProgram, ownedToolWith)
import Utils

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["profile"] -> do
            print ordinaryBuildProfile
            print emitterBuildDescription
            emitterConstruction >>= print
        ["advance", output] -> do
            one <- cachedSourceEmitter
            case one of
                Error e -> fail ("stage 1: " ++ e)
                Ok stageOne -> do
                    owned <- ownedToolWith stageOne emitterEntry
                    case owned of
                        Error e -> fail ("stage 1 owning the emitter: " ++ e)
                        Ok program -> emitWith stageOne (writeProgram program) >>= written output
        ["emit", output] -> regenerate >>= written output
        ["certify", output, association] -> do
            before <- emitterConstruction
            current <- emitterSourcesMatch
            construction <- case before of
                Ok (Just identity) | current -> pure identity
                _ -> fail "certification needs an ordinary configured build and unchanged source"
            inputs <- emitterInputs
            preflight <- checkEmitterOutputs inputs [output, association]
            case preflight of Error e -> fail e; Ok () -> pure ()
            result <- regenerate
            ir <- case result of Error e -> fail e; Ok text -> pure text
            (status, digest, _) <- readProcessWithExitCode "sha256sum" [] ir
            after <- emitterConstruction
            unchanged <- emitterSourcesMatch
            if status /= ExitSuccess || takeWhile (/= ' ') digest /= seedSha256
                then fail "source stage 1 did not reproduce the complete published emitter pin"
                else if before /= after || not unchanged
                    then fail "emitter construction changed during certification"
                    else do
                        finalPaths <- checkEmitterOutputs inputs [output, association]
                        case finalPaths of Error e -> fail e; Ok () -> pure ()
                        writeFile output ir
                        writeFile association (seedSha256 ++ " " ++ construction ++ "\n")
        _ -> fail "usage: emitter-seed profile | advance <output.ll> | emit <output.ll> | certify <output.ll> <candidate.pin>"

regenerate :: IO (Result String String)
regenerate = do
    zero <- cachedSeed
    one <- cachedSourceEmitter
    case (zero, one) of
        (Error e, _) -> pure (Error ("stage 0: " ++ e))
        (_, Error e) -> pure (Error ("stage 1: " ++ e))
        (Ok stageZero, Ok stageOne) -> do
            owned0 <- ownedToolWith stageZero emitterEntry
            owned1 <- ownedToolWith stageOne emitterEntry
            case (owned0, owned1, emitterOwnedProgram) of
                (Ok a, Ok b, Ok c)
                    | a /= b -> pure (Error "stage 0 and source stage 1 own the emitter differently")
                    | b /= c -> pure (Error "the owned emitter pipeline is not source stage 1's")
                    | otherwise -> do
                        ir0 <- emitWith stageZero (writeProgram a)
                        ir1 <- emitWith stageOne (writeProgram b)
                        pure $ case (ir0, ir1) of
                            (Error e, _) -> Error ("stage 0 emitting the emitter: " ++ e)
                            (_, Error e) -> Error ("source stage 1 emitting the emitter: " ++ e)
                            (Ok x, Ok y) | x /= y -> Error "stage 0 and source stage 1 write different IR for the emitter"
                                        | otherwise -> Ok y
                (Error e, _, _) -> pure (Error ("stage 0 owning the emitter: " ++ e))
                (_, Error e, _) -> pure (Error ("source stage 1 owning the emitter: " ++ e))
                (_, _, Error e) -> pure (Error ("the owned emitter: " ++ e))

written :: FilePath -> Result String String -> IO ()
written _ (Error e) = fail e
written output (Ok text) = do
    inputs <- emitterInputs
    checked <- checkEmitterOutputs inputs [output]
    case checked of Error e -> fail e; Ok () -> writeFile output text

emitterInputs :: IO [FilePath]
emitterInputs = do
    verified <- emitterSeedFile
    seed <- case verified of Error e -> fail e; Ok path -> pure path
    pure (seed : ["bootstrap/emitter.sha256", "bootstrap/frontend.sha256", "bootstrap/parser.sha256"] ++ map fst emitterSourceFiles)
