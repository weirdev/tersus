module Bootstrap
    ( seedHash
    , seedSha256
    , seedUrl
    , emitterHash
    , stageZero
    , stageOne
    , cachedSeed
    , cachedEmitter
    , tersusLlvm
    , llvmOfOwned
    , emitWith
    ) where

import qualified Mir as M
import MirData (writeProgram)
import Native (buildExecutable, cachedProgram, runWithInput)
import Pipeline (ownedSource)
import PreludeSource (emitterSource)
import Seed (cachedSeed, emitterHash, seedHash, seedSha256, seedUrl, stageZero)
import Utils

-- The lowering to LLVM IR that is written in Tersus (examples/emit.tersus, step 31 and STEP31.md) is the compiler's only emitter. An executable of it reads the MIR of a
-- program as data (MirData) and writes its LLVM IR; `tersus build`, `llvm` and `run` use it. It is a
-- program of the language that needs a compiler, so it is made in stages from a seed:
-- - the seed is the IR of an emitter. It is the IR that the emitter wrote for its own source when the seed was made, and
--   it does not have to be the latest: it only has to be able to compile the emitter as it is now, which it can as long as the data it reads and the runtime it calls
--   are the same. The seed itself is not kept in the repository: it is a GitHub release asset (`seedUrl`), and the repository keeps only its SHA-256
--   (bootstrap/emitter.sha256, embedded by `PreludeSource` as `seedSha256`). It is fetched once, verified against that pin, and kept in the cache
--   directory of the user. A seed at $TERSUS_SEED_FILE, or a bootstrap/emitter.ll in the working tree, is used instead when present (and also verified),
--   which is how a machine with no network keeps working;
-- - stage 0 is the seed built with clang (`stageZero`);
-- - stage 1 is the emitter as it is now, built from the IR that stage 0 writes for its source (`stageOne`). This is the one that compiles programs;
-- - and the fixpoint is that stage 1 writes for the emitter the same IR as stage 0 did, so that stage 2 would be stage 1 again (the tests check it). Making a new seed is
--   `tersus llvm examples/emit.tersus > emitter.ll.new`, then `sha256sum emitter.ll.new`, upload it as the asset `emitter.ll` of a new release tagged
--   `bootstrap-<first 12 digits of that digest>`, and put the digest in bootstrap/emitter.sha256. Never redirect straight into a seed file that the
--   running compiler is using: the shell truncates it before the compiler runs.
--   When a change breaks the data the seed reads (a MirData format change), that command cannot run until there is a seed that reads it: build the emitter as it is now with stage 0 fed the emitter's data in the format the seed reads (the same types with the old type words), which gives an emitter that reads the new format, and make the seed with it (`<that emitter>`, fed the new data by hand, in place of `tersus llvm`); upload the result as the asset of a new release as above and put its digest in bootstrap/emitter.sha256. The result is a seed only when it writes the same IR for the emitter again.
-- Both are built when they are first needed and kept in the cache directory of the user, so that building this package needs no clang and no network.

-- Stage 1: the emitter as it is now, built at the path from the IR that the emitter at the first path writes for it
stageOne :: FilePath -> FilePath -> IO (Result () String)
stageOne compiler output = case ownedSource emitterSource of
    Error e -> pure (Error e)
    Ok owned -> do
        ir <- emitWith compiler (writeProgram owned)
        case ir of
            Error e -> pure (Error e)
            Ok text -> buildExecutable output text

-- What the emitter at the path writes for the MIR as data: its IR, or its reason (on the standard error) for refusing the program (Native.runWithInput)
emitWith :: FilePath -> String -> IO (Result String String)
emitWith = runWithInput

-- Stage 1 in the cache, built (from stage 0, which is built too if it is not there) if it is not there yet
cachedEmitter :: IO (Result FilePath String)
cachedEmitter = cachedProgram "emitter" emitterHash "the emitter written in Tersus" $ \output -> do
    zero <- cachedSeed
    case zero of
        Error e -> pure (Error e)
        Ok compiler -> stageOne compiler output

-- The LLVM IR of a program, by the emitter in Tersus
tersusLlvm :: String -> IO (Result String String)
tersusLlvm source = case ownedSource source of
    Error e -> pure (Error e)
    Ok owned -> llvmOfOwned owned

-- The LLVM IR of a program that who owns each value has been made explicit in (the owned MIR of Pipeline), by the emitter in
-- Tersus: what `tersusLlvm` does with what `ownedSource` gives, for a caller that has the program already.
llvmOfOwned :: M.Program -> IO (Result String String)
llvmOfOwned owned = do
    exe <- cachedEmitter
    case exe of
        Error e -> pure (Error e)
        Ok path -> do
            ir <- emitWith path (writeProgram owned)
            pure (either' ir)
  where
    either' (Error e) = Error ("Native code failed: " ++ e)
    either' ok = ok
