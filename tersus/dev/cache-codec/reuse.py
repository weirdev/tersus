import json
import os
import shutil
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[2]
overlay = root / "dev/cache-codec/identity"
overlay.mkdir(exist_ok=True)
for directory in ["src", "test"]:
    (overlay / directory).mkdir(exist_ok=True)
for entry in (root / "src").iterdir():
    if not entry.is_file():
        raise RuntimeError("identity probe expects a flat src directory")
    shutil.copyfile(entry, overlay / "src" / entry.name)
for name in ["TestHarness.hs", "TestParserFragments.hs"]:
    destination = overlay / "test" / name
    if destination.is_symlink():
        destination.unlink()
    shutil.copyfile(root / "test" / name, destination)
for name in ["package.yaml", "stack.yaml", "stack.yaml.lock", "tersus.cabal"]:
    destination = overlay / name
    if destination.is_symlink():
        destination.unlink()
    shutil.copyfile(root / name, destination)
for name in ["lib", "examples", "bootstrap"]:
    destination = overlay / name
    if not destination.exists():
        destination.symlink_to(root / name, target_is_directory=True)

environment = dict(os.environ, XDG_CACHE_HOME=str(overlay / "cache-home"))
records = []

def run(label, expression):
    command = ["ghc", "-w", "-O0", "-isrc", "-itest", "-odir", "build", "-hidir", "build", "test/TestHarness.hs", "-e", expression]
    result = subprocess.run(command, cwd=overlay, env=environment, capture_output=True, text=True, timeout=180)
    if result.returncode:
        raise RuntimeError((label, result.stdout, result.stderr))
    records.append({"label": label, "stdout": result.stdout.strip()})
    print(label + " " + result.stdout.strip(), flush=True)
    return result.stdout.strip()

source = '"codec-reuse-exact-source"'
stage = '"codec-probe"'
run("seed actual sharedProgram", 'do { text <- readFile "../fixtures/small.show"; let { program = fst (head (reads (unlines (drop 2 (lines text))) :: [(Program, String)])) }; result <- sharedProgram '+stage+' '+source+' (pure (Ok program)); case result of { Error e -> error e; Ok p -> Exception.evaluate (length (encodeProgram p)) >> pure () }; Just path <- sharedProgramCacheFile '+stage+' '+source+'; putStrLn path; writeFile "baseline-key.txt" path }')
run("fresh process disk hit with throwing fallback", 'do { result <- sharedProgram '+stage+' '+source+' (throwIO (userError "UNEXPECTED_FALLBACK")); case result of { Error e -> error e; Ok p -> Exception.evaluate (length (encodeProgram p)) >>= print } }')
run("source and stage changes actually miss", 'do { Just a <- sharedProgramCacheFile '+stage+' '+source+'; Just b <- sharedProgramCacheFile '+stage+' "codec-reuse-changed-source"; Just c <- sharedProgramCacheFile "codec-other-stage" '+source+'; if a == b || a == c then error "key did not invalidate" else pure (); result <- try (sharedProgram '+stage+' "codec-reuse-changed-source" (throwIO (userError "EXPECTED_FALLBACK"))) :: IO (Either IOException (Result Program String)); case result of { Left e | "EXPECTED_FALLBACK" `isInfixOf` show e -> putStrLn "PASS changed source fallback reached"; _ -> error "changed source reused" } }')
baseline = run("baseline compiler/harness/key", 'do { putStrLn (compilerIdentity ++ " " ++ harnessSourceHash); Just p <- sharedProgramCacheFile '+stage+' '+source+'; putStrLn p }')
for label, relative in [("changed compiler source", "src/Hash.hs"), ("changed harness source", "test/TestHarness.hs")]:
    target = overlay / relative
    original = target.read_text()
    target.write_text(original + "\n-- isolated identity probe change\n")
    changed = run(label, 'do { putStrLn (compilerIdentity ++ " " ++ harnessSourceHash); Just p <- sharedProgramCacheFile '+stage+' '+source+'; baseline <- readFile "baseline-key.txt"; if p == baseline then error "key did not invalidate" else pure (); putStrLn p; result <- try (sharedProgram '+stage+' '+source+' (throwIO (userError "EXPECTED_FALLBACK"))) :: IO (Either IOException (Result Program String)); case result of { Left e | "EXPECTED_FALLBACK" `isInfixOf` show e -> putStrLn "PASS changed identity fallback reached"; _ -> error "changed identity reused" } }')
    if changed.splitlines()[0] == baseline.splitlines()[0]:
        raise RuntimeError("identity unchanged")
    target.write_text(original)
run("restored identity disk hit", 'do { result <- sharedProgram '+stage+' '+source+' (throwIO (userError "UNEXPECTED_FALLBACK")); case result of { Error e -> error e; Ok p -> Exception.evaluate (length (encodeProgram p)) >>= print } }')
(root / "dev/cache-codec/identity-results.json").write_text(json.dumps(records, indent=2) + "\n")
