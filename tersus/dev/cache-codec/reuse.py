"""Recompile controlled source variants; never modify the original worktree inputs.

The approved identity is ONLY for this known direct-GHC fixture build. It keeps
executable differences from making source-fingerprint assertions vacuous. Normal
builds retain the conservative executable-byte identity.
"""
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[2]
overlay = root / "dev/cache-codec/identity"
overlay.mkdir(exist_ok=True)
for directory in ["src", "test", "bin", "build", "tmp", "cache-home"]:
    (overlay / directory).mkdir(exist_ok=True)
for entry in (root / "src").iterdir():
    if not entry.is_file():
        raise RuntimeError("identity probe expects a flat src directory")
    shutil.copyfile(entry, overlay / "src" / entry.name)
helpers = ["TestHarness.hs", "TestParserFragments.hs", "TestSharedCache.hs", "TestProgramBinary.hs", "TestProgramBinaryChecks.hs", "TestProgramBuildIdentity.hs"]
for name in helpers:
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

main = root / "dev/cache-codec/integration/Main.hs"
flags = ["--make", "-O0", "-w", "-threaded", "-rtsopts", "-isrc", "-itest", "-odir", "build", "-hidir", "build", str(main)]
manifest = {"flags": flags, "compiler": subprocess.check_output(["ghc", "--info"], text=True), "GHC_ENVIRONMENT": os.environ.get("GHC_ENVIRONMENT"), "GHC_PACKAGE_PATH": os.environ.get("GHC_PACKAGE_PATH"), "approval": "controlled fixture build only; output executable name is immaterial; no other injected flags"}
approved = hashlib.sha256(json.dumps(manifest, sort_keys=True).encode()).hexdigest()
(overlay / "approved-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
environment = dict(os.environ, XDG_CACHE_HOME=str(overlay / "cache-home"), TMPDIR=str(overlay / "tmp"), TERSUS_TEST_APPROVED_BUILD_IDENTITY=approved)
records = [{"label": "controlled approved manifest", "sha256": approved}]

def build(label):
    executable = overlay / "bin" / label
    # Clean the identity module's objects when switching approval mode: environment
    # variables are not GHC recompilation dependencies.
    for suffix in ["o", "hi", "dyn_o", "dyn_hi"]:
        path = overlay / "build" / ("TestProgramBuildIdentity." + suffix)
        if path.exists():
            path.unlink()
    result = subprocess.run(["ghc"] + flags + ["-o", str(executable)], cwd=overlay, env=environment, capture_output=True, text=True, timeout=240)
    if result.returncode:
        raise RuntimeError((label, result.stdout, result.stderr))
    return executable

def run(executable, label, role, extra=None, expect_success=True):
    marker = overlay / (label + ".marker")
    env = dict(environment, TERSUS_SHARED_CACHE_PROBE=str(marker), TERSUS_SHARED_BINARY_PROBE=role)
    if extra:
        env.update(extra)
    result = subprocess.run([str(executable), "testSharedCacheProbe", "--child", "+RTS", "-N1", "-RTS"], cwd=overlay, env=env, capture_output=True, text=True, timeout=30)
    if (result.returncode == 0) != expect_success:
        raise RuntimeError((label, result.stdout, result.stderr))
    content = marker.read_text() if marker.exists() else ""
    records.append({"label": label, "exit_code": result.returncode, "marker": content, "stdout": result.stdout.strip()})
    print(label + " exit=" + str(result.returncode) + (" identity=" + repr(content.splitlines()) if role == "identity" else ""), flush=True)
    return content

baseline = build("approved-baseline")
run(baseline, "seed", "seed")
run(baseline, "fresh-process-hit", "hit")
baseline_identity = run(baseline, "baseline-identity", "identity").splitlines()
run(baseline, "source-miss", "miss", {"TERSUS_SHARED_BINARY_SOURCE": "return 314159;\n"})
run(baseline, "stage-miss", "miss", {"TERSUS_SHARED_BINARY_STAGE": "binary-other-stage"})

variants = [
    ("compiler-source", "src/Hash.hs", lambda s: s + "\n-- controlled compiler source change\n", True),
    ("harness-source", "test/TestHarness.hs", lambda s: s + "\n-- controlled harness source change\n", True),
    ("codec-source", "test/TestProgramBinary.hs", lambda s: s + "\n-- controlled codec source change; format unchanged\n", True),
    ("codec-version", "test/TestProgramBinary.hs", lambda s: s.replace('codecVersion = "tersus-test-program binary 1\\n"', 'codecVersion = "tersus-test-program binary 2\\n"'), True),
    ("compiler-metadata", "test/TestProgramBuildIdentity.hs", lambda s: s.replace("compilerName, showVersion compilerVersion, os, arch", 'compilerName, showVersion compilerVersion, os, arch, "controlled alternate compiler metadata"'), True),
    ("test-only-name", "test/TestProgramBinaryChecks.hs", lambda s: s.replace("rich roundtrip structural equality", "renamed test-only assertion"), False),
]
for label, relative, mutate, misses in variants:
    target = overlay / relative
    original = target.read_text()
    changed = mutate(original)
    if changed == original:
        raise RuntimeError("mutation did not apply: " + label)
    try:
        target.write_text(changed)
        executable = build(label)
        identity = run(executable, label + "-identity", "identity").splitlines()
        if (identity[0] != baseline_identity[0]) != misses:
            raise RuntimeError("wrong key relation: " + label)
        if (identity[1] != baseline_identity[1]) != misses:
            raise RuntimeError("wrong compiler identity relation: " + label)
        run(executable, label + "-lookup", "miss" if misses else "hit")
    finally:
        target.write_text(original)
restored = build("approved-restored")
run(restored, "restored-fresh-process-hit", "hit")

# Default, unapproved builds must not share the approved namespace; each remains
# reusable across fresh processes of its own exact executable.
environment.pop("TERSUS_TEST_APPROVED_BUILD_IDENTITY")
default = build("default-executable")
default_identity = run(default, "default-identity", "identity").splitlines()
if default_identity[0] == baseline_identity[0] or default_identity[1:] != baseline_identity[1:]:
    raise RuntimeError("default executable identity was not isolated from the approved manifest")
run(default, "default-does-not-trust-approved", "miss")
run(default, "default-seed", "seed")
run(default, "default-fresh-process-hit", "hit")

(root / "dev/cache-codec/integration-identity-results.json").write_text(json.dumps(records, indent=2) + "\n")
