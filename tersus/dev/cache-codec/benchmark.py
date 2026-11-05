import json
import os
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[2]
probe = root / "dev/cache-codec/probe"
cpu = min(os.sched_getaffinity(0))
rawOnly = sys.argv[1:] == ["raw-only"]
resultsPath = root / "dev/cache-codec/results.json"
results = json.loads(resultsPath.read_text()) if rawOnly else []
phases = ["raw-read"] if rawOnly else ["raw-read", "read", "decode", "encode"]
for fixture in ["small", "large"]:
    path = root / ("dev/cache-codec/fixtures/" + fixture + ".show")
    for phase in phases:
        for repetition in range(1, 4):
            for codec in ["old", "binary"]:
                command = ["taskset", "-c", str(cpu), str(probe), "bench", codec, phase, str(path), "+RTS", "-N1", "-T"]
                run = subprocess.run(command, cwd=root, capture_output=True, text=True, timeout=180)
                if run.returncode:
                    raise RuntimeError((command, run.stdout, run.stderr))
                row = {"fixture": fixture, "phase": phase, "codec": codec, "repetition": repetition, "cpu_affinity": cpu, "output": run.stdout.strip()}
                results.append(row)
                print(json.dumps(row), flush=True)
                (root / "dev/cache-codec/results.json").write_text(json.dumps(results, indent=2) + "\n")
