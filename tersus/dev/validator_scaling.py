#!/usr/bin/env python3
"""How the validator's time grows with what is in scope at a loop.

Each family is a function with N of something around a loop, checked with
`tersus-exe check`; the table is the time to check it for each N. A salt
constant makes every program new to the verdict cache, so each is checked.

  python3 dev/validator_scaling.py                 # every family, default sizes
  python3 dev/validator_scaling.py --family unrelated --sizes 0,16,32,64
  python3 dev/validator_scaling.py --tersus /path/to/tersus-exe --timeout 300

Families:
  unrelated  N locals `bK = x + K` before a loop that changes one local
  branches   N `if x > K { cK = 1; } else { cK = 2; }` before that loop
  changed    the loop changes N locals, with nothing else in scope
  nested     N unrelated locals before a loop nested in another
  noloop     N unrelated locals and no loop (the floor)
"""
import argparse
import os
import random
import subprocess
import sys
import tempfile
import time

HEADER = "fn f(a: List<Int>, x: Int) -> Int [{ affirm x >= 0; affirm x < 1000; }] [{ }] {"


def unrelated(n):
    return " ".join(f"b{k} = x + {k};" for k in range(n))


def branches(n):
    return " ".join(f"if x > {k} {{ c{k} = 1; }} else {{ c{k} = 2; }};" for k in range(n))


def loop(changed):
    inits = " ".join(f"n{j} = 0;" for j in range(changed))
    updates = " ".join(f"n{j} = i;" for j in range(changed))
    return f"{inits} for i in 0..size(a) {{ if get(a, i) > 2 {{ {updates} }}; }};"


def nested_loop():
    return "n0 = 0; for i in 0..size(a) { for j in 0..i { if get(a, j) > 2 { n0 = j; }; }; };"


def program(family, n, salt):
    if family == "unrelated":
        body = unrelated(n) + " " + loop(1)
    elif family == "branches":
        body = branches(n) + " " + loop(1)
    elif family == "changed":
        body = loop(max(n, 1))
    elif family == "nested":
        body = unrelated(n) + " " + nested_loop()
    elif family == "noloop":
        body = unrelated(n) + " n0 = 0;"
    else:
        raise ValueError(family)
    return f"{HEADER} salt = {salt}; {body} return n0; }}; return f([1, 2, 3], 5);\n"


FAMILIES = {
    "unrelated": [0, 8, 16, 32, 64],
    "branches": [0, 8, 16, 32, 64],
    "changed": [1, 2, 4, 8],
    "nested": [0, 8, 16, 32],
    "noloop": [0, 64],
}


def check(tersus, source, timeout):
    with tempfile.NamedTemporaryFile("w", suffix=".tersus", delete=False) as handle:
        handle.write(source)
        path = handle.name
    try:
        start = time.monotonic()
        try:
            result = subprocess.run([tersus, "check", path], capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return None, "timeout"
        elapsed = time.monotonic() - start
        verdict = "ok" if result.returncode == 0 else (result.stdout + result.stderr).strip().splitlines()[-1][:80]
        return elapsed, verdict
    finally:
        os.unlink(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--tersus", default="tersus-exe", help="the tersus-exe binary (default: on the PATH)")
    parser.add_argument("--family", action="append", choices=sorted(FAMILIES), help="a family to run (repeatable)")
    parser.add_argument("--sizes", help="comma-separated sizes, instead of each family's defaults")
    parser.add_argument("--timeout", type=float, default=600, help="seconds before a check is given up")
    args = parser.parse_args()
    families = args.family or list(FAMILIES)
    print(f"{'family':<10} {'N':>4} {'seconds':>9}  verdict")
    for family in families:
        sizes = [int(s) for s in args.sizes.split(",")] if args.sizes else FAMILIES[family]
        for n in sizes:
            elapsed, verdict = check(args.tersus, program(family, n, random.randrange(1 << 30)), args.timeout)
            shown = f"{elapsed:9.2f}" if elapsed is not None else f"{'>' + str(int(args.timeout)):>9}"
            print(f"{family:<10} {n:>4} {shown}  {verdict}", flush=True)


if __name__ == "__main__":
    sys.exit(main())
