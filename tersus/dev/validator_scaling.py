#!/usr/bin/env python3
"""How the validator's time grows with the shape of the code it checks.

Each family is a function with N of something in it, checked with
`tersus-exe check`; the table is the time to check it for each N. A salt
constant makes every program new to the verdict cache, so each is checked.

  python3 dev/validator_scaling.py                 # every family, default sizes
  python3 dev/validator_scaling.py --family unrelated --sizes 0,16,32,64
  python3 dev/validator_scaling.py --tersus /path/to/tersus-exe --timeout 300

A family whose shape repeats a condition tests a parameter of its own each
time, so that no condition follows from another and the arms are not pruned.
`joinedifs` is the deliberate exception: its tests are all on `x`, which is
what lets the bridge merge them, and it is the control the merged shapes are
read against.

Families:
  unrelated      N locals `bK = x + K` before a loop that changes one local
  branches       N `if x > K { cK = 1; } else { cK = 2; }` before that loop
  changed        the loop changes N locals, with nothing else in scope
  nested         N unrelated locals before a loop nested in another
  noloop         N unrelated locals and no loop (the floor)
  loopbranches   N independent `if pK > 0` in a loop body
  matcharms      N sequential `match` statements, each on its own parameter
                 of the one enum `E`
  nestedifs      N blocks of `if p > 0 { … if p > 0 { … } }`, two params each
  guardreturn    N guards of two tests each, returning from the inner one
  loopinarm      N `if pK > 0 { for … }` blocks
  joinedifs      N straight-line `if x > K { y = y + 1; }`, all on x
  chainaffirm    N steps of `y = y + 1`, each affirmed where it happens
  chainend       the same N steps with one affirm at the end
  unrelatedgoal  N locals off x, then one affirm about x (x is the hub)
  hintgoal       a goal N hops along a chain from the fact that proves it
  hintlinked     the same goal with that fact affirmed beside it
  nestedloops    loops nested N deep, each changing a local of its own
"""
import argparse
import os
import random
import subprocess
import sys
import tempfile
import time

PARAMS = "a: List<Int>, x: Int"
ARGS = "[1, 2, 3], 5"
CONTRACT = "[{ affirm x >= 0; affirm x < 1000; }] [{ }]"
ENUM = "enum E { A, B, C, }; impl Clone for E { }; impl Copy for E { }; "


def int_params(n):
    return [f"p{k}: Int" for k in range(n)], [str(k) for k in range(n)]


def enum_params(n):
    return [f"e{k}: E" for k in range(n)], [f"E::{'ABC'[k % 3]}" for k in range(n)]


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


def loop_branches(n):
    tests = " ".join(f"if p{k} > 0 {{ y = y + 1; }};" for k in range(n))
    return f"y = 0; for i in 0..size(a) {{ {tests} y = y + 1; }}; n0 = y;"


def match_arms(n):
    arms = " ".join(
        f"match e{k} {{ E::A => {{ y = y + 1; }}, E::B => {{ y = y + 2; }}, E::C => {{ y = y + 3; }}, }};"
        for k in range(n)
    )
    return f"y = 0; {arms} n0 = y;"


def nested_ifs(n):
    # N two-level blocks in a row, not one N-deep chain: a chain of N tests has
    # N+1 paths, so it would measure depth rather than the branching the family
    # is for.
    blocks = " ".join(
        f"if p{2 * k} > 0 {{ y = y + 1; if p{2 * k + 1} > 0 {{ y = y + 1; }}; }};" for k in range(n)
    )
    return f"y = 0; {blocks} n0 = y;"


def guard_return(n):
    guards = " ".join(
        f"if p{2 * k} > 0 {{ if p{2 * k + 1} > 0 {{ return y; }}; }}; y = y + 1;" for k in range(n)
    )
    return f"y = 0; {guards} n0 = y;"


def loop_in_arm(n):
    arms = " ".join(f"if p{k} > 0 {{ for i in 0..size(a) {{ y = y + 1; }}; }};" for k in range(n))
    return f"y = 0; {arms} n0 = y;"


def joined_ifs(n):
    tests = " ".join(f"if x > {k} {{ y = y + 1; }};" for k in range(n))
    return f"y = 0; {tests} n0 = y;"


def chain(n, affirm_each):
    steps = []
    for k in range(1, n + 1):
        steps.append(f"y{k} = y{k - 1} + 1;")
        if affirm_each:
            steps.append(f"affirm y{k} > y{k - 1};")
    end = "" if affirm_each or n == 0 else f"affirm y{n} > y0;"
    return f"y0 = x; {' '.join(steps)} {end} n0 = y{n};"


def unrelated_goal(n):
    return f"{unrelated(n)} g = x + 1; affirm g > x; n0 = g;"


def hint_goal(n, linked):
    steps = " ".join(f"z{k} = z{k - 1} + 1;" for k in range(1, n + 1))
    hint = f"affirm z{n} = x + {n + 1};" if linked else ""
    return f"z0 = x + 1; {steps} {hint} affirm z{n} > x; n0 = z{n};"


def nested_loops(n):
    inits = " ".join(f"m{k} = 0;" for k in range(n))
    body = ""
    for k in reversed(range(n)):
        body = f"for i{k} in 0..size(a) {{ m{k} = m{k} + 1; {body} }};"
    return f"n0 = 0; {inits} {body}"


def shape(family, n):
    """The declarations before `f`, its extra parameters and arguments, and its body."""
    if family == "unrelated":
        return "", ([], []), unrelated(n) + " " + loop(1)
    if family == "branches":
        return "", ([], []), branches(n) + " " + loop(1)
    if family == "changed":
        return "", ([], []), loop(max(n, 1))
    if family == "nested":
        return "", ([], []), unrelated(n) + " " + nested_loop()
    if family == "noloop":
        return "", ([], []), unrelated(n) + " n0 = 0;"
    if family == "loopbranches":
        return "", int_params(n), loop_branches(n)
    if family == "matcharms":
        return ENUM, enum_params(n), match_arms(n)
    if family == "nestedifs":
        return "", int_params(2 * n), nested_ifs(n)
    if family == "guardreturn":
        return "", int_params(2 * n), guard_return(n)
    if family == "loopinarm":
        return "", int_params(n), loop_in_arm(n)
    if family == "joinedifs":
        return "", ([], []), joined_ifs(n)
    if family == "chainaffirm":
        return "", ([], []), chain(n, True)
    if family == "chainend":
        return "", ([], []), chain(n, False)
    if family == "unrelatedgoal":
        return "", ([], []), unrelated_goal(n)
    if family == "hintgoal":
        return "", ([], []), hint_goal(n, False)
    if family == "hintlinked":
        return "", ([], []), hint_goal(n, True)
    if family == "nestedloops":
        return "", ([], []), nested_loops(n)
    raise ValueError(family)


def program(family, n, salt):
    declarations, (params, args), body = shape(family, n)
    signature = ", ".join([PARAMS] + params)
    call = ", ".join([ARGS] + args)
    return (
        f"{declarations}fn f({signature}) -> Int {CONTRACT} {{"
        f" salt = {salt}; {body} return n0; }}; return f({call});\n"
    )


FAMILIES = {
    "unrelated": [0, 8, 16, 32, 64],
    "branches": [0, 8, 16, 32, 64],
    "changed": [1, 2, 4, 8],
    "nested": [0, 8, 16, 32],
    "noloop": [0, 64],
    "loopbranches": [0, 4, 8, 10],
    "matcharms": [0, 4, 8, 10],
    "nestedifs": [0, 2, 4, 6],
    "guardreturn": [0, 2, 4, 6, 8],
    "loopinarm": [0, 2, 4, 6, 8],
    "joinedifs": [0, 16, 32, 64],
    "chainaffirm": [0, 32, 64, 128],
    "chainend": [0, 32, 64, 128],
    "unrelatedgoal": [0, 32, 64, 128],
    "hintgoal": [0, 32, 64, 128],
    "hintlinked": [0, 32, 64, 128],
    "nestedloops": [0, 2, 4, 6],
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
        if result.returncode == 0:
            return elapsed, "ok"
        lines = (result.stdout + result.stderr).strip().splitlines()
        return elapsed, lines[-1][:80] if lines else f"exit {result.returncode}"
    finally:
        os.unlink(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--tersus", default="tersus-exe", help="the tersus-exe binary (default: on the PATH)")
    parser.add_argument("--family", action="append", choices=sorted(FAMILIES), help="a family to run (repeatable)")
    parser.add_argument("--sizes", help="comma-separated sizes, instead of each family's defaults")
    parser.add_argument("--timeout", type=float, default=600, help="seconds before a check is given up")
    parser.add_argument("--print", metavar="N", type=int, help="print each family's program at size N and stop")
    args = parser.parse_args()
    if args.print is not None and args.print < 0:
        parser.error("--print takes a size of 0 or more")
    families = args.family or list(FAMILIES)
    if args.print is not None:
        for family in families:
            print(f"// {family}\n{program(family, args.print, 0)}")
        return
    print(f"{'family':<14} {'N':>4} {'seconds':>9}  verdict")
    for family in families:
        sizes = [int(s) for s in args.sizes.split(",")] if args.sizes else FAMILIES[family]
        for n in sizes:
            elapsed, verdict = check(args.tersus, program(family, n, random.randrange(1 << 30)), args.timeout)
            shown = f"{elapsed:9.2f}" if elapsed is not None else f"{'>' + str(int(args.timeout)):>9}"
            print(f"{family:<14} {n:>4} {shown}  {verdict}", flush=True)


if __name__ == "__main__":
    sys.exit(main())
