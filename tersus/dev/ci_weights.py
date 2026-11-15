#!/usr/bin/env python3
"""Median CI processor time of each test group, as the rows of TestScheduling.groupWeight.

Give it the logs of recent CI runs (`gh run view <id> --log > run.log`, or one job's log from
`gh api repos/<owner>/<repo>/actions/jobs/<id>/logs`); it reads the harness's `[CPU] <group> <s>s`
lines (what a group's process and the processes it waited for used) and prints one
`, ("<group>", <seconds>)` row per group, the median over the logs, rounded up.
"""
import math
import re
import statistics
import sys

CPU = re.compile(r"\[CPU\] (\S+) ([\d.]+)s")


def main(paths):
    times = {}
    for path in paths:
        with open(path, errors="replace") as log:
            for line in log:
                match = CPU.search(line)
                if match:
                    times.setdefault(match.group(1), []).append(float(match.group(2)))
    for group in sorted(times):
        print(f'        , ("{group}", {max(1, math.ceil(statistics.median(times[group])))})')


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("usage: ci_weights.py <CI log>...")
    main(sys.argv[1:])
