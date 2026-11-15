#!/usr/bin/env python3
"""The rows of TestScheduling.measuredWeights (or, with --peaks, of measuredPeaksMiB) from CI logs.

Give it the logs of recent CI runs (`gh run view <id> --log > run.log`, or one job's log from
`gh api repos/<owner>/<repo>/actions/jobs/<id>/logs`). A group's weight is the median, over the
logs, of the smaller of its `[CPU] <group> <s>s` (what its process and the processes it waited for
used) and its `[TIME] <group> <s>s` (how long it held a worker), in seconds, rounded up: the first
overstates a group whose builds run in parallel, the second one that waited on another group's build. Peaks are the largest `[PEAK] <group> <own>MiB ...` (the group's process's largest
resident set) with a tenth added, rounded up to 256 MiB, for the groups above the 1024 MiB default.
"""
import math
import re
import statistics
import sys

CPU = re.compile(r"\[CPU\] (\S+) ([\d.]+)s")
TIME = re.compile(r"\[TIME\] (\S+) ([\d.]+)s")
PEAK = re.compile(r"\[PEAK\] (\S+) (\d+)MiB")


def main(arguments):
    peaks = arguments[:1] == ["--peaks"]
    paths = arguments[1:] if peaks else arguments
    found = {}
    for path in paths:
        cpu, held = {}, {}
        with open(path, errors="replace") as log:
            for line in log:
                if peaks:
                    match = PEAK.search(line)
                    if match:
                        found.setdefault(match.group(1), []).append(float(match.group(2)))
                    continue
                for pattern, into in ((CPU, cpu), (TIME, held)):
                    match = pattern.search(line)
                    if match:
                        into[match.group(1)] = float(match.group(2))
        for group, seconds in cpu.items():
            found.setdefault(group, []).append(min(seconds, held.get(group, seconds)))
    for group in sorted(found):
        if peaks:
            value = math.ceil(max(found[group]) * 1.1 / 256) * 256
            if value <= 1024:
                continue
        else:
            value = max(1, math.ceil(statistics.median(found[group])))
        print(f'    , ("{group}", {value})')


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("usage: ci_weights.py [--peaks] <CI log>...")
    main(sys.argv[1:])
