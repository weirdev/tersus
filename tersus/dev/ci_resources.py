#!/usr/bin/env python3
import json
import os
import pathlib
import sys


def read(path):
    try:
        return pathlib.Path(path).read_text().strip()
    except OSError:
        return None


def main():
    try:
        affinity = sorted(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        affinity = None
    hardware = {"affinity": affinity, "meminfo": read("/proc/meminfo")}
    for name in ["cpu.max", "memory.max", "memory.swap.max", "memory.events"]:
        hardware[name] = read("/sys/fs/cgroup/" + name)
    try:
        print("[CI_HARDWARE] " + json.dumps(hardware, sort_keys=True), file=sys.stderr, flush=True)
    except OSError:
        pass


if __name__ == "__main__":
    main()
