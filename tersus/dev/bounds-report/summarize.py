#!/usr/bin/env python3
"""Summarize bounds-only report directories (Phase 0 spike). Usage: summarize.py DIR [DIR...]"""
import collections, os, sys

def parse(dirs):
    runs = []
    for d in dirs:
        for f in sorted(os.listdir(d)):
            mod, el, pr, stats, finds, lows = None, 0.0, 0.0, None, [], []
            for line in open(os.path.join(d, f), errors="replace"):
                line = line.rstrip("\n")
                if line.startswith("module "):
                    mod = line[7:]
                elif line.startswith("elaborateSeconds "):
                    el = float(line.split()[1])
                elif line.startswith("probeSeconds "):
                    pr = float(line.split()[1])
                elif line.startswith("boundsReport | stats"):
                    p = line.split(" | ")
                    stats = {k: int(v) for k, v in (x.rsplit(" ", 1) for x in p[2:])}
                elif line.startswith("boundsReport | "):
                    p = line.split(" | ", 3)
                    finds.append((p[1], p[2], p[3] if len(p) > 3 else ""))
                elif line.startswith("boundsLower | "):
                    p = line.split(" | ", 3)
                    lows.append((p[1], p[2], p[3] if len(p) > 3 else ""))
            runs.append(dict(dir=d, file=f, module=mod, el=el, pr=pr, stats=stats, finds=finds, lows=lows))
    return runs

def main():
    runs = parse(sys.argv[1:])
    spike = [r for r in runs if r["stats"] is not None]
    seed = [r for r in runs if r["stats"] is None]
    print(f"elaborator runs: {len(runs)} (spike elaborator {len(spike)}, seed/other {len(seed)})")
    tot = collections.Counter()
    for r in spike:
        for k, v in r["stats"].items():
            tot[k] += v
    print("elaborate seconds (spike runs):", round(sum(r["el"] for r in spike), 2), " probe seconds:", round(sum(r["pr"] for r in spike), 2))
    print("totals:", dict(tot))
    checked = collections.OrderedDict()
    viol = collections.OrderedDict()
    lows = collections.OrderedDict()
    for r in spike:
        modname = (r["module"] or "?").split(" | ")[0]
        for fn, what, detail in r["finds"]:
            if what == "checked":
                checked[(modname, fn)] = "checked"
            elif what == "refused":
                checked[(modname, fn)] = "refused: " + detail
                viol.setdefault((modname, fn, what, detail), 0)
                viol[(modname, fn, what, detail)] += 1
            else:
                viol.setdefault((modname, fn, what, detail), 0)
                viol[(modname, fn, what, detail)] += 1
        for fn, what, detail in r["lows"]:
            lows.setdefault((modname, fn, what, detail), 0)
            lows[(modname, fn, what, detail)] += 1
    print(f"\ndistinct (module, function) checked: {len(checked)}; refused: {sum(1 for v in checked.values() if v != 'checked')}")
    print(f"\n== findings (distinct) {len(viol)} ==")
    for (m, fn, what, detail), n in viol.items():
        print(f"{m} | {fn} | {what} | {detail[:400]} | x{n}")
    print(f"\n== lowering (distinct) {len(lows)} ==")
    c = collections.Counter(w for (_, _, w, _) in lows)
    print(dict(c))
    for (m, fn, what, detail), n in lows.items():
        if what != "lowered and move-checked":
            print(f"{m} | {fn} | {what} | {detail[:600]} | x{n}")

main()
