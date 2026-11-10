#!/usr/bin/env python3
"""Elaborator time of an off run (TERSUS_ELABORATE_TIMING dir) against an on run (TERSUS_BOUNDS_ONLY_REPORT dir), per module.
Usage: eltime.py OFF_DIR ON_DIR [cpu]. Off runs written before the first on run (a warm-up) are left out."""
import os,collections,sys
def el(d, after=0):
    per=collections.defaultdict(list); first=None
    for f in os.listdir(d):
        p=os.path.join(d,f); mt=os.path.getmtime(p)
        if mt < after: continue
        mod=None; stats=False
        for l in open(p):
            if l.startswith('module '): mod=l[7:].split(' | ')[0]
            if l.startswith('elaborateSeconds'): t=float(l.split()[1])
            if l.startswith('elaborateCpuSeconds') and CPU: t=float(l.split()[1])
            if 'boundsReport | stats' in l: stats=True
        per[mod].append(t)
    return per
offd, ond = sys.argv[1], sys.argv[2]
CPU = len(sys.argv) > 3
firstOn=min(os.path.getmtime(os.path.join(ond,f)) for f in os.listdir(ond))
a=el(offd, firstOn); b=el(ond)
so=sum(sum(v) for v in a.values()); sn=sum(sum(v) for v in b.values())
print('elaborator (excluding off runs before the first on run): off %.1f s (%d runs) on %.1f s (%d runs) diff %.1f (%.2f%%)'%(so,sum(map(len,a.values())),sn,sum(map(len,b.values())),sn-so,100*(sn-so)/so))
for m in sorted(set(a)|set(b), key=lambda m:-sum(b.get(m,[0]))):
    print('  %-28s n=%d/%d off %.2f on %.2f'%(m,len(a.get(m,[])),len(b.get(m,[])),sum(a.get(m,[])),sum(b.get(m,[]))))
