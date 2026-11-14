#!/usr/bin/env python3
"""D9 (R-26): restore chains of results/d6_chain.txt usable in the frame of the pull generator:
gliders flying SE (from the side of the pull generator), NE (from the free south-west side), or
NW on lanes x - y <= -13 or >= 7 (frame of SlidingBlock.lean; they then pass the pull salvo
head-on, results/z0_headon.txt).  No SW glider (it would come through the assembly K).
For each: the NZ case (all four gliders + counter k, k = 0 .. 6, 40, no detector product):
survivors must be the same for all k and contain no NE glider (it would fly into K)."""
from d7_unitnz import parse, nz_outcome
from dcat import *
import sys
MIRROR = '--mirror' in sys.argv
if MIRROR: sys.argv.remove('--mirror')


def nw_ok(w):
    if w[0] != NW:
        return True
    c = -w[1]
    if MIRROR:
        return c <= -16 or c >= 4
    return c <= -13 or c >= 7


if __name__ == '__main__':
    seen = set()
    for line in __import__('gzip').open('results/d6_chain.txt.gz', 'rt'):
        if 'two steps' not in line:
            continue
        det, u1, pos, u2 = parse(line)
        if det != ('SW9' if MIRROR else 'NE-10'):
            continue
        gl = u1 + u2
        bad = NE if MIRROR else SW
        if any(w[0] == bad for w in gl) or not all(nw_ok(w) for w in gl):
            continue
        key = tuple(sorted(gl))
        if key in seen:
            continue
        seen.add(key)
        res = nz_outcome(gl)
        if res is None or (len(sys.argv) < 2 and any(w[0] == (SW if MIRROR else NE) for w in res)):
            continue
        print(det, 'unit1', [(DIRNAME[w[0]], w[1], w[2]) for w in u1], 'block', pos, 'unit2',
              [(DIRNAME[w[0]], w[1], w[2]) for w in u2], 'NZ survivors', [(DIRNAME[w[0]], w[1], w[2]) for w in res], flush=True)
