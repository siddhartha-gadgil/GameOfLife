#!/usr/bin/env python3
"""D12 (R-26): all restore programs of one or two steps (d11_bfs.py rules) whose gliders, together
with the pull salvo and the detector, satisfy the R-25 lane rule: two parallel gliders are either
on the same lane or at least 4 lanes apart.  (Same-lane timing is checked later.)
Usage: d12_programs.py [--mirror]  -> results/d12_programs[_mirror].txt"""
import os
import sys
from d11_bfs import *

ANTI = int(os.environ.get('D12_ANTI', '0'))
MPULL = [(SE, -2, -6), (SE, -8, -11)]
PULL = [(SE, -5, 0), (SE, 1, -29)]


def lanes_ok(gl):
    for i in range(len(gl)):
        for j in range(i):
            a, b = gl[i], gl[j]
            if a[0] == b[0] and a[1] != b[1] and abs(a[1] - b[1]) < 4:
                return False
            # antiparallel NE / SW gliders (D's lane family): at least ANTI lanes apart, so that a
            # survivor never flies into the emitter of the other (results/z0_rfpass.txt)
            if ANTI and {a[0], b[0]} == {NE, SW} and abs(abs(a[1]) - abs(b[1])) < ANTI:
                return False
    return True


if __name__ == '__main__':
    U = load_units()
    sw = DETSW if REG else MIRROR
    start = (7, 8) if sw else (4, 11)
    D = (SW, 9, 0) if sw else (NE, -10, 0)
    fixed = (MPULL if MIRROR else PULL) + [D]
    goal = tuple(int(v) for v in os.environ.get('D12_GOAL', '7,11').split(','))
    steps = [('move', [(d, rl, 0)], (u, v)) for (d, rl, (u, v)) in MOVES]
    steps += [('unit', [un[0], un[1]], un[2]) for un in U if not un[3]]
    bydisp = {}
    for st in steps:
        bydisp.setdefault(st[2], []).append(st)
    n = 0
    for (k1, g1, d1) in steps:
        g1p = [shift_wl(w, start[0], start[1], 0) for w in g1]
        if not all(allowed(w) for w in g1p) or not lanes_ok(fixed + g1p):
            continue
        p = (start[0] + d1[0], start[1] + d1[1])
        if p == goal:
            n += 1
            print('1', [(DIRNAME[w[0]], w[1], w[2]) for w in g1p], flush=True)
            continue
        for (k2, g2, d2) in bydisp.get((goal[0] - p[0], goal[1] - p[1]), []):
            g2p = [shift_wl(w, p[0], p[1], 0) for w in g2]
            if not all(allowed(w) for w in g2p) or not lanes_ok(fixed + g1p + g2p):
                continue
            n += 1
            print('2', [(DIRNAME[w[0]], w[1], w[2]) for w in g1p], p, [(DIRNAME[w[0]], w[1], w[2]) for w in g2p], flush=True)
    print('programs', n)
