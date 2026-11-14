#!/usr/bin/env python3
"""D6 (R-26): restore chains X -> counter 0 made of harmless steps (single-glider moves of
d3_moves.py and two-glider units of d4_block2.py whose gliders each pass every counter k >= 0).
Prints all chains of length <= 2 for both detectors (stored gzipped: results/d6_chain.txt.gz)."""
from dcat import *

BYDISP = {}
MOVES = [(SE, -5, (-2, -1)), (SE, 6, (-1, -2)), (SW, -7, (1, -2)), (SW, 4, (2, -1)),
         (NW, -5, (2, 1)), (NW, 6, (1, 2)), (NE, -5, (-1, 2)), (NE, 6, (-2, 1))]
DET = {'SW9': ((SW, 9, 0), (7, 8)), 'NE-10': ((NE, -10, 0), (4, 11))}
GOAL = (7, 11)


def steps(U, p, want=None):
    """harmless steps from block position p: (kind, gliders, new position)"""
    out = []
    if want is not None:
        U = BYDISP.get((want[0] - p[0], want[1] - p[1]), [])
    for (d, rl, (u, v)) in MOVES:
        w = (d, rl + lane_of(d, p), 0)
        if harmless(w):
            out.append(('move', [w], (p[0] + u, p[1] + v)))
    for un in U:
        if un[3]:
            continue
        w = move_unit(un, p[0], p[1], 0)
        if harmless(w[0]) and harmless(w[1]):
            out.append(('unit%s' % ('F' if un[4] else 'A'), [w[0], w[1]], (p[0] + un[2][0], p[1] + un[2][1])))
    return out


if __name__ == '__main__':
    U = load_units()
    for un in U:
        BYDISP.setdefault(un[2], []).append(un)
    for name, (D, X) in DET.items():
        for a in steps(U, X):
            if a[2] == GOAL:
                print(name, 'one step:', a[0], a[1])
                continue
            for b in steps(U, a[2], GOAL):
                if b[2] == GOAL:
                    print(name, 'two steps:', a[0], a[1], '->', a[2], '|', b[0], b[1])
