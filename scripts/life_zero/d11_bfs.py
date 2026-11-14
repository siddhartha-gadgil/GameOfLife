#!/usr/bin/env python3
"""D11 (R-26): breadth-first search of restore programs X -> counter 0 made of single-glider moves
(d3_moves.py) and two-glider units (d4_block2.py, closed under symmetry), where every glider is
ALLOWED by the geometry of the pull generator (frame of SlidingBlock.lean):

  original frame (gate K north-east of the register, free side south-west), detector NE-10:
    SE gliders: harmless (pass every counter k >= 0) and lane <= -10 or >= 5 (4 lanes or more from
                the salvo lanes -5 and 1);
    NE gliders: harmless and x + y <= 6 (4 lanes or more from the detector, x + y = 10);
    NW gliders: x - y <= -13 or >= 7 (they pass the salvo head-on, results/z0_headon.txt);
    SW gliders: none (they would come through K).
  mirrored frame (--mirror; salvo lanes -2, -8, detector SW9, K south-west): the mirror image of
  these rules: SE harmless and lane <= -12 or >= 3; SW harmless and x + y <= 5 ... (see allowed()).
Prints the shortest programs (fewest gliders) up to depth 3."""
import sys
from collections import deque
from dcat import *

MIRROR = '--mirror' in sys.argv
REG = '--reg' in sys.argv          # REG1 frame: both NE and SW sides of the register are free
DETSW = '--sw' in sys.argv          # with --reg: detector SW9 instead of NE-10
MOVES = [(SE, -5, (-2, -1)), (SE, 6, (-1, -2)), (SW, -7, (1, -2)), (SW, 4, (2, -1)),
         (NW, -5, (2, 1)), (NW, 6, (1, 2)), (NE, -5, (-1, 2)), (NE, 6, (-2, 1))]
_A = {}


def allowed(w):
    key = (w[0], w[1])
    if key in _A:
        return _A[key]
    d, L = key
    if d == NW:
        c = -L
        r = (c <= -16 or c >= 4) if MIRROR else (c <= -13 or c >= 7)
    elif d == SE:
        r = harmless(w) and ((L <= -12 or L >= 3) if MIRROR else (L <= -10 or L >= 5))
    elif REG and d in (NE, SW):
        r = harmless(w)
    elif d == NE:
        r = (not MIRROR) and harmless(w) and (-L <= 6 or -L == 10)
    else:
        r = MIRROR and harmless(w) and (L <= 5 or L == 9)
    _A[key] = r
    return r


if __name__ == '__main__':
    U = load_units()
    start = (7, 8) if MIRROR else (4, 11)
    goal = (7, 11)
    steps = []
    for (d, rl, (u, v)) in MOVES:
        steps.append(('move', [(d, rl, 0)], (u, v)))
    for un in U:
        if not un[3]:
            steps.append(('unit', [un[0], un[1]], un[2]))
    print('steps', len(steps), flush=True)
    prev = {start: None}
    frontier = [start]
    for depth in range(3):
        nxt = []
        for p in frontier:
            for (kind, gl, (u, v)) in steps:
                q = (p[0] + u, p[1] + v)
                if q in prev or abs(q[0] - 6) > 14 or abs(q[1] - 10) > 14:
                    continue
                g2 = [shift_wl(w, p[0], p[1], 0) for w in gl]
                if not all(allowed(w) for w in g2):
                    continue
                prev[q] = (p, kind, g2)
                nxt.append(q)
        frontier = nxt
        print('depth', depth + 1, 'positions', len(prev), 'goal' if goal in prev else '', flush=True)
        if goal in prev:
            break
    q = goal
    while q in prev and prev[q]:
        p, kind, g2 = prev[q]
        print('  ', p, '->', q, kind, [(DIRNAME[w[0]], w[1], w[2]) for w in g2])
        q = p
