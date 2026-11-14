#!/usr/bin/env python3
"""D4 (R-26): catalogue of two-glider reactions with a block that leave one block (anywhere)
and at most one glider.  Block at (0, 0) .. (1, 1); g1 = (d1, l1, 0) on a lane that interacts
with the block alone; g2 = (d2, l2, tau2) any lane within 13 of the block, reaching the block
between -60 and +60 generations after g1 (both orders of directions, so every pair is covered).

Output: results/d4_block2.txt (stored gzipped as results/d4_block2.txt.gz), one line per hit:
  d1 l1 d2 l2 tau2  dx dy  [glider world lines]  free
(free = the two gliders do not interact without the block).
"""
import os
import sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, NE, NW, glider_at, DIRNAME, cells_of_window, translate, step_cells   # noqa: E402
from reactions import run_free                                                                 # noqa: E402
from net import time_at                                                                        # noqa: E402

BLOCK = frozenset(cells_of_window(0, 0, [3, 3]))
CEN = (0.5, 0.5)
DIRS = (SE, SW, NW, NE)
INTER = {d: range(-7, 5) if d == SW else range(-5, 7) for d in DIRS}   # from d3_moves.py
# (SW interacting rel lanes -7 .. 4, the others -5 .. 6; block lane 0 for SE/NW/NE, SW lane of (0,0) is 0)


def free_ok(a, b, t0):
    c = glider_at(*a, t0) | glider_at(*b, t0)
    for t in range(t0, t0 + 300):
        if c != glider_at(*a, t) | glider_at(*b, t):
            return False
        c = step_cells(c)
    return True


def job(args):
    d1, l1, d2 = args
    g1 = (d1, l1, 0)
    tc1 = time_at(g1, CEN)
    out = []
    for l2 in range(-13, 14):
        for tau in range(-700, 700):
            g2 = (d2, l2, tau)
            dt = time_at(g2, CEN) - tc1
            if not (-60 <= dt <= 60):
                continue
            if d2 == d1 and (l2, tau) == (l1, 0):
                continue
            t0 = int(min(tc1, tc1 + dt)) - 40
            st, t, rest, gl = run_free([g1, g2], extra=BLOCK, t0=t0, max_gen=600, max_pop=150, max_span=60)
            if st != 'settled' or len(rest) != 4 or len(gl) > 1:
                continue
            u, v = min(rest)
            if set(translate(BLOCK, u, v)) != set(rest):
                continue
            out.append((DIRNAME[d1], l1, DIRNAME[d2], l2, tau, u, v, gl, free_ok(g1, g2, t0 - 150)))
    return out


if __name__ == '__main__':
    jobs = [(d1, l1, d2) for d1 in DIRS for l1 in INTER[d1] for d2 in DIRS]
    n = 0
    with Pool(8) as p:
        for res in p.imap_unordered(job, jobs):
            for r in res:
                n += 1
                print(*r, flush=True)
    print('hits', n)
