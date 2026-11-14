#!/usr/bin/env python3
"""S4: salvos that contain the pulling salvo and move the block by (+1, +1).

Why: the gliders of a salvo are put on their lanes by reflectors standing beside the diagonal
(R-21, 3.1).  A reflector lets parallel gliders pass only on its far side, 4 or more lanes away.
With RF2 and RF3 of the certified generator PG1 in place (pull lanes -1 and 5 relative to the
block), a further glider can be added only on a lane <= -5 or >= 9 (relative to the block), by a
reflector further downstream, or on the lanes -1 and 5 themselves at multiples of 30 generations.
None of the 176 three-glider pushes of scripts/life_search avoids the lanes -4 .. 8 (p1_pushes.py),
and `pushSalvo` has two gliders on one lane 25 generations apart.  So we look for salvos
        pullSalvo  +  two more gliders on lanes <= -5 or >= 9
with net displacement (+1, +1): then "push" = "PG1 fires" + two gliders, and PG1 is reused as it is.

Frame: block with upper left cell (0, 0); pull gliders a = (SE, -1, 0), b = (SE, 5, -29) (world
lines as in common.py); extra gliders (SE, l1, t1), (SE, l2, t2), l in LANES, t in TMIN .. TMAX,
|l1 - l2| >= 4.  A hit: after the reaction exactly one block, displaced by (1, 1), and nothing
else (bit-parallel board; hits are re-checked with the set simulator).  All single-block outcomes
are counted by displacement.

Usage: s4_salvo4.py [TMIN TMAX]      Output: results/s4_salvo4.json, summary on stdout
"""
import json
import os
import sys
import time
from multiprocessing import Pool

from common import glider_at, SE, life, step_cells, evolve_cells

A = (SE, -1, 0)
B = (SE, 5, -29)
LANES = list(range(-14, -4)) + list(range(9, 16))
TMIN, TMAX = -140, 60
BOARD = (-95, -95, 135, 135)
BLOCK = {(0, 0), (1, 0), (0, 1), (1, 1)}
SETTLE = 240


def start_time(wls):
    """A time (multiple of 4) at which every glider is at least 8 cells before the block."""
    return 4 * (min(w[2] for w in wls) // 4) - 44


def free_salvo(wls, t0):
    """Do the gliders fly freely as a set (for 12 generations)?"""
    c = set()
    for w in wls:
        g = glider_at(*w, t0)
        if g & c:
            return False
        c |= g
    c2 = evolve_cells(c, 12)
    e = set()
    for w in wls:
        e |= glider_at(*w, t0 + 12)
    return c2 == e


def work(job):
    l1, l2, tmin, tmax = job
    bd = life.Board(*BOARD)
    step = bd.step
    blk = bd.of_cells(BLOCK)
    targets = {}
    for dx in range(-6, 7):
        for dy in range(-6, 7):
            targets[bd.of_cells({(x + dx, y + dy) for (x, y) in BLOCK})] = (dx, dy)
    hits, table = [], {}
    gl = {}
    for t1 in range(tmin, tmax + 1):
        for t2 in range(tmin, tmax + 1):
            if l1 == l2 and t2 <= t1:
                continue
            wls = [A, B, (SE, l1, t1), (SE, l2, t2)]
            t0 = start_time(wls)
            if abs(l1 - l2) < 8 and abs(t1 - t2) < 24 and not free_salvo(wls, t0):
                continue
            g = blk
            for w in wls:
                g |= bd.of_cells(glider_at(*w, t0))
            n = max(0, max(t1, t2)) - t0 + SETTLE
            ok = True
            for i in range(n):
                g = step(g)
                if (i & 31) == 0:
                    if g & bd.ring:
                        ok = False
                        break
                    if g == 0:
                        break
            if not ok or (g & bd.ring):
                continue
            d = targets.get(g)
            if d is None:
                continue
            table[d] = table.get(d, 0) + 1
            if d == (1, 1):
                hits.append((l1, t1, l2, t2))
    return hits, table


def verify(h):
    l1, t1, l2, t2 = h
    wls = [A, B, (SE, l1, t1), (SE, l2, t2)]
    t0 = start_time(wls)
    c = set(BLOCK)
    for w in wls:
        c |= glider_at(*w, t0)
    n = max(0, t1, t2) - t0 + SETTLE
    return evolve_cells(c, n) == {(x + 1, y + 1) for (x, y) in BLOCK}


def main():
    tmin, tmax = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (TMIN, TMAX)
    t = time.time()
    jobs = [(l1, l2, tmin, tmax) for i, l1 in enumerate(LANES) for l2 in LANES[i:]
            if l1 == l2 or abs(l1 - l2) >= 4]
    jobs = [j for j in jobs if j[0] != j[1]]
    hits, table = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for hs, tb in pool.imap_unordered(work, jobs, chunksize=1):
            hits.extend(hs)
            for k, v in tb.items():
                table[k] = table.get(k, 0) + v
    hits.sort()
    good = [h for h in hits if verify(h)]
    print('lane pairs %d, delays %d .. %d: runs about %d, %.0f s' % (len(jobs), tmin, tmax, len(jobs) * (tmax - tmin + 1) ** 2, time.time() - t))
    print('single-block outcomes by displacement:', sorted(table.items()))
    print('hits with displacement (1, 1): %d, verified with the set simulator: %d' % (len(hits), len(good)))
    for h in good:
        print('   extra gliders (SE, %d, %d), (SE, %d, %d)' % h)
    json.dump({'tmin': tmin, 'tmax': tmax, 'lanes': LANES, 'table': [[list(k), v] for k, v in sorted(table.items())], 'hits': good},
              open('results/s4_salvo4.json', 'w'))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
