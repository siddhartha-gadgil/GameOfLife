#!/usr/bin/env python3
"""Search R0: which lanes parallel to the stream of a Gosper gun can a glider use?

A glider flying SE (the direction of the stream of `gosperGun`, lane 14) or NW, on every lane
from -40 to 70 and with every phase tau = 0 .. 29, is run past the free gun.  `pass` means: after
the glider has left the neighbourhood of the gun, the configuration is exactly the free gun (with
its own gliders) plus the glider on its world line.

Consequence used in R-21: two guns firing in the same direction cannot have streams closer than
the width of the blocked band, so at most one glider of a salvo (lanes -5 and 1) can come
directly from a gun.

Usage: r0_obstruction.py        Output: results/r0_obstruction.txt (stdout)
"""
import os
from multiprocessing import Pool

from common import glider_at, bbox, step_cells, GUN, SE, NW, DIRNAME
import gates


def gun_cells(t):
    return gates.gun_at(t)


def work(job):
    d, lane = job
    passes = []
    for tau in range(30):
        # glider far from the gun at time 0: choose the world line representative
        # SE: comes from the upper left; NW: from the lower right.  Start 60 cells away.
        if d == SE:
            tau0 = tau + 30 * 8 + 0            # x = (t - tau0)/4 = -60 at t = 0
        else:
            tau0 = tau + 30 * 14               # x = (tau0 - t)/4 = +105 at t = 0
        wl = (d, lane, tau0)
        c = set(GUN) | glider_at(*wl, 0)
        T = 1000
        for _ in range(T):
            c = step_cells(c)
        expect = gun_cells(T) | glider_at(*wl, T)
        if c == expect:
            passes.append(tau)
    return d, lane, passes


def main():
    jobs = [(SE, lane) for lane in range(-40, 71)] + [(NW, -lane) for lane in range(-40, 71)]
    res = {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for d, lane, p in pool.imap_unordered(work, jobs, chunksize=2):
            res[(d, lane)] = p
    for d in (SE, NW):
        print('glider flying %s past the free gun (stream: SE, lane 14); lane = x - y of the canonical box' % DIRNAME[d])
        full = []
        for lane in range(-40, 71):
            key = (d, lane if d == SE else -lane)       # life.py lane of NW is -(x - y)
            if key not in res:
                continue
            n = len(res[key])
            if n < 30:
                full.append((lane, n))
        lanes = [l for l, n in full]
        print('  lanes on which not every phase passes: %d .. %d' % (min(lanes), max(lanes)))
        print('  (lane: number of passing phases out of 30):', ', '.join('%d: %d' % x for x in full))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
