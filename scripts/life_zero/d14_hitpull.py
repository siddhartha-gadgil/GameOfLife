#!/usr/bin/env python3
"""D14 (R-26): one extra glider D (flying SW or NE) that meets the pull reaction at k = 0 while it is
in progress or just finished, and passes when k >= 1.  Frame of SlidingBlock.lean; salvo = pullSalvo
(or its mirror image with --mirror).  Records every (D, outcome at k = 0) for which
   k = 1, 2, 3, 40: salvo + D + counter k -> counter (k - 1) + D   (D unchanged)
and the outcome at k = 0 is settled.  Prints those whose k = 0 outcome is one block + at most one
glider."""
import sys
from multiprocessing import Pool
from dcat import *
from common import step_cells, life
from recipes import settle

MIRROR = '--mirror' in sys.argv
PULL = [(SE, -2, -6), (SE, -8, -11)] if MIRROR else [(SE, -5, 0), (SE, 1, -29)]
T0 = -200


def evolve(gl, k, n):
    cells = set(counter(k))
    for w in gl:
        g = glider_at(*w, T0)
        if life.chebyshev_dist(g, cells) < 3:
            return None
        cells |= g
    for _ in range(n - T0):
        cells = step_cells(cells)
    return cells


def job(args):
    d, L = args
    out = []
    for tau in range(-200, 200):
        D = (d, L, tau)
        tc = time_at(D, (6.5, 10.5))
        if not (-15 <= tc <= 70):
            continue
        ok = True
        for k in (1, 2, 3, 40):
            n = 4 * k + 300
            c = evolve(PULL + [D], k, n)
            if c != set(counter(k - 1)) | glider_at(*D, n):
                ok = False
                break
        if not ok:
            continue
        c = evolve(PULL + [D], 0, 100)
        if c is None:
            continue
        st, t, rest, gl = settle(c, 100, max_gen=800, max_pop=300, max_span=120)
        if st != 'settled':
            continue
        out.append((D, tc, sorted(rest), gl))
    return out


if __name__ == '__main__':
    jobs = [(d, L) for d in (SW, NE) for L in (range(0, 30) if d == SW else range(-30, 1))]
    with Pool(8) as p:
        for res in p.imap_unordered(job, jobs):
            for (D, tc, rest, gl) in res:
                nb = len(rest)
                tag = ''
                if nb == 4:
                    u, v = min(rest)
                    if set(translate(BLOCK, u, v)) == set(rest):
                        tag = 'BLOCK (%d,%d)%s' % (u, v, ' = counter %d' % (u - 7) if v - u == 4 else '')
                if nb == 0:
                    tag = 'EMPTY'
                print(DIRNAME[D[0]], D[1], D[2], 'tc %.1f' % tc, tag, 'cells', nb, 'gliders', [(DIRNAME[w[0]], w[1], w[2]) for w in gl], flush=True)
