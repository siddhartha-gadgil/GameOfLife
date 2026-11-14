#!/usr/bin/env python3
"""D8 (R-26): the core of the decrement-from-zero test in the frame of SlidingBlock.lean.

   pull salvo (pullSalvo at time 0) + detector D = (NE, -10, tauD) + restore pair
   U1 = (NW, 12, -6 + s), U2 = (SE, -10, -6 + s) (unit of d4_block2.py, found by d5_harmless.py)

k = 0 (case Z): counter 0 -> counter (-1) (pull) -> block (4, 11) (D consumed) -> counter 0 (U1, U2
consumed); nothing else.   k >= 1 (case NZ): counter k -> counter (k - 1); D passes and flies on
(NE); U1 and U2 annihilate each other.
Scans tauD and s; prints the valid ranges (k = 0, 1, 2, 3, 4, 5, 40)."""
from dcat import *
from common import PULL_SALVO, step_cells, life

PULL = [(SE, -5, 0), (SE, 1, -29)]
KS = (0, 1, 2, 3, 4, 5, 40)


T0 = -300


def run(D, U, k, gen=None):
    """from time T0 (all gliders far away) to time n"""
    cells = set(counter(k))
    for w in PULL + [D] + list(U):
        g = glider_at(*w, T0)
        if cells and life.chebyshev_dist(g, cells) < 3:
            return None, None
        cells |= g
    n = gen if gen is not None else 4 * k + 600
    for _ in range(n - T0):
        cells = step_cells(cells)
    return cells, n


def expect(D, U, k, n):
    if k == 0:
        return set(counter(0))
    c = set(counter(k - 1)) | glider_at(*D, n)
    return c


def ok(D, U):
    for k in KS:
        c, n = run(D, U, k)
        if c is None or c != expect(D, U, k, n):
            return False
    return True


def det_ok(D):
    c, n = run(D, [], 0, 400)
    if c != set(translate(BLOCK, 4, 11)):
        return False
    for k in KS[1:]:
        c, n = run(D, [], k)
        if c is None or c != expect(D, [], k, n):
            return False
    return True


if __name__ == '__main__':
    import sys
    U0 = [(NW, 12, -6), (SE, -10, -6)]
    dets = [t for t in range(-60, 160) if det_ok((NE, -10, t))]
    print('valid detector taus:', dets, flush=True)
    for tauD in [int(a) for a in sys.argv[1:]] or dets[:1]:
        D = (NE, -10, tauD)
        goods = [s for s in range(0, 300) if ok(D, [shift_wl(w, 0, 0, s) for w in U0])]
        print('tauD', tauD, 'valid s:', goods, flush=True)
