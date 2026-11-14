#!/usr/bin/env python3
"""D10 (R-26): the decision core with the MIRRORED pull salvo (frame of SlidingBlock.lean).

The pull generator is used in its mirror image M(x, y) = (y - 4, x + 4) (the reflection in the
register diagonal; it fixes every counter k), so that its gate K lies on the south-west side of
the register and the north-east side is free.  Core:
   mirrored pull salvo M(pullSalvo) (time 0)
   detector D = (SW, 9, tauD)                                         (d0_single.py)
   restore pair U1 = (NW, -3, 24 + s), U2 = (SE, 3, -32 + s)        (unit of d5_harmless.py)
k = 0 (case Z): counter 0 -> counter (-1) -> block (7, 8) -> counter 0, nothing else;
k >= 1 (case NZ): counter (k - 1), D flies on (SW), U1 + U2 annihilate each other.
Usage: d10_core.py [tauD ...]"""
import sys
from dcat import *
from common import PULL_SALVO, step_cells, life, glider_worldline

PULL = [(SE, -5, 0), (SE, 1, -29)]
KS = (0, 1, 2, 3, 4, 5, 6, 7, 40)
T0 = -300


def mirror_wl(w):
    c = translate(transform(glider_at(*w, 0), 6), -4, 4)
    return glider_worldline(c, 0)


MPULL = [mirror_wl(w) for w in PULL]
UNIT = [(NW, -3, 24), (SE, 3, -32)]


def run(gl, k, n):
    cells = set(counter(k))
    for w in gl:
        g = glider_at(*w, T0)
        if cells and life.chebyshev_dist(g, cells) < 3:
            return None
        cells |= g
    for _ in range(n - T0):
        cells = step_cells(cells)
    return cells


def check(D, U, ks=KS):
    for k in ks:
        n = 4 * k + 700
        c = run(MPULL + [D] + list(U), k, n)
        if k == 0:
            want = set(counter(0)) if U else set(translate(BLOCK, 7, 8))
        else:
            want = set(counter(k - 1)) | glider_at(*D, n)
        if c != want:
            return False
    return True


if __name__ == '__main__':
    # sanity: the mirrored salvo pulls
    for k in range(0, 6):
        c = run(MPULL, k, 4 * k + 300)
        assert c == set(counter(k - 1)), k
    print('mirrored pull salvo', MPULL, ': counter k -> counter (k - 1) for k = 0..5 (checked)')
    dets = [t for t in range(-40, 160) if check((SW, 9, t), [])]
    print('valid detector taus:', dets[:5], '..', dets[-3:], len(dets), flush=True)
    for tauD in [int(a) for a in sys.argv[1:]] or dets[:1]:
        D = (SW, 9, tauD)
        goods = [s for s in range(0, 300) if check(D, [shift_wl(w, 0, 0, s) for w in UNIT])]
        print('tauD', tauD, 'valid s:', goods, flush=True)
