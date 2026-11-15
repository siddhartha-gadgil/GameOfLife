#!/usr/bin/env python3
"""E1 (R-27): the Z restore through the INC salvo, frame of SlidingBlock.lean.
   k = 0: pullSalvo -> counter (-1); detector D = (NE, -10, tauD) -> block (4, 11) (X3);
          R = (SW, 19, tauR) -> counter (-1) (single-glider move (2, -1));
          REG1's push salvo (SE,-10,1034), (SE,1,983), (SE,8,1010) delayed by P -> counter 0.
   k >= 1: pullSalvo + D -> counter (k - 1) + D (D flies on).
Prints the valid ranges of tauR (for tauD) and of the push delay P."""
import sys
from dcat import *
from common import step_cells, life

PULL = [(SE, -5, 0), (SE, 1, -29)]
PUSH = [(SE, -10, 1034), (SE, 1, 983), (SE, 8, 1010)]


def evolve(gl, k, t0, t1, extra=()):
    c = set(counter(k)) | set(extra)
    for w in gl:
        g = glider_at(*w, t0)
        if life.chebyshev_dist(g, c) < 3:
            return None
        c |= g
    for _ in range(t1 - t0):
        c = step_cells(c)
    return c


if __name__ == '__main__':
    SW9 = '--sw9' in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    if SW9:
        taus = [t for t in range(-60, 200) if evolve(PULL + [(SW, 9, t)], 0, -300, 300) == set(translate(BLOCK, 7, 8))
                and all(evolve(PULL + [(SW, 9, t)], k, -300, 400 + 4 * k) == set(counter(k - 1)) | glider_at(SW, 9, t, 400 + 4 * k) for k in (1, 2, 3, 40))]
        print('valid SW9 detector taus:', taus[:3], '..', taus[-3:], len(taus))
    tauD = int(args[0]) if args else (taus[0] if SW9 else 19)
    D = (SW, 9, tauD) if SW9 else (NE, -10, tauD)
    X3 = set(translate(BLOCK, 7, 8)) if SW9 else set(translate(BLOCK, 4, 11))
    RL = (NE, -20) if SW9 else (SW, 19)
    assert evolve(PULL + [D], 0, -300, 300) == X3
    for k in (1, 2, 3, 40):
        n = 400 + 4 * k
        assert evolve(PULL + [D], k, -300, n) == set(counter(k - 1)) | glider_at(*D, n)
    print('D =', D, ': k = 0 -> X3, k = 1, 2, 3, 40 -> counter (k-1) + D: checked')
    rs = [t for t in range(-200, 400) if evolve(PULL + [D, RL + (t,)], 0, -300, 700) == set(counter(-1))]
    print('tauR with k = 0 -> counter (-1):', rs[:3], '..', rs[-3:], len(rs))
    R = RL + (rs[0] + 30,)
    ps = []
    for P in range(-1200, 2000, 10):
        gl = PULL + [D, R] + [shift_wl(w, 0, 0, P) for w in PUSH]
        c = evolve(gl, 0, -300 + min(0, P + 900), 1300 + max(0, P))
        if c == set(counter(0)):
            ps.append(P)
    print('R =', R, '; push delays P (step 10) with k = 0 -> counter 0:', ps[:3], '..', ps[-3:], len(ps))
