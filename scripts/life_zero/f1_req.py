#!/usr/bin/env python3
"""F1 (R-28): all world lines of the unconditional glider O that work with the frozen NZ gate G_N:
in case NZ, N2 + O annihilate and N1 passes (two-glider simulation), and O's whole line
(t_cross +- 3000) keeps >= 15 from REG1 and the frozen pieces and RF_R, >= 12 from the blocks
B_-1..B_80, >= 6 from the paths of C, C0, Y_A, W1, D, R, R_in.  Crossings 20..260 cells beyond
G_N, both perpendicular directions.  Output: results/f1_req.json"""
import json
import os
from multiprocessing import Pool
from f0_frozen import *
from common import bbox
from net import time_at
ODIRS = tuple({'SW': SW, 'NE': NE}[x] for x in os.environ.get('F1_DIRS', 'NE').split(','))


def cen(p):
    b = bbox(env_cells(p))
    return ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)


def seg(w, a, b, pad=0):
    ta, tb = int(time_at(w, a)), int(time_at(w, b))
    return glider_path(w, min(ta, tb) - pad, max(ta, tb) + pad)


def glider_paths(with_c=True):
    """the real flight segments of the frozen design's gliders"""
    fa, ra, rb, gn, rr, reg = cen(F_A[0]), cen(RF_A), cen(RF_B), cen(G_N), cen(RF_R), (155, 251)
    p = set()
    if with_c:
        p |= glider_path(C, int(time_at(C, fa)) - 4000, int(time_at(C, fa)))
    p |= seg(C0, fa, (-358, -399))
    p |= seg(Y_A, fa, ra)
    p |= seg(W1, ra, rb)
    p |= seg(D, rb, gn)
    p |= seg(R0, rr, reg)
    p |= glider_path(R_IN0, int(time_at(R_IN0, rr)) - 4000, int(time_at(R_IN0, rr)))
    return p


def job(j):
    E = envelope(frozen_pieces() + [RF_R])
    EN, BN = Near(E), Near(blocks())
    RAY = Near(blocks(-1, 600))
    paths = glider_paths()
    PN = Near(paths)
    solid = env_cells(G_N)
    b = bbox(solid)
    t_g = time_at(N2, ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2))
    t = int(t_g) + 4 * j
    pt = min(glider_at(*N2, t))
    out = []
    for od in ODIRS:
        for dl in range(-3, 4):
            lane = od[1] * pt[0] - od[0] * pt[1] + dl
            base = time_at((od, lane, 0), pt)
            for dt in range(-8, 9):
                O = (od, lane, int(t - base) + dt)
                st, tt, rest, gl = run_free([N1, N2, O], t0=t - 200, max_gen=600)
                if not (st == 'settled' and not rest and gl == [N1]):
                    continue
                po = glider_path(O, t - 3000, t + 3000)
                pre = glider_path(O, t - 3000, t)
                # the register is unbounded: before the crossing (both cases) O must keep away from
                # every block position B_k, k <= 600; after it (case Z only, k = 0) from B_-1..B_80
                dd = (EN.dist(po, 15), min(RAY.dist(pre, 12), BN.dist(po, 12)), PN.dist(po, 6))
                if dd[0] >= 15 and dd[1] >= 12 and dd[2] >= 6:
                    out.append(([list(O[0]), O[1], O[2]], j, t, dd))
    return out


if __name__ == '__main__':
    res = []
    with Pool(8) as p:
        for r in p.imap_unordered(job, range(20, 261)):
            res += r
    res.sort(key=lambda r: r[1])
    print('O candidates:', len(res))
    for r in res[:10]:
        print('  ', r)
    json.dump(res, open(os.path.join(HERE, 'results', 'f1_req.json'), 'w'))
