#!/usr/bin/env python3
"""G16 (R-29): the flight traces of DZ2' (all cells occupied by moving gliders / reactions outside
the pieces' envelopes), k = 0 (Z path) and k = 1 (NZ path), sampled every 2 generations; used as
an extra clearance filter for new pieces.  Cached in $G16_CACHE (default: ./.cache)."""
import os
import pickle
from gcommon import *
from net import env_cells
import g11_inc_check as G11

CACHE = os.environ.get('G16_CACHE', os.path.join(HERE, '.cache'))


def trace():
    f = os.path.join(CACHE, 'g16_trace.pkl')
    if os.path.exists(f):
        return pickle.load(open(f, 'rb'))
    pieces, GI, RFC3, CI = G11.design(0)
    _, D = dz2()
    envs = set()
    for p in pieces:
        envs |= env_cells(p)
    tr = set()
    for k, N in ((0, 27540), (1, 11490)):
        c = state(pieces, [D['ctrl']], -300, block(k))
        S = Sim(c, (-1700, -1800, 1200, 1400), 400)
        for t in range(0, N, 2):
            try:
                S.run(2)
            except RuntimeError:
                S = Sim({x for x in S.cells() if -1650 < x[0] < 1150 and -1750 < x[1] < 1350}, (-1700, -1800, 1200, 1400), 400)
                continue
            cells = S.cells()
            tr |= {x for x in cells if x not in envs and -1700 < x[0] < 1200 and -1800 < x[1] < 1400}
    tr -= blocks(-1, 1)
    os.makedirs(CACHE, exist_ok=True)
    pickle.dump(tr, open(f, 'wb'))
    return tr


if __name__ == '__main__':
    tr = trace()
    print('trace cells:', len(tr), bbox(tr))
