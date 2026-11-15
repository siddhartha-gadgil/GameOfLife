#!/usr/bin/env python3
"""F10 (R-28): separations of the complete DZ2 (f8_full.py design): for every new piece the minimum
Chebyshev distance of its envelope (all cells over a cycle) to every other piece's envelope, and
the whole envelope box."""
from f8_full import *
from net import env_cells
from common import bbox

if __name__ == '__main__':
    d = design()
    named = [('REG1+frozen', None)]
    new = [('RF_R', d['rfr']), ('F_B.S', d['supply'][0]), ('F_B.K', d['supply'][1]), ('RF_O', d['supply'][2]), ('G_O', d['supply'][3])]
    zb = d['zb']
    new += [('F_Z1.S', zb[0]), ('F_Z1.K', zb[1]), ('F_Z2.S', zb[2]), ('F_Z2.K', zb[3]), ('RF_R1', zb[4]), ('RF_R2', zb[5]),
            ('RF_C1', zb[6]), ('RF_C2', zb[7]), ('RF_C3', zb[8])]
    FZ = envelope(frozen_pieces())
    envs = {nm: env_cells(p) for nm, p in new}
    allc = set(FZ)
    for e in envs.values():
        allc |= e
    print('whole envelope box: x %d..%d, y %d..%d' % (lambda b: (b[0], b[2], b[1], b[3]))(bbox(allc)))
    FN = Near(FZ)
    worst = 99
    for nm, e in envs.items():
        dd = [('frozen', FN.dist(e, 60))]
        for nm2, e2 in envs.items():
            if nm2 != nm and not (nm.split('.')[0] == nm2.split('.')[0] and '.' in nm):
                dd.append((nm2, Near(e2).dist(e, 60)))
        m = min(dd, key=lambda x: x[1])
        worst = min(worst, m[1])
        print('  %-7s %-28s nearest: %s at %d' % (nm, dict(new)[nm], m[0], m[1]))
    print('minimum separation of a new piece from any other piece: %d (pairs within one fan-out excluded)' % worst)
