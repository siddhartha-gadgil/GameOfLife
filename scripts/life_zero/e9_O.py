#!/usr/bin/env python3
"""E9 (R-27): the unconditional glider O of DZ2.  It crosses the lane of G_N's two outputs: in case
NZ the second output N2 and O annihilate (N1 passes the crossing 30 generations earlier); in case Z
O flies on (the Z signal).  O's whole line must stay >= 20 from REG1, >= 10 from G_N, the front
pieces, RF_R, >= 15 from the register blocks, >= 8 from the paths of D, R and R's input.
Usage: e9_O.py GATE_INDEX RFR_J   -> prints candidates (results/e9_O.json)"""
import json
import os
import sys
from dcat import *
from common import bbox
from net import env_cells, glider_path, time_at
import e2_gate as E2

FRONT = json.load(open(os.path.join(HERE, 'results', 'e5_front.json')))[0]


def T(w):
    return (tuple(w[0]), w[1], w[2])


if __name__ == '__main__':
    gi, rj = int(sys.argv[1]), int(sys.argv[2])
    g = json.load(open(os.path.join(HERE, 'results', 'e2_gate.json')))[gi]
    GN = tuple(g['piece'])
    n1, n2 = sorted([T(w) for w in g['outs']], key=lambda w: w[2])
    rr = [r for r in json.load(open(os.path.join(HERE, 'results', 'e8_rfr.json'))) if r['j'] == rj][0]
    rf, R, Rin = tuple(rr['rf']), T(rr['R']), T(rr['Rin'])
    D = T(FRONT['D'])
    pieces, E = E2.reg_env()
    blocks = set()
    for kk in range(-1, 81):
        blocks |= translate(set(counter(kk)), 148, 240)
    solid = env_cells(('asm',) + GN[1:]) if GN[0] == 'asm' else env_cells(GN)
    GNN = Near(solid)
    other = set()
    for p in FRONT['pieces']:
        other |= env_cells(tuple(p))
    other |= env_cells(rf)
    ON = Near(other)
    tD = int(time_at(D, (155, 251)))
    tr = int(time_at(R, (rf[2], rf[3])))
    paths = Near(glider_path(D, tD - 3000, tD + 400) | glider_path(R, tr, tr + 600) | glider_path(Rin, tr - 2400, tr))
    EN, BN = Near(E), Near(blocks)
    b = bbox(solid)
    cen = ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)
    t_g = time_at(n2, cen)
    d = n2[0]
    perp = [x for x in (SE, SW, NE, NW) if x[0] * d[0] + x[1] * d[1] == 0]
    res = []
    for j in range(25, 200, 3):
        t = int(t_g) + 4 * j
        pt = min(glider_at(*n2, t))
        for od in perp:
            lane = od[1] * pt[0] - od[0] * pt[1]
            for dl in range(-3, 4):
                for tau in range(t - 4 * abs(pt[0]) - 1600, t + 4 * abs(pt[0]) + 1600):
                    O = (od, lane + dl, tau)
                    if abs(time_at(O, pt) - t) > 6:
                        continue
                    st, tt, rest, gl = run_free([n1, n2, O], t0=t - 200, max_gen=600)
                    if not (st == 'settled' and not rest and gl == [n1]):
                        continue
                    po = glider_path(O, t - 2500, t + 2500)
                    dd = (EN.dist(po, 20), GNN.dist(po, 10), ON.dist(po, 10), BN.dist(po, 15), paths.dist(po, 8))
                    if dd[0] >= 20 and dd[1] >= 10 and dd[2] >= 10 and dd[3] >= 15 and dd[4] >= 8:
                        res.append({'O': [list(O[0]), O[1], O[2]], 'j': j})
                        print('  O', O, 'crossing j', j, 'distances', dd, flush=True)
        if len(res) >= 4:
            break
    json.dump(res, open(os.path.join(HERE, 'results', 'e9_O.json'), 'w'))
