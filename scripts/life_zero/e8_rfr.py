#!/usr/bin/env python3
"""E8 (R-27): the reflector RF_R that emits the Z-restore glider R (local (NE, -20, tauR): block
(7, 8) -> B_-1) close to the register, from an input flying SE (from the free region west of REG1), so that
the NZ gate G_N on the detector's onward line can stand beyond R's short segment.
Filters: RF_R >= 8 from the blocks B_-1 .. B_80, >= 15 from REG1, >= 6 from the detector's line,
R's segment and the input path >= 8 from the blocks (except R's target).  Output: results/e8_rfr.json"""
import json
import os
from dcat import *
from net import env_cells, glider_path, reflect_to, time_at
import e2_gate as E2

FRONT = json.load(open(os.path.join(HERE, 'results', 'e5_front.json')))[0]

if __name__ == '__main__':
    pieces, E = E2.reg_env()
    blocks = set()
    for kk in range(1, 81):
        blocks |= translate(set(counter(kk)), 148, 240)
    EN, BN = Near(E), Near(blocks)
    D = (tuple(FRONT['D'][0]), FRONT['D'][1], FRONT['D'][2])
    n30 = FRONT['n30']
    locD = D[2] - 2324 - n30
    R = shift_wl((NE, -20, locD + 60), 148, 240, 1732 + n30)
    tD = int(time_at(D, (155, 251)))
    DN = Near(glider_path(D, tD - 600, tD + 1200))
    out = []
    for j in range(-260, 60, 2):
        rf, rin = reflect_to(R, SE, j)
        e = env_cells(rf)
        dB, dE, dD = BN.dist(e, 12), EN.dist(e, 20), DN.dist(e, 10)
        tr = int(time_at(R, (j, 408 - j)))
        segR = glider_path(R, tr + 20, int(time_at(R, (155, 253))) - 30)
        segI = glider_path(rin, tr - 2000, tr - 20)
        dI = min(BN.dist(segI, 12), EN.dist(segI, 20))
        if dB >= 8 and dE >= 15 and dD >= 5 and dI >= 10:
            out.append({'rf': list(rf), 'R': [list(R[0]), R[1], R[2]], 'Rin': [list(rin[0]), rin[1], rin[2]], 'j': j,
                        'dB': dB, 'dD': dD, 'dI': dI})
            print('RF_R', rf, 'j', j, 'R', R, 'input', rin, 'dist blocks', dB, 'D line', dD, 'input path', dI, flush=True)
    json.dump(out, open(os.path.join(HERE, 'results', 'e8_rfr.json'), 'w'))
