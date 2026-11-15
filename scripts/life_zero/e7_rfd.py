#!/usr/bin/env python3
"""E7 (R-27): reflector RF_D turning the detector, after it has passed the register (case NZ), from
SW to SE (lane L), so that the NZ gate G_N can stand far south-east, away from the line of the
restore glider R = (NE, -408) of the Z branch.  Filters: RF_D >= 6 from R's line, >= 8 from the
blocks B_-1 .. B_80, >= 15 from REG1; D' (SE) >= 10 from the blocks.  Prints the placements."""
import json
import os
from dcat import *
from net import env_cells, glider_path, reflect, time_at
import e2_gate as E2

FRONT = json.load(open(os.path.join(HERE, 'results', 'e5_front.json')))[0]

if __name__ == '__main__':
    pieces, E = E2.reg_env()
    blocks = set()
    for kk in range(-1, 81):
        blocks |= translate(set(counter(kk)), 148, 240)
    EN, BN = Near(E), Near(blocks)
    D = (tuple(FRONT['D'][0]), FRONT['D'][1], FRONT['D'][2])
    rw = (NE, -408, 0)
    RN = Near(glider_path(rw, int(time_at(rw, (155, 251))) - 2400, int(time_at(rw, (155, 251))) + 600))
    out = []
    for j in range(12, 120):
        x = 155 - j
        L = 2 * x - 397
        for dl in (0, 1):
            r = reflect(D, SE, L + dl)
            if r is None:
                continue
            rf, D2 = r
            e = env_cells(rf)
            dR, dB, dE = RN.dist(e, 10), BN.dist(e, 12), EN.dist(e, 20)
            t0 = int(time_at(D2, (x, 397 - x)))
            p2 = glider_path(D2, t0 + 30, t0 + 1600)
            dD = BN.dist(p2, 12)
            if dR >= 6 and dB >= 8 and dE >= 15 and dD >= 10:
                out.append({'rf': list(rf), 'D2': [list(D2[0]), D2[1], D2[2]], 'j': j, 'dR': dR, 'dB': dB, 'dD': dD})
                print('RF_D', rf, 'j', j, "D'", D2, 'dist to R line', dR, 'blocks', dB, "D' path to blocks", dD, flush=True)
    json.dump(out, open(os.path.join(HERE, 'results', 'e7_rfd.json'), 'w'))
