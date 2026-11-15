#!/usr/bin/env python3
"""E4 (R-27): front supply of the detector.  A round-trip fan-out F_A (the fan-out F1 of R-22,
scripts/life_machine/c1_continue.py: control (SE, 41, 22) -> link (SE, -13, 214) + SW glider
(SW, 75, 891), pieces ('asm', 0, 0, 0, 0) and ('asm', 0, 35, 62, 25)) is put upstream of REG1 on
the line of REG1's DEC control C0 = (SE, 41, 22), so that its link glider IS C0 (delayed 30 n).
Its SW glider Y is turned by two reflectors RF_a (SW -> SE, lane L1) and RF_b (SE -> NE, lane
-398) into the detector D = (NE, -398, tau) with the local detector time tau - 1140 - 30 n in
[19, 159] (e1_core.py / d8_core.py).
Filters: piece envelopes >= SEP from the REG1 envelope and from each other, flight segments
>= CLEAR from the pieces they do not use, D's segment >= CLEAR from REG1 and from the blocks.
Prints the candidates; with --sim simulates the best few (REG1 + F_A + RF_a + RF_b, control C:
outputs exactly the pull salvo (delayed 30 n) and D).  Output: results/e4_front.json"""
import json
import os
import sys
from dcat import *
from common import bbox, life
from net import (Net, env_cells, glider_path, set_dist, move_piece, move_wl, reflect, time_at,
                 piece_cells)
import e2_gate as E2

import gzip
_FO = json.load(gzip.open(os.path.join(HERE, '..', 'life_machine', 'results', 'f2_roundtrip.json.gz'), 'rt'))['good']
FOI = int(os.environ.get('E4_FO', '31'))      # fan-out 31 of f2_roundtrip: the detector arrives in the window
F1 = ('asm',) + tuple(_FO[FOI]['asm'])
CF = (SE, 41, 22)
G1 = [(tuple(o[0]), o[1], o[2]) for o in _FO[FOI]['outs'] if tuple(o[0]) == SE][0]
G2 = [(tuple(o[0]), o[1], o[2]) for o in _FO[FOI]['outs'] if tuple(o[0]) == SW][0]
SEP, CLEAR = 15, 10
REGPT = (155, 251)
# detector: SW9 (world (SW, 397, local tau + 2324), local tau in [61, 199]; e1_core.py --sw9)
DDIR, DLANE, DOFF, DLO, DHI = SW, 397, 2324, 61, 199


def seg(w, a, b):
    return glider_path(w, int(a), int(b))


def candidates(E, blocks, urange, lanes):
    global EN, BN
    EN, BN = Near(E), Near(blocks)
    out = []
    for u in urange:
        v = u + G1[1] - 41
        s = (22 - G1[2] + 4 * u) % 30
        SF, KF = ('asm', 0, u, v, s), move_piece(F1, u, v, s)
        link = move_wl(G1, u, v, s)
        assert link[:2] == (SE, 41) and (link[2] - 22) % 30 == 0
        n30 = link[2] - 22
        eS, eK = env_cells(SF), env_cells(KF)
        if EN.dist(eS | eK, SEP) < SEP:
            continue
        ctrl, Y = move_wl(CF, u, v, s), move_wl(G2, u, v, s)
        for L1 in lanes:
            ra = reflect(Y, SE, L1)
            if ra is None:
                continue
            rfA, w1 = ra
            rb = reflect(w1, DDIR, DLANE)
            if rb is None:
                continue
            rfB, Dw = rb
            loc = Dw[2] - DOFF - n30
            if not (DLO <= loc <= DHI):
                continue
            eA, eB = env_cells(rfA), env_cells(rfB)
            if min(EN.dist(eA, SEP), EN.dist(eB, SEP)) < SEP or Near(eS | eK).dist(eA, SEP) < SEP or Near(eS | eK | eA).dist(eB, SEP) < SEP:
                continue
            if BN.dist(eB, SEP) < SEP:
                continue
            # flight segments
            bA, bB = bbox(eA), bbox(eB)
            cA = ((bA[0] + bA[2]) / 2, (bA[1] + bA[3]) / 2)
            cB = ((bB[0] + bB[2]) / 2, (bB[1] + bB[3]) / 2)
            tY0 = time_at(Y, ((bbox(eK)[0] + bbox(eK)[2]) / 2, (bbox(eK)[1] + bbox(eK)[3]) / 2)) + 80
            sY = seg(Y, tY0, time_at(Y, cA) - 30)
            s1 = seg(w1, time_at(w1, cA) + 30, time_at(w1, cB) - 30)
            sD = seg(Dw, time_at(Dw, cB) + 30, time_at(Dw, REGPT) - 40)
            cl = min(EN.dist(sY, 30), Near(eA | eB).dist(sY, 30), EN.dist(s1, 30), Near(eS | eK).dist(s1, 30), EN.dist(sD, 30), Near(eS | eK | eA).dist(sD, 30))
            if cl < CLEAR:
                continue
            out.append({'u': u, 'L1': L1, 'n30': n30, 'loc': loc, 'cl': cl, 'pieces': [SF, KF, rfA, rfB],
                        'ctrl': ctrl, 'Y': Y, 'w1': w1, 'D': Dw})
    return out


if __name__ == '__main__':
    pieces, E = E2.reg_env()
    blocks = set()
    for kk in range(-1, 81):
        blocks |= translate(set(counter(kk)), 148, 240)
    cs = candidates(E, blocks, range(-700, -380, 4), range(-7, 314, 1))
    cs.sort(key=lambda c: (-c['cl'], c['u']))
    print('candidates:', len(cs))
    for c in cs[:10]:
        print('  u %d L1 %d n30 %d local tauD %d clearance %d pieces %s D %s' % (c['u'], c['L1'], c['n30'], c['loc'], c['cl'], c['pieces'], c['D']), flush=True)
    good = []
    if '--sim' in sys.argv:
        for c in cs[:6]:
            nt = Net(pieces + c['pieces'])
            st, outs, Ts, Te = nt.react([c['ctrl']], limit=6000, t_hint=0)
            want = sorted([(SE, -97, 1140 + c['n30']), (SE, -91, 1111 + c['n30']), c['D']])
            print('  simulate u %d L1 %d: %s %s' % (c['u'], c['L1'], st, 'outputs = pull salvo + D' if outs == want else outs), flush=True)
            if st == 'ok' and outs == want:
                c['Ts'], c['Te'] = Ts, Te
                good.append(c)
                break
    json.dump(good or cs[:10], open(os.path.join(HERE, 'results', 'e4_front.json'), 'w'))
