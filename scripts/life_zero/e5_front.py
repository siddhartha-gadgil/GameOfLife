#!/usr/bin/env python3
"""E5 (R-27): front supply of the detector, second version.  The round-trip fan-out F_A (fan-out
FOI of scripts/life_machine/results/f2_roundtrip.json.gz) is used in its TRANSPOSED image (sym 6,
which fixes the direction SE): its link glider is REG1's DEC control C0 = (SE, 41, 22 + n30), its
other output Y flies NE above REG1; RF_a turns Y to SE on lane L1 (right of REG1), RF_b turns that
onto the detector line (SW, 397) north-east of the register.  The route of fixed type has a fixed
arrival time (taxicab invariant); every fan-out gives the local detector time loc (>= 61 needed,
e1_core.py --sw9; later is fine).
Usage: e5_front.py [--sim]   -> results/e5_front.json"""
import gzip
import json
import os
import sys
from dcat import *
from common import bbox, life
from net import Net, env_cells, glider_path, move_wl, reflect, time_at, compose
from reactions import sym_wl
import e2_gate as E2

FOI = int(os.environ.get('E5_FO', '0'))
_FO = json.load(gzip.open(os.path.join(HERE, '..', 'life_machine', 'results', 'f2_roundtrip.json.gz'), 'rt'))['good'][FOI]
INNER = [('asm', 0, 0, 0, 0), ('asm',) + tuple(_FO['asm'])]
CF = (SE, 41, 22)
G1 = sym_wl([(tuple(o[0]), o[1], o[2]) for o in _FO['outs'] if tuple(o[0]) == SE][0], 6)
G2 = sym_wl([(tuple(o[0]), o[1], o[2]) for o in _FO['outs'] if tuple(o[0]) == SW][0], 6)
CT = sym_wl(CF, 6)
DLANE, DOFF, DLO = 397, 2324, 61
SEP, CLEAR = 15, 10
REGPT = (155, 251)


def fanout(u):
    v = u + G1[1] - 41
    s = (22 - (G1[2] - 4 * u)) % 30
    outer = ('asm', 6, u, v, s)
    pcs = [compose(outer, p) for p in INNER]
    link, Y, ctrl = shift_wl(G1, u, v, s), shift_wl(G2, u, v, s), shift_wl(CT, u, v, s)
    assert link[:2] == (SE, 41) and (link[2] - 22) % 30 == 0
    return pcs, ctrl, link, Y


def cen(e):
    b = bbox(e)
    return ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)


def candidates(E, blocks, urange, lanes):
    EN, BN = Near(E), Near(blocks)
    out = []
    for u in urange:
        pcs, ctrl, link, Y = fanout(u)
        n30 = link[2] - 22
        eF = env_cells(pcs[0]) | env_cells(pcs[1])
        if EN.dist(eF, SEP) < SEP:
            continue
        FN = Near(eF)
        for L1 in lanes:
            ra = reflect(Y, SE, L1)
            if ra is None:
                continue
            rb = reflect(ra[1], SW, DLANE)
            if rb is None:
                continue
            (rfA, w1), (rfB, Dw) = ra, rb
            loc = Dw[2] - DOFF - n30
            if loc < DLO:
                continue
            eA, eB = env_cells(rfA), env_cells(rfB)
            if min(EN.dist(eA, SEP), EN.dist(eB, SEP), FN.dist(eA, SEP), FN.dist(eB, SEP), BN.dist(eB, SEP)) < SEP:
                continue
            cA, cB, cF = cen(eA), cen(eB), cen(eF)
            sY = glider_path(Y, int(time_at(Y, cF)) + 100, int(time_at(Y, cA)) - 30)
            s1 = glider_path(w1, int(time_at(w1, cA)) + 30, int(time_at(w1, cB)) - 30)
            sD = glider_path(Dw, int(time_at(Dw, cB)) + 30, int(time_at(Dw, REGPT)) - 40)
            sC = glider_path(link, int(time_at(link, cF)) + 100, int(time_at(link, (-358, -399))))
            AB = Near(eA | eB)
            cl = min(EN.dist(sY, 30), Near(eB).dist(sY, 30), EN.dist(s1, 30), FN.dist(s1, 30), EN.dist(sD, 30), FN.dist(sD, 30),
                     Near(eA).dist(sD, 30), AB.dist(sC, 30))
            if cl < CLEAR:
                continue
            out.append({'u': u, 'L1': L1, 'n30': n30, 'loc': loc, 'cl': cl, 'pieces': pcs + [rfA, rfB],
                        'ctrl': ctrl, 'Y': Y, 'w1': w1, 'D': Dw})
    return out


if __name__ == '__main__':
    pieces, E = E2.reg_env()
    blocks = set()
    for kk in range(-1, 81):
        blocks |= translate(set(counter(kk)), 148, 240)
    cs = candidates(E, blocks, range(-560, -360, 4), range(530, 760, 1))
    cs.sort(key=lambda c: (-min(c['cl'], 20), c['loc'], c['u']))
    print('fan-out %d %s: candidates %d' % (FOI, INNER[1], len(cs)))
    for c in cs[:8]:
        print('  u %d L1 %d n30 %d local tauD %d clearance %d pieces %s D %s control %s' % (
            c['u'], c['L1'], c['n30'], c['loc'], c['cl'], c['pieces'], c['D'], c['ctrl']), flush=True)
    good = []
    if '--sim' in sys.argv:
        for c in cs[:4]:
            nt = Net(pieces + c['pieces'])
            st, outs, Ts, Te = nt.react([c['ctrl']], limit=8000, t_hint=0)
            want = sorted([(SE, -97, 1140 + c['n30']), (SE, -91, 1111 + c['n30']), c['D']])
            print('  simulate u %d L1 %d: %s %s Ts %s Te %s' % (c['u'], c['L1'], st, 'outputs = pull salvo + D' if outs == want else outs, Ts, Te), flush=True)
            if st == 'ok' and outs == want:
                c['Ts'], c['Te'] = Ts, Te
                good.append(c)
                break
    json.dump(good or cs[:8], open(os.path.join(HERE, 'results', 'e5_front.json'), 'w'))
