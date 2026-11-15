#!/usr/bin/env python3
"""F3 (R-28): geometry of the O supply.  For the exact solutions of f2_route.py: place the gate
G_O, the fan-out F_B (family and symmetry of the solution, translated along C's line upstream of
F_A, link = C) and the reflectors of the route Y_B -> E, and keep the placements whose pieces and
flight segments clear everything (REG1, the frozen pieces, RF_R, the blocks, the frozen glider
paths).  Then simulate the best one (Net.react, no block): control C' -> exactly the pull salvo,
N1 and nothing else (D -> G_N; N2 + O annihilate).  Output: results/f3_place.json"""
import gzip
import json
import os
import sys
from f0_frozen import *
from common import bbox
from net import Net, reflect, time_at, compose
from reactions import sym_wl
import f1_req as F1

SEP, CLEAR = 15, 8
FOS = json.load(gzip.open(os.path.join(HERE, '..', 'life_machine', 'results', 'f2_roundtrip.json.gz'), 'rt'))['good']


def fanout(i, sym, u):
    fo = FOS[i]
    outs = [(tuple(o[0]), o[1], o[2]) for o in fo['outs']]
    g1 = sym_wl([w for w in outs if w[0] == SE][0], sym)
    g2 = sym_wl([w for w in outs if w[0] == SW][0], sym)
    ct = sym_wl((SE, 41, 22), sym)
    v = u + g1[1] - C[1]
    s = (C[2] - (g1[2] - 4 * u)) % 30
    outer = ('asm', sym, u, v, s)
    pcs = [compose(outer, p) for p in [('asm', 0, 0, 0, 0), ('asm',) + tuple(fo['asm'])]]
    link, Y, ctrl = shift_wl(g1, u, v, s), shift_wl(g2, u, v, s), shift_wl(ct, u, v, s)
    assert link[:2] == C[:2]
    return pcs, ctrl, link, Y, link[2] - C[2]


def cen_e(e):
    b = bbox(e)
    return ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)


def routes(Y, E):
    """lists of (reflector pieces, glider legs) from Y onto exactly E (up to the 30 n shift)"""
    out = []
    if E[0][0] * Y[0][0] + E[0][1] * Y[0][1] == 0:
        r = reflect(Y, E[0], E[1])
        if r:
            out.append(([r[0]], [Y, r[1]]))
        return out
    mids = [x for x in (SE, SW, NE, NW) if x[0] * Y[0][0] + x[1] * Y[0][1] == 0]
    for m in mids:
        for Lm in range(300, 1300, 25):
            a = reflect(Y, m, Lm)
            if a is None:
                continue
            b = reflect(a[1], E[0], E[1])
            if b is None:
                continue
            out.append(([a[0], b[0]], [Y, a[1], b[1]]))
    return out


if __name__ == '__main__':
    sols = json.load(open(os.path.join(HERE, 'results', 'f2_route.json')))
    sols.sort(key=lambda s: (s['E'][0] == [-1, -1], s['dist']))
    E_all = envelope(frozen_pieces() + [RF_R])
    # every unconditional piece and flight segment must keep away from all block positions
    # (the register is unbounded)
    EN, BN = Near(E_all), Near(blocks(-1, 600))
    PN = Near(F1.glider_paths(with_c=False) | glider_path(N1, int(time_at(N1, (0, 400))), int(time_at(N1, (0, 400))) + 3000))
    good = []
    for sol in sols:
        O = (tuple(sol['O'][0]), sol['O'][1], sol['O'][2])
        gate = tuple(sol['gate'])
        Ew = (tuple(sol['E'][0]), sol['E'][1], sol['E'][2])
        eG = env_cells(gate)
        if EN.dist(eG, SEP) < SEP or BN.dist(eG, SEP) < SEP or PN.dist(eG, SEP) < SEP:
            continue
        GNr = Near(eG)
        cG = cen_e(eG)
        tO = int(time_at(O, cG))
        segO = glider_path(O, tO + 60, tO + 4 * sol['dist'] - 60)
        if EN.dist(segO, 12) < 12 or BN.dist(segO, 12) < 12 or PN.dist(segO, 8) < 8:
            continue
        for (i, sym) in sol['fams']:
            for u in range(-1100, -700, 8):
                pcs, ctrl, link, Y, n = fanout(i, sym, u)
                E = shift_wl(Ew, 0, 0, n)
                eF = env_cells(pcs[0]) | env_cells(pcs[1])
                if EN.dist(eF, SEP) < SEP or GNr.dist(eF, SEP) < SEP:
                    continue
                FN = Near(eF)
                cF = cen_e(eF)
                for rfs, legs in routes(Y, E):
                    if legs[-1] != E:
                        continue
                    er = set()
                    for rp in rfs:
                        er |= env_cells(rp)
                    if EN.dist(er, SEP) < SEP or BN.dist(er, SEP) < SEP or FN.dist(er, SEP) < SEP or GNr.dist(er, SEP) < SEP or PN.dist(er, 10) < 10:
                        continue
                    # flight segments: Y_B from F_B to rf1, legs between rfs, E from last rf to G_O
                    pts = [cF] + [cen_e(env_cells(rp)) for rp in rfs] + [cG]
                    cl = 99
                    FNr = Near(eF)
                    for li, w in enumerate(legs):
                        a, b = pts[li], pts[li + 1]
                        sg = glider_path(w, int(time_at(w, a)) + 40, int(time_at(w, b)) - 40)
                        cl = min(cl, EN.dist(sg, 20), BN.dist(sg, 20), PN.dist(sg, 20))
                        if li > 0:
                            cl = min(cl, FNr.dist(sg, 20))
                        if li < len(legs) - 1:
                            cl = min(cl, GNr.dist(sg, 20))
                        for ri, rp in enumerate(rfs):
                            if ri not in (li - 1, li):
                                cl = min(cl, Near(env_cells(rp)).dist(sg, 20))
                        if cl < CLEAR:
                            break
                    if cl < CLEAR:
                        continue
                    good.append({'O': sol['O'], 'gate': list(gate), 'E': [list(E[0]), E[1], E[2]], 'n': n, 'fam': [i, sym], 'u': u,
                                 'F_B': [list(p) for p in pcs], 'ctrl': [list(ctrl[0]), ctrl[1], ctrl[2]], 'rfs': [list(r) for r in rfs], 'cl': cl})
                    print('OK', good[-1], flush=True)
                    break
                if len(good) >= 3:
                    break
            if len(good) >= 3:
                break
        if len(good) >= 3:
            break
    json.dump(good, open(os.path.join(HERE, 'results', 'f3_place.json'), 'w'))
    print('placements', len(good))
