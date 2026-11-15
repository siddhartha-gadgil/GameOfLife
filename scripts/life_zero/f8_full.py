#!/usr/bin/env python3
"""F8 (R-28): the complete DZ2, one control glider, no free inputs.

Pieces: REG1 + frozen F_A, RF_a, RF_b, G_N (R-27) + O supply (f3_place.json: F_B, RF_O, G_O)
+ Z branch (f9_zbranch.json: F_Z1, F_Z2, 2 + 3 reflectors) + RF_R re-phased to R_in.
Control C' only.  Set simulator, unbounded plane:
   k >= 1: cycle ∪ C' ∪ B_k  ->  cycle ∪ B_(k-1) ∪ N1          (NZ)
   k = 0 : cycle ∪ C' ∪ B_0  ->  cycle ∪ B_0 ∪ Zout            (Z; via R and REG1's INC push)
Usage: F8_KS=0,1,2,3,40 f8_full.py"""
import json
import os
from f0_frozen import *
from common import step_cells, life, bbox, lean_window
from net import Net, time_at


def T(w):
    return (tuple(w[0]), w[1], w[2])


def design():
    pl = json.load(open(os.path.join(HERE, 'results', 'f3_place.json')))[0]
    z = json.load(open(os.path.join(HERE, 'results', 'f9_zbranch.json')))
    n = pl['n']
    rin = T(z['R_in'])
    rfr = ('rf', RF_R[1], RF_R[2], RF_R[3], (RF_R[4] + rin[2] - R_IN0[2]) % 30)
    supply = [tuple(p) for p in pl['F_B']] + [tuple(r) for r in pl['rfs']] + [tuple(pl['gate'])]
    zb = [tuple(p) for p in z['F_Z1']] + [tuple(p) for p in z['F_Z2']] + \
        [tuple(r) for r in z['RF_R_route']] + [tuple(r) for r in z['RF_CI_route']]
    return {'n': n, 'ctrl': T(pl['ctrl']), 'supply': supply, 'zb': zb, 'rfr': rfr, 'zout': T(z['Zout']),
            'n1': shift_wl(N1, 0, 0, n), 'ci': T(z['C_I']), 'rin': rin, 'O': shift_wl(T(pl['O']), 0, 0, n)}


def main():
    d = design()
    pieces = frozen_pieces() + [d['rfr']] + d['supply'] + d['zb']
    nt = Net(pieces)
    print('pieces: REG1 (22) + F_A, RF_a, RF_b, G_N (frozen) + RF_R %s + O supply %s + Z branch %s' % (d['rfr'], d['supply'], d['zb']))
    print("control C' %s; NZ glider %s; Z glider %s; O %s; R_in %s; C_I %s" % (d['ctrl'], d['n1'], d['zout'], d['O'], d['rin'], d['ci']), flush=True)
    Ts = 30 * ((int(time_at(d['ctrl'], (-1100, -1100))) - 400) // 30)
    for k in [int(a) for a in os.environ.get('F8_KS', '0,1,2,3,40').split(',')]:
        t_end = (d['ci'][2] + 3570 + 1200) if k == 0 else (d['n1'][2] + 2400)
        N = 30 * ((t_end - Ts) // 30 + 1)
        c = nt.cycle(Ts) | glider_at(*d['ctrl'], Ts) | translate(set(counter(k)), 148, 240)
        box = list(bbox(c))
        for i in range(N):
            c = step_cells(c)
            if i % 64 == 0:
                bb = bbox(c)
                box = [min(box[0], bb[0]), min(box[1], bb[1]), max(box[2], bb[2]), max(box[3], bb[3])]
        t = Ts + N
        out = d['zout'] if k == 0 else d['n1']
        want = nt.cycle(t) | translate(set(counter(k - 1 if k else 0)), 148, 240) | glider_at(*out, t)
        print("  k = %2d: evolve %d (cycle(%d) ∪ C' ∪ B_%d) = cycle ∪ B_%d ∪ %s %s: %s; box x %d..%d, y %d..%d" % (
            k, N, Ts, k, k - 1 if k else 0, 'Z' if k == 0 else 'NZ', lean_window(glider_at(*out, t)),
            'checked' if c == want else 'FAILS', box[0], box[2], box[1], box[3]), flush=True)
        if c != want:
            ex = c - want
            print('     extra', len(ex), bbox(ex) if ex else None, 'missing', len(want - c))


if __name__ == '__main__':
    main()
