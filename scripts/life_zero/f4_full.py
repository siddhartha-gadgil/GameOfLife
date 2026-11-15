#!/usr/bin/env python3
"""F4 (R-28): DZ2 with the unconditional glider O supplied (f3_place.json, placement P).

Pieces: REG1 + frozen F_A, RF_a, RF_b, G_N (R-27) + RF_R (R-27) + new: fan-out F_B (in series
upstream of F_A), reflector RF_O, re-timing gate G_O.  One control glider C' (F_B's control):
F_B -> link C (delayed by n) -> frozen front -> REG1 DEC + detector D; F_B's second output -> RF_O
-> control E of G_O -> O.  Z-only inputs still free here (unless the Z branch file is given):
R_in, C_I (delayed by n + 30 m).
Checks, set simulator, unbounded plane, for k in E6_KS (default 0,1,2,3,40):
   k >= 1: cycle ∪ C' ∪ B_k -> cycle ∪ B_(k-1) ∪ N1(+n)       k = 0: -> cycle ∪ B_0 ∪ O(+n)
Usage: f4_full.py [P]   env F4_KS, F4_RDELAY (default 4500), F4_MI (default 500)"""
import json
import os
import sys
from f0_frozen import *
from common import step_cells, life, bbox, lean_window
from net import Net, time_at


def T(w):
    return (tuple(w[0]), w[1], w[2])


def main():
    P = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    pl = json.load(open(os.path.join(HERE, 'results', 'f3_place.json')))[P]
    n = pl['n']
    new = [tuple(p) for p in pl['F_B']] + [tuple(r) for r in pl['rfs']] + [tuple(pl['gate'])]
    pieces = frozen_pieces() + [RF_R] + new
    nt = Net(pieces)
    Cp = T(pl['ctrl'])
    O = shift_wl(T(pl['O']), 0, 0, n)
    n1 = shift_wl(N1, 0, 0, n)
    rdel = int(os.environ.get('F4_RDELAY', '4500'))
    mI = int(os.environ.get('F4_MI', '500'))
    Rin = shift_wl(R_IN0, 0, 0, n + rdel)
    CI = shift_wl(CI0, 0, 0, 30 * mI + n)
    print('new pieces:', new)
    print("control C' %s; O %s; NZ glider %s; free (case Z only): R_in %s, C_I %s" % (Cp, O, n1, Rin, CI), flush=True)
    rfr_c = (RF_R[2], RF_R[3])
    Ts = 30 * ((int(time_at(Cp, (-1100, -1100))) - 400) // 30)
    for k in [int(a) for a in os.environ.get('F4_KS', '0,1,2,3,40').split(',')]:
        sched = {Ts: [Cp]}
        if k == 0:
            sched.setdefault(int(time_at(Rin, rfr_c)) - 240, []).append(Rin)
            sched.setdefault(Ts, []).append(CI)
        t_end = (CI[2] + 3570 + 900) if k == 0 else (n1[2] + 2400)
        N = 30 * ((t_end - Ts) // 30 + 1)
        c = nt.cycle(Ts) | translate(set(counter(k)), 148, 240)
        box = list(bbox(c))
        t = Ts
        for _ in range(N):
            for w in sched.get(t, []):
                g = glider_at(*w, t)
                assert life.chebyshev_dist(g, c) >= 3, (w, t)
                c |= g
            c = step_cells(c)
            t += 1
            if t % 64 == 0:
                bb = bbox(c)
                box = [min(box[0], bb[0]), min(box[1], bb[1]), max(box[2], bb[2]), max(box[3], bb[3])]
        out = O if k == 0 else n1
        want = nt.cycle(t) | translate(set(counter(k - 1 if k else 0)), 148, 240) | glider_at(*out, t)
        print('  k = %2d: evolve %d (cycle(%d) ∪ C\' ∪ B_%d%s) = cycle ∪ B_%d ∪ %s %s: %s; box x %d..%d, y %d..%d' % (
            k, N, Ts, k, ' ∪ R_in ∪ C_I' if k == 0 else '', k - 1 if k else 0, 'O' if k == 0 else 'N1', lean_window(glider_at(*out, t)),
            'checked' if c == want else 'FAILS', box[0], box[2], box[1], box[3]), flush=True)
        if c != want:
            ex = c - want
            print('     extra', len(ex), bbox(ex) if ex else None, 'missing', len(want - c))


if __name__ == '__main__':
    main()
