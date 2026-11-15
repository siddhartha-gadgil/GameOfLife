#!/usr/bin/env python3
"""E6 (R-27): DZ2 — the decrement-from-zero test at REG1 with the restore through REG1's INC input,
run in full with the set simulator on the unbounded plane (world frame of REG1, R-24).

Pieces: REG1 (22 pieces) + the front of e5_front.py (transposed fan-out F_A = 2 copies of
blockedStream, reflectors RF_a, RF_b) + the NZ gate G_N (e2_gate.py).
Control: one glider C (results/e5_front.json) -> F_A -> REG1's DEC control C0 (delayed n30) and
the detector D (SW, 397, .).  Free inputs (to be supplied, see the report): O (unconditional, killed
by G_N's second glider in case NZ) and, in case Z only, R and C_I (the outputs required from the Z
branch: R moves the detector's block back to B_-1, C_I is REG1's INC control).
   k >= 1: B_k -> B_(k-1); D -> G_N -> N1 (= NZ) + N2; N2 + O annihilate.
   k = 0 : B_0 -> B_-1 -> (D) block (7, 8) -> (R) B_-1 -> (INC push) B_0; O flies on (Z signal).
Usage: e6_full.py GATE_INDEX O_DIR O_LANE O_TAU"""
import json
import os
import sys
from dcat import *
from common import step_cells, life, bbox, lean_window
from net import Net, env_cells, glider_path
import e2_gate as E2

FRONT = json.load(open(os.path.join(HERE, 'results', 'e5_front.json')))[0]
GATES = json.load(open(os.path.join(HERE, 'results', 'e2_gate.json')))


def T(w):
    return (tuple(w[0]), w[1], w[2])


def main():
    gi = int(sys.argv[1])
    O = (NAMED[sys.argv[2]], int(sys.argv[3]), int(sys.argv[4]))
    pieces, E = E2.reg_env()
    front = [tuple(p) for p in FRONT['pieces']]
    GN = tuple(GATES[gi]['piece'])
    outs = sorted([T(w) for w in GATES[gi]['outs']], key=lambda w: w[2])
    n1 = outs[0]
    C = T(FRONT['ctrl'])
    D = T(FRONT['D'])
    n30 = FRONT['n30']
    shift = (148, 240, 1732 + n30)
    locD = D[2] - 2324 - n30
    R = shift_wl((NE, -20, locD + 60), *shift)
    mI = int(os.environ.get('E6_MI', '172'))
    CI = (SE, 314, -2222 + 30 * mI)
    rr = [r for r in json.load(open(os.path.join(HERE, 'results', 'e8_rfr.json'))) if r['j'] == int(os.environ.get('E6_RFR_J', '50'))][0]
    RFR, Rin = tuple(rr['rf']), T(rr['Rin'])
    assert T(rr['R']) == R
    rdel = int(os.environ.get('E6_RDELAY', '0'))          # R and its input delayed (30 m): after the Z decision
    assert rdel % 30 == 0
    R, Rin = shift_wl(R, 0, 0, rdel), shift_wl(Rin, 0, 0, rdel)
    nt = Net(pieces + front + [GN, RFR])
    print('pieces: REG1 + F_A %s + RF_a %s + RF_b %s + G_N %s + RF_R %s' % (front[:2], front[2], front[3], GN, RFR))
    print('control C %s; D %s (local tau %d); O %s; R %s from RF_R, its input %s; C_I %s; NZ glider N1 %s' % (C, D, locD, O, R, Rin, CI, n1))
    Ts = 30 * (FRONT['Ts'] // 30)
    lead = lambda w, pt: int(time_at(w, pt)) - 240
    reg = (155, 251)
    for k in [int(a) for a in os.environ.get('E6_KS', '0,1,2,3,40').split(',')]:
        sched = {Ts: [C]}
        sched.setdefault(lead(O, sorted(glider_at(*n1, int(time_at(n1, (100, 400)))))[0]), []).append(O)
        if k == 0:
            sched.setdefault(lead(Rin, (RFR[2], RFR[3])), []).append(Rin)
            sched.setdefault(Ts, []).append(CI)
        t_end = (CI[2] + 3570 + 900) if k == 0 else (D[2] + 2600)
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
        print('  k = %2d: evolve %d (cycle(%d) ∪ C ∪ B_%d ∪ inputs) = cycle ∪ B_%d ∪ %s %s: %s; box x %d..%d, y %d..%d' % (
            k, N, Ts, k, k - 1 if k else 0, 'O (Z)' if k == 0 else 'N1 (NZ)', lean_window(glider_at(*out, t)),
            'checked' if c == want else 'FAILS', box[0], box[2], box[1], box[3]), flush=True)
        if c != want:
            extra = c - want
            print('     extra cells', len(extra), bbox(extra) if extra else None, 'missing', len(want - c))


if __name__ == '__main__':
    main()
