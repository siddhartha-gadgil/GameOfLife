#!/usr/bin/env python3
"""E3 (R-27): decision logic DZ2 at REG1 with the restore through REG1's INC input.

World frame of REG1 (R-24).  Pieces: the 22 pieces of REG1 + the NZ gate G_N (results/e2_gate.json).
Unconditional inputs (one per DEC use): C0 = (SE, 41, 22) (REG1's DEC control), the detector
D = (NE, -398, 1159) (= local (NE, -10, 19)), and O (searched here: crosses the lane of G_N's
outputs; N2 + O annihilate, N1 passes 30 generations before).
   k >= 1: pull k -> k-1; D passes the register, enters G_N, which releases N1 (= NZ, flies away)
           and N2 (kills O).
   k = 0 : pull 0 -> -1; D -> block (4, 11) (local); G_N idle; O flies on (= the Z signal).
           The Z branch (a fan-out of O, plan only) must deliver R = (SW, 407, .) (local
           (SW, 19, 117 + 30 m): block -> counter (-1)) and REG1's INC control C_I = (SE, 314,
           -2222 + 30 m); here R and C_I are added as free gliders in the k = 0 run and the push
           brings the block back to B_0.
Usage: e3_dz2.py search    (O)   |   e3_dz2.py check I O_LANE O_TAU   (full runs, set simulator)"""
import json
import os
import sys
from dcat import *
from common import step_cells, life, bbox, lean_window
from net import Net, env_cells, glider_path, set_dist
from recipes import settle
import e2_gate as E2

C0 = (SE, 41, 22)
DW = (NE, -398, 1159)
SH = (148, 240, 1732)
R_LOC = (SW, 19, 117)
MI = 180                                     # C_I delayed by 30 MI against its natural time
C_I = (SE, 314, -2222 + 30 * MI)


def gate(i):
    g = json.load(open(os.path.join(HERE, 'results', 'e2_gate.json')))[i]
    return tuple(g['piece']), [(tuple(w[0]), w[1], w[2]) for w in g['outs']]


def search_O(GN, outs, E, blocks):
    n1, n2 = sorted(outs, key=lambda w: w[2])
    d = n2[0]
    perp = [x for x in (SE, SW, NE, NW) if x[0] * d[0] + x[1] * d[1] == 0]
    genv = env_cells(('asm',) + GN[1:]) if GN[0] == 'asm' else env_cells(GN)
    res = []
    b = bbox(genv)
    cen = ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)
    t_g = time_at(n2, cen)
    for j in range(30, 160, 2):                    # crossing point j generations downstream of the gate
        t = int(t_g) + 4 * j
        pt = sorted(glider_at(*n2, t))[0]
        for od in perp:
            lane = od[1] * pt[0] - od[0] * pt[1]
            for dl in range(-3, 4):
                for tau in range(-4000, 6000):
                    O = (od, lane + dl, tau)
                    if abs(time_at(O, pt) - t) > 6:
                        continue
                    st, tt, rest, gl = run_free([n1, n2, O], t0=t - 200, max_gen=600)
                    if not (st == 'settled' and not rest and gl == [n1]):
                        continue
                    po = glider_path(O, t - 3000, t + 3000)
                    dE, dG, dB = set_dist(po, E), set_dist(po, genv), set_dist(po, blocks)
                    if dE >= 20 and dG >= 10 and dB >= 15:
                        res.append((O, j, dE, dG, dB))
        if len(res) >= 5:
            break
    return res


def run(nt, gl_sched, k, Ts, N, extra=()):
    c = nt.cycle(Ts) | set(extra) | translate(set(counter(k)), 148, 240)
    box = list(bbox(c))
    t = Ts
    sched = {}
    for (w, ti) in gl_sched:
        sched.setdefault(max(ti, Ts), []).append(w)
    for _ in range(N):
        for w in sched.get(t, []):
            g = glider_at(*w, t)
            assert life.chebyshev_dist(g, c) >= 3, (w, t)
            c |= g
        c = step_cells(c)
        t += 1
        bb = bbox(c)
        box = [min(box[0], bb[0]), min(box[1], bb[1]), max(box[2], bb[2]), max(box[3], bb[3])]
    return c, box


if __name__ == '__main__':
    pieces, E = E2.reg_env()
    blocks = set()
    for kk in range(-1, 81):
        blocks |= translate(set(counter(kk)), 148, 240)
    i = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    GN, outs = gate(i)
    print('G_N', GN, 'outputs', outs)
    if sys.argv[1] == 'search':
        for r in search_O(GN, outs, E, blocks):
            print('  O', r, flush=True)
    else:
        O = (NAMED[sys.argv[3]], int(sys.argv[4]), int(sys.argv[5]))
        nt = Net(pieces + [GN])
        Rw = shift_wl(R_LOC, *SH)
        n1 = sorted(outs, key=lambda w: w[2])[0]
        lead = lambda w, pt=(155, 251): int(time_at(w, pt)) - 250
        Ts = -1410
        for k in (0, 1, 2, 3, 40):
            sched = [(C0, Ts), (DW, lead(DW)), (O, lead(O, sorted(glider_at(*n1, int(time_at(n1, (155, 251)))))[0]) - 200)]
            if k == 0:
                sched += [(Rw, lead(Rw)), (C_I, Ts)]
            Te = 30 * ((C_I[2] + 3570 + 600 + 4 * k - Ts) // 30 + 1) + Ts if k == 0 else 30 * ((2600 + 4 * k - Ts) // 30 + 1) + Ts
            N = Te - Ts
            c, box = run(nt, sched, k, Ts, N)
            out = O if k == 0 else n1
            want = nt.cycle(Te) | translate(set(counter(k - 1 if k else 0)), 148, 240) | glider_at(*out, Te)
            print('  k = %2d: evolve %d from world time %d: R ∪ G_N ∪ B_%d ∪ inputs -> R ∪ G_N ∪ B_%d ∪ %s %s: %s; box x %d..%d, y %d..%d' % (
                k, N, Ts, k, k - 1 if k else 0, 'O (Z signal)' if k == 0 else 'N1 (NZ)', lean_window(glider_at(*out, Te)),
                'checked' if c == want else 'FAILS', box[0], box[2], box[1], box[3]), flush=True)
