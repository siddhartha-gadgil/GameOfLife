#!/usr/bin/env python3
"""D17 (R-26): the decision logic DZ1 (d16_logic.py) placed at the register of REG1 (R-24,
scripts/life_machine/results/register.json; register block B_k = translate (148, 240) (counter k),
DEC control C0 = (SE, 41, 22); the frame of counter 0 at time t is the world at time t + 1732).

Checks with the set simulator on the unbounded plane, for k = 0, 1, 2, 3, 40:
   cycle(Ts) + C0 + DZ1 inputs + eater + B_k  --N-->  cycle(Ts + N) + eater + B_(k-1) + NZ      (k >= 1)
                                               --N-->  cycle(Ts + N) + eater + B_0 + Z            (k = 0)
and the clearances of all DZ1 glider paths (whole lines, both directions) to the envelope of REG1.
Usage: d17_reg1.py [O_LANE O_TAU]"""
import json
import os
import sys
from dcat import *
from common import step_cells, life, bbox, lean_window, cells_of_window
from net import Net, env_cells, glider_path, set_dist, piece_cells
import d16_logic as L

REGF = os.path.join(HERE, '..', 'life_machine', 'results', 'register.json')
SHIFT = (148, 240, 1732)
C0 = (SE, 41, 22)
LEAD = {SE: 200, NE: 160, SW: 160, NW: 160}
EATER_L = frozenset(cells_of_window(-12, 1, [3, 2, 10, 12]))


def W(w):
    return shift_wl(w, *SHIFT)


def main():
    O = (SE, int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (SE, 60, 73)
    d = json.load(open(REGF))
    pieces = [tuple(p) for p in d['pieces']]
    nt = Net(pieces)
    env = set()
    for p in pieces:
        env |= env_cells(p)
    eater = set(translate(EATER_L, 148, 240))
    names = ['D', 'A', 'B', 'S', 'V', 'O']
    loc = [L.D, L.A, L.B, L.S, L.V, O]
    wl = [W(w) for w in loc]
    print('DZ1 in the world frame of REG1:')
    for nm, a, b in zip(names, loc, wl):
        print('  %s  local %s  world %s' % (nm, (DIRNAME[a[0]],) + a[1:], (DIRNAME[b[0]],) + b[1:]))
    print('  eater E local %s, world %s' % (lean_window(set(EATER_L)), lean_window(eater)))
    print('  salvo (world): (SE, -97, 1140), (SE, -91, 1111)')
    # clearance of the full lines to the REG1 envelope
    for nm, w in zip(names, wl):
        tc = time_at(w, (155, 251))
        p = glider_path(w, int(tc) - 2400, int(tc) + 2400)
        print('  %s: distance of its line (|t - t_register| <= 2400) to the REG1 envelope: %d' % (nm, set_dist(p, env)))
    print('  eater to REG1 envelope: %d' % set_dist(eater, env))
    Ts = -1410
    for k in (0, 1, 2, 3, 40):
        N = 30 * ((1732 + 1500 + 4 * k - Ts) // 30 + 1)
        c = nt.cycle(Ts) | eater | translate(set(counter(k)), 148, 240)
        c |= glider_at(*C0, Ts)
        # each DZ1 glider enters LEAD generations before it reaches the register area (it is then
        # outside the REG1 envelope; the region it comes from is empty)
        sched = {}
        for w in wl:
            ti = int(time_at(w, (155, 251))) - LEAD[w[0]]
            sched.setdefault(ti, []).append(w)
        box = list(bbox(c))
        t = Ts
        for _ in range(N):
            for w in sched.get(t, []):
                g = glider_at(*w, t)
                assert life.chebyshev_dist(g, c) >= 3, (w, t)
                assert set_dist(g, env) >= 10, (w, t, set_dist(g, env))
                c |= g
            t += 1
            c = step_cells(c)
            b = bbox(c)
            box = [min(box[0], b[0]), min(box[1], b[1]), max(box[2], b[2]), max(box[3], b[3])]
        te = Ts + N
        out = W(O) if k == 0 else W(L.A)
        want = nt.cycle(te) | eater | translate(set(counter(max(k - 1, 0))), 148, 240) | glider_at(*out, te)
        print('  k = %2d: evolve %d (R ∪ C0 ∪ inputs ∪ E ∪ B_%d) = R ∪ E ∪ B_%d ∪ %s: %s; box x %d..%d, y %d..%d' % (
            k, N, k, max(k - 1, 0), 'Z' if k == 0 else 'NZ', 'checked' if c == want else 'FAILS',
            box[0], box[2], box[1], box[3]), flush=True)


if __name__ == '__main__':
    main()
