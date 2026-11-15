#!/usr/bin/env python3
"""G5 (R-29): MERGE - a chain of copies of the OR gate of g4_or.py (blockedStream, through input
T = (SE, 43, .), side input S = (NE, -76, .), output A = (SE, 14, .) in gate coordinates) placed in
series by translation, the last copy releasing exactly DZ2's control C' = (SE, 41, 4444 + 30 m).

Chain: G_N = ('asm', 0, X, X - 27, s_N) (output lane 41); G_(i-1) = G_i moved by (-a - 29, -a)... in
general G_(i-1) = G_i translated by v = (-(A + 29), -A) where A is the along spacing (so that the
output lane of G_(i-1), 14 + 29 + ..., is the through lane of G_i), delay chosen so that the
output of G_(i-1) meets G_i at residue 5 of its through window.
Usage: g5_chain.py [N] [A] [X]   (default 3 copies, smallest A with clearances, X = -1700)"""
import sys
import json
from gcommon import *
from net import wl_out, wl_in, env_cells, env_box, box_dist
from dcat import Near

T_LANE, S_LANE = 43, -76
T_RES = {2: 119, 4: 119, 5: 119, 6: 119, 7: 119, 12: 119, 13: 119, 14: 119, 21: 149, 22: 149, 23: 149, 24: 149}
S_RES = {r: 29 for r in range(1, 14)}
S_RES.update({18: 59, 28: 59})


def gate_out(piece, w_in_gate_tau):
    """World line of the released glider of a gate piece whose control has gate-coordinate tau."""
    r = w_in_gate_tau % 30
    return None


def chain(N, A, X, cp=None):
    """List of gate pieces G_1 .. G_N (G_N releases C' class) and the side input lines."""
    if cp is None:
        cp = f8_full.design()['ctrl']
    # last gate: output (SE, 14, 119) in gate coords maps to lane 14 + vx - vy = 41
    vx, vy = X, X - (cp[1] - 14)
    # its phase: world output tau of gate-output (SE,14,119) with delay s is 119 + s + 4*vx*... use wl_out
    s = 0
    o = wl_out((SE, 14, 119), ('asm', 0, vx, vy, 0))
    s = (cp[2] - o[2]) % 30
    gates = [('asm', 0, vx, vy, s)]
    for i in range(N - 1):
        g = gates[0]
        # previous gate: translated by (-(A + 29), -A)  [its output lane = this gate's through lane]
        p, q = -A + (T_LANE - 14), -A
        # this gate's through control at residue 5 (gate coords tau 305) in world:
        need = wl_out((SE, T_LANE, 5), g)          # world line of the input wanted
        o = wl_out((SE, 14, 119), ('asm', 0, g[2] + p, g[3] + q, 0))
        assert o[1] == need[1], (o, need)
        s2 = (need[2] - o[2]) % 30
        gates.insert(0, ('asm', 0, g[2] + p, g[3] + q, s2))
    return gates


def side_lines(gates):
    """For each gate: the world lines (NE, lane, tau) of its side input for residues 1..13 (all
    release; tau may be increased by any multiple of 30)."""
    return [[wl_out((NE, S_LANE, r), g) for r in range(1, 14)] for g in gates]


def clearances(gates, others=()):
    """min envelope distance between gates, and min distance of each side line / through segment
    to the envelopes of the pieces it does not use (and of `others`)."""
    envs = [env_cells(g) for g in gates]
    dmin = 10 ** 9
    for i in range(len(gates)):
        for j in range(i):
            dmin = min(dmin, box_dist(env_box(gates[i]), env_box(gates[j])))
    near_other = [Near(e) for e in envs]
    side = 10 ** 9
    for i, g in enumerate(gates):
        w = wl_out((NE, S_LANE, 5), g)
        cx, cy = g[2] + 45, g[3] + 31
        # from 1500 cells SW of the gate to the gate
        path = glider_path(w, time_at(w, (cx - 1500, cy + 1500)), time_at(w, (cx, cy)))
        for j, e in enumerate(near_other):
            if j != i:
                side = min(side, e.dist(path, 200))
    return dmin, side


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    X = int(sys.argv[3]) if len(sys.argv) > 3 else -1700
    if len(sys.argv) > 2:
        As = [int(sys.argv[2])]
    else:
        As = range(0, 400, 2)
    for A in As:
        g = chain(N, A, X)
        d, s = clearances(g)
        print('A = %d: gate envelope distance %d, side lines to other gates %d' % (A, d, s), flush=True)
        if d >= 12 and s >= 12 and len(As) > 1:
            break
    json.dump({'N': N, 'A': A, 'X': X, 'gates': g, 'side': side_lines(g)}, open(os.path.join(RES, 'g5_chain.json'), 'w'))
    for i, gg in enumerate(g):
        print('  G_%d = %s; side input (NE, lane, tau) for residues 1..13: %s .. %s' % (i + 1, gg, side_lines(g)[i][0], side_lines(g)[i][-1]))


if __name__ == '__main__':
    main()
