#!/usr/bin/env python3
"""G11 (R-29): check the INC OR gate G_I of g10_inc_or.py with DZ2 and REG1 (exact simulation).
DZ2' = DZ2 with RF_C3 replaced by RF_C3' and the gate G_I added.
 (1) DZ2' + C' + B_k: k = 0 -> B_0 + Z (DZ2's internal C_I now passes G_I); k >= 1 -> B_(k-1) + NZ;
 (2) external INC through G_I's side input (S_RES residues 1..13 of g4_or.py): B_k -> B_(k+1);
 (3) clearance of G_I's side line (from 3000 cells away) to all pieces and the blocks.
Usage: g11_inc_check.py SOLUTION_INDEX [ks]"""
import sys
import json
from gcommon import *
from net import wl_out, env_cells, set_dist
from life import sym_apply
from dcat import Near

PIECES, D = dz2()
RF_C3 = ('rf', 7, -876, -1175, 11)
SOLS = json.load(open(os.path.join(RES, 'g10_inc_or.json')))


def design(i):
    s = SOLS[i]
    g, rf = tuple(s['gate']), tuple(s['rf'])
    pieces = [p for p in PIECES if p != RF_C3] + [rf, g]
    return pieces, g, rf, (tuple(s['C_I'][0]), s['C_I'][1], s['C_I'][2])


def main():
    i = int(sys.argv[1])
    ks = [int(a) for a in (sys.argv[2] if len(sys.argv) > 2 else '0,1,2,3,40').split(',')]
    pieces, g, rf, ci = design(i)
    print("G_I = %s, RF_C3' = %s, DZ2's C_I after G_I: %s" % (g, rf, wl(ci)))
    cx = sym_apply(g[1], (45, 31))
    cx = (cx[0] + g[2], cx[1] + g[3])
    # side line clearance
    side = wl_out((NE, -76, 7), g)
    away = (cx[0] - 3000 * side[0][0], cx[1] - 3000 * side[0][1])
    path = glider_path(side, time_at(side, away), time_at(side, cx))
    NO = Near(set().union(*[env_cells(p) for p in pieces if p != g]))
    print('side input %s (residues 1..13 release; +30 m): path from 3000 cells away: %d from the other pieces, %d from B_-1..B_600' % (
        wl(side), NO.dist(path, 200), Near(blocks(-1, 600)).dist(path, 200)))
    cbox = core_box(pieces, [(140, 230, 900, 900)])
    Ts = -300
    for k in (ks if os.environ.get('G11_DZ2', '1') == '1' else []):
        N = 27540 + 600 if k == 0 else 11490
        cells, rem = run_peel(pieces, [D['ctrl']], Ts, Ts + N, extra=block(k), cbox=cbox)
        want = state(pieces, [], Ts + N, block(k - 1 if k else 0))
        exp = [D['zout'] if k == 0 else D['n1']]
        print("  (1) DZ2' C' on B_%d: %s %s" % (k, [wl(x) for x in rem], 'ok' if (cells == want and rem == exp) else 'FAIL'), flush=True)
    for k in ks:
        for r in (1, 7, 13):
            w = shift_wl(wl_out((NE, -76, r), g), 0, 0, 30 * 100)
            t0 = 30 * ((int(time_at(w, cx)) - 200) // 30)
            t1 = t0 + 30 * ((7000 + 4 * k) // 30)
            cells, rem = run_peel(pieces, [w], t0, t1, extra=block(k), cbox=cbox)
            want = state(pieces, [], t1, block(k + 1))
            print('  (2) external INC %s on B_%d: %s' % (wl(w), k, 'ok' if (cells == want and not rem) else 'FAIL %s' % rem), flush=True)


if __name__ == '__main__':
    main()
