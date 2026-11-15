#!/usr/bin/env python3
"""G12 (R-29): MERGE for the INC input: a chain of copies of the OR gate (g5_chain.py geometry,
translation (35, 64) per copy) whose last output is turned by one reflector RF_J into the side
input of G_I (g10/g11, solution 0), so that external INC instructions reach REG1's INC lane 314
through G_I while DZ2's internal C_I uses G_I's through input.
Search: RF_J along G_I's side line (SW of G_I), the last chain copy along RF_J's input lane (NW of
RF_J); filters: envelopes >= 15 from all pieces (DZ2', DEC chain, G_I), chain side lines (from 1500
cells) and segments >= 12 from pieces they do not use, all >= 12 from B_-1..B_600.
Usage: g12_inc_chain.py [N]"""
import sys
import json
from gcommon import *
from net import wl_out, wl_in, reflect_to, env_cells, env_box, box_dist
from life import sym_apply
from dcat import Near
import g5_chain
import g11_inc_check as G11

N = int(sys.argv[1]) if len(sys.argv) > 1 else 3
pieces, GI, RFC3, CI = G11.design(0)
DEC = [tuple(g) for g in json.load(open(os.path.join(RES, 'g5_chain.json')))['gates']]
ALL = pieces + DEC
NEAR = Near(set().union(*[env_cells(p) for p in ALL]))
import g16_trace
TRACE = Near(g16_trace.trace())
NEAR_NOGI = Near(set().union(*[env_cells(p) for p in ALL if p != GI]))
BL = Near(blocks(-1, 600))
cx = sym_apply(GI[1], (45, 31))
CX = (cx[0] + GI[2], cx[1] + GI[3])


def main():
    sols = []
    from collections import Counter
    why = Counter()
    side = wl_out((NE, -76, 7), GI)            # residue 7 of the side window, any + 30 m
    for j in range(-850, -2500, -3):
        rf, win = reflect_to(side, SE, j)
        pt = (rf[2], rf[3])
        if time_at(side, pt) > time_at(side, CX) - 60:
            continue
        if NEAR.dist(env_cells(rf), 16) < 15 or TRACE.dist(env_cells(rf), 16) < 12:
            why['rf near'] += 1
            continue
        # side segment RF_J -> G_I clear of everything but G_I
        seg = glider_path(side, time_at(side, pt) + 10, time_at(side, CX) - 40)
        if NEAR_NOGI.dist(seg, 16) < 12:
            why['side segment'] += 1
            continue
        why['rf ok'] += 1
        for X in range(rf[2] - 150, rf[2] - 1200, -4):
            gates = g5_chain.chain(N, 64, X, cp=win)
            last = gates[-1]
            if box_dist(env_box(last), env_box(rf)) < 15:
                continue
            envs = [env_cells(g) for g in gates]
            if min(NEAR.dist(e, 16) for e in envs) < 15 or min(TRACE.dist(e, 16) for e in envs) < 12:
                why['gates near'] += 1
                continue
            # segment last gate -> RF_J
            lc = sym_apply(0, (45, 31))
            seg2 = glider_path(win, time_at(win, (last[2] + 45, last[3] + 31)) + 20, time_at(win, pt) - 20)
            if NEAR.dist(seg2, 16) < 12:
                why['seg2'] += 1
                continue
            # side lines of the chain copies, 1500 cells
            ok = True
            for g in gates:
                w = wl_out((NE, -76, 5), g)
                c = (g[2] + 45, g[3] + 31)
                p = glider_path(w, time_at(w, (c[0] - 1500, c[1] + 1500)), time_at(w, c) - 30)
                if NEAR.dist(p, 16) < 12 or BL.dist(p, 16) < 12:
                    ok = False
                    break
            if not ok:
                why['chain side lines'] += 1
                continue
            # through input of the first copy, 1500 cells
            w = wl_out((SE, 43, 5), gates[0])
            c = (gates[0][2] + 45, gates[0][3] + 31)
            p = glider_path(w, time_at(w, (c[0] - 1500, c[1] - 1500)), time_at(w, c) - 30)
            if NEAR.dist(p, 16) < 12:
                why['through input'] += 1
                continue
            sols.append({'RF_J': rf, 'in': win, 'side': side, 'gates': gates})
            print('RF_J %s (input %s -> %s), chain %s' % (rf, wl(win), wl(side), gates), flush=True)
            break
        if len(sols) >= 3:
            break
    print(why)
    json.dump(sols, open(os.path.join(RES, 'g12_inc_chain.json'), 'w'))


if __name__ == '__main__':
    main()
