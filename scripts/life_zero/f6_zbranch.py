#!/usr/bin/env python3
"""F6 (R-28): the Z branch with a re-timing gate for C_I.

The phase of a reflector/fan-out route is an invariant: from O, every route of fan-outs and
reflectors reaches C_I's lane with tau - (-2222) = 2, 6, 8, ..., 28 (mod 30) but never 0
(f5_zbranch.py, results/f6_zbranch.txt).  So C_I is released by a gate G_CI (copy of
blockedStream, catalogue record of kind 'gate') placed on C_I's lane; its control E_CI comes
from the route.  Structure (case Z only):
   O -> F_Z1 (control NE): link = Z OUTPUT (flies NE), second output y1 ->
   F_Z2: outputs u1 -> reflectors -> E_CI -> G_CI -> C_I = (SE, 314, -2222 + 30 m)
                u2 -> reflectors -> R_in = (SE, -345, .) -> RF_R (re-phased) -> R.
Writes results/f6_zbranch.json (first complete solution)."""
import json
import os
import sys
from f5_zbranch import *
from machine import load_catalog, wl_map
from f2_route import place_out

GREC = None


def arrival_fn(w):
    """{(dir, parity): (a, b)} with arrival tau = a + b * lane (reflector routes from w)"""
    out = {}
    for dE in (SE, SW, NE):
        for par in (0, 1):
            v = []
            for L in (par - 2000, par - 1998):
                a = arrival(w, dE, L)
                if a is not None:
                    v.append((L, a[2]))
            if len(v) == 2:
                b = (v[1][1] - v[0][1]) // 2
                out[(dE, par)] = (v[0][1] - b * v[0][0], b)
    return out


GBASE = None


def gate_bases():
    """[(record, k, asm0, dt, E0)] for every gate record and symmetry with output on C_I's line"""
    out = []
    for r in GREC:
        ow = r['outs'][0][0]
        for k in range(8):
            if life.sym_apply(k, ow[0]) != SE:
                continue
            for p in (-400, -401):
                pl = place_out(ow, k, (SE, CI0[1], CI0[2]), p)
                if pl is not None:
                    asm, dt = pl
                    E = shift_wl(wl_map(r['wl'], asm), 0, 0, dt)
                    if E[0] != NW:
                        out.append((r, k, asm, dt, E))
                    break
    return out


def gate_for_CI(W, u1, src, n, lr, skip):
    """(gate piece, E, C_I, reflector route, local push time) or None"""
    global GBASE
    if GBASE is None:
        GBASE = gate_bases()
    AF = arrival_fn(u1)
    cands = []
    for (r, k, asm, dt, E0) in GBASE:
        for dl in range(0, 1300, 2):
            E = shift_wl(E0, -dl, -dl, -4 * dl)
            f = AF.get((E[0], E[1] % 2))
            if f is None:
                continue
            a = f[0] + f[1] * E[1]
            if (a - E[2]) % 30:
                continue
            m = (a - E[2]) // 30
            ci = shift_wl((SE, CI0[1], CI0[2]), 0, 0, dt + 30 * m)
            lp = 2062 + (ci[2] - n - (-2222 + 30 * 172))
            if lp < lr + 200:
                continue
            gate = ('asm', asm[0], asm[1] - dl, asm[2] - dl, (asm[3] - 4 * dl) % 30)
            cands.append((gate, shift_wl(E, 0, 0, 30 * m), ci, lp))
    cands.sort(key=lambda c: c[1][0][0] * u1[0][0] + c[1][0][1] * u1[0][1] != 0)
    two = 0
    for (gate, Em, ci, lp) in cands:
        if Em[0][0] * u1[0][0] + Em[0][1] * u1[0][1] != 0:
            two += 1
            if two > 40:
                break
        eg = env_cells(gate)
        if not W.piece_ok(eg):
            continue
        gi = W.add(eg)
        for (rr, legs, endp) in route(W, u1, src, Em[0], Em[1], list(range(-1600, 1600, 11)), skip):
            if legs[-1] != Em:
                continue
            if not W.seg_ok(Em, endp, cen(eg), skip=(gi,)):
                continue
            if not W.seg_ok(ci, cen(eg), (-90, -403), skip=(gi,)):
                continue
            return gate, Em, ci, rr, lp
        W.pop(gi)
    return None


def main():
    global GREC
    GREC = [r for r in load_catalog() if r['kind'] == 'gate' and r['from_infinity'] and len(r['outs']) == 1]
    pl = json.load(open(os.path.join(HERE, 'results', 'f3_place.json')))[0]
    n = pl['n']
    supply = [tuple(p) for p in pl['F_B']] + [tuple(r) for r in pl['rfs']] + [tuple(pl['gate'])]
    W = World(frozen_pieces() + [RF_R] + supply, F1.glider_paths(with_c=False), blocks(-1, 600))
    O = shift_wl((tuple(pl['O'][0]), pl['O'][1], pl['O'][2]), 0, 0, n)
    x0 = int(min(glider_at(*O, int(time_at(O, (155, 251)))))[0])
    lanes_mid = list(range(-1600, 1600, 11))
    tried = 0
    for (i1, a1, b1) in FAMS[:3]:
        for k1 in (5, 3):
            if life.sym_apply(k1, SE) != NE:
                continue
            for p1 in range(x0 + 250, x0 + 700, 15):
                f = fanout_on(O, i1, a1, b1, k1, p1)
                if f is None:
                    continue
                pcs1, zout, y1 = f
                e1 = envs(pcs1)
                if not W.piece_ok(e1):
                    continue
                m1 = W.add(e1)
                c1 = cen(e1)
                if not W.seg_ok(zout, c1, (c1[0] + zout[0][0] * 1500, c1[1] + zout[0][1] * 1500), skip=(m1,)):
                    W.pop(m1)
                    continue
                for (i2, a2, b2) in FAMS[:3]:
                    for k2 in range(8):
                        if life.sym_apply(k2, SE) != y1[0]:
                            continue
                        for dist2 in range(150, 1300, 37):
                            f2 = fanout_on(y1, i2, a2, b2, k2, int(c1[0] + y1[0][0] * dist2))
                            if f2 is None:
                                continue
                            pcs2, u1, u2 = f2
                            e2 = envs(pcs2)
                            if not W.piece_ok(e2) or not W.seg_ok(y1, c1, cen(e2), skip=(m1,)):
                                continue
                            m2 = W.add(e2)
                            c2 = cen(e2)
                            for (wa, wb) in ((u1, u2), (u2, u1)):
                                ri0 = arrival(wb, SE, R_IN0[1])
                                if ri0 is None:
                                    continue
                                lr = ri0[2] - n - R_IN0[2] + 1885
                                if lr < 2085:
                                    continue
                                for (rb, lb, endb) in route(W, wb, c2, SE, R_IN0[1], lanes_mid, (m2,)):
                                    rin = lb[-1]
                                    if not W.seg_ok(rin, endb, (RF_R[2], RF_R[3])):
                                        continue
                                    mb = W.add(envs(rb))
                                    tried += 1
                                    g = gate_for_CI(W, wa, c2, n, lr, (m2,))
                                    if g:
                                        gate, E, ci, ra, lp = g
                                        sol = {'F_Z1': [list(x) for x in pcs1], 'F_Z2': [list(x) for x in pcs2],
                                               'RF_RIN': [list(x) for x in rb], 'RF_ECI': [list(x) for x in ra], 'G_CI': list(gate),
                                               'Zout': [list(zout[0]), zout[1], zout[2]], 'R_in': [list(rin[0]), rin[1], rin[2]],
                                               'E_CI': [list(E[0]), E[1], E[2]], 'C_I': [list(ci[0]), ci[1], ci[2]],
                                               'loc_R': lr, 'loc_push': lp, 'choice': [i1, k1, p1, i2, k2, dist2]}
                                        print(json.dumps(sol), flush=True)
                                        json.dump(sol, open(os.path.join(HERE, 'results', 'f6_zbranch.json'), 'w'))
                                        return
                                    W.pop(mb)
                                    print('  no C_I gate for placement', tried, (i1, k1, p1, i2, k2, dist2), flush=True)
                                    break
                            W.pop(m2)
                W.pop(m1)
    print('no solution')


if __name__ == '__main__':
    main()
