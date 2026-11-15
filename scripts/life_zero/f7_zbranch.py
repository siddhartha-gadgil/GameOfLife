#!/usr/bin/env python3
"""F7 (R-28): the Z branch with two re-timing gates.

Invariants of reflector routes fix both the phase mod 30 and the lane parity of what can be reached
from O: C_I (exact phase mod 30) and R_in (odd lane -345) are both unreachable by fan-outs and
reflectors alone (f5/f6).  So each is released by its own gate (copy of blockedStream, catalogue
records of kind 'gate'):
   O -> F_Z1 (control NE): link = Z OUTPUT (flies NE), second output y1 -> F_Z2: outputs u1, u2;
   u1 -> 1-2 reflectors -> E_CI -> G_CI -> C_I = (SE, 314, -2222 + 30 m)
   u2 -> 1-2 reflectors -> E_R  -> G_R  -> R_in = (SE, -345, .) -> RF_R (re-phased) -> R.
Writes results/f7_zbranch.json."""
import json
import os
import sys
from f5_zbranch import *
from machine import load_catalog, wl_map
from f2_route import place_out
from f6_zbranch import arrival_fn
import f6_zbranch as F6

GREC = [r for r in load_catalog() if r['kind'] == 'gate' and r['from_infinity'] and len(r['outs']) == 1]
BASES = {}


def bases(line, p0):
    key = (line, p0)
    if key not in BASES:
        out = []
        for r in GREC:
            ow = r['outs'][0][0]
            for k in range(8):
                if life.sym_apply(k, ow[0]) != line[0]:
                    continue
                for p in (p0, p0 - 1):
                    pl = place_out(ow, k, line, p)
                    if pl is not None:
                        asm, dt = pl
                        E = shift_wl(wl_map(r['wl'], asm), 0, 0, dt)
                        if E[0] != NW:
                            out.append((r, k, asm, dt, E))
                        break
        BASES[key] = out
    return BASES[key]


def arrival_typed(w, dE, L, mid):
    if mid is None:
        r = reflect(w, dE, L)
        return None if r is None else r[1]
    for Lm in range(0, 6):
        a = reflect(w, mid, Lm + 2000 * mid[0])
        if a is None:
            continue
        b = reflect(a[1], dE, L)
        if b is not None:
            return b[1]
    return None


def arrival_fns(w):
    """{(dE, parity, mid): (a, b)}: arrival tau = a + b * lane for the route type 'mid'"""
    out = {}
    for dE in (SE, SW, NE):
        perp = dE[0] * w[0][0] + dE[1] * w[0][1] == 0
        mids = [None] if perp else [x for x in (SE, SW, NE, NW) if x[0] * w[0][0] + x[1] * w[0][1] == 0]
        for mid in mids:
            for par in (0, 1):
                v = []
                for L in (par - 2000, par - 1998):
                    a = arrival_typed(w, dE, L, mid)
                    if a is not None:
                        v.append((L, a[2]))
                if len(v) == 2:
                    b = (v[1][1] - v[0][1]) // 2
                    out[(dE, par, mid)] = (v[0][1] - b * v[0][0], b)
    return out


def route_typed(W, w, src, dE, L, lanes, skip, mid):
    if mid is None:
        yield from route(W, w, src, dE, L, lanes, skip)
        return
    yield from route(W, w, src, dE, L, lanes, skip, only_mid=mid)


def gate_for(W, u, src, line, p0, dls, accept, end_pt, skip, max2=30, sign=1):
    """gate on `line` (SE glider world line, tau = reference), placed at x = p0 - dl, released
    glider = line delayed by dt + 30 m; accept(glider) -> bool.  Returns (gate, E, out, rfs) or None.
    Every route type (direct, or two reflectors via either perpendicular direction) is tried."""
    AFS = arrival_fns(u)
    cands = []
    for (r, k, asm, dt, E0) in bases(line, p0):
        for dl in dls:
            E = shift_wl(E0, -dl, -dl, -4 * dl)
            for mid in (None, SE, SW, NE, NW):
                f = AFS.get((E[0], E[1] % 2, mid))
                if f is None:
                    continue
                a = f[0] + f[1] * E[1]
                if (a - E[2]) % 30:
                    continue
                m = (a - E[2]) // 30
                out = shift_wl(line, 0, 0, dt + 30 * m)
                if not accept(out):
                    continue
                gate = ('asm', asm[0], asm[1] - dl, asm[2] - dl, (asm[3] - 4 * dl) % 30)
                cands.append((gate, shift_wl(E, 0, 0, 30 * m), out, mid))
    cands.sort(key=lambda c: (c[3] is not None, sign * c[2][2]))
    # spread the attempts: at most CAP candidates, taken evenly from the sorted list
    CAP = 160
    if len(cands) > CAP:
        step = len(cands) / CAP
        cands = [cands[int(i * step)] for i in range(CAP)]
    two = 0
    for (gate, Em, out, mid) in cands:
        if mid is not None:
            two += 1
            if two > max2:
                break
        eg = env_cells(gate)
        if not W.piece_ok(eg):
            continue
        gi = W.add(eg)
        for (rr, legs, endp) in route_typed(W, u, src, Em[0], Em[1], list(range(-4500, 4500, 17)), skip, mid):
            if legs[-1] != Em:
                continue
            if not W.seg_ok(Em, endp, cen(eg), skip=(gi,)):
                continue
            if not W.seg_ok(out, cen(eg), end_pt, skip=(gi,)):
                continue
            W.add(envs(rr))
            return gate, Em, out, rr
        W.pop(gi)
    return None


def main():
    pl = json.load(open(os.path.join(HERE, 'results', 'f3_place.json')))[0]
    n = pl['n']
    supply = [tuple(p) for p in pl['F_B']] + [tuple(r) for r in pl['rfs']] + [tuple(pl['gate'])]
    W = World(frozen_pieces() + [RF_R] + supply, F1.glider_paths(with_c=False), blocks(-1, 600))
    O = shift_wl((tuple(pl['O'][0]), pl['O'][1], pl['O'][2]), 0, 0, n)
    x0 = int(min(glider_at(*O, int(time_at(O, (155, 251)))))[0])
    ci_line = (SE, CI0[1], CI0[2])
    r_line = (SE, R_IN0[1], R_IN0[2])
    count = 0
    for (i1, a1, b1) in FAMS[:3]:
        for k1 in (5, 3):
            if life.sym_apply(k1, SE) != NE:
                continue
            for p1 in range(x0 + 250, x0 + 700, 23):
                f = fanout_on(O, i1, a1, b1, k1, p1)
                if f is None:
                    continue
                pcs1, g1o, g2o = f
                e1 = envs(pcs1)
                if not W.piece_ok(e1):
                    continue
                m1 = W.add(e1)
                c1 = cen(e1)
                for (zout, y1) in ((g1o, g2o),):
                  if not W.seg_ok(zout, c1, (c1[0] + zout[0][0] * 1500, c1[1] + zout[0][1] * 1500), skip=(m1,)):
                    continue
                  for (i2, a2, b2) in FAMS[:2]:
                    for k2 in range(8):
                        if life.sym_apply(k2, SE) != y1[0]:
                            continue
                        for dist2 in range(900, 2700, 53):
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
                                count += 1
                                mark = len(W.extra)
                                # R_in first: any time with R after the detector (local >= 2085);
                                # a plain reflector route if the lane parity allows, else a gate
                                gR = None
                                best = {}
                                perpR = wb[0][0] * SE[0] + wb[0][1] * SE[1] == 0
                                for mid in ([None] if perpR else [x for x in (SE, SW, NE, NW) if x[0] * wb[0][0] + x[1] * wb[0][1] == 0]):
                                    a0 = arrival_typed(wb, SE, R_IN0[1], mid)
                                    if a0 is None or a0[2] - n - R_IN0[2] + 1885 < 2085:
                                        continue
                                    for (rr, lb, endb) in route_typed(W, wb, c2, SE, R_IN0[1], list(range(-4500, 4500, 17)), (m2,), mid):
                                        rin = lb[-1]
                                        if not W.seg_ok(rin, endb, (RF_R[2] - 10, RF_R[3] - 10)):
                                            continue
                                        best[mid] = (rin, rr)
                                        break
                                if best:
                                    rin, rr = min(best.values(), key=lambda v: v[0][2])
                                    W.add(envs(rr))
                                    gR = (None, None, rin, rr)
                                if gR is None:
                                  gR = gate_for(W, wb, c2, r_line, -420, range(0, 900, 3),
                                              lambda g: g[2] - n - R_IN0[2] + 1885 >= 2085, (RF_R[2] - 10, RF_R[3] - 10), (m2,), sign=1)
                                if gR is None:
                                    W.pop(mark)
                                    print('  placement %d %s: no R_in route or gate' % (count, (i1, k1, p1, i2, k2, dist2)), flush=True)
                                    continue
                                lr = gR[2][2] - n - R_IN0[2] + 1885
                                gC = gate_for(W, wa, c2, ci_line, -420, range(0, 4000, 3),
                                              lambda g: 2062 + (g[2] - n - (-2222 + 30 * 172)) >= lr + 200, (-90, -403), (m2,), sign=-1)
                                if gC is None:
                                    W.pop(mark)
                                    print('  placement %d %s: R_in gate ok, no C_I gate' % (count, (i1, k1, p1, i2, k2, dist2)), flush=True)
                                    continue
                                lp = 2062 + (gC[2][2] - n - (-2222 + 30 * 172))
                                sol = {'F_Z1': [list(x) for x in pcs1], 'F_Z2': [list(x) for x in pcs2],
                                       'G_R': list(gR[0]) if gR[0] else None, 'E_R': [list(gR[1][0]), gR[1][1], gR[1][2]] if gR[1] else None,
                                       'RF_ER': [list(x) for x in gR[3]],
                                       'R_in': [list(gR[2][0]), gR[2][1], gR[2][2]],
                                       'G_CI': list(gC[0]), 'E_CI': [list(gC[1][0]), gC[1][1], gC[1][2]], 'RF_ECI': [list(x) for x in gC[3]],
                                       'C_I': [list(gC[2][0]), gC[2][1], gC[2][2]],
                                       'Zout': [list(zout[0]), zout[1], zout[2]], 'loc_R': lr, 'loc_push': lp,
                                       'choice': [i1, k1, p1, i2, k2, dist2]}
                                print(json.dumps(sol), flush=True)
                                json.dump(sol, open(os.path.join(HERE, 'results', 'f7_zbranch.json'), 'w'))
                                return
                            W.pop(m2)
                W.pop(m1)
    print('no solution')


if __name__ == '__main__':
    main()
