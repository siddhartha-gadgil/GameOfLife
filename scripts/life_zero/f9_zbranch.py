#!/usr/bin/env python3
"""F9 (R-28): the Z branch without gates.  Reflector routes with a REVERSAL (e.g. NW -> SW -> SE)
are not taxicab-invariant: their arrival time depends on the turning lane (8 generations per two
lanes), so phase mod 30 and the order "R before the INC push" can be tuned; only the lane parity is
fixed.  Structure (case Z only):
   O -> F_Z1 (control NE): link = Z OUTPUT (flies NE), second output y1 (NW) -> F_Z2:
   output a (parity fits R_in) -> 2 reflectors (with reversal) -> R_in (SE, -345) -> RF_R (re-phased)
   output b                    -> 3 reflectors                 -> C_I (SE, 314, -2222 (mod 30))
Usage: f9_zbranch.py [dist2 ...]   -> results/f9_zbranch.json"""
import json
import os
import sys
from f5_zbranch import *

PERP = {SE: (NE, SW), NW: (NE, SW), NE: (SE, NW), SW: (SE, NW)}
LANES = list(range(-3600, 3600, 3))


def fwd(w, a, b, gap=100):
    return time_at(w, b) - time_at(w, a) >= gap


def chain(W, w, src, dirs, target, accept, skip, lanes=LANES, limit=200000):
    """reflector chain from w (leaving src) through the directions `dirs` (last = target[0]) onto
    the lane target[1]; accept(final glider) -> bool.  Yields (pieces, legs)."""
    k = len(dirs)
    tried = 0

    def rec(g, pt, i, pcs, legs):
        nonlocal tried
        if i == k - 1:
            r = reflect(g, dirs[i], target[1])
            if r is None:
                return
            q = (r[0][2], r[0][3])
            if not fwd(g, pt, q):
                return
            if not accept(r[1]):
                return
            yield pcs + [r[0]], legs + [g, r[1]]
            return
        for L in lanes:
            r = reflect(g, dirs[i], L)
            if r is None:
                continue
            q = (r[0][2], r[0][3])
            if not fwd(g, pt, q):
                continue
            tried += 1
            if tried > limit:
                return
            yield from rec(r[1], q, i + 1, pcs + [r[0]], legs + [g])

    for pcs, legs in rec(w, src, 0, [], []):
        # geometry: pieces and legs
        es = [env_cells(p) for p in pcs]
        if not all(W.piece_ok(e) for e in es):
            continue
        bad = False
        for i in range(len(es)):
            for j in range(i):
                if Near(es[j]).dist(es[i], SEP) < SEP:
                    bad = True
        if bad:
            continue
        marks = [W.add(e) for e in es]
        pts = [src] + [cen(e) for e in es]
        ok = all(W.seg_ok(legs[i], pts[i], pts[i + 1], skip=tuple(skip) + ((marks[i - 1],) if i >= 1 else ()) + (marks[i],))
                 for i in range(len(es)))
        W.pop(marks[0])
        if ok:
            yield pcs, legs + [legs[-1]] if False else legs


def arith(w, src, dirs, tgt_lane, lanes_list):
    """all reflector chains (ordering checked on the anchors only): [(pieces, legs)]"""
    out = []

    def rec(g, pt, i, pcs, legs):
        if i == len(dirs) - 1:
            r = reflect(g, dirs[i], tgt_lane)
            if r is None:
                return
            q = (r[0][2], r[0][3])
            if fwd(g, pt, q):
                out.append((pcs + [r[0]], legs + [g, r[1]]))
            return
        for L in lanes_list[i]:
            r = reflect(g, dirs[i], L)
            if r is None:
                continue
            q = (r[0][2], r[0][3])
            if fwd(g, pt, q):
                rec(r[1], q, i + 1, pcs + [r[0]], legs + [g])
    rec(w, src, 0, [], [])
    return out


def geom_ok(W, src, pcs, legs, skip, end_pt):
    es = [env_cells(p) for p in pcs]
    if not all(W.piece_ok(e) for e in es):
        return False
    for i in range(len(es)):
        for j in range(i):
            if Near(es[j]).dist(es[i], SEP) < SEP:
                return False
    marks = [W.add(e) for e in es]
    pts = [src] + [cen(e) for e in es] + [end_pt]
    ok = True
    for i, g in enumerate(legs):
        sk = tuple(skip) if i == 0 else ()
        sk += tuple(marks[j] for j in (i - 1, i) if 0 <= j < len(marks))
        if not W.seg_ok(g, pts[i], pts[i + 1], skip=sk):
            ok = False
            break
    W.pop(marks[0])
    return ok


def main():
    pl = json.load(open(os.path.join(HERE, 'results', 'f3_place.json')))[0]
    n = pl['n']
    supply = [tuple(p) for p in pl['F_B']] + [tuple(r) for r in pl['rfs']] + [tuple(pl['gate'])]
    W = World(frozen_pieces() + [RF_R] + supply, F1.glider_paths(with_c=False), blocks(-1, 600))
    O = shift_wl((tuple(pl['O'][0]), pl['O'][1], pl['O'][2]), 0, 0, n)
    f = fanout_on(O, *FAMS[0], 5, 543)
    pcs1, zout, y1 = f
    e1 = envs(pcs1)
    assert W.piece_ok(e1)
    m1 = W.add(e1)
    c1 = cen(e1)
    assert W.seg_ok(zout, c1, (c1[0] + 1500 * zout[0][0], c1[1] + 1500 * zout[0][1]), skip=(m1,))
    d2s = [int(a) for a in sys.argv[1:]] or list(range(900, 2700, 53))
    for (i2, a2, b2) in FAMS[:3]:
        for k2 in range(8):
            if life.sym_apply(k2, SE) != y1[0]:
                continue
            for d2 in d2s:
                f2 = fanout_on(y1, i2, a2, b2, k2, int(c1[0] + y1[0][0] * d2))
                pcs2, u1, u2 = f2
                e2 = envs(pcs2)
                if not W.piece_ok(e2) or not W.seg_ok(y1, c1, cen(e2), skip=(m1,)):
                    continue
                m2 = W.add(e2)
                c2 = cen(e2)
                for (wr, wc) in ((u1, u2), (u2, u1)):
                    # R_in: two reflectors, earliest arrival with R after the detector
                    rsol = None
                    rc = []
                    for d1 in PERP[wr[0]]:
                        if SE in PERP[d1]:
                            rc += arith(wr, c2, [d1, SE], R_IN0[1], [range(-4000, 4000, 3)])
                    rc = [x for x in rc if x[1][-1][2] - n - R_IN0[2] + 1885 >= 2085]
                    rc.sort(key=lambda x: x[1][-1][2])
                    for (pcs, legs) in rc[:400]:
                        if geom_ok(W, c2, pcs, legs, (m2,), (RF_R[2] - 10, RF_R[3] - 10)):
                            rsol = (pcs, legs)
                            break
                    if rsol is None:
                        print('  d2 %d k2 %d: no R_in route from %s (%d arithmetic)' % (d2, k2, DIRNAME[wr[0]], len(rc)), flush=True)
                        continue
                    lr = rsol[1][-1][2] - n - R_IN0[2] + 1885
                    mr = [W.add(env_cells(p)) for p in rsol[0]]
                    csol = None
                    cc = []
                    for da in PERP[wc[0]]:
                        for db in PERP[da]:
                            if SE in PERP[db]:
                                cc += arith(wc, c2, [da, db, SE], CI0[1], [range(-4000, 4000, 7), range(-4000, 4000, 7)])
                    cc = [x for x in cc if (x[1][-1][2] - CI0[2]) % 30 == 0 and 2062 + (x[1][-1][2] - n - (-2222 + 30 * 172)) >= lr + 200]
                    cc.sort(key=lambda x: x[1][-1][2])
                    for (pcs, legs) in cc[:600]:
                        if geom_ok(W, c2, pcs, legs, (m2,), (-90, -403)):
                            csol = (pcs, legs)
                            break
                    if csol is None:
                        print('  d2 %d k2 %d: R_in ok (R local %d), no C_I chain from %s (%d arithmetic)' % (d2, k2, lr, DIRNAME[wc[0]], len(cc)), flush=True)
                        W.pop(mr[0])
                        continue
                    ci = csol[1][-1]
                    lp = 2062 + (ci[2] - n - (-2222 + 30 * 172))
                    sol = {'F_Z1': [list(x) for x in pcs1], 'F_Z2': [list(x) for x in pcs2],
                           'RF_R_route': [list(x) for x in rsol[0]], 'RF_CI_route': [list(x) for x in csol[0]],
                           'R_in': [list(rsol[1][-1][0]), rsol[1][-1][1], rsol[1][-1][2]],
                           'C_I': [list(ci[0]), ci[1], ci[2]], 'Zout': [list(zout[0]), zout[1], zout[2]],
                           'loc_R': lr, 'loc_push': lp, 'choice': [i2, k2, d2]}
                    print(json.dumps(sol), flush=True)
                    json.dump(sol, open(os.path.join(HERE, 'results', 'f9_zbranch.json'), 'w'))
                    return
                W.pop(m2)
    print('no solution')


if __name__ == '__main__':
    main()
