#!/usr/bin/env python3
"""G6: push-salvo generator (with a continue glider) from ONE control glider:
       fan-out (S, K)  +  comb (S', K1', K2')  +  four reflectors.

  C0 = (SE, 41, 22) -> S = `blockedStream`: fan-out F2 with K = (7, 90, 132, 25) as in PG1:
        G1 = (NW, 29, 730) from K,   G2 = (SW, 75, 771) from S.
  path 1: G1 -> RF1 (NW -> SW, lane m) -> RF2 (SW -> SE, lane L)                -> glider p1
  path 2: G2 is a control glider (catalogue record r: an NE glider from infinity that releases a
          glider of stream A) of the first assembly S' = (k, vx, vy, s) of a comb fan-out
          (f3_comb.py), k in {2, 6}, so that the two teeth of the comb (gliders of the streams B of
          S' and K1') fly NE, in parallel; the third output of the comb (the stream glider of K2')
          is the CONTINUE glider.
          tooth 1 -> RF3 (NE -> SE) -> p2,      tooth 2 -> RF4 (NE -> SE) -> p3     (or swapped)
  The salvo {p1, p2, p3} must be one of the three-glider pushes of p1_pushes.py that can be
  assembled in the order (leftmost lane first, then two insertions from the left side):
  net.assembly_orders, types ('any', 'L', 'L').

The difference tau(p3) - tau(p2) does not depend on the positions, only on the shape of the comb
(f1, f2), on k and on the push: a "lottery" over the verified combs; for every winner all r, vx, L
are enumerated and matched with path 1.  Candidates are filtered geometrically (causality,
clearances, separations) and simulated (board, then set simulator on the unbounded plane).

Usage: g6_push.py [NSIM]      Output: results/g6_push.json.gz, summary on stdout
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import glider_at, bbox, SE, SW, NW, NE, DIRNAME, life
import machine
from machine import load_catalog, wl_map, wl_unmap
import net
from net import (reflect, compose, wl_out, wl_in, env_box, env_cells, box_dist, seg_box_dist, asm_cross,
                 rf_point, time_at, assembly_orders, glider_path, set_dist)

S = ('asm', 0, 0, 0, 0)
K = ('asm', 7, 90, 132, 25)
C0 = (SE, 41, 22)
G0 = (SE, 14, 119)
G1 = (NW, 29, 730)
G2 = (SW, 75, 771)
MR = range(-200, 131)
LR = range(-520, -90)
VR = range(-220, 60)
GAP_PIECE = 5
GAP_FLIGHT = 4


def tup(o):
    return (tuple(o[0]), o[1], o[2])


def push_candidates():
    """[(name, d2, t2, d3, t3)]: p1 = (L, t), p2 = (L + d2, t + t2), p3 = (L + d3, t + t3), both
    inserted from the left side after p1 (p2 before p3)."""
    P = json.load(open('results/p1_pushes.json'))
    out = []
    for i, p in enumerate(P):
        wl = [tuple(w) for w in p['wl']]
        if len(set(w[0] for w in wl)) < 3:
            continue
        for seq in assembly_orders(wl):
            if [ty for g, ty in seq] == ['any', 'L', 'L']:
                (l1, t1), (l2, t2), (l3, t3) = [g for g, ty in seq]
                out.append((i, l2 - l1, t2 - t1, l3 - l1, t3 - t1, l1))
    return out


def path1():
    """{(L, tau): (rf1, rf2)} for G1 -> SW lane m -> SE lane L."""
    t_src = time_at(G1, asm_cross(K)) + 100
    out = {}
    for m in MR:
        r1 = reflect(G1, SW, m)
        if not r1:
            continue
        t1 = time_at(G1, rf_point(r1[0]))
        if t1 < t_src:
            continue
        for L in LR:
            r2 = reflect(r1[1], SE, L)
            if r2 and time_at(r1[1], rf_point(r2[0])) > t1 + 100:
                out.setdefault((L, r2[1][2]), []).append((r1[0], r2[0]))
    return out


def comb_own(c, fos):
    """Teeth and spare glider of a comb record, in the own coordinates of its first assembly,
    for the stream glider G0 = (SE, 14, 119) of that assembly; and the pieces K1, K2."""
    pieces = [tuple(p) for p in c['pieces']]
    outs = [tup(o) for o in c['outs']]
    return pieces[1], pieces[2], outs[0], outs[1], outs[2]


_P1 = None
_PUSH = None


def init():
    global _P1, _PUSH
    _P1 = path1()
    _PUSH = push_candidates()


def nb_slope():
    """tau of the glider reflected NE -> SE onto lane l is  c + B * l  (l of one parity)."""
    g = (NE, -40, 0)
    a, b = reflect(g, SE, 10), reflect(g, SE, 12)
    if a is None:
        a, b = reflect(g, SE, 11), reflect(g, SE, 13)
    return (b[1][2] - a[1][2]) // 2


def double(X, lane, tau):
    """Reflectors (r1, r2) and lanes with X -> NE (lane m) -> SE (lane, tau); [] if none."""
    if X[0] not in (NW, SE):
        return []
    out = []
    for m0 in (0, 1):
        a = reflect(X, NE, m0)
        b = reflect(X, NE, m0 + 2)
        if not a or not b:
            continue
        a2, b2 = reflect(a[1], SE, lane), reflect(b[1], SE, lane)
        if not a2 or not b2:
            continue
        sl = b2[1][2] - a2[1][2]
        if sl == 0 or (tau - a2[1][2]) % sl:
            continue
        m = m0 + 2 * ((tau - a2[1][2]) // sl)
        r1 = reflect(X, NE, m)
        r2 = reflect(r1[1], SE, lane)
        assert r2[1] == (SE, lane, tau)
        out.append((r1[0], r2[0], r1[1]))
    return out


_IDX = None
_B = None


def init():
    global _P1, _PUSH, _IDX, _B
    _P1 = path1()
    _PUSH = push_candidates()
    _B = nb_slope()
    _IDX = {}
    for (L, t1) in _P1:
        _IDX.setdefault(t1 - _B * L, []).append((L, t1))


def quick_ok(pieces):
    bs = [env_box(p) for p in pieces]
    for a in range(2, len(bs)):
        for b in range(a):
            if box_dist(bs[a], bs[b]) < GAP_PIECE:
                if set_dist(env_cells(pieces[a]), env_cells(pieces[b]), GAP_PIECE) < GAP_PIECE:
                    return None
    return (min(x[0] for x in bs), min(x[1] for x in bs), max(x[2] for x in bs), max(x[3] for x in bs))


def work(job):
    """All solutions for one comb, one k and one control record; the KEEP smallest are returned."""
    c, k, rd, rlane, rtau, otau = job
    K1o, K2o, T1, T2, SP = comb_own(c, None)
    r_wl = (rd, rlane, rtau)
    d, lane0, tau0 = wl_map(r_wl, (k, 0, 0, 0))
    assert d == G2[0]
    Lc = G2[1] - lane0
    if wl_out(T1, ('asm', k, 0, 0, 0))[0] != NE:
        return []
    sols = []
    nall = 0
    for vx in VR:
        vy = d[0] * (d[1] * vx - Lc)
        s = (G2[2] - tau0 + 4 * d[0] * vx) % 30
        Sp = ('asm', k, vx, vy, s)
        if box_dist(env_box(Sp), env_box(S)) < GAP_PIECE or box_dist(env_box(Sp), env_box(K)) < GAP_PIECE:
            continue
        K1p, K2p = compose(Sp, K1o), compose(Sp, K2o)
        if quick_ok([S, K, Sp, K1p, K2p]) is None:
            continue
        cc = wl_in(G2, Sp)
        n, rem = divmod(cc[2] - rtau, 30)
        assert rem == 0 and cc[1] == rlane
        dt = otau + 30 * n - G0[2]
        sh = lambda w: (w[0], w[1], w[2] + dt)
        W = [wl_out(sh(T1), Sp), wl_out(sh(T2), Sp), wl_out(sh(SP), Sp)]
        for ti in (0, 1):
            Wt = W[ti]
            # tau of the reflected tooth on lane l: a0 + B l
            pr_ = reflect(Wt, SE, -300) or reflect(Wt, SE, -301)
            a0 = pr_[1][2] - _B * pr_[1][1]
            for pi, (i, d2, t2, d3, t3, l1) in enumerate(_PUSH):
                for x, (dx_, tx_, dy_, ty_) in enumerate(((d2, t2, d3, t3), (d3, t3, d2, t2))):
                    # tooth ti -> the glider (dx_, tx_); the other glider (dy_, ty_) from another output
                    for (L, t1) in _IDX.get(a0 + _B * dx_ - tx_, ()):
                        ra = reflect(Wt, SE, L + dx_)
                        if not ra:
                            continue
                        assert ra[1][2] == t1 + tx_
                        others = []
                        Wo = W[1 - ti]
                        rb = reflect(Wo, SE, L + dy_)
                        if rb and rb[1][2] == t1 + ty_:
                            others.append(('tt', [rb[0]], [], 2))            # tooth-tooth; continue = spare
                        for (r1, r2, mid) in double(W[2], L + dy_, t1 + ty_):
                            others.append(('ts', [r1, r2], [mid], 1 - ti))     # continue = other tooth
                        for (mode, rfs, mids, cont) in others:
                            for (rf1, rf2) in _P1[(L, t1)]:
                                nall += 1
                                pieces = [S, K, rf1, rf2, Sp, K1p, K2p, ra[0]] + rfs
                                box = quick_ok(pieces)
                                if box is None:
                                    continue
                                pa, pb = ra[1], (SE, L + dy_, t1 + ty_)
                                p2, p3 = (pa, pb) if x == 0 else (pb, pa)
                                sols.append({'comb': [c['i'], c['j']], 'k': k, 'push': i, 'mode': mode, 'tooth': ti, 'x': x,
                                             'rec': [list(rd), rlane, rtau], 'pieces': pieces,
                                             'p': [(SE, L, t1), p2, p3], 'outs': W, 'mids': mids, 'cont': cont, 'l1': l1,
                                             'box': box, 'area': (box[2] - box[0] + 1) * (box[3] - box[1] + 1)})
    sols.sort(key=lambda s: s['area'])
    return sols[:KEEP], nall


KEEP = 400


def piece_names(sol):
    n = ['S', 'K', 'RF1', 'RF2', "S'", "K1'", "K2'"]
    if sol['mode'] == 'tt':
        return n + ['RF3', 'RF4']
    return n + ['RF3', 'RF4', 'RF5']


def segments(sol):
    """Flight segments [(name, world line, t_from, t_to, indices of the pieces it uses)]."""
    pc = [tuple(p) for p in sol['pieces']]
    Sx, Kx = asm_cross(pc[0]), asm_cross(pc[1])
    cr = [asm_cross(pc[4]), asm_cross(pc[5]), asm_cross(pc[6])]
    p1, p2, p3 = [tup(w) for w in sol['p']]
    W = [tup(w) for w in sol['outs']]
    leg = reflect(G1, SW, _leg_lane(pc[2]))[1]
    far = 4000
    r1, r2 = rf_point(pc[2]), rf_point(pc[3])
    ti, x = sol['tooth'], sol['x']
    pa, pb = (p2, p3) if x == 0 else (p3, p2)       # pa from tooth ti, pb from the other source
    src = [4, 5, 6]                                  # sources of the outputs W[0], W[1], W[2]
    ra = rf_point(pc[7])
    segs = [
        ('G1', G1, time_at(G1, Kx) + 60, time_at(G1, r1) - 30, (1, 2)),
        ('leg', leg, time_at(leg, r1) + 30, time_at(leg, r2) - 30, (2, 3)),
        ('p1', p1, time_at(p1, r2) + 30, time_at(p1, r2) + far, (3,)),
        ('G2', G2, time_at(G2, Sx) + 20, time_at(G2, cr[0]) + 10, (0, 4)),
        ('tooth', W[ti], time_at(W[ti], cr[ti]) + 40, time_at(W[ti], ra) - 30, (src[ti], 7)),
        ('pa', pa, time_at(pa, ra) + 30, time_at(pa, ra) + far, (7,)),
    ]
    if sol['mode'] == 'tt':
        rb = rf_point(pc[8])
        o = W[1 - ti]
        segs += [('tooth 2', o, time_at(o, cr[1 - ti]) + 40, time_at(o, rb) - 30, (src[1 - ti], 8)),
                 ('pb', pb, time_at(pb, rb) + 30, time_at(pb, rb) + far, (8,))]
    else:
        rb1, rb2 = rf_point(pc[8]), rf_point(pc[9])
        o, mid = W[2], tup(sol['mids'][0])
        segs += [('spare', o, time_at(o, cr[2]) + 60, time_at(o, rb1) - 30, (6, 8)),
                 ('mid', mid, time_at(mid, rb1) + 30, time_at(mid, rb2) - 30, (8, 9)),
                 ('pb', pb, time_at(pb, rb2) + 30, time_at(pb, rb2) + far, (9,))]
    cg = W[sol['cont']]
    cs = src[sol['cont']]
    segs.append(('continue', cg, time_at(cg, cr[sol['cont']]) + 60, time_at(cg, cr[sol['cont']]) + far, (cs,)))
    return segs


def _leg_lane(rf1):
    for m in MR:
        r = reflect(G1, SW, m)
        if r and r[0] == rf1:
            return m
    raise ValueError


def plausible(sol):
    pc = [tuple(p) for p in sol['pieces']]
    boxes = [env_box(p) for p in pc]
    # pieces apart (the fan-out S, K is given)
    for a in range(len(pc)):
        for b in range(a):
            if (a, b) == (1, 0):
                continue
            bd = box_dist(boxes[a], boxes[b])
            if bd < GAP_PIECE and set_dist(env_cells(pc[a]), env_cells(pc[b]), GAP_PIECE) < GAP_PIECE:
                return False
    try:
        segs = segments(sol)
    except ValueError:
        return False
    for (nm, w, ta, tb, used) in segs:
        if tb < ta + 20:
            return False                     # not causal
        for i, p in enumerate(pc):
            if i in used:
                continue
            if seg_box_dist(w, ta, tb, boxes[i]) >= GAP_FLIGHT:
                continue
            if set_dist(glider_path(w, ta, tb), env_cells(p), GAP_FLIGHT) < GAP_FLIGHT:
                return False
    return True


def simulate(sol):
    pc = [tuple(p) for p in sol['pieces']]
    try:
        nt = net.Net(pc, piece_names(sol))
    except (ValueError, AssertionError):
        return sol, 'not periodic'
    st, outs, Ts, Te = nt.react([C0], limit=8000)
    if st != 'ok':
        return sol, st
    want = sorted([tup(w) for w in sol['p']] + [tup(sol['outs'][sol['cont']])])
    if outs != want:
        return sol, 'other gliders'
    sol = dict(sol)
    sol['Ts'], sol['Te'], sol['env'] = Ts, Te, list(nt.env)
    return sol, 'ok'


def main():
    nsim = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    ncomb = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    t = time.time()
    init()
    print('pushes that can be assembled as (any, L, L): %d; path 1 entries: %d' % (len(_PUSH), len(_P1)))
    combs = json.load(gzip.open('results/f3_comb.json.gz', 'rt'))['good'][:ncomb]
    recs = [r for r in load_catalog() if r['kind'] == 'gate' and r['from_infinity'] and r['outs'][0][1] == 'A' and r['d'] == NE]
    jobs = [(c, k, r['d'], r['lane'], r['tau'], r['outs'][0][0][2]) for c in combs for k in (2, 6) for r in recs]
    sols, nall = [], 0
    with Pool(min(20, os.cpu_count() or 1), initializer=init) as pool:
        for res in pool.imap_unordered(work, jobs, chunksize=2):
            if res:
                sols.extend(res[0])
                nall += res[1]
    print('combs %d, control records %d: exact solutions of the lane and timing equations: %d; kept (boxes of the pieces >= %d apart, %d smallest per job): %d (%.0f s)' % (
        len(combs), len(recs), nall, GAP_PIECE, KEEP, len(sols), time.time() - t))
    sols.sort(key=lambda s: s['area'])
    cnt = {}
    for s in sols:
        cnt[s['mode']] = cnt.get(s['mode'], 0) + 1
    print('by mode (tt: both teeth; ts: one tooth and the spare glider):', cnt)
    keep = []
    with Pool(min(20, os.cpu_count() or 1), initializer=init) as pool:
        for i0 in range(0, len(sols), 4000):
            chunk = sols[i0:i0 + 4000]
            flags = pool.map(plausible, chunk, chunksize=16)
            keep.extend(s for s, f in zip(chunk, flags) if f)
            if len(keep) >= nsim:
                break
    print('causal, separated and with clear flight segments: %d of the first %d (%.0f s)' % (len(keep), min(len(sols), i0 + 4000) if sols else 0, time.time() - t))
    with gzip.open('results/g6_candidates.json.gz', 'wt') as f:
        json.dump(keep[:2000], f, separators=(',', ':'))
    good, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for s, st in pool.imap_unordered(simulate, keep[:nsim], chunksize=1):
            stats[st] = stats.get(st, 0) + 1
            if st == 'ok':
                good.append(s)
                print('   ok: comb %s k %d push %d mode %s box %s (%.0f s)' % (s['comb'], s['k'], s['push'], s['mode'], s['box'], time.time() - t), flush=True)
    good.sort(key=lambda s: s['area'])
    print('simulated %d: %s (%.0f s)' % (min(nsim, len(keep)), stats, time.time() - t))
    with gzip.open('results/g6_push.json.gz', 'wt') as f:
        json.dump({'solutions': nall, 'plausible': len(keep), 'stats': stats, 'good': good}, f, separators=(',', ':'))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
