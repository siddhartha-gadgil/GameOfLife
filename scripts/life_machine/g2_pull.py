#!/usr/bin/env python3
"""Search G2: pull-salvo generator = round-trip fan-out (S, K) + reflectors.

One control glider C0 = (SE, 41, 22) enters the gate S = `blockedStream`; the fan-out
(f2_roundtrip.py) gives G1 (from K) and G2 (from S, flying SW).  Each of them is led by copies of
the reflector RF (q1_reflector.py; g1_pull.py) onto a lane of direction SE:
    a glider flying SW needs one reflection (SW -> SE), a glider flying NW two (NW -> SW -> SE),
    a glider flying SE none or two (SE -> SW -> SE).
A copy of RF that turns a given glider onto a given lane is unique (reflect()); its delay s
(mod 30) is thereby fixed.  Unknowns: the final lane L of the first salvo glider and the
intermediate lanes.  Condition: the two final gliders are (SE, L, t) and (SE, L + 6, t - 29),
i.e. `pullSalvo` up to translation along the diagonal and evolution.

Each solution is checked by full simulation: the composite (S, K, reflectors) has period 30;
with C0 it returns to its cycle and exactly the two salvo gliders leave (board, then set
simulator on the unbounded plane).  Further checks are in g3_check.py.

Usage: g2_pull.py [MAXSIM]      Output: results/g2_pull.json.gz, summary on stdout
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import (glider_at, bbox, SE, SW, NW, NE, DIRNAME, gates, life, transform, translate)
import machine
from machine import asm_cells, asm_envelope, box_dist, run_scheduled, verify_scheduled
from reactions import shift_wl, sym_wl
from g1_pull import RF0, RF_IN, RF_OUT, rf_cells, rf_cycle, C0, S_ASM, Comp

IMG = [(sym_wl(RF_IN, k), sym_wl(RF_OUT, k)) for k in range(8)]
TURN = {(i[0], o[0]): k for k, (i, o) in enumerate(IMG)}
CHAINS = {SW: [[SE]], NE: [[SE]], NW: [[SW, SE], [NE, SE]], SE: [[], [SW, SE], [NE, SE]]}
LMIN, LMAX = -260, 60


def reflect(g, dout, lane_out):
    """The copy (k, p, q, s) of RF turning g into a glider of direction dout on lane_out, and
    that glider; None if impossible (parity)."""
    k = TURN.get((g[0], dout))
    if k is None:
        return None
    i0, o0 = IMG[k]
    di, do = i0[0], o0[0]
    a1, b1, c1 = di[1], -di[0], g[1] - i0[1]
    a2, b2, c2 = do[1], -do[0], lane_out - o0[1]
    det = a1 * b2 - a2 * b1
    pn, qn = c1 * b2 - c2 * b1, a1 * c2 - a2 * c1
    if pn % det or qn % det:
        return None
    p, q = pn // det, qn // det
    s = g[2] - i0[2] + 4 * di[0] * p
    return (k, p, q, s % 30), shift_wl(o0, p, q, s)


def pos(g, t):
    """Box origin of the glider (canonical parameter) at time t."""
    d, lane, tau = g
    x = d[0] * ((t - tau) // 4)
    return (x, d[0] * (d[1] * x - lane))


def time_at(g, pt):
    """Time at which the glider is nearest to the point pt."""
    d, lane, tau = g
    # along the glider: x = d0 (t - tau)/4 ; choose t with x + d0 d1 y matching
    # project: (x, y) . d = d0 x + d1 y = (t - tau)/2 + const ... use x and y of pt
    x, y = pt
    # y = d0 (d1 x - lane)  ->  on the lane; parameter by s = d0 x + d1 y
    s = d[0] * x + d[1] * y
    # for the glider: x = d0 q, y = d0 d1 x - d0 lane = d1 q - d0 lane; s = q + q - d0 d1 lane
    q = (s + d[0] * d[1] * lane) / 2
    return tau + 4 * q


def rf_center(rf):
    k, p, q, s = rf
    b = bbox(translate(transform(RF0, k), p, q))
    return ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)


def solve(fo):
    """All (reflectors, a, b) for a fan-out record."""
    asm = tuple(fo['asm'])
    outs = [(tuple(o[0]), o[1], o[2]) for o in fo['outs']]
    g2 = [w for w in outs if w == w and w[0] == SW and w[1] == 75]
    g1 = [w for w in outs if w not in g2]
    if len(g1) != 1 or len(g2) != 1:
        return []
    g1, g2 = g1[0], g2[0]
    # source times: G2 leaves the crossing of S near (45, 31); G1 the crossing of K
    kx, ky = machine.life.sym_apply(asm[0], (45, 31))
    src = {g1: time_at(g1, (kx + asm[1], ky + asm[2])), g2: time_at(g2, (45, 31))}
    sols = []
    paths = {}
    for g in (g1, g2):
        plist = []
        for chain in CHAINS[g[0]]:
            if not chain:
                plist.append(([], g))
            elif len(chain) == 1:
                for L in range(LMIN, LMAX + 1):
                    r = reflect(g, chain[0], L)
                    if r and time_at(g, rf_center(r[0])) > src[g] + 60:
                        plist.append(([r[0]], r[1]))
            else:
                # intermediate lane m of direction chain[0]
                d1 = chain[0]
                for m in range(-420, 421):
                    r1 = reflect(g, d1, m)
                    if not r1:
                        continue
                    t1 = time_at(g, rf_center(r1[0]))
                    if t1 < src[g] + 60:
                        continue
                    for L in range(LMIN, LMAX + 1):
                        r2 = reflect(r1[1], chain[1], L)
                        if r2 and time_at(r1[1], rf_center(r2[0])) > t1 + 120:
                            plist.append(([r1[0], r2[0]], r2[1]))
        paths[g] = plist
    # match: (L, t) and (L + 6, t - 29)
    index = {}
    for rfs, w in paths[g2]:
        index.setdefault((w[1], w[2]), []).append(rfs)
    for rfs1, w1 in paths[g1]:
        for (dl, dt) in ((6, -29), (-6, 29)):
            key = (w1[1] + dl, w1[2] + dt)
            for rfs2 in index.get(key, []):
                w2 = (SE, key[0], key[1])
                a, b = (w1, w2) if dl == 6 else (w2, w1)
                if len(rfs1) + len(rfs2) == 0:
                    continue
                sols.append({'asm': list(asm), 'K': fo['K'], 'rfs': [list(r) for r in rfs1 + rfs2],
                             'a': a, 'b': b, 'n1': len(rfs1), 'g1': g1, 'g2': g2})
    return sols


def footprint(sol):
    cells = set(asm_cells(S_ASM, 0)) | set(asm_cells(tuple(sol['asm']), 0))
    for rf in sol['rfs']:
        c = rf_cells(tuple(rf), 0)
        if c & cells:
            return None
        cells |= c
    return cells


def simulate(sol):
    cells = footprint(sol)
    if cells is None:
        return sol, 'overlap'
    b = bbox(cells)
    if (b[2] - b[0]) * (b[3] - b[1]) > 500 * 500:
        return sol, 'too large'
    try:
        comp = Comp(cells)
    except AssertionError:
        return sol, 'not periodic'
    res = run_scheduled(comp, [C0], limit=12000, t_hint=200)
    if res['status'] != 'restored':
        return sol, res['status']
    outs = sorted(w for (w, th) in res['out'])
    if outs != sorted([tuple(sol['a']), tuple(sol['b'])]):
        return sol, 'other gliders'
    ok, Ts, Te = verify_scheduled(comp, [C0], res)
    if not ok:
        return sol, 'verification failed'
    sol = dict(sol)
    sol['Ts'], sol['Te'], sol['env'] = Ts, Te, list(comp.R.env)
    return sol, 'ok'


def main():
    maxsim = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    t = time.time()
    d = json.load(gzip.open('results/f2_roundtrip.json.gz', 'rt'))
    sols = []
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for ss in pool.imap_unordered(solve, d['good'], chunksize=1):
            sols.extend(ss)
    print('fan-outs %d; exact solutions of the lane and timing equations: %d (%.0f s)' % (len(d['good']), len(sols), time.time() - t))
    for s in sols:
        cells = footprint(s)
        s['area'] = None
        if cells is not None:
            b = bbox(cells)
            s['area'] = (b[2] - b[0] + 1) * (b[3] - b[1] + 1)
    sols = [s for s in sols if s['area'] is not None]
    sols.sort(key=lambda s: (len(s['rfs']), s['area']))
    cnt = {}
    for s in sols:
        cnt[len(s['rfs'])] = cnt.get(len(s['rfs']), 0) + 1
    print('without overlap: %d, by number of reflectors: %s' % (len(sols), cnt))
    good, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for s, st in pool.imap_unordered(simulate, sols[:maxsim], chunksize=1):
            stats[st] = stats.get(st, 0) + 1
            if st == 'ok':
                good.append(s)
    good.sort(key=lambda s: (len(s['rfs']), s['area']))
    print('simulated %d: %s (%.0f s)' % (min(maxsim, len(sols)), stats, time.time() - t))
    for s in good[:20]:
        print('  K asm %s reflectors %s a=%s b=%s env=%s N=%d' % (tuple(s['asm']), s['rfs'], tuple(s['a'][1:]), tuple(s['b'][1:]), s['env'], s['Te'] - s['Ts']))
    with gzip.open('results/g2_pull.json.gz', 'wt') as f:
        json.dump({'solutions': len(sols), 'stats': stats, 'good': good}, f, separators=(',', ':'))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
