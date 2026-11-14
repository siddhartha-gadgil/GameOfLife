#!/usr/bin/env python3
"""Search F2: fan-out by a round trip.  One control glider in, two gliders out, two assemblies.

Why not f1_fanout.py: a kickback sends the control glider back along the line on which it came,
and a period-30 stream cannot be crossed by a glider at a right angle (r4_stream.py: no phase
passes), so no second assembly can stand on that line between the source and the kicker.  But the
source of the control glider is itself a gate S, and the returning glider X can act on S.

  S  = BS1 (`blockedStream`, world time = 0 mod 30).  The input C0 = (SE, 41, 22) is the control
       glider of the certified gate (Gates.lean): S releases G0 = (SE, 14, 29 mod 30).
  K  = assembly (k, vx, vy, s) placed so that G0 is one of its kickback control gliders (R-20,
       section 3.4): K releases a stream glider G1 and returns G0 as X, which flies back to S.
  X  must be, for S, a gate control glider from infinity that releases a glider G2 of stream B
       (catalogue of s3_gate; a release of stream A would start the round trip again).
Outputs: G1 (from K) and G2 (from S, flying SW).

Enumeration: all 47 kickbacks of the catalogue (from infinity), the symmetries k with
sym_k (direction) = SE, |vx| <= VMAX; conditions as in f1_fanout.py; simulation of the composite
with C0 (bit-parallel board, control glider inserted outside the bounding box; then the set
simulator on the unbounded plane); reuse test with a second C0, T = 30 m later.

Usage: f2_roundtrip.py        Output: results/f2_roundtrip.json.gz, summary on stdout
"""
import gzip
import json
import os
import time
from multiprocessing import Pool

from common import glider_at, bbox, SE, SW, NW, NE, DIRNAME, life
import machine
from machine import load_catalog, wl_map, asm_envelope, box_dist, Composite
from f1_fanout import ray_clear, fast_env

VMAX = 160
SEP = 8
CLEAR = 6
S_ASM = (0, 0, 0, 0)
C0 = (SE, 41, 22)
G0 = (SE, 14, 119)          # released by S for C0 (R-20, G-S); gate time = world time


def candidates(recs):
    envS = asm_envelope(S_ASM)
    table = {}
    for r in recs:
        if r['from_infinity'] and r['kind'] == 'gate' and r['outs'][0][1] == 'B':
            table[(r['d'], r['lane'], r['tau'])] = r
    out = []
    for rK in recs:
        if rK['kind'] != 'kickback' or not rK['from_infinity']:
            continue
        (wS, nS), (wX, nX) = sorted(rK['outs'], key=lambda o: o[1] == 'X')
        for k in range(8):
            if life.sym_apply(k, rK['d']) != SE:
                continue
            d, lane0, tau0 = wl_map(rK['wl'], (k, 0, 0, 0))
            L = G0[1] - lane0
            for vx in range(-VMAX, VMAX + 1):
                vy = d[0] * (d[1] * vx - L)
                s = (G0[2] - tau0 + 4 * d[0] * vx) % 30
                asm = (k, vx, vy, s)
                env = fast_env(asm)
                sep = box_dist(envS, env)
                if sep < SEP:
                    continue
                X = wl_map(wX, asm)
                key = (X[0], X[1], X[2] % 30)
                if key not in table:
                    continue
                G1 = wl_map(wS, asm)
                r2 = table[key]
                G2 = r2['outs'][0][0]
                if ray_clear(G1, envS, 300) < CLEAR or ray_clear((G2[0], G2[1], G2[2] % 30), env, 300, steps=900) < CLEAR:
                    continue
                u = (min(envS[0], env[0]), min(envS[1], env[1]), max(envS[2], env[2]), max(envS[3], env[3]))
                out.append({'asm': asm, 'K': [list(rK['d']), rK['lane'], rK['tau']], 'k': k, 'sep': sep,
                            'X_in_S': [list(X[0]), X[1], X[2] % 30], 'X_repeat': r2['repeat'],
                            'box': u, 'area': (u[2] - u[0] + 1) * (u[3] - u[1] + 1),
                            'G1dir': list(G1[0])})
    return out


def simulate(c):
    asm = tuple(c['asm'])
    try:
        comp = Composite([S_ASM, asm], margin=20)
    except (AssertionError, ValueError):
        return None
    res = machine.run_scheduled(comp, [C0], limit=6000, t_hint=200)
    if res['status'] != 'restored' or len(res['out']) != 2:
        return None
    ok, Ts, Te = machine.verify_scheduled(comp, [C0], res)
    if not ok:
        return None
    outs = sorted(w for (w, th) in res['out'])
    c = dict(c)
    c['t_start'], c['t_end'], c['N'] = Ts, Te, Te - Ts
    c['outs'] = [[list(w[0]), w[1], w[2]] for w in outs]
    c['T'] = None
    for m in range(1, 60):
        w2 = (C0[0], C0[1], C0[2] + 30 * m)
        res2 = machine.run_scheduled(comp, [C0, w2], limit=6000, t_hint=200)
        want = sorted(list(outs) + [(w[0], w[1], w[2] + 30 * m) for w in outs])
        if res2['status'] == 'restored' and sorted(w for (w, th) in res2['out']) == want:
            ok2, Ts2, Te2 = machine.verify_scheduled(comp, [C0, w2], res2)
            if ok2:
                c['T'] = 30 * m
                c['N2'] = Te2 - Ts2
                break
    return c


def main():
    t = time.time()
    recs = load_catalog()
    cands = candidates(recs)
    cands.sort(key=lambda c: c['area'])
    print('candidates (lane, phase and clearance conditions): %d (%.0f s)' % (len(cands), time.time() - t))
    good = []
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for r in pool.imap_unordered(simulate, cands[:600], chunksize=1):
            if r is not None:
                good.append(r)
    good.sort(key=lambda c: (c['T'] is None, c['area']))
    with gzip.open('results/f2_roundtrip.json.gz', 'wt') as f:
        json.dump({'VMAX': VMAX, 'SEP': SEP, 'CLEAR': CLEAR, 'candidates': len(cands), 'good': good},
                  f, separators=(',', ':'))
    print('verified fan-outs: %d (%d reusable), %.0f s' % (len(good), sum(c['T'] is not None for c in good), time.time() - t))
    for c in good[:40]:
        print('  K=%s asm=%s X in S=%s sep=%d box=%s area=%d N=%d T=%s outs=%s' % (
            (DIRNAME[tuple(c['K'][0])], c['K'][1], c['K'][2]), tuple(c['asm']),
            (DIRNAME[tuple(c['X_in_S'][0])], c['X_in_S'][1], c['X_in_S'][2]), c['sep'], c['box'], c['area'],
            c['N'], c['T'], [(DIRNAME[tuple(o[0])], o[1], o[2]) for o in c['outs']]))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
