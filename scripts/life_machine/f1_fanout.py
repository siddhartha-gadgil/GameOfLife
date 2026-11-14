#!/usr/bin/env python3
"""Search F1: fan-out.  One control glider C in, two gliders out, two assemblies.

Assembly 1 is BS1 itself (`blockedStream` at world times = 0 mod 30).  C is one of the kickback
control gliders of BS1 (R-20, section 3.4): it deletes one glider of a stream, the partner
glider G1 escapes, and C comes back as a glider X.  Assembly 2 = (k, vx, vy, s) (machine.py) is
placed so that X is, in its coordinates, a repeatable gate control glider arriving from infinity;
it releases G2.  Enumeration: every kickback of BS1 from infinity (or the one given), every
symmetry k and every repeatable gate r of the catalogue with sym_k (direction of r) = direction
of X, every translation along X with |vx| <= VMAX (vy and s are then determined) and bounding box of the two
envelopes of area <= AREA_MAX, subject to
  * the envelopes of the two assemblies are at least SEP apart,
  * the lanes of G1 and G2 (after release) stay at least CLEAR away from the other envelope,
  * C, which flies in on (almost) the line on which X flies back, passes through assembly 2
    unchanged (tested for assembly 2 alone, then in the composite).
The NSIM candidates with the smallest bounding box (at most PERCLASS for each (k, direction of
G2)) are simulated: the composite must have period 30; with C it must return to its cycle with
exactly G1 and G2 in free flight (bit-parallel board, then the set simulator on the unbounded
plane); finally the smallest T = 30 m for which a second C, T generations later, also works.

Usage: f1_fanout.py [KLANE KTAU]     Output: results/f1_fanout.json.gz, summary on stdout
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import glider_at, bbox, SE, SW, NW, NE, DIRNAME, life
import machine
from machine import (load_catalog, wl_map, asm_envelope, box_dist, Composite)

VMAX = 220
SEP = 10
CLEAR = 6
NSIM = 400
AREA_MAX = 30000
PERCLASS = 40
ASM1 = (0, 0, 0, 0)


def ray_clear(wl, box, t_from, forward=True, steps=700):
    """Minimum distance between the glider (world line wl) and the box at the times
    t_from, t_from +- 4, ... (steps samples)."""
    d, lane, tau = wl
    best = 10 ** 9
    for i in range(steps):
        t = t_from + (4 * i if forward else -4 * i)
        q = (t - tau) // 4
        x = d[0] * q
        y = d[0] * (d[1] * x - lane)
        dd = box_dist((x - 1, y - 1, x + 3, y + 3), box)
        if dd < best:
            best = dd
    return best


_ENV0 = {}


def fast_env(asm):
    k, vx, vy, s = asm
    if k not in _ENV0:
        _ENV0[k] = asm_envelope((k, 0, 0, 0))
    e = _ENV0[k]
    return (e[0] + vx, e[1] + vy, e[2] + vx, e[3] + vy)


_R1 = None


def passes(key):
    """Does the glider (d, lane, tau) fly through BS1 (in its cycle) unchanged?"""
    global _R1
    if _R1 is None:
        _R1 = machine.gates.Reference(set(machine.bs1_cycle()[0]))
    R = _R1
    d, lane, tau = key
    ivs, t_in, t_out = machine.gates.free_intervals(R, d, lane, tau)
    if not ivs:
        return key, False
    if len(ivs) == 1 and ivs[0] == (t_in, t_out):
        return key, True
    if ivs[0][0] != t_in:
        return key, False
    res = machine.gates.run_gate(R, [key], ivs[0][1], limit=900)
    ok = (res['status'] == 'restored' and [w for (w, th) in res['out']] == [key])
    return key, ok


def candidates(recs, rK):
    env1 = asm_envelope(ASM1)
    wC = rK['wl']
    (wS, nS), (wX, nX) = sorted(rK['outs'], key=lambda o: o[1] == 'X')
    assert nX == 'X'
    out = []
    for r2 in recs:
        if r2['kind'] != 'gate' or not r2['from_infinity'] or len(r2['repeat']) != 3:
            continue
        for k in range(8):
            if life.sym_apply(k, r2['d']) != wX[0]:
                continue
            d, lane0, tau0 = wl_map(r2['wl'], (k, 0, 0, 0))
            L = wX[1] - lane0
            for vx in range(-VMAX, VMAX + 1):
                vy = d[0] * (d[1] * vx - L)
                s = (wX[2] - tau0 + 4 * d[0] * vx) % 30
                asm2 = (k, vx, vy, s)
                env2 = fast_env(asm2)
                sep = box_dist(env1, env2)
                if sep < SEP:
                    continue
                if abs(vx) + abs(vy) > 2 * VMAX:
                    continue
                u = (min(env1[0], env2[0]), min(env1[1], env2[1]), max(env1[2], env2[2]), max(env1[3], env2[3]))
                area = (u[2] - u[0] + 1) * (u[3] - u[1] + 1)
                if area > AREA_MAX:
                    continue
                w2 = wl_map(r2['outs'][0][0], asm2)
                t_rel = rK['t_back']
                wc2 = machine.wl_unmap(wC, asm2)
                ckey = (wc2[0], wc2[1], wc2[2] % 30)
                if ray_clear(wS, env2, t_rel) < CLEAR:
                    continue
                if ray_clear(w2, env1, t_rel) < CLEAR:
                    continue
                out.append({'asm2': asm2, 'r2': [list(r2['d']), r2['lane'], r2['tau']], 'k': k,
                            'sep': sep, 'area': area, 'box': u, 'g2dir': list(w2[0]),
                            'K': [list(wC[0]), wC[1], wC[2]], 't_ins': rK['t_ins'], 'ckey': ckey})
    return out


def simulate(c):
    asm2 = tuple(c['asm2'])
    wC = (tuple(c['K'][0]), c['K'][1], c['K'][2])
    try:
        comp = Composite([ASM1, asm2], margin=20)
    except (AssertionError, ValueError):
        return None
    # C enters from outside the bounding box of the whole composite (it flies through assembly 2)
    res = machine.run_scheduled(comp, [wC], limit=5000, t_hint=c['t_ins'])
    if res['status'] != 'restored' or len(res['out']) != 2:
        return None
    ok, Ts, Te = machine.verify_scheduled(comp, [wC], res)
    if not ok:
        return None
    outs = sorted(w for (w, th) in res['out'])
    c = dict(c)
    c['t_start'], c['t_end'], c['N'] = Ts, Te, Te - Ts
    c['outs'] = [[list(w[0]), w[1], w[2]] for w in outs]
    # reuse: second control glider T = 30 m later
    c['T'] = None
    for m in range(1, 80):
        w2 = (wC[0], wC[1], wC[2] + 30 * m)
        res2 = machine.run_scheduled(comp, [wC, w2], limit=5000, t_hint=c['t_ins'])
        want = sorted(list(outs) + [(w[0], w[1], w[2] + 30 * m) for w in outs])
        if res2['status'] == 'restored' and sorted(w for (w, th) in res2['out']) == want:
            ok2, Ts2, Te2 = machine.verify_scheduled(comp, [wC, w2], res2)
            if ok2:
                c['T'] = 30 * m
                c['N2'] = Te2 - Ts2
                break
    return c


def main():
    recs = load_catalog()
    kicks = [r for r in recs if r['kind'] == 'kickback' and r['from_infinity']]
    if len(sys.argv) >= 3:
        kl, kt = int(sys.argv[1]), int(sys.argv[2])
        kicks = [r for r in kicks if r['lane'] == kl and r['tau'] == kt]
    t = time.time()
    cands = []
    for rK in kicks:
        cands.extend(candidates(recs, rK))
    print('kickbacks used: %d; candidates after the geometric filters: %d (%.0f s)' % (len(kicks), len(cands), time.time() - t))
    keys = sorted({c['ckey'] for c in cands})
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        ptab = dict(pool.imap_unordered(passes, keys, chunksize=8))
    cands = [c for c in cands if ptab[c['ckey']]]
    for c in cands:
        del c['ckey']
    print('C flies through assembly 2 unchanged (%d of %d world lines pass): %d candidates (%.0f s)' % (
        sum(ptab.values()), len(keys), len(cands), time.time() - t))
    cands.sort(key=lambda c: c['area'])
    sel, per = [], {}
    for c in cands:
        key = (c['k'], tuple(c['g2dir']), tuple(c['K']) if False else tuple(c['K'][0]))
        if per.get(key, 0) >= PERCLASS:
            continue
        per[key] = per.get(key, 0) + 1
        sel.append(c)
    sel = sel[:NSIM] if len(per) <= 1 else sel
    print('simulating %d candidates' % len(sel))
    good = []
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for r in pool.imap_unordered(simulate, sel, chunksize=1):
            if r is not None:
                good.append(r)
    good.sort(key=lambda c: (c['T'] is None, c['area']))
    dt = time.time() - t
    with gzip.open('results/f1_fanout.json.gz', 'wt') as f:
        json.dump({'VMAX': VMAX, 'SEP': SEP, 'CLEAR': CLEAR, 'candidates': len(cands),
                   'simulated': len(sel), 'seconds': round(dt, 1), 'good': good}, f, separators=(',', ':'))
    print('verified fan-outs: %d (%d reusable), %.0f s' % (len(good), sum(c['T'] is not None for c in good), dt))
    for c in good[:60]:
        print('  C=%s asm2=%s r2=%s sep=%d box=%s area=%d N=%d T=%s outs=%s' % (
            (DIRNAME[tuple(c['K'][0])], c['K'][1], c['K'][2]), tuple(c['asm2']),
            (DIRNAME[tuple(c['r2'][0])], c['r2'][1], c['r2'][2]), c['sep'], c['box'], c['area'],
            c['N'], c['T'], [(DIRNAME[tuple(o[0])], o[1], o[2]) for o in c['outs']]))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
