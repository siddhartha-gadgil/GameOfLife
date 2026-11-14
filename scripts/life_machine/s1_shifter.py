#!/usr/bin/env python3
"""Search S1: a permanent lane shifter made of two terminated guns.

A terminated gun (R-20, section 1: `gosperGun ∪ translate (25 + n, 11 + n) eater1`, period 30) is
a free-running stream that ends in an eater.  Two of them, mirrored so that their streams fly SW,
are placed across the path of an SE glider g = (SE, 0, 0):
  kick 1: g meets a glider of stream 1 and comes back as an NW glider (kickback),
  kick 2: the NW glider meets a glider of stream 2 and flies SE again, 2 lanes to the left
          (lane -2), later by D generations.
Each stream loses one glider (its eater simply misses one), so the assembly is back in its cycle:
a lane shifter that needs no control glider.  It also has to let g cross stream 2 on the way in
and the shifted glider cross stream 1 on the way out.

Enumeration: positions j1, j2 of the two kicks (reactions.fit); for each, the two units
(k = 4 mirror image of the terminated gun with eater offset N, translated, delayed by s) are
determined up to a slide along their streams, which is fixed by putting the kick in the middle
of the free part of the stream.  Each candidate is simulated: the composite of the two units
must have period 30, and with g it must return to its cycle with exactly one glider leaving,
(SE, -2, D).  Then the reuse test (a second g, T = 30 m later) as in f1_fanout.py.

Usage: s1_shifter.py [N]   (default 24)     Output: stdout, results/s1_shifter.json.gz
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import (GUN, EATER1, translate, transform, step_cells, glider_at, glider_worldline, bbox,
                    SE, SW, NW, NE, DIRNAME, gates, life)
import machine
from machine import box_dist, run_scheduled, verify_scheduled
from reactions import KICK, images, fit

N = 24
KIM = images(KICK)
_unit = {}


def unit_cycle(n):
    """The 30 configurations of the terminated gun with eater at (25 + n, 11 + n), from a
    multiple of 30 after its transient."""
    if n not in _unit:
        c = set(GUN) | translate(EATER1, 25 + n, 11 + n)
        for _ in range(30 * ((4 * n) // 30 + 2)):
            c = step_cells(c)
        cyc = [frozenset(c)]
        for _ in range(29):
            c = step_cells(c)
            cyc.append(frozenset(c))
        assert step_cells(set(cyc[-1])) == set(cyc[0])
        _unit[n] = cyc
    return _unit[n]


def unit_cells(u, t):
    k, vx, vy, s, n = u
    return translate(transform(unit_cycle(n)[(t - s) % 30], k), vx, vy)


def unit_env(u):
    k, vx, vy, s, n = u
    allc = set().union(*unit_cycle(n))
    return bbox(translate(transform(allc, k), vx, vy))


def unit_env_cells(u):
    k, vx, vy, s, n = u
    allc = set().union(*unit_cycle(n))
    return translate(transform(allc, k), vx, vy)


def set_dist(A, B, cap=12):
    """Chebyshev distance between two cell sets, capped at `cap`."""
    Bs = set(B)
    for r in range(cap):
        for (x, y) in A:
            for dx in range(-r, r + 1):
                if (x + dx, y - r) in Bs or (x + dx, y + r) in Bs or (x - r, y + dx) in Bs or (x + r, y + dx) in Bs:
                    return r
    return cap


def unit_stream(u):
    """World line (mod 30 in tau) of the stream of the unit."""
    k, vx, vy, s, n = u
    c = translate(transform(glider_at(SE, 14, 29, 0), k), vx, vy)
    return glider_worldline(c, s)


def kick(main, kdir, j):
    for im in KIM:
        if im[0][0][0] == main[0] and im[0][1][0] == kdir:
            ins, outs = fit(im, 0, main, j)
            return ins[1], outs[0]
    raise ValueError


def place_unit(kicker, main, n, k=4):
    """The unit (k, vx, vy, s, n) whose stream contains the glider `kicker`, with the meeting
    point of kicker and main glider in the middle of the free part of the stream."""
    base = unit_stream((k, 0, 0, 0, n))
    d = base[0]
    assert d == kicker[0]
    # meeting point of the two world lines
    (dm, lm, tm), (dk, lk, tk) = main, kicker
    if dm[0] != dk[0]:
        ts = (dm[0] * tm - dk[0] * tk) / (dm[0] - dk[0])
    else:
        # y(t) = dy (t - tau) / 4 - dx lane
        ts = (dm[1] * tm - dk[1] * tk + 4 * (dm[0] * lm - dk[0] * lk)) / (dm[1] - dk[1])
    xs = dk[0] * (ts - tk) / 4
    # in base coordinates the middle of the free stream is at x = 24 + n / 2 + 1
    xb = 25 + n // 2
    (a, b), (c, e) = life.SYMS[k]
    assert b == 0                       # k = 4: x -> -x
    vx = int(round(xs - a * xb))
    # lane: d[1] x - d[0] y changes by d[1] vx - d[0] vy
    vy = (d[1] * vx - (kicker[1] - base[1])) * d[0]
    s = (kicker[2] - base[2] + 4 * d[0] * vx) % 30
    u = (k, vx, vy, s, n)
    w = unit_stream(u)
    assert w[1] == kicker[1] and (w[2] - kicker[2]) % 30 == 0, (w, kicker)
    return u


class Comp:
    """Minimal stand-in for machine.Composite built from arbitrary periodic cells."""

    def __init__(self, cells, margin=20):
        self.R = gates.Reference(cells, margin)


def candidate(job):
    j1, j2, n = job
    g = (SE, 0, 0)
    k1, m = kick(g, SW, j1)
    k2, out = kick(m, SW, j2)
    u1 = place_unit(k1, g, n)
    u2 = place_unit(k2, m, n)
    sep = set_dist(unit_env_cells(u1), unit_env_cells(u2))
    rec = {'j1': j1, 'j2': j2, 'n': n, 'u1': u1, 'u2': u2, 'sep': sep, 'out': out, 'k1': k1, 'k2': k2}
    if sep < 6:
        rec['status'] = 'too close'
        return rec
    c1, c2 = unit_cells(u1, 0), unit_cells(u2, 0)
    if c1 & c2:
        rec['status'] = 'overlap'
        return rec
    try:
        comp = Comp(set(c1) | set(c2))
    except AssertionError:
        rec['status'] = 'not periodic'
        return rec
    res = run_scheduled(comp, [g], limit=3000)
    rec['status'] = res['status']
    if res['status'] != 'restored':
        return rec
    outs = sorted(w for (w, th) in res['out'])
    rec['outs'] = outs
    if outs != [out]:
        rec['status'] = 'other gliders'
        return rec
    ok, Ts, Te = verify_scheduled(comp, [g], res)
    if not ok:
        rec['status'] = 'verification failed'
        return rec
    rec['status'] = 'shifter'
    rec['Ts'], rec['Te'] = Ts, Te
    rec['env'] = comp.R.env
    rec['T'] = None
    for mm in range(1, 40):
        g2 = (SE, 0, 30 * mm)
        r2 = run_scheduled(comp, [g, g2], limit=3000)
        want = sorted([out, (out[0], out[1], out[2] + 30 * mm)])
        if r2['status'] == 'restored' and sorted(w for (w, th) in r2['out']) == want:
            if verify_scheduled(comp, [g, g2], r2)[0]:
                rec['T'] = 30 * mm
                break
    return rec


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else N
    jobs = [(j1, j2, n) for j1 in range(-8, 9) for j2 in range(0, 60)]
    t = time.time()
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        recs = pool.map(candidate, jobs, chunksize=4)
    cnt = {}
    for r in recs:
        cnt[r['status']] = cnt.get(r['status'], 0) + 1
    print('eater offset n = %d; candidates %d; outcomes %s; %.0f s' % (n, len(jobs), cnt, time.time() - t))
    good = [r for r in recs if r['status'] == 'shifter']
    good.sort(key=lambda r: (r['T'] is None, (r['env'][2] - r['env'][0]) * (r['env'][3] - r['env'][1])))
    for r in good[:25]:
        e = r['env']
        print('  j1=%d j2=%d units %s %s sep=%d env=%s (%dx%d) out=%s N=%d reuse T=%s' % (
            r['j1'], r['j2'], r['u1'], r['u2'], r['sep'], e, e[2] - e[0] + 1, e[3] - e[1] + 1,
            (DIRNAME[r['out'][0]], r['out'][1], r['out'][2]), r['Te'] - r['Ts'], r['T']))
    with gzip.open('results/s1_shifter_%d.json.gz' % n, 'wt') as f:
        json.dump({'n': n, 'counts': cnt, 'good': good}, f, separators=(',', ':'), default=list)


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
