#!/usr/bin/env python3
"""Search 2: blocked streams -- two guns whose glider streams annihilate each other.

The initial configuration, for a signed phase p, is
    evolve pA gun  ∪  translate (dx, dy) (sym_k (evolve pB gun)),
    (pA, pB) = (0, p) if p >= 0,  (-p, 0) if p < 0
(gun A, stream direction (1, 1), and gun B; the gun is that of Guns.lean; for fewer than 30
generations no glider has separated, later the evolved gun carries its gliders in flight).
Negative p is needed for completeness: with p >= 0 only, some annihilating phase classes start
with one unpaired glider that escapes.  Two enumerations of p:
    mode `right`:    -30 < p < 30 (both guns within one period of the gun of Guns.lean);
    mode `centered`: |p - 4 (b - a)| < 30, i.e. -30 < Delta < 30 below: the first gliders of the
                     two guns reach the crossing point within 30 generations of each other.  This
                     is the enumeration that is exhaustive over the periodic configurations.
sym_k is one of the symmetries of life.SYMS:
    right angle:  k = 1, 4  (stream direction (-1, 1)),   k = 3, 5  (stream direction (1, -1));
    head-on:      k = 2, 7  (stream direction (-1, -1)).

Translations.  Let cA = (24, 10) be the centre of the first glider of A (generation 30) and
cB = sym_k(24, 10) + (dx, dy) the centre of the first glider of B (generation 30 - pB).
  right angle: the lanes cross at  P = cA + a (1, 1) = cB + b dB;  all (dx, dy) with
               AMIN <= a, b <= AMAX are enumerated (a and b are both integers or both
               half-integers).
  head-on:     cB - cA = (u, w);  all (dx, dy) with  SMIN <= (u + w) / 2 <= SMAX  (the distance
               between the two emission points along the lane) and |u - w| <= QMAX (lane offset).
All 59 values of p are tried for each translation (head-on: p = 0 .. 29, which is exhaustive
there because the first two gliders always meet).  For a right angle the outcome depends only on
k, the parity of 2a, and
    Delta = 4 (b - a) - p
(arrival time of the first glider of B at the crossing point minus that of A), unless the
guns are so close that a gun body is disturbed.

A triple (k, dx, dy, p) is a solution when the evolution never leaves the box (the bounding box
of the two guns and the crossing point, plus a margin), becomes periodic with period 30 (60, 90,
120 are also detected) and stays so up to generation 3000, with least period 30, and both guns are
undisturbed (compared with the free gun on the rows of the gun body during a whole cycle).

Usage:  s2_blocked.py right [AMIN AMAX]     (default 15 60)
        s2_blocked.py centered [AMIN AMAX]
        s2_blocked.py headon [SMIN SMAX QMAX]   (default 30 120 10)
Output: results/s2_<mode>_<range>.json.gz, summary on stdout.
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

import life
from life import (GUN, Board, bbox, transform, translate, run_periodic, window_of_cells,
                  sym_apply, gun_phase, components, glider_worldline)

TMAX = 3000
MARGIN = 14
CA = (24, 10)
GUN_BODY = (-3, -3, 38, 8)       # rows of the gun body
GUN_ZONE = (-3, -3, 38, 11)      # body and the zone where the glider forms


def rect_cells(r):
    return {(x, y) for x in range(r[0], r[2] + 1) for y in range(r[1], r[3] + 1)}


def phases(p):
    return (0, p) if p >= 0 else (-p, 0)


def gun_at(p):
    """The gun after p generations (any p >= 0), with its gliders in flight."""
    if p < 30:
        return set(gun_phase(p))
    c = set(gun_phase(p % 30))
    for j in range(p // 30):
        c |= life.glider_at((1, 1), 14, -61, p - 30 * j)
    return c


def b_gun(k, dx, dy, p):
    return translate(transform(gun_at(phases(p)[1]), k), dx, dy)


def crossing(k, dx, dy):
    """(a, b, P) doubled: returns (2a, 2b, 2P) for right angle; (u + w, u - w, None) for head-on."""
    d = sym_apply(k, (1, 1))
    c = sym_apply(k, CA)
    vx, vy = c[0] + dx - CA[0], c[1] + dy - CA[1]
    if d == (-1, 1):
        a2, b2 = vx + vy, vx - vy
    elif d == (1, -1):
        a2, b2 = vx + vy, vy - vx
    else:
        return (vx + vy, vx - vy, None)
    return (a2, b2, (2 * CA[0] + a2, 2 * CA[1] + a2))


def analyse(k, dx, dy, p, full=False):
    pA, pB = phases(p)
    A = gun_at(pA)
    B = b_gun(k, dx, dy, p)
    a2, b2, P2 = crossing(k, dx, dy)
    pts = list(A | B)
    if P2 is not None:
        pts.append((P2[0] // 2, P2[1] // 2))
    x0, y0, x1, y1 = bbox(pts)
    bd = Board(x0 - MARGIN, y0 - MARGIN, x1 - x0 + 1 + 2 * MARGIN, y1 - y0 + 1 + 2 * MARGIN)
    if A & B:
        return {'k': k, 'dx': dx, 'dy': dy, 'p': p, 'status': 'overlap'}
    g = bd.of_cells(A | B)
    r = run_periodic(bd, g, tmax=TMAX, periods=(30, 60, 90, 120), give_up=1800)
    out = {'k': k, 'dx': dx, 'dy': dy, 'p': p, 'a2': a2, 'b2': b2, 'status': r['status']}
    if r['status'] != 'periodic':
        out['t'] = r['t']
        return out
    per, t0, hist = r['period'], r['transient'], r['hist']
    out['period'] = per
    out['transient'] = t0
    tref = ((t0 + per - 1) // per) * per
    out['tref'] = tref
    out['min_period'] = min(q for q in range(1, per + 1)
                            if per % q == 0 and hist[tref] == hist[tref + q])
    # guns undisturbed?
    bodyA = bd.of_cells(rect_cells(GUN_BODY) & {c for c in rect_cells(GUN_BODY) if bd.contains(*c, 1)})
    rb = {c for c in translate(transform(rect_cells(GUN_BODY), k), dx, dy) if bd.contains(*c, 1)}
    bodyB = bd.of_cells(rb)
    okA = okB = True
    for s in range(tref, tref + per):
        fa = {c for c in gun_phase((s + pA) % 30) if c[1] <= 8}
        if bd.to_cells(hist[s] & bodyA) != fa:
            okA = False
        fb = translate(transform({c for c in gun_phase((s + pB) % 30) if c[1] <= 8}, k), dx, dy)
        if bd.to_cells(hist[s] & bodyB) != fb:
            okB = False
    out['gunA_intact'] = okA
    out['gunB_intact'] = okB
    cyc = 0
    for s in range(tref, tref + per):
        cyc |= hist[s]
    env = bbox(bd.to_cells(cyc))
    out['envelope'] = list(env)
    out['env_area'] = (env[2] - env[0] + 1) * (env[3] - env[1] + 1)
    out['pop_ref'] = life.popcount(hist[tref])
    # reaction: phases at which some component (cells linked at Chebyshev distance <= 2) is
    # neither a glider nor contained in the zone of a gun (body and forming glider)
    zA = rect_cells(GUN_ZONE)
    zB = translate(transform(zA, k), dx, dy)
    react = set()
    nreact = 0
    for s in range(tref, tref + per):
        bad = False
        for comp in components(bd.to_cells(hist[s]), 2):
            if glider_worldline(comp, s) is None and not comp <= zA and not comp <= zB:
                bad = True
                react |= comp
        nreact += bad
    out['reaction_phases'] = nreact
    out['reaction_bbox'] = list(bbox(react)) if react else None
    if full:
        out['hist'] = hist
        out['board'] = bd
    return out


def work(job):
    return analyse(*job)


def jobs_right(amin, amax, centered=False):
    jobs = []
    for k in (1, 4, 3, 5):
        d = sym_apply(k, (1, 1))
        c = sym_apply(k, CA)
        for a2 in range(2 * amin, 2 * amax + 1):
            for b2 in range(2 * amin, 2 * amax + 1):
                if (a2 - b2) % 2:
                    continue
                # invert `crossing`
                if d == (-1, 1):
                    vx, vy = (a2 + b2) // 2, (a2 - b2) // 2
                else:
                    vx, vy = (a2 - b2) // 2, (a2 + b2) // 2
                dx, dy = vx + CA[0] - c[0], vy + CA[1] - c[1]
                assert crossing(k, dx, dy)[:2] == (a2, b2)
                c0 = 2 * (b2 - a2) if centered else 0
                for p in range(c0 - 29, c0 + 30):
                    jobs.append((k, dx, dy, p))
    return jobs


def jobs_headon(smin, smax, qmax):
    jobs = []
    for k in (2, 7):
        c = sym_apply(k, CA)
        for s2 in range(2 * smin, 2 * smax + 1):
            for q in range(-qmax, qmax + 1):
                if (s2 - q) % 2:
                    continue
                vx, vy = (s2 + q) // 2, (s2 - q) // 2
                dx, dy = vx + CA[0] - c[0], vy + CA[1] - c[1]
                for p in range(30):
                    jobs.append((k, dx, dy, p))
    return jobs


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'right'
    args = [int(x) for x in sys.argv[2:]]
    if mode in ('right', 'centered'):
        amin, amax = args if args else (15, 60)
        jobs = jobs_right(amin, amax, mode == 'centered')
        rng = {'mode': mode, 'AMIN': amin, 'AMAX': amax}
        tag = '%s_%d_%d' % (mode, amin, amax)
    else:
        smin, smax, qmax = args if args else (30, 120, 10)
        jobs = jobs_headon(smin, smax, qmax)
        rng = {'mode': mode, 'SMIN': smin, 'SMAX': smax, 'QMAX': qmax}
        tag = 'headon_%d_%d_%d' % (smin, smax, qmax)
    t = time.time()
    stat = {}
    periodic = []
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for r in pool.imap_unordered(work, jobs, chunksize=100):
            key = r['status']
            if key == 'periodic':
                good = r['min_period'] == r['period'] and r['gunA_intact'] and r['gunB_intact']
                key = 'periodic-%d%s' % (r['period'], '' if good else '-degenerate')
                r['good'] = good
                periodic.append(r)
            stat[key] = stat.get(key, 0) + 1
    dt = time.time() - t
    periodic.sort(key=lambda r: (r['k'], r['dx'], r['dy'], r['p']))
    for r in periodic:
        if mode != 'headon':
            r['cls'] = [r['k'], r['a2'] % 2, 2 * (r['b2'] - r['a2']) - r['p']]
        else:
            r['cls'] = [r['k'], r['b2'], (r['p'] + 2 * r['a2']) % 30]
    summary = {'range': rng, 'margin': MARGIN, 'tmax': TMAX, 'jobs': len(jobs),
               'status_counts': stat, 'seconds': round(dt, 1), 'periodic': periodic}
    os.makedirs('results', exist_ok=True)
    with gzip.open('results/s2_%s.json.gz' % tag, 'wt') as f:
        json.dump(summary, f, separators=(',', ':'))
    print('mode %s range %s: %d jobs, %.1f s' % (mode, rng, len(jobs), dt))
    print('status counts:', dict(sorted(stat.items())))
    for per in (30, 60, 90, 120):
        sols = [r for r in periodic if r['good'] and r['period'] == per]
        if not sols:
            continue
        print('solutions with period %d (guns intact): %d' % (per, len(sols)))
        cnt = {}
        for r in sols:
            key = tuple(r['cls'])
            c = cnt.setdefault(key, [0, set(), set()])
            c[0] += 1
            c[1].add(r['reaction_phases'])
            c[2].add(r['transient'] - 2 * max(r['a2'], r['b2']) if mode != 'headon' else 0)
        print('  classes (k, %s): count, reaction phases, transient - 4 max(a, b)'
              % ('parity of 2a, Delta' if mode != 'headon' else 'lane offset q, (p + 4 s) mod 30'))
        for key in sorted(cnt):
            c = cnt[key]
            print('    %-14s %6d  %s  %s' % (key, c[0], sorted(c[1]), sorted(c[2])[:6]))
        sols.sort(key=lambda r: (r['env_area'], r['transient']))
        print('  most compact (k, dx, dy, p, a, b, transient, envelope, area, reaction phases, reaction box):')
        for r in sols[:40]:
            print('    k=%d d=(%d,%d) p=%d a=%.1f b=%.1f cls=%s t0=%d env=%s area=%d react=%d %s' % (
                r['k'], r['dx'], r['dy'], r['p'], r['a2'] / 2, r['b2'] / 2, r['cls'], r['transient'],
                r['envelope'], r['env_area'], r['reaction_phases'], r['reaction_bbox']))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
