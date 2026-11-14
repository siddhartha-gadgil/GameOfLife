#!/usr/bin/env python3
"""Search 1: the gun of Guns.lean terminated by one eater 1.

Exhaustive over: the 8 orientations of the eater, and all positions (ex, ey) of the bounding box
origin of the eater with  EX0 <= ex <= EX1,  ey >= EY0  and  |(ex - ey) - 14| <= LANE  (14 is the lane x - y of
the emitted glider), such that the eater is at Chebyshev distance >= 3 from the gun at
generation 0.  A placement is a solution when the evolution from `gun + eater` never leaves the box
and satisfies state(t) = state(t + 30) for all t from a transient t0 up to generation 3000.

Output: results/s1_eater.json.gz and a summary on stdout.
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

import life
from life import (GUN, EATER1, Board, bbox, transform, normalize, translate, run_periodic,
                  window_of_cells, chebyshev_dist)

EX0, EX1, LANE, EY0 = 16, 72, 14, 4
BOARD = (-14, -14, 128, 128)      # x0, y0, W, H
TMAX = 3000

EATERS = [frozenset(normalize(transform(EATER1, k))) for k in range(8)]


def work(job):
    k, ex, ey = job
    eater = translate(EATERS[k], ex, ey)
    if chebyshev_dist(eater, GUN) < 3:
        return None
    b = Board(*BOARD)
    g = b.of_cells(set(GUN) | eater)
    r = run_periodic(b, g, tmax=TMAX, periods=(30, 60, 90, 120), give_up=1500)
    out = {'k': k, 'ex': ex, 'ey': ey, 'status': r['status']}
    if r['status'] != 'periodic':
        out['t'] = r['t']
        return out
    p, t0, hist = r['period'], r['transient'], r['hist']
    out['period'] = p
    out['transient'] = t0
    # reference time: the first multiple of 30 (60 for period 60 ...) that is >= t0
    tref = ((t0 + p - 1) // p) * p
    out['tref'] = tref
    cyc = 0
    for s in range(tref, tref + p):
        cyc |= hist[s]
    env = b.to_cells(cyc)
    out['envelope'] = list(bbox(env))            # bounding box over the whole cycle
    ref = b.to_cells(hist[tref])
    out['ref_window'] = list(window_of_cells(ref))
    out['ref_bbox'] = list(bbox(ref))
    out['pop_ref'] = len(ref)
    # least period (a divisor of p)
    out['min_period'] = min(q for q in range(1, p + 1) if p % q == 0 and hist[tref] == hist[tref + q])
    # is the gun itself undisturbed?  compare with the free gun on the region y <= 8 (the gun
    # body; the glider forms in the rows 9 .. 11) at every generation of one cycle
    gunbox = b.rect_mask(-3, -3, 38, 8)
    out['gun_intact'] = all(
        b.to_cells(hist[s] & gunbox) == {c for c in life.gun_phase(s % 30) if c[1] <= 8}
        for s in range(tref, tref + p))
    # phases of the cycle at which the eater is at rest: all its cells alive and no other live
    # cell within Chebyshev distance 2 of it
    em = b.of_cells(eater)
    halo = b.dilate(em, 2) & ~em
    out['eater_rest_phases'] = sum(
        1 for s in range(tref, tref + p) if hist[s] & em == em and not (hist[s] & halo))
    out['rest'] = sorted(ref - set(GUN) - eater)   # at tref: gliders in flight (and anything else)
    return out


def main():
    jobs = []
    for k in range(8):
        for ex in range(EX0, EX1 + 1):
            for ey in range(ex - 14 - LANE, ex - 14 + LANE + 1):
                if ey >= EY0:
                    jobs.append((k, ex, ey))
    t = time.time()
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        res = pool.map(work, jobs, chunksize=64)
    dt = time.time() - t
    res = [r for r in res if r is not None]
    stat = {}
    for r in res:
        key = r['status'] if r['status'] != 'periodic' else 'periodic-%d' % r['period']
        stat[key] = stat.get(key, 0) + 1
    sols = [r for r in res if r['status'] == 'periodic']
    for r in sols:
        e = r['envelope']
        r['env_w'] = e[2] - e[0] + 1
        r['env_h'] = e[3] - e[1] + 1
        r['env_area'] = r['env_w'] * r['env_h']
    sols.sort(key=lambda r: (r['period'], r['env_area'], r['transient']))
    good = [r for r in sols if r['min_period'] == 30 and r['gun_intact'] and r['eater_rest_phases'] > 0]
    summary = {'range': {'EX0': EX0, 'EX1': EX1, 'LANE': LANE, 'EY0': EY0, 'board': BOARD, 'tmax': TMAX},
               'jobs': len(jobs), 'simulated': len(res), 'status_counts': stat,
               'seconds': round(dt, 1), 'solutions': sols}
    os.makedirs('results', exist_ok=True)
    with gzip.open('results/s1_eater.json.gz', 'wt') as f:
        json.dump(summary, f, separators=(',', ':'))
    print('jobs %d, simulated %d, %.1f s' % (len(jobs), len(res), dt))
    print('status counts:', stat)
    mp = {}
    for r in sols:
        mp[r['min_period']] = mp.get(r['min_period'], 0) + 1
    print('least periods of the periodic outcomes:', mp)
    print('period 30, least period 30, gun intact: %d;  of these with the eater at rest in some phase: %d'
          % (len([r for r in sols if r['min_period'] == 30 and r['gun_intact']]), len(good)))
    print('proper solutions (k, ex, ey, transient, envelope, w x h, eater rest phases, pop at tref):')
    for r in good:
        print('  k=%d (%d,%d) t0=%d env=%s %dx%d=%d rest=%d pop=%d' % (
            r['k'], r['ex'], r['ey'], r['transient'], r['envelope'], r['env_w'],
            r['env_h'], r['env_area'], r['eater_rest_phases'], r['pop_ref']))
    others = [r for r in sols if r['min_period'] == 30 and r not in good]
    print('other outcomes with least period 30 (rows 0 .. 8 of the gun differ from the free gun at some phase): %d'
          % len(others))
    for r in others:
        print('  k=%d (%d,%d) t0=%d env=%s %dx%d=%d rest=%d pop=%d' % (
            r['k'], r['ex'], r['ey'], r['transient'], r['envelope'], r['env_w'],
            r['env_h'], r['env_area'], r['eater_rest_phases'], r['pop_ref']))
    p60 = [r for r in sols if r['period'] == 60 and r['min_period'] == 60 and r['gun_intact']]
    print('period 60 with the gun intact: %d; by orientation: %s' % (
        len(p60), {k: len([r for r in p60 if r['k'] == k]) for k in range(8)}))
    for r in sorted(p60, key=lambda r: (r['env_area'], r['transient']))[:6]:
        print('  k=%d (%d,%d) t0=%d env=%s %dx%d=%d' % (
            r['k'], r['ex'], r['ey'], r['transient'], r['envelope'], r['env_w'], r['env_h'], r['env_area']))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
