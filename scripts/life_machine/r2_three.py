#!/usr/bin/env python3
"""Search R2: all collisions of three gliders SE + SW + NE (one of each; any timing).

Up to translation in space and time: SE = (lane 0, tau 0); SW on lane w in {0, 1} with
tau = 4 w + i, |i| <= IMAX (SE and SW come within a few cells of each other); NE on every lane and
with every tau for which it comes within distance 5 of the SE glider or of the SW glider (flying
alone) during the window of times [t_meet - PRE, t_meet + POST] (t_meet = time at which SE and SW
are closest).  This contains every slow recipe of r1 with three gliders whose third glider
arrives at most POST generations after the first two meet, and all simultaneous collisions.

A triple is recorded when the configuration settles (recipes.settle) with nothing left but
gliders, and the outcome is not that of the three gliders flying on undisturbed.

Usage: r2_three.py        Output: results/r2_three.json.gz
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import glider_at, bbox, SE, SW, NE, NW, DIRNAME
from recipes import settle, _cheb_box

IMAX = 44
PRE = 24
POST = 130


def gbox(wl, t):
    return bbox(glider_at(*wl, t))


def jobs():
    out = []
    for w in (0, 1):
        for i in range(-IMAX, IMAX + 1):
            out.append((w, 4 * w + i))
    return out


def work(job):
    w, tw = job
    e = (SE, 0, 0)
    s = (SW, w, tw)
    tm = tw // 2                               # x equal: t/4 = (tw - t)/4
    x0 = tm // 4
    t_lo, t_hi = tm - PRE, tm + POST
    # NE gliders: x = (t - tau)/4, y = -n - x
    found = []
    runs = 0
    eb = {t: gbox(e, t) for t in range(t_lo, t_hi + 1)}
    sb = {t: gbox(s, t) for t in range(t_lo, t_hi + 1)}
    cands = set()
    for t in range(t_lo, t_hi + 1):
        for b in (eb[t], sb[t]):
            # NE glider boxes within distance 5 of b at time t: canonical parameter q, lane n
            for x in range(b[0] - 8, b[2] + 6):
                for y in range(b[1] - 8, b[3] + 6):
                    for j in range(4):
                        # glider canonical at time t - j at (x, y): tau = t - j - 4 x, lane = -x - y
                        cands.add((-x - y, t - j - 4 * x))
    for (n, tn) in sorted(cands):
        c = (NE, n, tn)
        # start: a time at which all three are pairwise >= 6 apart and were before
        t0 = None
        for t in range(tm - 400, tm + 400):
            b1, b2, b3 = gbox(e, t), gbox(s, t), gbox(c, t)
            if min(_cheb_box(b1, b2), _cheb_box(b1, b3), _cheb_box(b2, b3)) < 6:
                break
            t0 = t
        if t0 is None:
            continue
        cells = glider_at(*e, t0) | glider_at(*s, t0) | glider_at(*c, t0)
        st, t, rest, gl = settle(cells, t0, max_gen=700)
        runs += 1
        if st != 'settled' or rest:
            continue
        if sorted(gl) == sorted([e, s, c]):
            continue
        found.append({'in': [e, s, c], 'out': gl})
    return found, runs


def main():
    t = time.time()
    found, runs = [], 0
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for f, r in pool.imap_unordered(work, jobs(), chunksize=1):
            found.extend(f)
            runs += r
    dt = time.time() - t
    with gzip.open('results/r2_three.json.gz', 'wt') as f:
        json.dump({'IMAX': IMAX, 'PRE': PRE, 'POST': POST, 'runs': runs, 'seconds': round(dt, 1),
                   'recipes': found}, f, separators=(',', ':'))
    print('runs %d, outcomes with gliders only (and some interaction): %d, %.1f s' % (runs, len(found), dt))
    summary(found)


def summary(found):
    cnt = {}
    for r in found:
        key = ' '.join(sorted(DIRNAME[tuple(o[0])] for o in r['out'])) or '(nothing)'
        cnt[key] = cnt.get(key, 0) + 1
    print('by output directions:')
    for k in sorted(cnt):
        print('   %-20s %d' % (k, cnt[k]))
    print('single SE glider out: lane shift (relative to the SE input), tau shift: count')
    c2 = {}
    for r in found:
        if len(r['out']) == 1 and tuple(r['out'][0][0]) == SE:
            key = (r['out'][0][1], r['out'][0][2])
            c2[key] = c2.get(key, 0) + 1
    for k in sorted(c2):
        print('   lane %+d tau %+d: %d' % (k[0], k[1], c2[k]))
    print('two SE gliders out: (lane difference, tau difference) : count   [pull salvo = (6, -29)]')
    c3 = {}
    for r in found:
        se = sorted((o[1], o[2]) for o in r['out'] if tuple(o[0]) == SE)
        if len(se) == 2:
            key = (se[1][0] - se[0][0], se[1][1] - se[0][1], len(r['out']))
            c3[key] = c3.get(key, 0) + 1
    for k in sorted(c3):
        print('   ', k, c3[k])


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    if len(sys.argv) == 3 and sys.argv[1] == 'summary':
        summary(json.load(gzip.open(sys.argv[2], 'rt'))['recipes'])
    else:
        main()
