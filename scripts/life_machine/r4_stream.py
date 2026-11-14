#!/usr/bin/env python3
"""Search R4: gated gliders against a free-running period-30 stream.

The stream flies SW on lane 0: gliders (SW, 0, 30 j), j = 0 .. NS-1 (a finite piece; the test
requires the last gliders of the piece to fly on undisturbed, so the outcome is that of an
infinite stream).

mode `one`  : one glider against the stream.
              SE on lane 0 or 1 with tau = 0 .. 29 (all classes up to the symmetry of the stream);
              NE (head-on) on the lanes |c| <= 12 with tau = 0, 1.
              (NW is the mirror image of SE.)
mode `two`  : two gliders SE (lane 0, tau 0) and NE (lane n in {0, 1}, tau = i, |i| <= 44)
              against a stream SW on every lane and with every phase that brings a stream glider
              within distance 6 of the place and time at which the two meet.
Recorded: runs that settle with gliders only, in which the stream gliders from some index on are
intact, and at least one glider other than stream gliders and the unchanged inputs leaves.

Usage: r4_stream.py one | two      Output: results/r4_stream_<mode>.json.gz
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import glider_at, bbox, SE, SW, NE, NW, DIRNAME
from recipes import settle, _cheb_box

NS = 12


def run(inputs, stream, t0, max_gen=1200):
    """inputs, stream: lists of world lines.  Returns None or a record."""
    cells = set()
    for w in inputs + stream:
        cells |= glider_at(*w, t0)
    st, t, rest, gl = settle(cells, t0, max_gen=max_gen, max_pop=200, max_span=140)
    if st != 'settled':
        return 'fail'
    if rest:
        return 'rest'
    gl = [tuple(g) for g in gl]
    ss = set(stream)
    surv = [w in gl for w in stream]
    # the stream must be intact from some index on (at least the last 3 gliders)
    j0 = len(stream)
    while j0 > 0 and surv[j0 - 1]:
        j0 -= 1
    if len(stream) - j0 < 3:
        return 'stream'
    others = [g for g in gl if g not in ss]
    if sorted(others) == sorted(inputs):
        return 'pass'
    new = [g for g in others if g not in inputs]
    if not new:
        return 'absorbed'
    return {'in': inputs, 'stream': [stream[0][0], stream[0][1], stream[0][2] % 30],
            'consumed': j0 - sum(surv[:j0]), 'first_intact': j0,
            'stream_survivors_before': sum(surv[:j0]), 'out': others}


def work_one(job):
    d, lane, tau = job
    stream = [(SW, 0, 30 * j) for j in range(NS)]
    g = (d, lane, tau)
    if d == SE:
        g = (d, lane, tau + 60)          # meets the stream around its gliders 2, 3
        t0 = 0
    else:
        t0 = -40
    return job, run([g], stream, t0)


def two_jobs():
    return [(n, i) for n in (0, 1) for i in range(-44, 45)]


def work_two(job):
    n, i = job
    e = (SE, 0, 0)
    c = (NE, n, i)
    # e: x = t/4, y = x.  c: x = (t - i)/4, y = -n - x.  They are closest near t = -2 n.
    tm = -2 * n
    out = []
    stats = {}
    # stream SW on lane w with phase p: glider j at x = (p + 30 j - t)/4, y = w - x.
    # near the meeting point (x ~ tm/4, y ~ tm/4): w ~ tm/2
    for w in range(tm // 2 - 16, tm // 2 + 17):
        for p in range(30):
            # glider index j0 such that the stream glider is near the meeting point at time tm:
            # p + 30 j - tm ~ tm  ->  j ~ (2 tm - p) / 30 ; take the stream from 3 gliders earlier
            jb = (2 * tm - p) // 30 - 3
            stream = [(SW, w, p + 30 * j) for j in range(jb, jb + NS)]
            t0 = tm - 60
            # e and c must still be far apart at t0 (they approach at a right angle)
            r = run([e, c], stream, t0)
            key = r if isinstance(r, str) else 'recorded'
            stats[key] = stats.get(key, 0) + 1
            if not isinstance(r, str):
                out.append(r)
    return out, stats


def main():
    mode = sys.argv[1]
    t = time.time()
    found, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        if mode == 'one':
            jobs = [(SE, l, tau) for l in (0, 1) for tau in range(30)] + \
                   [(NE, c, tau) for c in range(-12, 13) for tau in (0, 1)]
            for job, r in pool.imap_unordered(work_one, jobs):
                key = r if isinstance(r, str) else 'recorded'
                stats[key] = stats.get(key, 0) + 1
                if not isinstance(r, str):
                    found.append(r)
        else:
            for f, s in pool.imap_unordered(work_two, two_jobs(), chunksize=1):
                found.extend(f)
                for k, v in s.items():
                    stats[k] = stats.get(k, 0) + v
    dt = time.time() - t
    with gzip.open('results/r4_stream_%s.json.gz' % mode, 'wt') as f:
        json.dump({'mode': mode, 'NS': NS, 'stats': stats, 'seconds': round(dt, 1), 'recipes': found},
                  f, separators=(',', ':'))
    print('mode %s: outcomes %s, %.1f s' % (mode, stats, dt))
    cnt = {}
    for r in found:
        new = [g for g in r['out'] if g not in [tuple(x) for x in r['in']]]
        key = (r['consumed'], ' '.join(sorted(DIRNAME[tuple(o[0])] for o in new)))
        cnt[key] = cnt.get(key, 0) + 1
    print('recorded, by (stream gliders consumed, directions of the new gliders):')
    for k in sorted(cnt):
        print('   ', k, cnt[k])
    for r in found:
        new = [g for g in r['out'] if g not in [tuple(x) for x in r['in']]]
        if len(new) == 1 and tuple(new[0][0]) != SW and len(new) == len(r['out']):
            print('   in', [(DIRNAME[tuple(w[0])], w[1], w[2]) for w in r['in']], 'stream', (r['stream'][1], r['stream'][2]),
                  'consumed', r['consumed'], 'out', [(DIRNAME[tuple(o[0])], o[1], o[2]) for o in new])


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
