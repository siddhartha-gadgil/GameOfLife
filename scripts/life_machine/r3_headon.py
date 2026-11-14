#!/usr/bin/env python3
"""Search R3: two head-on gated streams (pure insertion from the two sides).

Gliders W_a = (SW, lane 0, tau 30 a), a in A, and N_b = (NE, lane c, tau i + 30 b), b in B, for
all nonempty A, B contained in {0, .., K-1}, all lane offsets |c| <= CMAX and i = 0 .. 7 (the
classes of a head-on pair up to translation).  These are exactly the gliders that two gates
facing each other can release.  Recorded: outcomes that settle with gliders only and contain a
glider flying SE or NW (at a right angle to the two lanes).

Usage: r3_headon.py [K]   (default 4)      Output: results/r3_headon_<K>.json.gz
"""
import gzip
import itertools
import json
import os
import sys
import time
from multiprocessing import Pool

from common import glider_at, bbox, SE, SW, NE, NW, DIRNAME
from recipes import settle, _cheb_box

CMAX = 12
K = 4


def subsets(k):
    out = []
    for r in range(1, k + 1):
        out.extend(itertools.combinations(range(k), r))
    return out


def work(job):
    c, i, k = job
    found = []
    stats = {}
    subs = subsets(k)
    for A in subs:
        for B in subs:
            wls = [(SW, 0, 30 * a) for a in A] + [(NE, c, i + 30 * b) for b in B]
            if len(wls) < 3:
                continue
            # start: last time at which all gliders are pairwise >= 6 apart, and were before
            t0 = None
            for t in range(-200, 400):
                bs = [bbox(glider_at(*w, t)) for w in wls]
                if any(_cheb_box(bs[p], bs[q]) < 6 for p in range(len(bs)) for q in range(p)):
                    break
                t0 = t
            if t0 is None:
                continue
            cells = set()
            for w in wls:
                cells |= glider_at(*w, t0)
            st, t, rest, gl = settle(cells, t0, max_gen=900)
            key = st if st != 'settled' else ('rest' if rest else 'gliders')
            stats[key] = stats.get(key, 0) + 1
            if st != 'settled' or rest:
                continue
            if any(tuple(g[0]) in (SE, NW) for g in gl):
                found.append({'in': wls, 'out': gl})
    return found, stats


def main():
    global K
    if len(sys.argv) > 1:
        K = int(sys.argv[1])
    t = time.time()
    jobs = [(c, i, K) for c in range(-CMAX, CMAX + 1) for i in range(8)]
    found, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for f, s in pool.imap_unordered(work, jobs, chunksize=1):
            found.extend(f)
            for k, v in s.items():
                stats[k] = stats.get(k, 0) + v
    dt = time.time() - t
    with gzip.open('results/r3_headon_%d.json.gz' % K, 'wt') as f:
        json.dump({'K': K, 'CMAX': CMAX, 'stats': stats, 'seconds': round(dt, 1), 'recipes': found},
                  f, separators=(',', ':'))
    print('K = %d: runs by outcome %s; with a glider at a right angle: %d; %.1f s' % (K, stats, len(found), dt))
    cnt = {}
    for r in found:
        key = (len(r['in']), ' '.join(sorted(DIRNAME[tuple(o[0])] for o in r['out'])))
        cnt[key] = cnt.get(key, 0) + 1
    for k in sorted(cnt):
        print('   ', k, cnt[k])
    for r in found:
        if len(r['out']) <= 2:
            print('   in', [(DIRNAME[tuple(w[0])], w[1], w[2]) for w in r['in']],
                  'out', [(DIRNAME[tuple(o[0])], o[1], o[2]) for o in r['out']])


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
