#!/usr/bin/env python3
"""Tables for report R-20 from a result file of s2_blocked.py.

Usage: s2_summary.py results/s2_<mode>_<range>.json.gz
"""
import collections
import gzip
import json
import sys


def line(r):
    if r['cls'][0] in (2, 7):
        return ('k=%d d=(%d,%d) p=%d s=%.1f q=%d cls=%s t0=%d env=%s %dx%d=%d react=%d %s' % (
            r['k'], r['dx'], r['dy'], r['p'], r['a2'] / 2, r['b2'], r['cls'], r['transient'],
            r['envelope'], r['envelope'][2] - r['envelope'][0] + 1,
            r['envelope'][3] - r['envelope'][1] + 1, r['env_area'], r['reaction_phases'],
            r['reaction_bbox']))
    return ('k=%d d=(%d,%d) p=%d a=%.1f b=%.1f cls=%s t0=%d env=%s %dx%d=%d react=%d %s' % (
        r['k'], r['dx'], r['dy'], r['p'], r['a2'] / 2, r['b2'] / 2, r['cls'], r['transient'],
        r['envelope'], r['envelope'][2] - r['envelope'][0] + 1,
        r['envelope'][3] - r['envelope'][1] + 1, r['env_area'], r['reaction_phases'],
        r['reaction_bbox']))


def main():
    d = json.load(gzip.open(sys.argv[1], 'rt'))
    P = d['periodic']
    mode = d['range']['mode']
    print('file', sys.argv[1], 'range', d['range'], 'jobs', d['jobs'], 'seconds', d['seconds'])
    print('status counts', dict(sorted(d['status_counts'].items())))
    deg = collections.Counter((r['period'], r['min_period'], r['gunA_intact'], r['gunB_intact'])
                              for r in P if not r['good'])
    print('degenerate periodic outcomes (period found, least period, gun A intact, gun B intact): count')
    for k in sorted(deg):
        print('   ', k, deg[k])
    good = [r for r in P if r['good'] and r['period'] == 30]
    clean = [r for r in good if r['reaction_phases'] < 30]
    print('period 30, guns intact: %d; of these without permanent debris (some phase consists of guns and gliders only): %d'
          % (len(good), len(clean)))
    if mode != 'headon':
        lo, hi = 2 * d['range']['AMIN'], 2 * d['range']['AMAX']
        per = collections.Counter((r['k'], r['a2'], r['b2']) for r in good)
        cls = collections.defaultdict(set)
        for r in good:
            cls[(r['k'], r['a2'] % 2)].add(r['cls'][2])
        print('values of Delta per (k, parity of 2a) [those realised for at least half of the translations]:')
        gen = {}
        for k in (1, 3, 4, 5):
            for par in (0, 1):
                n = collections.Counter(r['cls'][2] for r in good if r['k'] == k and r['a2'] % 2 == par)
                top = max(n.values()) if n else 0
                gen[(k, par)] = sorted(x for x in n if 2 * n[x] >= top)
                rare = sorted((x, n[x]) for x in n if 2 * n[x] < top)
                print('   k=%d parity %d: %s   rare: %s' % (k, par, gen[(k, par)], rare))
        print('translations (a, b) in the range whose number of solutions differs from the generic number:')
        for k in (1, 3, 4, 5):
            bad = []
            tot = 0
            for a2 in range(lo, hi + 1):
                for b2 in range(lo, hi + 1):
                    if (a2 - b2) % 2 == 0:
                        tot += 1
                        if per.get((k, a2, b2), 0) != len(gen[(k, a2 % 2)]):
                            bad.append((a2 / 2, b2 / 2, per.get((k, a2, b2), 0)))
            okab = [(a, b) for (a, b, n) in bad]
            # smallest m such that every translation with a, b >= m is generic
            m = max([min(a, b) for (a, b) in okab], default=None)
            print('   k=%d: %d of %d translations; all translations with min(a, b) > %s are generic' % (k, len(bad), tot, m))
    else:
        tab = collections.defaultdict(lambda: [set(), 0, 0, collections.Counter()])
        for r in good:
            t = tab[(r['k'], r['cls'][1])]
            t[0].add(r['cls'][2])
            t[1] += 1
            t[2] += r['reaction_phases'] < 30
            t[3][r['reaction_phases']] += 1
        print('(k, lane offset q): number of phase classes (p + 4 s) mod 30 with a solution, solutions, clean solutions, {reaction phases: count}')
        for key in sorted(tab):
            t = tab[key]
            print('   %s: %d classes, %d, %d, %s' % (key, len(t[0]), t[1], t[2], dict(sorted(t[3].items()))))
        for per_ in (60, 90, 120):
            g = [r for r in P if r['good'] and r['period'] == per_]
            c = collections.Counter((r['k'], r['cls'][1]) for r in g)
            print('period %d, guns intact: %d, by (k, q): %s' % (per_, len(g), dict(sorted(c.items()))))
    print('most compact clean solutions, for each k:')
    for k in sorted(set(r['k'] for r in clean)):
        rr = sorted([r for r in clean if r['k'] == k], key=lambda r: (r['env_area'], r['transient']))
        for r in rr[:4]:
            print('   ', line(r))
    print('most compact clean solutions with p = 0 (both guns at generation 0), for each k:')
    for k in sorted(set(r['k'] for r in clean)):
        rr = sorted([r for r in clean if r['k'] == k and r['p'] == 0], key=lambda r: (r['env_area'], r['transient']))
        for r in rr[:4]:
            print('   ', line(r))
    t0 = collections.Counter(r['transient'] == 0 for r in clean)
    print('clean solutions with transient 0 (the initial configuration is itself periodic): %d' % t0[True])
    for r in sorted([r for r in clean if r['transient'] == 0], key=lambda r: r['env_area'])[:8]:
        print('   ', line(r))


if __name__ == '__main__':
    main()
