#!/usr/bin/env python3
"""Search 3: gates.  One control glider C is added to a blocked stream in its periodic cycle.

Exhaustive over all world lines of C: the 4 directions, all lanes meeting the envelope of the
blocked stream (enlarged by 5 cells), and the 30 phases tau = 0 .. 29 relative to the cycle
(tau and tau + 30 give the same experiment one period later).  For each world line the gate times
at which the ideal glider is "free" (Chebyshev distance >= 3 from the cycle) form intervals.  C is
inserted at the end of the first interval (C arrives from infinity) and, when a later interval is
not simply the continuation of an earlier run, at the end of that interval (C is created beyond
an obstacle on its lane; reported with from_infinity = False and the first time of insertion).

Outcome 'restored': after removal of gliders that fly away, the configuration is exactly the
cycle again.  The gliders flying away are classified: 'A' / 'B' a glider of the stream of gun A /
gun B (same lane and phase mod 30 as the stream), 'C' the control glider itself on its own
world line, 'X' any other glider.
    gate      : exactly one glider flies away and it is a stream glider;
    kickback  : one stream glider and one other glider (the control glider sent elsewhere);
    absorbed  : nothing flies away;   pass : only C itself;   other : anything else.
Every gate and kickback is re-checked with the set simulator on the unbounded plane.

Usage: s3_gate.py k dx dy p        Output: results/s3_gate_<k>_<dx>_<dy>_<p>.json.gz
       s3_gate.py summary FILE    (print the summary of a result file again)
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

import life
import gates
from life import DIRS, glider_at, bbox

R = None


def init(spec):
    global R
    R = gates.Reference.blocked(*spec)


def classify(names):
    s = sorted(names)
    if s == ['C']:
        return 'pass'
    if s == []:
        return 'absorbed'
    if s in (['A'], ['B']):
        return 'gate'
    if len(s) == 2 and 'X' in s and ('A' in s or 'B' in s):
        return 'kickback'
    return 'other'


def work(job):
    d, lane = job
    recs = []
    counts = {}
    for tau in range(30):
        wl = (d, lane, tau)
        ivs, t_in, t_out = gates.free_intervals(R, d, lane, tau)
        if not ivs:
            counts['never-free'] = counts.get('never-free', 0) + 1
            continue
        if len(ivs) == 1 and ivs[0] == (t_in, t_out):
            counts['no-contact'] = counts.get('no-contact', 0) + 1
            continue
        covered = [False] * len(ivs)
        first = True
        for i, (s, e) in enumerate(ivs):
            if covered[i]:
                continue
            if e >= t_out:          # free until it leaves the board: nothing happens afterwards
                break
            # watch the later intervals: is the run still "reference + ideal C" there?
            res = None
            cont = []
            for j in range(i + 1, len(ivs)):
                tj = ivs[j][0]
                r1 = gates.run_gate(R, [wl], e, limit=tj - e + 1, watch=(tj, glider_at(*wl, tj)))
                if r1.get('watch'):
                    cont.append(j)
                else:
                    break
            for j in cont:
                covered[j] = True
            res = gates.run_gate(R, [wl], e)
            from_inf = (i == 0 and s == t_in and first)
            first = False
            st = res['status']
            if st != 'restored':
                counts[st] = counts.get(st, 0) + 1
                continue
            names = []
            for (w, th) in res['out']:
                if w == wl:
                    names.append('C')
                else:
                    names.append(R.stream_name(w) or 'X')
            kind = classify(names)
            counts[kind] = counts.get(kind, 0) + 1
            if kind == 'pass':
                continue
            tb = gates.back_time(R, res, e)
            rec = {'d': list(d), 'lane': lane, 'tau': tau, 'from_infinity': from_inf,
                   'free_from': None if from_inf else s, 't_ins': e, 'kind': kind,
                   't_back': tb, 'duration': tb - e, 't_end': res['t_end'],
                   'out': [[list(w[0]), w[1], w[2], nm] for (w, th), nm in zip(res['out'], names)]}
            if kind in ('gate', 'kickback', 'other'):
                tc = res['t_end'] + 8
                rec['verified'] = gates.verify_gate(R, [wl], e, [w for (w, th) in res['out']], tc)
            recs.append(rec)
    return recs, counts


def main():
    spec = tuple(int(x) for x in sys.argv[1:5])
    init(spec)
    ex0, ey0, ex1, ey1 = R.env
    box = (ex0 - 5, ey0 - 5, ex1 + 5, ey1 + 5)
    jobs = []
    for d in DIRS:
        vals = [d[1] * x - d[0] * y for x in (box[0], box[2]) for y in (box[1], box[3])]
        for lane in range(min(vals) - 3, max(vals) + 1):
            jobs.append((d, lane))
    t = time.time()
    recs = []
    counts = {}
    with Pool(min(20, os.cpu_count() or 1), initializer=init, initargs=(spec,)) as pool:
        for rr, cc in pool.imap_unordered(work, jobs, chunksize=4):
            recs.extend(rr)
            for k, v in cc.items():
                counts[k] = counts.get(k, 0) + v
    dt = time.time() - t
    recs.sort(key=lambda r: (r['kind'], r['d'], r['lane'], r['tau'], r['t_ins']))
    summary = {'spec': spec, 'tref': R.tref, 'transient': R.transient, 'envelope': R.env,
               'streams': [[list(s[0]), s[1], s[2]] for s in R.streams],
               'worldlines': len(jobs) * 30, 'counts': counts, 'seconds': round(dt, 1),
               'records': recs}
    os.makedirs('results', exist_ok=True)
    name = 'results/s3_gate_%d_%d_%d_%d.json.gz' % spec
    with gzip.open(name, 'wt') as f:
        json.dump(summary, f, separators=(',', ':'))
    print_summary(summary)


def print_summary(summary):
    recs = summary['records']
    print('blocked stream', tuple(summary['spec']), 'tref', summary['tref'], 'envelope', summary['envelope'])
    print('streams (direction, lane, tau mod 30):', summary['streams'])
    print('world lines: %d, %.1f s' % (summary['worldlines'], summary['seconds']))
    print('counts of runs:', dict(sorted(summary['counts'].items())))
    print('all gates and kickbacks re-checked with the set simulator:',
          all(r.get('verified') for r in recs if r['kind'] in ('gate', 'kickback')))
    print()
    print('GATES (exactly one glider flies away, a stream glider; C is destroyed)')
    print('  one line per (direction of C, released stream, C from infinity?, lane):')
    print('  tau values, [min .. max] of the number of generations from the last free time of C')
    print('  to the return to the cycle')
    groups = {}
    for r in recs:
        if r['kind'] == 'gate':
            key = (tuple(r['d']), r['out'][0][3], r['from_infinity'])
            groups.setdefault(key, {}).setdefault(r['lane'], []).append(r)
    for key in sorted(groups, key=lambda k: (k[0], k[1], not k[2])):
        n = sum(len(v) for v in groups[key].values())
        print(' C direction %s releases %s, from infinity: %s  -- %d world lines on %d lanes'
              % (key[0], key[1], key[2], n, len(groups[key])))
        for lane in sorted(groups[key]):
            rs = groups[key][lane]
            ds = [r['duration'] for r in rs]
            print('   lane %4d: tau %s  [%d .. %d]' % (lane, sorted(set(r['tau'] for r in rs)), min(ds), max(ds)))
    print()
    print('KICKBACKS (one stream glider and one other glider fly away)')
    for r in recs:
        if r['kind'] == 'kickback':
            print('  C d=%s lane=%d tau=%d inf=%s t_ins=%d dur=%d  out=%s' % (
                tuple(r['d']), r['lane'], r['tau'], r['from_infinity'], r['t_ins'], r['duration'],
                [(tuple(o[0]), o[1], o[2], o[3]) for o in r['out']]))
    print()
    print('OTHER outcomes with the cycle restored: (direction of C, from infinity, gliders flying away): count')
    cnt = {}
    for r in recs:
        if r['kind'] in ('other', 'absorbed'):
            key = (tuple(r['d']), r['from_infinity'], ''.join(sorted(o[3] for o in r['out'])) or '-')
            cnt[key] = cnt.get(key, 0) + 1
    for key in sorted(cnt):
        print('   ', key, cnt[key])
    print('  single other glider (C is turned, nothing is released):')
    for r in recs:
        if r['kind'] == 'other' and [o[3] for o in r['out']] == ['X']:
            print('  C d=%s lane=%d tau=%d inf=%s t_ins=%d dur=%d  out=%s' % (
                tuple(r['d']), r['lane'], r['tau'], r['from_infinity'], r['t_ins'], r['duration'],
                [(tuple(o[0]), o[1], o[2]) for o in r['out']]))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    if len(sys.argv) == 3 and sys.argv[1] == 'summary':
        print_summary(json.load(gzip.open(sys.argv[2], 'rt')))
    else:
        main()
