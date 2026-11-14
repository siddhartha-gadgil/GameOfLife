#!/usr/bin/env python3
"""Search Q1: a period-30 reflector made from a queen bee shuttle (half of the Gosper gun).

Step 1 (stabilise): the left half of `gosperGun` (cells with x <= 17: a block and the queen bee)
plus one stabiliser on the right -- a block, or eater 1 in one of its 8 orientations, with
bounding box origin (bx, by), 14 <= bx <= 34, -8 <= by <= 14 -- is run for 600 generations; kept
if it has least period 30 (from generation 0 or after a transient; the periodic state is used).
Step 2 (reflect): for every such oscillator (up to NOSC, smallest first) and every glider world
line (4 directions, all lanes meeting its envelope + 5, tau = 0 .. 29) arriving from infinity:
run as in scripts/life_gates/s3_gate.py.  Recorded: oscillator restored and exactly one glider
leaves that is not the incoming glider on its own world line.

Usage: q1_reflector.py        Output: results/q1_reflector.json.gz, summary on stdout
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import (GUN, EATER1, translate, transform, step_cells, glider_at, bbox, SE, SW, NW, NE,
                    DIRNAME, gates, life, lean_window)

LEFT = frozenset(c for c in GUN if c[0] <= 17)
BLOCK = frozenset(life.BLOCK)


def stabilisers():
    out = [('block', BLOCK)]
    for k in range(8):
        out.append(('eater%d' % k, frozenset(life.normalize(transform(EATER1, k)))))
    return out


def step1(job):
    name, shape, bx, by = job
    st = translate(shape, bx, by)
    if life.chebyshev_dist(st, LEFT) < 2:
        return None
    c = set(LEFT) | st
    hist = [frozenset(c)]
    for t in range(660):
        c = step_cells(c)
        if len(c) > 120 or not c:
            return None
        hist.append(frozenset(c))
    if hist[600] != hist[630]:
        return None
    if any(hist[600] == hist[600 + q] for q in range(1, 30)):
        return None
    t0 = 600
    while t0 > 0 and hist[t0 - 1] == hist[t0 - 1 + 30]:
        t0 -= 1
    tref = 30 * ((t0 + 29) // 30)
    cells = hist[tref]
    env = bbox(set().union(*hist[tref:tref + 30]))
    return {'stab': name, 'bx': bx, 'by': by, 'transient': t0, 'cells': sorted(cells), 'env': env,
            'left_intact': all((LEFT <= hist[tref + 30 * 0]) for _ in (0,))}


R = None


def init2(cells):
    global R
    R = gates.Reference(set(map(tuple, cells)))


def step2(job):
    d, lane = job
    recs = []
    for tau in range(30):
        wl = (d, lane, tau)
        ivs, t_in, t_out = gates.free_intervals(R, d, lane, tau)
        if not ivs or (len(ivs) == 1 and ivs[0] == (t_in, t_out)) or ivs[0][0] != t_in:
            continue
        e = ivs[0][1]
        if e >= t_out:
            continue
        res = gates.run_gate(R, [wl], e, limit=600)
        if res['status'] != 'restored':
            continue
        outs = [w for (w, th) in res['out']]
        if outs == [wl]:
            continue
        recs.append({'in': wl, 'out': outs, 't_ins': e, 't_end': res['t_end'],
                     'verified': gates.verify_gate(R, [wl], e, outs, res['t_end'] + 8)})
    return recs


def main():
    t = time.time()
    jobs = [(n, s, bx, by) for (n, s) in stabilisers() for bx in range(14, 35) for by in range(-8, 15)]
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        oscs = [r for r in pool.imap_unordered(step1, jobs, chunksize=8) if r is not None]
    oscs.sort(key=lambda o: ((o['env'][2] - o['env'][0] + 1) * (o['env'][3] - o['env'][1] + 1), o['stab'], o['bx'], o['by']))
    print('step 1: %d placements, %d oscillators of least period 30 (%.0f s)' % (len(jobs), len(oscs), time.time() - t))
    for o in oscs:
        print('   %s at (%d, %d): transient %d, envelope %s, %d cells: %s' % (
            o['stab'], o['bx'], o['by'], o['transient'], o['env'], len(o['cells']), lean_window(set(map(tuple, o['cells'])))))
    allrecs = []
    for o in oscs:
        init2(o['cells'])
        ex0, ey0, ex1, ey1 = R.env
        box = (ex0 - 5, ey0 - 5, ex1 + 5, ey1 + 5)
        jobs2 = []
        for d in life.DIRS:
            vals = [d[1] * x - d[0] * y for x in (box[0], box[2]) for y in (box[1], box[3])]
            jobs2.extend((d, lane) for lane in range(min(vals) - 3, max(vals) + 1))
        with Pool(min(20, os.cpu_count() or 1), initializer=init2, initargs=(o['cells'],)) as pool:
            recs = [r for rr in pool.imap_unordered(step2, jobs2, chunksize=4) for r in rr]
        cnt = {}
        for r in recs:
            key = (DIRNAME[r['in'][0]], ' '.join(sorted(DIRNAME[w[0]] for w in r['out'])) or '-')
            cnt[key] = cnt.get(key, 0) + 1
        print('step 2: %s at (%d, %d): restored outcomes by (direction in, directions out): %s' % (
            o['stab'], o['bx'], o['by'], dict(sorted(cnt.items()))))
        for r in recs:
            if len(r['out']) == 1 and r['verified']:
                din, dout = r['in'][0], r['out'][0][0]
                if din[0] * dout[0] + din[1] * dout[1] == 0:
                    print('      REFLECTOR 90: in %s lane %d tau %d -> out %s lane %d tau %d  (t_ins %d, t_end %d)' % (
                        DIRNAME[din], r['in'][1], r['in'][2], DIRNAME[dout], r['out'][0][1], r['out'][0][2], r['t_ins'], r['t_end']))
        allrecs.append({'osc': o, 'records': recs})
    with gzip.open('results/q1_reflector.json.gz', 'wt') as f:
        json.dump(allrecs, f, separators=(',', ':'))
    print('%.0f s' % (time.time() - t))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
