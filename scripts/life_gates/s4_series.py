#!/usr/bin/env python3
"""Search 4: repeated use of a gate and two gates in series.

Input: the result file of s3_gate.py for a blocked stream (k, dx, dy, p).

(a) Repetition.  For every gate found by s3 with the control glider C arriving from infinity,
    a second control glider on the same lane 30 m generations later (m = 1, 2), and three
    control gliders (m = 0, 1, 2), are tested: the outcome must be the cycle again with exactly
    2 (3) escaped gliders of the same stream, 30 m generations apart, and nothing else.

(b) Series.  Gate 2 is gate 1 translated by v = (vx, vy) (same phase of the cycle).  The glider
    released by gate 1 (stream A, direction (1, 1)) must be, in the coordinates of gate 2, a
    control glider (direction (1, 1), from infinity) that releases a glider of stream A of
    gate 2 and passes the repetition test.  All v with 0 <= vx <= VMAX, 0 <= vy <= VMAX whose
    envelopes are at least SEP cells apart are enumerated; each candidate is checked by evolving
    the union of the two cycles (which must itself have period 30) with one control glider for
    gate 1, and re-checked with the set simulator.

Usage: s4_series.py k dx dy p        Output: results/s4_series_<k>_<dx>_<dy>_<p>.json.gz
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

import life
import gates
from life import glider_at, bbox, translate

VMAX = 160
SEP = 6
R = None


def init(spec):
    global R
    R = gates.Reference.blocked(*spec)


def repeat_test(rec):
    """Returns the list of m-sets ((1,), (2,), (1, 2)) for which the repeated gate works."""
    d, lane, tau = tuple(rec['d']), rec['lane'], rec['tau']
    w0 = (tuple(rec['out'][0][0]), rec['out'][0][1], rec['out'][0][2])
    ok = []
    for ms in ((1,), (2,), (1, 2)):
        wls = [(d, lane, tau)] + [(d, lane, tau + 30 * m) for m in ms]
        b = R.board
        t_ins = rec['t_ins']
        try:
            for wl in wls:
                c = b.of_cells(glider_at(*wl, t_ins))
                if c & R.refdil[t_ins % 30]:
                    raise ValueError
        except ValueError:
            continue
        res = gates.run_gate(R, wls, t_ins, limit=1200)
        if res['status'] != 'restored':
            continue
        got = sorted(w for (w, th) in res['out'])
        want = sorted([w0] + [(w0[0], w0[1], w0[2] + 30 * m) for m in ms])
        if got == want and gates.verify_gate(R, wls, t_ins, want, res['t_end'] + 8):
            ok.append(list(ms))
    return ok


def work_repeat(rec):
    return rec, repeat_test(rec)


def series_candidates(good):
    """good: gates with d = (1, 1), output A, from infinity, repeatable."""
    (ex0, ey0, ex1, ey1) = R.env
    A = [s for s in R.streams if s[0] == (1, 1)][0]
    table = {}
    for r in good:
        table.setdefault((r['lane'], r['tau']), r)
    # every gate releases a glider of stream A on the same world line mod 30, so one gate 1
    # (the fastest) suffices; gate 2 may use any of the good control world lines
    r1 = min(good, key=lambda r: (r['duration'], r['lane'], r['tau']))
    out = []
    for vx in range(0, VMAX + 1):
        for vy in range(0, VMAX + 1):
            if not (vx > ex1 - ex0 + SEP or vy > ey1 - ey0 + SEP):
                continue                         # envelopes too close
            lane2 = A[1] - (vx - vy)             # world line of the released glider in the
            tau2 = (A[2] + 4 * vx) % 30          # coordinates of gate 2
            if (lane2, tau2) in table:
                out.append((r1, table[(lane2, tau2)], vx, vy))
    return out


def check_series(job):
    r1, r2, vx, vy = job
    cells = set(R.ref_cells[0]) | translate(R.ref_cells[0], vx, vy)
    try:
        RC = gates.Reference(cells)
    except AssertionError:
        return None
    wl = (tuple(r1['d']), r1['lane'], r1['tau'])
    t_ins = r1['t_ins']
    c = RC.board.of_cells(glider_at(*wl, t_ins))
    if c & RC.refdil[t_ins % 30]:
        return None
    res = gates.run_gate(RC, [wl], t_ins, limit=2500)
    if res['status'] != 'restored':
        return None
    outs = [w for (w, th) in res['out']]
    A = [s for s in R.streams if s[0] == (1, 1)][0]
    if len(outs) != 1 or outs[0][0] != (1, 1) or outs[0][1] != A[1] + vx - vy:
        return None
    tb = gates.back_time(RC, res, t_ins)
    if not gates.verify_gate(RC, [wl], t_ins, outs, res['t_end'] + 8):
        return None
    env = RC.env
    return {'vx': vx, 'vy': vy, 'control': [list(wl[0]), wl[1], wl[2]], 't_ins': t_ins,
            't_back': tb, 'duration': tb - t_ins, 'out': [list(outs[0][0]), outs[0][1], outs[0][2]],
            'gate2_control': [r2['d'], r2['lane'], r2['tau']],
            'envelope': list(env), 'area': (env[2] - env[0] + 1) * (env[3] - env[1] + 1)}


def main():
    spec = tuple(int(x) for x in sys.argv[1:5])
    name = 'results/s3_gate_%d_%d_%d_%d.json.gz' % spec
    d = json.load(gzip.open(name, 'rt'))
    init(spec)
    gs = [r for r in d['records'] if r['kind'] == 'gate' and r['from_infinity'] and r.get('verified')]
    t = time.time()
    rep = []
    with Pool(min(20, os.cpu_count() or 1), initializer=init, initargs=(spec,)) as pool:
        for rec, ok in pool.imap_unordered(work_repeat, gs, chunksize=8):
            rec['repeat'] = ok
            rep.append(rec)
        rep.sort(key=lambda r: (r['d'], r['lane'], r['tau']))
        full = [r for r in rep if len(r['repeat']) == 3]
        print('gates from infinity: %d;  repeatable with m = 1: %d, m = 2: %d, three in a row: %d; all three tests: %d' % (
            len(rep), sum([1] in r['repeat'] for r in rep), sum([2] in r['repeat'] for r in rep),
            sum([1, 2] in r['repeat'] for r in rep), len(full)))
        cnt = {}
        for r in rep:
            key = (tuple(r['d']), r['out'][0][3], len(r['repeat']) == 3)
            cnt[key] = cnt.get(key, 0) + 1
        print('by (direction of C, released stream, fully repeatable):')
        for key in sorted(cnt):
            print('   ', key, cnt[key])
        good = [r for r in full if tuple(r['d']) == (1, 1) and r['out'][0][3] == 'A']
        cands = series_candidates(good)
        print('series: %d gates usable, %d candidate translations' % (len(good), len(cands)))
        ser = [x for x in pool.imap_unordered(check_series, cands, chunksize=4) if x is not None]
    ser.sort(key=lambda x: (x['area'], x['duration']))
    dt = time.time() - t
    print('series: %d verified translations, %.1f s' % (len(ser), dt))
    for x in ser[:15]:
        print('   v=(%d,%d) control=%s t_ins=%d dur=%d out=%s env=%s area=%d' % (
            x['vx'], x['vy'], x['control'], x['t_ins'], x['duration'], x['out'], x['envelope'], x['area']))
    with gzip.open('results/s4_series_%d_%d_%d_%d.json.gz' % spec, 'wt') as f:
        json.dump({'spec': spec, 'VMAX': VMAX, 'SEP': SEP, 'seconds': round(dt, 1),
                   'repeat': [{'d': r['d'], 'lane': r['lane'], 'tau': r['tau'], 'out': r['out'][0],
                               'duration': r['duration'], 't_ins': r['t_ins'], 'repeat': r['repeat']}
                              for r in rep],
                   'series': ser}, f, separators=(',', ':'))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
