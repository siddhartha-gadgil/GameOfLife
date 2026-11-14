#!/usr/bin/env python3
"""S7 (R-23): rank the verified push generators of g7_push.py by exact clearances.

For each design: minimum Chebyshev distance between the envelopes of any two pieces, minimum
distance between every flight segment and the envelopes of the pieces it does not use (the same
segments as report23.py), and the smallest reuse spacing T (multiples of 30 from TMIN) for which a
second control glider T generations later gives two salvos.

Usage: s7_select.py FILE.json.gz [N [TMIN TMAX]]
"""
import gzip
import json
import os
import sys
from multiprocessing import Pool

from common import bbox, SE, SW, NE, NW
import net
from net import Net, env_cells, set_dist, glider_path, box_dist, time_at, asm_cross, rf_point, move_wl

NAMES = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3', 'SF', 'KF', 'RFc']
TR = (300, 900)


def tup(o):
    return (tuple(o[0]), o[1], o[2])


def segments(e, Ts, Te):
    xs, xk, xg = asm_cross(e['S']), asm_cross(e['K']), asm_cross(e['Gb'])
    xsf, xkf = asm_cross(e['SF']), asm_cross(e['KF'])
    p1, p2, p3, pcf = rf_point(e['RF1']), rf_point(e['RF2']), rf_point(e['RF3']), rf_point(e['RFc'])
    T = lambda w, p: int(time_at(w, p))
    C0 = (SE, 41, 22)
    return [('control C_U (before SF)', e['ctrl'], Ts, T(e['ctrl'], xsf) - 20, ['SF']),
            ('link C0 (KF to S)', C0, T(C0, xkf) + 60, T(C0, xs) - 20, ['KF', 'S']),
            ('continue (SF to RFc)', e['cont'], T(e['cont'], xsf) + 40, T(e['cont'], pcf) - 20, ['SF', 'RFc']),
            ('c (from RFc)', e['c'], T(e['c'], pcf) + 20, Te + 1500, ['RFc']),
            ('G1 (K to RF1)', e['G1'], T(e['G1'], xk) + 60, T(e['G1'], p1) - 20, ['K', 'RF1']),
            ('leg (RF1 to RF2)', e['leg'], T(e['leg'], p1) + 20, T(e['leg'], p2) - 20, ['RF1', 'RF2']),
            ('a (from RF2)', e['a'], T(e['a'], p2) + 20, Te + 1500, ['RF2']),
            ('G2 (S to Gb)', e['G2'], T(e['G2'], xs) + 20, T(e['G2'], xg) - 10, ['S', 'Gb']),
            ('o (Gb to RF3)', e['o'], T(e['o'], xg) + 40, T(e['o'], p3) - 20, ['Gb', 'RF3']),
            ('b (from RF3)', e['b'], T(e['b'], p3) + 20, Te + 1500, ['RF3'])]


def norm(e):
    e = dict(e)
    for n in NAMES:
        e[n] = tuple(e[n])
    for n in ('G1', 'leg', 'a', 'G2', 'o', 'b', 'c', 'ctrl', 'cont'):
        e[n] = tup(e[n])
    return e


def rank(arg):
    i, e = arg
    e = norm(e)
    pieces = [e[n] for n in NAMES]
    envs = [env_cells(p) for p in pieces]
    dp = 10 ** 9
    for a in range(len(envs)):
        for b in range(a):
            if box_dist(bbox(envs[a]), bbox(envs[b])) < 40:
                dp = min(dp, set_dist(envs[a], envs[b]))
    Ts, Te = e['Ts'], e['Te']
    seg_min = {}
    for (nm, w, ta, tb, used) in segments(e, Ts, Te):
        path = glider_path(w, ta, tb)
        pb = bbox(path)
        m = 10 ** 9
        for j, n in enumerate(NAMES):
            if n in used or box_dist(pb, bbox(envs[j])) >= 20:
                continue
            m = min(m, set_dist(path, envs[j]))
        seg_min[nm] = m
    nt = Net(pieces, NAMES)
    want = sorted([e['a'], e['b'], e['c']])
    T = None
    for t in range(TR[0], TR[1] + 1, 30):
        c2 = [e['ctrl'], (e['ctrl'][0], e['ctrl'][1], e['ctrl'][2] + t)]
        st, outs, _, _ = nt.react(c2, limit=20000)
        if st == 'ok' and outs == sorted(want + [(w[0], w[1], w[2] + t) for w in want]):
            T = t
            break
    return i, dp, seg_min, T


def main():
    global TR
    d = json.load(gzip.open(sys.argv[1], 'rt'))
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    if len(sys.argv) > 4:
        TR = (int(sys.argv[3]), int(sys.argv[4]))
    good = d['good'][:n]
    rows = []
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for i, dp, sm, T in pool.imap_unordered(rank, list(enumerate(good))):
            e = good[i]
            inherent = min(v for k, v in sm.items())
            others = min(v for k, v in sm.items() if k != 'c (from RFc)')
            rows.append((i, dp, inherent, others, T, e['area'], e['box'], e['uj'], e['ci'], sm))
    rows.sort(key=lambda r: (-min(r[1], r[2]), -r[3], r[5]))
    print('design  pieces  flights(all)  flights(without c)  reuse T  area  box  U  core')
    for r in rows:
        print('  %3d   %3d   %3d   %3d   %s   %6d  %s  U %d  core %d' % (r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8]))
    best = rows[0]
    print('best: design %d; segment minima %s' % (best[0], best[9]))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
