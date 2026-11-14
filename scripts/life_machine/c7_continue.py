#!/usr/bin/env python3
"""C7 (R-23): continue glider for the push generator PSG1 = a fan-out V in series with PSG1.

As c1_continue.py for PG1: a verified fan-out (results/f2_roundtrip.json.gz) with an SE output is
translated along the lane of PSG1's control glider C_U = (SE, 95, -170) (results/psg1.json) so that
its SE output is exactly C_U; its SW output is the continue glider.  Filters: boxes of the new
pieces >= SEP from the boxes of all PSG1 pieces; new control glider and continue glider >= CLEAR
(box distance) from every piece they do not use.  The NSIM smallest are simulated; the first
verified one (smallest box) is described in full (report22.describe, set simulator) with the
block test.

Usage: c7_continue.py [NSIM [T ...]]      Output: results/c7_continue.txt (stdout), results/psg1c.json
"""
import gzip
import json
import os
import sys
from multiprocessing import Pool

from common import SE, SW, NW, NE, bbox, counter, translate, glider_at
import net
from net import (move_piece, move_wl, env_box, box_dist, seg_box_dist, asm_cross, time_at, wlname)

SEP = 12
CLEAR = 8
FAR = 3000
C0 = (SE, 41, 22)
NAMES = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3', 'SF', 'KF', 'RFc']
UR = range(-40, -400, -1)


def tup(o):
    return (tuple(o[0]), o[1], o[2])


def load_psg():
    e = json.load(open('results/psg1.json'))
    pcs = [tuple(e[n]) for n in NAMES]
    return e, pcs, tup(e['ctrl']), [tup(e[k]) for k in ('a', 'b', 'c')]


def candidates():
    e, pcs, CU, sal = load_psg()
    d = json.load(gzip.open('results/f2_roundtrip.json.gz', 'rt'))
    boxes = [env_box(p) for p in pcs]
    out = []
    for fo in d['good']:
        outs = [tup(o) for o in fo['outs']]
        g1 = [w for w in outs if w[0] == SE]
        g2 = [w for w in outs if w[0] == SW]
        if len(g1) != 1 or len(g2) != 1:
            continue
        g1, g2 = g1[0], g2[0]
        for u in UR:
            v = u + g1[1] - CU[1]
            s = CU[2] - g1[2] + 4 * u
            sV, kV = ('asm', 0, u, v, s % 30), move_piece(('asm',) + tuple(fo['asm']), u, v, s)
            ctrl, cont, link = move_wl(C0, u, v, s), move_wl(g2, u, v, s), move_wl(g1, u, v, s)
            assert link == CU
            nb = [env_box(sV), env_box(kV)]
            sep = min(box_dist(a, b) for a in nb for b in boxes)
            if sep < SEP:
                continue
            xs, xk = asm_cross(sV), asm_cross(kV)
            t1, t2 = time_at(ctrl, xs), time_at(cont, xs)
            cl = min(seg_box_dist(cont, t2, t2 + FAR, b) for b in boxes + [nb[1]])
            cl = min(cl, min(seg_box_dist(ctrl, t1 - FAR, t1, b) for b in boxes + [nb[1]]))
            if cl < CLEAR:
                continue
            allb = boxes + nb
            box = (min(b[0] for b in allb), min(b[1] for b in allb), max(b[2] for b in allb), max(b[3] for b in allb))
            out.append({'fo': fo['asm'], 'T_fo': fo['T'], 'u': u, 'v': v, 's': s, 'sep': sep, 'clear': cl, 'box': box,
                        'area': (box[2] - box[0] + 1) * (box[3] - box[1] + 1), 'SV': sV, 'KV': kV,
                        'ctrl': ctrl, 'cont': cont})
            break                          # the first u (most compact) for this fan-out
    return out


def simulate(c):
    e, pcs, CU, sal = load_psg()
    try:
        nt = net.Net(pcs + [tuple(c['SV']), tuple(c['KV'])], NAMES + ['SV', 'KV'])
    except (ValueError, AssertionError):
        return c, 'not periodic'
    st, outs, Ts, Te = nt.react([tup(c['ctrl'])], limit=8000)
    if st != 'ok':
        return c, st
    if outs != sorted(sal + [tup(c['cont'])]):
        return c, 'other gliders'
    c = dict(c)
    c['Ts'], c['Te'] = Ts, Te
    return c, 'ok'


def main():
    nsim = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    reuse = [int(x) for x in sys.argv[2:]]
    cands = sorted(candidates(), key=lambda c: (c['area'], -c['clear']))
    print('fan-outs with an SE output placed in series with PSG1 (first u per fan-out, sep >= %d, clear >= %d): %d' % (SEP, CLEAR, len(cands)))
    good, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for c, st in pool.imap_unordered(simulate, cands[:nsim], chunksize=1):
            stats[st] = stats.get(st, 0) + 1
            if st == 'ok':
                good.append(c)
    good.sort(key=lambda c: (c['area'], -c['clear']))
    print('simulated %d: %s' % (min(nsim, len(cands)), stats))
    for c in good[:10]:
        print('  V = %s moved by (%d, %d), delay %d: sep %d clear %d box %s N %d control %s continue %s' % (
            tuple(c['fo']), c['u'], c['v'], c['s'], c['sep'], c['clear'], c['box'], c['Te'] - c['Ts'],
            wlname(tup(c['ctrl'])), wlname(tup(c['cont']))))
    if not good:
        return
    best = good[0]
    json.dump(best, open('results/psg1c.json', 'w'))
    # full description of the best one
    from report22 import describe, block_test
    e, pcs, CU, sal = load_psg()
    pieces = pcs + [tuple(best['SV']), tuple(best['KV'])]
    names = NAMES + ['SV', 'KV']
    cont = tup(best['cont'])
    nt, Ts, Te, outs, start, end = describe(
        'Push generator with continue glider PSG1C: fan-out %s moved by (%d, %d), delayed by %d, in series with PSG1' % (
            tuple(best['fo']), best['u'], best['v'], best['s']),
        pieces, names, [tup(best['ctrl'])], sal + [cont], reuse,
        note=' link glider (SE output of V) = control glider C_U of PSG1 = %s' % wlname(CU))
    # register: translate (84, 149) (counter k), as for PSG1 (report_push.txt)
    tx, ty = 84, 149
    blocks = [(k, translate(set(counter(k)), tx, ty), translate(set(counter(k + 1)), tx, ty)) for k in (0, 1, 2, 3, 4, 40)]
    n0 = Te - Ts
    print(' with the block translate (%d, %d) (counter k):' % (tx, ty))
    block_test(nt, [tup(best['ctrl'])], Ts, blocks, [cont], lambda k: n0 + 30 * ((4 * k + 32 + 29) // 30 + 2),
               lambda k, i: 'translate (%d, %d) (counter %d)' % (tx, ty, k + i))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
