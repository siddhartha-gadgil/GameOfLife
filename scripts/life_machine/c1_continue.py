#!/usr/bin/env python3
"""C1: continue glider for the pull generator = a round-trip fan-out F in series with PG1.

PG1 (the certified `pullGenerator`) stays in its own frame.  A verified fan-out (S', K') of
results/f2_roundtrip.json.gz whose output G1 flies SE is translated by (u, v) and delayed by s so
that its G1 is the control glider (SE, 41, 22 + 30 n) of PG1; its other output G2 (flying SW) is
the continue glider.  The only freedom is u (the position along the lane of the control glider).

Filters: boxes of the new pieces at least SEP from the boxes of all other pieces; the continue
glider and the new control glider at least CLEAR (box distance) from every piece they do not use.
Every candidate kept is simulated: with the control glider of F the composite returns to its
cycle and exactly three gliders leave: the two of translate (51, 143) pullSalvo (delayed by 30 n)
and the continue glider (board, then set simulator on the unbounded plane).

Usage: c1_continue.py [UMIN UMAX]      Output: results/c1_continue.json, summary on stdout
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import SE, SW, NW, NE, DIRNAME, bbox
import net
from net import (PG1, PG1_NAMES, PG1_C, PG1_A, PG1_B, move_piece, move_wl, env_box, box_dist,
                 seg_box_dist, asm_cross, time_at)

SEP = 12
CLEAR = 8
FAR = 3000
C0 = (SE, 41, 22)


def candidates(umin, umax):
    d = json.load(gzip.open('results/f2_roundtrip.json.gz', 'rt'))
    pg_boxes = [env_box(p) for p in PG1]
    out = []
    for fo in d['good']:
        outs = [(tuple(o[0]), o[1], o[2]) for o in fo['outs']]
        g1 = [w for w in outs if w[0] == SE]
        g2 = [w for w in outs if w[0] == SW]
        if len(g1) != 1 or len(g2) != 1:
            continue
        g1, g2 = g1[0], g2[0]
        for u in range(umin, umax + 1):
            v = u + g1[1] - PG1_C[1]
            s = (PG1_C[2] - g1[2] + 4 * u) % 30
            sF = ('asm', 0, u, v, s)
            kF = move_piece(('asm',) + tuple(fo['asm']), u, v, s)
            ctrl = move_wl(C0, u, v, s)
            cont = move_wl(g2, u, v, s)
            link = move_wl(g1, u, v, s)
            assert link[:2] == PG1_C[:2] and (link[2] - PG1_C[2]) % 30 == 0
            nb = [env_box(sF), env_box(kF)]
            sep = min(box_dist(a, b) for a in nb for b in pg_boxes)
            if sep < SEP:
                continue
            xs, xk = asm_cross(sF), asm_cross(kF)
            t1, t2 = time_at(ctrl, xs), time_at(cont, xs)
            t3, t4 = time_at(link, xk), time_at(link, (45, 31))
            if t4 < t3 + 100:
                continue
            cl = min(seg_box_dist(cont, t2, t2 + FAR, b) for b in pg_boxes + [nb[1]])
            cl = min(cl, min(seg_box_dist(ctrl, t1 - FAR, t1, b) for b in pg_boxes + [nb[1]]))
            cl = min(cl, min(seg_box_dist(link, t3, t4, b) for b in pg_boxes[1:] + [nb[0]]))
            if cl < CLEAR:
                continue
            allb = pg_boxes + nb
            box = (min(b[0] for b in allb), min(b[1] for b in allb), max(b[2] for b in allb), max(b[3] for b in allb))
            out.append({'fo': fo['asm'], 'u': u, 'v': v, 's': s, 'sep': sep, 'clear': cl, 'box': box,
                        'area': (box[2] - box[0] + 1) * (box[3] - box[1] + 1), 'T_fo': fo['T'],
                        'ctrl': ctrl, 'cont': cont, 'link': link})
    return out


def pieces_of(c):
    u, v, s = c['u'], c['v'], c['s']
    return PG1 + [('asm', 0, u, v, s), move_piece(('asm',) + tuple(c['fo']), u, v, s)]


def simulate(c):
    try:
        nt = net.Net(pieces_of(c), PG1_NAMES + ['SF', 'KF'])
    except (ValueError, AssertionError) as e:
        return c, 'not periodic'
    ctrl, cont, link = [(tuple(w[0]), w[1], w[2]) for w in (c['ctrl'], c['cont'], c['link'])]
    st, outs, Ts, Te = nt.react([ctrl], limit=8000)
    if st != 'ok':
        return c, st
    dt = link[2] - PG1_C[2]
    want = sorted([cont, (SE, PG1_A[1], PG1_A[2] + dt), (SE, PG1_B[1], PG1_B[2] + dt)])
    if outs != want:
        return c, 'other gliders'
    c = dict(c)
    c['Ts'], c['Te'], c['N'], c['outs'] = Ts, Te, Te - Ts, outs
    return c, 'ok'


def main():
    umin, umax = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (-260, -20)
    t = time.time()
    cands = candidates(umin, umax)
    cands.sort(key=lambda c: (c['area'], -c['clear']))
    print('placements with separation >= %d and clearance >= %d: %d' % (SEP, CLEAR, len(cands)))
    good, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for c, st in pool.imap_unordered(simulate, cands[:120], chunksize=1):
            stats[st] = stats.get(st, 0) + 1
            if st == 'ok':
                good.append(c)
    good.sort(key=lambda c: (c['area'], -c['clear']))
    print('simulated %d: %s (%.0f s)' % (min(120, len(cands)), stats, time.time() - t))
    for c in good[:25]:
        print('  F = %s moved by (%d, %d), delay %d: sep %d clear %d box %s N %d control %s continue %s' % (
            tuple(c['fo']), c['u'], c['v'], c['s'], c['sep'], c['clear'], c['box'], c['N'],
            net.wlname(tuple(c['ctrl'])), net.wlname(tuple(c['cont']))))
    json.dump(good, open('results/c1_continue.json', 'w'))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
