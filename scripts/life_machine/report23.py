#!/usr/bin/env python3
"""Cell-exact data of the push-salvo generator of report R-23, every statement re-checked with the
set simulator on the unbounded plane.

Usage: report23.py DESIGN.json [T ...]
       report23.py --pick FILE.json.gz I DESIGN.json     (the I-th verified design of a g7_push.py output)
  T: reuse spacings to test.
"""
import gzip
import json
import sys

from common import (lean_window, glider_at, evolve_cells, counter, translate, bbox, SE, SW, NW, NE, life,
                    step_cells)
import net
from net import Net, piece_cells, env_cells, time_at, asm_cross, rf_point, wlname, pr, move_wl, glider_path, set_dist
from report22 import describe, clearances

NAMES = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3', 'SF', 'KF', 'RFc']
BLOCK0 = frozenset({(0, 0), (1, 0), (0, 1), (1, 1)})


def tup(o):
    return (tuple(o[0]), o[1], o[2])


def pc(p):
    return tuple(p)


def load(path):
    e = json.load(open(path))
    for n in NAMES:
        e[n] = pc(e[n])
    for n in ('G1', 'leg', 'a', 'G2', 'o', 'b', 'c', 'ctrl', 'cont'):
        e[n] = tup(e[n])
    return e


def push_frame(e):
    """The push record and the map rec frame (block at (0, 0)) -> world: lanes + Lo, taus + to."""
    P = json.load(open('results/p1_pushes.json'))
    ro = e['role']
    la, ta = ro['a']
    Lo, to = e['a'][1] - la, e['a'][2] - ta
    for k in ('b', 'c'):
        l, t = ro[k]
        assert (e[k][1], e[k][2]) == (l + Lo, t + to)
    return P[ro['push']], ro, Lo, to


def salvo_rec(rec, time):
    c = set()
    for (l, t) in rec['wl']:
        c |= glider_at(SE, l, t, time)
    return c


def lean_statement(rec):
    """The salvo against `counter 0` (block (7, 11)) of SlidingBlock.lean: frame = rec frame
    translated by (7, 11); returns (time t0, cells of the salvo at t0, n)."""
    wl = [(SE, l - 4, t - 28) for (l, t) in rec['wl']]
    b0 = set(counter(0))
    # earliest common time at which all gliders are >= 3 from the block and from each other,
    # searched downwards from the time of the normal form
    for t0 in range(-28, -400, -1):
        cells = [glider_at(*w, t0) for w in wl]
        ok = all(life.chebyshev_dist(c, b0) >= 3 for c in cells)
        ok = ok and all(life.chebyshev_dist(cells[i], cells[j]) >= 3 for i in range(3) for j in range(i))
        # and no glider has passed the block: they approach it (distance decreasing)
        if ok:
            sal = set().union(*cells)
            for n in range(1, 400):
                end = evolve_cells(sal | b0, n)
                if end == set(counter(1)):
                    return t0, sal, n, wl
            raise AssertionError
    raise AssertionError


def main():
    if sys.argv[1] == '--pick':
        d = json.load(gzip.open(sys.argv[2], 'rt'))
        e = d['good'][int(sys.argv[3])]
        e['role'] = d['roles'][e['ri']]
        json.dump(e, open(sys.argv[4], 'w'))
        return
    e = load(sys.argv[1])
    reuse = [int(x) for x in sys.argv[2:]]
    pieces = [e[n] for n in NAMES]
    rec, ro, Lo, to = push_frame(e)
    want = [e['a'], e['b'], e['c']]
    note = (' push %s of results/p1_pushes.json (n = %d), roles a %s, b %s, c %s (lanes relative to the block, taus relative)\n'
            ' u = %d (position of the upstream fan-out along the lane of C0), m = %d (SW lane RF1 -> RF2)' % (
                rec['wl'], rec['n'], ro['a'], ro['b'], ro['c'], e['u'], e['m']))
    nt, Ts, Te, outs, start, end = describe('Push-salvo generator PSG (g7_push.py): upstream fan-out U = (SF, KF) + RF_c, core (S, K, Gb, RF1, RF2, RF3)',
                                            pieces, NAMES, [e['ctrl']], want, reuse, note=note)
    # flight segments
    xs, xk, xg = asm_cross(e['S']), asm_cross(e['K']), asm_cross(e['Gb'])
    xsf, xkf = asm_cross(e['SF']), asm_cross(e['KF'])
    p1, p2, p3, pcf = rf_point(e['RF1']), rf_point(e['RF2']), rf_point(e['RF3']), rf_point(e['RFc'])
    g0 = move_wl((SE, 14, 119), e['SF'][2], e['SF'][3], 0)
    g0 = (SE, g0[1], g0[2])
    T = lambda w, p: int(time_at(w, p))
    C0 = (SE, 41, 22)
    segs = [('control C_U (before SF)', e['ctrl'], Ts, T(e['ctrl'], xsf) - 20, ['SF']),
            ('link C0 (KF to S)', C0, T(C0, xkf) + 60, T(C0, xs) - 20, ['KF', 'S']),
            ('continue (SF to RFc)', e['cont'], T(e['cont'], xsf) + 40, T(e['cont'], pcf) - 20, ['SF', 'RFc']),
            ('c (from RFc)', e['c'], T(e['c'], pcf) + 20, Te + 1500, ['RFc']),
            ('G1 (K to RF1)', e['G1'], T(e['G1'], xk) + 60, T(e['G1'], p1) - 20, ['K', 'RF1']),
            ('leg (RF1 to RF2)', e['leg'], T(e['leg'], p1) + 20, T(e['leg'], p2) - 20, ['RF1', 'RF2']),
            ('a (from RF2)', e['a'], T(e['a'], p2) + 20, Te + 1500, ['RF2']),
            ('G2 (S to Gb)', e['G2'], T(e['G2'], xs) + 20, T(e['G2'], xg) - 10, ['S', 'Gb']),
            ('o (Gb to RF3)', e['o'], T(e['o'], xg) + 40, T(e['o'], p3) - 20, ['Gb', 'RF3']),
            ('b (from RF3)', e['b'], T(e['b'], p3) + 20, Te + 1500, ['RF3'])]
    clearances(pieces, NAMES, segs)
    # glider - glider distances of the salvo at the end: they are the push salvo
    # block: rec frame -> world: translation (X, Y) with X - Y = Lo, delay D = to + 4 X
    env = nt.env
    X = max(env[2], env[3] + Lo) + 60
    Y = X - Lo
    D = to + 4 * X
    print(' the salvo {a, b, c} is the push %s with the block (rec frame (0, 0)) at (%d, %d), reached at world time %d' % (rec['wl'], X, Y, D))
    for k in (0, 1, 2, 3, 4, 40):
        n = 30 * ((D + 4 * k + rec['n'] + 60 - Ts) // 30 + 1)
        b0 = translate(BLOCK0, X + k, Y + k)
        endk, box = nt.trace([e['ctrl']], Ts, Ts + n, extra=b0)
        assert endk == nt.cycle(Ts + n) | translate(BLOCK0, X + k + 1, Y + k + 1), k
        print('    k = %2d: evolve %d (R ∪ C_U ∪ B_k) = R ∪ B_(k+1),  B_k = block at (%d, %d): checked; box x %d..%d, y %d..%d' % (
            k, n, X + k, Y + k, box[0], box[2], box[1], box[3]))
    # the salvo against counter 0
    t0, sal, n, wl = lean_statement(rec)
    print(' the salvo in the frame of SlidingBlock.lean (counter 0 = block at (7, 11)):')
    print('    world lines %s' % ', '.join(wlname(w) for w in wl))
    pr('pushSalvo3 (time %d)' % t0, sal)
    print('    evolve %d (pushSalvo3 ∪ counter 0) = counter 1: checked (set simulator)' % n)
    for k in range(0, 6):
        assert evolve_cells(sal | set(counter(k)), n + 4 * k) == set(counter(k + 1))
    print('    evolve (%d + 4 k) (pushSalvo3 ∪ counter k) = counter (k + 1) for k = 0 .. 5: checked' % n)
    # the generator's salvo at the end of the reaction as a translate of pushSalvo3
    G = set()
    for w in want:
        G |= glider_at(*w, Te)
    sb = bbox(sal)
    gb = bbox(G)
    tx, ty = gb[0] - sb[0], gb[1] - sb[1]
    assert G == translate(sal, tx, ty)
    print('    the three gliders at the end of the reaction: R ∪ G with G = translate (%d, %d) pushSalvo3: checked' % (tx, ty))
    print('    hence evolve %d (R ∪ C_U) = R ∪ translate (%d, %d) pushSalvo3, and translate (%d, %d) (counter k) is the register block:' % (
        Te - Ts, tx, ty, tx, ty))
    for k in (0, 1, 2, 3, 4, 40):
        n2 = (Te - Ts) + n + 4 * k
        n2 = 30 * ((n2 + 29) // 30)
        b0 = translate(set(counter(k)), tx, ty)
        endk, box = nt.trace([e['ctrl']], Ts, Ts + n2, extra=b0)
        assert endk == nt.cycle(Ts + n2) | translate(set(counter(k + 1)), tx, ty), k
        print('    k = %2d: evolve %d (R ∪ C_U ∪ translate (%d, %d) (counter %d)) = R ∪ translate (%d, %d) (counter %d): checked; box x %d..%d, y %d..%d' % (
            k, n2, tx, ty, k, tx, ty, k + 1, box[0], box[2], box[1], box[3]))


if __name__ == '__main__':
    main()
