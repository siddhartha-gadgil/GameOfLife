#!/usr/bin/env python3
"""Cell-exact data of the designs of report R-22, every statement re-checked with the set
simulator on the unbounded plane.

Usage:
    report22.py continue U V S [T ...]     CG: fan-out F1 moved by (U, V), delayed by S, + PG1
    report22.py comb I J [T ...]           comb fan-out number (I, J) of results/f3_comb.json.gz
    report22.py push FILE [T ...]          push generator in a JSON file (g6_push.py / g7)
"""
import gzip
import json
import sys

from common import (lean_window, show, bbox, glider_at, step_cells, evolve_cells, counter, SE, SW, NW,
                    NE, DIRNAME, life, translate)
import net
from net import (Net, PG1, PG1_NAMES, PG1_C, PG1_A, PG1_B, move_piece, move_wl, piece_cells, env_cells,
                 env_box, set_dist, glider_path, glider_clearance, time_at, asm_cross, rf_point, wlname,
                 pr, register_block, box_dist)


def tup(o):
    return (tuple(o[0]), o[1], o[2])


def describe(label, pieces, names, controls, want, reuse=(), note=None):
    """Prints the pieces, the composite, the reaction (verified with the set simulator, with the
    box of all generations) and the reuse tests.  Returns (net, Ts, Te, outs, start, end)."""
    nt = Net(pieces, names)                       # asserts period 30
    print(label)
    if note:
        print(note)
    print(' pieces at world time 0 (mod 30):')
    for nm, p in zip(names, pieces):
        kind = 'assembly' if p[0] == 'asm' else 'reflector'
        pr('%s = %s %s' % (nm, kind, tuple(p[1:])), piece_cells(p, 0))
    pr('whole periodic configuration R', nt.cells0)
    cyc = nt.comp.R.ref_cells
    assert all(set(cyc[0]) != set(cyc[q]) for q in range(1, 30))
    e = nt.env
    print('  period 30 (least); envelope over a cycle: x %d..%d, y %d..%d (%d x %d); %d cells at time 0' % (
        e[0], e[2], e[1], e[3], e[2] - e[0] + 1, e[3] - e[1] + 1, len(nt.cells0)))
    print(' minimum Chebyshev distances between the envelopes (all cells over a cycle) of the pieces')
    print(' (pairs whose boxes are 40 or more apart: box distance, marked >=):')
    best = None
    line = []
    for (a, b, d, far) in nt.piece_distances():
        line.append('%s-%s %s%d' % (a, b, '>=' if far else '', d))
        best = d if best is None else min(best, d)
    for i in range(0, len(line), 8):
        print('    ' + ', '.join(line[i:i + 8]))
    print('    minimum: %d' % best)
    st, outs, Ts, Te = nt.react(controls, limit=20000)
    assert st == 'ok', st
    assert outs == sorted(want), (outs, sorted(want))
    end, box = nt.trace(controls, Ts, Te)
    expect = nt.cycle(Te)
    for w in outs:
        expect |= glider_at(*w, Te)
    assert end == expect
    N = Te - Ts
    print(' reaction (set simulator, unbounded plane):  evolve %d (R ∪ C) = R ∪ G   (world times %d -> %d, both = 0 mod 30)' % (N, Ts, Te))
    start = set(nt.cells0)
    for i, w in enumerate(controls):
        g = glider_at(*w, Ts)
        pr('C%d %s' % (i + 1, wlname(w)), g)
        start |= g
    for i, w in enumerate(outs):
        pr('G%d %s' % (i + 1, wlname(w)), glider_at(*w, Te))
    pr('start R ∪ C', start)
    pr('end R ∪ G', end)
    print('  box of all generations 0 .. %d of the reaction: x %d..%d, y %d..%d' % (N, box[0], box[2], box[1], box[3]))
    for T in reuse:
        c2 = list(controls) + [(w[0], w[1], w[2] + T) for w in controls]
        st2, outs2, Ts2, Te2 = nt.react(c2, limit=20000)
        good = st2 == 'ok' and outs2 == sorted(list(want) + [(w[0], w[1], w[2] + T) for w in want])
        print(' second control glider %d generations later: %s' % (T, 'works (set simulator)' if good else 'FAILS'))
    return nt, Ts, Te, outs, start, end


def clearances(pieces, names, segs):
    """segs: [(name, world line, t_from, t_to, names of the pieces the glider uses)]."""
    envs = [env_cells(p) for p in pieces]
    boxes = [bbox(e) for e in envs]
    print(' flight segments: minimum Chebyshev distance to the envelopes of the pieces not used')
    print(' (only distances below 20 are listed):')
    allmin = None
    for (nm, w, ta, tb, used) in segs:
        path = glider_path(w, ta, tb)
        pb = bbox(path)
        out = []
        m = None
        for i, e in enumerate(envs):
            if names[i] in used:
                continue
            if box_dist(pb, boxes[i]) >= 20:
                continue
            d = set_dist(path, e)
            m = d if m is None else min(m, d)
            if d < 20:
                out.append('%s %d' % (names[i], d))
        allmin = m if allmin is None else (allmin if m is None else min(allmin, m))
        print('    %-22s %s lane %d, times %d..%d: %s' % (nm, DIRNAME[w[0]], w[1], ta, tb, ', '.join(out) if out else 'all >= 20'))
    print('    minimum over all segments: %s' % allmin)


def block_test(nt, controls, Ts, blocks, others, extra_gens, label):
    """blocks: [(k, start block cells, expected block cells)]; others: world lines of the
    gliders that remain in flight (continue glider)."""
    for (k, b0, b1) in blocks:
        n = extra_gens(k)
        assert n % 30 == 0
        end, box = nt.trace(controls, Ts, Ts + n, extra=b0)
        expect = nt.cycle(Ts + n) | set(b1)
        for w in others:
            expect |= glider_at(*w, Ts + n)
        assert end == expect, 'block test failed for k = %d' % k
        print('    k = %d: evolve %d (R ∪ C ∪ %s) = R ∪ %s%s: checked; box x %d..%d, y %d..%d' % (
            k, n, label(k, 0), label(k, 1), ' ∪ continue glider' if others else '', box[0], box[2], box[1], box[3]))


def do_continue(u, v, s, reuse):
    F1 = ('asm', 0, 35, 62, 25)
    C0 = (SE, 41, 22)
    G1, G2 = (SE, -13, 214), (SW, 75, 891)
    sF, kF = ('asm', 0, u, v, s), move_piece(F1, u, v, s)
    pieces, names = PG1 + [sF, kF], PG1_NAMES + ['SF', 'KF']
    ctrl, cont, link = move_wl(C0, u, v, s), move_wl(G2, u, v, s), move_wl(G1, u, v, s)
    dt = link[2] - PG1_C[2]
    assert link[:2] == PG1_C[:2] and dt % 30 == 0
    a, b = (SE, PG1_A[1], PG1_A[2] + dt), (SE, PG1_B[1], PG1_B[2] + dt)
    nt, Ts, Te, outs, start, end = describe(
        'Pull generator with continue glider: fan-out F1 moved by (%d, %d), delayed by %d, in series with PG1' % (u, v, s),
        pieces, names, [ctrl], [a, b, cont], reuse,
        note=' link glider (output G1 of the fan-out = control glider of PG1): %s = (SE, 41, 22 + %d)' % (wlname(link), dt))
    sal = glider_at(*a, Te) | glider_at(*b, Te)
    from common import PULL_SALVO
    d = (Te - 1320 - dt) // 4
    assert (Te - 1320 - dt) % 4 == 0 and sal == translate(set(PULL_SALVO), 51 + d, 143 + d)
    print('  the two SE gliders at the end are translate (%d, %d) pullSalvo; continue glider %s' % (51 + d, 143 + d, lean_window(glider_at(*cont, Te))))
    xs, xk = asm_cross(sF), asm_cross(kF)
    segs = [('control (before SF)', ctrl, Ts, int(time_at(ctrl, xs)) - 20, ['SF']),
            ('link (KF to S)', link, int(time_at(link, xk)) + 60, int(time_at(link, (45, 31))) - 20, ['KF', 'S']),
            ('continue (from SF)', cont, int(time_at(cont, xs)) + 40, Te + 2000, ['SF']),
            ('G0 of F (SF to KF)', move_wl((SE, 14, 119), u, v, s), int(time_at(move_wl((SE, 14, 119), u, v, s), xs)) + 60,
             int(time_at(move_wl((SE, 14, 119), u, v, s), xk)) - 40, ['SF', 'KF'])]
    clearances(pieces, names, segs)
    pgbox = (-86, -9, 90, 152)
    path = glider_path(cont, int(time_at(cont, xs)), Te + 3000)
    dcont = min(max(pgbox[0] - x, x - pgbox[2], pgbox[1] - y, y - pgbox[3]) for (x, y) in path)
    fbox = bbox(env_cells(sF) | env_cells(kF))
    print('  continue glider against the box x -86..90, y -9..152 of `pullGenerator_reaction`: minimum distance %d' % dcont)
    print('  envelope of the fan-out: x %d..%d, y %d..%d; distance to that box: %d' % (fbox[0], fbox[2], fbox[1], fbox[3], box_dist(fbox, pgbox)))
    print(' with the block registerBlock k = translate (51, 143) (counter k):')
    blocks = [(k, register_block(k), register_block(k - 1)) for k in (1, 2, 3, 4, 40)]
    n0 = Te - Ts
    block_test(nt, [ctrl], Ts, blocks, [cont], lambda k: n0 + 30 * ((4 * (k + 8) + 29) // 30 + 1),
               lambda k, i: 'registerBlock %d' % (k - i))
    return nt


def main():
    a = sys.argv[1:]
    if a[0] == 'continue':
        do_continue(int(a[1]), int(a[2]), int(a[3]), [int(x) for x in a[4:]])
    elif a[0] == 'comb':
        d = json.load(gzip.open('results/f3_comb.json.gz', 'rt'))
        rec = [r for r in d['good'] if r['i'] == int(a[1]) and r['j'] == int(a[2])][0]
        pieces = [tuple(p) for p in rec['pieces']]
        want = [tup(o) for o in rec['outs']]
        nt, Ts, Te, outs, start, end = describe('Comb fan-out (%s, %s)' % (a[1], a[2]), pieces, ['S', 'K1', 'K2'], [(SE, 41, 22)], want,
                                                [int(x) for x in a[3:]])
        print(show(start))
    elif a[0] == 'push':
        import push_report
        push_report.run(a[1], [int(x) for x in a[2:]])


if __name__ == '__main__':
    main()
