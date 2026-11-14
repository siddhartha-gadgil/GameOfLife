#!/usr/bin/env python3
"""Cell-exact data of the designs of report R-21 (windows `ofRows x0 y0 [rows]`), every statement
re-checked with the set simulator on the unbounded plane.

Usage:
    report_data.py reflector
    report_data.py fanout K VX VY S                (assembly K of f2_roundtrip.py; S = blockedStream)
    report_data.py generator [T ...]               (the design PG1 in results/pg1.json; reuse tests)
"""
import gzip
import json
import sys

from common import (lean_window, show, bbox, glider_at, step_cells, evolve_cells, counter, SE, SW, NW,
                    NE, DIRNAME, life, gates)
import machine
from machine import asm_cells, asm_guns, run_scheduled, verify_scheduled, bs1_cycle
from g1_pull import RF0, RF_IN, RF_OUT, rf_cells, rf_cycle, C0, S_ASM, Comp
from common import transform, translate


def pr(name, cells):
    b = bbox(cells)
    print('  %-34s %s   -- %d cells, box x %d..%d, y %d..%d' % (name + ':', lean_window(cells), len(cells), b[0], b[2], b[1], b[3]))


def env_cells(cyc_fn):
    return set().union(*[cyc_fn(t) for t in range(30)])


def set_dist(A, B):
    return min(max(abs(a[0] - b[0]), abs(a[1] - b[1])) for a in A for b in B)


def wlname(w):
    return '(%s, lane %d, tau %d)' % (DIRNAME[w[0]], w[1], w[2])


def describe(parts, controls, label, blocks=None, reuse=None, picture=True):
    """parts: list of (name, fn t -> cells).  Checks and prints the reaction with the controls."""
    cells0 = set()
    for nm, fn in parts:
        c = fn(0)
        assert not (c & cells0)
        cells0 |= c
    comp = Comp(cells0)                      # asserts period 30
    print(label)
    print(' pieces at world time 0 (mod 30):')
    for nm, fn in parts:
        pr(nm, fn(0))
    pr('whole periodic configuration R', cells0)
    cyc = comp.R.ref_cells
    assert all(set(cyc[0]) != set(cyc[q]) for q in range(1, 30))
    e = comp.R.env
    print('  period 30 (least), envelope over a cycle: x %d..%d, y %d..%d (%d x %d)' % (e[0], e[2], e[1], e[3], e[2] - e[0] + 1, e[3] - e[1] + 1))
    envs = [(nm, env_cells(fn)) for nm, fn in parts]
    print(' minimum Chebyshev distance between the envelopes (all cells over a cycle) of the pieces:')
    best = None
    for i in range(len(envs)):
        for j in range(i):
            dd = set_dist(envs[i][1], envs[j][1])
            print('    %s -- %s: %d' % (envs[j][0], envs[i][0], dd))
            best = dd if best is None else min(best, dd)
    print('    minimum: %d' % best)
    res = run_scheduled(comp, controls, limit=20000, t_hint=200)
    assert res['status'] == 'restored', res
    ok, Ts, Te = verify_scheduled(comp, controls, res)
    assert ok
    outs = sorted(w for (w, th) in res['out'])
    N = Te - Ts
    print(' reaction (set simulator, unbounded plane):  evolve %d (R ∪ C) = R ∪ G   (world times %d -> %d, both = 0 mod 30)' % (N, Ts, Te))
    start = set(cells0)
    for i, w in enumerate(controls):
        g = glider_at(*w, Ts)
        pr('C%d %s' % (i + 1, wlname(w)), g)
        start |= g
    end = set(cells0)
    for i, w in enumerate(outs):
        g = glider_at(*w, Te)
        pr('G%d %s' % (i + 1, wlname(w)), g)
        end |= g
    pr('start R ∪ C', start)
    pr('end R ∪ G', end)
    if reuse:
        for T in reuse:
            c2 = controls + [(w[0], w[1], w[2] + T) for w in controls]
            r2 = run_scheduled(comp, c2, limit=20000, t_hint=200)
            want = sorted(outs + [(w[0], w[1], w[2] + T) for w in outs])
            good = r2['status'] == 'restored' and sorted(w for (w, th) in r2['out']) == want and verify_scheduled(comp, c2, r2)[0]
            print(' second control glider(s) %d generations later: %s' % (T, 'works (set simulator)' if good else 'FAILS'))
    if blocks is not None:
        a, b = blocks
        # pullSalvo at time T0 = a.tau - 4 d translated by (-d, -d): world lines (SE, -5 + 0, ..);
        # translate the block instead: salvo lanes (L, L + 6) = (-5, 1) + (x0 - y0)
        assert a[1] + 6 == b[1] and a[2] - 29 == b[2]
        # pullSalvo translated by (u, v): lanes -5 + u - v, taus 0 - 4 u + T
        for k in range(4):
            K = k
            # choose (u, v) with u - v = a.lane + 5 and far ahead of everything: u = big
            u = max(e[2], e[3]) + 60 + (a[1] + 5)
            v = u - (a[1] + 5)
            T0 = a[2] + 4 * u                       # time at which the salvo is translate (u, v) pullSalvo
            blk = translate(set(counter(K)), u, v)
            cc = set(start) | blk
            n = (T0 - Ts) + 4 * K + 26
            n30 = 30 * ((n + 29) // 30)
            out = evolve_cells(cc, n30)
            expect = set(cells0) | translate(set(counter(K - 1)), u, v)
            assert out == expect, 'block test failed for k = %d' % K
            if k == 0:
                print(' with the block: pullSalvo translated by (%d, %d) is reached at world time %d;' % (u, v, T0))
            print('    k = %d: evolve %d (R ∪ C ∪ translate (%d, %d) (counter %d)) = R ∪ translate (%d, %d) (counter %d): checked' % (K, n30, u, v, K, u, v, K - 1))
    if picture:
        print(show(start))
    return comp, Ts, Te, outs


def reflector():
    cyc = rf_cycle()
    R = gates.Reference(set(cyc[0]))
    print('Reflector RF0 (queen bee shuttle of the gun = cells of gosperGun with x <= 17, and eater 1 at (19, 7))')
    pr('RF0', cyc[0])
    assert all(cyc[0] != cyc[q] for q in range(1, 30)) and step_cells(set(cyc[29])) == set(cyc[0])
    e = R.env
    print('  period 30 (least); envelope x %d..%d, y %d..%d' % (e[0], e[2], e[1], e[3]))
    T = -60
    for N in (30, 60):
        gi, go = glider_at(*RF_IN, T), glider_at(*RF_OUT, T + N)
        assert evolve_cells(set(cyc[0]) | gi, N) == set(cyc[0]) | go
        print('  evolve %d (RF0 ∪ %s) = RF0 ∪ %s      [in %s, out %s]' % (N, lean_window(gi), lean_window(go), wlname(RF_IN), wlname(RF_OUT)))
    print(show(set(cyc[0]) | glider_at(*RF_IN, T)))


def main():
    a = sys.argv[1:]
    if a[0] == 'reflector':
        reflector()
    elif a[0] == 'fanout':
        asm = tuple(int(x) for x in a[1:5])
        parts = [('S gun A', lambda t: asm_guns(S_ASM, t)[0]), ('S gun B', lambda t: asm_guns(S_ASM, t)[1]),
                 ('K gun A', lambda t: asm_guns(asm, t)[0]), ('K gun B', lambda t: asm_guns(asm, t)[1])]
        full = [('S = blockedStream', lambda t: asm_cells(S_ASM, t)), ('K = assembly %s' % (asm,), lambda t: asm_cells(asm, t))]
        describe(full, [C0], 'Fan-out: S and K = (k, vx, vy, s) = %s' % (asm,), reuse=[int(x) for x in a[5:]] or None)
        print(' gun bodies at world time 0 (the streams in flight belong to the assemblies as well):')
        for nm, fn in parts:
            pr(nm, fn(0))
    elif a[0] == 'generator':
        s = json.load(open('results/pg1.json'))          # the recommended design PG1
        import g4_pull3
        gb = tuple(s['gb'])
        fo = g4_pull3.FANOUT
        full = [('S = blockedStream', lambda t: asm_cells(S_ASM, t)), ('K = assembly %s' % (fo,), lambda t: asm_cells(fo, t)),
                ('Gb = assembly %s' % (gb,), lambda t: asm_cells(gb, t))]
        for i, rf in enumerate(s['rfs']):
            full.append(('RF%d = reflector %s' % (i + 1, tuple(rf)), (lambda rf: (lambda t: rf_cells(tuple(rf), t)))(rf)))
        A = (SE, s['a'][1], s['a'][2])
        B = (SE, s['b'][1], s['b'][2])
        describe(full, [C0], 'Pull-salvo generator: fan-out (S, K), gate Gb, three reflectors', blocks=(A, B),
                 reuse=[int(x) for x in a[1:]] or None, picture=False)


if __name__ == '__main__':
    main()
