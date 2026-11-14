#!/usr/bin/env python3
"""Clearances of the recommended pull-salvo generator PG1 (results/pg1.json; or of the design
number INDEX of results/g4_pull3.json.gz): for
every flight segment of a glider, the minimum Chebyshev distance between the cells of the glider
and the envelopes (all cells over a cycle) of the pieces that the glider does not use.

Usage: g5_clearance.py [INDEX]
"""
import gzip
import json
import sys

from common import glider_at, SE, SW, NW, NE, DIRNAME, life
import machine
from machine import asm_cells
from g1_pull import rf_cells, C0, S_ASM
from g2_pull import reflect, time_at, rf_center
import g4_pull3 as g4


def env(fn):
    return set().union(*[fn(t) for t in range(30)])


def mind(w, e, ta, tb):
    best = 999
    for t in range(int(ta), int(tb), 2):
        for (x, y) in glider_at(*w, t):
            for (a, b) in e:
                dd = max(abs(x - a), abs(y - b))
                if dd < best:
                    best = dd
    return best


def main():
    if len(sys.argv) > 1:
        s = json.load(gzip.open('results/g4_pull3.json.gz', 'rt'))['good'][int(sys.argv[1])]
    else:
        s = json.load(open('results/pg1.json'))          # the recommended design PG1
    gb = tuple(s['gb'])
    rf1, rf2, rf3 = [tuple(r) for r in s['rfs']]
    E = {'S': env(lambda t: asm_cells(S_ASM, t)), 'K': env(lambda t: asm_cells(g4.FANOUT, t)),
         'Gb': env(lambda t: asm_cells(gb, t)), 'RF1': env(lambda t: rf_cells(rf1, t)),
         'RF2': env(lambda t: rf_cells(rf2, t)), 'RF3': env(lambda t: rf_cells(rf3, t))}
    o = (tuple(s['gb_out'][0]), s['gb_out'][1], s['gb_out'][2])
    a, b = (SE, s['a'][1], s['a'][2]), (SE, s['b'][1], s['b'][2])
    leg = reflect(g4.G1, SW, g4._lane_of_leg(rf1))[1]
    P2 = reflect(o, SE, g4._out_lane(rf3, o))[1]
    P1 = a if P2 == b else b
    kx, ky = life.sym_apply(gb[0], (45, 31))
    cg = (kx + gb[1], ky + gb[2])
    G0 = (SE, 14, 119)
    t_k = time_at(g4.G1, g4.KCROSS)
    t_r1, t_r2 = time_at(g4.G1, rf_center(rf1)), time_at(leg, rf_center(rf2))
    t_s, t_g, t_o, t_r3 = time_at(g4.G2, (45, 31)), time_at(g4.G2, cg), time_at(o, cg), time_at(o, rf_center(rf3))
    segs = [('C0 (control, before S)', C0, -400, 239, ['K', 'Gb', 'RF1', 'RF2', 'RF3']),
            ('G0 (S to K)', G0, 300, time_at(G0, g4.KCROSS) - 60, ['Gb', 'RF1', 'RF2', 'RF3']),
            ('G1 (K to RF1)', g4.G1, t_k + 60, t_r1 - 30, ['S', 'Gb', 'RF2', 'RF3']),
            ('leg (RF1 to RF2)', leg, t_r1 + 30, t_r2 - 30, ['S', 'K', 'Gb', 'RF3']),
            ('P1 (RF2 onwards)', P1, t_r2 + 30, t_r2 + 2000, ['S', 'K', 'Gb', 'RF1', 'RF3']),
            ('G2 (S to Gb)', g4.G2, t_s + 40, t_g - 60, ['K', 'RF1', 'RF2', 'RF3']),
            ('o (Gb to RF3)', o, t_o + 60, t_r3 - 30, ['S', 'K', 'RF1', 'RF2']),
            ('P2 (RF3 onwards)', P2, t_r3 + 30, t_r3 + 2000, ['S', 'K', 'Gb', 'RF1', 'RF2'])]
    print('world lines: G0 %s, G1 %s, leg %s, G2 %s, o %s, P1 %s, P2 %s' % (G0, g4.G1, leg, g4.G2, o, P1, P2))
    allmin = 999
    for nm, w, ta, tb, others in segs:
        ds = {k: mind(w, E[k], ta, tb) for k in others}
        allmin = min(allmin, min(ds.values()))
        print('  %-24s %s lane %d: %s' % (nm, DIRNAME[w[0]], w[1], ', '.join('%s %d' % kv for kv in ds.items())))
    print('minimum over all segments:', allmin)


if __name__ == '__main__':
    main()
