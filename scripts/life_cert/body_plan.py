#!/usr/bin/env python3
"""Segment plan of a unit body of R-31 (whole body fact of cat_specs.json).  Usage: body_plan.py dec|inc"""
import json
import os
import pickle
import sys
import time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_zero'))
import dz2_plan as DP                                            # noqa: E402
from f0_frozen import *                                          # noqa: E402,F401,F403
from net import piece_cells                                      # noqa: E402
import plan as P                                                 # noqa: E402

T0 = time.time()


def log(s):
    print('%6.0fs %s' % (time.time() - T0, s), flush=True)


def main():
    kind = sys.argv[1]
    spec = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'cat_specs.json')))
    e = [x for x in spec['catalogue'] if x['name'] == 'unit_body_' + kind][0]['whole_body_fact']
    pieces = [tuple(p) for p in e['pieces']]
    Ts = int(e["t0"]) - 120
    D = int(e['Delta'])
    N = 30 * ((D + 180 + 29) // 30)
    groups = [g for g in DP.build_groups(pieces) if g.name != 'blk']
    log('groups: %s' % [g.name for g in groups])
    start = set()
    for p in pieces:
        start |= piece_cells(p, Ts)
    w = e['In'][0]['wl']
    start |= glider_at(NAMED[w[0]], w[1], w[2], Ts)
    cyc = []
    for r in range(30):
        cc = set()
        for p in pieces:
            cc |= piece_cells(p, Ts + r)
        cyc.append(cc)
    act, segs, final = P.plan(groups, start, Ts, N, lambda t: cyc[(t - Ts) % 30], log)
    pickle.dump({'groups': [(g.name, g.kind, g.env, getattr(g, 'members', None)) for g in groups],
                 'k': None, 'Ts': Ts, 'N': N, 'pieces': pieces, 'act': act, 'segs': segs, 'final': final},
                open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'body_%s.pkl' % kind), 'wb'))
    log('done: %d segments' % len(segs))


if __name__ == '__main__':
    main()
