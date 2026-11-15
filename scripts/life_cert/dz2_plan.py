#!/usr/bin/env python3
"""The segment plan of DZ2 (R-28) for k = DZ2_K (untrusted oracle).  -> results/dz2_plan_k<K>.pkl"""
import os
import pickle
import sys
import time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_zero'))
from f8_full import design, frozen_pieces, reg1_pieces          # noqa: E402
from f0_frozen import *                                          # noqa: E402,F401,F403
from net import time_at, env_box, piece_cells                    # noqa: E402
import plan as P                                                 # noqa: E402

T0 = time.time()


def log(s):
    print('%6.0fs %s' % (time.time() - T0, s), flush=True)


def build_groups(pieces):
    """Pieces closer than the detection margin form one group; plus the block group."""
    # clusters of pieces closer than the detection margin form one group
    cl = [[i] for i in range(len(pieces))]
    def cbox(c):
        bs = [env_box(pieces[i]) for i in c]
        return (min(b[0] for b in bs), min(b[1] for b in bs), max(b[2] for b in bs), max(b[3] for b in bs))
    changed = True
    while changed:
        changed = False
        for x in range(len(cl)):
            for y in range(x):
                bx, by = cbox(cl[x]), cbox(cl[y])
                if not P.far(P.grow(bx, P.ME + 3), by):
                    cl[y] = cl[y] + cl[x]
                    del cl[x]
                    changed = True
                    break
            if changed:
                break
    groups = []
    for c in cl:
        ps = [pieces[i] for i in c]
        g = P.Group('g' + '_'.join(str(i) for i in sorted(c)), 'piece', cbox(c),
                    (lambda t, ps=ps: set().union(*[piece_cells(p, t) for p in ps])))
        g.members = sorted(c)
        groups.append(g)
    groups.append(P.Group('blk', 'still', (137, 227, 163, 256)))
    return groups


def main():
    k = int(os.environ.get('DZ2_K', '1'))
    d = design()
    pieces = reg1_pieces() + frozen_pieces()[len(reg1_pieces()):] + [d['rfr']] + d['supply'] + d['zb']
    Ts = 30 * ((int(time_at(d['ctrl'], (-1100, -1100))) - 400) // 30)
    t_end = (d['ci'][2] + 3570 + 1200) if k == 0 else (d['n1'][2] + 2400)
    N = 30 * ((t_end - Ts) // 30 + 1)
    groups = build_groups(pieces)
    log('groups: %s' % [g.name for g in groups])
    start = set()
    for p in pieces:
        start |= piece_cells(p, Ts)
    start |= glider_at(*d['ctrl'], Ts) | translate(set(counter(k)), 148, 240)
    cyc = []
    for r in range(30):
        cc = set()
        for p in pieces:
            cc |= piece_cells(p, Ts + r)
        cyc.append(cc)
    act, segs, final = P.plan(groups, start, Ts, N, lambda t: cyc[(t - Ts) % 30], log)
    pickle.dump({'groups': [(g.name, g.kind, g.env, getattr(g, 'members', None)) for g in groups],
                 'k': k, 'Ts': Ts, 'N': N, 'pieces': pieces, 'act': act, 'segs': segs,
                 'final': final}, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'dz2_plan_k%d.pkl' % k), 'wb'))
    log('done: %d segments' % len(segs))


if __name__ == '__main__':
    main()
