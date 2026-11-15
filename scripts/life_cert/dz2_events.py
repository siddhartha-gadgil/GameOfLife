#!/usr/bin/env python3
"""Timeline of DZ2 (R-28) for the Lean certificate: the intervals during which each piece deviates
from its free cycle (events), and the free gliders in between.  Untrusted oracle; the Lean
certificate is the check.  Usage: DZ2_K=1 dz2_events.py  -> results/dz2_events_k<K>.json"""
import json
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_zero'))
from f8_full import design, frozen_pieces, reg1_pieces                  # noqa: E402
from f0_frozen import *                                                  # noqa: E402,F401
from common import step_cells, bbox                                      # noqa: E402
from net import Net, time_at, env_box, piece_cells                       # noqa: E402

M = 3


def main():
    k = int(os.environ.get('DZ2_K', '1'))
    d = design()
    reg = reg1_pieces()
    others = frozen_pieces()[len(reg):] + [d['rfr']] + d['supply'] + d['zb']
    nt = Net(reg + others)
    Ts = 30 * ((int(time_at(d['ctrl'], (-1100, -1100))) - 400) // 30)
    t_end = (d['ci'][2] + 3570 + 1200) if k == 0 else (d['n1'][2] + 2400)
    N = 30 * ((t_end - Ts) // 30 + 1)
    # groups: REG1 (one box), then each other piece
    groups = [('R%d' % i, [p], env_box(p)) for i, p in enumerate(reg)]
    for i, p in enumerate(others):
        groups.append(('P%d' % i, [p], env_box(p)))
    c = nt.cycle(Ts) | glider_at(*d['ctrl'], Ts) | translate(set(counter(k)), 148, 240)
    dev = {g[0]: [] for g in groups}
    for t in range(Ts, Ts + N + 1):
        diff = c ^ nt.cycle(t)
        hit = set()
        for q in diff:
            for name, ps, b in groups:
                if b[0] - M <= q[0] <= b[2] + M and b[1] - M <= q[1] <= b[3] + M:
                    hit.add(name)
        for name in hit:
            iv = dev[name]
            if iv and iv[-1][1] == t - 1:
                iv[-1][1] = t
            else:
                iv.append([t, t])
        if t < Ts + N:
            c = step_cells(c)
    out = {'k': k, 'Ts': Ts, 'N': N, 'groups': [(g[0], g[1], g[2]) for g in groups], 'dev': dev}
    json.dump(out, open(os.path.join(HERE, 'results', 'dz2_events_k%d.json' % k), 'w'))
    for name, ps, b in groups:
        print(name, ps, b, dev[name])


if __name__ == '__main__':
    main()
