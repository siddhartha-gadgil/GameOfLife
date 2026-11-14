#!/usr/bin/env python3
"""P1: the 176 three-glider pushes of scripts/life_search (results/block_salvo_hits.txt, read-only)
as glider world lines in the conventions of this directory, each re-checked by simulation.

Frame: the block has its upper left cell at (0, 0) (lane 0).  A push is a list of three world
lines (SE, lane, tau); the whole salvo may be translated by (j, j), which subtracts 4 j from all
tau, so only tau differences matter.  Output: results/p1_pushes.json (list of records
{'wl': [[lane, tau] x 3] sorted by tau, 'n': generations from the normal form}), and a table of
the lane patterns on stdout.

`pushSalvo` of SlidingBlock.lean is the hit (-1, 0), (5, -29), (5, -4) (asserted).
"""
import json
import os
import re

from common import (HERE, life, evolve_cells, translate, worldlines_of, glider_at, SE, PUSH_SALVO,
                    counter, bbox)

HITS = os.path.join(HERE, '..', 'life_search', 'results', 'block_salvo_hits.txt')
BLOCK0 = frozenset({(0, 0), (1, 0), (0, 1), (1, 1)})


def load():
    out = []
    for line in open(HITS):
        if not line.startswith('1 1 '):
            continue
        head, names, nf = [s.strip() for s in line.split('|')]
        n = int(head.split()[2])
        gl = []
        for tok in nf.split():
            m = re.fullmatch(r'(-?\d+),(-?\d+)\+(\d+)', tok)
            x, y, t = int(m.group(1)), int(m.group(2)), int(m.group(3))
            gl.append(evolve_cells(translate(life.GLIDER, x, y), t))
        if len(gl) != 3:
            continue
        cells = set().union(*gl)
        wls = [life.glider_worldline(g, 0) for g in gl]
        assert all(w is not None for w in wls) and len(cells) == 15
        end = evolve_cells(cells | BLOCK0, n)
        assert end == translate(BLOCK0, 1, 1), line
        t0 = max(w[2] for w in wls)
        wl = sorted([[w[1], w[2] - t0] for w in wls], key=lambda w: (w[1], w[0]))
        out.append({'wl': wl, 'n': n, 'name': names})
    return out


def salvo_cells(rec, L, t, time):
    """The salvo with lanes L + lane_i and tau = t + tau_i, at the given time."""
    c = set()
    for (l, tau) in rec['wl']:
        c |= glider_at(SE, L + l, t + tau, time)
    return c


def main():
    P = load()
    print('three-glider pushes re-checked: %d' % len(P))
    # pushSalvo: block counter 0 at (7, 11) (lane -4); world lines (-5, 0), (1, -29), (1, -4)
    key = sorted([[-1, 0], [5, -29], [5, -4]], key=lambda w: (w[1], w[0]))
    assert any(p['wl'] == key for p in P)
    json.dump(P, open(os.path.join(HERE, 'results', 'p1_pushes.json'), 'w'))
    print('lanes (sorted) and tau - tau_last, by minimal lane gap:')
    rows = []
    for p in P:
        ls = sorted(w[0] for w in p['wl'])
        gap = min(ls[1] - ls[0], ls[2] - ls[1])
        same30 = [(a, b) for a in p['wl'] for b in p['wl'] if a is not b and a[0] == b[0] and (a[1] - b[1]) % 30 == 0]
        rows.append((gap, p['wl'], p['n'], bool(same30)))
    for gap, wl, n, s in sorted(rows, key=lambda r: (-r[0], r[2])):
        print('  gap %2d  n %3d  %s%s' % (gap, n, wl, '   SAME LANE 30 APART' if s else ''))


if __name__ == '__main__':
    main()
