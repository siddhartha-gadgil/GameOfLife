#!/usr/bin/env python3
"""Search B1: single-lane salvos for the sliding block (what ONE gate can emit).

Motivation: by the obstruction of r0_obstruction.py two guns cannot fire in the same direction on
lanes closer than 23, but `pullSalvo` and `pushSalvo` need gliders on the lanes -5 and 1.  A
salvo whose gliders all fly on ONE lane, a multiple of 30 generations apart, is exactly what one
gate releases (R-20: gates accept control gliders 30 and 60 generations apart).

The block is `counter 0` = ofRows 7 11 [3, 3].  For every lane of an SE glider that can touch it
(and lanes around), and every spacing S in SPACINGS, gliders (SE, lane, -S j), j = 0, 1, ..
(glider j+1 follows glider j at distance S generations) are sent one after the other.  After
each glider the configuration is evolved S generations; whenever the configuration just before
the next glider arrives (taken without that glider) settles to exactly one block, the
displacement of the block is recorded.  A displacement (d, d) with d != 0 is a diagonal move.

Usage: b1_single_lane.py        Output on stdout (results/b1_single_lane.txt)
"""
from common import glider_at, step_cells, bbox, counter, SE
from recipes import settle

SPACINGS = (30, 60, 90, 120, 150, 180)
NMAX = 16


def is_block(cells):
    if len(cells) != 4:
        return None
    b = bbox(cells)
    if b[2] - b[0] == 1 and b[3] - b[1] == 1:
        return (b[0], b[1])
    return None


def run(lane, S):
    """Returns the list of (number of gliders, block displacement) at which a single block is left."""
    hits = []
    cells = set(counter(0))
    LEAD = 200                       # glider j is added at time S j - LEAD, at x = -50
    t = -LEAD
    for j in range(NMAX):
        wl = (SE, lane, S * j)
        g = glider_at(*wl, t)
        if cells and bbox(cells)[0] < -60:
            return hits, 'debris reached the launch region after %d gliders' % j
        cells |= g
        # outcome of gliders 0 .. j alone
        st, ts, rest, gl = settle(cells, t, max_gen=2500, max_pop=400, max_span=160)
        if st == 'settled' and not gl:
            p = is_block(rest)
            if p is not None:
                hits.append((j + 1, (p[0] - 7, p[1] - 11)))
            elif not rest:
                return hits, 'everything destroyed after %d gliders' % (j + 1)
        elif st == 'settled' and gl and all(w[0] == SE and w[1] == lane for w in gl) and is_block(rest):
            return hits, 'gliders %d.. pass the block' % (j + 2 - len(gl))
        for _ in range(S):
            cells = step_cells(cells)
        t += S
        if len(cells) > 500:
            return hits, 'population > 500 after %d gliders' % (j + 1)
    return hits, 'stopped after %d gliders' % NMAX


def main():
    print('block ofRows 7 11 [3, 3]; SE gliders on one lane, S generations apart')
    for S in SPACINGS:
        for lane in range(-14, 6):
            hits, why = run(lane, S)
            moved = [h for h in hits if h[1] != (0, 0)]
            if True:
                print('S=%3d lane %3d: single block after n gliders at displacement: %s   [%s]' % (
                    S, lane, ', '.join('%d: (%d, %d)' % (n, p[0], p[1]) for n, p in hits), why))


if __name__ == '__main__':
    main()
