#!/usr/bin/env python3
"""Shared helpers of the d* scripts (R-26): the catalogue of d4_block2.py closed under the 8
symmetries of the block, translations of reactions, harmlessness of a glider for the register."""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, NE, NW, counter, glider_at, DIRNAME, cells_of_window, translate, transform, life  # noqa: E402
from reactions import run_free, shift_wl, sym_wl                                                          # noqa: E402
from net import time_at                                                                                   # noqa: E402

NAMED = {'SE': SE, 'SW': SW, 'NE': NE, 'NW': NW}
BLOCK = frozenset(cells_of_window(0, 0, [3, 3]))


def parse_line(line):
    import ast
    a = line.split(None, 7)
    if len(a) < 8 or a[0] not in NAMED:
        return None
    rest = a[7].rsplit(' ', 1)
    g1 = (NAMED[a[0]], int(a[1]), 0)
    g2 = (NAMED[a[2]], int(a[3]), int(a[4]))
    gl = [tuple((tuple(w[0]), w[1], w[2])) for w in ast.literal_eval(rest[0])]
    return (g1, g2, (int(a[5]), int(a[6])), gl, rest[1] == 'True')


def sym_unit(unit, k):
    """Image of a reaction with the block (0,0) under sym_k, translated back to the block (0,0)."""
    g1, g2, disp, gl, free = unit
    b = transform(BLOCK, k)
    ox, oy = min(b)
    f = lambda w: shift_wl(sym_wl(w, k), -ox, -oy, 0)
    d2 = transform(translate(BLOCK, *disp), k)
    nd = min(d2)
    return (f(g1), f(g2), (nd[0] - ox, nd[1] - oy), [f(w) for w in gl], free)


def load_units(path=os.path.join(HERE, 'results', 'd4_block2.txt.gz')):
    seen = set()
    out = []
    import gzip
    for line in gzip.open(path, 'rt'):
        u = parse_line(line)
        if u is None:
            continue
        for k in range(8):
            v = sym_unit(u, k)
            key = (tuple(sorted([v[0], v[1]])),)
            # normalise the time: earliest glider tau shift is irrelevant -> key by relative data
            g1, g2 = sorted([v[0], v[1]])
            s = -g1[2]
            key = (shift_wl(g1, 0, 0, s), shift_wl(g2, 0, 0, s))
            if key in seen:
                continue
            seen.add(key)
            out.append(v)
    return out


def move_unit(unit, p, q, s):
    g1, g2, disp, gl, free = unit
    f = lambda w: shift_wl(w, p, q, s)
    return (f(g1), f(g2), disp, [f(w) for w in gl], free)


INTER_REL = {SE: range(-5, 7), NW: range(-5, 7), NE: range(-5, 7), SW: range(-7, 5)}


def lane_of(d, p):
    return d[1] * p[0] - d[0] * p[1]


def harmless(w, kmax=200):
    """Does the glider (world line, frame of SlidingBlock.lean) pass every counter k, k >= 0
    (lane criterion of d3_moves.py, single glider against a still block)?"""
    d, L, _ = w
    for k in range(0, kmax):
        if L - lane_of(d, (7 + k, 11 + k)) in INTER_REL[d]:
            return False
    return True


def passes_sim(w, k):
    st, t, rest, gl = run_free([w], extra=counter(k), t0=int(time_at(w, (7 + k, 11 + k))) - 80, max_gen=500)
    return st == 'settled' and set(rest) == set(counter(k)) and gl == [w]


class Near:
    """A fixed set of cells with fast Chebyshev distance queries (bucket grid)."""

    def __init__(self, cells, size=16):
        self.size = size
        self.b = {}
        for (x, y) in cells:
            self.b.setdefault((x // size, y // size), []).append((x, y))

    def dist(self, A, cap=64):
        """min(cap, Chebyshev distance between A and the set)"""
        s = self.size
        r = cap // s + 1
        best = cap
        seen = {}
        for (x, y) in A:
            bx, by = x // s, y // s
            for i in range(bx - r, bx + r + 1):
                for j in range(by - r, by + r + 1):
                    L = self.b.get((i, j))
                    if not L:
                        continue
                    # lower bound by bucket
                    dx = max(i * s - x, x - (i * s + s - 1), 0)
                    dy = max(j * s - y, y - (j * s + s - 1), 0)
                    if max(dx, dy) >= best:
                        continue
                    for (a, b) in L:
                        d = max(abs(a - x), abs(b - y))
                        if d < best:
                            best = d
                            if best == 0:
                                return 0
        return best
