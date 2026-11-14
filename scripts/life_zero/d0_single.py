#!/usr/bin/env python3
"""D0 (R-26): one glider against the block at -1 (counter (-1), frame of SlidingBlock.lean).

For SW and NE gliders on every lane that touches the block region, the outcome (settled
constellation + gliders), and whether the same lane passes the blocks at 0 .. 3 untouched.
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, NE, NW, counter, glider_at, lean_window, DIRNAME   # noqa: E402
from reactions import run_free                                               # noqa: E402


def passes(wl, k):
    st, t, rest, gl = run_free([wl], extra=counter(k), t0=wl[2] - 200, max_gen=600)
    return st == 'settled' and set(rest) == set(counter(k)) and gl == [wl]


def outcome(wl, k=-1):
    st, t, rest, gl = run_free([wl], extra=counter(k), t0=wl[2] - 200, max_gen=1500, max_pop=300, max_span=150)
    return st, t, rest, gl


if __name__ == '__main__':
    for d in (SW, NE):
        for lane in range(-10, 50) if d == SW else range(-50, 10):
            wl = (d, lane, 0)
            st, t, rest, gl = outcome(wl)
            if st == 'settled' and gl == [wl] and set(rest) == set(counter(-1)):
                continue
            pz = all(passes(wl, k) for k in range(0, 4))
            r = lean_window(rest) if rest else 'empty'
            print(DIRNAME[d], lane, st, 'rest', r, 'gliders', gl, 'passes 0..3' if pz else '')
