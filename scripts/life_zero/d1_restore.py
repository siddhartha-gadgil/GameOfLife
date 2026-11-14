#!/usr/bin/env python3
"""D1 (R-26): after a detector glider has hit the block at -1 (constellations X of d0_single.py),
which single glider R turns X into counter 0 (plus at most one glider), and does R pass the
blocks counter k, k = 0 .. 3 untouched?
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, NE, NW, counter, glider_at, lean_window, DIRNAME, bbox   # noqa: E402
from reactions import run_free                                                     # noqa: E402

DETECTORS = [(SW, 9, 0), (SW, 10, 0), (NE, -10, 0), (NE, -11, 0)]


def settle_from(cells, wls, t0, gen=1500):
    return run_free(wls, extra=cells, t0=t0, max_gen=gen, max_pop=300, max_span=150)


def x_of(det):
    st, t, rest, gl = run_free([det], extra=counter(-1), t0=-200, max_gen=600)
    assert st == 'settled' and not gl
    return set(rest)


def passes(wl, k):
    st, t, rest, gl = run_free([wl], extra=counter(k), t0=wl[2] - 300, max_gen=800)
    return st == 'settled' and set(rest) == set(counter(k)) and gl == [wl]


if __name__ == '__main__':
    for det in DETECTORS:
        X = x_of(det)
        b = bbox(X)
        print('detector', DIRNAME[det[0]], det[1], 'X =', lean_window(X))
        cx, cy = (b[0] + b[2]) // 2, (b[1] + b[3]) // 2
        for d in (SE, SW, NW, NE):
            # lane of the line through the centre
            l0 = d[1] * cx - d[0] * cy
            for lane in range(l0 - 14, l0 + 15):
                wl = (d, lane, 0)
                st, t, rest, gl = run_free([wl], extra=X, t0=-400, max_gen=1500, max_pop=300, max_span=150)
                if st != 'settled':
                    continue
                if set(rest) == set(counter(0)) and len(gl) <= 1:
                    ok = [k for k in range(0, 4) if passes(wl, k)]
                    print('   R', DIRNAME[d], lane, '-> counter 0 +', gl, 'passes k =', ok)
