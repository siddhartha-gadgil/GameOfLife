#!/usr/bin/env python3
"""D2 (R-26): two-glider salvos S = (S1, S2) against the block at -1 that leave exactly counter 0
(plus at most one glider), where S1 is one of the four detector world lines of d0_single.py and
S2 passes every block counter k, k = 0 .. 3, on its own.

Usage: d2_pair.py [DT_LO DT_HI]  (S2 reaches the block between DT_LO and DT_HI generations after S1)
"""
import os
import sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, NE, NW, counter, glider_at, lean_window, DIRNAME, step_cells  # noqa: E402
from reactions import run_free                                                          # noqa: E402
from net import time_at                                                                 # noqa: E402

DETECTORS = [(SW, 9, 0), (SW, 10, 0), (NE, -10, 0), (NE, -11, 0)]
CEN = (6.5, 10.5)


def passes(wl, k):
    st, t, rest, gl = run_free([wl], extra=counter(k), t0=int(time_at(wl, CEN)) - 120, max_gen=500)
    return st == 'settled' and set(rest) == set(counter(k)) and gl == [wl]


def lanes(d):
    c = d[1] * CEN[0] - d[0] * CEN[1]
    return range(int(c) - 16, int(c) + 17)


def free_ok(a, b, t0):
    c = glider_at(*a, t0) | glider_at(*b, t0)
    for t in range(t0, t0 + 400):
        if c != glider_at(*a, t) | glider_at(*b, t):
            return False
        c = step_cells(c)
    return True


def job(args):
    s1, d, lane, lo, hi = args
    out = []
    w = (d, lane, 0)
    if not all(passes(w, k) for k in range(4)):
        return out
    tc1 = time_at(s1, CEN)
    for tau in range(-400, 400):
        s2 = (d, lane, tau)
        dt = time_at(s2, CEN) - tc1
        if not (lo <= dt <= hi):
            continue
        t0 = int(min(tc1, time_at(s2, CEN))) - 60
        st, t, rest, gl = run_free([s1, s2], extra=counter(-1), t0=t0, max_gen=700, max_pop=200, max_span=80)
        if st == 'settled' and set(rest) == set(counter(0)) and len(gl) <= 1:
            if free_ok(s1, s2, t0 - 200):
                out.append((s1, s2, gl, t - t0))
    return out


if __name__ == '__main__':
    lo, hi = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (-30, 60)
    jobs = [(s1, d, lane, lo, hi) for s1 in DETECTORS for d in (SE, SW, NW, NE) for lane in lanes(d)]
    n = 0
    with Pool(8) as p:
        for res in p.imap_unordered(job, jobs):
            for (s1, s2, gl, dur) in res:
                n += 1
                print('S1', s1, 'S2', s2, '-> counter 0 +', gl, 'dur', dur, flush=True)
    print('hits', n)
