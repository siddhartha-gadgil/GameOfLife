#!/usr/bin/env python3
"""D15 (R-26): like d13_eval.py, but every glider on the detector's lane is forced to be 30 m
generations after the detector (s1, s2 chosen accordingly); prints Z/NZ outcomes per k."""
import sys, ast
from d13_eval import *


def same_lane_ok(D, gl):
    return all((w[2] - D[2]) % 30 == 0 for w in gl if w[0] == D[0] and w[1] == D[1] and w != D)


if __name__ == '__main__':
    mirror = sys.argv[1] == 'mirror'
    tauD = int(sys.argv[2])
    D = (SW, 9, tauD) if mirror else (NE, -10, tauD)
    st1 = [(NAMED[a], b, c) for (a, b, c) in ast.literal_eval(sys.argv[3])]
    pos = ast.literal_eval(sys.argv[4])
    st2 = [(NAMED[a], b, c) for (a, b, c) in ast.literal_eval(sys.argv[5])]
    s1s = [s for s in first_steps(mirror, D, st1, pos, range(0, 300))
           if same_lane_ok(D, [shift_wl(w, 0, 0, s) for w in st1])]
    print('s1 candidates', s1s, flush=True)
    for s1 in s1s[:3]:
        for s2 in range(0, 300):
            gl = program(mirror, D, [st1, st2], s1, s2)
            if not same_lane_ok(D, gl):
                continue
            c = evolve_from(gl, 0, 1300)
            if c != set(counter(0)):
                continue
            rows = []
            for k in (1, 2, 3, 4, 5, 40):
                o = outcome(gl, k, 1300 + 4 * k)
                rows.append(None if o is None else (o[0] == frozenset(counter(k - 1)), [(DIRNAME[w[0]], w[1], w[2]) for w in o[1]]))
            print('s1', s1, 's2', s2, 'Z ok; NZ:', rows, flush=True)
