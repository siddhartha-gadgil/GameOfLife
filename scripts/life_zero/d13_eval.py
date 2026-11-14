#!/usr/bin/env python3
"""D13 (R-26): evaluate a restore program (d12_programs.py) with the pull salvo and the detector:
scan the delays s1 (step 1 after the detector) and s2 (step 2 after step 1); a glider on the
detector's lane must be 30 m generations from it.  Case Z (k = 0) must give exactly counter 0;
case NZ (k = 1 .. 7, 40) must give counter (k - 1) plus a set of free gliders that is the same
for every k.  Prints the valid (s1, s2) with the NZ survivors."""
import sys
from dcat import *
from common import step_cells, life, glider_worldline
from recipes import settle

T0 = -500
PULL = [(SE, -5, 0), (SE, 1, -29)]
MPULL = [(SE, -2, -6), (SE, -8, -11)]


def evolve_from(gl, k, n):
    cells = set(counter(k))
    for w in gl:
        g = glider_at(*w, T0)
        if cells and life.chebyshev_dist(g, cells) < 3:
            return None
        cells |= g
    for _ in range(n - T0):
        cells = step_cells(cells)
    return cells


def outcome(gl, k, n):
    c = evolve_from(gl, k, n)
    if c is None:
        return None
    st, t, rest, out = settle(c, n, max_gen=400, max_pop=400, max_span=200)
    if st != 'settled':
        return None
    return frozenset(rest), tuple(out), t


def program(mirror, D, steps, s1, s2):
    gl = [shift_wl(w, 0, 0, s1) for w in steps[0]] + [shift_wl(w, 0, 0, s1 + s2) for w in steps[1]]
    return (MPULL if mirror else PULL) + [D] + gl


def evaluate(mirror, D, steps, s1r, s2r, ks=(1, 2, 3, 4, 5, 6, 7, 40)):
    res = []
    for s1 in s1r:
        for s2 in s2r:
            gl = program(mirror, D, steps, s1, s2)
            same = [w for w in gl if w[0] == D[0] and w[1] == D[1] and w != D]
            if any((w[2] - D[2]) % 30 for w in same):
                continue
            n = 1200
            c = evolve_from(gl, 0, n)
            if c != set(counter(0)):
                continue
            surv = None
            good = True
            for k in ks:
                o = outcome(gl, k, n + 4 * k)
                if o is None or o[0] != frozenset(counter(k - 1)):
                    good = False
                    break
                # survivors as world lines (independent of the time of settling)
                if surv is None:
                    surv = o[1]
                elif o[1] != surv:
                    good = False
                    break
            if good:
                res.append((s1, s2, surv))
                print('  s1', s1, 's2', s2, 'NZ survivors', [(DIRNAME[w[0]], w[1], w[2]) for w in surv], flush=True)
    return res


def first_steps(mirror, D, st1, pos, s1r):
    """delays s1 for which salvo + D + step 1 take counter 0 to the block at pos (case Z)"""
    out = []
    for s1 in s1r:
        gl = (MPULL if mirror else PULL) + [D] + [shift_wl(w, 0, 0, s1) for w in st1]
        if evolve_from(gl, 0, 900) == set(translate(BLOCK, *pos)):
            out.append(s1)
    return out


if __name__ == '__main__':
    import ast
    mirror = sys.argv[1] == 'mirror'
    tauD = int(sys.argv[2])
    D = (SW, 9, tauD) if mirror else (NE, -10, tauD)
    st1 = [(NAMED[a], b, c) for (a, b, c) in ast.literal_eval(sys.argv[3])]
    pos = ast.literal_eval(sys.argv[4])
    st2 = [(NAMED[a], b, c) for (a, b, c) in ast.literal_eval(sys.argv[5])]
    print('detector', D, 'step 1', st1, '->', pos, 'step 2', st2, flush=True)
    s1s = first_steps(mirror, D, st1, pos, range(0, 300))
    print('valid s1 (case Z, step 1 only):', s1s, flush=True)
    for s1 in s1s[:1] + s1s[len(s1s) // 2: len(s1s) // 2 + 1]:
        evaluate(mirror, D, [st1, st2], [s1], range(0, 250))
