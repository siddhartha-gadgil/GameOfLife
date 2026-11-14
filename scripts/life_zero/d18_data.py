#!/usr/bin/env python3
"""D18 (R-26): cell data of DZ1 for the report (frame of SlidingBlock.lean): the inputs at time 0,
the final configurations, the duration N, the box of the reaction, separations, and the reuse
spacing T (a second copy of all inputs T generations later)."""
from d16_logic import *
from common import cells_of_window

O = (SE, 60, 73)
E = set(cells_of_window(-12, 1, [3, 2, 10, 12]))
INP = PULL + [D, A, B, S, V, O]
NAMES = ['a (salvo)', 'b (salvo)', 'D', 'A', 'B', 'S', 'V', 'O']


def run_box(gl, k, t0, n, extra=()):
    cells = set(counter(k)) | set(E) | set(extra)
    for w in gl:
        cells |= glider_at(*w, t0)
    box = list(bbox(cells))
    for _ in range(n):
        cells = step_cells(cells)
        b = bbox(cells)
        box = [min(box[0], b[0]), min(box[1], b[1]), max(box[2], b[2]), max(box[3], b[3])]
    return cells, box


if __name__ == '__main__':
    t0 = -120
    start0 = set()
    for nm, w in zip(NAMES, INP):
        g = glider_at(*w, t0)
        print('  %-10s %-16s at time %d: %s' % (nm, (DIRNAME[w[0]],) + w[1:], t0, lean_window(g)))
    allg = [glider_at(*w, t0) for w in INP] + [set(E), set(counter(0))]
    sep = min(life.chebyshev_dist(allg[i], allg[j]) for i in range(len(allg)) for j in range(i))
    print('  minimum distance between the inputs, the eater and counter 0 at time %d: %d' % (t0, sep))
    print('  eater E: %s' % lean_window(E))
    n = 360
    for k in (0, 1, 2, 3, 40):
        nn = n + 4 * k if k == 40 else n
        c, box = run_box(INP, k, t0, nn - t0 if False else nn)
        out = O if k == 0 else A
        want = set(counter(max(k - 1, 0) if k else 0)) | E | glider_at(*out, t0 + nn)
        if k >= 1:
            want = set(counter(k - 1)) | E | glider_at(*out, t0 + nn)
        rest = c - set(E) - set(counter(k - 1 if k else 0))
        print('  k = %2d: evolve %d (inputs ∪ E ∪ counter %d) = E ∪ counter %d ∪ %s %s: %s; box x %d..%d, y %d..%d' % (
            k, nn, k, k - 1 if k else 0, 'Z' if k == 0 else 'NZ', lean_window(rest), 'exact' if c == want else 'FAILS',
            box[0], box[2], box[1], box[3]))
    # reuse: a second copy T later; k = 2 -> 1 -> 0 (NZ, NZ), k = 1 -> 0 -> 0 (NZ, Z), k = 0 -> 0 -> 0 (Z, Z)
    for T in range(60, 900, 30):
        good = True
        for (k, outs) in ((1, [A, shift_wl(O, 0, 0, T)]), (2, [A, shift_wl(A, 0, 0, T)]), (3, [A, shift_wl(A, 0, 0, T)]),
                          (0, [O, shift_wl(O, 0, 0, T)])):
            gl = INP + [shift_wl(w, 0, 0, T) for w in INP]
            ke = max(k - 2, 0)
            c, box = run_box(gl, k, -200, T + 900)
            want = set(counter(ke)) | E
            for w in outs:
                want |= glider_at(*w, T + 700)
            if c != want:
                good = False
                break
        if good:
            print('  reuse: a second copy of all inputs %d generations later works (k = 0, 1, 2, 3; smaller multiples of 30 fail)' % T)
            break
