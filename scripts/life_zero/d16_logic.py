#!/usr/bin/env python3
"""D16 (R-26): the complete decision logic DZ1 with free gliders (frame of SlidingBlock.lean).

  pull salvo  (SE, -5, 0), (SE, 1, -29)                   = pullSalvo at time 0
  train       D = (NE, -10, 19), A = (NE, -10, 49), B = (NE, -10, 79)   (one lane, 30 apart)
  restore     S = (SW, 8, 58)  (with A: block (4, 11) -> (3, 10)),
              V = (NW, 13, 87) (with B: block (3, 10) -> counter 0)   (programme of d12/d15)
  O           (SE, ., .)  the Z glider; killed by B in case NZ          (searched here)
  eater E     absorbs V in case NZ                                      (searched here)

case Z (k = 0): pull -> counter (-1); D -> block (4, 11); S + A -> (3, 10); V + B -> counter 0;
               O flies on = Z.
case NZ (k >= 1): counter (k - 1); D + S annihilate; A flies on = NZ; B + O annihilate;
               V is eaten by E.
Usage: d16_logic.py search | d16_logic.py check O_LANE O_TAU EATER_JSON"""
import sys
import json
from dcat import *
from common import step_cells, life, EATER1, bbox, lean_window
from net import glider_path, set_dist
from recipes import settle

PULL = [(SE, -5, 0), (SE, 1, -29)]
D, A, B = (NE, -10, 19), (NE, -10, 49), (NE, -10, 79)
S, V = (SW, 8, 58), (NW, 13, 87)
CORE = PULL + [D, A, B, S, V]
T0 = -600
KS = (0, 1, 2, 3, 4, 5, 6, 7, 40)


def free_pairs(gl, t0=T0, back=1500):
    """every pair of gliders flies freely during the times t0 - back .. t0 (no interaction)"""
    bad = []
    for i in range(len(gl)):
        for j in range(i):
            a, b = gl[i], gl[j]
            c = glider_at(*a, t0 - back) | glider_at(*b, t0 - back)
            for t in range(t0 - back, t0):
                if c != glider_at(*a, t) | glider_at(*b, t):
                    bad.append((a, b, t))
                    break
                c = step_cells(c)
    return bad


def run(gl, k, n, extra=()):
    cells = set(counter(k)) | set(extra)
    for w in gl:
        g = glider_at(*w, T0)
        if life.chebyshev_dist(g, cells) < 3:
            return None
        cells |= g
    for _ in range(n - T0):
        cells = step_cells(cells)
    return cells


def check(O, E, n=1400, ks=KS, verbose=False):
    E = set(E)
    ok = True
    for k in ks:
        nn = n + 4 * k
        c = run(CORE + [O], k, nn, E)
        if k == 0:
            want = set(counter(0)) | E | glider_at(*O, nn)
        else:
            want = set(counter(k - 1)) | E | glider_at(*A, nn)
        good = (c == want)
        ok = ok and good
        if verbose:
            print('   k = %d: %s' % (k, 'exact' if good else 'FAILS'))
    return ok


def eater_options(g, avoid_paths, j_range, block_dist=5):
    """eater 1 placements that absorb the NW glider g (placed j cells beyond the register)"""
    forb = set()
    for p in avoid_paths:
        forb |= {(x + a, y + b) for (x, y) in p for a in range(-2, 3) for b in range(-2, 3)}
    forb |= {(x + a, y + b) for k in range(61) for (x, y) in counter(k) for a in range(-block_dist, block_dist + 1) for b in range(-block_dist, block_dist + 1)}
    out = []
    for j in j_range:
        for k in range(8):
            e0 = transform(EATER1, k)
            bb = bbox(e0)
            for dx in range(-4, 5):
                for dy in range(-4, 5):
                    # point of the NW glider's path j cells NW of the register
                    x = 6 - j + dx
                    y = (6 - j) + 13 + dy
                    e = frozenset(translate(e0, x - bb[0], y - bb[1]))
                    if e & forb:
                        continue
                    tq = int(time_at(g, (x, y))) - 60
                    c = glider_at(*g, tq)
                    if set_dist(c, e) < 4:
                        continue
                    if life.evolve_cells(set(c) | e, 200) != set(e):
                        continue
                    out.append((j, e))
    return out


if __name__ == '__main__':
    print('pairs that interact before time %d (should be none):' % T0, free_pairs(CORE))
    if sys.argv[1] == 'search':
        # 1. O: SE glider crossing the train lane x + y = 10 at (x0, 10 - x0)
        nzs = [A, B]                 # the train survivors in case NZ (D is killed by S)
        cand = []
        for x0 in range(14, 40):
            c = 2 * x0 - 10
            tb = time_at(B, (x0, 10 - x0))
            for tau in range(-600, 600):
                O = (SE, c, tau)
                to = time_at(O, (x0, 10 - x0))
                if abs(to - tb) > 6:
                    continue
                st, t, rest, gl = run_free([A, B, O], t0=int(tb) - 120, max_gen=600)
                if st == 'settled' and not rest and gl == [A]:
                    cand.append(O)
        print('O candidates (A passes, B + O annihilate):', cand)
        # 2. eater for V
        paths = [glider_path(w, -600, 1400) for w in PULL + [D, A, B, S]]
        es = eater_options(V, paths, range(14, 40))
        print('eater placements:', len(es))
        good = []
        for O in cand:
            po = glider_path(O, -600, 1400)
            for (j, e) in es:
                if set_dist(po, e) < 3:
                    continue
                if check(O, e, ks=(0, 1, 2)) and check(O, e):
                    good.append((O, j, sorted(e)))
                    print('  OK: O', O, 'eater j', j, lean_window(set(e)), flush=True)
                    break
        json.dump([(list(map(list, [g[0][0]])) + list(g[0][1:]), g[1], g[2]) for g in good],
                  open('results/d16_logic.json', 'w'))
