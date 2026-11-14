#!/usr/bin/env python3
"""Z5 (R-25): the alternative zero-test decision logic, complete with one eater, verified with the
set simulator of scripts/life_gates on the unbounded plane (frame of SlidingBlock.lean).

Inputs (all at time 0): A1 = (SW, 12, 0), A2 = (SW, 12, 30), B = (SW, 8, 53) (unconditional
zero-test salvo of z1_salvo.py: the block at 0 destroys all three and stays at 0; every block
k >= 1 lets all three pass) and a detector D (SE) of z2_detector.py (A1 annihilates D when it has
passed the register).  One survivor in case NZ is absorbed by an eater 1 (searched here), the
other one is the output NZ.  No glider of the logic ever returns towards the inputs.

Checked:  k = 0:  evolve N (S + D + E + counter 0) = counter 0 + E + Z      (Z = D flown on)
          k = 1..12, 40:  evolve N (S + D + E + counter k) = counter k + E + NZ
Usage: z5_logic.py [L_D tau_D] > results/z5_logic.txt
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import (SE, SW, counter, glider_at, transform, translate, bbox, EATER1, life,    # noqa: E402
                    lean_window, DIRNAME)
from net import glider_path, set_dist                                                     # noqa: E402

A1, A2, B = (SW, 12, 0), (SW, 12, 30), (SW, 8, 53)
T0, N = -300, 900


def cells(wls, t):
    c = set()
    for w in wls:
        c |= glider_at(*w, t)
    return c


def _dilate(cs, r):
    return {(x + a, y + b) for (x, y) in cs for a in range(-r + 1, r) for b in range(-r + 1, r)}


def eaters(g, avoid):
    """Eaters 1 absorbing the SW glider g cleanly, at distance >= 2 from the paths of the
    gliders `avoid` and >= 5 from the blocks counter 0..60, placed 25 .. 70 cells beyond the
    register (first distance j with a solution)."""
    out = []
    forb = set()
    for w in avoid:
        forb |= _dilate(glider_path(w, -600, 1200), 2)
    forb |= _dilate(set().union(*[counter(k) for k in range(61)]), 5)
    for j in range(25, 71):
        for k in range(8):
            e0 = transform(EATER1, k)
            b = bbox(e0)
            for dx in range(-4, 5):
                for dy in range(-4, 5):
                    x = -j + dx
                    y = g[1] + j + dy
                    e = frozenset(translate(e0, x - b[0], y - b[1]))
                    if e & forb:
                        continue
                    tq = g[2] + 4 * j - 80
                    c = glider_at(*g, tq)
                    if set_dist(c, e) < 4:
                        continue
                    if life.evolve_cells(set(c) | e, 200) != set(e):
                        continue
                    out.append((j, e))
        if out:
            return out
    return out


def check(D, E, nz):
    E = set(E)
    res = {}
    for k in [0] + list(range(1, 13)) + [40]:
        start = cells([A1, A2, B, D], T0) | E | set(counter(k))
        end = life.evolve_cells(start, N)
        exp = E | set(counter(k)) | (glider_at(*D, T0 + N) if k == 0 else glider_at(*nz, T0 + N))
        res[k] = (end == exp)
    return res


def probe(g, other, js=range(25, 71, 5)):
    """All eater 1 placements absorbing g (no distance filter) and their distance to the path of
    `other`."""
    res = []
    po = glider_path(other, -600, 1200)
    for j in js:
        for k in range(8):
            e0 = transform(EATER1, k)
            b = bbox(e0)
            for dx in range(-4, 5):
                for dy in range(-4, 5):
                    e = frozenset(translate(e0, -j + dx - b[0], g[1] + j + dy - b[1]))
                    tq = g[2] + 4 * j - 80
                    c = glider_at(*g, tq)
                    if set_dist(c, e) < 4 or life.evolve_cells(set(c) | e, 200) != set(e):
                        continue
                    res.append((j, k, set_dist(e, po)))
    return res


def main():
    sys.stdout.reconfigure(line_buffering=True)
    D = (SE, int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (SE, -29, 64)
    print('alternative decision: A1 %s, A2 %s, B %s, D %s' % (A1, A2, B, D))
    for eat, nz in ((A2, B), (B, A2), (A1, B)):
        r = probe(eat, nz)
        print(' eater 1 absorbing %s (j = 25, 30, .., 70): %d placements; max distance to the path of %s: %s' % (
            eat, len(r), nz, max(x[2] for x in r) if r else None))
    for eat, nz in ((A2, B), (B, A2)):
        es = eaters(eat, [nz, D])
        print(' eat %s, NZ = %s: %d eater placements at distance >= 2 from the NZ and D paths' % (eat, nz, len(es)))
        for j, e in es[:4]:
            r = check(D, e, nz)
            ok = all(r.values())
            print('   eater %s (j %d): k = 0 -> Z, k = 1..12, 40 -> NZ: %s' % (lean_window(e), j, 'ALL OK' if ok else r))
            if ok:
                show(D, e, nz)
                return


def show(D, E, nz):
    print('\nDESIGN (frame of SlidingBlock.lean, numerical observation, not verified in Lean)')
    X = cells([A1, A2, B, D], 0)
    print('  inputs at time 0 (A1, A2, B, D):', lean_window(X))
    print('  eater E:', lean_window(set(E)))
    print('  Z  = D  = (%s, %d, %d); at time %d: %s' % (DIRNAME[D[0]], D[1], D[2], T0 + N, lean_window(glider_at(*D, T0 + N))))
    print('  NZ =      (%s, %d, %d); at time %d: %s' % (DIRNAME[nz[0]], nz[1], nz[2], T0 + N, lean_window(glider_at(*nz, T0 + N))))
    blocks = set().union(*[counter(k) for k in range(61)])
    for nm, w in (('A1', A1), ('A2', A2), ('B', B), ('D', D)):
        print('  path of %s (times -300 .. 900) to blocks counter 1..60: %d' % (
            nm, set_dist(glider_path(w, -300, 900), set().union(*[counter(k) for k in range(1, 61)]))))
    print('  eater to blocks 0..60: %d; eater to the paths of D, NZ: %d, %d' % (
        set_dist(set(E), blocks), set_dist(set(E), glider_path(D, -600, 1500)), set_dist(set(E), glider_path(nz, -600, 1500))))
    # envelope box of the reactions
    for k in (0, 1):
        c = cells([A1, A2, B, D], T0) | set(E) | set(counter(k))
        bb = list(bbox(c))
        for _ in range(N):
            c = life.step_cells(c)
            b = bbox(c)
            bb = [min(bb[0], b[0]), min(bb[1], b[1]), max(bb[2], b[2]), max(bb[3], b[3])]
        print('  k = %d: box of all generations %d .. %d: x %d..%d, y %d..%d' % (k, T0, T0 + N, bb[0], bb[2], bb[1], bb[3]))


if __name__ == '__main__':
    main()
