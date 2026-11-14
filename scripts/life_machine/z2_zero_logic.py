#!/usr/bin/env python3
"""Z2: zero-test logic with the unconditional three-glider test (Collisions.lean
`zeroTestSalvo_hit`, R-19 R7) and a detector glider; free gliders and two eaters, no guns.

Frame of SlidingBlock.lean: block at position k = `counter k`.  Test gliders (all SW, time 0):
   T1 = ofRows 6 6 [2, 1, 7],  T2 = ofRows 5 0 [2, 1, 7],  T3 = ofRows 13 (-2) [1, 5, 3]
(their union with counter 0 evolves in 33 generations to counter 0).  A detector D flies SE on a
lane to the left of the register, timed so that one test glider Ti, if it passed the register,
kicks it back (kickback SE + SW -> NW): output NZ (flying NW).  If the block is at 0 the test
gliders are consumed (the block is restored) and D flies on: output Z = D.  The two other test
gliders, which pass when k >= 1, are absorbed by eaters (eater 1, all 8 orientations, positions
along their lanes) placed beyond the detector lane.

Checked with the set simulator, for every accepted design:
   k = 0:            counter 0 + T + D + eaters  ->  counter 0 + eaters + Z (= D)
   k = 1..KMAX, 40:  counter k + T + D + eaters  ->  counter k + eaters + NZ
Usage: z2_zero_logic.py      Output: results/z2_zero_logic.txt (stdout)
"""
from common import (cells_of_window, glider_at, glider_worldline, evolve_cells, counter, SE, SW, NW, NE,
                    DIRNAME, lean_window, transform, translate, bbox, EATER1, life)
from reactions import KICK, fit
from net import glider_path, set_dist

TS = [glider_worldline(cells_of_window(6, 6, [2, 1, 7]), 0),
      glider_worldline(cells_of_window(5, 0, [2, 1, 7]), 0),
      glider_worldline(cells_of_window(13, -2, [1, 5, 3]), 0)]
KMAX = 12
T0, N = -300, 1400


def test_cells(t):
    c = set()
    for w in TS:
        c |= glider_at(*w, t)
    return c


def eater_for(g, j):
    """Eaters (cells) that absorb the glider g (SW), placed j cells along its lane; all
    orientations that absorb it cleanly."""
    out = []
    d, lane, tau = g
    for k in range(8):
        e0 = transform(EATER1, k)
        b = bbox(e0)
        for dx in range(-6, 7):
            # glider at time tau-ish around point p = (x, y) on its lane: x + y = lane (SW: lane = x + y)
            x = -j + dx
            y = lane - (-j)
            e = translate(e0, x - b[0], y - b[1] + 4)
            t0 = tau + 4 * j - 60
            c = glider_at(*g, t0)
            if set_dist(c, e) < 3:
                continue
            if evolve_cells(c | e, 200) == e:
                out.append(e)
    return out


def main():
    assert evolve_cells(test_cells(0) | set(counter(0)), 33) == set(counter(0))
    print('test salvo T1, T2, T3 =', [(DIRNAME[w[0]], w[1], w[2]) for w in TS], '; zeroTestSalvo_hit checked')
    found = []
    for i in range(3):
        for j in range(4, 40):
            ins, outs = fit(KICK, 1, TS[i], j)
            D, NZ = ins[0], outs[0]
            # NZ case without eaters: other test gliders must fly on unchanged
            others = [TS[q] for q in range(3) if q != i]
            ok = True
            for k in list(range(1, KMAX + 1)) + [40]:
                c = set(counter(k)) | test_cells(T0) | glider_at(*D, T0)
                e = set(counter(k)) | glider_at(*NZ, T0 + N)
                for w in others:
                    e |= glider_at(*w, T0 + N)
                if evolve_cells(c, N) != e:
                    ok = False
                    break
            if not ok:
                continue
            c = set(counter(0)) | test_cells(T0) | glider_at(*D, T0)
            if evolve_cells(c, N) != set(counter(0)) | glider_at(*D, T0 + N):
                continue
            found.append((i, j, D, NZ, others))
    print('kicker i, position j with both cases correct (no eaters):', [(f[0], f[1]) for f in found])
    best = None
    for (i, j, D, NZ, others) in found:
        if j < 12:
            continue
        # eaters for the two passing test gliders, beyond the detector lane: try positions
        eat = []
        for w in others:
            done = None
            for jj in range(j + 30, j + 120, 2):
                for e in eater_for(w, jj):
                    blocks = set().union(*[set(counter(k)) for k in range(0, 60)])
                    pathD = glider_path(D, T0, T0 + N)
                    pathNZ = glider_path(NZ, T0, T0 + N)
                    if set_dist(e, pathD) >= 6 and set_dist(e, pathNZ) >= 6 and set_dist(e, blocks) >= 6:
                        done = e
                        break
                if done:
                    break
            eat.append(done)
        if None in eat:
            continue
        E = eat[0] | eat[1]
        ok = True
        for k in [0] + list(range(1, KMAX + 1)) + [40]:
            c = set(counter(k)) | test_cells(T0) | glider_at(*D, T0) | E
            want = set(counter(k)) | E | (glider_at(*D, T0 + N) if k == 0 else glider_at(*NZ, T0 + N))
            if evolve_cells(c, N) != want:
                ok = False
                break
        if ok:
            best = (i, j, D, NZ, E, eat)
            break
    if best is None:
        print('no design with eaters')
        return
    i, j, D, NZ, E, eat = best
    print('DESIGN: kicker T%d, j = %d' % (i + 1, j))
    print('  detector D = (SE, lane %d, tau %d) = %s at time 0' % (D[1], D[2], lean_window(glider_at(*D, 0))))
    print('  NZ = (NW, lane %d, tau %d); Z = D' % (NZ[1], NZ[2]))
    for q, e in enumerate(eat):
        print('  eater %d: %s' % (q + 1, lean_window(e)))
    start = set(counter(0)) | test_cells(0) | glider_at(*D, 0) | E
    print('  test gliders + D at time 0 (frame of SlidingBlock.lean): %s' % lean_window(test_cells(0) | glider_at(*D, 0)))
    blocks = set().union(*[set(counter(k)) for k in range(0, 60)])
    print('  distances: D path to blocks 0..59: %d; NZ path to blocks: %d; eaters to blocks: %d; eaters to D/NZ paths: %d, %d' % (
        set_dist(glider_path(D, T0, T0 + N), blocks), set_dist(glider_path(NZ, T0, T0 + N), blocks), set_dist(E, blocks),
        set_dist(E, glider_path(D, T0, T0 + N)), set_dist(E, glider_path(NZ, T0, T0 + N))))
    for k in [0, 1, 2, 3, 40]:
        n = N
        c = set(counter(k)) | test_cells(T0) | glider_at(*D, T0) | E
        out = evolve_cells(c, n)
        want = set(counter(k)) | E | (glider_at(*D, T0 + n) if k == 0 else glider_at(*NZ, T0 + n))
        assert out == want
        tag = 'Z = D' if k == 0 else 'NZ'
        print('  k = %d: from time %d, evolve %d -> counter %d ∪ eaters ∪ %s: checked' % (k, T0, n, k, tag))


if __name__ == '__main__':
    main()
