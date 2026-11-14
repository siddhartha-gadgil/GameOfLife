#!/usr/bin/env python3
"""Z1: the conditional core of the zero test, with free gliders (no guns).

Frame of SlidingBlock.lean: the block at position k is `counter k` (upper left cell
(7 + k, 11 + k)); `zeroTestGlider` T = ofRows 5 6 [2, 1, 7] flies SW; `zeroRestoreGlider`
= ofRows 6 15 [2, 6, 5] flies NE (Collisions.lean).

Idea (N-15, "an absent glider fails to delete a blocking glider", with the kickback of R-19 in
place of an annihilation, so that both cases give exactly one glider):
  * a detector glider D flies SE on a lane parallel to the register, DELTA lanes to its left,
    timed so that T, if it has passed the register, kicks it back:  D + T -> one glider NZ
    flying NW (the kickback `glider_kickback`: SE (0, 0) + SW (6, 7) -> NW (2, 12));
  * if the block is at position 0, T is consumed, D flies on: D itself is the glider Z;
  * the restoring glider must be sent only in the case Z (it would hit a block at 1 .. 5).
For every position j of the kick along the lane of T the script checks, with the set simulator:
  NZ: counter k + T + D          ->  counter k + NZ            for k = 1 .. KMAX and k = 40
  Z : counter 0 + T + D + restore (launched late) ->  counter 0 + D
and reports the lanes and the minimum distances of D and NZ from the blocks.

Usage: z1_zero_core.py        Output: summary on stdout (results/z1_zero_core.txt)
"""
from common import (cells_of_window, glider_at, glider_worldline, evolve_cells, step_cells, counter,
                    SE, SW, NW, NE, DIRNAME, lean_window, life)
from reactions import KICK, fit, images
from net import glider_path, set_dist

T = glider_worldline(cells_of_window(5, 6, [2, 1, 7]), 0)
RESTORE = glider_worldline(cells_of_window(6, 15, [2, 6, 5]), 0)
KMAX = 12


def run(cells, n):
    return evolve_cells(set(cells), n)


def check(j, late=40):
    ins, outs = fit(KICK, 1, T, j)
    D, NZ = ins[0], outs[0]
    # the kick happens near the meeting point; start early enough that T is before the register
    t0 = -200
    n = 900
    res = {'j': j, 'D': D, 'NZ': NZ}
    ok = True
    for k in list(range(1, KMAX + 1)) + [40]:
        c = set(counter(k)) | glider_at(*T, t0) | glider_at(*D, t0)
        end = run(c, n)
        if end != set(counter(k)) | glider_at(*NZ, t0 + n):
            ok = False
            break
    res['NZ ok'] = ok
    # Z: block at 0; restore glider delayed by `late` generations relative to zeroTest_restore
    R = (RESTORE[0], RESTORE[1], RESTORE[2] + late)
    c = set(counter(0)) | glider_at(*T, t0) | glider_at(*D, t0) | glider_at(*R, t0)
    end = run(c, n)
    res['Z ok'] = end == set(counter(0)) | glider_at(*D, t0 + n)
    if res['NZ ok'] and res['Z ok']:
        blocks = set()
        for k in range(0, 60):
            blocks |= set(counter(k))
        blocks |= {(8, 9), (9, 9), (8, 10), (9, 10)}          # the displaced block of zeroTest_hit
        res['dist D'] = set_dist(glider_path(D, -400, 400), blocks)
        res['dist NZ'] = set_dist(glider_path(NZ, -400, 400), blocks)
    return res


def main():
    assert T[0] == SW and RESTORE[0] == NE
    print('zeroTestGlider    = (%s, lane %d, tau %d)' % (DIRNAME[T[0]], T[1], T[2]))
    print('zeroRestoreGlider = (%s, lane %d, tau %d); the register (blocks counter k) is on the SE lane -4' % (DIRNAME[RESTORE[0]], RESTORE[1], RESTORE[2]))
    # cross-check of Collisions.lean
    assert run(set(counter(0)) | glider_at(*T, 0), 9) == set(cells_of_window(8, 9, [3, 3]))
    assert run(set(counter(0)) | glider_at(*T, 0) | glider_at(*RESTORE, 0), 20) == set(counter(0))
    print('zeroTest_hit (9 generations) and zeroTest_restore (20 generations): checked')
    good = []
    for j in range(-10, 31):
        r = check(j)
        if r['NZ ok'] and r['Z ok']:
            good.append(r)
    print('positions j of the kick with both cases correct: %s' % [r['j'] for r in good])
    for r in good:
        print('  j = %3d: D = (SE, lane %d, tau %d) [%d lanes left of the register], NZ = (NW, lane %d, tau %d); '
              'distance from all blocks counter 0 .. 59: D %d, NZ %d' % (
                  r['j'], r['D'][1], r['D'][2], -4 - r['D'][1], r['NZ'][1], r['NZ'][2], r['dist D'], r['dist NZ']))
    if good:
        r = [g for g in good if g["dist D"] >= 10][0] if any(g["dist D"] >= 10 for g in good) else good[0]
        print('example j = %d, windows at time 0 (frame of SlidingBlock.lean):' % r['j'])
        print('   T = %s, D = %s' % (lean_window(glider_at(*T, 0)), lean_window(glider_at(*r['D'], 0))))
        print('   NZ at time 400 = %s, D at time 400 = %s' % (lean_window(glider_at(*r['NZ'], 400)), lean_window(glider_at(*r['D'], 400))))


if __name__ == '__main__':
    main()
