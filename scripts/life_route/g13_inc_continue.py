#!/usr/bin/env python3
"""G13 (R-29): INC instruction with continue glider.  A copy F_I of the transposed round-trip
fan-out 0 of f2_roundtrip (the same image as DZ2's F_A) placed on REG1's INC lane: its link output
is REG1's INC control C_I = (SE, 314, -2222 + 30 m), its second output (NE) is the free continue
glider.  Exact simulation on REG1 alone, B_k -> B_(k+1) + continue, k = 0, 1, 2, 3, 40, 100.
Times: when the continue glider leaves F_I, when the push salvo reaches the block, when the block
has arrived at B_(k+1) (first time from which the block region equals B_(k+1)).
Usage: g13_inc_continue.py"""
from gcommon import *
from net import env_cells, set_dist, box_dist, env_box
from dcat import Near

F_A = f0_frozen.F_A
C_A = (SE, -13, 2446)               # F_A's input
C0_A = (SE, 41, 2422)               # F_A's link output
Y_A = (NE, 1071, 2851)              # F_A's second output
REG = reg1()


def place(t):
    u, v = t + 273, t
    d = (-2222 - (C0_A[2] - 4 * u)) % 30          # delay making the link (SE, 314, -2222 mod 30)
    F = [('asm', p[1], p[2] + u, p[3] + v, (p[4] + d) % 30) for p in F_A]
    sh = lambda w: shift_wl(w, u, v, d)
    return F, sh(C_A), sh(C0_A), sh(Y_A)


def main():
    NR = Near(set().union(*[env_cells(p) for p in REG]))
    for t in range(-150, -900, -2):
        F, K, CI, Y = place(t)
        if min(NR.dist(env_cells(p), 64) for p in F) >= 20:
            break
    print('F_I = %s; input K_I = %s; link = %s (REG1 INC control (SE, 314, -2222) + 30 m); continue = %s' % (F, wl(K), wl(CI), wl(Y)))
    print('  F_I envelope to REG1 pieces: %d' % min(NR.dist(env_cells(p), 64) for p in F))
    # continue path from F_I to 1500 cells away, distance to REG1 and blocks
    p = glider_path(Y, time_at(Y, (F[0][2], F[0][3])) + 60, time_at(Y, (F[0][2] + 1500, F[0][3] - 1500)))
    print('  continue path (1500 cells): %d from REG1, %d from B_-1..B_600' % (NR.dist(p, 64), Near(blocks(-1, 600)).dist(p, 64)))
    pieces = REG + F
    cbox = core_box(pieces, [(140, 230, 900, 900)])
    t0 = 30 * ((int(time_at(K, (F[0][2], F[0][3]))) - 300) // 30)
    for k in (0, 1, 2, 3, 40, 100):
        t1 = t0 + 30 * ((CI[2] - t0 + 3570 + 4 * k + 900) // 30)
        cells, rem = run_peel(pieces, [K], t0, t1, extra=block(k), cbox=cbox)
        want = state(pieces, [], t1, block(k + 1))
        print('  k = %3d: evolve %d (cycle ∪ K_I ∪ B_%d) = cycle ∪ B_%d ∪ continue %s: %s' % (
            k, t1 - t0, k, k + 1, [wl(x) for x in rem], 'ok' if (cells == want and rem == [Y]) else 'FAIL'), flush=True)
    # timing of the block move: peel to C_I + 3000, then step generation by generation
    from gsim import Sim
    for k in (0, 1, 40, 100):
        ta = 30 * ((CI[2] + 3000) // 30)
        cells, rem = run_peel(pieces, [K], t0, ta, extra=block(k), cbox=cbox)
        S = Sim(cells, cbox, 600)
        bx = (148 + 7 + k - 14, 240 + 11 + k - 14, 148 + 7 + k + 16, 240 + 11 + k + 16)
        inbox = lambda cs: {x for x in cs if bx[0] <= x[0] <= bx[2] and bx[1] <= x[1] <= bx[3]}
        t = ta
        first = last = None
        prev = inbox(cells)
        while t < CI[2] + 3570 + 4 * k + 300:
            S.run(1)
            t += 1
            cur = inbox(S.cells())
            if cur != prev:
                if first is None:
                    first = t
                last = t
            prev = cur
        assert prev == block(k + 1)
        print('  k = %3d: continue glider leaves F_I at about t = %d (K_I passes F_I at %d); near the block: first change t = %d '
              '(C_I tau + %d), block at B_%d for good from t = %d (C_I tau + %d)' % (
                  k, int(time_at(Y, (F[1][2] + 60, F[1][3]))), int(time_at(K, (F[0][2], F[0][3]))),
                  first, first - CI[2], k + 1, last, last - CI[2]), flush=True)


if __name__ == '__main__':
    main()
