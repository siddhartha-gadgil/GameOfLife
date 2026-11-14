#!/usr/bin/env python3
"""Search R5: the pulling salvo from gliders that gates can supply, by kickbacks and one side step.

All SE gliders come from ONE gun lane (lane -5, the lane of the first salvo glider; their taus are
equal mod 30).  Kickbacks (reactions.KICK) preserve the parity of tau, the side step
(reactions.SIDE) changes it and moves a glider by 6 lanes; the two salvo gliders are 6 lanes apart
and their taus differ by 29, so exactly one side step is needed:

  e1 = SE(-5, t1)  --5 kickbacks by NE gliders-->  f = NW glider 5 lanes to the right
  e2 = SE(-5, t2)  + f  --side step-->  b0 = SE(1, t2 - 13)
  b0 --2 kickbacks (NE, then SW: lane unchanged, delay D)-->  b = SE(1, t2 - 13 + D)
  a  = SE(-5, t3)  direct,   t3 = t2 - 13 + D + 29.

Parameters: positions j of the kicks; the kickers of the kicks 1, 3, 5 are put on one lane (and
equal mod 30), as are those of the kicks 2, 4.  Every candidate is verified by simulation of the
free gliders together with the block `counter k` for k = 0 .. 3: the result must be exactly
`counter (k - 1)`.

Usage: r5_synth.py        Output: stdout (results/r5_synth.txt)
"""
import itertools

from common import (glider_at, counter, lean_window, SE, SW, NW, NE, DIRNAME, bbox, step_cells,
                    PULL_WL, evolve_cells)
from reactions import KICK, SIDE, images, fit, run_free

KIM = images(KICK)
SIM = images(SIDE)


def kick(main, kdir, j):
    for im in KIM:
        if im[0][0][0] == main[0] and im[0][1][0] == kdir:
            ins, outs = fit(im, 0, main, j)
            return ins[1], outs[0]
    raise ValueError


def side_step_for_nw(f, j):
    """SE input and SE output of the side step that uses the NW glider f (SE moves +6 lanes)."""
    for im in SIM:
        if im[0][0][0] == SE and im[0][1][0] == NW and im[1][0][0] == SE and im[1][0][1] - im[0][0][1] == 6:
            ins, outs = fit(im, 1, f, j)
            return ins[0], outs[0]
    raise ValueError


def build(j1, j2, jH, j6, j7, order=(NE, SW)):
    """Returns (list of input world lines with roles, a, b) or None if the mod-30 conditions fail."""
    t1 = 0
    e1 = (SE, -5, t1)
    ins = [('e1', e1)]
    cur = e1
    js = [j1, j2, j1 - 1, j2 + 1, j1 - 2]
    kickers = []
    for i, j in enumerate(js):
        k, cur = kick(cur, NE, j)
        kickers.append(k)
        ins.append(('k%d' % (i + 1), k))
    # kickers 1, 3, 5 on one lane, equal mod 30; kickers 2, 4 likewise
    if len({k[1] for k in kickers[0::2]}) != 1 or len({k[2] % 30 for k in kickers[0::2]}) != 1:
        return None
    if len({k[1] for k in kickers[1::2]}) != 1 or len({k[2] % 30 for k in kickers[1::2]}) != 1:
        return None
    f = cur
    e2, b0 = side_step_for_nw(f, jH)
    if e2[1] != -5 or (e2[2] - t1) % 30 != 0:
        return None
    ins.append(('e2', e2))
    k6, m = kick(b0, order[0], j6)
    k7, b = kick(m, order[1], j7)
    ins += [('k6', k6), ('k7', k7)]
    if b[1] != 1:
        return None
    a = (SE, -5, b[2] + 29)
    if (a[2] - t1) % 30 != 0:
        return None
    ins.append(('a', a))
    return ins, a, b


def verify(ins, a, b, ks=(0, 1, 2, 3)):
    wls = [w for (nm, w) in ins]
    t0 = min(w[2] for w in wls) - 200
    # 1. the free gliders alone give exactly a and b
    st, t, rest, gl = run_free(wls, t0=t0, max_gen=6000)
    if st != 'settled' or rest or sorted(gl) != sorted([a, b]):
        return False
    # 2. with the block: standard position of the salvo is tau_a = 0; here tau_a = a[2], so the
    #    block `counter k` is translated by (-d, -d) with 4 d = a[2] ... use a time shift instead:
    #    world lines (SE, -5, T), (SE, 1, T - 29) = pullSalvo at time T.
    T = a[2]
    for k in ks:
        K = 300 + k                       # a block far down the diagonal: counter K
        cells = set(counter(K))
        for w in wls:
            cells |= glider_at(*w, t0)
        n = (T - t0) + 4 * K + 26         # pull: evolve (4 K + 26) (pullSalvo ∪ counter K) = counter (K - 1)
        if evolve_cells(cells, n) != set(counter(K - 1)):
            return False
    return True


def main():
    found = []
    for j1 in range(4, 12):
        j2 = 10 - j1
        for jH in range(-20, 21):
            for order in ((NE, SW), (SW, NE)):
                for j6 in range(-2, 14):
                    for j7 in range(-14, 14):
                        r = build(j1, j2, jH, j6, j7, order)
                        if r is None:
                            continue
                        ins, a, b = r
                        span = max(w[2] for n, w in ins) - min(w[2] for n, w in ins)
                        found.append((span, j1, j2, jH, j6, j7, order, ins, a, b))
    print('candidates satisfying the lane and mod-30 conditions:', len(found))
    found.sort(key=lambda x: x[0])
    good = 0
    for (span, j1, j2, jH, j6, j7, order, ins, a, b) in found:
        if verify(ins, a, b):
            good += 1
            if good <= 3:
                print('VERIFIED synthesis (free gliders -> pull salvo -> counter k -> counter (k - 1), k = 300 .. 303):')
                print('  parameters j1=%d j2=%d jH=%d j6=%d j7=%d order=%s' % (j1, j2, jH, j6, j7, [DIRNAME[d] for d in order]))
                for nm, w in ins:
                    print('   %-3s %s lane %4d tau %5d (tau mod 30 = %2d)' % (nm, DIRNAME[w[0]], w[1], w[2], w[2] % 30))
                print('   -> a = SE lane %d tau %d,  b = SE lane %d tau %d' % (a[1], a[2], b[1], b[2]))
            if good >= 40:
                break
    print('verified:', good, 'of the first', min(len(found), 10 ** 9), 'candidates tried in order of time span')


if __name__ == '__main__':
    main()
