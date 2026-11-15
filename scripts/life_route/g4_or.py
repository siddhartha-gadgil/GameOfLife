#!/usr/bin/env python3
"""G4 (R-29): the 2-input OR gate (a copy of blockedStream) and its re-use spacing (own simulation).

Gate coordinates (blockedStream itself, phase 0).  Released glider A = (SE, 14, .) (gun A).
Through input T = (SE, LT, tau) (same direction as A: chainable by translation), side input
S = (NE, LS, tau).  For every residue tau (mod 30) of both lines: does the control release exactly
one glider A (and the gate return to its cycle)?  Then pairs of controls (TT, TS, ST, SS) with
gap d: both released, nothing else?  Usage: g4_or.py LT LS"""
import sys
from gcommon import *
from net import piece_cells

G = ('asm', 0, 0, 0, 0)


def single(w, tmax=700):
    """cycle + w  ->  ?  Returns the released world line(s) or None."""
    t0 = 30 * ((int(time_at(w, (45, 31))) - 160) // 30)
    t1 = t0 + 30 * (tmax // 30)
    c, _ = run([G], [w], t0, t1)
    rest = c - state([G], [], t1)
    if state([G], [], t1) - c:
        return None
    from common import components, glider_worldline
    outs = []
    for comp in components(rest, 2):
        g = glider_worldline(comp, t1)
        if g is None:
            return None
        outs.append(g)
    return sorted(outs)


def pair(w1, w2, tmax=900):
    t0 = 30 * ((int(time_at(w1, (45, 31))) - 160) // 30)
    t1 = 30 * ((int(time_at(w2, (45, 31))) + tmax) // 30)
    cells = state([G], [w1], t0)
    # insert w2 at the time it is 120 generations from the crossing, if it is free there
    ti = int(time_at(w2, (45, 31))) - 160
    if ti > t0:
        c, _ = run([], [], t0, ti, extra=cells)
        from life import chebyshev_dist
        g = glider_at(*w2, ti)
        if chebyshev_dist(g, c) < 4:
            return None
        c |= g
        c, _ = run([], [], ti, t1, extra=c)
    else:
        c, _ = run([], [w2], t0, t1, extra=cells)
    rest = c - state([G], [], t1)
    if state([G], [], t1) - c:
        return None
    from common import components, glider_worldline
    outs = []
    for comp in components(rest, 2):
        g = glider_worldline(comp, t1)
        if g is None:
            return None
        outs.append(g)
    return sorted(outs)


def main():
    LT, LS = int(sys.argv[1]), int(sys.argv[2])
    good = {}
    for name, d, L in (('T', SE, LT), ('S', NE, LS)):
        ok = []
        for r in range(30):
            o = single((d, L, r + 300))
            line = '%s (%s, %d, %d): %s' % (name, DIRNAME[d], L, r + 300, [wl(x) for x in o] if o is not None else 'debris')
            if o is not None and len(o) == 1 and o[0][0] == SE and o[0][1] == 14:
                ok.append((r, o[0][2] - 300))
            print(line)
        good[name] = ok
        print('%s: residues releasing A: %s' % (name, ok), flush=True)
    # pairs: first control at a good residue, second at every later time with a good residue
    for a in 'TS':
        for b in 'TS':
            da, La = (SE, LT) if a == 'T' else (NE, LS)
            db, Lb = (SE, LT) if b == 'T' else (NE, LS)
            r1, o1 = good[a][0]
            w1 = (da, La, r1 + 300)
            gres = dict(good[b])
            fails = []
            X = (45, 31)
            ta = time_at(w1, X)
            for D in range(1, 601):
                # second control arriving at the crossing D generations after the first
                tau2 = int(round(r1 + 300 + D + ta - (r1 + 300) - time_at((db, Lb, 0), X)))
                if abs(time_at((db, Lb, tau2), X) - ta - D) > 0.6 or (tau2 % 30) not in gres:
                    continue
                w2 = (db, Lb, tau2)
                o = pair(w1, w2)
                exp = sorted([(SE, 14, o1 + 300), (SE, 14, tau2 - tau2 % 30 + gres[tau2 % 30])])
                if o != exp:
                    fails.append(D)
            print('pair %s then %s (first %s): arrival gaps at the crossing (45, 31) that fail: %s' % (a, b, wl(w1), fails), flush=True)


if __name__ == '__main__':
    main()
