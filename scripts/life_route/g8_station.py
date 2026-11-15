#!/usr/bin/env python3
"""G8 (R-29): the complete DISPATCH station (gate coordinates) and its chaining by translation.

Station(D) = gate G (blockedStream) + reflector RF_S (S = (SE, 14, .) -> NE, away from the shared
line) + eater E_T (eater 1 of Patterns.lean, absorbs an unpaired T), for the kickback variant
TPL1 sym0 of g7_station.py (X flies SE, i.e. parallel to S; Y returns on T's line + 2).
Checks (exact simulation):
  (a) G + K + X -> station + S'        (S' = the dispatched glider, flying NE)
  (b) G + K     -> station              (T eaten)
  (c) X alone   -> station + X          (passes)
Chain: station_j = station_0 translated by (j a, j a) and delayed by 4 j a (so that the same X
arrives at every station in the same phase).  (d) X with the token of station 1 only: X passes
station 0 and is dispatched at station 1; (e) tokens without X; (f) X without tokens.
Usage: g8_station.py D"""
import sys
import json
from gcommon import *
from net import reflect, env_cells, env_box, box_dist, set_dist
from common import components, glider_worldline, transform, EATER1
from reactions import run_free
from g7_station import TPL1, images, fit, gl_list

G = ('asm', 0, 0, 0, 0)
K0 = (SW, 46, 305)
T0 = (SW, 75, 411)


def station_core(D):
    im = images(TPL1)[0]
    for j in range(-400, 401):
        ins, outs = fit(im, 1, T0, j)
        X = ins[0]
        if round(45 - (75 + X[1]) / 2) == D:
            return X, outs[0]
    return None


def eater_for(T, P, X, far=12):
    """eater-1 placements (cells) that absorb T beyond the point P, ≥ far cells from X's path."""
    out = []
    xp = set()
    for t in range(int(time_at(X, P)) - 200, int(time_at(X, P)) + 200):
        xp |= glider_at(*X, t)
    for k in range(8):
        e0 = transform(set(EATER1), k)
        for dd in range(far, far + 25):
            cx, cy = P[0] - dd, P[1] + dd
            for u in range(-6, 7):
                for v in range(-6, 7):
                    e = translate(e0, cx + u - min(x for x, y in e0), cy + v - min(y for x, y in e0))
                    tt = int(time_at(T, (cx, cy)))
                    g = glider_at(*T, tt - 40)
                    if min(max(abs(a - c), abs(b - d)) for (a, b) in g for (c, d) in e) < 4:
                        continue
                    st, t, rest, gl = run_free([T], extra=e, t0=tt - 40, max_gen=300)
                    if st == 'settled' and set(rest) == set(e) and not gl:
                        dx = set_dist(e, xp)
                        if dx >= far:
                            return e, dx
    return None


def check(pieces, extra, gliders, t0, t1, want_gl):
    c, _ = run(pieces, gliders, t0, t1, extra=extra, box=(-3000, -3000, 3000, 3000), margin=100)
    base = state(pieces, [], t1, extra)
    if base - c:
        return False, 'damaged'
    gl = gl_list(c - base, t1)
    return gl == sorted(want_gl), gl


def main():
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 36
    X, Y = station_core(D)
    P = (45 - D, 31 + D)
    print('D = %d: X = %s, Y = %s, meeting point P = %s' % (D, wl(X), wl(Y), P))
    genv = env_cells(G)
    # RF_S: first position along S's line (beyond the crossing) with envelope >= 10 from the gate
    S_wl = None
    tK = int(time_at(K0, (45, 31)))
    ok, gl = check([G], set(), [K0, X], 30 * ((tK - 150) // 30), 30 * ((tK + 16 * D + 900) // 30), [])
    S_wl = [g for g in gl if g[0] == SE][0]
    print('  G + K + X -> %s' % [wl(g) for g in gl])
    rf = None
    for n in range(10, 400):
        e = n / 2
        # S' on the NE lane through the point (45 + e, 31 + e):  NE lane = -x - y
        r = reflect(S_wl, NE, -(76 + n))
        if r is None:
            continue
        piece, Sp = r
        if box_dist(env_box(piece), env_box(G)) < 10:
            continue
        # S' path (NE) must be >= 10 from the gate envelope
        path = glider_path(Sp, time_at(Sp, (45 + e, 31 + e)), time_at(Sp, (45 + e + 300, 31 + e - 300)))
        if set_dist(path, genv) < 10:
            continue
        rf = (piece, Sp, e)
        break
    print('  RF_S = %s (e = %.1f): S\' = %s' % (rf[0], rf[2], wl(rf[1])))
    E, dx = eater_for(T0, P, X)
    print('  E_T = eater 1, %s, distance to the path of X: %d' % (lean_window(E), dx))
    pieces = [G, rf[0]]
    t0 = 30 * ((tK - 150) // 30)
    t1 = 30 * ((tK + 16 * D + 1500) // 30)
    ra = check(pieces, E, [K0, X], t0, t1, [rf[1]])
    rb = check(pieces, E, [K0], t0, t1, [])
    tx = 30 * ((int(time_at(X, P)) - 400) // 30)
    rc = check(pieces, E, [X], tx, tx + 900, [X])
    print('  (a) K + X -> S\': %s   (b) K alone -> nothing: %s   (c) X alone passes: %s' % (ra[0], rb[0], rc[0]))
    # separations of the station
    xpath = glider_path(X, time_at(X, P) - 400, time_at(X, P) + 400)
    print('  distances to the path of X: gate %d, RF_S %d, eater %d' % (
        set_dist(genv, xpath), set_dist(env_cells(rf[0]), xpath), dx))
    # chain: smallest a with all checks
    res = None
    for a in range(60, 400, 2):
        sh = lambda p: ('asm' if p[0] == 'asm' else 'rf', p[1], p[2] + a, p[3] + a, (p[4] + 4 * a) % 30)
        p1 = [sh(p) for p in pieces]
        E1 = translate(E, a, a)
        if min(box_dist(env_box(p), env_box(q)) for p in pieces for q in p1) < 12:
            continue
        if set_dist(E1, set().union(*[env_cells(p) for p in pieces])) < 12 or set_dist(E, set().union(*[env_cells(p) for p in p1])) < 12:
            continue
        K1 = shift_wl(K0, a, a, 4 * a)
        S1 = shift_wl(rf[1], a, a, 4 * a)
        allp = pieces + p1
        alle = E | E1
        t1b = t1 + 8 * a + 600
        d1 = check(allp, alle, [K1, X], t0, t1b, [S1])
        d0 = check(allp, alle, [K0, X], t0, t1b, [rf[1]])
        e2 = check(allp, alle, [K0, K1], t0, t1b, [])
        f = check(allp, alle, [X], tx, tx + 8 * a + 1200, [X])
        print('  a = %d: (d) token at station 1: %s; token at station 0: %s; (e) both tokens, no X: %s; (f) X alone passes both: %s' % (
            a, d1[0], d0[0], e2[0], f[0]), flush=True)
        if d1[0] and d0[0] and e2[0] and f[0]:
            res = a
            break
    json.dump({'D': D, 'K': K0, 'T': T0, 'X': X, 'Y': Y, 'S': S_wl, 'RF_S': rf[0], 'Sp': rf[1], 'E': sorted(E), 'a': res},
              open(os.path.join(RES, 'g8_station_%d.json' % D), 'w'))


if __name__ == '__main__':
    main()
