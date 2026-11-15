#!/usr/bin/env python3
"""G9 (R-29): DISPATCH on DZ2's two output lines, world frame of REG1, exact simulation.

Station (g8_station.json, gate coordinates) mapped to the world:
  NZ line X = (SE, -391, .): gate symmetry 6 (transpose; SE stays SE, the station lies on the SW
     side of the line, away from the register diagonal);
  Z line  X = (NE, -537, .): gate symmetry chosen so that X is NE (both images tested).
Stations j = 0, 1 on each line (two calling instructions), spacing a (g8) along the line; eaters at
the ends of both lines.  Tokens (free gliders) for station 1 on both lines (the caller is
instruction 1); then:
   k = 0: Z output dispatched at Z station 1 (glider S'_Z1), the NZ token eaten;
   k >= 1: NZ output dispatched at NZ station 1 (S'_N1), the Z token eaten;
end state = cycle of all pieces ∪ eaters ∪ block, plus exactly the dispatched glider.
Usage: g9_dispatch.py [ks] [first station distance]"""
import sys
import json
from gcommon import *
from net import wl_out, compose, env_cells, set_dist
from common import transform
from life import sym_apply

ST = json.load(open(os.path.join(RES, 'g8_station_36.json')))
TT = lambda w: (tuple(w[0]), w[1], w[2])
X_G, K_G, SP_G = TT(ST['X']), TT(ST['K']), TT(ST['Sp'])
RF_G = tuple(ST['RF_S'])
E_G = {tuple(c) for c in ST['E']}
A = ST['a']
P_G = (45 - ST['D'], 31 + ST['D'])
PIECES, DD = dz2()
CP = DD['ctrl']


def place(k, X_world, P_world):
    """Gate piece (sym k) whose image of X_G is exactly X_world, meeting point near P_world;
    returns (gate, rf, eater cells, K world line, S' world line, P) or None."""
    mp = sym_apply(k, P_G)
    v0 = (P_world[0] - mp[0], P_world[1] - mp[1])
    for du in range(-3, 4):
        for dv in range(-3, 4):
            g0 = ('asm', k, v0[0] + du, v0[1] + dv, 0)
            x0 = wl_out(X_G, g0)
            if x0[:2] != X_world[:2]:
                continue
            diff = X_world[2] - x0[2]
            s, m = diff % 30, diff // 30
            g = ('asm', k, g0[2], g0[3], s)
            assert wl_out(shift_wl(X_G, 0, 0, 30 * m), g) == X_world
            rf = compose(g, RF_G)
            E = translate(transform(E_G, k), g[2], g[3])
            K = wl_out(shift_wl(K_G, 0, 0, 30 * m), g)
            Sp = wl_out(shift_wl(SP_G, 0, 0, 30 * m), g)
            P = sym_apply(k, P_G)
            return g, rf, E, K, Sp, (P[0] + g[2], P[1] + g[3])
    return None


def line_stations(k, X, P0, n=2):
    d = X[0]
    out = []
    for j in range(n):
        Pj = (P0[0] + j * A * d[0], P0[1] + j * A * d[1])
        out.append(place(k, X, Pj))
    return out


def main():
    ks = [int(a) for a in (sys.argv[1] if len(sys.argv) > 1 else '0,1,2,40').split(',')]
    XN, XZ = DD['n1'], DD['zout']
    # first stations: NZ line point (450, 841) (x - y = -391), Z line point (900, -363) (x + y = 537)
    nz = line_stations(6, XN, (450, 841))
    zs = None
    for kz in range(8):
        if sym_apply(kz, (1, 1)) == (1, -1):      # gate SE -> world NE
            cand = line_stations(kz, XZ, (900, -363))
            if all(c is not None for c in cand):
                # the station must lie on the side away from DZ2 / REG1 (gate SE of the Z line)
                g = cand[0][0]
                side = (g[2] + g[3]) - 537
                print('Z line: gate symmetry %d, gate on the %s side' % (kz, 'SE' if side > 0 else 'NW'))
                if side > 0:
                    zs = cand
    assert all(c is not None for c in nz) and zs
    pieces = list(PIECES)
    eaters = set()
    for name, sts in (('NZ', nz), ('Z', zs)):
        for j, (g, rf, E, K, Sp, P) in enumerate(sts):
            pieces += [g, rf]
            eaters |= E
            print('%s station %d: gate %s, RF_S %s, eater %s; meeting point %s; token K %s -> dispatched %s' % (
                name, j, g, rf, lean_window(E), P, wl(K), wl(Sp)))
    # line ends: eaters 120 cells beyond the last station
    for X, sts in ((XN, nz), (XZ, zs)):
        P = sts[-1][5]
        far = (P[0] + 120 * X[0][0], P[1] + 120 * X[0][1])
        e = eater_absorbing(X, far)
        print('end eater of %s: %s' % (wl(X), lean_window(e)))
        eaters |= e
    # separations: every new piece / eater to everything else, and to the blocks
    allenv = [env_cells(p) for p in pieces]
    newi = range(len(PIECES), len(pieces))
    bl = blocks(-1, 600)
    dmin = min(set_dist(allenv[i], allenv[j]) for i in newi for j in range(len(pieces)) if j != i and
               (i - len(PIECES)) // 2 != (j - len(PIECES)) // 2 or (j < len(PIECES) and i != j))
    print('min envelope distance new piece - other piece (gate/RF_S pairs of one station excluded): %d' % dmin)
    print('min distance new pieces + eaters - blocks B_-1..B_600: %d' % min(
        set_dist(set().union(*[allenv[i] for i in newi]) | eaters, bl), 999))
    json.dump({'pieces': pieces[len(PIECES):], 'eaters': sorted(eaters), 'nz': [[s[0], s[1], s[3], s[4], s[5]] for s in nz],
               'z': [[s[0], s[1], s[3], s[4], s[5]] for s in zs]}, open(os.path.join(RES, 'g9_dispatch.json'), 'w'))
    cbox = core_box(pieces, [(140, 230, 900, 900)] + [(min(x for x, y in eaters), min(y for x, y in eaters),
                                                      max(x for x, y in eaters), max(y for x, y in eaters))])
    Ts = -300
    for k in ks:
        for caller in (0, 1, None):
            evs = []
            for (K, st) in (() if caller is None else ((nz[caller][3], nz[caller]), (zs[caller][3], zs[caller]))):
                g = st[0]
                cx = sym_apply(g[1], (45, 31))
                evs.append((30 * ((int(time_at(K, (cx[0] + g[2], cx[1] + g[3]))) - 250) // 30), K))
            # check the tokens' lines from infinity: distance of the path (2000 cells back) to all other pieces
            for (tK, K), st in zip(evs, (() if caller is None else (nz[caller], zs[caller]))):
                path = glider_path(K, tK - 8000, tK)
                dd = min(set_dist(path, env_cells(p)) for p in pieces if p != st[0])
                de = set_dist(path, eaters) if eaters else 999
                if k == ks[0]:
                    print('  token %s: its path (2000 cells before insertion) is %d from the other pieces, %d from the eaters' % (wl(K), dd, de))
            evs.append((Ts, CP))
            t_end = 30 * (max([Ts + (27540 if k == 0 else 11490)] + [e[0] for e in evs]) // 30) + 1500
            cells0 = state(pieces, [], Ts, eaters | block(k))
            cells, rem = run_events(cells0, Ts, evs, t_end, cbox)
            want = state(pieces, [], t_end, eaters | block(k - 1 if k else 0))
            exp = [] if caller is None else [(zs if k == 0 else nz)[caller][4]]
            ok = cells == want and rem == exp
            print('  k = %d, caller %s: %s -> %s %s' % (k, caller, 'Z' if k == 0 else 'NZ', [wl(x) for x in rem],
                                                       'ok' if ok else 'FAIL (extra %d, missing %d)' % (len(cells - want), len(want - cells))), flush=True)


if __name__ == '__main__':
    main()
