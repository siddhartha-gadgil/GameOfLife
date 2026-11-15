#!/usr/bin/env python3
"""L0 (R-30): the register module M(nd, ni) in the world frame of REG1 (register at the origin).

M(nd) = REG1 + DZ2' (DZ2 with RF_C3', R-29 §1.3) + G_I + RF_J
          + DEC merge chain of 2 nd copies (g5_chain.chain(2 nd, 64, -1700): translation (35, 64) per copy)
          + INC merge chain of 1 copy (g5_chain.chain(1, 64, -1132, cp = RF_J's input))
          + nd dispatch stations on the NZ line and nd on the Z line (g9_dispatch.line_stations,
            translation (72, 72) j resp. (72, -72) j, delay 288 j) + 2 nd token eaters
          + 2 line-end eaters (120 cells beyond the last station).
Ports (all world lines; any tau + 30 m with the residue given):
  dec[j]  = side input of DEC copy j (NE, lane, tau .. tau + 12)
  inc[j]  = side input of INC copy j (NE, lane, tau .. tau + 12)
  nz[j]   = (token K_NZ, dispatched S'_NZ) at NZ station j, timed for C' = (SE, 41, 4444)
  z[j]    = (token K_Z,  dispatched S'_Z)  at Z station j, timed for C' = (SE, 41, 4444)
The copy j of a chain is j = 0 .. n-1 counted from upstream (copy n - 1 feeds DZ2 / RF_J).
Usage: l0_module.py ND   (prints the footprint in (u, v) coordinates)"""
import sys
import json
from lcommon import *
import g5_chain
import g11_inc_check as G11
import g9_dispatch as G9

_BASE = None


def base():
    global _BASE
    if _BASE is None:
        pieces, GI, RFC3, CI = G11.design(0)
        _, D = dz2()
        inc = json.load(open(os.path.join(ROUTE, 'results', 'g12_inc_chain.json')))[0]
        _BASE = (pieces, D, tuple(inc['RF_J']), T(inc['in']))
    return _BASE


def module(nd, ni=1):
    """nd = number of DECJZ callers: DEC chain of 2 nd copies (both side-line parities), nd stations
    per line; INC chain of ni copies (the layout uses ni = 1: INC callers are merged upstream)."""
    pieces, D, RFJ, win = base()
    CP = D['ctrl']
    dec = g5_chain.chain(2 * nd, 64, -1700) if nd else []
    inc = g5_chain.chain(ni, 64, -1132, cp=win) if ni else []
    out = {'CP': CP, 'D': D}
    P = list(pieces) + ([RFJ] if ni else []) + inc + dec
    out['dec_gates'] = dec
    out['inc_gates'] = inc
    out['dec'] = [wl_out((NE, -76, 1), g) for g in dec]      # residues 1..13: tau .. tau + 12
    out['inc'] = [wl_out((NE, -76, 1), g) for g in inc]
    eaters = set()
    nz = G9.line_stations(6, D['n1'], (450, 841), nd) if nd else []
    zs = G9.line_stations(5, D['zout'], (900, -363), nd) if nd else []
    for sts in (nz, zs):
        for (g, rf, E, K, Sp, Pm) in sts:
            P += [g, rf]
            eaters |= E
    for X, sts in ((D['n1'], nz), (D['zout'], zs)):
        if sts:
            Pm = sts[-1][5]
        else:
            Pm = (450, 841) if X == D['n1'] else (900, -363)
        far = (Pm[0] + 120 * X[0][0], Pm[1] + 120 * X[0][1])
        e = eater_absorbing(X, far)
        assert e
        eaters |= e
    out['nz'] = [(s[3], s[4]) for s in nz]
    out['z'] = [(s[3], s[4]) for s in zs]
    out['stations'] = {'nz': [s[:2] for s in nz], 'z': [s[:2] for s in zs]}
    out['pieces'] = P
    out['eaters'] = eaters
    out['nd'], out['ni'] = nd, ni
    return out


def uvbox(cells):
    us = [x - y for x, y in cells]
    vs = [x + y for x, y in cells]
    return (min(us), min(vs), max(us), max(vs))


def main():
    nd = int(sys.argv[1])
    M = module(nd)
    names = ['REG1/DZ2 %d' % i for i in range(len(M['pieces']))]
    for p in M['pieces']:
        print('%-30s uv box %s' % (p, uvbox(env_cells(p))))
    print('eaters uv', uvbox(M['eaters']))
    allc = set().union(*[env_cells(p) for p in M['pieces']]) | M['eaters']
    print('module uv box', uvbox(allc), 'xy box', bbox(allc))
    for k in ('dec', 'inc'):
        for w in M[k]:
            print(k, wl(w))
    for k in ('nz', 'z'):
        for K, S in M[k]:
            print(k, 'token', wl(K), 'dispatched', wl(S))


if __name__ == '__main__':
    main()
