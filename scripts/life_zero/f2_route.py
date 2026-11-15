#!/usr/bin/env python3
"""F2 (R-28): supply of the unconditional glider O through a RE-TIMING GATE.

Route: C -> fan-out F_B (round-trip fan-out of f2_roundtrip, plain or transposed, in series
upstream of F_A: its link glider is C) -> its second output Y_B -> one or two copies of RF0 ->
control E of a gate G_O (copy of blockedStream; catalogue records of kind 'gate', from infinity)
whose released stream glider is exactly O.
Arrival of a reflector route on a lane L in direction dE: tau = a + b L (taxicab invariant; a
depends on the fan-out family, b on the directions); the gate's position j along O's line is free,
the control world line E(j) moves linearly with j, so each (O, record, symmetry, family) gives at
most one j.  Prints every exact solution with the gate 40..400 cells upstream of O's crossing.
Usage: f2_route.py [MAX_O]   -> results/f2_route.json"""
import gzip
import json
import os
import sys
from multiprocessing import Pool
from f0_frozen import *
from common import life
from machine import load_catalog, wl_map
from net import reflect, time_at
from reactions import sym_wl

DIRS3 = (SE, SW, NE)


def families():
    """{(dE, parity of L): {(b, a): [(family, sym)]}}"""
    d = json.load(gzip.open(os.path.join(HERE, '..', 'life_machine', 'results', 'f2_roundtrip.json.gz'), 'rt'))['good']
    out = {}
    for i, fo in enumerate(d):
        outs = [(tuple(o[0]), o[1], o[2]) for o in fo['outs']]
        se = [w for w in outs if w[0] == SE]
        sw = [w for w in outs if w[0] == SW]
        if len(se) != 1 or len(sw) != 1:
            continue
        for sym in (0, 6):
            g1, g2 = sym_wl(se[0], sym), sym_wl(sw[0], sym)
            u = -900
            v = u + g1[1] - C[1]
            s = (C[2] - (g1[2] - 4 * u)) % 30
            link, Y = shift_wl(g1, u, v, s), shift_wl(g2, u, v, s)
            n = link[2] - C[2]
            for dE in DIRS3:
                for par in (0, 1):
                    vals = []
                    for L in (-400 + par, -398 + par):
                        r = route_to(Y, dE, L)
                        if r is not None:
                            vals.append((L, r[2] - n))
                    if len(vals) == 2:
                        b = (vals[1][1] - vals[0][1]) // 2
                        a = vals[0][1] - b * vals[0][0]
                        out.setdefault((dE, par), {}).setdefault((b, a), []).append((i, sym))
    return out


def route_to(Y, dE, L):
    if dE[0] * Y[0][0] + dE[1] * Y[0][1] == 0:
        r = reflect(Y, dE, L)
        return None if r is None else r[1]
    mid = [x for x in (SE, SW, NE, NW) if x[0] * Y[0][0] + x[1] * Y[0][1] == 0 and x[0] * dE[0] + x[1] * dE[1] == 0]
    for m in mid:
        for Lm in range(600, 604):
            a = reflect(Y, m, Lm)
            if a is None:
                continue
            r = reflect(a[1], dE, L)
            if r is not None:
                return r[1]
    return None


def place_out(out_wl, k, target, p):
    """asm (k, p, q, s) whose image of out_wl is target up to 30 m; returns (asm, dt) or None"""
    w0 = wl_map(out_wl, (k, 0, 0, 0))
    d = w0[0]
    num = w0[1] + d[1] * p - target[1]
    if num % d[0]:
        return None
    q = num // d[0]
    s = (target[2] - (w0[2] - 4 * d[0] * p)) % 30
    asm = (k, p, q, s)
    w = wl_map(out_wl, asm)
    if w[:2] != target[:2] or (w[2] - target[2]) % 30:
        return None
    return asm, target[2] - w[2]


GATES = None
FAM = None
# E must reach the gate from the free east side of REG1: SE-flying on lanes >= 540 or SW-flying
ROUTE_ANY = bool(os.environ.get('F2_ANY'))


def init():
    global GATES, FAM
    recs = load_catalog()
    GATES = [r for r in recs if r['kind'] == 'gate' and r['from_infinity'] and len(r['outs']) == 1]
    FAM = families()


def job(item):
    O, jx, tcross = item
    O = (tuple(O[0]), O[1], O[2])
    cx = min(glider_at(*O, tcross))[0]
    sols = []
    for r in GATES:
        ow = r['outs'][0][0]
        for k in range(8):
            if life.sym_apply(k, ow[0]) != O[0]:
                continue
            # positions p upstream: O flies with dx = O[0][0]; upstream means x - dx * dist
            res = []
            for p in (cx - O[0][0] * 100, cx - O[0][0] * 101):
                pl = place_out(ow, k, O, p)
                if pl is None:
                    res = None
                    break
                asm, dt = pl
                E = shift_wl(wl_map(r['wl'], asm), 0, 0, dt)
                res.append((p, asm, E))
            if not res:
                continue
            (p0, a0, E0), (p1, a1, E1) = res
            dE = E0[0]
            if dE not in DIRS3:
                continue
            for par in (E0[1] % 2,):
                tab = FAM.get((dE, par))
                if not tab:
                    continue
                for (b, a), fams in tab.items():
                    i0 = E0[2] - b * E0[1]
                    i1 = E1[2] - b * E1[1]
                    sig = i1 - i0
                    if sig == 0:
                        if i0 != a:
                            continue
                        js = [100]
                    else:
                        if (a - i0) % sig:
                            continue
                        js = [100 + (a - i0) // sig]
                    for jj in js:
                        if not (40 <= jj <= 400):
                            continue
                        p = cx - O[0][0] * jj
                        pl = place_out(ow, k, O, p)
                        if pl is None:
                            continue
                        asm, dt = pl
                        E = shift_wl(wl_map(r['wl'], asm), 0, 0, dt)
                        if E[1] % 2 != par:
                            continue
                        if E[2] - b * E[1] == a and (E[0] == SW or (E[0] == SE and E[1] >= 540) or ROUTE_ANY):
                            sols.append({'O': [list(O[0]), O[1], O[2]], 'gate': ['asm'] + list(asm), 'E': [list(E[0]), E[1], E[2]],
                                         'rec': [list(r['wl'][0]), r['wl'][1], r['wl'][2]], 'dist': jj, 'fams': fams[:4]})
    return sols


if __name__ == '__main__':
    req = json.load(open(os.path.join(HERE, 'results', 'f1_req.json')))
    mx = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    req.sort(key=lambda r: -min(r[3][0], 15) - min(r[3][2], 6))
    seen, items = set(), []
    for r in req:
        key = (tuple(r[0][0]), r[0][1], r[0][2])
        if key in seen:
            continue
        seen.add(key)
        items.append((r[0], r[1], r[2]))
    print('distinct O:', len(items), flush=True)
    items = items[:mx]
    out = []
    with Pool(8, initializer=init) as p:
        for s in p.imap_unordered(job, items):
            for x in s:
                out.append(x)
    print('solutions', len(out))
    for x in out[:20]:
        print(json.dumps(x))
    json.dump(out[:2000], open(os.path.join(HERE, 'results', 'f2_route.json'), 'w'))
