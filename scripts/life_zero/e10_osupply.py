#!/usr/bin/env python3
"""E10 (R-27): can the unconditional glider O be supplied by a second round-trip fan-out F_B in
series upstream of F_A (its link glider = F_A's control C) plus two reflectors (route
NE -> SE -> SW or SE -> SW for the plain / transposed image)?  The route has a fixed arrival time
(taxicab invariant), so for every target lane the reachable taus form a small discrete set; the
required O's (every G_N of results/e2_gate.json, every crossing point, both directions) are
enumerated without clearance filters and intersected with it.
Prints the matches (exact equality of world lines)."""
import gzip
import json
import os
from dcat import *
from net import reflect, env_cells, time_at
from reactions import sym_wl
from common import bbox

C = (SE, -13, 2446)


def reachable(lanes):
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
            for (od, ol) in lanes:
                for L in range(700, 1100):
                    ra = reflect(Y, SE, L)
                    if ra is None:
                        continue
                    rb = reflect(ra[1], od, ol)
                    if rb:
                        out.setdefault((od, ol), set()).add((rb[1][2] - n, i, sym))
                        break
    return out


def _req_job(a):
    gi, j = a
    g = json.load(open(os.path.join(HERE, 'results', 'e2_gate.json')))[gi]
    req = []
    n1, n2 = sorted([(tuple(w[0]), w[1], w[2]) for w in g['outs']], key=lambda w: w[2])
    solid = env_cells(tuple(g['piece']))
    b = bbox(solid)
    t_g = time_at(n2, ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2))
    if True:
            t = int(t_g) + 4 * j
            pt = min(glider_at(*n2, t))
            for od in (SW, NE):
                lane = od[1] * pt[0] - od[0] * pt[1]
                for dl in range(-3, 4):
                    for dt in range(-8, 9):
                        # tau such that O is at the crossing at about time t
                        O0 = (od, lane + dl, 0)
                        tau = int(t - time_at(O0, pt)) + dt
                        O = (od, lane + dl, tau)
                        st, tt, rest, gl = run_free([n1, n2, O], t0=t - 200, max_gen=600)
                        if st == 'settled' and not rest and gl == [n1]:
                            req.append((O, gi, j))
    return req


def required():
    from multiprocessing import Pool
    n = len(json.load(open(os.path.join(HERE, 'results', 'e2_gate.json'))))
    jobs = [(gi, j) for gi in range(n) for j in range(25, 200, 2)]
    req = []
    with Pool(8) as p:
        for r in p.imap_unordered(_req_job, jobs):
            req += r
    return req


if __name__ == '__main__':
    req = required()
    print('required O (all gates, crossings 25..199):', len(req), flush=True)
    lanes = sorted(set((o[0], o[1]) for (o, gi, j) in req))
    rch = reachable(lanes)
    m = 0
    for (O, gi, j) in req:
        for (tau, i, sym) in rch.get((O[0], O[1]), ()):
            if tau == O[2]:
                m += 1
                print('  match: O %s gate %d crossing %d  <- fan-out %d (sym %d) + 2 reflectors' % (O, gi, j, i, sym), flush=True)
    print('matches', m)
