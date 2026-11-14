#!/usr/bin/env python3
"""Search G4: pull-salvo generator from ONE control glider:
       fan-out (S, K)  +  a third gate Gb  +  three reflectors.

Why a third gate: reflections change (lane parity, tau parity) of a glider together, and the two
gliders G1, G2 of the fan-out have classes from which reflections alone never give two SE gliders
on lanes of equal parity (g2_pull.py finds no solution).  A gate re-times its output to its own
guns, whose position and delay are free, which removes the parity obstruction.

  C0 = (SE, 41, 22) -> S = `blockedStream`: fan-out with K = FANOUT (f2_roundtrip.py):
        G1 = (NW, 29, 730) from K,   G2 = (SW, 75, 771) from S.
  path 1: G1 -> RF (NW -> SW, on the SW lane m) -> RF (SW -> SE, lane L)          -> glider P1
  path 2: G2 -> gate Gb = (k, vx, vy, s), G2 being one of its repeatable gate control gliders
              from infinity -> released glider -> RF (-> SE, lane L2)               -> glider P2
  condition: {P1, P2} = {(SE, L, t), (SE, L + 6, t - 29)}  (pullSalvo up to translation along the
  diagonal and evolution).

Enumeration: m in MR, L in LR; all 712 repeatable gates r, the symmetries k with
sym_k (direction of r) = SW, vx in VR.  Candidates that are not causal (a reflector behind the source of its glider), whose flight
segments come within 3 cells of the envelope of a gun assembly they do not use or touch the
envelope of a reflector they do not use, or whose pieces overlap are dropped; the NSIM with
the smallest bounding box are simulated (period 30 of the composite; with C0: back in the cycle
with exactly the two salvo gliders leaving; set simulator on the unbounded plane).

Usage: g4_pull3.py [NSIM]      Output: results/g4_pull3.json.gz, summary on stdout
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import glider_at, bbox, SE, SW, NW, NE, DIRNAME, life
import machine
from machine import load_catalog, wl_map, wl_unmap, asm_cells, box_dist, run_scheduled, verify_scheduled
from g1_pull import rf_cells, C0, S_ASM, Comp
from g2_pull import reflect, time_at, rf_center
from f1_fanout import fast_env

# the fan-out used (a line of results/f2_roundtrip.txt): K = (7, 90, 132, 25), kickback control
# (NW, -55, 8) in the coordinates of K; G1 flies NW, so that the length of its first leg delays it
# as much as is needed (with the smallest fan-out, K = (0, 35, 62, 25), G1 flies SE and G2 is
# about 500 generations late for every position of the reflectors: no causal solution).
FANOUT = (7, 90, 132, 25)
G1 = (NW, 29, 730)
G2 = (SW, 75, 771)
MR = range(-160, 131)          # SW lane (x + y) of the second leg of path 1
LR = range(-420, -90)          # final SE lanes
VR = range(-150, 40)
NPLAUS = 400000
KX = life.sym_apply(FANOUT[0], (45, 31))
KCROSS = (KX[0] + FANOUT[1], KX[1] + FANOUT[2])     # crossing point of the streams of K
_P1 = None


def path1():
    """{(L, tau): (rf1, rf2)} for G1 -> SW lane m -> SE lane L."""
    t_src = time_at(G1, KCROSS) + 100
    out = {}
    for m in MR:
        r1 = reflect(G1, SW, m)
        if not r1:
            continue
        t1 = time_at(G1, rf_center(r1[0]))
        if t1 < t_src:
            continue
        for L in LR:
            r2 = reflect(r1[1], SE, L)
            if r2 and time_at(r1[1], rf_center(r2[0])) > t1 + 100:
                out.setdefault((L, r2[1][2]), (r1[0], r2[0]))
    return out


def init():
    global _P1
    _P1 = path1()


def work(job):
    rd, rlane, rtau, od, olane, otau, k = job
    r_wl = (rd, rlane, rtau)
    d, lane0, tau0 = wl_map(r_wl, (k, 0, 0, 0))
    Lc = G2[1] - lane0
    envS = fast_env(S_ASM)
    envK = fast_env(FANOUT)
    t_src2 = time_at(G2, (45, 31))
    sols = []
    for vx in VR:
        vy = d[0] * (d[1] * vx - Lc)
        s = (G2[2] - tau0 + 4 * d[0] * vx) % 30
        asm = (k, vx, vy, s)
        env = fast_env(asm)
        if box_dist(env, envS) < 8 or box_dist(env, envK) < 8:
            continue
        c = wl_unmap(G2, asm)
        n, rem = divmod(c[2] - rtau, 30)
        assert rem == 0 and c[1] == rlane
        o = wl_map((od, olane, otau + 30 * n), asm)
        if o[0] == SE:
            continue
        chains = [[SE]] if o[0] in (SW, NE) else [[SW, SE], [NE, SE]]
        for chain in chains:
            if len(chain) == 2:
                continue                      # keep to one reflector on path 2
            for L2 in LR:
                r = reflect(o, SE, L2)
                if not r:
                    continue
                p2 = r[1]
                for (dl, dt) in ((-6, 29), (6, -29)):       # P1 = P2 + (dl, dt)
                    hit = _P1.get((p2[1] + dl, p2[2] + dt))
                    if hit is None:
                        continue
                    p1 = (SE, p2[1] + dl, p2[2] + dt)
                    a, b = (p1, p2) if dl == -6 else (p2, p1)
                    sols.append({'gb': list(asm), 'rec': [list(rd), rlane, rtau], 'rfs': [list(hit[0]), list(hit[1]), list(r[0])],
                                 'a': a, 'b': b, 'gb_out': o})
    return sols


_GROWN = {}


def grown(kind, k, gap):
    """Cells within Chebyshev distance < gap of the envelope (union over the cycle) of the
    assembly BS1 (kind 'asm') or of the reflector (kind 'rf'), transformed by sym_k."""
    key = (kind, k, gap)
    if key not in _GROWN:
        from g1_pull import rf_cycle
        from common import transform
        base = set().union(*(machine.bs1_cycle() if kind == 'asm' else rf_cycle()))
        gs = set()
        for (x, y) in transform(base, k):
            for dx in range(-gap + 1, gap):
                for dy in range(-gap + 1, gap):
                    gs.add((x + dx, y + dy))
        _GROWN[key] = gs
    return _GROWN[key]


def seg_clear(g, t_a, t_b, obstacles):
    """Is the glider g, during the times t_a .. t_b, clear of all obstacles?  An obstacle is
    (grown cell set, (ox, oy)): the set translated by (ox, oy)."""
    d, lane, tau = g
    q = (int(t_a) - tau) // 4
    q_end = (int(t_b) - tau) // 4
    while q <= q_end:
        x = d[0] * q
        y = d[0] * (d[1] * x - lane)
        for gs, (ox, oy) in obstacles:
            for cx in range(x - 1 - ox, x + 4 - ox):
                for cy in range(y - 1 - oy, y + 4 - oy):
                    if (cx, cy) in gs:
                        return False
        q += 1
    return True


GAP_ASM = 4
GAP_RF = 2


def plausible(sol):
    """Causality and clearance of all flight segments: every glider stays at Chebyshev distance
    >= GAP_ASM from the envelopes of the gun assemblies it does not use and >= GAP_RF from the
    envelopes of the reflectors it does not use."""
    gb = tuple(sol['gb'])
    rf1, rf2, rf3 = [tuple(r) for r in sol['rfs']]
    oS = (grown('asm', 0, GAP_ASM), (0, 0))
    oK = (grown('asm', FANOUT[0], GAP_ASM), (FANOUT[1], FANOUT[2]))
    oG = (grown('asm', gb[0], GAP_ASM), (gb[1], gb[2]))
    o1, o2, o3 = [(grown('rf', r[0], GAP_RF), (r[1], r[2])) for r in (rf1, rf2, rf3)]
    o = tuple(sol['gb_out'])
    o = (tuple(o[0]), o[1], o[2])
    a, b = tuple(sol['a']), tuple(sol['b'])
    leg = reflect(G1, SW, _lane_of_leg(rf1))[1]
    P2 = reflect(o, SE, _out_lane(rf3, o))[1]
    P1 = a if P2 == b else b
    kx, ky = life.sym_apply(gb[0], (45, 31))
    cross_g = (kx + gb[1], ky + gb[2])
    t_k = time_at(G1, KCROSS) + 100
    t_r1 = time_at(G1, rf_center(rf1))
    t_r2 = time_at(leg, rf_center(rf2))
    t_s = time_at(G2, (40, 36))
    t_g = time_at(G2, cross_g)
    t_o = time_at(o, cross_g)
    t_r3 = time_at(o, rf_center(rf3))
    if not (t_r3 > t_o + 60 and t_g > t_s + 100):
        return False
    # static separation: the envelope of every reflector is at distance >= GAP_ASM from the
    # envelopes of the gun assemblies and of the other reflectors
    renv = [(grown('rf', r[0], 1), (r[1], r[2])) for r in (rf1, rf2, rf3)]
    rgrown = [(grown('rf', r[0], GAP_ASM), (r[1], r[2])) for r in (rf1, rf2, rf3)]
    for i, (cs, (px, py)) in enumerate(renv):
        for gs, (ox, oy) in [oS, oK, oG] + [rgrown[j] for j in range(3) if j != i]:
            for (x, y) in cs:
                if (x + px - ox, y + py - oy) in gs:
                    return False
    far = 2400
    checks = [
        (G1, t_k, t_r1 - 30, [oS, oG, o2, o3]),
        (leg, t_r1 + 30, t_r2 - 30, [oS, oK, oG, o3]),
        (P1, t_r2 + 30, t_r2 + far, [oS, oK, oG, o1, o3]),
        (G2, t_s, t_g + 10, [oK, o1, o2, o3]),
        (o, t_o + 40, t_r3 - 30, [oS, oK, o1, o2]),
        (P2, t_r3 + 30, t_r3 + far, [oS, oK, oG, o1, o2]),
    ]
    for (g, ta, tb, obs) in checks:
        if not seg_clear(g, ta, tb, obs):
            return False
    return True


def _lane_of_leg(rf1):
    # the SW lane of the leg after the first reflector: recover it by trying the lanes of MR
    for m in MR:
        r = reflect(G1, SW, m)
        if r and r[0] == rf1:
            return m
    raise ValueError


def _out_lane(rf3, o):
    for L in LR:
        r = reflect(o, SE, L)
        if r and r[0] == rf3:
            return L
    raise ValueError


def footprint(sol):
    cells = set(asm_cells(S_ASM, 0)) | set(asm_cells(FANOUT, 0))
    parts = [asm_cells(tuple(sol['gb']), 0)] + [rf_cells(tuple(rf), 0) for rf in sol['rfs']]
    for c in parts:
        if c & cells:
            return None
        cells |= c
    return cells


def simulate(sol):
    cells = footprint(sol)
    if cells is None:
        return sol, 'overlap'
    try:
        comp = Comp(cells)
    except AssertionError:
        return sol, 'not periodic'
    res = run_scheduled(comp, [C0], limit=3000, t_hint=200)
    if res['status'] != 'restored':
        return sol, res['status']
    outs = sorted(w for (w, th) in res['out'])
    if outs != sorted([tuple(sol['a']), tuple(sol['b'])]):
        return sol, 'other gliders'
    ok, Ts, Te = verify_scheduled(comp, [C0], res)
    if not ok:
        return sol, 'verification failed'
    sol = dict(sol)
    sol['Ts'], sol['Te'], sol['env'] = Ts, Te, list(comp.R.env)
    return sol, 'ok'


def main():
    nsim = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    t = time.time()
    recs = load_catalog()
    jobs = []
    for r in recs:
        if r['kind'] == 'gate' and r['from_infinity'] and len(r['repeat']) == 3:
            (ow, nm) = r['outs'][0]
            for k in range(8):
                if life.sym_apply(k, r['d']) == SW:
                    jobs.append((r['d'], r['lane'], r['tau'], ow[0], ow[1], ow[2], k))
    sols = []
    with Pool(min(20, os.cpu_count() or 1), initializer=init) as pool:
        for ss in pool.imap_unordered(work, jobs, chunksize=4):
            sols.extend(ss)
    print('gate placements tried: %d records x symmetries; exact solutions: %d (%.0f s)' % (len(jobs), len(sols), time.time() - t))
    # cheap ordering by the bounding box of the pieces, then the expensive checks on the smallest
    envS, envK = fast_env(S_ASM), fast_env(FANOUT)
    for s in sols:
        bs = [envS, envK, fast_env(tuple(s['gb']))] + [(r[1] - 25, r[2] - 25, r[1] + 25, r[2] + 25) for r in s['rfs']]
        b = (min(x[0] for x in bs), min(x[1] for x in bs), max(x[2] for x in bs), max(x[3] for x in bs))
        s['area'] = (b[2] - b[0] + 1) * (b[3] - b[1] + 1)
    sols.sort(key=lambda s: s['area'])
    keep = []
    tried = 0
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for i0 in range(0, min(len(sols), NPLAUS), 2000):
            chunk = sols[i0:i0 + 2000]
            flags = pool.map(plausible, chunk, chunksize=16)
            tried += len(chunk)
            for s, f in zip(chunk, flags):
                if f and footprint(s) is not None:
                    b = bbox(footprint(s))
                    s['area'] = (b[2] - b[0] + 1) * (b[3] - b[1] + 1)
                    s['box'] = b
                    keep.append(s)
            if len(keep) >= nsim:
                break
    keep.sort(key=lambda s: s['area'])
    print('of the %d solutions with the smallest boxes: causal, with clear flight segments and without overlap: %d (%.0f s)' % (tried, len(keep), time.time() - t))
    with gzip.open('results/g4_candidates.json.gz', 'wt') as f:
        json.dump(keep, f, separators=(',', ':'))
    good, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for s, st in pool.imap_unordered(simulate, keep[:nsim], chunksize=1):
            stats[st] = stats.get(st, 0) + 1
            print('   %s: Gb %s reflectors %s box %s (%.0f s)' % (st, tuple(s['gb']), s['rfs'], s.get('box'), time.time() - t), flush=True)
            if st == 'ok':
                good.append(s)
    good.sort(key=lambda s: s['area'])
    print('simulated %d: %s (%.0f s)' % (min(nsim, len(keep)), stats, time.time() - t))
    for s in good[:10]:
        print('  Gb %s (control %s) reflectors %s a=%s b=%s env=%s N=%d' % (
            tuple(s['gb']), s['rec'], s['rfs'], tuple(s['a'][1:]), tuple(s['b'][1:]), s['env'], s['Te'] - s['Ts']))
    with gzip.open('results/g4_pull3.json.gz', 'wt') as f:
        json.dump({'solutions': len(sols), 'no_overlap': len(keep), 'stats': stats, 'good': good}, f, separators=(',', ':'))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
