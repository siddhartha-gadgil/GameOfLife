#!/usr/bin/env python3
"""G7 (R-23): push-salvo generator = an upstream fan-out U in series with a re-solved PG1-type core.

Idea (R-22 section 3, "most promising next idea", variant (A) of the task):

  C_U -> U = fan-out (S_U, K_U) of results/f2_roundtrip.json.gz whose output G1 flies SE:
           link glider (its SE output)   = the control glider C0 = (SE, 41, 22) of the core S;
           continue glider (its SW output) -> RF_c (SW -> SE)                    -> salvo glider c
  core:  C0 -> S = blockedStream, K: a fan-out with an NW output (as in PG1):
           G1 (NW) -> RF1 (NW -> SW, SW lane m) -> RF2 (SW -> SE, lane L_a)        -> salvo glider a
           G2 (SW) -> gate Gb (G2 is one of its repeatable control gliders from infinity)
                   -> released glider o -> RF3 (o -> SE)                           -> salvo glider b

Exact conditions.  The salvo {a, b, c} must be one of the three-glider pushes of
results/p1_pushes.json (up to translation), with an insertion order (net.assembly_orders) in which c
is emitted first (RF_c is the most upstream reflector), a is inserted by RF2 (input flying SW:
type 'R') and b by RF3 (type 'L' if o flies NE, 'R' if o flies SW).

Invariants used (checked numerically in `invariants`):
  * a reflection SW -> SE keeps  tau + 4 lane  of the glider; NE -> SE keeps tau;
  * hence  I_a = tau_a + 4 L_a  depends only on m (and on the core fan-out), and
    I_c = tau_c + 4 L_c  only on the type of U (not on its position u along the lane of C0, nor on
    L_c): one exact equation  I_c - I_a = Delta(push)  fixes m;
  * then L_a is free, and b = (L_a + dl_b, tau_a + dt_b) is an exact target for the gate path
    (position of Gb along G2, lane of RF3): solved by indexing.
  * u (the position of U along the lane of C0) only slides RF_c along the lane of c: it is chosen
    as the first value (from UMAX downwards) for which all separations hold.

Filters before simulation: causality; envelopes of all pieces pairwise >= GAP_PIECE; every flight
segment at distance >= GAP_FLIGHT_ASM from the envelopes of gun assemblies and >= GAP_FLIGHT_RF from
those of reflectors it does not use.  Simulation (net.Net.react): with the control glider of U the
composite returns to its cycle and exactly {a, b, c} leave (board, then set simulator on the
unbounded plane).  Then the block test (`block_test`).

Usage: g7_push.py [NSIM [MAXKEEP]]       Output: results/g7_push.json.gz (or $G7_OUT), summary on stdout
Environment: G7_GAP_PIECE, G7_GAP_ASM, G7_GAP_RF (defaults 5, 4, 2), G7_OUT.
"""
import gzip
import itertools
import json
import os
import sys
import time
from multiprocessing import Pool

from common import SE, SW, NW, NE, DIRNAME, bbox, life, glider_at, translate, step_cells
import machine
from machine import load_catalog, wl_map, wl_unmap
from f1_fanout import fast_env
import net
from net import (reflect, move_wl, move_piece, env_box, env_cells, box_dist, set_dist, glider_path,
                 seg_box_dist, asm_cross, time_at, rf_point, assembly_orders)

C0 = (SE, 41, 22)
S = ('asm', 0, 0, 0, 0)
G2_BASE_TAU = 771
LA_RANGE = range(-460, -59)          # lane of a
M_RANGE = range(-240, 11)            # SW lane of the leg RF1 -> RF2
VX_RANGE = range(-240, 40)           # Gb along G2
U_RANGE = range(-60, -420, -1)       # U along the lane of C0 (scanned downwards)
GAP_PIECE = int(os.environ.get('G7_GAP_PIECE', 5))          # envelopes of pieces
GAP_FLIGHT_ASM = int(os.environ.get('G7_GAP_ASM', 4))       # flight segments to gun assemblies
GAP_FLIGHT_RF = int(os.environ.get('G7_GAP_RF', 2))         # flight segments to reflectors
OUT = os.environ.get('G7_OUT', 'results/g7_push.json.gz')
FAR = 2500
NFILTER = 60000


def tup(o):
    return (tuple(o[0]), o[1], o[2])


# --- inputs ------------------------------------------------------------------------------------
def load_fanouts():
    d = json.load(gzip.open('results/f2_roundtrip.json.gz', 'rt'))
    core, ups = [], []
    for fo in d['good']:
        outs = [tup(o) for o in fo['outs']]
        nw = [w for w in outs if w[0] == NW]
        sw = [w for w in outs if w[0] == SW]
        se = [w for w in outs if w[0] == SE]
        if nw and sw:
            core.append({'K': ('asm',) + tuple(fo['asm']), 'G1': nw[0], 'G2': sw[0], 'T': fo['T']})
        if se and sw:
            ups.append({'K': ('asm',) + tuple(fo['asm']), 'G1': se[0], 'G2': sw[0], 'T': fo['T']})
    return core, ups


G0_OWN = (SE, 14, 119)                # the stream glider of S released by C0 (own coordinates)


def U_SHIFT(fu, u):
    g1 = fu['G1']
    return u, u + g1[1] - C0[1], C0[2] - g1[2] + 4 * u


def place_U(fu, u):
    """The fan-out U moved by (u, v) and delayed so that its SE output is exactly C0."""
    g1, g2 = fu['G1'], fu['G2']
    v = u + g1[1] - C0[1]
    s = C0[2] - g1[2] + 4 * u
    SF = ('asm', 0, u, v, s % 30)
    KF = move_piece(fu['K'], u, v, s)
    ctrl, link, cont = move_wl(C0, u, v, s), move_wl(g1, u, v, s), move_wl(g2, u, v, s)
    assert link == C0
    return SF, KF, ctrl, cont


def invariant_c(fu):
    """I_c = tau_c + 4 L_c of the glider reflected SW -> SE from the continue glider (asserted
    independent of u and L_c); and the parity of L_c."""
    vals = set()
    for u in (-150, -151, -200):
        cont = place_U(fu, u)[3]
        for L in range(-120, -116):
            r = reflect(cont, SE, L)
            if r:
                vals.add((r[1][2] + 4 * L, L % 2))
    assert len(vals) == 1, vals
    return vals.pop()


def invariant_a(fc):
    """{m: I_a} for path 1 of the core fan-out fc (asserted independent of L_a), and the parity
    of L_a."""
    out = {}
    par = set()
    for m in M_RANGE:
        r1 = reflect(fc['G1'], SW, m)
        if not r1:
            continue
        vals = set()
        for L in range(-121, -117):
            r2 = reflect(r1[1], SE, L)
            if r2:
                vals.add(r2[1][2] + 4 * L)
                par.add(L % 2)
        assert len(vals) == 1
        out[m] = vals.pop()
    assert len(par) == 1
    return out, par.pop()


def push_roles():
    """[(push index, roles {'a','b','c'} -> (lane, tau), type of b)] with c first, a of type R."""
    P = json.load(open('results/p1_pushes.json'))
    out = []
    for i, p in enumerate(P):
        wl = [tuple(w) for w in p['wl']]
        seen = set()
        for order in assembly_orders(wl):
            (gc, _), (g2, t2), (g3, t3) = order
            for (ga, ta), (gb, tb) in (((g2, t2), (g3, t3)), ((g3, t3), (g2, t2))):
                if ta != 'R':
                    continue
                key = (ga, gb, gc, tb)
                if key in seen:
                    continue
                seen.add(key)
                out.append({'push': i, 'n': p['n'], 'wl': wl, 'a': ga, 'b': gb, 'c': gc, 'tb': tb,
                            'order': [list(order[0][0]), list(order[1][0]), list(order[2][0])]})
    return out


def invariants():
    """Prints the slopes of the reflections used (tau_out = A + B lane_out)."""
    for g in ((NE, -46, 1092), (SW, 75, 771), (NW, 29, 730)):
        r = [(L, reflect(g, SE if g[0] != NW else SW, L)) for L in range(-100, -90)]
        r = [(L, x[1][2]) for (L, x) in r if x]
        print('  ', DIRNAME[g[0]], 'input: (lane_out, tau_out) =', r[:3])


B_OF = {NE: 0, SW: -4}                # tau_out = A + B lane_out for o -> SE


# --- enumeration -------------------------------------------------------------------------------
_T = None


def build_targets(core, ups, roles):
    """Index {(o direction, lane parity, A): [target]}; a target fixes everything but Gb, RF3, u."""
    idx = {}
    n = 0
    stats = {}
    Ic = {}
    for j, fu in enumerate(ups):
        Ic.setdefault(invariant_c(fu), []).append(j)
    for ci, fc in enumerate(core):
        Ia, apar = invariant_a(fc)
        g2off = fc['G2'][2] - G2_BASE_TAU
        assert fc['G2'][:2] == (SW, 75) and g2off % 30 == 0
        for ri, ro in enumerate(roles):
            (la, ta), (lb, tb), (lc, tc) = ro['a'], ro['b'], ro['c']
            delta = (tc - ta) + 4 * (lc - la)
            odir = NE if ro['tb'] == 'L' else SW
            for (ic, cpar), js in Ic.items():
                for m, ia in Ia.items():
                    if ic - ia != delta:
                        continue
                    r1 = reflect(fc['G1'], SW, m)
                    for La in LA_RANGE:
                        if La % 2 != apar or (La + lc - la) % 2 != cpar:
                            continue
                        r2 = reflect(r1[1], SE, La)
                        a = r2[1]
                        Lb, tb_ = La + lb - la, a[2] + tb - ta
                        Lc, tc_ = La + lc - la, a[2] + tc - ta
                        assert tc_ + 4 * Lc == ic
                        key = (odir, Lb % 2, tb_ - g2off - B_OF[odir] * Lb)
                        idx.setdefault(key, []).append((ci, ri, js[0], m, La, Lb, tb_, Lc, tc_))
                        n += 1
                        stats[(ri, ro['n'])] = stats.get((ri, ro['n']), 0) + 1
    return idx, n, stats


def gate_jobs():
    recs = load_catalog()
    jobs = []
    for r in recs:
        if r['kind'] == 'gate' and r['from_infinity'] and len(r['repeat']) == 3:
            (ow, nm) = r['outs'][0]
            for k in range(8):
                if life.sym_apply(k, r['d']) == SW:
                    jobs.append((r['d'], r['lane'], r['tau'], ow[0], ow[1], ow[2], k))
    return jobs


def init_targets(idx):
    global _T
    _T = idx


def gate_work(job):
    """All exact solutions for one gate record in one symmetry (base G2 = (SW, 75, 771))."""
    rd, rlane, rtau, od, olane, otau, k = job
    G2 = (SW, 75, G2_BASE_TAU)
    d, lane0, tau0 = wl_map((rd, rlane, rtau), (k, 0, 0, 0))
    Lc = G2[1] - lane0
    sols = []
    for vx in VX_RANGE:
        vy = d[0] * (d[1] * vx - Lc)
        s = (G2[2] - tau0 + 4 * d[0] * vx) % 30
        asm = (k, vx, vy, s)
        c = wl_unmap(G2, asm)
        n, rem = divmod(c[2] - rtau, 30)
        assert rem == 0 and c[1] == rlane
        o = wl_map((od, olane, otau + 30 * n), asm)
        if o[0] not in B_OF:
            continue
        # tau_b = A + B L_b on the lanes of one parity
        smp = [(L, reflect(o, SE, L)) for L in (-200, -199)]
        smp = [(L, r) for (L, r) in smp if r]
        L0, r0 = smp[0]
        A = r0[1][2] - B_OF[o[0]] * L0
        for t in _T.get((o[0], L0 % 2, A), ()):
            sols.append((list(asm), [list(o[0]), o[1], o[2]], [list(rd), rlane, rtau]) + t)
    return sols


# --- geometry ----------------------------------------------------------------------------------
_CORE = None
_UPS = None
_ROLES = None


def init_geo():
    global _CORE, _UPS, _ROLES
    _CORE, _UPS = load_fanouts()
    _ROLES = push_roles()


def expand(sol):
    """The candidate as a dict of pieces and world lines (core only: no U)."""
    gb, o, rec, ci, ri, uj, m, La, Lb, tb, Lc, tc = sol
    fc = _CORE[ci]
    g2off = fc['G2'][2] - G2_BASE_TAU
    Gb = ('asm',) + tuple(gb)
    o = (tuple(o[0]), o[1], o[2] + g2off)
    r1 = reflect(fc['G1'], SW, m)
    r2 = reflect(r1[1], SE, La)
    r3 = reflect(o, SE, Lb)
    assert r3[1] == (SE, Lb, tb), (r3, Lb, tb)
    return {'ci': ci, 'ri': ri, 'uj': uj, 'm': m, 'S': S, 'K': fc['K'], 'Gb': Gb, 'RF1': r1[0], 'RF2': r2[0],
            'RF3': r3[0], 'G1': fc['G1'], 'leg': r1[1], 'a': r2[1], 'G2': fc['G2'], 'o': o, 'b': r3[1],
            'c': (SE, Lc, tc), 'rec': rec}


_GROWN = {}


def _env0(p):
    """Envelope of the piece p at the origin (sym only), cached."""
    key = ('env', p[0], p[1])
    if key not in _GROWN:
        _GROWN[key] = frozenset(env_cells((p[0], p[1], 0, 0, 0)))
    return _GROWN[key]


def _grown0(p, gap):
    """Cells at Chebyshev distance < gap from the envelope of p at the origin, cached."""
    key = ('grown', p[0], p[1], gap)
    if key not in _GROWN:
        g = set()
        for (x, y) in _env0(p):
            for dx in range(-gap + 1, gap):
                for dy in range(-gap + 1, gap):
                    g.add((x + dx, y + dy))
        _GROWN[key] = frozenset(g)
    return _GROWN[key]


def _near(cells, p, gap):
    """Is some cell of `cells` at distance < gap from the envelope of the piece p?"""
    g = _grown0(p, gap)
    ox, oy = p[2], p[3]
    for (x, y) in cells:
        if (x - ox, y - oy) in g:
            return True
    return False


def _clear(w, ta, tb, pieces):
    """Is the glider w (times ta .. tb) clear of the given pieces?"""
    for p in pieces:
        gap = GAP_FLIGHT_ASM if p[0] == 'asm' else GAP_FLIGHT_RF
        b = env_box(p)
        if seg_box_dist(w, ta, tb, b) >= gap:
            continue
        if _near(glider_path(w, ta, tb), p, gap):
            return False
    return True


def _apart(new, old):
    for p in new:
        for q in old:
            if box_dist(env_box(p), env_box(q)) >= GAP_PIECE:
                continue
            a, b = (p, q) if len(_env0(p)) <= len(_env0(q)) else (q, p)
            if _near(translate(_env0(a), a[2], a[3]), b, GAP_PIECE):
                return False
    return True


def core_segments(e):
    xs, xk, xg = asm_cross(e['S']), asm_cross(e['K']), asm_cross(e['Gb'])
    p1, p2, p3 = rf_point(e['RF1']), rf_point(e['RF2']), rf_point(e['RF3'])
    return [
        ('G1', e['G1'], time_at(e['G1'], xk) + 60, time_at(e['G1'], p1) - 30, ('K', 'RF1')),
        ('leg', e['leg'], time_at(e['leg'], p1) + 30, time_at(e['leg'], p2) - 30, ('RF1', 'RF2')),
        ('a', e['a'], time_at(e['a'], p2) + 30, time_at(e['a'], p2) + FAR, ('RF2',)),
        ('G2', e['G2'], time_at(e['G2'], xs) + 20, time_at(e['G2'], xg) - 10, ('S', 'Gb')),
        ('o', e['o'], time_at(e['o'], xg) + 40, time_at(e['o'], p3) - 30, ('Gb', 'RF3')),
        ('b', e['b'], time_at(e['b'], p3) + 30, time_at(e['b'], p3) + FAR, ('RF3',)),
    ]


CORE_NAMES = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3']


def core_ok(sol):
    """Causality, separations and clear flight segments of the core."""
    try:
        e = expand(sol)
    except (AssertionError, TypeError):
        return None
    xk, xs, xg = asm_cross(e['K']), asm_cross(e['S']), asm_cross(e['Gb'])
    t1 = time_at(e['G1'], rf_point(e['RF1']))
    if t1 < time_at(e['G1'], xk) + 100:
        return None
    if time_at(e['leg'], rf_point(e['RF2'])) < t1 + 60:
        return None
    if time_at(e['G2'], xg) < time_at(e['G2'], xs) + 100:
        return None
    if time_at(e['o'], rf_point(e['RF3'])) < time_at(e['o'], xg) + 60:
        return None
    pcs = {n: e[n] for n in CORE_NAMES}
    if not _apart([pcs['Gb']], [pcs['S'], pcs['K']]):
        return None
    for i, n in enumerate(['RF1', 'RF2', 'RF3']):
        if not _apart([pcs[n]], [pcs[x] for x in CORE_NAMES if x != n]):
            return None
    for (nm, w, ta, tb, used) in core_segments(e):
        if tb < ta + 10:
            return None
        if not _clear(w, ta, tb, [pcs[x] for x in CORE_NAMES if x not in used]):
            return None
    # c flies through the core: clear of everything (RF_c is placed upstream later)
    c = e['c']
    tcs = time_at(c, (-400, -400 - c[1]))
    if not _clear(c, tcs, tcs + FAR + 1600, list(pcs.values())):
        return None
    return e


def add_U(e):
    """Choose u (the first one in U_RANGE that works): pieces SF, KF, RF_c."""
    fu = _UPS[e['uj']]
    core = [e[n] for n in CORE_NAMES]
    c = e['c']
    t_first = min(time_at(c, rf_point(p)) for p in core)
    for u in U_RANGE:
        SF, KF, ctrl, cont = place_U(fu, u)
        r = reflect(cont, SE, e['c'][1])
        if r is None:
            return None
        rfc, c = r
        assert c == e['c']
        pc = rf_point(rfc)
        # RF_c upstream of the core along c: c reaches RF_c before it comes near any core piece
        if time_at(c, pc) > t_first - 60:
            continue
        if not _apart([rfc], core) or not _apart([SF, KF], core + [rfc]):
            continue
        xsf, xkf = asm_cross(SF), asm_cross(KF)
        if time_at(cont, pc) < time_at(cont, xsf) + 100:
            continue
        g0 = move_wl(G0_OWN, *U_SHIFT(fu, u))
        segs = [('G0', g0, time_at(g0, xsf) + 20, time_at(g0, xkf) - 20, [rfc] + core),
                ('ctrl', ctrl, time_at(ctrl, xsf) - FAR, time_at(ctrl, xsf) - 20, [rfc] + core),
                ('link', C0, time_at(C0, xkf) + 30, time_at(C0, asm_cross(S)) - 30, [rfc] + core[1:]),
                ('cont', cont, time_at(cont, xsf) + 60, time_at(cont, pc) - 30, [KF] + core),
                ('c', c, time_at(c, pc) + 30, time_at(c, pc) + FAR, [SF, KF])]
        if all(_clear(w, ta, tb, ps) for (nm, w, ta, tb, ps) in segs):
            e = dict(e)
            e.update({'u': u, 'SF': SF, 'KF': KF, 'RFc': rfc, 'ctrl': ctrl, 'cont': cont})
            return e
    return None


NAMES = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3', 'SF', 'KF', 'RFc']


def candidate(sol):
    e = core_ok(sol)
    if e is None:
        return None
    e = add_U(e)
    if e is None:
        return None
    pcs = [e[n] for n in NAMES]
    bs = [env_box(p) for p in pcs]
    box = (min(b[0] for b in bs), min(b[1] for b in bs), max(b[2] for b in bs), max(b[3] for b in bs))
    e['box'] = box
    e['area'] = (box[2] - box[0] + 1) * (box[3] - box[1] + 1)
    return e


def simulate(e):
    pcs = [e[n] for n in NAMES]
    try:
        nt = net.Net(pcs, NAMES)
    except (ValueError, AssertionError):
        return e, 'not periodic'
    st, outs, Ts, Te = nt.react([e['ctrl']], limit=8000)
    if st != 'ok':
        return e, st
    if outs != sorted([e['a'], e['b'], e['c']]):
        return e, 'other gliders'
    e = dict(e)
    e['Ts'], e['Te'], e['env'] = Ts, Te, list(nt.env)
    return e, 'ok'


def jsonable(e):
    out = {}
    for k, v in e.items():
        out[k] = v
    return out


def main():
    nsim = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    maxkeep = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
    t = time.time()
    core, ups = load_fanouts()
    roles = push_roles()
    print('gaps: pieces %d, flight to assemblies %d, flight to reflectors %d' % (GAP_PIECE, GAP_FLIGHT_ASM, GAP_FLIGHT_RF))
    print('core fan-outs (NW output): %d; upstream fan-outs (SE output): %d; push roles (c first, a by RF2): %d' % (
        len(core), len(ups), len(roles)))
    for ro in roles:
        print('   push %3d (n %3d) %s: a %s b %s (type %s) c %s' % (ro['push'], ro['n'], ro['wl'], ro['a'], ro['b'], ro['tb'], ro['c']))
    invariants()
    idx, nt_, stats = build_targets(core, ups, roles)
    print('targets for b: %d (by role: %s) (%.0f s)' % (nt_, sorted(stats.items()), time.time() - t))
    jobs = gate_jobs()
    sols = []
    with Pool(min(20, os.cpu_count() or 1), initializer=init_targets, initargs=(idx,)) as pool:
        for ss in pool.imap_unordered(gate_work, jobs, chunksize=4):
            sols.extend(ss)
    print('gate jobs %d; exact solutions: %d (%.0f s)' % (len(jobs), len(sols), time.time() - t))
    by = {}
    for s in sols:
        by[s[4]] = by.get(s[4], 0) + 1
    print('  by role: %s' % sorted(by.items()))
    # cheap order: by the box of S, K, Gb and the reflectors' points
    _, _ = core, ups

    def roughbox(s):
        gb = s[0]
        L = s[7]
        e = fast_env(tuple(gb))
        return max(e[2], 90) - min(e[0], -60, L) + max(e[3], 132) - min(e[1], 0)
    sols.sort(key=roughbox)
    nall = len(sols)
    sols = sols[:NFILTER]
    keep = []
    tried = 0
    with Pool(min(20, os.cpu_count() or 1), initializer=init_geo) as pool:
        for i0 in range(0, len(sols), 2000):
            chunk = sols[i0:i0 + 2000]
            for e in pool.map(candidate, chunk, chunksize=20):
                if e is not None:
                    keep.append(e)
            tried += len(chunk)
            print('   filtered %d: %d candidates (%.0f s)' % (tried, len(keep), time.time() - t), flush=True)
            if len(keep) >= maxkeep:
                break
    keep.sort(key=lambda e: e['area'])
    print('candidates (causal, separated, clear flight segments): %d of %d tried (of %d, smallest first) (%.0f s)' % (len(keep), tried, nall, time.time() - t))
    good, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1), initializer=init_geo) as pool:
        for e, st in pool.imap_unordered(simulate, keep[:nsim], chunksize=1):
            stats[st] = stats.get(st, 0) + 1
            if st == 'ok':
                good.append(e)
                print('   ok: role %d m %d u %d Gb %s box %s (%.0f s)' % (e['ri'], e['m'], e['u'], e['Gb'], e['box'], time.time() - t), flush=True)
    good.sort(key=lambda e: e['area'])
    print('simulated %d: %s (%.0f s)' % (min(nsim, len(keep)), stats, time.time() - t))
    for e in good[:10]:
        print('  role %d core %d U %d m %d u %d: pieces %s; a %s b %s c %s; box %s N %d' % (
            e['ri'], e['ci'], e['uj'], e['m'], e['u'], [e[n] for n in NAMES], e['a'], e['b'], e['c'], e['box'], e['Te'] - e['Ts']))
    with gzip.open(OUT, 'wt') as f:
        json.dump({'solutions': len(sols), 'candidates': len(keep), 'stats': stats, 'good': good[:200],
                   'roles': roles}, f, separators=(',', ':'))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
