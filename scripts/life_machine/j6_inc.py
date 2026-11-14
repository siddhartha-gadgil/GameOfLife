#!/usr/bin/env python3
"""J6 (R-24): the INC machinery, third variant (with a jog J1, J2 when the lane of the gate output
would cross the gate Gb of the pull): the class (parity) obstruction of j4_inc.py and
j5_inc.py is removed by a GATE on the path of c, which re-times its output to its own guns.

  C_I -> U    = verified fan-out with outputs SE + SW, placed so that its SE output is the control
                of the core;  U's SW output = control glider (from infinity, repeatable) of a gate
                Gc = copy of blockedStream in symmetry 0 or 6 whose released glider (stream A) flies
                SE on lane l3  ->  R3a (SE -> NE)  = cin (input of RF_c);
         core = verified fan-out with outputs NW (G1) + SW (G2), frame (0, X, Y, s):
                G2 (SW) -> R_w (SW -> SE)                                 = w   (OR control of Gb),
                G1 (NW) -> RF1' (NW -> SW, leg lane m) -> RF2' (SW -> SE)  = s1  (input of Rp).
Exactness: s is fixed by w, m by s1 (congruence mod 4) as in j4_inc.py; for Gc the released glider's
tau depends only on (record, l3) (the delay of Gc only selects the phase), so l3 is found by a scan.

Usage: j6_inc.py DESIGN [NSIM]      Output: results/j6_inc_DESIGN.json.gz, summary on stdout.
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import SE, SW, NE, NW, life
from reactions import shift_wl
from machine import load_catalog, wl_map, wl_unmap
from net import Net, reflect_to, env_box, time_at, rf_point, box_dist, move_piece, asm_cross
from g2_pull import reflect
from g4_pull3 import seg_clear
import j2_pocket as J
import j3_stage as J3
import j4_inc as J4
from j4_inc import CORE, UPS, C0, FAR, obs, core_geometry, core_exact

GAP = int(os.environ.get('J6_GAP', 5))
L3R = range(-60, -900, -1)      # lanes of the gate output; lanes > -222 cross the gate Gb of the pull: jog
_GATES = None


def gates_sw():
    """[(k, record)]: repeatable gate records from infinity releasing stream A, in a symmetry k
    (0 or 6) in which the control flies SW and the released glider SE."""
    global _GATES
    if _GATES is None:
        _GATES = []
        for r in load_catalog():
            if r['from_infinity'] and r['repeat'] and len(r['outs']) == 1 and r['outs'][0][1] == 'A':
                for k in (0, 6):
                    if life.sym_apply(k, r['d']) == SW:
                        _GATES.append((k, r))
    return _GATES


_G0 = {}


def gate_for(cont, k, r, target_tau):
    """All copies (k, vx, vy, s) of blockedStream with control `cont` (a repeatable control of the
    record r, up to 30 n) whose released glider is (SE, l3, target_tau), l3 in L3R: [(piece, glider)]."""
    key = (k, r['wl'])
    if key not in _G0:
        _G0[key] = (wl_map(r['outs'][0][0], (k, 0, 0, 0)), wl_map(r['wl'], (k, 0, 0, 0)))
    o0, c0 = _G0[key]
    out = []
    b = cont[1] - c0[1]                       # SW control lane = c0.lane + vx + vy
    def tau_out(l3):
        a = l3 - o0[1]                        # SE lane l3 = o0.lane + vx - vy
        vx, vy = (a + b) // 2, (b - a) // 2
        o = shift_wl(o0, vx, vy, 0)
        c = shift_wl(c0, vx, vy, 0)
        return o[2] + cont[2] - c[2], vx, vy
    for par in (0, 1):
        l3a = L3R[0] - ((L3R[0] - o0[1] + b) % 2) - 2 * par
        ta, _, _ = tau_out(l3a)
        tb, _, _ = tau_out(l3a - 2)
        slope = tb - ta
        if slope == 0:
            continue
        num = target_tau - ta
        if num % slope:
            continue
        l3 = l3a - 2 * (num // slope)
        if not (L3R[-1] <= l3 <= L3R[0]):
            continue
        t, vx, vy = tau_out(l3)
        if t != target_tau:
            continue
        d = cont[2] - shift_wl(c0, vx, vy, 0)[2]
        sdel = d % 30
        frame = (k, vx, vy, sdel)
        n = (d - sdel) // 30
        own = r['outs'][0][0]
        if wl_unmap(cont, frame) != (r['wl'][0], r['wl'][1], r['wl'][2] + 30 * n):
            continue
        o = wl_map((own[0], own[1], own[2] + 30 * n), frame)
        if o != (SE, l3, target_tau):
            continue
        out.append((('asm',) + frame, o))
        break
    return out


def jog(s3, target_tau, lmax=-222, lmin=-700, mrange=range(-400, -10)):
    """s3 (SE) -> J1 (SE -> SW, SW lane m) -> J2 (SW -> SE, lane l) with the output tau equal to
    target_tau and l in [lmin, lmax]: yields (J1, leg, J2, glider)."""
    for m in mrange:
        r1 = reflect(s3, SW, m)
        if r1 is None:
            continue
        leg = r1[1]
        pts = []
        for l0 in (lmax, lmax - 1):
            r2 = reflect(leg, SE, l0)
            if r2:
                pts.append((l0, r2[1][2]))
        if not pts:
            continue
        l0, t0 = pts[0]
        r2b = reflect(leg, SE, l0 - 2)
        slope = r2b[1][2] - t0
        if slope == 0 or (target_tau - t0) % slope:
            continue
        l = l0 - 2 * ((target_tau - t0) // slope)
        if not (lmin <= l <= lmax):
            continue
        r2 = reflect(leg, SE, l)
        if r2 is None or r2[1][2] != target_tau:
            continue
        yield ('rf',) + tuple(r1[0]), leg, ('rf',) + tuple(r2[0]), r2[1]


_GNE = None


def gates_ne():
    """[(k, record)]: repeatable gate records from infinity in a symmetry k in which the control
    flies SE and the released glider NE."""
    global _GNE
    if _GNE is None:
        _GNE = []
        for r in load_catalog():
            if r['from_infinity'] and r['repeat'] and len(r['outs']) == 1:
                for k in range(8):
                    if life.sym_apply(k, r['d']) == SE and life.sym_apply(k, r['outs'][0][0][0]) == NE:
                        _GNE.append((k, r))
    return _GNE


LAR = range(-90, -900, -1)           # SE lane of the control of Gc (clearance of the gate Gb of the pull checked exactly)


def gate_ne(cont, cin):
    """cont (SW) -> R_a (SW -> SE, lane lam) -> gate Gc (lam its control lane) -> released glider
    exactly cin (NE), lam in LAR.  Yields (R_a, control, Gc).  The residual is affine in lam on
    each parity class: solved directly."""
    for (k, r) in gates_ne():
        key = (k, r['wl'])
        if key not in _G0:
            _G0[key] = (wl_map(r['outs'][0][0], (k, 0, 0, 0)), wl_map(r['wl'], (k, 0, 0, 0)))
        o0, c0 = _G0[key]
        a = o0[1] - cin[1]                       # vx + vy

        def resid(lam):
            b = lam - c0[1]                      # vx - vy
            if (a + b) % 2:
                return None
            ra = reflect(cont, SE, lam)
            if ra is None:
                return None
            ctl = ra[1]
            vx, vy = (a + b) // 2, (a - b) // 2
            d = ctl[2] - shift_wl(c0, vx, vy, 0)[2]
            return shift_wl(o0, vx, vy, 0)[2] + d - cin[2], ra, ctl, vx, vy, d

        base = None
        for l0 in (LAR[0], LAR[0] - 1, LAR[0] - 2, LAR[0] - 3):
            r0 = resid(l0)
            if r0 is not None:
                base = (l0, r0)
                break
        if base is None:
            continue
        l0, r0 = base
        r1 = None
        for st in (2, 4):
            r1 = resid(l0 - st)
            if r1 is not None:
                break
        if r1 is None:
            continue
        slope = (r1[0] - r0[0])
        if slope == 0 or r0[0] % slope:
            continue
        lam = l0 + st * (r0[0] // slope)
        if not (LAR[-1] <= lam <= LAR[0]):
            continue
        rr = resid(lam)
        if rr is None or rr[0] != 0:
            continue
        _, ra, ctl, vx, vy, d = rr
        sdel = d % 30
        n = (d - sdel) // 30
        frame = (k, vx, vy, sdel)
        own = r['outs'][0][0]
        if wl_unmap(ctl, frame) != (r['wl'][0], r['wl'][1], r['wl'][2] + 30 * n):
            continue
        if wl_map((own[0], own[1], own[2] + 30 * n), frame) != cin:
            continue
        yield ('rf',) + tuple(ra[0]), ctl, ('asm',) + frame


def u_gate(fu, core, cin, rfc, fixed, ux, loop):
    """U, a delay loop J1 (SE -> NE), J2 (NE -> NW), J3 (NW -> SW), J4 (SW -> SE) on the link from
    U to the core (its NW leg delays the core, hence w, s1 and T, against U's SW output; a loop
    without a NW leg would not change the timing invariant), R_a and the gate Gc."""
    cx = core['cx']
    k, X, Y, s = cx['frame']
    ctrl = shift_wl(C0, X, Y, s)
    Sc = core['pieces'][0]
    j4, la, lb, lc = loop
    J4p, sw = reflect_to(ctrl, SW, j4)
    J3p, nw = reflect_to(sw, NW, j4 + la)
    J2p, ne = reflect_to(nw, NE, j4 + la + lb)
    J1p, link = reflect_to(ne, SE, j4 + la + lb - lc)
    g = fu['G1']
    vx = ux
    vy = vx - (link[1] - g[1])
    su = link[2] - g[2] + 4 * vx
    Su = ('asm', 0, vx, vy, su % 30)
    Ku = move_piece(fu['K'], vx, vy, su)
    cont = shift_wl(fu['G2'], vx, vy, su)
    cI = shift_wl(C0, vx, vy, su)
    others = fixed + [rfc] + core['pieces']
    ob = [env_box(p) for p in others]
    t_rfc = time_at(cin, rf_point(rfc))
    t_c = time_at(cont, asm_cross(Su)) + 60
    t_l = time_at(link, asm_cross(Ku)) + 60
    legs = [(link, J1p), (ne, J2p), (nw, J3p), (sw, J4p)]
    times = []
    for i, (g_, piece) in enumerate(legs):
        times.append(time_at(g_, rf_point(piece)))
    # causality: each reflector after the previous one
    prev = t_l
    for i, (g_, piece) in enumerate(legs):
        t_in = time_at(g_, rf_point(piece))
        if t_in < prev + 30:
            return None
        nxt = legs[i + 1][0] if i + 1 < len(legs) else ctrl
        prev = time_at(nxt, rf_point(piece))
    t_s = time_at(ctrl, asm_cross(Sc))
    if t_s < prev + 100:
        return None
    base = [Su, Ku, J1p, J2p, J3p, J4p]
    nb0 = [env_box(p) for p in base]
    for i, b in enumerate(nb0):
        if min(box_dist(b, x) for x in ob) < GAP:
            return None
        for j in range(i):
            if box_dist(b, nb0[j]) < GAP and (i, j) != (1, 0):
                return None
    for (Ra, ctl, Gc) in gate_ne(cont, cin):
        new = base + [Ra, Gc]
        nb = nb0 + [env_box(Ra), env_box(Gc)]
        if any(min(box_dist(nb[i], x) for x in ob + nb[:i]) < GAP for i in (6, 7)):
            continue
        t_a = time_at(cont, rf_point(Ra))
        t_a2 = time_at(ctl, rf_point(Ra))
        t_g = time_at(ctl, asm_cross(Gc))
        t_o = time_at(cin, asm_cross(Gc)) + 40
        if not (t_a > t_c + 40 and t_g > t_a2 + 150 and t_rfc > t_o + 60):
            continue
        allp = others + new
        ex = lambda e_: obs([p for p in allp if p not in e_])
        checks = [(cont, t_c, t_a - 30, ex([Su, Ku, Ra])),
                  (ctl, t_a2 + 30, t_g - 120, ex([Ra, Gc])),
                  (cin, t_o, t_rfc - 30, ex([Gc, rfc])),
                  (cI, time_at(cI, asm_cross(Su)) - FAR, time_at(cI, asm_cross(Su)) - 100, ex([Su, Ku])),
                  ]
        pts = [t_l] + [time_at(legs[i][0], rf_point(legs[i][1])) for i in range(4)]
        outs = [time_at(legs[i + 1][0] if i < 3 else ctrl, rf_point(legs[i][1])) for i in range(4)]
        checks.append((link, t_l, pts[1] - 30, ex([Su, Ku, J1p])))
        checks.append((ne, outs[0] + 30, pts[2] - 30, ex([J1p, J2p])))
        checks.append((nw, outs[1] + 30, pts[3] - 30, ex([J2p, J3p])))
        checks.append((sw, outs[2] + 30, pts[4] - 30, ex([J3p, J4p])))
        checks.append((ctrl, outs[3] + 30, t_s - 100, ex([J4p, Sc, core['pieces'][1]])))
        if not all(seg_clear(g_, a_, b_, o_) for (g_, a_, b_, o_) in checks):
            continue
        # the flights of the core (INC) and of the pull (DEC) must not meet the new pieces
        return {'pieces': new, 'C_I': cI, 'l3': ctl[1], 'ux': ux, 'gate': Gc, 'jog': loop}
    return None


_CTX = {}


def core_flights_clear(cg, new, fixed, pull_segs):
    """The INC flights of the core and the DEC flights of the pull keep >= 3 from the pieces new."""
    cx = cg['cx']
    Kc, Sc = cg['pieces'][1], cg['pieces'][0]
    g1, g2, leg = cx['g1'], cx['g2'], cx['leg']
    segs = [(g1, time_at(g1, asm_cross(Kc)) + 100, time_at(g1, rf_point(cx['RF1'])) - 30),
            (leg, time_at(leg, rf_point(cx['RF1'])) + 30, time_at(leg, rf_point(cx['RF2'])) - 30),
            (g2, time_at(g2, asm_cross(Sc)) + 60, time_at(g2, rf_point(cx['Rw'])) - 30)]
    segs += [(g, a, b) for (nm, g, a, b) in pull_segs]
    return all(seg_clear(g, a, b, obs(new)) for (g, a, b) in segs)


def init(ctx):
    _CTX.update(ctx)


def work(job):
    ti, fi = job
    rec, T = _CTX['rec'], _CTX['targets'][ti]
    sol = rec['sol']
    w, Tb, e, c, rfcs, opts = T
    fc = CORE[fi]
    pull = J.pull_pieces(sol)
    pull_segs = J.segments(sol)
    gb = tuple(sol['gb'])
    kx, ky = life.sym_apply(gb[0], (45, 31))
    t_gb = time_at(w, (kx + gb[1], ky + gb[2]))
    for (rfe, rp, s1) in opts:
        if core_exact(fc, w, s1, -200, -400) is None and core_exact(fc, w, s1, -201, -400) is None:
            continue
        fixed = pull + [rfe, rp]
        fixed_boxes = [env_box(p) for p in fixed]
        t_rp = time_at(s1, rf_point(rp))
        tried = 0
        for Y in range(-60, -700, -2):
            for d in range(-60, 200, 1):
                cg = core_geometry(fc, w, s1, Y + d, Y, fixed, fixed_boxes, t_gb, t_rp, pull_segs)
                if cg is None:
                    continue
                tried += 1
                for (rfc, cin) in rfcs[:6]:
                    if min(box_dist(env_box(rfc), env_box(p)) for p in cg['pieces']) < GAP:
                        continue
                    for ui, fu in enumerate(UPS):
                        X0 = cg['cx']['frame'][1]
                        for j4 in (X0 - 60, X0 - 120):
                          for lb in range(10, 90, 8):
                            for (la, lc) in ((20, 50), (50, 20), (20, 70), (70, 20)):
                              if True:
                                for ux in (j4 + la + lb - lc - 140, j4 + la + lb - lc - 220):
                                    ug = u_gate(fu, cg, cin, rfc, fixed, ux, (j4, la, lb, lc))
                                    if ug is None:
                                        continue
                                    allp = fixed + [rfc] + cg['pieces'] + ug['pieces']
                                    if not core_flights_clear(cg, ug['pieces'], fixed, pull_segs):
                                        continue
                                    bs = [env_box(p) for p in allp]
                                    bx = (min(b[0] for b in bs), min(b[1] for b in bs), max(b[2] for b in bs), max(b[3] for b in bs))
                                    return [{'jog': ug['jog'], 'gate': ug['gate'], 'w': w, 'T': Tb, 'e': e, 'c': c, 'cin': cin, 's1': s1, 'core': fi, 'U': ui,
                                             'frame': cg['cx']['frame'], 'm': cg['cx']['m'], 'l3': ug['l3'], 'ux': ux,
                                             'pieces': allp, 'C_I': ug['C_I'], 'box': bx,
                                             'area': (bx[2] - bx[0] + 1) * (bx[3] - bx[1] + 1)}]
                if tried >= 3:
                    break
            if tried >= 3:
                break
    return []


NAMES = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3', 'RFe', 'Rp', 'RFc', 'Sc', 'Kc', 'RF1c', 'RF2c', 'Rw', 'Su', 'Ku', 'J1', 'J2', 'J3', 'J4', 'Ra', 'Gc']


def names_of(d):
    return NAMES


def simulate(d):
    try:
        nt = Net(d['pieces'], names_of(d))
    except (AssertionError, ValueError):
        return d, 'not periodic/overlap'
    s1, outs1, Ts1, Te1 = nt.react([C0], limit=4000)
    if s1 != 'ok' or outs1 != sorted([d['a'], d['b']]):
        return d, 'DEC %s' % s1
    s2, outs2, Ts2, Te2 = nt.react([d['C_I']], limit=15000)
    if s2 != 'ok' or outs2 != sorted([d['e'], d['bp'], d['c']]):
        return d, 'INC %s %s' % (s2, outs2)
    d = dict(d)
    d['dec'] = (Ts1, Te1)
    d['inc'] = (Ts2, Te2)
    d['env'] = list(nt.env)
    return d, 'ok'


def main():
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    di = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    nsim = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    t = time.time()
    recs = json.load(gzip.open(J3.POCKET_FILE, 'rt'))
    rec = recs[di]
    base = J3.build(rec)
    T = J4.targets(rec, base)
    print('design %d: OR controls %d, (RF_e, Rp) options %d, RF_c options %d; core records %d, U records %d, gates %d (%.0f s)' % (
        di, len(T), len(T[0][5]), len(T[0][4]), len(CORE), len(UPS), len(gates_sw()), time.time() - t), flush=True)
    jobs = [(ti, fi) for ti in range(len(T)) for fi in range(len(CORE))]
    found = []
    with Pool(min(20, os.cpu_count() or 1), initializer=init, initargs=({'rec': rec, 'targets': T},)) as pool:
        for k, res in enumerate(pool.imap_unordered(work, jobs, chunksize=1)):
            found.extend(res)
            if k % 200 == 0 or res:
                print('  jobs %d / %d, designs %d (%.0f s)' % (k + 1, len(jobs), len(found), time.time() - t), flush=True)
            if len(found) >= 2 * nsim:
                pool.terminate()
                break
    found.sort(key=lambda g: g['area'])
    with gzip.open('results/j6_geom_%d%s.json.gz' % (di, J3.SUFFIX), 'wt') as fh:
        json.dump(found, fh, separators=(',', ':'), default=list)
    print('complete geometric designs: %d (%.0f s)' % (len(found), time.time() - t), flush=True)
    for g in found[:10]:
        print('   area %d box %s core %d U %d w %s gate %s control lane %d frame %s m %d loop %s ux %d' % (
            g['area'], g['box'], g['core'], g['U'], g['w'], g['gate'], g['l3'], g['frame'], g['m'], g['jog'], g['ux']))
    jobs = []
    for g in found[:nsim]:
        g = dict(g)
        g.update({'a': base['a'], 'b': base['b'], 'bp': (SE, base['L'] + 6, g['T'])})
        jobs.append(g)
    good, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for d, s in pool.imap_unordered(simulate, jobs, chunksize=1):
            stats[s] = stats.get(s, 0) + 1
            print('   %s: area %d (%.0f s)' % (s, d['area'], time.time() - t), flush=True)
            if s == 'ok':
                good.append(d)
    good.sort(key=lambda d: d['area'])
    print('simulated %d: %s' % (len(jobs), stats))
    with gzip.open('results/j6_inc_%d%s.json.gz' % (di, J3.SUFFIX), 'wt') as fh:
        json.dump(good, fh, separators=(',', ':'), default=list)


if __name__ == '__main__':
    main()
