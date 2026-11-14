#!/usr/bin/env python3
"""J4 (R-24): the INC machinery of the register: ONE control glider C_I -> the three inputs of the
push part of the joint final stage (j3_stage.py):
    w   = the second (OR) control of Gb      (SE from the far NW; any repeatable catalogue line),
    s1  = the input of Rp                     (SE from the far NW; RF_e and Rp may slide),
    cin = the input of RF_c                   (NE from the SW).

Structure (that of PSG1, R-23, with new targets):
  C_I -> U    = verified fan-out of R-21 with outputs SE + SW (results/f2_roundtrip.json.gz),
                placed so that its SE output is the control C0' of the core;
         core = verified fan-out with outputs NW (G1, from K') + SW (G2, from S'), frame (0, X, Y, s):
                G2 (SW) -> R_w (SW -> SE)                              = w   exactly,
                G1 (NW) -> RF1' (NW -> SW, leg lane m) -> RF2' (SW -> SE) = s1  exactly,
         U's SW output -> R_y (SW -> SE, lane l3) -> R3a (SE -> NE)    = cin exactly.
Invariants (checked numerically): SW -> SE maps (lane, tau) to an output with tau + 4 lane =
tau_in - 4 lane_in + const; path 1 gives tau + 4 lane = tau_G1 - 4 m + const; SE -> NE and NE -> SE
keep tau (+ const).  Hence: the delay s of the core is fixed by w (and does not depend on X), m by
s1 (m = const + X + Y), and l3 depends only on (core record, U record, w): exact conditions are
solved per combination; the position (X, Y) of the core and the slide u of U are free and chosen by
the geometric filters (closest to the pull first).

Every candidate is simulated (net.Net, board then set simulator on the unbounded plane): with C0
exactly {a, b} leave, with C_I exactly {e, b', c}; the composite returns to its cycle.

Usage: j4_inc.py DESIGN [NSIM]      (DESIGN = index into results/j2_pocket_4.json.gz)
Output: results/j4_inc_DESIGN.json.gz, summary on stdout.
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import SE, SW, NE, NW, life
from reactions import shift_wl
import net
from net import Net, reflect_to, env_box, time_at, rf_point, box_dist, move_piece, asm_cross
from g2_pull import reflect
from g4_pull3 import seg_clear
import g7_push as g7
import j2_pocket as J
import j3_stage as J3

GAP = int(os.environ.get('J4_GAP', 6))
C0 = (SE, 41, 22)
FAR = 2500
CORE, UPS = g7.load_fanouts()


def rp_options(sol, rfe, gin):
    """All feeders Rp of RF_e (the tests of j2_pocket): [(jp, Rp, s1)]."""
    pieces = J.pull_pieces(sol)
    boxes = [env_box(p) for p in pieces] + [env_box(rfe)]
    pieces_g = [J.obst(p, J.GAP) for p in pieces] + [J.obst(rfe, J.GAP)]
    segs = J.segments(sol)
    t_in = time_at(gin, rf_point(rfe))
    out = []
    for jp in range(-300, 300):
        rp, gp = reflect_to(gin, SE, jp)
        tp = time_at(gin, rf_point(rp))
        if tp > t_in - 40:
            continue
        if min(box_dist(env_box(rp), b) for b in boxes) < J.GAP:
            continue
        if J.cells_hit(net.env_cells(rp), pieces_g):
            continue
        if not seg_clear(gin, tp + 30, t_in - 30, [J.obst(p, 3) for p in pieces]):
            continue
        tq = time_at(gp, rf_point(rp))
        if not seg_clear(gp, tq - FAR, tq - 30, [J.obst(p, 3) for p in pieces] + [J.obst(rfe, 3)]):
            continue
        if not all(seg_clear(g, ta, tb, [J.obst(rp, 3)]) for (nm, g, ta, tb) in segs):
            continue
        out.append((jp, rp, gp))
    return out


def rfc_options(sol, base, c, jc0):
    """Positions of RF_c near that of the stage (j3_stage.build) with its clearances: [(RF_c, cin)]."""
    pieces = base['pieces'][:8]
    boxes = [env_box(p) for p in pieces]
    segs = J.segments(sol)
    a, b = base['a'], base['b']
    e = (SE, base['L'] + J3.LE, 0)
    out = []
    for jc in range(jc0 - 6, jc0 + 30):
        q, ci = reflect_to(c, NE, jc)
        pt = rf_point(q)
        if min(box_dist(env_box(q), x) for x in boxes) < 6:
            continue
        ok = all(seg_clear(g, ta, tb, [J.obst(q, 3)]) for (nm, g, ta, tb) in segs if nm not in ('a', 'b'))
        ok = ok and seg_clear(a, time_at(a, pt) - 200, time_at(a, pt) + 200, [J.obst(q, 2)])
        ok = ok and seg_clear(b, time_at(b, pt) - 200, time_at(b, pt) + 200, [J.obst(q, 1)])
        ok = ok and seg_clear(e, time_at(e, pt) - 200, time_at(e, pt) + 200, [J.obst(q, 2)])
        tq = time_at(ci, pt)
        ok = ok and seg_clear(ci, tq - FAR, tq - 30, [J.obst(p, 3) for p in pieces])
        if ok:
            out.append((q, ci))
    return out


def targets(rec, base):
    """[(w, T, e, c, [(RF_c, cin)], [(RF_e, Rp, s1)])] for every OR control w of Gb."""
    sol = rec['sol']
    L = base['L']
    rfc0 = base['pieces'][8]
    jc0 = None
    for jc in range(-400, 400):
        q, ci = reflect_to((SE, L + J3.LC, 0), NE, jc)
        if q[1:4] == rfc0[1:4]:
            jc0 = jc
    out = []
    cache = {}
    for (w, oo) in J.or_controls(sol, base['pieces'][6:8]):
        r3 = reflect(oo, SE, L + 6)
        if r3 is None or tuple(r3[0][:4]) != tuple(sol['rfs'][2]):
            continue
        T = r3[1][2]
        e = (SE, L + J3.LE, T + J3.PUSH_E)
        c = (SE, L + J3.LC, T + J3.PUSH_C)
        rfcs = rfc_options(sol, base, c, jc0)
        opts = []
        for pk in rec['pocket']:
            rfe, gin = reflect_to(e, SW, pk['j'])
            if pk['j'] not in cache:
                cache[pk['j']] = [jp for (jp, _, _) in rp_options(sol, rfe, gin)]
            for jp in cache[pk['j']]:
                rp, s1 = reflect_to(gin, SE, jp)
                opts.append((rfe, rp, s1))
        out.append((w, T, e, c, rfcs, opts))
    return out


def core_exact(fc, w, s1, X, Y):
    """Core frame (0, X, Y, s) with R_w(G2) = w and path 1 (G1) = s1 exactly, or None."""
    g2 = shift_wl(fc['G2'], X, Y, 0)
    r = reflect(g2, SE, w[1])
    if r is None:
        return None
    s = w[2] - r[1][2]
    g2 = shift_wl(fc['G2'], X, Y, s)
    rw = reflect(g2, SE, w[1])
    assert rw[1] == w
    g1 = shift_wl(fc['G1'], X, Y, s)
    # I(m) = tau + 4 L after path 1 is linear in m with slope -4; find m
    for m0 in (0, 1):
        ra = reflect(g1, SW, m0)
        if ra is None:
            continue
        rb = reflect(ra[1], SE, s1[1])
        if rb is None:
            continue
        num = rb[1][2] - s1[2]
        if num % 4:
            return None
        m = m0 + num // 4
        r1 = reflect(g1, SW, m)
        if r1 is None:
            return None
        r2 = reflect(r1[1], SE, s1[1])
        if r2 is None or r2[1] != s1:
            return None
        return {'frame': (0, X, Y, s), 'g1': g1, 'g2': g2, 'leg': r1[1], 'm': m,
                'RF1': ('rf',) + tuple(r1[0]), 'RF2': ('rf',) + tuple(r2[0]), 'Rw': ('rf',) + tuple(rw[0])}
    return None


def obs(ps, gap=3):
    return [J.obst(p, gap) for p in ps]


def core_geometry(fc, w, s1, X, Y, fixed, fixed_boxes, t_gb, t_rp, pull_segs):
    cx = core_exact(fc, w, s1, X, Y)
    if cx is None:
        return None
    k, X, Y, s = cx['frame']
    Sc = ('asm', 0, X, Y, s % 30)
    Kc = move_piece(fc['K'], X, Y, s)
    new = [Sc, Kc, cx['RF1'], cx['RF2'], cx['Rw']]
    nb = [env_box(p) for p in new]
    for i, b in enumerate(nb):
        if min(box_dist(b, x) for x in fixed_boxes) < GAP:
            return None
        for j in range(i):
            if box_dist(b, nb[j]) < GAP and not (i == 1 and j == 0):
                return None
    # causality
    g1, g2, leg = cx['g1'], cx['g2'], cx['leg']
    t_k = time_at(g1, asm_cross(Kc)) + 100
    t1 = time_at(g1, rf_point(cx['RF1']))
    t2 = time_at(leg, rf_point(cx['RF2']))
    t_s1 = time_at(s1, rf_point(cx['RF2']))
    t_s = time_at(g2, asm_cross(Sc)) + 60
    t_w = time_at(g2, rf_point(cx['Rw']))
    t_w2 = time_at(w, rf_point(cx['Rw']))
    if not (t1 > t_k + 40 and t_s1 < t_rp - 60 and t_w > t_s + 40 and t_w2 < t_gb - 150):
        return None
    allp = fixed + new
    excl = lambda ex: obs([p for p in allp if p not in ex])
    checks = [(g1, t_k, t1 - 30, excl([Kc, cx['RF1']])),
              (leg, time_at(leg, rf_point(cx['RF1'])) + 30, t2 - 30, excl([cx['RF1'], cx['RF2']])),
              (s1, t_s1 + 30, t_rp - 30, excl([cx['RF2'], fixed[7]])),
              (g2, t_s, t_w - 30, excl([Sc, cx['Rw']])),
              (w, t_w2 + 30, t_gb - 120, excl([cx['Rw'], fixed[2]]))]
    for (g, ta, tb, ob) in checks:
        if not seg_clear(g, ta, tb, ob):
            return None
    # the DEC machinery (its control from the far NW included) must not meet the new pieces
    for (nm, g, ta, tb) in pull_segs:
        if not seg_clear(g, ta, tb, obs(new)):
            return None
    return {'cx': cx, 'pieces': new}


def u_geometry(fu, core, l3, cin, rfc, fixed, ux):
    cx = core['cx']
    k, X, Y, s = cx['frame']
    ctrl = shift_wl(C0, X, Y, s)                  # control of the core
    g = fu['G1']
    vx = ux
    vy = vx - (ctrl[1] - g[1])
    su = ctrl[2] - g[2] + 4 * vx
    assert shift_wl(g, vx, vy, su) == ctrl
    Su = ('asm', 0, vx, vy, su % 30)
    Ku = move_piece(fu['K'], vx, vy, su)
    cont = shift_wl(fu['G2'], vx, vy, su)
    cI = shift_wl(C0, vx, vy, su)
    ry = reflect(cont, SE, l3)
    if ry is None:
        return None
    r3a = reflect(ry[1], NE, cin[1])
    if r3a is None or r3a[1] != cin:
        return None
    Ry, R3 = ('rf',) + tuple(ry[0]), ('rf',) + tuple(r3a[0])
    s3 = ry[1]
    new = [Su, Ku, Ry, R3]
    others = fixed + core['pieces']
    ob = [env_box(p) for p in others]
    nb = [env_box(p) for p in new]
    for i, b in enumerate(nb):
        if min(box_dist(b, x) for x in ob) < GAP:
            return None
        for j in range(i):
            if box_dist(b, nb[j]) < GAP and not (i == 1 and j == 0):
                return None
    t_c = time_at(cont, asm_cross(Su)) + 60
    t_y = time_at(cont, rf_point(Ry))
    t_y3 = time_at(s3, rf_point(Ry))
    t_3 = time_at(s3, rf_point(R3))
    t_3c = time_at(cin, rf_point(R3))
    t_rfc = time_at(cin, rf_point(rfc))
    if not (t_y > t_c + 40 and t_3 > t_y3 + 60 and t_rfc > t_3c + 60):
        return None
    allp = others + new
    excl = lambda ex: obs([p for p in allp if p not in ex])
    Sc = core['pieces'][0]
    tI = time_at(cI, asm_cross(Su))
    checks = [(cont, t_c, t_y - 30, excl([Su, Ku, Ry])),
              (s3, t_y3 + 30, t_3 - 30, excl([Ry, R3])),
              (cin, t_3c + 30, t_rfc - 30, excl([R3, rfc])),
              (cI, tI - FAR, tI - 100, excl([Su, Ku])),
              (ctrl, time_at(ctrl, asm_cross(Ku)) + 60, time_at(ctrl, asm_cross(Sc)) - 100,
               excl([Su, Ku, Sc, core['pieces'][1]]))]
    for (g, ta, tb, o) in checks:
        if not seg_clear(g, ta, tb, o):
            return None
    return {'pieces': new, 'C_I': cI, 'l3': l3, 'ux': ux}


def l3_of(fu, core, cin):
    """The lane l3 for which U's SW output, turned SE by R_y and NE by R3a, is exactly cin."""
    cx = core['cx']
    k, X, Y, s = cx['frame']
    ctrl = shift_wl(C0, X, Y, s)
    g = fu['G1']
    vx = -200
    vy = vx - (ctrl[1] - g[1])
    su = ctrl[2] - g[2] + 4 * vx
    cont = shift_wl(fu['G2'], vx, vy, su)
    for l0 in range(-300, -308, -1):
        ry = reflect(cont, SE, l0)
        if ry is None:
            continue
        r3 = reflect(ry[1], NE, cin[1])
        if r3 is None:
            continue
        d = r3[1][2] - cin[2]            # tau_out = I - 4 l3: d = -4 (l3 - l0)
        if d % 8:
            continue
        l3 = l0 + d // 4
        ry = reflect(cont, SE, l3)
        if ry is None:
            continue
        r3 = reflect(ry[1], NE, cin[1])
        if r3 is not None and r3[1] == cin:
            return l3
    return None


def work(job):
    di, ti, fi = job
    rec, base, T = _CTX['rec'], _CTX['base'], _CTX['targets'][ti]
    sol = rec['sol']
    w, Tb, e, c, rfcs, opts = T
    fc = CORE[fi]
    pull = J.pull_pieces(sol)
    pull_segs = J.segments(sol)
    gb = tuple(sol['gb'])
    kx, ky = life.sym_apply(gb[0], (45, 31))
    t_gb = time_at(w, (kx + gb[1], ky + gb[2]))
    results = []
    for (rfe, rp, s1) in opts:
        fixed = pull + [rfe, rp]
        fixed_boxes = [env_box(p) for p in fixed]
        t_rp = time_at(s1, rf_point(rp))
        # parity / divisibility test at one point of each parity of X + Y
        if core_exact(fc, w, s1, -200, -400) is None and core_exact(fc, w, s1, -201, -400) is None:
            continue
        found = 0
        for Y in range(-60, -700, -3):
            for d in range(-60, 200, 1):
                X = Y + d
                cg = core_geometry(fc, w, s1, X, Y, fixed, fixed_boxes, t_gb, t_rp, pull_segs)
                if cg is None:
                    continue
                for ui, fu in enumerate(UPS):
                  for (rfc, cin) in rfcs:
                    if min(box_dist(env_box(rfc), env_box(p)) for p in cg['pieces']) < GAP:
                        continue
                    l3 = l3_of(fu, cg, cin)
                    if l3 is None or not (-900 <= l3 <= -150):
                        continue
                    for ux in range(-40, -700, -2):
                        ug = u_geometry(fu, cg, l3, cin, rfc, fixed + [rfc], ux)
                        if ug is None:
                            continue
                        allp = fixed + [rfc] + cg['pieces'] + ug['pieces']
                        bs = [env_box(p) for p in allp]
                        bx = (min(b[0] for b in bs), min(b[1] for b in bs), max(b[2] for b in bs), max(b[3] for b in bs))
                        results.append({'w': w, 'T': Tb, 'e': e, 'c': c, 'cin': cin, 's1': s1, 'core': fi, 'U': ui,
                                        'frame': cg['cx']['frame'], 'm': cg['cx']['m'], 'l3': l3, 'ux': ux,
                                        'pieces': allp, 'C_I': ug['C_I'], 'box': bx,
                                        'area': (bx[2] - bx[0] + 1) * (bx[3] - bx[1] + 1)})
                        break
                    if len(results) > found:
                        break
                  if len(results) > found:
                    break
                if len(results) > found:
                    found = len(results)
                    break
            if found:
                break
    return results


_CTX = {}


def init(ctx):
    _CTX.update(ctx)


NAMES = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3', 'RFe', 'Rp', 'RFc', 'Sc', 'Kc', 'RF1c', 'RF2c', 'Rw', 'Su', 'Ku', 'Ry', 'R3a']


def simulate(d):
    try:
        nt = Net(d['pieces'], NAMES)
    except (AssertionError, ValueError):
        return d, 'not periodic/overlap'
    s1, outs1, Ts1, Te1 = nt.react([C0], limit=4000)
    if s1 != 'ok' or outs1 != sorted([d['a'], d['b']]):
        return d, 'DEC %s' % s1
    s2, outs2, Ts2, Te2 = nt.react([d['C_I']], limit=12000)
    if s2 != 'ok' or outs2 != sorted([d['e'], d['bp'], d['c']]):
        return d, 'INC %s %s' % (s2, outs2)
    d = dict(d)
    d['dec'] = (Ts1, Te1)
    d['inc'] = (Ts2, Te2)
    d['env'] = list(nt.env)
    return d, 'ok'


def main():
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    di = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    nsim = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    t = time.time()
    recs = json.load(gzip.open(J3.POCKET_FILE, 'rt'))
    rec = recs[di]
    base = J3.build(rec)
    T = targets(rec, base)
    print('design %d: OR controls %d, (RF_e, Rp) options %d; core records %d, U records %d (%.0f s)' % (
        di, len(T), len(T[0][5]) if T else 0, len(CORE), len(UPS), time.time() - t), flush=True)
    jobs = [(di, ti, fi) for ti in range(len(T)) for fi in range(len(CORE))]
    found = []
    with Pool(min(20, os.cpu_count() or 1), initializer=init, initargs=({'rec': rec, 'base': base, 'targets': T},)) as pool:
        for k, res in enumerate(pool.imap_unordered(work, jobs, chunksize=1)):
            found.extend(res)
            if k % 100 == 0:
                print('  jobs %d / %d, designs %d (%.0f s)' % (k, len(jobs), len(found), time.time() - t), flush=True)
    found.sort(key=lambda g: g['area'])
    print('complete geometric designs: %d (%.0f s)' % (len(found), time.time() - t), flush=True)
    for g in found[:10]:
        print('   area %d box %s core %d U %d w %s l3 %d frame %s ux %d' % (g['area'], g['box'], g['core'], g['U'], g['w'], g['l3'], g['frame'], g['ux']))
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
    with gzip.open('results/j4_inc_%d.json.gz' % di, 'wt') as fh:
        json.dump(good, fh, separators=(',', ':'), default=list)


if __name__ == '__main__':
    main()
