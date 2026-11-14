#!/usr/bin/env python3
"""J5 (R-24): the INC machinery, second variant (the first, j4_inc.py, fails by parity: the lane
of RF_c's input cannot be reached from U's SW output by SW -> SE -> NE).

  C_I -> U    = verified fan-out with outputs SE + SW (results/f2_roundtrip.json.gz), placed so that
                its SE output is the control of the core; its SW output -> R_w (SW -> SE) = w,
                the second (OR) control of Gb;
         core = verified fan-out with outputs NW (G1, from K') + SW (G2, from S'), frame (0, X, Y, s):
                G1 (NW) -> RF1' (NW -> SW, leg lane m) -> RF2' (SW -> SE)  = s1 (input of Rp),
                G2 (SW) -> R_y (SW -> SE, lane l3) -> R3a (SE -> NE)       = cin (input of RF_c).
Exactness: the delay s is fixed by w (through U), m by s1 (a congruence mod 4), l3 by cin (mod 8
and the parity of the NE lane); (X, Y) and the slide u of U are free and chosen by the geometric
filters (nearest first).  Then simulation as in j4_inc.py.

Usage: j5_inc.py DESIGN [NSIM]      Output: results/j5_inc_DESIGN.json.gz, summary on stdout.
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import SE, SW, NE, NW, life
from reactions import shift_wl
from net import Net, env_box, time_at, rf_point, box_dist, move_piece, asm_cross
from g2_pull import reflect
from g4_pull3 import seg_clear
import j2_pocket as J
import j3_stage as J3
import j4_inc as J4
from j4_inc import CORE, UPS, C0, FAR, obs

GAP = int(os.environ.get('J5_GAP', 5))
UX0 = -200


def u_frame(fu, ctrl, ux):
    g = fu['G1']
    vy = ux - (ctrl[1] - g[1])
    su = ctrl[2] - g[2] + 4 * ux
    assert shift_wl(g, ux, vy, su) == ctrl
    return ux, vy, su


def l3_solve(g2, cin):
    for l0 in range(-300, -308, -1):
        ry = reflect(g2, SE, l0)
        if ry is None:
            continue
        r3 = reflect(ry[1], NE, cin[1])
        if r3 is None:
            continue
        d = r3[1][2] - cin[2]
        if d % 8:
            return None
        l3 = l0 + d // 4
        ry = reflect(g2, SE, l3)
        if ry is None:
            return None
        r3 = reflect(ry[1], NE, cin[1])
        if r3 is not None and r3[1] == cin:
            return l3, ('rf',) + tuple(ry[0]), ry[1], ('rf',) + tuple(r3[0])
        return None
    return None


def exact(fc, fu, w, s1, cin, X, Y):
    ctrl0 = shift_wl(C0, X, Y, 0)
    vx, vy, su = u_frame(fu, ctrl0, UX0)
    cont0 = shift_wl(fu['G2'], vx, vy, su)
    rw = reflect(cont0, SE, w[1])
    if rw is None:
        return None
    s = w[2] - rw[1][2]
    g1 = shift_wl(fc['G1'], X, Y, s)
    g2 = shift_wl(fc['G2'], X, Y, s)
    m = None
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
        break
    if m is None:
        return None
    r1 = reflect(g1, SW, m)
    if r1 is None:
        return None
    r2 = reflect(r1[1], SE, s1[1])
    if r2 is None or r2[1] != s1:
        return None
    y = l3_solve(g2, cin)
    if y is None:
        return None
    l3, Ry, s3, R3a = y
    return {'frame': (0, X, Y, s), 'g1': g1, 'g2': g2, 'leg': r1[1], 'm': m, 'l3': l3, 's3': s3,
            'RF1': ('rf',) + tuple(r1[0]), 'RF2': ('rf',) + tuple(r2[0]), 'Ry': Ry, 'R3a': R3a,
            'ctrl': shift_wl(C0, X, Y, s)}


def sep_ok(new, others, gap):
    nb = [env_box(p) for p in new]
    ob = [env_box(p) for p in others]
    for i, b in enumerate(nb):
        if ob and min(box_dist(b, x) for x in ob) < gap:
            return False
        for j in range(i):
            if box_dist(b, nb[j]) < gap and not (new[i][0] == new[j][0] == 'asm' and abs(i - j) == 1 and i % 2 == 1 and j == i - 1):
                return False
    return True


def geometry(fc, fu, w, s1, cin, rfc, X, Y, fixed, t_gb, t_rp, pull_segs):
    cx = exact(fc, fu, w, s1, cin, X, Y)
    if cx is None:
        return None
    k, X, Y, s = cx['frame']
    Sc = ('asm', 0, X, Y, s % 30)
    Kc = move_piece(fc['K'], X, Y, s)
    core = [Sc, Kc, cx['RF1'], cx['RF2'], cx['Ry'], cx['R3a']]
    if not sep_ok(core, fixed + [rfc], GAP):
        return None
    g1, g2, leg, s3 = cx['g1'], cx['g2'], cx['leg'], cx['s3']
    t_k = time_at(g1, asm_cross(Kc)) + 100
    t1 = time_at(g1, rf_point(cx['RF1']))
    t2 = time_at(leg, rf_point(cx['RF2']))
    t_s1 = time_at(s1, rf_point(cx['RF2']))
    t_s = time_at(g2, asm_cross(Sc)) + 60
    t_y = time_at(g2, rf_point(cx['Ry']))
    t_y3 = time_at(s3, rf_point(cx['Ry']))
    t_3 = time_at(s3, rf_point(cx['R3a']))
    t_3c = time_at(cin, rf_point(cx['R3a']))
    t_rfc = time_at(cin, rf_point(rfc))
    if not (t1 > t_k + 40 and t_s1 < t_rp - 60 and t_y > t_s + 40 and t_3 > t_y3 + 60 and t_rfc > t_3c + 60):
        return None
    allp = fixed + [rfc] + core
    ex = lambda e_: obs([p for p in allp if p not in e_])
    checks = [(g1, t_k, t1 - 30, ex([Kc, cx['RF1']])),
              (leg, time_at(leg, rf_point(cx['RF1'])) + 30, t2 - 30, ex([cx['RF1'], cx['RF2']])),
              (s1, t_s1 + 30, t_rp - 30, ex([cx['RF2'], fixed[7]])),
              (g2, t_s, t_y - 30, ex([Sc, cx['Ry']])),
              (s3, t_y3 + 30, t_3 - 30, ex([cx['Ry'], cx['R3a']])),
              (cin, t_3c + 30, t_rfc - 30, ex([cx['R3a'], rfc]))]
    for (g, ta, tb, o) in checks:
        if not seg_clear(g, ta, tb, o):
            return None
    for (nm, g, ta, tb) in pull_segs:
        if not seg_clear(g, ta, tb, obs(core)):
            return None
    # U along the control of the core
    ctrl = cx['ctrl']
    for ux in range(-30, -700, -2):
        vx, vy, su = u_frame(fu, ctrl, ux)
        Su = ('asm', 0, vx, vy, su % 30)
        Ku = move_piece(fu['K'], vx, vy, su)
        cont = shift_wl(fu['G2'], vx, vy, su)
        rw = reflect(cont, SE, w[1])
        if rw is None or rw[1] != w:
            continue
        Rw = ('rf',) + tuple(rw[0])
        unew = [Su, Ku, Rw]
        if not sep_ok(unew, allp, GAP):
            continue
        cI = shift_wl(C0, vx, vy, su)
        t_c = time_at(cont, asm_cross(Su)) + 60
        t_w = time_at(cont, rf_point(Rw))
        t_w2 = time_at(w, rf_point(Rw))
        if not (t_w > t_c + 40 and t_w2 < t_gb - 150):
            continue
        all2 = allp + unew
        ex2 = lambda e_: obs([p for p in all2 if p not in e_])
        tI = time_at(cI, asm_cross(Su))
        c2 = [(cont, t_c, t_w - 30, ex2([Su, Ku, Rw])),
              (w, t_w2 + 30, t_gb - 120, ex2([Rw, fixed[2]])),
              (cI, tI - FAR, tI - 100, ex2([Su, Ku])),
              (ctrl, time_at(ctrl, asm_cross(Ku)) + 60, time_at(ctrl, asm_cross(Sc)) - 100, ex2([Su, Ku, Sc, Kc]))]
        if not all(seg_clear(g, ta, tb, o) for (g, ta, tb, o) in c2):
            continue
        if not all(seg_clear(g, ta, tb, obs(unew)) for (nm, g, ta, tb) in pull_segs):
            continue
        # the INC flights of the core must not meet U
        c3 = [(g1, t_k, t1 - 30), (leg, time_at(leg, rf_point(cx['RF1'])) + 30, t2 - 30), (s1, t_s1 + 30, t_rp - 30),
              (g2, t_s, t_y - 30), (s3, t_y3 + 30, t_3 - 30), (cin, t_3c + 30, t_rfc - 30)]
        if not all(seg_clear(g, ta, tb, obs(unew)) for (g, ta, tb) in c3):
            continue
        bs = [env_box(p) for p in all2]
        bx = (min(b[0] for b in bs), min(b[1] for b in bs), max(b[2] for b in bs), max(b[3] for b in bs))
        return {'pieces': all2, 'C_I': cI, 'frame': cx['frame'], 'm': cx['m'], 'l3': cx['l3'], 'ux': ux,
                'box': bx, 'area': (bx[2] - bx[0] + 1) * (bx[3] - bx[1] + 1)}
    return None


_CTX = {}


def init(ctx):
    _CTX.update(ctx)


def work(job):
    ti, fi, ui = job
    rec, T = _CTX['rec'], _CTX['targets'][ti]
    sol = rec['sol']
    w, Tb, e, c, rfcs, opts = T
    fc, fu = CORE[fi], UPS[ui]
    pull = J.pull_pieces(sol)
    pull_segs = J.segments(sol)
    gb = tuple(sol['gb'])
    kx, ky = life.sym_apply(gb[0], (45, 31))
    t_gb = time_at(w, (kx + gb[1], ky + gb[2]))
    out = []
    for (rfe, rp, s1) in opts:
        fixed = pull + [rfe, rp]
        t_rp = time_at(s1, rf_point(rp))
        for (rfc, cin) in rfcs:
            classes = [(a, b) for a in range(4) for b in range(4) if exact(fc, fu, w, s1, cin, -400 + a, -400 + b)]
            if not classes:
                continue
            hit = None
            for Y in range(-60, -760, -1):
                for d in range(-80, 220):
                    X = Y + d
                    if ((X % 4), (Y % 4)) not in classes:
                        continue
                    g = geometry(fc, fu, w, s1, cin, rfc, X, Y, fixed, t_gb, t_rp, pull_segs)
                    if g:
                        hit = g
                        break
                if hit:
                    break
            if hit:
                hit.update({'w': w, 'T': Tb, 'e': e, 'c': c, 's1': s1, 'cin': cin, 'core': fi, 'U': ui})
                out.append(hit)
                return out
    return out


NAMES = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3', 'RFe', 'Rp', 'RFc', 'Sc', 'Kc', 'RF1c', 'RF2c', 'Ry', 'R3a', 'Su', 'Ku', 'Rw']


def simulate(d):
    try:
        nt = Net(d['pieces'], NAMES)
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
    print('design %d: OR controls %d, (RF_e, Rp) options %d, RF_c options %d; core records %d, U records %d (%.0f s)' % (
        di, len(T), len(T[0][5]), len(T[0][4]), len(CORE), len(UPS), time.time() - t), flush=True)
    jobs = [(ti, fi, ui) for ti in range(len(T)) for fi in range(len(CORE)) for ui in range(len(UPS))]
    print('combinations (w, core, U): %d (%.0f s)' % (len(jobs), time.time() - t), flush=True)
    found = []
    with Pool(min(20, os.cpu_count() or 1), initializer=init, initargs=({'rec': rec, 'targets': T},)) as pool:
        for k, res in enumerate(pool.imap_unordered(work, jobs, chunksize=1)):
            found.extend(res)
            if k % 5000 == 0 or res:
                print('  jobs %d / %d, designs %d (%.0f s)' % (k + 1, len(jobs), len(found), time.time() - t), flush=True)
            if len(found) >= 4 * nsim:
                pool.terminate()
                break
    found.sort(key=lambda g: g['area'])
    print('complete geometric designs: %d (%.0f s)' % (len(found), time.time() - t), flush=True)
    for g in found[:10]:
        print('   area %d box %s core %d U %d w %s l3 %d frame %s m %d ux %d' % (g['area'], g['box'], g['core'], g['U'], g['w'], g['l3'], g['frame'], g['m'], g['ux']))
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
    with gzip.open('results/j5_inc_%d.json.gz' % di, 'wt') as fh:
        json.dump(good, fh, separators=(',', ':'), default=list)


if __name__ == '__main__':
    main()
