#!/usr/bin/env python3
"""J2 (R-24): pull-salvo generators of PG1 type (g4_pull3 enumeration) that leave a POCKET for the
push glider e of a joint register.

Joint final stage found by j1_lanes.py (with sharing, R-24 section 2): pull {a, b} = pullSalvo
(a on lane L from path 1 by RF2, R-type; b on L + 6 by RF3 from the gate output o, L-type) and a push
{e, b', c} that SHARES b (b' leaves the same RF3, released by a second control glider of the same
gate Gb: an OR gate), with e on lane L - 4 (push (5, -47), (11, -25), (-5, 0)) or L - 5 (push
(5, -51), (12, -24), (-6, 0)) inserted by an R-type reflector RF_e BETWEEN RF2 and RF3, and c on
L + 12 / L + 13 inserted by an L-type reflector RF_c downstream of RF3.  In PG1 itself the pocket
between RF2 and the path of o is too narrow (R-24 section 3).

This script runs the exact enumeration of g4_pull3 (3.8 M solutions), keeps those with o flying NE,
path 1 giving a, and room between RF2 and o (cheap test), and checks in order of increasing box:
  * the pull itself: g4_pull3.plausible (causal, clear flight segments, no overlap);
  * RF_e: an R-type copy of RF0 emitting e, downstream of RF2 and upstream of RF3, envelope >= GAP
    from all pieces, clear of all flight segments (a: 5 x 5 box of the glider >= 1, i.e. cells >= 2, inherent; others >= 3), e clear of all
    pieces downstream;
  * its feeder Rp: a copy of RF0 turning an SE glider from the far NW into the SW input of RF_e,
    with Rp's envelope >= GAP from everything and both of its flight segments clear (>= 3);
  * an OR control of Gb from the far NW (an SE world line from the catalogue releasing the same
    glider o), clear of all pieces (>= 3).
Output: results/j2_pocket.json.gz (candidates), summary on stdout.

Usage: j2_pocket.py [NWANT] [LE_OFFSET]      (LE_OFFSET 4 or 5)
       j2_pocket.py pg1                         (the test for the certified PG1 itself)
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

import g4_pull3 as g4
from common import life, SE, SW, NE, NW
from machine import load_catalog, wl_map
from net import env_box, reflect_to, time_at, rf_point, box_dist
from g2_pull import reflect
from g4_pull3 import grown, seg_clear, FANOUT, G1, G2

GAP = 4
_CAT = None


def catalog_or():
    """Repeatable gate records from infinity with a single output glider."""
    global _CAT
    if _CAT is None:
        _CAT = [r for r in load_catalog() if r['from_infinity'] and r['repeat'] and len(r['outs']) == 1]
    return _CAT


def or_controls(sol, extra, dirs=(SE,), far=2500):
    """Second control gliders of the gate Gb of `sol` (an OR gate): repeatable control world lines
    of the catalogue (directions `dirs`) whose released glider is the glider o of the pull, up to a
    multiple of 30 generations, and whose path from far away is clear (>= 3) of all pieces of the pull
    and of the pieces `extra`.  Returns [(w, o')]."""
    gb = tuple(sol['gb'])
    o = sol['gb_out']
    kx, ky = life.sym_apply(gb[0], (45, 31))
    cross_g = (kx + gb[1], ky + gb[2])
    pieces = pull_pieces(sol)
    allp = pieces[:2] + pieces[3:] + list(extra)
    out = []
    for r in catalog_or():
        w = wl_map(r['wl'], gb)
        if w[0] not in dirs:
            continue
        oo = wl_map(r['outs'][0][0], gb)
        if oo[0] != tuple(o[0]) or oo[1] != o[1] or (oo[2] - o[2]) % 30:
            continue
        tc = time_at(w, cross_g)
        if seg_clear(w, tc - far, tc - 120, [obst(p, 3) for p in allp]):
            out.append((w, oo))
    return out


def pull_pieces(sol):
    rf1, rf2, rf3 = [tuple(r) for r in sol['rfs']]
    return [('asm', 0, 0, 0, 0), ('asm',) + FANOUT, ('asm',) + tuple(sol['gb']),
            ('rf',) + rf1, ('rf',) + rf2, ('rf',) + rf3]


def obst(p, gap):
    return (grown(p[0], p[1], gap), (p[2], p[3]))


def cells_hit(cells, obstacles):
    for gs, (ox, oy) in obstacles:
        for (x, y) in cells:
            if (x - ox, y - oy) in gs:
                return True
    return False


def piece_cells_env(p):
    from net import env_cells
    return env_cells(p)


def segments(sol):
    """Flight segments of the pull: (name, glider, t_a, t_b)."""
    rf1, rf2, rf3 = [tuple(r) for r in sol['rfs']]
    o = tuple(sol['gb_out'])
    o = (tuple(o[0]), o[1], o[2])
    leg = reflect(G1, SW, g4._lane_of_leg(rf1))[1]
    a, b = tuple(sol['a']), tuple(sol['b'])
    a = (tuple(a[0]), a[1], a[2])
    b = (tuple(b[0]), b[1], b[2])
    c_rf1 = rf_point(('rf',) + rf1)
    c_rf2 = rf_point(('rf',) + rf2)
    c_rf3 = rf_point(('rf',) + rf3)
    gb = tuple(sol['gb'])
    kx, ky = life.sym_apply(gb[0], (45, 31))
    cross_g = (kx + gb[1], ky + gb[2])
    t_r1 = time_at(G1, c_rf1)
    t_r2 = time_at(leg, c_rf2)
    t_r3 = time_at(o, c_rf3)
    return [('G1', G1, time_at(G1, g4.KCROSS) + 100, t_r1 - 30),
            ('leg', leg, t_r1 + 30, t_r2 - 30),
            ('a', a, t_r2 + 30, t_r2 + 2400),
            ('G2', G2, time_at(G2, (40, 36)), time_at(G2, cross_g) + 10),
            ('o', o, time_at(o, cross_g) + 40, t_r3 - 30),
            ('b', b, t_r3 + 30, t_r3 + 2400),
            ('C0', g4.C0, time_at(g4.C0, (0, 0)) - 1500, time_at(g4.C0, (0, 0)) - 20)]


def pocket(sol, le_off, want_rp=3):
    """Feasible (RF_e, Rp, OR control) combinations for the pull `sol`."""
    pieces = pull_pieces(sol)
    names = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3']
    a = sol['a']
    L = a[1]
    Le = L - le_off
    boxes = [env_box(p) for p in pieces]
    rf2b, rf3b = boxes[4], boxes[5]
    segs = segments(sol)
    s_rf3 = (rf3b[0] + rf3b[2] + rf3b[1] + rf3b[3]) / 2
    pieces_g = [obst(p, GAP) for p in pieces]
    out = []
    for j in range(-260, 260):
        rfe, gin = reflect_to((SE, Le, 0), SW, j)
        be = env_box(rfe)
        se = (be[0] + be[2] + be[1] + be[3]) / 2
        if se > s_rf3 - 6:
            continue
        if min(box_dist(be, b) for b in boxes) < GAP:
            continue
        ecells = piece_cells_env(rfe)
        if cells_hit(ecells, pieces_g):
            continue
        ok = True
        for (nm, g, ta, tb) in segs:
            if not seg_clear(g, ta, tb, [obst(rfe, 1 if nm == 'a' else 3)]):
                ok = False
                break
        if not ok:
            continue
        e = (SE, Le, 0)
        te = time_at(e, rf_point(rfe))
        if not seg_clear(e, te + 30, te + 2400, [obst(p, 3) for p in pieces]):
            continue
        # feeder Rp on the input line of RF_e
        t_in = time_at(gin, rf_point(rfe))
        rps = []
        for jp in range(-300, 300):
            rp, gp = reflect_to(gin, SE, jp)
            tp = time_at(gin, rf_point(rp))
            if tp > t_in - 40:
                continue
            bp = env_box(rp)
            if min(box_dist(bp, b) for b in boxes + [be]) < GAP:
                continue
            pcells = piece_cells_env(rp)
            if cells_hit(pcells, pieces_g + [obst(rfe, GAP)]):
                continue
            if not seg_clear(gin, tp + 30, t_in - 30, [obst(p, 3) for p in pieces]):
                continue
            tq = time_at(gp, rf_point(rp))
            if not seg_clear(gp, tq - 2500, tq - 30, [obst(p, 3) for p in pieces] + [obst(rfe, 3)]):
                continue
            ok = True
            for (nm, g, ta, tb) in segs:
                if not seg_clear(g, ta, tb, [obst(rp, 3)]):
                    ok = False
                    break
            if not ok:
                continue
            rps.append((jp, rp, gp))
            if len(rps) >= want_rp:
                break
        if not rps:
            continue
        # OR controls of Gb from the far NW (SE world lines), clear of all pieces + RF_e + Rp
        ors = or_controls(sol, [rfe, rps[0][1]])
        if not ors:
            continue
        out.append({'j': j, 'rfe': rfe, 'gin': gin, 'rps': rps, 'ors': ors[:12], 'n_or': len(ors)})
    return out


def check(args):
    sol, le_off = args
    if not g4.plausible(sol):
        return sol, None
    return sol, pocket(sol, le_off)


def enumerate_pulls():
    recs = load_catalog()
    jobs = []
    for r in recs:
        if r['kind'] == 'gate' and r['from_infinity'] and len(r['repeat']) == 3:
            (ow, nm) = r['outs'][0]
            for k in range(8):
                if life.sym_apply(k, r['d']) == SW:
                    jobs.append((r['d'], r['lane'], r['tau'], ow[0], ow[1], ow[2], k))
    sols = []
    with Pool(min(20, os.cpu_count() or 1), initializer=g4.init) as pool:
        for ss in pool.imap_unordered(g4.work, jobs, chunksize=4):
            sols.extend(ss)
    return sols


def pg1_check():
    """The certified PG1 itself: is there any position for RF_e (without its feeder)?"""
    sol = {'gb': [2, 4, 121, 29], 'rfs': [[5, -32, 18, 0], [7, -45, 67, 13], [2, -4, 73, 0]],
           'a': [list(SE), -97, 1116], 'b': [list(SE), -91, 1087], 'gb_out': [list(NE), -46, 1092]}
    pieces = pull_pieces(sol)
    segs = segments(sol)
    boxes = [env_box(p) for p in pieces]
    s_rf3 = (boxes[5][0] + boxes[5][2] + boxes[5][1] + boxes[5][3]) / 2
    for le_off in (4, 5):
        stats = {}
        for j in range(-260, 260):
            rfe, gin = reflect_to((SE, -97 - le_off, 0), SW, j)
            be = env_box(rfe)
            if (be[0] + be[2] + be[1] + be[3]) / 2 > s_rf3 - 6:
                why = 'downstream of RF3'
            elif min(box_dist(be, b) for b in boxes) < GAP:
                why = 'box of a piece within %d' % GAP
            elif cells_hit(piece_cells_env(rfe), [obst(p, GAP) for p in pieces]):
                why = 'envelope of a piece within %d' % GAP
            else:
                bad = [nm for (nm, g, ta, tb) in segs if not seg_clear(g, ta, tb, [obst(rfe, 1 if nm == 'a' else 3)])]
                if bad:
                    why = 'on the path of ' + bad[0]
                else:
                    te = time_at((SE, -97 - le_off, 0), rf_point(rfe))
                    why = 'ok' if seg_clear((SE, -97 - le_off, 0), te + 30, te + 2400, [obst(p, 3) for p in pieces]) else 'e meets a piece (RF2)'
            stats[why] = stats.get(why, 0) + 1
        print('PG1, e on lane a - %d: positions j = -260 .. 259 of RF_e: %s' % (le_off, stats))


def main():
    if len(sys.argv) > 1 and sys.argv[1] == 'pg1':
        pg1_check()
        return
    nwant = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    le_off = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    t = time.time()
    g4.init()
    sols = enumerate_pulls()
    print('g4 enumeration: %d exact solutions (%.0f s)' % (len(sols), time.time() - t))
    keep = []
    for s in sols:
        o = s['gb_out']
        if tuple(o[0]) != NE:
            continue
        rf2 = tuple(s['rfs'][1])
        b2 = env_box(('rf',) + rf2)
        so = -o[1]
        if so - (b2[2] + b2[3]) < 36:
            continue
        keep.append(s)
    # path 1 gives a: RF3 turns o into b
    keep = [s for s in keep if reflect((NE, s['gb_out'][1], s['gb_out'][2]), SE, s['b'][1]) is not None
            and tuple(reflect((NE, s['gb_out'][1], s['gb_out'][2]), SE, s['b'][1])[0]) == tuple(s['rfs'][2])]
    for s in keep:
        bs = [env_box(p) for p in pull_pieces(s)]
        s['box'] = (min(b[0] for b in bs), min(b[1] for b in bs), max(b[2] for b in bs), max(b[3] for b in bs))
        s['area'] = (s['box'][2] - s['box'][0] + 1) * (s['box'][3] - s['box'][1] + 1)
    keep.sort(key=lambda s: s['area'])
    print('o flying NE, path 1 gives a, room between RF2 and o: %d (%.0f s)' % (len(keep), time.time() - t))
    found = []
    tried = 0
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for i0 in range(0, len(keep), 400):
            chunk = keep[i0:i0 + 400]
            for sol, res in pool.imap(check, [(s, le_off) for s in chunk], chunksize=4):
                tried += 1
                if res:
                    found.append({'sol': sol, 'pocket': res})
            print('  tried %d, with pocket %d (%.0f s)' % (tried, len(found), time.time() - t), flush=True)
            if len(found) >= nwant or time.time() - t > 3000:
                break
    for f in found[:20]:
        s = f['sol']
        p = f['pocket'][0]
        print('  Gb %s rfs %s a %s b %s box %s | RF_e j %d %s, Rp %s, %d OR controls, e.g. %s' % (
            tuple(s['gb']), s['rfs'], s['a'], s['b'], s['box'], p['j'], p['rfe'], p['rps'][0][1], p['n_or'], p['ors'][0]))
    with gzip.open('results/j2_pocket_%d.json.gz' % le_off, 'wt') as fh:
        json.dump(found, fh, separators=(',', ':'), default=list)


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
