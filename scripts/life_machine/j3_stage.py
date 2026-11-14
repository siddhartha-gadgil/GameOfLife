#!/usr/bin/env python3
"""J3 (R-24): the joint FINAL STAGE of the register, checked with free gliders.

For a pull design with a pocket (results/j2_pocket_4.json.gz, j2_pocket.py) build
  pull  : S, K, Gb, RF1, RF2, RF3 (control C0 -> a on lane L, b on L + 6: pullSalvo);
  push  : the OR control w of Gb (b' = second glider of the same RF3), RF_e + its feeder Rp
          (e on lane L - 4), RF_c (c on L + 12, L-type, input from the SW),
the push salvo being (5, -47), (11, -25), (-5, 0) of results/p1_pushes.json relative to the block:
e = b' + 47, c = b' + 22 (tau).  The INC inputs are three free gliders: w, s1 (SE, into Rp), c_in
(NE, into RF_c).  Checks (net.Net, board then set simulator on the unbounded plane):
  * the composite is periodic (period 30);
  * DEC: C0 -> exactly {a, b};  INC: {w, s1, c_in} -> exactly {e, b', c};
  * block tests with the register block (lane L + 1) for DEC (k -> k - 1) and INC (k -> k + 1).

Usage: j3_stage.py [INDEX ...]     (indices into the pocket file; default: first 10)
Output: results/j3_stage.json (the stages that pass), summary on stdout.
"""
import gzip
import json
import os
import sys

from common import SE, SW, NE, NW, life, translate, counter, glider_at, bbox
import net
from net import Net, reflect_to, env_cells, env_box, set_dist, time_at, rf_point, box_dist
from g2_pull import reflect
import g4_pull3 as g4
import j2_pocket as J

# the push: R24_PUSH=5 (default): (5, -47), (11, -25), (-5, 0): e = b' + 47 on lane a - 4, c = b' + 22 on a + 12;
#           R24_PUSH=6:           (5, -51), (12, -24), (-6, 0): e = b' + 51 on lane a - 5, c = b' + 27 on a + 13
PUSH = int(os.environ.get('R24_PUSH', 5))
if PUSH == 5:
    PUSH_E, PUSH_C, LE, LC = 47, 22, -4, 12
else:
    PUSH_E, PUSH_C, LE, LC = 51, 27, -5, 13
POCKET_FILE = 'results/j2_pocket_%d.json.gz' % (-LE)
SUFFIX = '' if PUSH == 5 else '_q6'


def tup(w):
    return (tuple(w[0]), w[1], w[2])


def build(rec, ior=0, irp=0, jc_range=range(0, 400)):
    sol = rec['sol']
    pk = rec['pocket'][0] if isinstance(rec['pocket'], list) else rec['pocket']
    pull = J.pull_pieces(sol)
    a, b = tup(sol['a']), tup(sol['b'])
    L = a[1]
    jp0 = pk['rps'][irp][0]
    rfe0, gin0 = reflect_to((SE, L + LE, 0), SW, pk['j'])
    ors = J.or_controls(sol, [rfe0, reflect_to(gin0, SE, jp0)[0]])
    if not ors:
        return None
    w, oo = ors[ior]
    r3 = reflect(oo, SE, L + 6)
    assert r3 is not None and tuple(r3[0]) == tuple(sol['rfs'][2]), (r3, sol['rfs'][2])
    bp = r3[1]
    T = bp[2]
    e = (SE, L + LE, T + PUSH_E)
    c = (SE, L + LC, T + PUSH_C)
    rfe, gin = reflect_to(e, SW, pk['j'])
    jp = pk['rps'][irp][0]
    rp, s1 = reflect_to(gin, SE, jp)
    pieces = pull + [rfe, rp]
    # RF_c: first position downstream of RF3 with clearances
    segs = J.segments(sol)
    boxes = [env_box(p) for p in pieces]
    s_rf3 = rf_point(pull[5])
    rfc = cin = None
    for jc in jc_range:
        q, ci = reflect_to(c, NE, jc)
        pt = rf_point(q)
        if pt[0] + pt[1] < s_rf3[0] + s_rf3[1] + 20:
            continue
        bq = env_box(q)
        if min(box_dist(bq, x) for x in boxes) < 6:
            continue
        ok = all(g4.seg_clear(g, ta, tb, [J.obst(q, 3)]) for (nm, g, ta, tb) in segs if nm not in ('a', 'b'))
        ok = ok and g4.seg_clear(a, time_at(a, pt) - 200, time_at(a, pt) + 200, [J.obst(q, 2)])
        ok = ok and g4.seg_clear(b, time_at(b, pt) - 200, time_at(b, pt) + 200, [J.obst(q, 1)])
        ok = ok and g4.seg_clear(e, time_at(e, pt) - 200, time_at(e, pt) + 200, [J.obst(q, 2)])
        tq = time_at(ci, pt)
        ok = ok and g4.seg_clear(ci, tq - 2500, tq - 30, [J.obst(p, 3) for p in pieces])
        if ok:
            rfc, cin = q, ci
            break
    if rfc is None:
        return None
    pieces = pieces + [rfc]
    names = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3', 'RFe', 'Rp', 'RFc']
    return {'pieces': pieces, 'names': names, 'a': a, 'b': b, 'C0': g4.C0, 'w': w, 's1': s1, 'cin': cin,
            'e': e, 'bp': bp, 'c': c, 'L': L}


def block_at(L, k, ymin):
    """counter k translated onto lane L + 1 (upper left cell lane), far below ymin."""
    # counter 0 has its upper left cell at (7, 11): lane -4
    dy = ymin - 11
    dx = (L + 1) + 4 + dy
    return translate(set(counter(k)), dx, dy), (dx, dy)


def check(st, ks=(0, 1, 2, 3, 4, 40), verbose=True):
    nt = Net(st['pieces'], st['names'])
    out = {}
    s, outs, Ts, Te = nt.react([st['C0']], limit=4000)
    out['dec'] = (s, outs, Ts, Te)
    okd = s == 'ok' and outs == sorted([st['a'], st['b']])
    s2, outs2, Ts2, Te2 = nt.react([st['w'], st['s1'], st['cin']], limit=6000)
    out['inc'] = (s2, outs2, Ts2, Te2)
    oki = s2 == 'ok' and outs2 == sorted([st['e'], st['bp'], st['c']])
    if verbose:
        print('   DEC: %s %s   INC: %s %s' % (s, okd, s2, oki), flush=True)
    if not (okd and oki):
        return False, out
    env = nt.env
    ymin = env[3] + 30
    blk = {}
    for k in ks:
        for name, ctr, (Ts_, Te_), dk in (('dec', [st['C0']], (Ts, Te), -1), ('inc', [st['w'], st['s1'], st['cin']], (Ts2, Te2), 1)):
            B, off = block_at(st['L'], k, ymin)
            B2, _ = block_at(st['L'], k + dk, ymin)
            extra = 30 * ((4 * (k + ymin) + 600) // 30)
            fin, box = nt.trace(ctr, Ts_, Te_ + extra, extra=B)
            good = fin == (nt.cycle(Te_ + extra) | B2)
            blk[(name, k)] = (good, Te_ + extra - Ts_, box)
            if verbose:
                print('   block %s k=%d: %s (N %d, box %s)' % (name, k, good, Te_ + extra - Ts_, box), flush=True)
            if not good:
                return False, out
    out['blocks'] = blk
    out['offset'] = off
    return True, out


def main():
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    recs = json.load(gzip.open(POCKET_FILE, 'rt'))
    idx = [int(x) for x in sys.argv[1:]] or list(range(min(10, len(recs))))
    good = []
    for i in idx:
        rec = recs[i]
        st = build(rec)
        print('design %d: Gb %s a %s; stage %s' % (i, rec['sol']['gb'], rec['sol']['a'], 'built' if st else 'no RF_c'), flush=True)
        if not st:
            continue
        ok, info = check(st, ks=(0, 3))
        if ok:
            good.append({'index': i, 'stage': {k: v for k, v in st.items()}})
    json.dump(good, open('results/j3_stage%s.json' % SUFFIX, 'w'), default=list)
    print('stages passing (DEC, INC, block k = 0, 3): %d of %d' % (len(good), len(idx)))


if __name__ == '__main__':
    main()
