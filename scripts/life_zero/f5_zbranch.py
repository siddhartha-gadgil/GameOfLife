#!/usr/bin/env python3
"""F5 (R-28): the Z branch of DZ2.  In case Z the glider O (NE-flying, f3_place.json) passes G_N's
lane and becomes the control of a fan-out F_Z1 (any round-trip fan-out of f2_roundtrip, image
with control direction NE): its link glider continues NE = the Z OUTPUT; its second output feeds a
fan-out F_Z2 whose two outputs are turned by reflectors into
   C_I : REG1's INC control, (SE, 314, tau), tau = -2222 (mod 30)  (exact lane, phase mod 30), and
   R_in: (SE, -345, tau') (exact lane; RF_R is re-phased to its time), with R arriving at the block
         after the detector and at least 200 generations before the INC push.
Every new piece keeps >= SEP from all pieces and from the block positions B_-1..B_600, every new
flight segment >= CLEAR from all pieces it does not use and from the unconditional glider paths.
Output: results/f5_zbranch.json (the first solution found)."""
import gzip
import json
import os
import sys
from f0_frozen import *
from common import bbox, life
from net import reflect, time_at, compose
from reactions import sym_wl
import f1_req as F1

SEP, CLEAR = 15, 8
FOS = json.load(gzip.open(os.path.join(HERE, '..', 'life_machine', 'results', 'f2_roundtrip.json.gz'), 'rt'))['good']
FAMS = []
for i, fo in enumerate(FOS):
    outs = [(tuple(o[0]), o[1], o[2]) for o in fo['outs']]
    se = [w for w in outs if w[0] == SE]
    sw = [w for w in outs if w[0] == SW]
    if len(se) == 1 and len(sw) == 1:
        FAMS.append((i, se[0], sw[0]))
CF = (SE, 41, 22)


def fanout_on(target, i, g1c, g2c, k, p):
    """fan-out family i in image sym_k whose control is exactly `target`; p = x translation"""
    ct, g1, g2 = sym_wl(CF, k), sym_wl(g1c, k), sym_wl(g2c, k)
    d = ct[0]
    num = ct[1] + d[1] * p - target[1]
    if num % d[0]:
        return None
    q = num // d[0]
    s = target[2] - ct[2] + 4 * d[0] * p
    outer = ('asm', k, p, q, s % 30)
    pcs = [compose(outer, x) for x in [('asm', 0, 0, 0, 0), ('asm',) + tuple(FOS[i]['asm'])]]
    assert shift_wl(ct, p, q, s) == target
    return pcs, shift_wl(g1, p, q, s), shift_wl(g2, p, q, s)


def cen(e):
    b = bbox(e)
    return ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)


def envs(pcs):
    e = set()
    for x in pcs:
        e |= env_cells(x)
    return e


class World:
    def __init__(self, pieces, paths, ray):
        self.E = envelope(pieces)
        self.EN = Near(self.E)
        self.PN = Near(paths)
        self.RN = Near(ray)
        self.extra = []          # (env, Near) of placed new pieces

    def piece_ok(self, e):
        if self.EN.dist(e, SEP) < SEP or self.RN.dist(e, SEP) < SEP or self.PN.dist(e, 10) < 10:
            return False
        return all(N.dist(e, SEP) >= SEP for (_, N) in self.extra)

    def seg_ok(self, w, a, b, skip=()):
        if time_at(w, b) - time_at(w, a) < 100:      # the glider must fly from a to b
            return False
        sg = glider_path(w, int(time_at(w, a)) + 40, int(time_at(w, b)) - 40)
        if self.EN.dist(sg, CLEAR) < CLEAR:
            return False
        return all(N.dist(sg, CLEAR) >= CLEAR for (j, (_, N)) in enumerate(self.extra) if j not in skip)

    def add(self, e):
        self.extra.append((e, Near(e)))
        return len(self.extra) - 1

    def pop(self, m):
        del self.extra[m:]


def arrival(w, target_dir, target_lane):
    """the glider on (target_dir, target_lane) reached from w by 1 or 2 reflectors (route invariant)"""
    if target_dir[0] * w[0][0] + target_dir[1] * w[0][1] == 0:
        r = reflect(w, target_dir, target_lane)
        return None if r is None else r[1]
    for m in [x for x in (SE, SW, NE, NW) if x[0] * w[0][0] + x[1] * w[0][1] == 0]:
        for Lm in range(0, 6):
            a = reflect(w, m, Lm + 1000 * m[0])
            if a is None:
                continue
            b = reflect(a[1], target_dir, target_lane)
            if b is not None:
                return b[1]
    return None


def route(W, w, src_pt, target_dir, target_lane, mids_lanes, skip_src, only_mid=None):
    """1 or 2 reflectors turning w (leaving src_pt) onto (target_dir, target_lane).  Yields
    (pieces, legs, end point) with every piece and segment checked."""
    if target_dir[0] * w[0][0] + target_dir[1] * w[0][1] == 0:
        r = reflect(w, target_dir, target_lane)
        if r is None:
            return
        if time_at(w, (r[0][2], r[0][3])) - time_at(w, src_pt) < 100:
            return
        e = env_cells(r[0])
        if not W.piece_ok(e):
            return
        if not W.seg_ok(w, src_pt, cen(e), skip=skip_src):
            return
        yield [r[0]], [w, r[1]], cen(e)
        return
    mids = [x for x in (SE, SW, NE, NW) if x[0] * w[0][0] + x[1] * w[0][1] == 0]
    if only_mid is not None:
        mids = [only_mid]
    for m in mids:
        for Lm in mids_lanes:
            a = reflect(w, m, Lm)
            if a is None:
                continue
            b = reflect(a[1], target_dir, target_lane)
            if b is None:
                continue
            # cheap ordering test first: w reaches RF1 after leaving src, the middle leg runs from RF1 to RF2
            pa, pb = (a[0][2], a[0][3]), (b[0][2], b[0][3])
            if time_at(w, pa) - time_at(w, src_pt) < 100 or time_at(a[1], pb) - time_at(a[1], pa) < 100:
                continue
            ea, eb = env_cells(a[0]), env_cells(b[0])
            if not (W.piece_ok(ea) and W.piece_ok(eb)) or Near(ea).dist(eb, SEP) < SEP:
                continue
            if not W.seg_ok(w, src_pt, cen(ea), skip=skip_src):
                continue
            ia = W.add(ea)
            ok = W.seg_ok(a[1], cen(ea), cen(eb), skip=(ia,))
            W.pop(ia)
            if not ok:
                continue
            yield [a[0], b[0]], [w, a[1], b[1]], cen(eb)


def main():
    pl = json.load(open(os.path.join(HERE, 'results', 'f3_place.json')))[0]
    n = pl['n']
    supply = [tuple(p) for p in pl['F_B']] + [tuple(r) for r in pl['rfs']] + [tuple(pl['gate'])]
    pieces = frozen_pieces() + [RF_R] + supply
    O = shift_wl((tuple(pl['O'][0]), pl['O'][1], pl['O'][2]), 0, 0, n)
    paths = F1.glider_paths(with_c=False)
    ray = blocks(-1, 600)
    W = World(pieces, paths, ray)
    # crossing of O with N's lane: Z branch starts beyond it, east of the register
    t_reg = time_at(O, (155, 251))
    lanes_mid = list(range(-1600, 1600, 7))
    push_after = 3570 + 3200      # rough: INC salvo reaches the block about 3570 + travel after C_I
    x0 = int(min(glider_at(*O, int(t_reg)))[0])
    combos = set()
    for (i1, a1, b1) in FAMS:
        for k1 in range(8):
            if life.sym_apply(k1, SE) != NE:
                continue
            f = fanout_on(O, i1, a1, b1, k1, x0 + 400)
            if f is None:
                continue
            y1 = f[2]
            cc = cen(envs(f[0]))
            for (i2, a2, b2) in FAMS:
                for k2 in range(8):
                    if life.sym_apply(k2, SE) != y1[0]:
                        continue
                    g = fanout_on(y1, i2, a2, b2, k2, int(cc[0] + y1[0][0] * 500))
                    if g is None:
                        continue
                    for o, (wa, wb) in enumerate(((g[1], g[2]), (g[2], g[1]))):
                        ci0, ri0 = arrival(wa, SE, CI0[1]), arrival(wb, SE, R_IN0[1])
                        if ci0 is None or ri0 is None or (ci0[2] - CI0[2]) % 30:
                            continue
                        lr = ri0[2] - n - R_IN0[2] + 1885
                        lp = 2062 + (ci0[2] - n - (-2222 + 30 * 172))
                        if lr >= 1885 + 200 and lp >= lr + 200:
                            combos.add((i1, k1, i2, k2))
    print('phase/timing combos:', len(combos), flush=True)
    for (i1, a1, b1) in FAMS:
        for k1 in range(8):
            if life.sym_apply(k1, SE) != NE or not any(c[0] == i1 and c[1] == k1 for c in combos):
                continue
            for p1 in range(int(min(glider_at(*O, int(t_reg)))[0]) + 250, int(min(glider_at(*O, int(t_reg)))[0]) + 700, 9):
                f = fanout_on(O, i1, a1, b1, k1, p1)
                if f is None:
                    continue
                pcs1, zout, y1 = f
                e1 = envs(pcs1)
                if not W.piece_ok(e1):
                    continue
                m1 = W.add(e1)
                c1 = cen(e1)
                # Z output must fly away freely: its line ahead clear of everything
                if not W.seg_ok(zout, c1, (c1[0] + zout[0][0] * 1500, c1[1] + zout[0][1] * 1500), skip=(m1,)):
                    W.pop(m1)
                    continue
                for (i2, a2, b2) in FAMS:
                    for k2 in range(8):
                        if life.sym_apply(k2, SE) != y1[0] or (i1, k1, i2, k2) not in combos:
                            continue
                        for dist2 in range(150, 1300, 23):
                            p2 = int(c1[0] + y1[0][0] * dist2)
                            f2 = fanout_on(y1, i2, a2, b2, k2, p2)
                            if f2 is None:
                                continue
                            pcs2, u1, u2 = f2
                            e2 = envs(pcs2)
                            if not W.piece_ok(e2):
                                continue
                            if not W.seg_ok(y1, c1, cen(e2), skip=(m1,)):
                                continue
                            m2 = W.add(e2)
                            c2 = cen(e2)
                            for (wa, wb) in ((u1, u2), (u2, u1)):
                                ci0 = arrival(wa, SE, CI0[1])
                                ri0 = arrival(wb, SE, R_IN0[1])
                                if ci0 is None or ri0 is None or (ci0[2] - CI0[2]) % 30:
                                    continue
                                lr = ri0[2] - n - R_IN0[2] + 1885
                                lp = 2062 + (ci0[2] - n - (-2222 + 30 * 172))
                                if lr < 1885 + 200 or lp < lr + 200:
                                    continue
                                for (ra, la, enda) in route(W, wa, c2, SE, CI0[1], lanes_mid, (m2,)):
                                    ci = la[-1]
                                    if (ci[2] - CI0[2]) % 30:
                                        continue
                                    ma = W.add(envs(ra))
                                    for (rb, lb, endb) in route(W, wb, c2, SE, R_IN0[1], lanes_mid, (m2,)):
                                        rin = lb[-1]
                                        # R's local time and the push's local time (frame of counter 0, design shifted by n)
                                        loc_R = rin[2] - n - R_IN0[2] + 1885
                                        loc_push = 2062 + (ci[2] - n - (-2222 + 30 * 172))
                                        if loc_R < 1885 + 200 or loc_push < loc_R + 200:
                                            continue
                                        # R_in's segment to RF_R and C_I's segment to REG1
                                        if not W.seg_ok(rin, endb, (RF_R[2], RF_R[3])):
                                            continue
                                        if not W.seg_ok(ci, enda, (-90, -403)):
                                            continue
                                        sol = {'F_Z1': [list(x) for x in pcs1], 'F_Z2': [list(x) for x in pcs2],
                                               'RF_CI': [list(x) for x in ra], 'RF_RIN': [list(x) for x in rb],
                                               'Zout': [list(zout[0]), zout[1], zout[2]], 'C_I': [list(ci[0]), ci[1], ci[2]],
                                               'R_in': [list(rin[0]), rin[1], rin[2]], 'loc_R': loc_R, 'loc_push': loc_push,
                                               'fams': [i1, k1, p1, i2, k2, dist2]}
                                        print(json.dumps(sol), flush=True)
                                        json.dump(sol, open(os.path.join(HERE, 'results', 'f5_zbranch.json'), 'w'))
                                        return
                                    W.pop(ma)
                            W.pop(m2)
                W.pop(m1)
    print('no solution')


if __name__ == '__main__':
    main()
