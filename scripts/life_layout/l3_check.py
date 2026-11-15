#!/usr/bin/env python3
"""L3 (R-30): static checks of a layout (l2_layout.layout):
  (a) piece envelopes of different groups (module r, unit, routing reflector) >= 12 apart;
  (b) every route leg (glider path) >= 12 from every piece it does not use (the reflectors at its
      ends, the emitting / receiving group at the first / last leg excluded: inside modules and
      units the verified R-28 / R-29 / l1 geometry applies);
  (c) block diagonals B_-1 .. B_600 of every register >= 12 from every piece, eater and route leg
      not belonging to that register's module;
  (d) concurrent links (the three outputs of one DECJZ unit; INC link, its merge link and the
      continue) never pass a crossing point less than 40 generations apart;
  (e) the HALT line: nothing at u below the halt cell.
Usage: l3_check.py PROGRAM_NAME"""
import sys
from lcommon import *
import l2_layout as L2
from dcat import Near

PROGS = {
    'add': [('dec', 0, 3), ('inc', 1), ('dec', 2, 0), ('halt',)],
    'share': [('inc', 0), ('dec', 0, 3), ('dec', 0, 3), ('halt',)],
}


def group_of(name):
    return name


def leg_segments(L):
    """[(world line, (x0, y0), (x1, y1))] of the legs of a link between consecutive corners (xy)."""
    segs = []
    pts = [None] + [xy(*c) if (c[0] + c[1]) % 2 == 0 else ((c[0] + c[1]) / 2, (c[1] - c[0]) / 2) for c in L['corners']] + [None]
    if L.get('gate'):
        pts[-1] = cross(L['gate'])          # the last leg ends in the receiving gate
    elif L['dst'][0] == 'halt':
        g = L['legs'][-1]                   # the HALT line, checked up to u = -9000
        vv = L2.coord_of(g)
        pts[-1] = ((-9000 + vv) / 2, (vv + 9000) / 2)
    for k, g in enumerate(L['legs']):
        segs.append((g, pts[k], pts[k + 1]))
    return segs


def seg_cells(g, p0, p1, cut=0):
    t0 = time_at(g, p0) if p0 else None
    t1 = time_at(g, p1) if p1 else None
    if t0 is None:
        t0 = t1 - 600
    if t1 is None:
        t1 = t0 + 1200
    return glider_path(g, int(t0) + cut, int(t1) - cut)


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else 'add'
    m = L2.layout(PROGS[name])
    L2.describe(m)
    # groups
    grp = []
    for p, n in zip(m.pieces, m.names):
        grp.append(n if n.startswith('M') or n.startswith('U') else n + ':' + str(p))
    envs = [env_cells(p) for p in m.pieces]
    boxes = [bbox(e) for e in envs]
    bad = 0
    dmin = 10 ** 9
    for i in range(len(envs)):
        for j in range(i):
            if grp[i] == grp[j]:
                continue
            bd = box_dist(boxes[i], boxes[j])
            if bd >= 40:
                continue
            d = set_dist(envs[i], envs[j])
            dmin = min(dmin, d)
            if d < 12:
                bad += 1
                print('  (a) FAIL %s %s / %s %s: %d' % (m.names[i], m.pieces[i], m.names[j], m.pieces[j], d))
    print('(a) min envelope distance between groups (< 40 box): %d, failures %d' % (dmin, bad), flush=True)
    # (b), (c): a bucket grid of all envelope cells (and eaters) tagged with their owner
    SZ = 16
    grid = {}
    for i, e in enumerate(envs):
        for (x, y) in e:
            grid.setdefault((x // SZ, y // SZ), []).append((x, y, i))
    for (x, y) in m.eaters:
        grid.setdefault((x // SZ, y // SZ), []).append((x, y, -1))

    def near_owners(cells, cap=12):
        """{owner: min distance < cap} for the cells."""
        res = {}
        for (x, y) in cells:
            bx, by = x // SZ, y // SZ
            for i in (bx - 1, bx, bx + 1):
                for j in (by - 1, by, by + 1):
                    for (a, b, o) in grid.get((i, j), ()):
                        d = max(abs(a - x), abs(b - y))
                        if d < cap and d < res.get(o, cap):
                            res[o] = d
        return res

    worst, fails = 10 ** 9, 0
    pidx = {}
    for i, p in enumerate(m.pieces):
        pidx.setdefault(p, i)
    for L in m.links:
        segs = leg_segments(L)
        own = {pidx[p] for p in L['pieces']}
        for k, (g, p0, p1) in enumerate(segs):
            path = seg_cells(g, p0, p1, cut=0)
            for o, d in near_owners(path, 13).items():
                if o in own:
                    continue
                nm = m.names[o] if o >= 0 else 'eater'
                if k == 0 and L['src'][0] == 'unit' and nm == 'U%s%s' % L['src'][1]:
                    continue
                if k <= 1 and L['src'][0] == 'ret' and nm in ('M%d' % L['src'][1], 'eater'):
                    continue
                if k == len(segs) - 1 and L['dst'][0] == 'unit' and nm == 'U%s%s' % L['dst'][1]:
                    continue
                if k >= len(segs) - 2 and L['dst'][0] == 'port' and nm in ('M%d' % L['dst'][1], 'eater'):
                    continue
                worst = min(worst, d)
                fails += 1
                print('  (b) FAIL link %s leg %d %s passes %s %s at %d' % (L['name'], k, wl(g), nm, m.pieces[o] if o >= 0 else '', d))
    print('(b) route legs vs pieces they do not use: failures (distance < 13) %d' % fails, flush=True)
    # (c) diagonals: cells of B_-1 .. B_600 of register r vs foreign pieces, eaters, route legs
    fails = 0
    for r in m.regs:
        B = translate(blocks(-1, 600), m.U[r] // 2, -m.U[r] // 2)
        for o, d in near_owners(B, 13).items():
            nm = m.names[o] if o >= 0 else 'eater'
            if nm == 'M%d' % r:
                continue
            if o == -1:
                # eaters: those of module r are at >= 99 (R-29); report any
                pass
            fails += 1
            print('  (c) FAIL register %d diagonal - %s: %d' % (r, nm, d))
        NB = Near(B)
        bb = bbox(B)
        for L in m.links:
            for k, (g, p0, p1) in enumerate(leg_segments(L)):
                path = seg_cells(g, p0, p1)
                if box_dist(bbox(path), bb) > 20:
                    continue
                d = NB.dist(path, 20)
                if d < 13:
                    fails += 1
                    print('  (c) FAIL register %d diagonal - link %s leg %d: %d' % (r, L['name'], k, d))
    print('(c) register diagonals B_-1..B_600 vs foreign pieces, eaters and route legs: failures (distance < 13) %d' % fails, flush=True)
    # (d) concurrent crossings
    byname = {L['name']: L for L in m.links}
    groups = []
    for i, ins in enumerate(m.prog):
        if ins[0] == 'dec':
            groups.append([byname['dec%d.%s' % (i, o)] for o in ('C', 'KNZ', 'KZ')])
        elif ins[0] == 'inc':
            Lm = dict(byname['merge%d' % ins[1]])
            Lm['legs'] = byname['inc%d.link' % i]['merge_legs']
            groups.append([byname['inc%d.link' % i], byname['inc%d.cont' % i], Lm])
    def uv_segs(L):
        """[(glider, 'u'|'v', line coordinate, lo, hi)] in (u, v) for the legs of L."""
        out = []
        for (g, p0, p1) in leg_segments(L):
            c = L2.coord_of(g)
            typ = 'u' if L2.is_u(g[0]) else 'v'
            ends = []
            for pt in (p0, p1):
                if pt is not None:
                    q = (pt[0] - pt[1], pt[0] + pt[1])
                    ends.append(q[1] if typ == 'u' else q[0])
            if len(ends) == 1:
                ends.append(ends[0] + (-600 if p0 is None else 600) * (1 if (typ == 'u' and g[0] == SE) or (typ == 'v' and g[0] == NE) else -1))
            out.append((g, typ, c, min(ends), max(ends)))
        return out

    worst = 10 ** 9
    fails = 0
    for gl in groups:
        for a in range(len(gl)):
            for b in range(a):
                A, B = gl[a], gl[b]
                for (g1, t1, c1, lo1, hi1) in uv_segs(A):
                    for (g2, t2, c2, lo2, hi2) in uv_segs(B):
                        if t1 != t2:
                            # perpendicular: crossing point
                            if not (lo2 - 6 <= c1 <= hi2 + 6 and lo1 - 6 <= c2 <= hi1 + 6):
                                continue
                            uu, vv = (c1, c2) if t1 == 'u' else (c2, c1)
                        else:
                            if abs(c1 - c2) > 10 or hi1 < lo2 - 6 or hi2 < lo1 - 6:
                                continue
                            mid = (max(lo1, lo2) + min(hi1, hi2)) / 2
                            uu, vv = (c1, mid) if t1 == 'u' else (mid, c1)
                        pt = ((uu + vv) / 2, (vv - uu) / 2)
                        dt = abs(time_at(g1, pt) - time_at(g2, pt))
                        worst = min(worst, dt)
                        if dt < 40:
                            fails += 1
                            print('  (d) FAIL %s / %s cross at uv (%d, %d), dt %d' % (A['name'], B['name'], uu, vv, dt))
    print('(d) min time difference at crossings of concurrent links: %s, failures %d' % (worst, fails), flush=True)
    # (e) halt
    minu = min(min(x - y for x, y in e) for e in envs)
    for L in m.links:
        for c in L['corners']:
            minu = min(minu, c[0])
    hu = minu - 600
    hv = L2.coord_of(m.halt)
    cell = xy(hu + (hu + hv) % 2, hv)
    print('(e) leftmost piece / corner at u = %d; HALT cell %s on the halt line %s (u = %d)' % (minu, cell, wl(m.halt), hu))


if __name__ == '__main__':
    main()
