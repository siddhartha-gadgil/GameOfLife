#!/usr/bin/env python3
"""P0 (R-31): unit templates of the provable layout, in local coordinates (last entry copy at the
origin), and their exact input/output behaviour (gsim).

Differences with R-30's l1_parts.Unit (whose pieces are reused):
  * input columns by formula: c_in(t) = C0 - 61 t (C0 + v_0 odd), so that the corner
    (c_in(t), v_t) (v_t = 76 - 99 t, side line of copy t) has odd u + v for every t;
  * the decJz unit's D output is moved right of R by a jog of two RF0 (SE -> NE at v = 1501,
    NE -> SE at u = 188), so that its three source columns are L (-155, odd), R (127, odd),
    D' (188, even): this is what the nesting of the three concurrent links needs (R-31 §3).
Usage: p0_parts.py [P ...]   (simulates kind x copy t x residue, prints the I/O table)"""
import sys
import json
from lpcommon import *

JOG_V, JOG_U = 1501, 188


class UnitLP:
    def __init__(self, kind, n):
        U = l1_parts.Unit(kind, n)
        self.kind, self.n = kind, n
        self.gates, self.side = U.gates, U.side
        pieces = list(U.pieces)
        cols = dict(U.cols)
        if kind == 'dec':
            g = cols['D']
            assert coord_of(g) == 14
            rf1, g1 = reflect(g, NE, lane_of(NE, JOG_V))
            rf2, g2 = reflect(g1, SE, lane_of(SE, JOG_U))
            pieces += [rf1, rf2]
            cols['D'] = g2
            self.jog = [rf1, rf2]
        self.pieces = pieces
        self.cols = cols                      # output world lines (representative times)
        allenv = set().union(*[env_cells(p) for p in pieces])
        self.uvbox = l0_module.uvbox(allenv)
        v0 = -self.side[0][1]
        C0 = self.uvbox[0] - 60
        if (C0 + v0) % 2 == 0:
            C0 -= 1
        self.C0 = C0
        self.in_cols = [C0 - 61 * t for t in range(n)]
        self.v_side = [-s[1] for s in self.side]
        for t in range(n):
            assert (self.in_cols[t] + self.v_side[t]) % 2 == 1
        self.left = self.in_cols[-1] - 30
        self.right = max(self.uvbox[2], max(coord_of(w) for w in cols.values())) + 30

    def simulate(self, t, r=5, m=20):
        """Exact run, input at copy t, residue r of its window (1 .. 13), + 30 m: (removed, ok)."""
        w = mwl(self.side[t], 0, 0, r - 1 + 30 * m)
        cbox = core_box(self.pieces, margin=80)
        c0 = (min(cbox[0], -900), min(cbox[1], -900), cbox[2], cbox[3])
        t0 = 30 * ((int(time_at(w, cross(self.gates[t]))) - 200) // 30)
        t1 = t0 + 30 * 300
        cells, rem = run_peel(self.pieces, [w], t0, t1, cbox=c0)
        ok = cells == state(self.pieces, [], t1)
        return rem, ok


_U = {}


def unit(kind, n, check=True):
    """Template with its I/O table io[t] = {output: world line} for the input at copy t at window
    residue 5, slot 20 (tau_t + 4 + 600); outputs of other residues / slots: same residue (checked)."""
    key = (kind, n)
    if key in _U:
        return _U[key]
    U = UnitLP(kind, n)
    cache = os.path.join(LPRES, 'p0_units.json')
    data = json.load(open(cache)) if os.path.exists(cache) else {}
    k = '%s_%d' % key
    if k not in data:
        res = {}
        for t in range(n):
            for r in (1, 5, 13):
                rem, ok = U.simulate(t, r)
                assert ok, (key, t, r, rem)
                res['%d_%d' % (t, r)] = [[list(w[0]), w[1], w[2]] for w in rem]
        data[k] = res
        json.dump(data, open(cache, 'w'))
    U.io = []
    for t in range(n):
        outs = {}
        for r in (1, 5, 13):
            rem = [(tuple(w[0]), w[1], w[2]) for w in data[k]['%d_%d' % (t, r)]]
            d = {}
            for name, col in U.cols.items():
                cand = [w for w in rem if w[:2] == col[:2]]
                assert len(cand) == 1, (key, t, name, rem, col)
                d[name] = cand[0]
            assert len(d) == len(rem), (key, t, rem)
            outs[r] = d
        # the unit re-times: the outputs do not depend on the residue inside the window
        assert outs[1] == outs[5] == outs[13], (key, t, outs)
        U.io.append(outs[5])
    _U[key] = U
    return U


def main():
    Ps = [int(a) for a in sys.argv[1:]] or [1, 2, 3]
    out = open(os.path.join(LPRES, 'p0_units.txt'), 'w')

    def log(s):
        print(s, flush=True)
        out.write(s + '\n')
    for P in Ps:
        for kind in ('dec', 'inc', 'halt', 'merge'):
            U = unit(kind, 2 * P)
            log('%s n=%d: %d pieces, uv box %s, slab [%d, %d], C0 %d, outputs %s' % (
                kind, 2 * P, len(U.pieces), U.uvbox, U.left, U.right, U.C0, {k: wl(w) for k, w in U.cols.items()}))
            for t in range(U.n):
                w = mwl(U.side[t], 0, 0, 4 + 600)
                res = {k: (wl(g), g[2] % 30, g[2] - w[2]) for k, g in U.io[t].items()}
                log('   copy %d side %s (window tau..tau+12, residues 1, 5, 13 checked): outputs %s' % (t, wl(U.side[t]), res))


if __name__ == '__main__':
    main()
