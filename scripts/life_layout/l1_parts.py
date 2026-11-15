#!/usr/bin/env python3
"""L1 (R-30): the parts of the layout, in local coordinates, with their exact input/output behaviour
(exact simulation with gsim).

Instruction unit template U(kind, n), kind in {'dec', 'inc', 'halt', 'merge'}:
  * entry chain: n copies of the OR gate (blockedStream, sym 0) of R-29 §1.1, the last copy at
    ('asm', 0, 0, 0, 0), copy t upstream = last - t (35, 64) with the relay delays of g5_chain;
    input t = the side input of copy t, (NE, lane_t, tau_t .. tau_t + 12) + 30 m.  Side lines of
    consecutive copies differ by 99 in v = x + y, so they alternate in parity.
  * body: 'dec' = the DZ2 front F_B + F_A (R-28, three outputs L (SW), R (NE), D (SE));
          'inc' = F_A alone (= R-29's F_I; outputs R (NE, continue), D (SE, link));
          'halt', 'merge' = nothing (output D = the chain output).
  * the outputs L, R are turned down (SE) by one reflector each, at columns c_L, c_R.
  Interface: every input is a NW glider on the column c_in(t) (turned NE onto the side line by a
  reflector placed by the router), every output an SE glider on a column (u-line).
Usage: l1_parts.py   (simulates every template, prints the I/O table)"""
import sys
import json
from lcommon import *
from net import Net
import g5_chain
import l0_module

F_B = [('asm', 0, -1100, -1100, 22), ('asm', 0, -945, -918, 17)]
F_A = list(f0_frozen.F_A)
FRONT_IN = (SE, 41, 4444)          # F_B + F_A: (SW,-2125,-2527) L, (NE,1071,5041) R, (SE,41,4612) D
FA_IN = (SE, -13, 2446)            # F_A: (NE,1071,2851) R, (SE,41,2422) D
OR_OUT = (SE, 14, 119)             # gate coordinates


def entry_chain(n):
    """Pieces copy 0 (last) .. copy n-1 (upstream) and the side input world lines (residue 1)."""
    gates = [('asm', 0, 0, 0, 0)]
    for t in range(1, n):
        g = gates[-1]
        need = wl_out((SE, 43, 5), g)
        p, q = g[2] - 35, g[3] - 64
        o = wl_out(OR_OUT, ('asm', 0, p, q, 0))
        assert o[1] == need[1]
        gates.append(('asm', 0, p, q, (need[2] - o[2]) % 30))
    side = [wl_out((NE, -76, 1), g) for g in gates]
    return gates, side


def body(kind, out_lane=14, top=217):
    """Body pieces placed under the chain output (SE, out_lane): (pieces, input world line, outputs)."""
    if kind == 'dec':
        pcs, w_in, outs = F_B + F_A, FRONT_IN, {'L': (SW, -2125, -2527), 'R': (NE, 1071, 5041), 'D': (SE, 41, 4612)}
        vtop = -2196
    elif kind == 'inc':
        pcs, w_in, outs = F_A, FA_IN, {'R': (NE, 1071, 2851), 'D': (SE, 41, 2422)}
        vtop = -1143
    else:
        return [], None, {}
    du = out_lane - w_in[1]                    # dx - dy
    s = top - vtop                              # dx + dy >= s, same parity as du
    if (s - du) % 2:
        s += 1
    dx, dy = (s + du) // 2, (s - du) // 2
    return [move(p, dx, dy) for p in pcs], mwl(w_in, dx, dy), {k: mwl(w, dx, dy) for k, w in outs.items()}


def par(x, p):
    """x or x - 1 with parity p."""
    return x if x % 2 == p % 2 else x - 1


class Unit:
    """An instruction unit template (local coordinates; the last entry copy at the origin)."""

    def __init__(self, kind, n):
        self.kind, self.n = kind, n
        gates, side = entry_chain(n)
        self.gates = gates
        self.side = side                                   # input t: (NE, lane, tau..tau+12) + 30 m
        chain_out = wl_out(OR_OUT, gates[0])
        bp, w_in, outs = body(kind)
        pieces = list(gates)
        self.cols = {}
        self.turns = []
        if kind in ('dec', 'inc'):
            # make the body input exactly the chain output (choose the body's delay)
            d = chain_out[2] - w_in[2]
            bp = [move(p, 0, 0, d) for p in bp]
            outs = {k: mwl(w, 0, 0, d) for k, w in outs.items()}
            pieces += bp
            env = set().union(*[env_cells(p) for p in bp])
            ub = l0_module.uvbox(env)
            for k, w in outs.items():
                if k == 'D':
                    self.cols['D'] = w
                    continue
                v = -w[1] if w[0] == NE else w[1]
                if k == 'R':
                    c = par(ub[2] + 70, 1 - v % 2)
                else:
                    c = par(ub[0] - 70, 1 - v % 2)
                rf, g2 = reflect(w, SE, c)
                assert g2[1] == c
                pieces.append(rf)
                self.turns.append(rf)
                self.cols[k] = g2
        else:
            self.cols['D'] = chain_out
        self.pieces = pieces
        allenv = set().union(*[env_cells(p) for p in pieces])
        self.uvbox = l0_module.uvbox(allenv)
        # input columns: left of everything, 60 apart, upstream copies further left
        u0 = self.uvbox[0] - 60
        self.in_cols = []
        for t in range(n):
            vt = -self.side[t][1]
            self.in_cols.append(par(u0 - 60 * t, 1 - vt % 2))
        self.width = (self.in_cols[-1] - 40, self.uvbox[2] + 40)

    def out_names(self):
        return sorted(self.cols, key=lambda k: self.cols[k][1])

    def simulate(self, t, r=6, m=20):
        """Exact run: input at copy t (residue r of its window, + 30 m): (outputs as removed world lines, ok)."""
        w = mwl(self.side[t], 0, 0, r - 1 + 30 * m)
        cbox = core_box(self.pieces, margin=80)
        c0 = (min(cbox[0], -800), min(cbox[1], -800), cbox[2], cbox[3])
        t0 = 30 * ((int(time_at(w, cross(self.gates[t]))) - 200) // 30)
        t1 = t0 + 30 * 260
        cells, rem = run_peel(self.pieces, [w], t0, t1, cbox=c0)
        ok = cells == state(self.pieces, [], t1)
        return rem, ok


_UNITS = {}


def unit(kind, n):
    key = (kind, n)
    if key not in _UNITS:
        U = Unit(kind, n)
        cache = os.path.join(RES, 'l1_units.json')
        data = json.load(open(cache)) if os.path.exists(cache) else {}
        k = '%s_%d' % key
        if k not in data:
            res = []
            for t in range(n):
                rem, ok = U.simulate(t)
                assert ok, (key, t, rem)
                res.append([list(map(list, [w[0]])) + [w[1], w[2]] for w in rem])
            data[k] = res
            json.dump(data, open(cache, 'w'))
        # outputs for input t at tau_t + 5 + 30 * 20: map them to the column names
        U.io = []
        for t in range(n):
            rem = [(tuple(w[0]), w[1], w[2]) for w in data[k][t]]
            d = {}
            for name, col in U.cols.items():
                cand = [w for w in rem if w[:2] == col[:2]]
                assert len(cand) == 1, (key, t, name, rem, col)
                d[name] = cand[0]
            assert len(d) == len(rem)
            U.io.append(d)
        _UNITS[key] = U
    return _UNITS[key]


def main():
    for kind in ('dec', 'inc', 'halt', 'merge'):
        for n in (1, 2, 3, 4):
            U = unit(kind, n)
            print('%s n=%d: pieces %d, uv box %s, out columns %s, in columns %s' % (
                kind, n, len(U.pieces), U.uvbox, {k: wl(w) for k, w in U.cols.items()}, U.in_cols), flush=True)
            for t in range(n):
                print('   input %d %s (+5 +600): %s' % (t, wl(U.side[t]), {k: wl(w) for k, w in U.io[t].items()}))


if __name__ == '__main__':
    main()
