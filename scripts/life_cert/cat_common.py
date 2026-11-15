#!/usr/bin/env python3
"""Shared helpers of the cat_* scripts (R-31 catalogue of local certificates; untrusted extractor,
Lean is the check).  Exact set simulation of small reactions (life_gates.step_cells) on the
unbounded plane, choice of t0 / Delta, windows in the ofRows convention (bit j of rows[i] = cell
(x0 + j, y0 + i))."""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
CHERE = HERE                     # (the star imports below rebind HERE)
for d in ('life_lp',):
    p = os.path.join(HERE, '..', d)
    if p not in sys.path:
        sys.path.insert(0, p)
from lpcommon import *  # noqa  (life_layout, life_route, life_machine, life_zero, life_gates)
from life import step_cells as _step, window_of_cells, cells_of_window, transform as _transform  # noqa
from life import glider_worldline as _gwl  # noqa

CRES = os.path.join(CHERE, 'results')
assert os.path.basename(os.path.dirname(CRES)) == 'life_cert'


def win(cells):
    if not cells:
        return None
    x0, y0, rows = window_of_cells(cells)
    return {'x0': x0, 'y0': y0, 'rows': [str(r) if r >= 2 ** 53 else r for r in rows]}


def boxd(b):
    return {'xmin': b[0], 'ymin': b[1], 'xmax': b[2], 'ymax': b[3]}


def hull(a, b):
    if a is None:
        return b
    return (min(a[0], b[0]), min(a[1], b[1]), max(a[2], b[2]), max(a[3], b[3]))


def inbox(b, B):
    return B[0] <= b[0] and B[1] <= b[1] and b[2] <= B[2] and b[3] <= B[3]


def gcells(pieces, eaters, t):
    c = set(eaters)
    for p in pieces:
        c |= piece_cells(p, t)
    return c


def cycle_box(pieces, eaters, t0=0):
    b = None
    for t in range(t0, t0 + 30):
        b = hull(b, bbox(gcells(pieces, eaters, t)))
    c0 = gcells(pieces, eaters, t0)
    assert gcells(pieces, eaters, t0 + 30) == c0
    # period 30 checked with the set simulator too
    c = set(c0)
    for _ in range(30):
        c = _step(c)
    assert c == c0, 'not period 30'
    return b


def envset(pieces, eaters):
    e = set(eaters)
    for p in pieces:
        e |= env_cells(p)
    return e


class Env:
    """Exact Chebyshev distance to a fixed finite set (bucket grid)."""
    S = 16
    CAP = 64          # distances >= 64 are reported as 64

    def __init__(self, cells):
        self.b = {}
        for (x, y) in cells:
            self.b.setdefault((x // self.S, y // self.S), []).append((x, y))
        ks = list(self.b)
        self.kb = (min(k[0] for k in ks), min(k[1] for k in ks), max(k[0] for k in ks), max(k[1] for k in ks))

    def _d1(self, cx, cy):
        S = self.S
        bx, by = cx // S, cy // S
        best = None
        r = 0
        while True:
            if best is not None and (r - 1) * S >= best:
                return best
            if best is None and (r - 1) * S >= self.CAP:
                return self.CAP
            if r > 0 and bx - r < self.kb[0] and by - r < self.kb[1] and bx + r > self.kb[2] and by + r > self.kb[3]:
                return best
            for i in range(bx - r, bx + r + 1):
                for j in range(by - r, by + r + 1):
                    if max(abs(i - bx), abs(j - by)) != r:
                        continue
                    for (x, y) in self.b.get((i, j), ()):
                        d = max(abs(x - cx), abs(y - cy))
                        if best is None or d < best:
                            best = d
            r += 1

    def dist(self, cells):
        return min(self._d1(cx, cy) for cx, cy in cells)


def gl(w, t):
    return set(glider_at(*w, t))


def approach(E, w, tc, span=2000):
    """(t_close, t_in, t_out) for the glider w near the envelope E: t_close the first time of minimal
    distance; t_in the latest multiple of 30 <= t_close with distance >= 3; t_out the first time
    after which the distance stays >= 3 (within span) and >= t_close."""
    ts = list(range(int(tc) - span, int(tc) + span))
    ds = [E.dist(gl(w, t)) for t in ts]
    m = min(ds)
    i = ds.index(m)
    t_close = ts[i]
    t_in = 30 * (t_close // 30)
    while E.dist(gl(w, t_in)) < 3:
        t_in -= 30
    j = len(ts) - 1
    while j >= 0 and ds[j] >= 3:
        j -= 1
    t_out = max(ts[j] + 1 if j >= 0 else ts[0], t_close)
    assert ds[-1] >= 3 and ds[-1] >= ds[len(ts) // 2 + 1]
    return t_close, t_in, t_out


def wl_s(w):
    return [DIRNAME[tuple(w[0])], w[1], w[2]]


def make_fact(name, pieces, eaters, ins, outs, tref, kind='stage', t0=None, t_min_out=None, limit=4000, extra=None, span=2000):
    """Exact reaction: pieces (+ eater cells) at time t0 (a multiple of 30) with the input gliders
    `ins` (world lines) evolve in Delta generations to the pieces at t0 + Delta and exactly the
    gliders `outs` (world lines; [] = absorbed).  tref: a time near the reaction (for the scans)."""
    ES = envset(pieces, eaters)
    E = Env(ES)
    B = cycle_box(pieces, eaters)
    eb = bbox(ES)
    apps = {}
    for w in ins + outs:
        tc = tref if tref is not None else time_at(w, ((eb[0] + eb[2]) / 2, (eb[1] + eb[3]) / 2))
        apps[w] = approach(E, w, tc, span=span)
    if t0 is None:
        t0 = min(apps[w][1] for w in ins)
    assert t0 % 30 == 0
    G0 = gcells(pieces, eaters, t0)
    In = [gl(w, t0) for w in ins]
    InU = set().union(*In)
    assert sum(len(c) for c in In) == len(InU) == 5 * len(ins)
    dIn = min(E.dist(c) for c in In)
    assert dIn >= 3, (name, dIn)
    # the inputs arrive freely: from t0 - 600 the pieces + gliders evolve to G0 + In (exact)
    c = gcells(pieces, eaters, t0 - 600) | set().union(*[gl(w, t0 - 600) for w in ins])
    for _ in range(600):
        c = _step(c)
    assert c == G0 | InU, (name, 'free arrival')
    tlo = max([apps[w][2] for w in outs] + [apps[w][0] for w in ins] + [t0 + 1] + ([t_min_out] if t_min_out else []))
    c = G0 | InU
    R = bbox(c)
    t = t0
    Delta = None
    while t < t0 + limit:
        c = _step(c)
        t += 1
        R = hull(R, bbox(c))
        if t >= tlo:
            want = gcells(pieces, eaters, t)
            for w in outs:
                want = want | gl(w, t)
            if c == want:
                Delta = t - t0
                break
    assert Delta is not None, (name, 'no Delta')
    OutC = [gl(w, t0 + Delta) for w in outs]
    dOut = min([E.dist(o) for o in OutC] or [999])
    assert dOut >= 3, (name, dOut)
    GD = gcells(pieces, eaters, t0 + Delta)
    dG = min([min(Env(G0).dist(x) for x in In)] + [Env(GD).dist(o) for o in OutC])
    Rf = hull(R, B)
    f = {
        'name': name, 'kind': kind, 'frame': 'world frame of REG1 (cells (x, y), y down)',
        'pieces': [list(p) for p in pieces],
        'eater_cells': win(set(eaters)) if eaters else None,
        't0': t0,
        'G_note': 'G = union of the pieces at time t0 (t0 = 0 mod 30: every piece at phase 0 of the common clock) and the eater cells',
        'G_by_piece': [win(piece_cells(p, t0)) for p in pieces],
        'G': win(G0) if len(G0) < 3000 else None,
        'In': [{'wl': wl_s(w), 'cells': win(cc)} for w, cc in zip(ins, In)],
        'In_union': win(InU),
        'Delta': Delta, 'Delta_mod30': Delta % 30,
        'Out': [{'wl': wl_s(w), 'cells': win(cc)} for w, cc in zip(outs, OutC)],
        'Out_union': win(set().union(*OutC)) if OutC else None,
        'B': boxd(B), 'R': boxd(Rf), 'R_tight': boxd(R), 'B_in_R_tight': inbox(B, R),
        'dist_In_env': dIn, 'dist_Out_env': dOut if outs else None, 'dist_InOut_G': dG,
        'verified': 'evolve Delta (G u In) = (pieces at t0 + Delta) u Out, exact set simulation on the unbounded plane; also free arrival from t0 - 600',
    }
    if extra:
        f.update(extra)
    print('%-28s t0 %7d Delta %5d  in %s  out %s  B %s R %s  dIn %d dOut %s' % (
        name, t0, Delta, [wl(w) for w in ins], [wl(w) for w in outs], B, Rf, dIn, f['dist_Out_env']), flush=True)
    return f
