#!/usr/bin/env python3
"""Networks of pieces (R-22): gun assemblies (copies of `blockedStream`) and reflectors (copies of
RF0), the exact maps they induce on glider world lines, composites and their checks.

A *piece* is ('asm', k, vx, vy, s) or ('rf', k, p, q, s): `blockedStream`, respectively the
reflector RF0, transformed by sym_k, translated and delayed by s generations (machine.asm_cells,
g1_pull.rf_cells).  World lines are (d, lane, tau) as in common.py.

Provided here:
  * PG1: the certified pull-salvo generator of R-21 (`pullGenerator` of SalvoGenerator.lean);
  * move_piece / move_wl: translation by (u, v) and delay by s of pieces and world lines;
  * env_cells: all cells of a piece over a cycle; set_dist; glider_clearance (exact minimum
    Chebyshev distances between the cells of a glider in flight and a set of cells);
  * Net: a composite (period 30 asserted) with `react` (bit-parallel run, then the set simulator
    on the unbounded plane), `react_block` (set simulator with a block in place) and `trace`
    (set simulator with the envelope box of the whole reaction).
"""
from common import (glider_at, glider_worldline, transform, translate, bbox, step_cells, SE, SW, NW,
                    NE, DIRNAME, life, gates, counter, lean_window)
import machine
from machine import asm_cells, run_scheduled, verify_scheduled, bs1_cycle
from g1_pull import rf_cells, rf_cycle, RF0, RF_IN, RF_OUT
from reactions import shift_wl, sym_wl

# --- the certified generator PG1 (frame of SalvoGenerator.lean) --------------------------------
PG1 = [('asm', 0, 0, 0, 0), ('asm', 7, 90, 132, 25), ('asm', 2, 4, 121, 29),
       ('rf', 5, -32, 18, 0), ('rf', 7, -45, 67, 13), ('rf', 2, -4, 73, 0)]
PG1_NAMES = ['S', 'K', 'Gb', 'RF1', 'RF2', 'RF3']
PG1_C = (SE, 41, 22)                     # `pullGeneratorControl` = ofRows 32 (-9) [2, 4, 7] at time 150
PG1_A = (SE, -97, 1116)                  # the two gliders of translate (51, 143) pullSalvo at time 1320
PG1_B = (SE, -91, 1087)
PG1_N = 1170
REG = (51, 143)                          # registerBlock k = translate (51, 143) (counter k)


def register_block(k):
    return translate(set(counter(k)), *REG)


def piece_cells(p, t):
    if p[0] == 'asm':
        return asm_cells(p[1:], t)
    return rf_cells(p[1:], t)


def move_piece(p, u, v, s):
    """The piece translated by (u, v) and delayed by s generations."""
    return (p[0], p[1], p[2] + u, p[3] + v, (p[4] + s) % 30)


def move_wl(wl, u, v, s):
    return shift_wl(wl, u, v, s)


_ENV = {}


def env_cells(p):
    """All cells of the piece over a cycle."""
    key = (p[0], p[1])
    if key not in _ENV:
        cyc = bs1_cycle() if p[0] == 'asm' else rf_cycle()
        _ENV[key] = frozenset(transform(set().union(*cyc), p[1]))
    return translate(_ENV[key], p[2], p[3])


def env_box(p):
    key = ('box', p[0], p[1])
    if key not in _ENV:
        _ENV[key] = bbox(env_cells((p[0], p[1], 0, 0, 0)))
    b = _ENV[key]
    return (b[0] + p[2], b[1] + p[3], b[2] + p[2], b[3] + p[3])


def box_dist(a, b):
    return max(a[0] - b[2], b[0] - a[2], a[1] - b[3], b[1] - a[3], 0)


def set_dist(A, B, cap=10 ** 9):
    """Chebyshev distance between two finite sets of cells (exact)."""
    if len(A) > len(B):
        A, B = B, A
    bb = bbox(B)
    best = cap
    Bl = list(B)
    for (x, y) in A:
        if max(bb[0] - x, x - bb[2], bb[1] - y, y - bb[3]) >= best:
            continue
        for (a, b) in Bl:
            d = abs(x - a)
            e = abs(y - b)
            if e > d:
                d = e
            if d < best:
                best = d
    return best


def glider_path(wl, ta, tb):
    """All cells occupied by the glider at the times ta .. tb."""
    out = set()
    for t in range(int(ta), int(tb) + 1):
        out |= glider_at(*wl, t)
    return out


def glider_clearance(wl, ta, tb, cells):
    """Minimum Chebyshev distance between the glider (times ta .. tb) and a set of cells."""
    return set_dist(glider_path(wl, ta, tb), cells)


def time_at(g, pt):
    """Time at which the glider is nearest to the point pt."""
    d, lane, tau = g
    s = d[0] * pt[0] + d[1] * pt[1]
    q = (s + d[0] * d[1] * lane) / 2
    return tau + 4 * q


def seg_box_dist(wl, ta, tb, box):
    """Minimum Chebyshev distance between a box and the 5 x 5 boxes that contain the glider during
    the times ta .. tb (a lower bound for the distance of its cells)."""
    d, lane, tau = wl
    best = 10 ** 9
    for q in range((int(ta) - tau) // 4, (int(tb) - tau) // 4 + 1):
        x = d[0] * q
        y = d[0] * (d[1] * x - lane)
        dd = box_dist((x - 1, y - 1, x + 3, y + 3), box)
        if dd < best:
            best = dd
    return best


def asm_cross(p):
    """The point where the two streams of the assembly meet (the image of (45, 31))."""
    kx, ky = life.sym_apply(p[1], (45, 31))
    return (kx + p[2], ky + p[3])


class _Comp:
    def __init__(self, cells, margin):
        self.R = gates.Reference(cells, margin)


class Net:
    """A composite of pieces; asserts that the union is periodic with period 30."""

    def __init__(self, pieces, names=None, margin=20):
        self.pieces = list(pieces)
        self.names = list(names) if names else ['P%d' % i for i in range(len(pieces))]
        cells = set()
        for p in self.pieces:
            c = piece_cells(p, 0)
            if c & cells:
                raise ValueError('pieces overlap')
            cells |= c
        self.cells0 = cells
        self.comp = _Comp(cells, margin)            # AssertionError if not periodic
        self.env = self.comp.R.env

    def cycle(self, t):
        return set(self.comp.R.ref_cells[t % 30])

    def react(self, controls, limit=6000, t_hint=200, verify=True):
        """Returns (status, outs, Ts, Te): cycle(Ts) + controls -> cycle(Te) + outs, Ts = Te = 0
        (mod 30); verified with the set simulator when verify is set."""
        res = run_scheduled(self.comp, controls, limit=limit, t_hint=t_hint)
        if res['status'] != 'restored':
            return res['status'], None, None, None
        outs = sorted(w for (w, th) in res['out'])
        Ts = 30 * (res['t_first'] // 30)
        Te = 30 * ((res['t_end'] + 29) // 30)
        if verify:
            ok, Ts, Te = verify_scheduled(self.comp, controls, res)
            if not ok:
                return 'verification failed', outs, Ts, Te
        return 'ok', outs, Ts, Te

    def trace(self, controls, Ts, Te, extra=()):
        """Set simulator from cycle(Ts) + controls + extra for Te - Ts generations; returns the
        final cells and the box (xmin, ymin, xmax, ymax) over all generations."""
        c = self.cycle(Ts) | set(extra)
        for wl in controls:
            g = glider_at(*wl, Ts)
            assert life.chebyshev_dist(g, c) >= 3
            c |= g
        b = list(bbox(c))
        for _ in range(Te - Ts):
            c = step_cells(c)
            bb = bbox(c)
            b = [min(b[0], bb[0]), min(b[1], bb[1]), max(b[2], bb[2]), max(b[3], bb[3])]
        return c, tuple(b)

    def piece_distances(self):
        """[(name_i, name_j, distance of the envelopes)]"""
        envs = [env_cells(p) for p in self.pieces]
        boxes = [bbox(e) for e in envs]
        out = []
        for i in range(len(envs)):
            for j in range(i):
                bd = box_dist(boxes[i], boxes[j])
                d = bd if bd >= 40 else set_dist(envs[i], envs[j])
                out.append((self.names[j], self.names[i], d, bd >= 40))
        return out


def wlname(w):
    return '(%s, lane %d, tau %d)' % (DIRNAME[w[0]], w[1], w[2])


def pr(name, cells):
    b = bbox(cells)
    print('  %-34s %s   -- %d cells, box x %d..%d, y %d..%d' % (name + ':', lean_window(cells), len(cells), b[0], b[2], b[1], b[3]))


# --- reflectors as maps on world lines ---------------------------------------------------------
RF_IMG = [(sym_wl(RF_IN, k), sym_wl(RF_OUT, k)) for k in range(8)]
RF_TURN = {(i[0], o[0]): k for k, (i, o) in enumerate(RF_IMG)}


def reflect(g, dout, lane_out):
    """(piece, outgoing world line) for the copy of RF0 that turns the glider g into a glider of
    direction dout on lane_out; None if there is none (parity)."""
    k = RF_TURN.get((g[0], dout))
    if k is None:
        return None
    i0, o0 = RF_IMG[k]
    di, do = i0[0], o0[0]
    a1, b1, c1 = di[1], -di[0], g[1] - i0[1]
    a2, b2, c2 = do[1], -do[0], lane_out - o0[1]
    det = a1 * b2 - a2 * b1
    pn, qn = c1 * b2 - c2 * b1, a1 * c2 - a2 * c1
    if pn % det or qn % det:
        return None
    p, q = pn // det, qn // det
    s = g[2] - i0[2] + 4 * di[0] * p
    return ('rf', k, p, q, s % 30), shift_wl(o0, p, q, s)


def reflect_to(out, din, j):
    """(piece, incoming world line) for the copy of RF0 that emits exactly the glider `out` from a
    glider of direction din; j is the position along the outgoing lane (the translation of the
    copy is (p, q) with p = j)."""
    k = RF_TURN[(din, out[0])]
    i0, o0 = RF_IMG[k]
    do = o0[0]
    # lane_out = o0.lane + do[1] p - do[0] q
    p = j
    num = o0[1] + do[1] * p - out[1]
    q = num // do[0]
    s = out[2] - o0[2] + 4 * do[0] * p
    assert shift_wl(o0, p, q, s) == out
    return ('rf', k, p, q, s % 30), shift_wl(i0, p, q, s)


def rf_point(p):
    """Centre of the bounding box of a reflector piece."""
    b = env_box(p)
    return ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)


def free_run(pieces, gliders, t0, n):
    """Set simulator, unbounded plane: the pieces at time t0 (any phase) plus free gliders (world
    lines), n generations.  Returns the final set of cells."""
    c = set()
    for p in pieces:
        c |= piece_cells(p, t0)
    for w in gliders:
        c |= glider_at(*w, t0)
    for _ in range(n):
        c = step_cells(c)
    return c


def expect(pieces, gliders, t):
    c = set()
    for p in pieces:
        c |= piece_cells(p, t)
    for w in gliders:
        c |= glider_at(*w, t)
    return c


def insertion_ok(out, din, others, j=0, lead=260, n=560):
    """Does a copy of RF0 emit the glider `out` (input from direction din) while the gliders
    `others` (free, parallel) fly past?  Independent of j up to the phase of the reflector."""
    rf, gin = reflect_to(out, din, j)
    tc = time_at(out, rf_point(rf))
    t0 = int(tc) - lead
    end = free_run([rf], [gin] + list(others), t0, n)
    return end == expect([rf], [out] + list(others), t0 + n)


# --- composition of placements -----------------------------------------------------------------
def sym_mul(k1, k2):
    """Index of sym_k1 o sym_k2."""
    (a, b), (c, d) = life.SYMS[k1]
    (e, f), (g, h) = life.SYMS[k2]
    m = ((a * e + b * g, a * f + b * h), (c * e + d * g, c * f + d * h))
    return life.SYMS.index(m)


def compose(outer, inner):
    """The piece `inner` (given in the frame of the assembly `outer`'s own coordinates) in world
    coordinates: sym, translation and delay of `outer` applied to `inner`."""
    k1, v1, s1 = outer[1], (outer[2], outer[3]), outer[4]
    w = life.sym_apply(k1, (inner[2], inner[3]))
    return (inner[0], sym_mul(k1, inner[1]), v1[0] + w[0], v1[1] + w[1], (s1 + inner[4]) % 30)


def wl_out(wl, piece):
    """World line (own coordinates of the assembly `piece`) in world coordinates."""
    return machine.wl_map(wl, piece[1:])


def wl_in(wl, piece):
    return machine.wl_unmap(wl, piece[1:])


# --- which salvos can be assembled by reflectors -----------------------------------------------
def insertion_clear(out, others):
    """Rule read off `insertion_ok` (scan: x1_insertion.py, results/x1_insertion.txt): the glider out = (lane, tau) can be
    inserted by a reflector while the gliders `others` (already in flight, all on one side, 4 or
    more lanes away) pass, iff no other glider has tau' - tau in the forbidden window."""
    L, t = out
    if not others:
        return 'any'
    if all(o[0] <= L - 4 for o in others):          # L-type: input NE, others to the left
        for (l, tt) in others:
            d = L - l
            if -13 <= tt - t <= (21 if d < 6 else 23):
                return None
        return 'L'
    if all(o[0] >= L + 4 for o in others):          # R-type: input SW, others to the right
        for (l, tt) in others:
            d = l - L
            if -13 - 4 * d <= tt - t <= (21 if d < 6 else 23) - 4 * d:
                return None
        return 'R'
    return None


def assembly_orders(new, fixed=()):
    """All orders in which the gliders `new` [(lane, tau)] can be inserted one after the other
    downstream of the gliders `fixed`: list of [(glider, type)]."""
    import itertools
    out = []
    for order in itertools.permutations(new):
        present = list(fixed)
        seq = []
        for g in order:
            ty = insertion_clear(g, present)
            if ty is None:
                seq = None
                break
            seq.append((g, ty))
            present.append(g)
        if seq:
            out.append(seq)
    return out
