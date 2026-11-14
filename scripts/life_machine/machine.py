#!/usr/bin/env python3
"""Composites of blocked-stream assemblies (copies of BS1 = `blockedStream` of Gates.lean).

An *assembly* is (k, vx, vy, s): the periodic cycle of BS1, transformed by the symmetry sym_k of
life.py, translated by (vx, vy) and delayed by s generations, i.e. at world time t it is
    translate (vx, vy) (sym_k (evolve ((t - s) mod 30) blockedStream)).
A glider world line w in the coordinates of BS1 ("gate time", gate time 0 = `blockedStream`)
becomes `wl_map(w, asm)` in world coordinates.

The catalogue of reactions of BS1 with one control glider is the result file of
scripts/life_gates/s3_gate.py (read-only): results/s3_gate_4_90_1_0.json.gz.
"""
import gzip
import json
import os

from common import (HERE, life, gates, BLOCKED_STREAM, step_cells, translate, transform, bbox,
                    glider_at, glider_worldline, components, lean_window, show, SE, SW, NW, NE,
                    DIRNAME, GUN, GUN_B)

CATALOG_FILE = os.path.join(HERE, '..', 'life_gates', 'results', 's3_gate_4_90_1_0.json.gz')
SERIES_FILE = os.path.join(HERE, '..', 'life_gates', 'results', 's4_series_4_90_1_0.json.gz')

_cycle = None


def bs1_cycle():
    """The 30 configurations of the cycle of BS1 (index = gate time mod 30)."""
    global _cycle
    if _cycle is None:
        c = [set(BLOCKED_STREAM)]
        for _ in range(29):
            c.append(step_cells(c[-1]))
        assert step_cells(c[-1]) == c[0]
        _cycle = [frozenset(x) for x in c]
    return _cycle


def asm_cells(asm, t):
    k, vx, vy, s = asm
    return translate(transform(bs1_cycle()[(t - s) % 30], k), vx, vy)


def asm_envelope(asm):
    k, vx, vy, s = asm
    allc = set().union(*bs1_cycle())
    return bbox(translate(transform(allc, k), vx, vy))


def asm_guns(asm, t=0):
    """(gun A cells, gun B cells) of the assembly at world time t (bodies with forming gliders:
    the rows of the gun bodies of the cycle configuration)."""
    k, vx, vy, s = asm
    c = bs1_cycle()[(t - s) % 30]
    A = {p for p in c if p[0] <= 35 and p[1] <= 8}
    B = {p for p in c if p[0] >= 55 and p[1] <= 9}
    return (translate(transform(A, k), vx, vy), translate(transform(B, k), vx, vy))


def wl_map(wl, asm):
    """World line in world coordinates of the glider with world line `wl` in BS1 coordinates."""
    k, vx, vy, s = asm
    t = 0
    c = translate(transform(glider_at(*wl, t), k), vx, vy)
    return glider_worldline(c, t + s)


def wl_unmap(wl, asm):
    """Inverse of wl_map."""
    k, vx, vy, s = asm
    kinv = {0: 0, 1: 3, 2: 2, 3: 1, 4: 4, 5: 5, 6: 6, 7: 7}[k]
    t = 0
    c = transform(translate(glider_at(*wl, t), -vx, -vy), kinv)
    return glider_worldline(c, t - s)


def load_catalog():
    """Records of s3_gate for BS1, with 'repeat' (list of repetition tests passed) merged in for
    the gates from infinity."""
    d = json.load(gzip.open(CATALOG_FILE, 'rt'))
    recs = d['records']
    rep = {}
    if os.path.exists(SERIES_FILE):
        for r in json.load(gzip.open(SERIES_FILE, 'rt'))['repeat']:
            rep[(tuple(r['d']), r['lane'], r['tau'])] = r['repeat']
    for r in recs:
        r['d'] = tuple(r['d'])
        r['wl'] = (r['d'], r['lane'], r['tau'])
        r['outs'] = [((tuple(o[0]), o[1], o[2]), o[3]) for o in r['out']]
        r['repeat'] = rep.get(r['wl'], []) if r['from_infinity'] else []
    return recs


def box_dist(a, b):
    dx = max(a[0] - b[2], b[0] - a[2], 0)
    dy = max(a[1] - b[3], b[1] - a[3], 0)
    return max(dx, dy)


def lane_box_dist(wl, box):
    """Minimum Chebyshev distance between the cells swept by a glider on the world line `wl`
    (all times) and a box."""
    d, lane, tau = wl
    best = None
    cx = (box[0] + box[2]) // 2
    span = (box[2] - box[0]) + (box[3] - box[1]) + 40
    for q in range(d[0] * cx - span, d[0] * cx + span + 1):
        x = d[0] * q
        y = d[0] * (d[1] * x - lane)
        # the glider occupies, during 4 generations, cells within the box (x-1 .. x+3, y-1 .. y+3)
        g = (x - 1, y - 1, x + 3, y + 3)
        dd = box_dist(g, box)
        if best is None or dd < best:
            best = dd
    return best


class Composite:
    """A union of assemblies (and optional still lifes), checked to be periodic with period 30."""

    def __init__(self, asms, extra=(), margin=30):
        self.asms = list(asms)
        self.extra = set(extra)
        cells = set(self.extra)
        for a in self.asms:
            c = asm_cells(a, 0)
            assert not (c & cells), 'assemblies overlap'
            cells |= c
        self.R = gates.Reference(cells, margin)        # asserts period 30
        self.envs = [asm_envelope(a) for a in self.asms]

    def min_separation(self):
        best = None
        for i in range(len(self.envs)):
            for j in range(i):
                dd = box_dist(self.envs[i], self.envs[j])
                if best is None or dd < best:
                    best = dd
        return best

    def run(self, controls, t_ins, limit=4000):
        """Insert control gliders (world lines) at world time t_ins; evolve until the composite is
        back in its cycle.  Returns (status, t_back, outs) with outs the world lines of the
        gliders that left; the result is re-checked with the set simulator when `restored`."""
        R = self.R
        res = gates.run_gate(R, controls, t_ins, limit=limit)
        if res['status'] != 'restored':
            return res['status'], None, None
        outs = sorted(w for (w, th) in res['out'])
        tb = gates.back_time(R, res, t_ins)
        return 'restored', tb, outs

    def verify(self, controls, t_start, outs, t_end):
        """Set simulator, unbounded plane: cycle(t_start) + controls -> cycle(t_end) + outs."""
        return gates.verify_gate(self.R, controls, t_start, outs, t_end)

    def free_start(self, controls, t_max):
        """The largest t <= t_max, t = 0 (mod 30), at which every control glider is at Chebyshev
        distance >= 3 from the cycle (and from the other controls)."""
        R = self.R
        b = R.board
        t = 30 * (t_max // 30)
        for _ in range(400):
            try:
                acc = R.ref[0]
                ok = True
                for wl in controls:
                    c = b.of_cells(glider_at(*wl, t))
                    if b.dilate(c, 2) & acc:
                        ok = False
                        break
                    acc |= c
                if ok:
                    return t
            except ValueError:
                return None
            t -= 30
        return None


def entry_time(env, wl, gap=4, t_hint=0, span=40000):
    """The last time before the glider `wl` first comes within Chebyshev distance < gap of the
    box env (None if it never does within t_hint +- span)."""
    d, lane, tau = wl
    # scan the canonical parameter q (4 generations each)
    q0 = (t_hint - span - tau) // 4
    q1 = (t_hint + span - tau) // 4
    for q in range(q0, q1 + 1):
        x = d[0] * q
        y = d[0] * (d[1] * x - lane)
        if box_dist((x - 1, y - 1, x + 3, y + 3), env) < gap:
            return tau + 4 * q - 1
    return None


def run_scheduled(comp, controls, limit=6000, t_hint=0):
    """Like gates.run_gate, but every control glider is inserted at its own entry time (just
    before it comes within distance 4 of the envelope of the whole composite), so that control
    gliders far apart in time can be used.  Returns a dict: status 'restored' (with t_first = the
    first insertion time, t_end, out = [(world line, time of removal)]), or a failure status."""
    R = comp.R
    b = R.board
    sched = []
    for wl in controls:
        te = entry_time(R.env, wl, 4, t_hint)
        if te is None:
            return {'status': 'no-entry'}
        sched.append((te, wl))
    sched.sort()
    t = sched[0][0]
    g = R.ref[t % 30]
    out = []
    mid = R.mid
    step = b.step
    pending = list(sched)
    t_stop = sched[-1][0] + limit
    pop_cap = max(life.popcount(x) for x in R.ref) + 5 * len(controls) + 600
    while t < t_stop:
        if t % 64 == 0 and life.popcount(g) > pop_cap:
            return {'status': 'explosion', 't': t}
        while pending and pending[0][0] == t:
            c = b.of_cells(glider_at(*pending[0][1], t))
            if b.dilate(c, 2) & g:
                return {'status': 'blocked-entry', 't': t}
            g |= c
            pending.pop(0)
        if not pending and g == R.ref[t % 30]:
            return {'status': 'restored', 't_first': sched[0][0], 't_end': t, 'out': out}
        if g & ~mid:
            if b.on_ring(g):
                return {'status': 'ring', 't': t}
            cells = b.to_cells(g & ~R.inner)
            for cc in components(cells, 2):
                cm = b.of_cells(cc)
                if not (cm & ~mid):
                    continue
                wl = glider_worldline(cc, t)
                if wl is None:
                    return {'status': 'debris', 't': t}
                if gates.outward(R, cc, wl[0]):
                    out.append((wl, t))
                    g &= ~cm
            if not pending and g == R.ref[t % 30]:
                continue
        g = step(g)
        t += 1
    return {'status': 'timeout'}


def verify_scheduled(comp, controls, res):
    """Set simulator on the unbounded plane: cycle(Ts) + all control gliders (free, far away)
    evolves in N = Te - Ts generations to cycle(Te) + the output gliders; Ts, Te = 0 (mod 30).
    Returns (ok, Ts, Te)."""
    R = comp.R
    Ts = 30 * (res['t_first'] // 30)
    Te = 30 * ((res['t_end'] + 29) // 30)
    c = set(R.ref_cells[0])
    for wl in controls:
        gl = glider_at(*wl, Ts)
        if life.chebyshev_dist(gl, c) < 3:
            return False, Ts, Te
        c |= gl
    for _ in range(Te - Ts):
        c = step_cells(c)
    expect = set(R.ref_cells[0])
    for (wl, th) in res['out']:
        gl = glider_at(*wl, Te)
        if life.chebyshev_dist(gl, expect) < 3:
            return False, Ts, Te
        expect |= gl
    return c == expect, Ts, Te
