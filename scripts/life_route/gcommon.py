#!/usr/bin/env python3
"""Shared data of the g* scripts (R-29): DZ2 of R-28 (scripts/life_zero, read-only) and REG1 (R-24),
world frame of REG1; helpers to build and check runs with the fast simulator gsim."""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
for sub in ('life_machine', 'life_zero', 'life_gates'):
    p = os.path.join(HERE, '..', sub)
    if p not in sys.path:
        sys.path.append(p)
from common import SE, SW, NE, NW, DIRNAME, glider_at, translate, counter, bbox, lean_window, step_cells  # noqa
from net import piece_cells, env_cells, time_at, glider_path, reflect, reflect_to, RF_IMG, shift_wl  # noqa
import f0_frozen  # noqa
import f8_full    # noqa
from gsim import Sim  # noqa

RES = os.path.join(HERE, 'results')


def block(k):
    return set(translate(set(counter(k)), 148, 240))


def blocks(k0=-1, k1=600):
    b = set()
    for k in range(k0, k1 + 1):
        b |= block(k)
    return b


def dz2():
    """(pieces, data) of the complete DZ2 (R-28), exactly as f8_full.py builds it."""
    d = f8_full.design()
    pieces = f0_frozen.frozen_pieces() + [d['rfr']] + d['supply'] + d['zb']
    return pieces, d


def reg1():
    return f0_frozen.reg1_pieces()


def state(pieces, gliders, t, extra=()):
    c = set(extra)
    for p in pieces:
        c |= piece_cells(p, t)
    for w in gliders:
        c |= glider_at(*w, t)
    return c


def run(pieces, gliders, t0, t1, extra=(), box=None, margin=300, check_dist=3):
    """Evolve the pieces (phase at t0) + gliders + extra from t0 to t1 (exact, unbounded plane).
    Returns the final cell set."""
    c = state(pieces, (), t0, extra)
    for w in gliders:
        g = glider_at(*w, t0)
        c |= g
    if box is None:
        b = bbox(c)
        box = (b[0] - 7000, b[1] - 7000, b[2] + 7000, b[3] + 7000)
    S = Sim(c, box, margin)
    S.run(t1 - t0)
    return S.cells(), S.runbox()


def wl(w):
    return '(%s, %d, %d)' % (DIRNAME[w[0]], w[1], w[2])


def _sep_forever(b1, v1, b2, v2, gap=6):
    for ax in (0, 1):
        lo1, hi1, lo2, hi2 = b1[ax], b1[ax + 2], b2[ax], b2[ax + 2]
        if lo2 - hi1 >= gap and v2[ax] - v1[ax] >= 0:
            return True
        if lo1 - hi2 >= gap and v1[ax] - v2[ax] >= 0:
            return True
    return False


def core_box(pieces, extra_boxes=(), margin=60):
    from net import env_box
    bs = [env_box(p) for p in pieces] + list(extra_boxes)
    return (min(b[0] for b in bs) - margin, min(b[1] for b in bs) - margin,
            max(b[2] for b in bs) + margin, max(b[3] for b in bs) + margin)


def run_peel(pieces, gliders, t0, t1, extra=(), cbox=None, chunk=240, grid_margin=700):
    """Exact evolution on the unbounded plane, from t0 to t1, of the pieces + gliders + extra, where a
    free glider that is outside the box `cbox` (which contains all pieces and the register diagonal)
    and moves away from it is removed and recorded (it can never come back).  Returns
    (final cells, removed world lines).  Removed gliders are checked pairwise never to meet."""
    from common import components, glider_worldline
    if cbox is None:
        cbox = core_box(pieces, [(140, 230, 900, 900)])
    c = state(pieces, gliders, t0, extra)
    gbox = (cbox[0] - grid_margin, cbox[1] - grid_margin, cbox[2] + grid_margin, cbox[3] + grid_margin)
    # input gliders may start far outside: enlarge the grid to contain them
    b = bbox(c)
    gbox = (min(gbox[0], b[0] - 100), min(gbox[1], b[1] - 100), max(gbox[2], b[2] + 100), max(gbox[3], b[3] + 100))
    S = Sim(c, gbox, 64)
    t = t0
    removed = []   # (wl, box at time t, t)
    while t < t1:
        n = min(chunk, t1 - t)
        S.run(n)
        t += n
        cells = S.cells()
        out = [x for x in cells if not (cbox[0] <= x[0] <= cbox[2] and cbox[1] <= x[1] <= cbox[3])]
        if not out:
            continue
        drop = set()
        for comp in components(set(out), 2):
            bb = bbox(comp)
            if min(abs(bb[0] - cbox[0]), abs(bb[2] - cbox[2]), abs(bb[1] - cbox[1]), abs(bb[3] - cbox[3])) < 8:
                continue      # touching the edge of the core box: decide later
            w = glider_worldline(comp, t)
            if w is None:
                continue
            if _sep_forever(bb, w[0], cbox, (0, 0), gap=8):
                # its neighbourhood (radius 2) must be free of other cells
                if any((x + dx, y + dy) in cells and (x + dx, y + dy) not in comp
                       for (x, y) in comp for dx in (-2, -1, 0, 1, 2) for dy in (-2, -1, 0, 1, 2)):
                    continue
                removed.append((w, bb, t))
                drop |= comp
        if drop:
            S.set(cells - drop)
    # removed gliders pairwise: bring them to a common time and check separation
    for i in range(len(removed)):
        for j in range(i):
            (w1, _, _), (w2, _, _) = removed[i], removed[j]
            g1, g2 = glider_at(*w1, t1 + 400), glider_at(*w2, t1 + 400)
            ok = _sep_forever(bbox(g1), w1[0], bbox(g2), w2[0], gap=4)
            if not ok:
                # they might have been far apart in the past only; check directly forward in time
                raise RuntimeError('removed gliders may meet: %s %s' % (w1, w2))
    return S.cells(), sorted(r[0] for r in removed)


def run_events(cells, t0, events, t_end, cbox):
    """Exact evolution from the cell set `cells` at time t0 to t_end; each event (t, w) inserts the
    glider w at time t (checked >= 4 from everything).  Escaping gliders are peeled (run_peel).
    Returns (cells, removed world lines) or raises if an insertion conflicts."""
    from life import chebyshev_dist
    t = t0
    removed = []
    ev = sorted(events)
    while True:
        tn = min(ev[0][0], t_end) if ev else t_end
        if tn > t:
            cells, rem = run_peel([], [], t, tn, extra=cells, cbox=cbox)
            removed += rem
            t = tn
        if not ev or t >= t_end:
            return cells, sorted(removed)
        _, w = ev.pop(0)
        g = glider_at(*w, t)
        if chebyshev_dist(g, cells) < 4:
            raise RuntimeError('insertion conflict %s at %d' % (w, t))
        cells = cells | g


def eater_absorbing(w, near, far=0, avoid=()):
    """An eater-1 placement (cells) that absorbs the glider w near the point `near`, cleanly."""
    from common import transform, EATER1
    from reactions import run_free
    from net import set_dist
    for k in range(8):
        e0 = transform(set(EATER1), k)
        mx, my = min(x for x, y in e0), min(y for x, y in e0)
        for u in range(-6, 7):
            for v in range(-6, 7):
                e = translate(e0, near[0] + u - mx, near[1] + v - my)
                tt = int(time_at(w, near))
                g = glider_at(*w, tt - 40)
                if min(max(abs(a - c), abs(b - d)) for (a, b) in g for (c, d) in e) < 4:
                    continue
                st, t, rest, gl = run_free([w], extra=e, t0=tt - 40, max_gen=300)
                if st == 'settled' and set(rest) == set(e) and not gl:
                    if avoid and set_dist(e, avoid) < far:
                        continue
                    return set(e)
    return None
