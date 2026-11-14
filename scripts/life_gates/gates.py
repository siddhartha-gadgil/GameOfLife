#!/usr/bin/env python3
"""Common code for the gate searches: periodic reference of a blocked stream, insertion of
control gliders, and classification of the outcome.

Time convention for gates: gate time 0 is the reference generation `tref` of the blocked stream
(a multiple of 30 not smaller than its transient); `ref[i]` is the periodic configuration at gate
time i (mod 30).  A control glider is given by its world line (d, lane, tau) in gate time, see
life.py.
"""
import life
from life import (Board, bbox, transform, translate, gun_phase, components, glider_worldline,
                  glider_at, sym_apply, popcount)

MARGIN = 30      # board = envelope of the blocked stream + MARGIN
INNER = 5        # gliders are recognised outside envelope + INNER ...
MID = 13         # ... and removed ("harvested") once outside envelope + MID and flying away


def phases(p):
    return (0, p) if p >= 0 else (-p, 0)


def gun_at(p):
    """The gun after p generations (any p >= 0), with its gliders in flight."""
    c = set(gun_phase(p % 30))
    for j in range(p // 30):
        c |= glider_at((1, 1), 14, -61, p - 30 * j)
    return c


def initial_cells(k, dx, dy, p):
    pA, pB = phases(p)
    return gun_at(pA) | translate(transform(gun_at(pB), k), dx, dy)


def blocked_cycle(k, dx, dy, p):
    """(cells of the periodic configuration at its reference time tref, tref, transient) for the
    blocked stream (k, dx, dy, p) of s2_blocked.py; tref is the first multiple of 30 that is not
    smaller than the transient."""
    init = initial_cells(k, dx, dy, p)
    x0, y0, x1, y1 = bbox(init)
    m = 90      # generous: the crossing point may lie outside the box of the guns
    bd = Board(x0 - m, y0 - m, x1 - x0 + 1 + 2 * m, y1 - y0 + 1 + 2 * m)
    r = life.run_periodic(bd, bd.of_cells(init), tmax=3000, periods=(30,), give_up=1500)
    if r['status'] != 'periodic':
        raise ValueError('not a blocked stream: %r' % (r,))
    tref = ((r['transient'] + 29) // 30) * 30
    return bd.to_cells(r['hist'][tref]), tref, r['transient']


class Reference:
    """A period-30 configuration (given by its cells at gate time 0) prepared for gate runs."""

    def __init__(self, cells0, margin=MARGIN):
        cyc = [set(cells0)]
        for i in range(30):
            cyc.append(life.step_cells(cyc[-1]))
        assert cyc[30] == cyc[0], 'not periodic with period 30'
        cyc = cyc[:30]
        allc = set().union(*cyc)
        self.env = bbox(allc)
        ex0, ey0, ex1, ey1 = self.env
        self.board = Board(ex0 - margin, ey0 - margin, ex1 - ex0 + 1 + 2 * margin,
                           ey1 - ey0 + 1 + 2 * margin)
        b = self.board
        self.ref_cells = cyc
        self.ref = [b.of_cells(c) for c in cyc]
        for i in range(30):
            assert b.step(self.ref[i]) == self.ref[(i + 1) % 30]
        self.refdil = [b.dilate(g, 2) for g in self.ref]
        self.inner = b.rect_mask(ex0 - INNER, ey0 - INNER, ex1 + INNER, ey1 + INNER)
        self.mid_box = (ex0 - MID, ey0 - MID, ex1 + MID, ey1 + MID)
        self.mid = b.rect_mask(*self.mid_box)
        # stream world lines (gate time), from the gliders in flight in the cycle
        st = set()
        for i in range(30):
            for comp in components(cyc[i], 2):
                wl = glider_worldline(comp, i)
                if wl is not None:
                    st.add((wl[0], wl[1], wl[2] % 30))
        self.streams = sorted(st)

    @classmethod
    def blocked(cls, k, dx, dy, p, margin=MARGIN):
        cells, tref, transient = blocked_cycle(k, dx, dy, p)
        R = cls(cells, margin)
        R.spec = (k, dx, dy, p)
        R.tref = tref
        R.transient = transient
        return R

    def stream_name(self, wl):
        """'A' for a glider on a stream world line of direction (1, 1) (gun A), 'B' for a
        glider on another stream world line (gun B); None otherwise."""
        key = (wl[0], wl[1], wl[2] % 30)
        if key in self.streams:
            return 'A' if wl[0] == (1, 1) else 'B'
        return None


def glider_times(board, d, lane, tau):
    """The interval of gate times at which the glider is inside the board (margin 3)."""
    dx, dy = d
    qs = []
    for q in range(-2000, 2000):
        x = dx * q
        y = dx * (dy * x - lane)
        if board.contains(x - 1, y - 1, 3) and board.contains(x + 3, y + 3, 3):
            qs.append(q)
    if not qs:
        return None
    return (tau + 4 * min(qs), tau + 4 * max(qs) + 3)


def free_intervals(R, d, lane, tau):
    """Maximal intervals [s, e] of gate times at which the ideal glider is at Chebyshev distance
    >= 3 from the reference cycle (so that the union evolves independently for one step).
    Returns (list of intervals, t_enter, t_exit)."""
    tt = glider_times(R.board, d, lane, tau)
    if tt is None:
        return [], None, None
    b = R.board
    out = []
    cur = None
    for t in range(tt[0], tt[1] + 1):
        c = b.of_cells(glider_at(d, lane, tau, t))
        if c & R.refdil[t % 30]:
            if cur is not None:
                out.append((cur, t - 1))
                cur = None
        else:
            if cur is None:
                cur = t
    if cur is not None:
        out.append((cur, tt[1]))
    return out, tt[0], tt[1]


def outward(R, comp, d):
    """Is the glider `comp` with direction d outside the mid box on a side it is flying towards?"""
    x0, y0, x1, y1 = bbox(comp)
    mx0, my0, mx1, my1 = R.mid_box
    return ((d[0] > 0 and x0 > mx1) or (d[0] < 0 and x1 < mx0) or
            (d[1] > 0 and y0 > my1) or (d[1] < 0 and y1 < my0))


def run_gate(R, gliders, t_ins, limit=900, watch=None):
    """Insert the control gliders (world lines) into the reference at gate time t_ins and evolve.

    Gliders flying away are removed and recorded.  Returns a dict:
      status 'restored': the configuration is again the reference cycle at gate time 't_end' and
                         'out' lists the removed gliders (world line, time of removal);
             'ring' / 'timeout' / 'debris': failure ('debris': something other than a single
                         glider was found more than MID cells outside the envelope).
      'watch': if watch = (t, cells) is given, whether the state at gate time t was exactly
               reference + cells (used to chain free intervals).
    """
    b = R.board
    g = R.ref[t_ins % 30]
    for wl in gliders:
        c = b.of_cells(glider_at(*wl, t_ins))
        assert not (c & R.refdil[t_ins % 30]), 'control glider not free at insertion'
        g |= c
    t = t_ins
    out = []
    step = b.step
    mid = R.mid
    res = {'watch': None}
    hist = {t: g}
    while t < t_ins + limit:
        if watch is not None and t == watch[0]:
            res['watch'] = (g == (R.ref[t % 30] | b.of_cells(watch[1])))
        if g == R.ref[t % 30]:
            res['status'] = 'restored'
            res['t_end'] = t
            res['out'] = out
            res['hist'] = hist
            return res
        if g & ~mid:
            if b.on_ring(g):
                res['status'] = 'ring'
                res['t'] = t
                return res
            cells = b.to_cells(g & ~R.inner)
            for comp in components(cells, 2):
                cm = b.of_cells(comp)
                if not (cm & ~mid):
                    continue                    # still near the assembly
                wl = glider_worldline(comp, t)
                if wl is None:
                    res['status'] = 'debris'    # something that is not a glider, far outside
                    res['t'] = t
                    return res
                if outward(R, comp, wl[0]):
                    out.append((wl, t))
                    g &= ~cm
            hist[t] = g
            if g == R.ref[t % 30]:
                continue
        g = step(g)
        t += 1
        hist[t] = g
    res['status'] = 'timeout'
    return res


def back_time(R, res, t_ins):
    """The first gate time T such that for all t >= T (up to the end of the run) the configuration
    is exactly  reference(t) + the escaping gliders in free flight (each at Chebyshev distance >= 3
    from everything else)."""
    b = R.board
    hist = res['hist']
    out = res['out']
    T = res['t_end']
    t = T
    while t > t_ins:
        s = t - 1
        g = hist[s]
        ok = True
        acc = R.ref[s % 30]
        for (wl, th) in out:
            if th > s:           # not yet removed at time s
                c = b.of_cells(glider_at(*wl, s))
                if (c & g) != c or (b.dilate(c, 2) & acc):
                    ok = False
                    break
                acc |= c
        if ok:
            rest = g
            for (wl, th) in out:
                if th > s:
                    rest &= ~b.of_cells(glider_at(*wl, s))
            ok = (rest == R.ref[s % 30])
        if not ok:
            break
        t = s
    return t


def verify_gate(R, gliders, t_ins, out, t_check, pad=None):
    """Independent check with the set simulator on the unbounded plane: reference(t_ins) plus the
    control gliders evolves, after t_check - t_ins generations, to reference(t_check) plus the
    gliders `out` (world lines) in free flight."""
    c = set(R.ref_cells[t_ins % 30])
    for wl in gliders:
        c |= glider_at(*wl, t_ins)
    for _ in range(t_check - t_ins):
        c = life.step_cells(c)
    expect = set(R.ref_cells[t_check % 30])
    for wl in out:
        gl = glider_at(*wl, t_check)
        assert not (gl & expect)
        expect |= gl
    return c == expect
