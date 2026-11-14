#!/usr/bin/env python3
"""Dependency-free Game of Life simulator for the gun-gate searches (untrusted oracle).

Conventions (those of the Lean project):
  * a cell is (x, y), x to the right, y DOWNWARD;
  * a window is (x0, y0, rows): rows is a list of naturals, top row first, and bit j of rows[i]
    (least significant bit = leftmost cell) is the cell (x0 + j, y0 + i).

Two simulators are provided:
  * `step_cells`  -- a reference simulator on sets of cells (unbounded plane);
  * `Board`       -- a bit-parallel simulator on a finite rectangle, the whole rectangle being
                     one Python integer.  A Board is faithful to the unbounded plane as long as
                     no live cell lies on the outermost ring of the rectangle; `Board.on_ring`
                     tests this and every search treats a hit as "left the box".

Run `python3 life.py` for the self test (cross-check against LeanTheory/Theory/Life/Guns.lean).
"""

# --------------------------------------------------------------------------------------------
# Windows and cell sets
# --------------------------------------------------------------------------------------------

def cells_of_window(x0, y0, rows):
    """The set of cells of the window (x0, y0, rows)."""
    out = set()
    for i, r in enumerate(rows):
        j = 0
        while r:
            if r & 1:
                out.add((x0 + j, y0 + i))
            r >>= 1
            j += 1
    return out


def window_of_cells(cells):
    """The trimmed window (x0, y0, rows) of a nonempty set of cells."""
    cells = list(cells)
    if not cells:
        return (0, 0, [])
    x0 = min(c[0] for c in cells)
    y0 = min(c[1] for c in cells)
    y1 = max(c[1] for c in cells)
    rows = [0] * (y1 - y0 + 1)
    for (x, y) in cells:
        rows[y - y0] |= 1 << (x - x0)
    return (x0, y0, rows)


def bbox(cells):
    """Bounding box (xmin, ymin, xmax, ymax), inclusive."""
    xs = [c[0] for c in cells]
    ys = [c[1] for c in cells]
    return (min(xs), min(ys), max(xs), max(ys))


def translate(cells, dx, dy):
    return {(x + dx, y + dy) for (x, y) in cells}


# The 8 symmetries of the square as integer matrices ((a, b), (c, d)): (x, y) -> (ax+by, cx+dy).
# With y downward, the image of the direction (1, 1) is listed on the right.
SYMS = [
    ((1, 0), (0, 1)),    # 0 identity            (1, 1)
    ((0, -1), (1, 0)),   # 1 (x,y) -> (-y, x)    (-1, 1)
    ((-1, 0), (0, -1)),  # 2 (x,y) -> (-x,-y)    (-1,-1)
    ((0, 1), (-1, 0)),   # 3 (x,y) -> (y, -x)    (1, -1)
    ((-1, 0), (0, 1)),   # 4 (x,y) -> (-x, y)    (-1, 1)
    ((1, 0), (0, -1)),   # 5 (x,y) -> (x, -y)    (1, -1)
    ((0, 1), (1, 0)),    # 6 (x,y) -> (y, x)     (1, 1)
    ((0, -1), (-1, 0)),  # 7 (x,y) -> (-y,-x)    (-1,-1)
]


def sym_apply(k, v):
    (a, b), (c, d) = SYMS[k]
    return (a * v[0] + b * v[1], c * v[0] + d * v[1])


def transform(cells, k):
    """Image of a set of cells under the symmetry number k (no normalisation)."""
    (a, b), (c, d) = SYMS[k]
    return {(a * x + b * y, c * x + d * y) for (x, y) in cells}


def normalize(cells):
    """Translate so that the bounding box starts at (0, 0)."""
    x0, y0, _, _ = bbox(cells)
    return translate(cells, -x0, -y0)


def show(cells, pad=0):
    """A picture: O alive, . dead."""
    if not cells:
        return "(empty)"
    x0, y0, x1, y1 = bbox(cells)
    lines = []
    for y in range(y0 - pad, y1 + pad + 1):
        lines.append("".join("O" if (x, y) in cells else "." for x in range(x0 - pad, x1 + pad + 1)))
    return "\n".join(lines)


def fmt_window(w):
    return "ofRows %d %d [%s]" % (w[0], w[1], ", ".join(str(r) for r in w[2]))


def lean_window(cells):
    """`ofRows x0 y0 [rows]` for a set of cells."""
    if not cells:
        return "∅"
    return fmt_window(window_of_cells(cells))


# --------------------------------------------------------------------------------------------
# Reference simulator on sets
# --------------------------------------------------------------------------------------------

def step_cells(cells):
    """One generation of Conway's rule B3/S23 on the unbounded plane."""
    cnt = {}
    for (x, y) in cells:
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                if dx or dy:
                    k = (x + dx, y + dy)
                    cnt[k] = cnt.get(k, 0) + 1
    return {c for c, n in cnt.items() if n == 3 or (n == 2 and c in cells)}


def evolve_cells(cells, n):
    for _ in range(n):
        cells = step_cells(cells)
    return cells


# --------------------------------------------------------------------------------------------
# Bit-parallel simulator on a rectangle
# --------------------------------------------------------------------------------------------

class Board:
    """A rectangle x0 <= x < x0 + W, y0 <= y < y0 + H; the state is one integer, the cell (x, y)
    being bit (y - y0) * W + (x - x0)."""

    def __init__(self, x0, y0, W, H):
        self.x0, self.y0, self.W, self.H = x0, y0, W, H
        row = ((1 << (W - 2)) - 1) << 1           # columns 1 .. W-2
        m = 0
        for i in range(1, H - 1):
            m |= row << (i * W)
        self.mask = m                             # the interior
        inner_row = ((1 << (W - 4)) - 1) << 2     # columns 2 .. W-3
        inner = 0
        for i in range(2, H - 2):
            inner |= inner_row << (i * W)
        self.ring = m & ~inner                    # outermost layer of the interior

    def bit(self, x, y):
        return 1 << ((y - self.y0) * self.W + (x - self.x0))

    def contains(self, x, y, margin=2):
        return (self.x0 + margin <= x < self.x0 + self.W - margin and
                self.y0 + margin <= y < self.y0 + self.H - margin)

    def of_cells(self, cells):
        g = 0
        W, x0, y0 = self.W, self.x0, self.y0
        for (x, y) in cells:
            if not self.contains(x, y, 1):
                raise ValueError("cell %r outside the board" % ((x, y),))
            g |= 1 << ((y - y0) * W + (x - x0))
        return g

    def to_cells(self, g):
        out = set()
        W, x0, y0 = self.W, self.x0, self.y0
        while g:
            low = g & -g
            i = low.bit_length() - 1
            out.add((x0 + i % W, y0 + i // W))
            g ^= low
        return out

    def rect_mask(self, xa, ya, xb, yb):
        """Mask of the cells with xa <= x <= xb, ya <= y <= yb (clipped to the board)."""
        xa = max(xa, self.x0)
        ya = max(ya, self.y0)
        xb = min(xb, self.x0 + self.W - 1)
        yb = min(yb, self.y0 + self.H - 1)
        if xa > xb or ya > yb:
            return 0
        row = ((1 << (xb - xa + 1)) - 1) << (xa - self.x0)
        m = 0
        for y in range(ya, yb + 1):
            m |= row << ((y - self.y0) * self.W)
        return m

    def step(self, g):
        W = self.W
        l = g << 1
        r = g >> 1
        h0 = l ^ r
        h1 = l & r
        s0 = h0 ^ g
        s1 = h1 | (h0 & g)
        a0 = s0 << W
        a1 = s1 << W
        b0 = s0 >> W
        b1 = s1 >> W
        x = a0 ^ b0
        t0 = x ^ h0
        c0 = (a0 & b0) | (x & h0)
        x1 = a1 ^ b1
        y1 = h1 ^ c0
        t1 = x1 ^ y1
        ge2 = (a1 & b1) | (h1 & c0) | (x1 & y1)
        return t1 & ~ge2 & (t0 | g) & self.mask

    def on_ring(self, g):
        return (g & self.ring) != 0

    def dilate(self, g, r=1):
        """Cells within Chebyshev distance r of g (clipped to the interior)."""
        W = self.W
        for _ in range(r):
            g = g | (g << 1) | (g >> 1)
            g = (g | (g << W) | (g >> W)) & self.mask
        return g


def popcount(g):
    return bin(g).count("1")


# --------------------------------------------------------------------------------------------
# The starting objects
# --------------------------------------------------------------------------------------------

GUN_WINDOW = (0, 0, [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539,
                     16843776, 34816, 12288])
GUN = frozenset(cells_of_window(*GUN_WINDOW))
GUN_GLIDER_WINDOW = (23, 9, [1, 6, 3])              # the glider emitted at generation 30
GUN_GLIDER = frozenset(cells_of_window(*GUN_GLIDER_WINDOW))
GLIDER = frozenset(cells_of_window(0, 0, [2, 4, 7]))    # Pattern.glider, velocity (1, 1)/4
BLOCK = frozenset(cells_of_window(0, 0, [3, 3]))
EATER1 = frozenset(cells_of_window(0, 0, [3, 5, 4, 12]))  # OO.. / O.O. / ..O. / ..OO

_gun_phase_cache = {}


def gun_phase(p):
    """The gun of Guns.lean after p generations (0 <= p < 30: no glider has separated yet)."""
    if p not in _gun_phase_cache:
        c = set(GUN)
        for _ in range(p):
            c = step_cells(c)
        _gun_phase_cache[p] = frozenset(c)
    return _gun_phase_cache[p]


# --------------------------------------------------------------------------------------------
# Gliders: recognition and world lines
# --------------------------------------------------------------------------------------------
# For a direction d = (dx, dy) the canonical glider S_d is the image of Pattern.glider under the
# coordinate flips taking (1, 1) to d, translated to have bounding box origin (0, 0).
# A world line is (d, lane, tau) with
#     lane = dy * x - dx * y,      tau = t - 4 * dx * x,
# where (x, y) is the bounding box origin of the glider at a time t at which it is a translate
# of S_d.  Both numbers are constant along the flight.  `glider_at(d, lane, tau, t)` gives the
# cells at time t.

DIRS = [(1, 1), (-1, 1), (-1, -1), (1, -1)]
_DIR_SYM = {(1, 1): 0, (-1, 1): 4, (1, -1): 5, (-1, -1): 2}
CANON = {}
_SHAPES = {}     # frozenset of normalised cells -> (d, j, offx, offy)


def _init_gliders():
    for d in DIRS:
        s = normalize(transform(GLIDER, _DIR_SYM[d]))
        CANON[d] = frozenset(s)
        c = set(s)
        for j in range(4):
            x0, y0, _, _ = bbox(c)
            _SHAPES[frozenset(translate(c, -x0, -y0))] = (d, j, x0, y0)
            c = step_cells(c)


_init_gliders()


def glider_worldline(cells, t):
    """If `cells` (a set) is exactly one glider at time t, its world line (d, lane, tau);
    otherwise None."""
    if len(cells) != 5:
        return None
    x0, y0, _, _ = bbox(cells)
    key = frozenset(translate(cells, -x0, -y0))
    if key not in _SHAPES:
        return None
    d, j, ox, oy = _SHAPES[key]
    # at time t - j the glider was S_d at (x0 - ox, y0 - oy)
    x, y, tt = x0 - ox, y0 - oy, t - j
    return (d, d[1] * x - d[0] * y, tt - 4 * d[0] * x)


_PHASES = {}     # d -> the 4 phases of S_d (not normalised: S_d evolved j generations)


def _init_phases():
    for d in DIRS:
        c = set(CANON[d])
        ph = []
        for j in range(4):
            ph.append(tuple(sorted(c)))
            c = step_cells(c)
        _PHASES[d] = ph


_init_phases()


def glider_at(d, lane, tau, t):
    """Cells at time t of the glider with world line (d, lane, tau)."""
    dx, dy = d
    # the glider is S_d at (x, y) at the time t0 = tau + 4 dx x <= t with t - t0 < 4
    q, j = divmod(t - tau, 4)
    x = dx * q
    y = dx * (dy * x - lane)        # lane = dy x - dx y
    return {(a + x, b + y) for (a, b) in _PHASES[d][j]}


def components(cells, r=2):
    """Connected components for the relation 'Chebyshev distance <= r'."""
    cells = set(cells)
    out = []
    while cells:
        c = cells.pop()
        comp = {c}
        stack = [c]
        while stack:
            (x, y) = stack.pop()
            for dx in range(-r, r + 1):
                for dy in range(-r, r + 1):
                    n = (x + dx, y + dy)
                    if n in cells:
                        cells.remove(n)
                        comp.add(n)
                        stack.append(n)
        out.append(comp)
    return out


def chebyshev_dist(A, B):
    """Chebyshev distance between two nonempty finite sets (quadratic; small sets only)."""
    return min(max(abs(a[0] - b[0]), abs(a[1] - b[1])) for a in A for b in B)


# --------------------------------------------------------------------------------------------
# Periodicity of a bounded evolution
# --------------------------------------------------------------------------------------------

def run_periodic(board, g, tmax=3000, periods=(30, 60, 90, 120), give_up=1800, check=150,
                 pop_cap=None):
    """Evolve g on the board for tmax + max(periods) generations.

    Returns a dict with 'status':
      'ring'      -- a live cell reached the outermost ring at time 't' (left the box);
      'pop'       -- the population exceeded pop_cap at time 't';
      'aperiodic' -- not periodic (with one of the given periods) by generation give_up;
      'periodic'  -- with 'period' p (the least of the given ones) and 'transient' t0, the least
                     t0 with state(t0) = state(t0 + p); by determinism state(t) = state(t + p)
                     for all t >= t0, and this was also compared explicitly up to tmax.
                     'hist' is the list of states 0 .. tmax + p.
    """
    hist = [g]
    step = board.step
    ring = board.ring
    found = None
    pmax = max(periods)
    t = 0
    end = tmax + pmax
    while t < end:
        g = step(g)
        t += 1
        if g & ring:
            return {'status': 'ring', 't': t}
        hist.append(g)
        if t % check == 0:
            if pop_cap is not None and popcount(g) > pop_cap:
                return {'status': 'pop', 't': t}
            if found is None:
                for p in periods:
                    if t >= p and hist[t - p] == g:
                        found = p
                        break
                if found is None and t >= give_up:
                    return {'status': 'aperiodic', 't': t}
    if found is None:
        return {'status': 'aperiodic', 't': t}
    p = found
    for q in periods:           # least period among the given ones
        if q < p and hist[tmax] == hist[tmax + q]:
            p = q
            break
    t0 = tmax
    while t0 > 0 and hist[t0 - 1] == hist[t0 - 1 + p]:
        t0 -= 1
    for s in range(t0, tmax + 1):
        assert hist[s] == hist[s + p]
    return {'status': 'periodic', 'period': p, 'transient': t0, 'hist': hist}


# --------------------------------------------------------------------------------------------
# Self test
# --------------------------------------------------------------------------------------------

def self_test():
    # 1. Guns.lean: gosperGun_evolve_thirty
    g30 = evolve_cells(set(GUN), 30)
    assert g30 == set(GUN) | set(GUN_GLIDER), "gun after 30 generations"
    assert len(GUN) == 36
    # 2. the emitted glider is a phase of the catalogue glider and moves by (1, 1) in 4 steps
    assert evolve_cells(set(GUN_GLIDER), 4) == translate(GUN_GLIDER, 1, 1)
    assert evolve_cells(set(GLIDER), 4) == translate(GLIDER, 1, 1)
    wl = glider_worldline(set(GUN_GLIDER), 30)
    assert wl is not None and wl[0] == (1, 1)
    assert glider_at(*wl, 30) == set(GUN_GLIDER)
    assert glider_at(*wl, 157) == evolve_cells(set(GUN_GLIDER), 127)
    # 3. still lifes
    assert step_cells(set(BLOCK)) == set(BLOCK)
    assert step_cells(set(EATER1)) == set(EATER1)
    # 4. the bit-parallel board agrees with the set simulator on the gun for 300 generations
    b = Board(-10, -10, 130, 110)
    g = b.of_cells(GUN)
    c = set(GUN)
    for t in range(300):
        assert b.to_cells(g) == c, "board differs from the set simulator at %d" % t
        assert not b.on_ring(g)
        g = b.step(g)
        c = step_cells(c)
    # 5. gosperGun_evolve: after 30 n generations, gun + n gliders
    expect = set(GUN)
    for j in range(10):
        expect |= evolve_cells(set(GUN_GLIDER), 30 * j)
    assert c == expect
    # 6. windows round trip, symmetries
    assert cells_of_window(*window_of_cells(GUN)) == set(GUN)
    for k in range(8):
        im = transform(GUN_GLIDER, k)
        w = glider_worldline(im, 0)
        assert w is not None and w[0] == sym_apply(k, (1, 1)), k
        assert step_cells(transform(GUN, k)) == transform(step_cells(set(GUN)), k)
    for d in DIRS:
        for t in range(-9, 9):
            for lane in (-3, 0, 5):
                cc = glider_at(d, lane, 7, t)
                assert glider_worldline(cc, t) == (d, lane, 7), (d, lane, t)
                assert step_cells(cc) == glider_at(d, lane, 7, t + 1)
    print("life.py self test passed: gun(30) = gun + glider window (23, 9, [1, 6, 3]);")
    print("  board simulator = set simulator for 300 generations; gun(300) = gun + 10 gliders.")
    print("  emitted glider world line:", wl)


if __name__ == "__main__":
    self_test()
