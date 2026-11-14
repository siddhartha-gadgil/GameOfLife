"""A small simulator of Conway's Game of Life for the search scripts of this folder.

Everything here is an UNTRUSTED ORACLE: results are numerical observations that
propose reactions; nothing is proved until it is certified in Lean.

Conventions (those of the Lean project, `LeanTheory/Theory/Life`):

* a cell is a pair (x, y), x to the right and y DOWNWARD;
* a configuration is a Python set (or frozenset) of cells;
* a window is (x0, y0, rows): `rows` is a list of natural numbers, top row first,
  and bit j of rows[i] (least significant bit = leftmost cell) is the cell
  (x0 + j, y0 + i).  This is `ofRows x0 y0 rows` in Lean;
* the catalogue glider `ofRows 0 0 [2, 4, 7]` travels (+1, +1) every 4 generations.

Gliders.  A glider is described by (d, phase, x, y): d is its direction, one of
DIRS; phase 0 is the mirror image of the catalogue glider that travels in direction
d, placed so that its 3x3 bounding box has upper left corner (x, y); phase r in
1, 2, 3 is phase 0 evolved r generations.  `glider(d, t, x, y)` accepts any integer
t and is the same trajectory t generations after (before, for t < 0) phase 0 at
(x, y).  The lane of a glider is x - y for the directions (1, 1), (-1, -1) and
x + y for (-1, 1), (1, -1); it is constant along the trajectory.

No dependencies outside the standard library.
"""

# --------------------------------------------------------------------------
# Evolution (set based; the reference implementation)
# --------------------------------------------------------------------------

def step(cells):
    """One generation of Conway's rule B3/S23."""
    count = {}
    for (x, y) in cells:
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                if dx or dy:
                    c = (x + dx, y + dy)
                    count[c] = count.get(c, 0) + 1
    return {c for c, n in count.items() if n == 3 or (n == 2 and c in cells)}


def evolve(cells, n):
    """n generations."""
    cells = set(cells)
    for _ in range(n):
        cells = step(cells)
    return cells


# --------------------------------------------------------------------------
# Geometry
# --------------------------------------------------------------------------

def translate(cells, dx, dy):
    return {(x + dx, y + dy) for (x, y) in cells}


def bbox(cells):
    """(xmin, ymin, xmax, ymax), or None for the empty configuration."""
    if not cells:
        return None
    xs = [c[0] for c in cells]
    ys = [c[1] for c in cells]
    return (min(xs), min(ys), max(xs), max(ys))


def bbox_union(b1, b2):
    if b1 is None:
        return b2
    if b2 is None:
        return b1
    return (min(b1[0], b2[0]), min(b1[1], b2[1]), max(b1[2], b2[2]), max(b1[3], b2[3]))


def normalize(cells):
    """Translate so that the bounding box has upper left corner (0, 0)."""
    if not cells:
        return frozenset()
    x0, y0, _, _ = bbox(cells)
    return frozenset((x - x0, y - y0) for (x, y) in cells)


def distance(A, B):
    """Chebyshev distance between two nonempty configurations."""
    return min(max(abs(a[0] - b[0]), abs(a[1] - b[1])) for a in A for b in B)


# The 8 symmetries of the square grid, as maps on cells.
SYMMETRIES = [
    ("id", lambda x, y: (x, y)),
    ("rot90", lambda x, y: (-y, x)),
    ("rot180", lambda x, y: (-x, -y)),
    ("rot270", lambda x, y: (y, -x)),
    ("flipx", lambda x, y: (-x, y)),
    ("flipy", lambda x, y: (x, -y)),
    ("transpose", lambda x, y: (y, x)),
    ("antitranspose", lambda x, y: (-y, -x)),
]


def transform(cells, k):
    """The image of `cells` under the k-th symmetry (not normalized)."""
    f = SYMMETRIES[k][1]
    return {f(x, y) for (x, y) in cells}


def all_symmetries(cells):
    """The 8 images of `cells`, each normalized to have bounding box corner (0, 0)."""
    return [normalize(transform(cells, k)) for k in range(8)]


# --------------------------------------------------------------------------
# Text and windows
# --------------------------------------------------------------------------

def parse_plaintext(text, x0=0, y0=0):
    """Cells of a picture: 'O' or '*' alive, anything else dead; lines starting
    with '!' are comments.  The first character of the first row is (x0, y0)."""
    cells = set()
    y = y0
    for line in text.splitlines():
        line = line.rstrip()
        if line.startswith("!"):
            continue
        if not line and not cells and y == y0:
            continue                      # leading blank lines
        for j, ch in enumerate(line):
            if ch in "O*":
                cells.add((x0 + j, y))
        y += 1
    return cells


def to_plaintext(cells, box=None):
    """A picture of `cells` ('O' alive, '.' dead) in the box (xmin, ymin, xmax, ymax)."""
    box = box or bbox(cells)
    if box is None:
        return ""
    xa, ya, xb, yb = box
    return "\n".join("".join("O" if (x, y) in cells else "." for x in range(xa, xb + 1))
                     for y in range(ya, yb + 1))


def from_window(x0, y0, rows):
    """The configuration `ofRows x0 y0 rows`."""
    cells = set()
    for i, r in enumerate(rows):
        j = 0
        while r:
            if r & 1:
                cells.add((x0 + j, y0 + i))
            r >>= 1
            j += 1
    return cells


def to_window(cells, origin=None):
    """The window (x0, y0, rows) of `cells`.

    Without `origin` the window is trimmed: (x0, y0) is the upper left corner of
    the bounding box and the last row is nonzero.  With origin = (x0, y0) the window
    starts there (all cells must have x >= x0 and y >= y0); this is used to write
    several parts of a configuration in one frame.  The empty configuration gives
    rows = []."""
    if not cells:
        return (0, 0, []) if origin is None else (origin[0], origin[1], [])
    xa, ya, xb, yb = bbox(cells)
    x0, y0 = (xa, ya) if origin is None else origin
    if xa < x0 or ya < y0:
        raise ValueError("cells outside the window frame")
    rows = [0] * (yb - y0 + 1)
    for (x, y) in cells:
        rows[y - y0] |= 1 << (x - x0)
    return (x0, y0, rows)


def lean_window(cells, origin=None):
    """`cells` as Lean source: `ofRows x0 y0 [rows]`, or `∅`."""
    if not cells:
        return "∅"
    x0, y0, rows = to_window(cells, origin)
    def z(n):
        return str(n) if n >= 0 else "(%d)" % n
    return "ofRows %s %s [%s]" % (z(x0), z(y0), ", ".join(str(r) for r in rows))


# --------------------------------------------------------------------------
# Starting objects (written down directly)
# --------------------------------------------------------------------------

GLIDER = frozenset(from_window(0, 0, [2, 4, 7]))       # .O. / ..O / OOO
BLOCK = frozenset(from_window(0, 0, [3, 3]))           # OO / OO
EATER1 = frozenset(from_window(0, 0, [3, 5, 4, 12]))   # OO.. / O.O. / ..O. / ..OO

DIRS = [(1, 1), (-1, 1), (1, -1), (-1, -1)]
DIR_NAME = {(1, 1): "SE", (-1, 1): "SW", (1, -1): "NE", (-1, -1): "NW"}


def _glider_phases(d):
    """Phases 0..3 of the glider travelling in direction d, phase 0 in the box
    [0, 2] x [0, 2]."""
    sx, sy = d
    phases = []
    g = set(GLIDER)
    for _ in range(4):
        phases.append(frozenset((x if sx == 1 else 2 - x, y if sy == 1 else 2 - y)
                                for (x, y) in g))
        g = step(g)
    return phases


GLIDER_PHASES = {d: _glider_phases(d) for d in DIRS}


def glider(d, t=0, x=0, y=0):
    """The glider travelling in direction d that is t generations after phase 0 at
    (x, y); t is any integer."""
    q, r = divmod(t, 4)
    return translate(GLIDER_PHASES[d][r], x + q * d[0], y + q * d[1])


def lane(d, x, y):
    """The lane of the glider (d, phase, x, y)."""
    return x - y if d[0] == d[1] else x + y


_GLIDER_LOOKUP = {}
for _d in DIRS:
    for _r in range(4):
        _shape = GLIDER_PHASES[_d][_r]
        _a = min(_shape)
        _GLIDER_LOOKUP[frozenset((x - _a[0], y - _a[1]) for (x, y) in _shape)] = (_d, _r, _a)


def identify_glider(cells):
    """(d, phase, x, y) if `cells` is exactly one glider, else None."""
    if len(cells) != 5:
        return None
    a = min(cells)
    key = frozenset((x - a[0], y - a[1]) for (x, y) in cells)
    hit = _GLIDER_LOOKUP.get(key)
    if hit is None:
        return None
    d, r, a0 = hit
    return (d, r, a[0] - a0[0], a[1] - a0[1])


def glider_at_time_zero(g, t):
    """A glider seen as g = (d, phase, x, y) at generation t, traced back to
    generation 0 as if it had always been flying: returns (d, phase0, x0, y0) with
    glider(d, phase0, x0, y0) evolving to g in t generations.  This is a
    time-independent name for an output glider (direction, lane and timing)."""
    d, p, x, y = g
    q, r = divmod(p - t, 4)
    return (d, r, x + q * d[0], y + q * d[1])


def describe_glider(g, t=0):
    """Text for a glider g = (d, phase, x, y) seen at generation t."""
    d, p, x, y = g
    d0, p0, x0, y0 = glider_at_time_zero(g, t)
    return "glider %s dir (%+d,%+d) lane %d: phase %d at (%d,%d) at gen %d [gen 0: phase %d at (%d,%d)]" % (
        DIR_NAME[d], d[0], d[1], lane(d, x, y), p, x, y, t, p0, x0, y0)


# --------------------------------------------------------------------------
# Named small objects, for classifying what is left
# --------------------------------------------------------------------------

_NAMED_PICTURES = {
    "block": "OO\nOO",
    "beehive": ".OO.\nO..O\n.OO.",
    "loaf": ".OO.\nO..O\n.O.O\n..O.",
    "boat": "OO.\nO.O\n.O.",
    "pond": ".OO.\nO..O\nO..O\n.OO.",
    "tub": ".O.\nO.O\n.O.",
    "ship": "OO.\nO.O\n.OO",
    "eater1": "OO..\nO.O.\n..O.\n..OO",
    "blinker": "OOO",
    "blinker ": "O\nO\nO",
}
_NAMED = {}
for _name, _pic in _NAMED_PICTURES.items():
    for _s in all_symmetries(parse_plaintext(_pic)):
        _NAMED[_s] = _name.strip()


def clusters(cells, link=2):
    """Partition `cells` into clusters: cells at Chebyshev distance <= link are in
    the same cluster."""
    todo = set(cells)
    out = []
    while todo:
        seed = todo.pop()
        comp = {seed}
        stack = [seed]
        while stack:
            (x, y) = stack.pop()
            for dx in range(-link, link + 1):
                for dy in range(-link, link + 1):
                    c = (x + dx, y + dy)
                    if c in todo:
                        todo.remove(c)
                        comp.add(c)
                        stack.append(c)
        out.append(comp)
    return out


def name_objects(cells):
    """Sorted list of names of the 8-connected pieces of `cells` ('?n' = an unnamed
    piece of n cells)."""
    names = []
    for comp in clusters(cells, link=1):
        names.append(_NAMED.get(normalize(comp), "?%d" % len(comp)))
    return sorted(names)


# --------------------------------------------------------------------------
# Detection of a settled state: periodic rest + escaping gliders
# --------------------------------------------------------------------------

def _gap(b1, b2, axis):
    """Signed description of the separation of two boxes on an axis: (gap, sign),
    where gap is the number of empty coordinates between them (negative if they
    overlap) and sign = +1 if b2 is on the positive side of b1."""
    lo1, hi1 = b1[axis], b1[axis + 2]
    lo2, hi2 = b2[axis], b2[axis + 2]
    if lo2 > hi1:
        return lo2 - hi1 - 1, 1
    if lo1 > hi2:
        return lo1 - hi2 - 1, -1
    return -1, 0


def _never_meet(b1, v1, b2, v2, margin=4):
    """True if two boxes moving with velocities v1, v2 (signs per axis) are, on some
    axis, at least `margin` apart and not approaching.  (Gliders wobble by one cell
    during a period; the margin allows for that.)"""
    for axis in (0, 1):
        gap, sign = _gap(b1, b2, axis)
        if gap >= margin and sign * (v2[axis] - v1[axis]) >= 0:
            return True
    return False


def analyse(cells, max_period=30):
    """Try to read `cells` as (periodic rest) + (escaping gliders).

    Returns None if it cannot, else a dict with
      'rest'    : the non-glider cells (a still life or oscillator, possibly empty),
      'period'  : period of the rest (1 for still lifes and for the empty rest),
      'gliders' : list of (d, phase, x, y).
    The gliders must be moving away from the envelope of the rest and can never
    meet each other.  This is a sufficient condition, checked by simple box
    arguments; it is part of the untrusted oracle."""
    gliders, rest = [], set()
    for comp in clusters(cells, link=3):
        g = identify_glider(comp)
        if g is None:
            rest |= comp
        else:
            gliders.append((g, bbox(comp)))
    # the rest must be periodic on its own
    period, env, r = None, bbox(rest), rest
    for p in range(1, max_period + 1):
        r = step(r)
        env = bbox_union(env, bbox(r))
        if r == rest:
            period = p
            break
    if period is None:
        return None
    for (g, b) in gliders:
        if env is not None and not _never_meet(env, (0, 0), b, g[0]):
            return None
    for i in range(len(gliders)):
        for j in range(i):
            if not _never_meet(gliders[i][1], gliders[i][0][0], gliders[j][1], gliders[j][0][0]):
                return None
    return {"rest": frozenset(rest), "period": period, "gliders": [g for (g, _) in gliders]}


def settle(cells, max_gen=1000, check_every=4):
    """Run `cells` until it is settled.

    Returns a dict with 'gen' (generation at which the settled state was seen),
    'cells' (the configuration then), 'rest', 'period', 'gliders' as in `analyse`,
    'box' (bounding box of all cells of generations 0..gen), 'maxpop'; or the same
    with 'rest' = None if not settled within max_gen generations.

    'gen' is exact (the first such generation) when the settled state is empty, a
    still life without gliders, or a single glider; otherwise it is the first
    multiple of `check_every` at which `analyse` succeeds."""
    cells = set(cells)
    box = bbox(cells)
    maxpop = len(cells)
    for t in range(max_gen + 1):
        res = None
        if not cells:
            res = {"rest": frozenset(), "period": 1, "gliders": []}
        elif len(cells) == 5 and identify_glider(cells):
            res = {"rest": frozenset(), "period": 1, "gliders": [identify_glider(cells)]}
        else:
            nxt = step(cells)
            if nxt == cells:
                res = {"rest": frozenset(cells), "period": 1, "gliders": []}
            elif t % check_every == 0:
                res = analyse(cells)
        if res is not None:
            res.update(gen=t, cells=frozenset(cells), box=box, maxpop=maxpop)
            return res
        cells = nxt
        box = bbox_union(box, bbox(cells))
        maxpop = max(maxpop, len(cells))
    return {"rest": None, "period": None, "gliders": [], "gen": max_gen,
            "cells": frozenset(cells), "box": box, "maxpop": maxpop}


def outcome_text(res):
    """Short text for a result of `settle`."""
    if res["rest"] is None:
        return "unsettled"
    parts = []
    if res["rest"]:
        names = name_objects(res["rest"])
        parts.append(" + ".join(n if names.count(n) == 1 else "%d %ss" % (names.count(n), n)
                                for n in sorted(set(names))))
        if res["period"] > 1:
            parts[-1] += " (p%d)" % res["period"]
    n = len(res["gliders"])
    if n:
        parts.append("%d glider%s" % (n, "" if n == 1 else "s"))
    return " + ".join(parts) if parts else "nothing"


def first_difference(parts, max_gen=400):
    """The first generation at which the union of the configurations in `parts`
    differs from the union of their separate evolutions (None if there is none up
    to max_gen): the generation at which they have started to interact."""
    parts = [set(p) for p in parts]
    union = set().union(*parts)
    for t in range(1, max_gen + 1):
        union = step(union)
        parts = [step(p) for p in parts]
        if union != set().union(*parts):
            return t
    return None


def footprint_box(cells, n):
    """Bounding box of all cells of generations 0..n."""
    cells = set(cells)
    box = bbox(cells)
    for _ in range(n):
        cells = step(cells)
        box = bbox_union(box, bbox(cells))
    return box


# --------------------------------------------------------------------------
# Bit-parallel evolution on a bounded grid (fast engine for large enumerations)
# --------------------------------------------------------------------------

class BitGrid:
    """A w x h grid packed into one Python integer: bit y * w + x is the cell
    (x, y).  `step` is exact as long as no live cell is in the outermost two rings
    of the grid; `near_edge` tests that.  Cross-checked against the set-based
    `step` in selftest.py."""

    def __init__(self, w, h):
        self.w, self.h = w, h
        row = (1 << w) - 1
        full = 0
        for y in range(h):
            full |= row << (y * w)
        ring = 0
        for y in range(h):
            for x in range(w):
                if x < 2 or y < 2 or x >= w - 2 or y >= h - 2:
                    ring |= 1 << (y * w + x)
        self.full = full
        self.ring = ring

    def pack(self, cells):
        g = 0
        for (x, y) in cells:
            if not (0 <= x < self.w and 0 <= y < self.h):
                raise ValueError("cell outside the grid")
            g |= 1 << (y * self.w + x)
        return g

    def unpack(self, g):
        cells = set()
        while g:
            low = g & -g
            i = low.bit_length() - 1
            cells.add((i % self.w, i // self.w))
            g ^= low
        return cells

    def near_edge(self, g):
        return (g & self.ring) != 0

    def step(self, g):
        w = self.w
        l, r = g << 1, g >> 1
        s0 = l ^ r ^ g                    # row sums of three, bits 0 and 1
        s1 = (l & r) | (g & (l ^ r))
        p0 = l ^ r                        # the two horizontal neighbours
        p1 = l & r
        a0, a1 = s0 << w, s1 << w
        b0, b1 = s0 >> w, s1 >> w
        t0 = a0 ^ b0 ^ p0                 # bit 0 of the number of neighbours
        c0 = (a0 & b0) | (p0 & (a0 ^ b0))
        # a1, b1, p1, c0 have weight 2: exactly one of them set <=> 2 or 3 neighbours
        odd = a1 ^ b1 ^ p1 ^ c0
        two = (a1 & b1) | (p1 & c0) | ((a1 | b1) & (p1 | c0))
        return odd & ~two & (t0 | g) & self.full


# --------------------------------------------------------------------------
# Reactions as Lean-ready records
# --------------------------------------------------------------------------

def reaction_record(name, parts, n, note="", keep_frame=False):
    """Text of a reaction in the conventions of the Lean project.

    `parts` is a list of (label, cells); the initial configuration is their union.
    Everything is translated so that the footprint of the whole reaction (all cells
    of generations 0..n) has upper left corner (0, 0), unless keep_frame is set.
    Positions and lanes of gliders in the record refer to the frame of the record.
    The final configuration is computed here by simulation."""
    union = set()
    for (_, c) in parts:
        union |= set(c)
    fx, fy, gx, gy = footprint_box(union, n)
    if keep_frame:
        sh = lambda c: set(c)
        foot = (fx, fy, gx, gy)
    else:
        sh = lambda c: translate(c, -fx, -fy)
        foot = (0, 0, gx - fx, gy - fy)
    init = sh(union)
    final = evolve(init, n)
    lines = []
    lines.append("-- %s" % name)
    lines.append("-- numerical observation (own search), not verified in Lean")
    if note:
        for ln in note.splitlines():
            lines.append("-- " + ln)
    for (label, c) in parts:
        c = sh(c)
        g = identify_glider(c)
        extra = ""
        if g:
            extra = "   -- glider dir (%+d,%+d), phase %d at (%d,%d), lane %d" % (
                g[0][0], g[0][1], g[1], g[2], g[3], lane(g[0], g[2], g[3]))
        lines.append("--   part %-10s := %s%s" % (label, lean_window(c), extra))
    lines.append("--   initial (union) := %s" % lean_window(init))
    lines.append("--   generations     := %d" % n)
    if final:
        res = analyse(final)
        if res and (res["gliders"] or len(clusters(final, link=3)) > 1):
            for comp in clusters(final, link=3):
                g = identify_glider(comp)
                what = "glider dir (%+d,%+d), phase %d at (%d,%d), lane %d" % (
                    g[0][0], g[0][1], g[1], g[2], g[3], lane(g[0], g[2], g[3])) if g \
                    else "+".join(name_objects(comp))
                lines.append("--   final part      := %s   -- %s" % (lean_window(comp), what))
        lines.append("--   final (union)   := %s   -- %s" % (
            lean_window(final), "+".join(name_objects(final)) if not identify_glider(final) else "glider"))
    else:
        lines.append("--   final           := ∅")
    lines.append("--   footprint box   := x in [%d, %d], y in [%d, %d]  (all generations 0..%d)" % (
        foot[0], foot[2], foot[1], foot[3], n))
    lines.append("-- candidate statement:")
    lines.append("--   conway.evolve %d (%s) = %s" % (n, lean_window(init), lean_window(final)))
    lines.append("-- picture of the initial configuration%s:" % (
        " (its bounding box)" if keep_frame else ""))
    pic = bbox(init) if keep_frame else (0, 0, max(c[0] for c in init), max(c[1] for c in init))
    for row in to_plaintext(init, pic).splitlines():
        lines.append("--   " + row)
    return "\n".join(lines)
