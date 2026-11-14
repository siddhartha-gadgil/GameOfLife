"""(d) A block and a salvo of 1, 2 or 3 gliders, all travelling (+1,+1), such that
only a block remains.

Run:  python3 block_salvo.py [--three] [--records] [--dump FILE] [--jobs N]
      (1 and 2 gliders: 15 seconds; --three adds the 3-glider search: about 3 hours
      of CPU time, divided by the number of cores; --dump writes every hit that
      moves the block by at most 2 cells in each coordinate to FILE)

Untrusted oracle: the output is a list of numerical observations.

Parametrisation.  The block has its upper left cell at (0, 0).  An SE glider
trajectory is named (c, tau): c = x - y is its lane, and tau its delay: the
trajectory is  t |-> glider(SE, t - tau, x_c, y_c), where (x_c, y_c) is the point
of lane c with x_c + y_c in {-START, -START + 1}.  Every SE trajectory has exactly
one name (c, tau) with tau an integer.  A salvo is a set of trajectories, up to a
common shift of the delays; it is enumerated with delays
0 = tau_1 <= tau_2 <= tau_3 <= DELAY and lanes in [-LANES, LANES], and only if
the gliders do not interact with each other (the salvo alone evolves as the union
of its gliders).

Search.  The configuration (block + salvo at generation 0) is run on a bounded
grid with the bit-parallel engine until it is exactly one block (a hit), until a
live cell comes within 2 cells of the border of the grid (given up: the reaction
is not confined to the box x, y in [-OFFSET + 2, SIZE - OFFSET - 3]), or until
generation tau_last + FLIGHT + RMAX (given up: too long).  Every hit is then
re-run with the set-based engine.

Normal form of a hit.  t1 = first generation at which the configuration differs
from (block + freely flying salvo), t0 = largest multiple of 4 below t1; the normal
form is the configuration at t0 and n is the number of generations from t0 to the
first generation at which only the block is left.
"""
import sys
import time
from multiprocessing import Pool
from life import *

SE = (1, 1)
START = 12            # the gliders of delay 0 start with x + y in {-12, -11}
LANES = 12            # lanes -12..12
DELAY2 = 80           # largest delay, 2-glider salvos
DELAY3 = 48           # largest delay, 3-glider salvos
FLIGHT = 24           # generations for a glider of delay 0 to reach the block
RMAX = 120            # a hit must be complete at generation tau_last + FLIGHT + RMAX
SIZE, OFFSET = 80, 48  # bit grid SIZE x SIZE, the block at (OFFSET, OFFSET)

GRID = BitGrid(SIZE, SIZE)
BLOCK0 = frozenset(BLOCK)


def std_pos(c):
    s = -START + ((START + c) % 2)
    return ((s + c) // 2, (s - c) // 2)


def traj(c, tau, t=0):
    """The glider of name (c, tau) at generation t."""
    x, y = std_pos(c)
    return glider(SE, t - tau, x, y)


def name_of(g):
    """The name (c, tau) of the trajectory that is the glider g = (SE, phase, x, y)
    at generation 0."""
    d, p, x, y = g
    assert d == SE
    c = x - y
    return (c, -p - 4 * (x - std_pos(c)[0]))


def independent(gliders):
    """The gliders (configurations) are disjoint and their union evolves for 4
    generations as the union of their evolutions."""
    union = set().union(*gliders)
    if len(union) != 5 * len(gliders):
        return False
    return first_difference(gliders, max_gen=4) is None


_pair_ok = {}


def pair_ok(c1, c2, dtau):
    """Gliders (c1, 0) and (c2, dtau) do not interact."""
    key = (c1, c2, dtau)
    if key not in _pair_ok:
        _pair_ok[key] = independent([traj(c1, 0), traj(c2, dtau)])
    return _pair_ok[key]


_packed = {}


def packed(c, tau):
    key = (c, tau)
    if key not in _packed:
        _packed[key] = GRID.pack(translate(traj(c, tau), OFFSET, OFFSET))
    return _packed[key]


PBLOCK = GRID.pack(translate(BLOCK0, OFFSET, OFFSET))
BLOCKPAT = 3 | (3 << SIZE)


def run_bits(g, tmax):
    """Run on the bit grid.  Returns (t, x, y): at generation t <= tmax the
    configuration is exactly one block, with upper left cell (x, y) relative to the
    original block; or None."""
    w, full, ring = SIZE, GRID.full, GRID.ring
    for t in range(1, tmax + 1):
        l, r = g << 1, g >> 1
        p0 = l ^ r
        p1 = l & r
        s0 = p0 ^ g
        s1 = p1 | (g & p0)
        a0, a1, b0, b1 = s0 << w, s1 << w, s0 >> w, s1 >> w
        x0 = a0 ^ b0
        c0 = (a0 & b0) | (p0 & x0)
        g = (a1 ^ b1 ^ p1 ^ c0) & ~((a1 & b1) | (p1 & c0) | ((a1 | b1) & (p1 | c0))) \
            & ((x0 ^ p0) | g) & full
        if g & ring or not g:
            return None
        if g.bit_count() == 4:
            low = g & -g
            if g == low * BLOCKPAT:
                i = low.bit_length() - 1
                return (t, i % w - OFFSET, i // w - OFFSET)
    return None


def search_two(c1):
    hits = []
    cases = 0
    for c2 in range(-LANES, LANES + 1):
        for tau in range(DELAY2 + 1):
            if (tau, c2) <= (0, c1) or not pair_ok(c1, c2, tau):
                continue
            cases += 1
            r = run_bits(PBLOCK | packed(c1, 0) | packed(c2, tau), tau + FLIGHT + RMAX)
            if r:
                hits.append((((c1, 0), (c2, tau)), r))
    return cases, hits


def search_three(args):
    c1, c2 = args
    hits = []
    cases = 0
    for tau2 in range(DELAY3 + 1):
        if (tau2, c2) <= (0, c1) or not pair_ok(c1, c2, tau2):
            continue
        g12 = PBLOCK | packed(c1, 0) | packed(c2, tau2)
        for c3 in range(-LANES, LANES + 1):
            for tau3 in range(tau2, DELAY3 + 1):
                if (tau3, c3) <= (tau2, c2) or not pair_ok(c1, c3, tau3) \
                        or not pair_ok(c2, c3, tau3 - tau2):
                    continue
                cases += 1
                r = run_bits(g12 | packed(c3, tau3), tau3 + FLIGHT + RMAX)
                if r:
                    hits.append((((c1, 0), (c2, tau2), (c3, tau3)), r))
    return cases, hits


def confirm(salvo):
    """Re-run a hit with the set-based engine.  Returns a dict with the normal form
    (gliders as configurations at t0), n, the displacement of the block, and the
    footprint box; or None if the hit is not confirmed."""
    gl = [traj(c, tau) for (c, tau) in salvo]
    if not independent(gl):
        return None
    t1 = first_difference([set(BLOCK0)] + gl, max_gen=400)
    if t1 is None:
        return None
    t0 = 4 * ((t1 - 1) // 4)
    parts = [traj(c, tau, t0) for (c, tau) in salvo]
    cells = set(BLOCK0).union(*parts)
    box = bbox(cells)
    for n in range(1, 400):
        cells = step(cells)
        box = bbox_union(box, bbox(cells))
        if len(cells) == 4 and normalize(cells) == BLOCK0:
            x, y, _, _ = bbox(cells)
            return {"salvo": salvo, "parts": parts, "n": n, "disp": (x, y), "box": box, "t0": t0}
    return None


def report(title, hits, show=6, maxdisp=None, note="; --dump writes all hits in [-2, 2]^2"):
    """Print the confirmed hits grouped by displacement (only the displacements with
    both coordinates at most maxdisp in absolute value, if maxdisp is given)."""
    by = {}
    for h in hits:
        by.setdefault(h["disp"], []).append(h)
    print("%s: %d hits, %d different displacements" % (title, len(hits), len(by)))
    if maxdisp is not None:
        print("  (listed: the displacements in [%d, %d]^2%s)" % (-maxdisp, maxdisp, note))
    print("  %-10s %5s   shortest reactions: n, box, gliders (phase 0 position and generations to add;" % ("displ.", "hits"))
    print("  %-10s %5s   i.e. the glider is glider(SE, t, x, y) written as (x, y)+t), block at (0,0)" % ("", ""))
    for disp in sorted(by, key=lambda v: (max(abs(v[0]), abs(v[1])), v)):
        if maxdisp is not None and max(abs(disp[0]), abs(disp[1])) > maxdisp:
            continue
        hs = sorted(by[disp], key=lambda h: (h["n"], h["salvo"]))
        print("  %-10s %5d" % ("(%d,%d)" % disp, len(hs)))
        for h in hs[:show]:
            gs = []
            for p in h["parts"]:
                g = identify_glider(p)
                gs.append("(%d,%d)+%d" % (g[2], g[3], g[1]))
            b = h["box"]
            print("      n = %3d  box %dx%d  %s   [lanes/delays %s]" % (
                h["n"], b[2] - b[0] + 1, b[3] - b[1] + 1, " ".join(gs),
                " ".join("%d/%d" % ct for ct in h["salvo"])))
    return by


def lean_salvo_check(name, window, block_at, hits, expected_disp):
    """Is the salvo of Theory/Life/SlidingBlock.lean among the hits?"""
    cells = translate(from_window(*window), -block_at[0], -block_at[1])
    names = sorted(name_of(identify_glider(comp)) for comp in clusters(cells, link=1))
    m = min(tau for (_, tau) in names)
    key = sorted((c, tau - m) for (c, tau) in names)
    tkey = None
    found = None
    for h in hits:
        if sorted(h["salvo"]) == key:
            found = h
    print("%s: gliders (lane, delay) = %s" % (name, key))
    if found is None:
        # try the mirror image in the diagonal of the block
        tcells = {(y, x) for (x, y) in cells}
        tn = sorted(name_of(identify_glider(comp)) for comp in clusters(tcells, link=1))
        m = min(tau for (_, tau) in tn)
        tkey = sorted((c, tau - m) for (c, tau) in tn)
        for h in hits:
            if sorted(h["salvo"]) == tkey:
                found = h
    if found is None:
        print("    NOT among the hits (mirror image: %s)" % tkey)
        return
    # relate the Lean configuration to the normal form of the hit
    init = set(BLOCK0).union(*found["parts"])
    lean = set(BLOCK0) | (cells if tkey is None else {(y, x) for (x, y) in cells})
    rel = None
    cur = set(init)
    for j in range(0, 60):
        if cur == lean:
            rel = j
            break
        cur = step(cur)
    print("    REDISCOVERED%s: hit with displacement %s (expected %s), n = %d from the normal form;" % (
        " (as the mirror image in the diagonal)" if tkey is not None else "",
        found["disp"], expected_disp, found["n"]))
    if rel is not None:
        print("    the Lean configuration is generation %d of the normal form, so the Lean duration is %d" % (
            rel, found["n"] - rel))
    else:
        cur = set(lean)
        for j in range(1, 60):
            cur = step(cur)
            if cur == init:
                print("    the normal form is generation %d of the Lean configuration, so the Lean duration is %d" % (
                    j, found["n"] + j))
                break


def records(title, by, disps, k=2):
    for disp in disps:
        for h in sorted(by.get(disp, []), key=lambda h: (h["n"], h["salvo"]))[:k]:
            parts = [("block", BLOCK0)] + [("glider%d" % (i + 1), p) for i, p in enumerate(h["parts"])]
            print()
            print(reaction_record("%s, block displaced by (%d,%d)" % ((title,) + disp), parts, h["n"]))


def main():
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else None
    print("=" * 100)
    print("(d) block at (0,0) and SE gliders; lanes %d..%d; grid box x, y in [%d, %d]" % (
        -LANES, LANES, -OFFSET + 2, SIZE - OFFSET - 3))
    print("=" * 100)

    # ---- one glider: every lane, complete outcome (set-based engine)
    print("one glider (lane c: the catalogue glider on lane c against the block):")
    one_hits = []
    for c in range(-LANES, LANES + 1):
        if first_difference([set(BLOCK0), traj(c, 0)], max_gen=200) is None:
            continue
        res = settle(set(BLOCK0) | traj(c, 0), max_gen=3000)
        h = confirm(((c, 0),))
        extra = ""
        if h:
            one_hits.append(h)
            extra = "   BLOCK ONLY: displacement %s, n = %d" % (h["disp"], h["n"])
        print("  lane %3d: settled at %4d: %s%s" % (c, res["gen"], outcome_text(res), extra))
    print()

    # ---- two gliders
    t = time.time()
    with Pool(jobs) as pool:
        out = pool.map(search_two, range(-LANES, LANES + 1))
    cases = sum(o[0] for o in out)
    raw = [h for o in out for h in o[1]]
    two_hits = [confirm(s) for (s, _) in raw]
    assert all(two_hits), "a hit of the bit engine was not confirmed"
    assert all(h["disp"] == (r[1], r[2]) for h, (_, r) in zip(two_hits, raw))
    print("two gliders: delays 0..%d; %d salvos of non-interacting gliders run; %.0f s" % (
        DELAY2, cases, time.time() - t))
    by2 = report("two gliders", two_hits)
    print()
    lean_salvo_check("pullSalvo (Lean)", (0, 5, [2, 4, 647, 768, 256]), (7, 11), two_hits, (-1, -1))
    print()

    by3 = {}
    if "--three" in sys.argv:
        t = time.time()
        tasks = [(c1, c2) for c1 in range(-LANES, LANES + 1) for c2 in range(-LANES, LANES + 1)]
        for (c1, c2) in tasks:                 # fill the tables before the workers are forked
            for tau in range(DELAY3 + 1):
                pair_ok(c1, c2, tau)
                packed(c2, tau)
        with Pool(jobs) as pool:
            out = pool.map(search_three, tasks, chunksize=1)
        cases = sum(o[0] for o in out)
        raw = [h for o in out for h in o[1]]
        three_hits = [confirm(s) for (s, _) in raw]
        assert all(three_hits), "a hit of the bit engine was not confirmed"
        print("three gliders: delays 0..%d; %d salvos of non-interacting gliders run; %.0f s" % (
            DELAY3, cases, time.time() - t))
        by3 = report("three gliders", three_hits, maxdisp=3)
        print()
        lean_salvo_check("pushSalvo (Lean)", (0, 0, [4, 8, 14, 0, 0, 2, 4, 647, 768, 256]), (7, 11),
                         three_hits, (1, 1))
        print()

    if "--dump" in sys.argv:
        # every hit whose block moves at most 2 cells in each coordinate, one per line
        path = sys.argv[sys.argv.index("--dump") + 1]
        with open(path, "w") as f:
            f.write("# hits of block_salvo.py with displacement in [-2, 2]^2: numerical observations\n")
            f.write("# dx dy n box_w box_h | gliders as lane/delay | normal form: glider(SE, t, x, y) as x,y+t\n")
            for by in (by2, by3):
                for disp in sorted(by):
                    if max(abs(disp[0]), abs(disp[1])) > 2:
                        continue
                    for h in sorted(by[disp], key=lambda h: (h["n"], h["salvo"])):
                        b = h["box"]
                        gs = [identify_glider(q) for q in h["parts"]]
                        f.write("%d %d %d %d %d | %s | %s\n" % (
                            disp[0], disp[1], h["n"], b[2] - b[0] + 1, b[3] - b[1] + 1,
                            " ".join("%d/%d" % ct for ct in h["salvo"]),
                            " ".join("%d,%d+%d" % (g[2], g[3], g[1]) for g in gs)))
        print("hits with displacement in [-2, 2]^2 written to %s" % path)
        print()

    if "--records" in sys.argv:
        print("=" * 100)
        print("Lean-ready records")
        records("one glider", {h["disp"]: [h] for h in one_hits}, [h["disp"] for h in one_hits])
        records("two gliders", by2, [(-1, -1), (1, 1), (0, 0)])
        records("three gliders", by3, [(1, 1), (-1, -1), (0, 0)])


if __name__ == "__main__":
    main()
