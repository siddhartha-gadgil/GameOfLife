"""(e) Zero test: one glider against a block, restoring gliders, and gliders that
pass a block that is one or more diagonal steps away.

Run:  python3 zero_test.py [--records] [--jobs N]     (a few minutes)

Untrusted oracle: the output is a list of numerical observations.

Setting.  The register block has its upper left cell at (k, k) for the value k;
"home" is k = 0.  A glider trajectory is named (d, c, tau): direction d, lane c
(x - y for SE and NW, x + y for SW and NE), delay tau: the trajectory is
t |-> glider(d, t - tau, x, y) with (x, y) the point of lane c whose coordinate
along the direction of travel, d.x * x + d.y * y, is -AHEAD or -AHEAD + 1.

Part 1.  Every direction and every lane in [-R, R] against the block at home:
         the outcome; "consuming" lanes leave exactly one (displaced) block.
Part 2.  For every direction and lane: for which k in 1..K the glider interacts
         with the block at (k, k).  "free" = for no k >= 1.  (For k > K the lanes
         are outside the interacting range found in part 1.)
Part 3.  For every consuming lane: every single glider that brings the displaced
         block back home, and the composite reaction.
Part 4.  Search for an unconditional test: two gliders, both free in the sense of
         part 2 and not interacting with each other when there is no block, that
         are both destroyed by the block at home and leave it at home.  Since the
         gliders must not meet without the block, one of them (glider 1, delay 0)
         is on a free lane that hits the block at home; glider 2 is on any free
         lane in [-R, R], in any direction, with any delay in [-DELAY, DELAY].
"""
import sys
import time
from multiprocessing import Pool
from life import *

R = 14          # lanes -R..R
AHEAD = 16
K = 14          # block positions (k, k), k = 1..K, tested for free passage
DELAY = 100     # largest delay (in absolute value) in part 4
RMAX = 150
SIZE, OFFSET = 160, 79
GRID = BitGrid(SIZE, SIZE)
BLOCK0 = frozenset(BLOCK)


def start(d, c):
    a = -AHEAD + ((AHEAD + c) % 2)
    sx, sy = d
    if sx == sy:                      # lane x - y = c, sx * (x + y) = a
        s = sx * a
        return ((s + c) // 2, (s - c) // 2)
    e = sx * a                        # lane x + y = c, x - y = sx * a
    return ((c + e) // 2, (c - e) // 2)


def traj(d, c, tau, t=0):
    x, y = start(d, c)
    return glider(d, t - tau, x, y)


def block_at(k):
    return translate(BLOCK0, k, k)


def single(d, c):
    """The glider (d, c) against the block at home.  Returns None (no interaction)
    or a dict: 'res' (result of settle from the normal form), 'glider' (the glider
    in the normal form, phase 0), 'n', and 'disp' if exactly one block is left."""
    t1 = first_difference([set(BLOCK0), traj(d, c, 0)], max_gen=300)
    if t1 is None:
        return None
    t0 = 4 * ((t1 - 1) // 4)
    g = traj(d, c, 0, t0)
    res = settle(set(BLOCK0) | g, max_gen=3000)
    out = {"res": res, "glider": identify_glider(g), "n": res["gen"], "disp": None}
    if res["rest"] is not None and not res["gliders"] and normalize(res["rest"]) == BLOCK0:
        out["disp"] = bbox(res["rest"])[:2]
    return out


def lane_shift(d, v):
    """Translating by v changes the lane of a d-glider by this much."""
    return v[0] - v[1] if d[0] == d[1] else v[0] + v[1]


# ---------------------------------------------------------------- part 4 (workers)

PBLOCK = GRID.pack(translate(BLOCK0, OFFSET, OFFSET))
BLOCKPAT = 3 | (3 << SIZE)


def run_bits(g, tmax):
    """Generation at which the configuration is exactly the block at home, or None
    (also None if it becomes any other single block)."""
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
                return t if g == PBLOCK else None
    return None


FREE = []       # filled in main: the free (d, c)
FIRST = []      # filled in main: the free (d, c) that interact with the block at home


def search_pairs(i):
    """All pairs (FIRST[i], delay 0), (FREE[j], delay tau), tau in -DELAY..DELAY."""
    d1, c1 = FIRST[i]
    g1 = traj(d1, c1, DELAY)              # everything is delayed by DELAY, to allow tau < 0
    p1 = GRID.pack(translate(g1, OFFSET, OFFSET))
    hits, cases = [], 0
    for (d2, c2) in FREE:
        for tau in range(-DELAY, DELAY + 1):
            if (d2, c2) in FIRST and (tau, (d2, c2)) <= (0, (d1, c1)):
                continue                  # the same pair in the other order
            g2 = traj(d2, c2, DELAY + tau)
            if distance(g1, g2) <= 2:
                continue
            cases += 1
            if run_bits(PBLOCK | p1 | GRID.pack(translate(g2, OFFSET, OFFSET)),
                        DELAY + max(tau, 0) + 4 * AHEAD + RMAX):
                hits.append(((d1, c1, DELAY), (d2, c2, DELAY + tau)))
    return cases, hits


def main():
    global FREE, FIRST
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else None
    lanes = range(-R, R + 1)

    # ------------------------------------------------------------ part 1
    print("=" * 100)
    print("(e) part 1: one glider against the block at home (upper left cell (0,0))")
    print("=" * 100)
    table = {}
    for d in DIRS:
        hit = [c for c in lanes if single(d, c) is not None]
        print("direction %s (%+d,%+d): interacting lanes %d..%d (%s)" % (
            DIR_NAME[d], d[0], d[1], min(hit), max(hit),
            "exhaustive" if min(hit) > -R and max(hit) < R else "NOT EXHAUSTIVE"))
        for c in hit:
            s = single(d, c)
            table[(d, c)] = s
            g = s["glider"]
            txt = outcome_text(s["res"])
            if s["disp"] is not None:
                txt = "BLOCK ONLY, displaced by (%d,%d)" % s["disp"]
            print("  lane %3d: glider at (%d,%d) [phase 0], n = %4d: %s" % (c, g[2], g[3], s["n"], txt))
    consuming = [(d, c) for (d, c) in sorted(table) if table[(d, c)]["disp"] is not None]

    # ------------------------------------------------------------ part 2
    print()
    print("=" * 100)
    print("(e) part 2: passing a block at (k,k), k = 1..%d (list of the k with interaction)" % K)
    print("=" * 100)
    hits_k = {}
    for d in DIRS:
        for c in lanes:
            # the glider is started 8 K generations (2 K cells) further back, so that it
            # is in front of every block (k, k) whatever its direction
            hits_k[(d, c)] = [k for k in range(1, K + 1)
                              if first_difference([block_at(k), traj(d, c, 8 * K)],
                                                  max_gen=16 * K + 200) is not None]
    for d in DIRS:
        free = [c for c in lanes if not hits_k[(d, c)]]
        print("direction %s: lanes free for all k >= 1: %s" % (DIR_NAME[d], free))
    print("consuming lanes:")
    for (d, c) in consuming:
        ks = hits_k[(d, c)]
        print("  %s lane %3d, displacement (%d,%d): %s" % (
            DIR_NAME[d], c, table[(d, c)]["disp"][0], table[(d, c)]["disp"][1],
            "FREE for all k >= 1" if not ks else "interacts for k = %s" % ks))

    # ------------------------------------------------------------ part 3
    print()
    print("=" * 100)
    print("(e) part 3: a second glider that brings the displaced block back home")
    print("=" * 100)
    recs = []
    for (d1, c1) in consuming:
        s1 = table[(d1, c1)]
        v = s1["disp"]
        for (d2, c2r) in consuming:
            s2 = table[(d2, c2r)]
            if s2["disp"] != (-v[0], -v[1]):
                continue
            c2 = c2r + lane_shift(d2, v)          # lane in the frame of the home block
            g1 = glider(*s1["glider"])
            # second glider: in its normal form (relative to the displaced block) at generation n1
            _, _, x2, y2 = s2["glider"]
            works = []
            for j in range(-8, 60):
                g2 = glider(d2, j - s1["n"], x2 + v[0], y2 + v[1])
                if distance(g1, g2) <= 2:
                    continue
                cells = set(BLOCK0) | g1 | g2
                res = settle(cells, max_gen=600)
                if res["rest"] == BLOCK0 and not res["gliders"]:
                    works.append(j)
            free1 = not hits_k[(d1, c1)]
            free2 = (-R <= c2 <= R) and not hits_k[(d2, c2)]
            print("test %s lane %d (displacement (%d,%d), n = %d)  +  restore %s lane %d (n = %d)" % (
                DIR_NAME[d1], c1, v[0], v[1], s1["n"], DIR_NAME[d2], c2, s2["n"]))
            print("    test glider free for all k >= 1: %s;  restore glider free for all k >= 1: %s%s" % (
                free1, free2, "" if free2 else "  (interacts for k = %s)" % hits_k.get((d2, c2))))
            # the tightest timing that is safe: the largest j <= 0 such that every tested
            # j' <= j works
            safe = None
            for j in range(-8, 1):
                if j not in works:
                    break
                safe = j
            print("    timing: let the restoring glider be in its normal form (relative to the displaced")
            print("    block) at generation n1 - j, n1 = %d the end of the first reaction; tested j = -8..59;" % s1["n"])
            print("    the block is home again and nothing else is left for j in %s; safe choice j = %s" % (works, safe))
            if safe is None:
                continue
            g2 = glider(d2, safe - s1["n"], x2 + v[0], y2 + v[1])
            total = settle(set(BLOCK0) | g1 | g2, max_gen=600)["gen"]
            recs.append(("zero test: test %s lane %d, then restore %s lane %d (j = %d)%s" % (
                DIR_NAME[d1], c1, DIR_NAME[d2], c2, safe,
                "; the TEST glider passes every block at (k,k), k >= 1" if free1 else ""),
                [("block", BLOCK0), ("test", g1), ("restore", g2)], total))
            recs.append(("first half of the preceding: test %s lane %d alone" % (DIR_NAME[d1], c1),
                         [("block", BLOCK0), ("test", g1)], s1["n"]))

    # ------------------------------------------------------------ part 4
    print()
    print("=" * 100)
    print("(e) part 4: unconditional test with two gliders (both free for all k >= 1)")
    print("=" * 100)
    FREE = [(d, c) for d in DIRS for c in lanes if not hits_k[(d, c)]]
    FIRST = [dc for dc in FREE if dc in table]
    print("free lanes that hit the block at home (glider 1): %s" % ", ".join(
        "%s %d" % (DIR_NAME[d], c) for (d, c) in FIRST))
    t = time.time()
    with Pool(jobs) as pool:
        out = pool.map(search_pairs, range(len(FIRST)), chunksize=1)
    cases = sum(o[0] for o in out)
    raw = [h for o in out for h in o[1]]
    print("free (d, c) for glider 2: %d; delays %d..%d; pairs run: %d; raw hits (block at home, nothing"
          % (len(FREE), -DELAY, DELAY, cases))
    print("else, within %d generations after the later glider would reach the block, in the box x, y in"
          % RMAX)
    print("[%d, %d]): %d;  %.0f s" % (-OFFSET + 2, SIZE - OFFSET - 3, len(raw), time.time() - t))
    good = []
    for (a, b) in raw:
        ga, gb = traj(*a), traj(*b)
        # the two gliders must not interact with each other when there is no block
        if first_difference([ga, gb], max_gen=600) is not None:
            continue
        # and both must take part in the reaction
        cells = set(BLOCK0) | ga | gb
        res = settle(cells, max_gen=800)
        if res["rest"] != BLOCK0 or res["gliders"]:
            continue
        ok = True
        for k in range(1, K + 1):
            ok &= first_difference([block_at(k), traj(a[0], a[1], a[2] + 8 * K),
                                    traj(b[0], b[1], b[2] + 8 * K)], max_gen=16 * K + 400) is None
        if ok:
            good.append((a, b, res["gen"]))
    print("hits whose gliders do not interact without the block and pass every block at (k,k), k = 1..%d: %d"
          % (K, len(good)))
    for (a, b, n) in sorted(good, key=lambda h: h[2]):
        print("  %s lane %d  +  %s lane %d delay %d:  block at home again after %d generations"
              % (DIR_NAME[a[0]], a[1], DIR_NAME[b[0]], b[1], b[2] - a[2], n))
        recs.append(("unconditional zero test: %s lane %d, %s lane %d delay %d" % (
            DIR_NAME[a[0]], a[1], DIR_NAME[b[0]], b[1], b[2] - a[2]),
            [("block", BLOCK0), ("glider1", traj(*a)), ("glider2", traj(*b))], n))

    if "--records" in sys.argv:
        print("=" * 100)
        print("Lean-ready records")
        for (name, parts, n) in recs:
            print()
            print(reaction_record(name, parts, n))


if __name__ == "__main__":
    main()
