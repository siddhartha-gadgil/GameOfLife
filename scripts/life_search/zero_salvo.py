"""(e, continued) Is there an unconditional zero test made of a salvo of three
gliders from ONE direction?

Run:  python3 zero_salvo.py [--records] [--jobs N]     (25 minutes of CPU time)

Untrusted oracle: the output is a list of numerical observations.

Wanted: a salvo that is destroyed by the block at home and leaves it at home, while
every glider of it passes a block that is one or more steps away along the
register.  With the salvo travelling SE (parametrised as in block_salvo.py: block
at (0, 0), gliders (lane c, delay tau)), the register is the anti-diagonal: the
other positions of the block are (-k, k), k >= 1.  A glider of lane c is at lane
c + 2 k relative to that block, and the lanes that interact with a block are
-5..6 (block_salvo.py, one glider); so the glider passes every such block iff
c >= 5.  (The mirror image, lanes <= -4 and blocks at (k, -k), is the same search.)

Search: all salvos of three non-interacting gliders with lanes in [5, LMAX] and
delays 0 = tau_1 <= tau_2 <= tau_3 <= DELAY, the rest as in block_salvo.py.
(For two gliders see zero_test.py, part 4, which allows all four directions.)
The displacement table of all hits is printed; a hit with displacement (0, 0) is
an unconditional zero test, and is checked against the blocks (-k, k), k = 1..K.
"""
import sys
import time
from multiprocessing import Pool
from life import *
import block_salvo as bs

LMIN, LMAX = 5, 16
DELAY = 64
K = 12
LANES = range(LMIN, LMAX + 1)


def search(args):
    c1, c2 = args
    hits, cases = [], 0
    for tau2 in range(DELAY + 1):
        if (tau2, c2) <= (0, c1) or not bs.pair_ok(c1, c2, tau2):
            continue
        g12 = bs.PBLOCK | bs.packed(c1, 0) | bs.packed(c2, tau2)
        for c3 in LANES:
            for tau3 in range(tau2, DELAY + 1):
                if (tau3, c3) <= (tau2, c2) or not bs.pair_ok(c1, c3, tau3) \
                        or not bs.pair_ok(c2, c3, tau3 - tau2):
                    continue
                cases += 1
                r = bs.run_bits(g12 | bs.packed(c3, tau3), tau3 + bs.FLIGHT + bs.RMAX)
                if r:
                    hits.append((((c1, 0), (c2, tau2), (c3, tau3)), r))
    return cases, hits


def main():
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else None
    t = time.time()
    with Pool(jobs) as pool:
        out = pool.map(search, [(c1, c2) for c1 in LANES for c2 in LANES], chunksize=1)
    cases = sum(o[0] for o in out)
    raw = [h for o in out for h in o[1]]
    hits = [bs.confirm(s) for (s, _) in raw]
    assert all(hits)
    print("three SE gliders, lanes %d..%d, delays 0..%d: %d salvos run, %d leave exactly one block; %.0f s"
          % (LMIN, LMAX, DELAY, cases, len(hits), time.time() - t))
    by = bs.report("three gliders on free lanes", hits, show=3, maxdisp=3, note="")
    zero = by.get((0, 0), [])
    print()
    print("hits with displacement (0,0): %d" % len(zero))
    recs = []
    for h in sorted(zero, key=lambda h: h["n"]):
        free = True
        for k in range(1, K + 1):
            parts = [translate(BLOCK, -k, k)] + [bs.traj(c, tau + 8 * K) for (c, tau) in h["salvo"]]
            free &= first_difference(parts, max_gen=16 * K + 400) is None
        print("  lanes/delays %s: n = %d; passes every block at (-k,k), k = 1..%d: %s" % (
            " ".join("%d/%d" % ct for ct in h["salvo"]), h["n"], K, free))
        if free:
            recs.append(h)
    if "--records" in sys.argv:
        for h in recs:
            parts = [("block", bs.BLOCK0)] + [("glider%d" % (i + 1), p) for i, p in enumerate(h["parts"])]
            print()
            print(reaction_record("unconditional zero test by an SE salvo (register along (-k, k))",
                                  parts, h["n"]))
            mirror = [(label, {(-x, y) for (x, y) in p}) for (label, p) in parts]
            print()
            print(reaction_record("the same, mirror image: SW salvo, register along (k, k)",
                                  mirror, h["n"]))


if __name__ == "__main__":
    main()
