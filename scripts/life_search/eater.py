"""(c) A glider meets eater 1.

Run:  python3 eater.py [--records]        (about a minute)

Untrusted oracle: the output is a list of numerical observations.

Enumeration.  The eater is taken in each of its 8 orientations, with the upper
left corner of its 4x4 bounding box at (0, 0).  The glider travels (+1,+1).  Its
trajectory is determined by its lane c = x - y alone (another phase at the same
place is the same trajectory at another time, and the eater does not move); the
script starts it as glider(SE, q, c - START, -START) for every lane c in [-R, R]
and, as a check, for every phase q in 0..3, and verifies that the four phases give
the same reaction.

Normal form.  Let t1 be the first generation at which the configuration differs
from (eater + freely flying glider) and t0 the largest multiple of 4 below t1.
The normal form is the configuration at t0: the eater and the catalogue glider at
some (x, y).  Durations are counted from the normal form.
"""
import sys
from life import *

R, START = 14, 12
SE = (1, 1)
PERIOD, NSTREAM = 30, 10


def normal_form(eater, q, c):
    """(x, y) of the catalogue glider in the normal form, or None (no interaction)."""
    x, y = c - START, -START
    t1 = first_difference([eater, glider(SE, q, x, y)], max_gen=200)
    if t1 is None:
        return None
    t0 = 4 * ((t1 + q - 1) // 4) - q          # generation at which the glider is in phase 0
    g = identify_glider(glider(SE, q + t0, x, y))
    assert g[1] == 0
    return (g[2], g[3])


def stream_test(eater, pos, n):
    """A period-30 stream of NSTREAM gliders into the eater.  Returns (restored,
    independent): restored = at the end exactly the eater is left; independent = at
    every generation n + 30 k the configuration is exactly the eater and the freely
    flying gliders k+1, k+2, ..."""
    x, y = pos
    fs = [(lambda t, k=k: glider(SE, t - PERIOD * k, x, y)) for k in range(NSTREAM)]
    cells = set(eater)
    for f in fs:
        cells |= f(0)
    independent = True
    t = 0
    for k in range(NSTREAM):
        cells = evolve(cells, n + PERIOD * k - t)
        t = n + PERIOD * k
        expect = set(eater)
        for f in fs[k + 1:]:
            expect |= f(t)
        independent &= cells == expect
    cells = evolve(cells, 2 * PERIOD)
    return (cells == set(eater), independent)


def main():
    records = []
    summary = []
    for k, eater in enumerate(all_symmetries(EATER1)):
        print("=" * 90)
        print("eater orientation %d (%s) = %s" % (k, SYMMETRIES[k][0], lean_window(eater)))
        for row in to_plaintext(eater).splitlines():
            print("    " + row)
        lanes = []
        phases_agree = True
        rows = []
        for c in range(-R, R + 1):
            nf = [normal_form(eater, q, c) for q in range(4)]
            phases_agree &= len(set(nf)) == 1
            if nf[0] is None:
                continue
            lanes.append(c)
            cells = set(eater) | glider(SE, 0, *nf[0])
            res = settle(cells, max_gen=3000)
            rows.append((c, nf[0], res))
        print("lanes searched %d..%d; interacting lanes %d..%d (%d lanes; %s); the 4 phases agree: %s" % (
            -R, R, min(lanes), max(lanes), len(lanes),
            "exhaustive" if -R not in lanes and R not in lanes else "NOT EXHAUSTIVE", phases_agree))
        print("  %-5s %-12s %5s  %s" % ("lane", "glider at", "n", "outcome"))
        nabs = 0
        for (c, pos, res) in rows:
            restored = res["rest"] == eater and not res["gliders"]
            txt = outcome_text(res)
            extra = ""
            if restored:
                nabs += 1
                ok, ind = stream_test(eater, pos, res["gen"])
                box = res["box"]
                txt = "EATER RESTORED, glider destroyed"
                extra = "  box %s; period-30 stream of %d: %s, %s" % (
                    str(box), NSTREAM, "eater restored" if ok else "FAILS",
                    "independent" if ind else "not independent")
                records.append((k, eater, pos, res["gen"]))
            elif res["rest"] is not None and eater <= res["rest"]:
                txt += "  (eater intact, something added)"
            print("  %-5d %-12s %5d  %s%s" % (c, str(pos), res["gen"], txt, extra))
        summary.append((k, len(lanes), nabs))
    print("=" * 90)
    print("summary: orientation, interacting lanes, absorbing lanes")
    for (k, nl, na) in summary:
        print("  %d %-14s %2d %2d" % (k, SYMMETRIES[k][0], nl, na))
    if "--records" in sys.argv:
        print("=" * 90)
        print("Lean-ready records of the absorptions")
        for (k, eater, pos, n) in records:
            print()
            print(reaction_record(
                "absorption, eater orientation %d (%s), glider lane %d" % (
                    k, SYMMETRIES[k][0], pos[0] - pos[1]),
                [("eater", eater), ("glider", glider(SE, 0, *pos))], n))


if __name__ == "__main__":
    main()
