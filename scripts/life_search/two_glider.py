"""(a) All collisions of two gliders, and (b) their behaviour in period-30 streams.

Run:  python3 two_glider.py [--records]        (20 seconds)

Untrusted oracle: the output is a list of numerical observations.

Enumeration.  Glider A is the catalogue glider, direction (+1,+1), phase 0 at (0,0).
Glider B travels in one of the other three directions.  Advancing both gliders by 4
generations and translating by (-1,-1) maps the pair (A, B at (x, y)) to
(A, B at (x, y) + dB - (1, 1)); so every collision from far apart is represented
exactly once by

  dB = (-1,+1):  B = glider(dB, q, x, y),  x in {X0, X0+1},  y in [-R, R],  q in 0..3;
  dB = (+1,-1):  B = glider(dB, q, x, y),  y in {X0, X0+1},  x in [-R, R],  q in 0..3;
  dB = (-1,-1):  B = glider(dB, q, x, y),  x - y = c in [-R, R],
                 x + y in {S0, S0+2} (S0 = X0 or X0+1, of the parity of c), q in 0..3.

The script checks that the extreme values of the transverse parameter give no
interaction, so that the range [-R, R] is exhaustive.

Normal form of a collision.  Let t1 be the first generation at which the pair
differs from two freely flying gliders, and t0 the largest multiple of 4 below t1.
The configuration at t0, translated so that A is again the catalogue glider at
(0, 0), is the normal form: A = glider(SE, 0, 0, 0), B = glider(dB, phase, x, y).
Durations are counted from the normal form.
"""
import sys
from life import *

X0, R = 30, 14
SE = (1, 1)
PERIOD = 30          # of the streams
NSTREAM = 10


def candidates(dB):
    """The representatives (q, x, y) of all pairs for direction dB, with the
    transverse parameter (used to check that the range is exhaustive)."""
    out = []
    for q in range(4):
        for c in range(-R, R + 1):
            for e in (0, 1):
                if dB == (-1, 1):
                    out.append((c, (q, X0 + e, c)))
                elif dB == (1, -1):
                    out.append((c, (q, c, X0 + e)))
                else:
                    s = X0 + ((X0 + c) % 2) + 2 * e
                    out.append((c, (q, (s + c) // 2, (s - c) // 2)))
    return out


def normal_form(dB, q, x, y):
    """Normal form (phase, x, y) of B, or None if the gliders do not interact."""
    A, B = glider(SE), glider(dB, q, x, y)
    t1 = first_difference([A, B], max_gen=8 * X0)
    if t1 is None:
        return None
    t0 = 4 * ((t1 - 1) // 4)
    g = identify_glider(translate(glider(dB, q + t0, x, y), -t0 // 4, -t0 // 4))
    return g[1:]


def symmetry_class(dB, B):
    """A key that is equal for collisions that differ by a symmetry of the plane
    (possibly exchanging the gliders): the configuration one generation before the
    first difference, in all 8 orientations."""
    A, Bc = glider(SE), glider(dB, *B)
    t1 = first_difference([A, Bc])
    cells = evolve(A | Bc, t1 - 1)
    return min(tuple(sorted(s)) for s in all_symmetries(cells))


def classify(res):
    if res["rest"] is None:
        return "other"
    if not res["rest"] and not res["gliders"]:
        return "nothing"
    if not res["rest"] and len(res["gliders"]) == 1:
        return "one glider"
    if not res["gliders"]:
        return "still life" if res["period"] == 1 else "oscillator"
    return "other"


def box_size(box):
    return "%dx%d" % (box[2] - box[0] + 1, box[3] - box[1] + 1)


# ---------------------------------------------------------------- streams

def traj(d, t0, x, y):
    """A glider trajectory as a function of the generation."""
    return lambda t: glider(d, t + t0, x, y)


def stream_pair_test(dB, B, n):
    """Both gliders are members of period-30 streams of NSTREAM gliders (glider k of
    a stream is 30 k generations behind glider 0).  Returns (final_empty,
    independent): final_empty = nothing is left after the last pair has reacted;
    independent = at every generation n + 30 k the configuration is exactly the
    freely flying gliders k+1, k+2, ... of both streams."""
    p, x, y = B
    As = [traj(SE, -PERIOD * k, 0, 0) for k in range(NSTREAM)]
    Bs = [traj(dB, p - PERIOD * k, x, y) for k in range(NSTREAM)]
    cells = set()
    for f in As + Bs:
        cells |= f(0)
    independent = True
    t = 0
    for k in range(NSTREAM):
        cells = evolve(cells, n + PERIOD * k - t)
        t = n + PERIOD * k
        expect = set()
        for f in As[k + 1:] + Bs[k + 1:]:
            expect |= f(t)
        independent &= cells == expect
    cells = evolve(cells, 4 * PERIOD)
    return (not cells, independent)


def stream_single_test(dB, B, n, outputs, which, hit=4, after=7 * PERIOD):
    """One glider meets a period-30 stream of NSTREAM gliders of the other kind
    (which = 'B': single A against a stream of B; which = 'A': the reverse); the
    single glider is timed to meet glider number `hit` of the stream.  True if,
    `after` generations after the end of the isolated reaction, the configuration
    is exactly: the other stream gliders in free flight plus the output gliders of
    the isolated reaction in free flight.  `outputs` are gliders (d, phase, x, y)
    seen at generation n."""
    p, x, y = B
    single = traj(SE, 0, 0, 0) if which == "B" else traj(dB, p, x, y)
    if which == "B":
        stream = [traj(dB, p - PERIOD * (k - hit), x, y) for k in range(NSTREAM)]
    else:
        stream = [traj(SE, -PERIOD * (k - hit), 0, 0) for k in range(NSTREAM)]
    cells = set(single(0))
    for f in stream:
        cells |= f(0)
    if len(cells) != 5 * (NSTREAM + 1):
        return False
    T = n + after
    cells = evolve(cells, T)
    expect = set()
    for k, f in enumerate(stream):
        if k != hit:
            expect |= f(T)
    for (d, ph, gx, gy) in outputs:
        expect |= glider(d, ph + after, gx, gy)
    return cells == expect


# ---------------------------------------------------------------- main

def main():
    all_classes = {}
    recommended = []
    for dB in [(-1, 1), (1, -1), (-1, -1)]:
        kind = "head-on" if dB == (-1, -1) else "perpendicular"
        print("=" * 100)
        print("(a) glider A: dir (+1,+1), catalogue glider at (0,0);  glider B: dir (%+d,%+d)  [%s]"
              % (dB[0], dB[1], kind))
        print("=" * 100)
        rows = []
        extremes_ok = True
        interacting_c = set()
        for (c, (q, x, y)) in candidates(dB):
            B = normal_form(dB, q, x, y)
            if B is None:
                continue
            interacting_c.add(c)
            if abs(c) == R:
                extremes_ok = False
            cells = glider(SE) | glider(dB, *B)
            res = settle(cells, max_gen=3000)
            rows.append((B, res, classify(res)))
            all_classes.setdefault(symmetry_class(dB, B), outcome_text(res))
        total = 8 * (2 * R + 1)
        print("pairs enumerated: %d;  interacting: %d;  transverse parameter of interacting pairs: "
              "%d..%d (range searched %d..%d: %s)" % (
                  total, len(rows), min(interacting_c), max(interacting_c), -R, R,
                  "exhaustive" if extremes_ok else "NOT EXHAUSTIVE"))
        counts = {}
        detail = {}
        for (B, res, cl) in rows:
            counts[cl] = counts.get(cl, 0) + 1
            detail.setdefault((cl, outcome_text(res)), []).append(B)
        print("\nclasses:")
        for cl in ["nothing", "one glider", "still life", "oscillator", "other"]:
            print("  %-12s %3d" % (cl, counts.get(cl, 0)))
        print("\noutcomes in detail:")
        for (cl, txt), Bs in sorted(detail.items(), key=lambda kv: -len(kv[1])):
            print("  %3d  %-12s %s" % (len(Bs), cl, txt))

        print("\nclean annihilations (B = glider(dB, phase, x, y) in normal form; n = generations")
        print("from the normal form until empty; box = bounding box of generations 0..n;")
        if kind == "perpendicular":
            print("streams = both gliders in period-30 streams of %d: final empty / pairs independent;" % NSTREAM)
        print("gate A|B = a single A against a stream of B removes exactly one glider of the stream,")
        print("and the same for a single B against a stream of A):")
        print("  %-14s %-24s %4s %-8s %-20s %-22s %s" % (
            "B (ph, x, y)", "B as a window", "n", "box", "box corners", "streams", "gate A|B / B|A"))
        for (B, res, cl) in sorted(rows, key=lambda r: (r[1]["gen"], r[0])):
            if cl != "nothing":
                continue
            n, box = res["gen"], res["box"]
            st = ""
            if kind == "perpendicular":
                fe, ind = stream_pair_test(dB, B, n)
                st = "%s / %s" % ("empty" if fe else "DIRTY", "independent" if ind else "not indep.")
            gA = stream_single_test(dB, B, n, [], "B")
            gB = stream_single_test(dB, B, n, [], "A")
            print("  %-14s %-24s %4d %-8s %-20s %-22s %s / %s" % (
                "(%d, %d, %d)" % B, lean_window(glider(dB, *B)), n, box_size(box), str(box), st,
                "yes" if gA else "no", "yes" if gB else "no"))
            recommended.append((dB, B, n, "annihilation", st, gA, gB, box))

        print("\none-glider outcomes (n = generations from the normal form until exactly one glider")
        print("is left; output glider as seen at generation n, and traced back to generation 0;")
        print("stream A|B as above, the output glider flying on freely):")
        for (B, res, cl) in sorted(rows, key=lambda r: (r[1]["gen"], r[0])):
            if cl != "one glider":
                continue
            n, box = res["gen"], res["box"]
            g = res["gliders"][0]
            gA = stream_single_test(dB, B, n, [g], "B")
            gB = stream_single_test(dB, B, n, [g], "A")
            print("  B = (%d, %d, %d)  n = %d  box %s %s" % (B + (n, box_size(box), box)))
            print("      output: %s" % describe_glider(g, n))
            print("      single A against stream of B: %s;  single B against stream of A: %s" % (
                "clean" if gA else "disturbs", "clean" if gB else "disturbs"))
            recommended.append((dB, B, n, "one glider", "", gA, gB, box))

        print("\nstill life and oscillator outcomes without gliders:")
        for (B, res, cl) in sorted(rows, key=lambda r: (r[1]["gen"], r[0])):
            if cl in ("still life", "oscillator"):
                print("  B = %-14s n = %4d  box %-8s %s" % (
                    "(%d, %d, %d)" % B, res["gen"], box_size(res["box"]), outcome_text(res)))
        print("\nother outcomes:")
        for (B, res, cl) in sorted(rows, key=lambda r: (r[1]["gen"], r[0])):
            if cl == "other":
                print("  B = %-14s settled at %4d  max population %3d  %s" % (
                    "(%d, %d, %d)" % B, res["gen"], res["maxpop"], outcome_text(res)))
        print()

    print("=" * 100)
    print("collisions up to symmetry (rotations, reflections, exchange of the gliders): %d" % len(all_classes))
    by = {}
    for v in all_classes.values():
        by[v] = by.get(v, 0) + 1
    for v, k in sorted(by.items(), key=lambda kv: -kv[1]):
        print("  %3d  %s" % (k, v))

    if "--records" in sys.argv:
        print("=" * 100)
        print("Lean-ready records of all clean annihilations and one-glider outcomes")
        for (dB, B, n, what, st, gA, gB, box) in recommended:
            print()
            print(reaction_record(
                "%s, B dir (%+d,%+d), normal form B = (%d, %d, %d)" % ((what,) + dB + B),
                [("gliderA", glider(SE)), ("gliderB", glider(dB, *B))], n))


if __name__ == "__main__":
    main()
