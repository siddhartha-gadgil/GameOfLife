"""The recommended reactions of report R-19, each checked by direct simulation and
printed as a Lean-ready record.

Run:  python3 recommended.py          (a second)

Untrusted oracle: numerical observations (own search), not verified in Lean.  The
windows written below were found by two_glider.py, eater.py, block_salvo.py and
zero_test.py; this script only re-checks them with the set-based engine, so that
the cell data quoted in the report has one reproducible source.
"""
from life import *

SE, SW, NE, NW = (1, 1), (-1, 1), (1, -1), (-1, -1)
W = from_window


def check(name, init, n, final, first=True):
    """evolve n init = final, and (if first) not earlier."""
    cells = set(init)
    for t in range(n):
        assert not first or cells != set(final), name
        cells = step(cells)
    assert cells == set(final), name


def show(name, parts, n, final, note="", keep_frame=False):
    union = set().union(*[set(c) for (_, c) in parts])
    check(name, union, n, final)
    print()
    print(reaction_record(name, parts, n, note, keep_frame))


A = glider(SE)                       # the catalogue glider, ofRows 0 0 [2, 4, 7]
assert A == W(0, 0, [2, 4, 7])

# ---- 1. absorption by eater 1
eater = W(4, 4, [3, 5, 4, 12])
show("R1 absorption: eater 1 (catalogue orientation, translated by (4,4)) eats an SE glider",
     [("eater", eater), ("glider", A)], 6, eater)
eater_t = W(3, 4, [3, 1, 14, 8])
show("R1' absorption, mirror image in the diagonal (eater transposed)",
     [("eater", eater_t), ("glider", A)], 4, eater_t)

# ---- 2. annihilation
B = glider(SW, 0, 4, 1)
assert B == W(4, 1, [2, 1, 7])
show("R2 annihilation at a right angle: SE glider and SW glider", [("gliderA", A), ("gliderB", B)], 4, set())
B = glider(NW, 0, 4, 0)
show("R2' annihilation head-on: SE glider and NW glider", [("gliderA", A), ("gliderB", B)], 3, set())

# ---- 3. kickback
B = glider(SW, 1, 2, 4)
out = glider(NW, 2, 1, 3)
show("R3 kickback: SE glider A meets SW glider B; B is destroyed and A returns as an NW glider",
     [("gliderA", A), ("gliderB", B)], 10, out)
B = glider(NW, 2, 0, 6)
out = glider(NW, 1, 1, 1)
show("R3' head-on collision leaving one NW glider on the line of A",
     [("gliderA", A), ("gliderB", B)], 6, out)

# ---- 4. block pull and push (salvos travelling SE along the register)
block = W(7, 11, [3, 3])             # counter 0 of Theory/Life/SlidingBlock.lean
pull = W(0, 5, [2, 4, 647, 768, 256])
check("pull_zero (Lean)", pull | block, 26, W(6, 10, [3, 3]))
g1, g2 = glider(SE, 0, 0, 5), glider(SE, 1, 7, 6)
assert g1 | g2 == pull
show("R4 pull, block displaced by (-1,-1): the salvo pullSalvo of SlidingBlock.lean (rediscovered)",
     [("block", block), ("glider1", g1), ("glider2", g2)], 26, W(6, 10, [3, 3]),
     "this is pull_zero; the search finds it one generation earlier (normal form, n = 27)", True)
push = W(0, 0, [4, 8, 14, 0, 0, 2, 4, 647, 768, 256])
g3 = glider(SE, 0, 1, 0)
assert g1 | g2 | g3 == push
show("R5 push, block displaced by (+1,+1): the salvo pushSalvo of SlidingBlock.lean (rediscovered)",
     [("block", block), ("glider1", g1), ("glider2", g2), ("glider3", g3)], 32, W(8, 12, [3, 3]),
     "this is push_zero; the search finds it one generation earlier (normal form, n = 33)", True)
b0 = W(0, 0, [3, 3])
show("R5' push, block displaced by (+1,+1): the shortest three-glider salvo found",
     [("block", b0), ("glider1", glider(SE, 0, -2, -5)), ("glider2", glider(SE, 3, -8, -5)),
      ("glider3", glider(SE, 1, -5, -10))], 19, W(1, 1, [3, 3]))

# ---- 5. zero test (frame of SlidingBlock.lean: counter k = ofRows (7 + k) (11 + k) [3, 3])
test = glider(SW, 0, 5, 6)
assert test == W(5, 6, [2, 1, 7])
moved = W(8, 9, [3, 3])
show("R6 zero test: an SW glider is destroyed by the block at position 0, which moves by (1,-2)",
     [("block", block), ("test", test)], 9, moved, "frame of SlidingBlock.lean: the block is counter 0", True)
restore = W(6, 15, [2, 6, 5])
assert identify_glider(restore) == (NE, 1, 6, 16)
show("R6 zero test with restoring NE glider: both gliders destroyed, block back at position 0",
     [("block", block), ("test", test), ("restore", restore)], 20, block,
     "frame of SlidingBlock.lean: the block is counter 0", True)
# the test glider passes the block at every position k >= 1 at distance >= 3
for k in range(1, 40):
    bk = translate(block, k, k)
    d = min(distance(glider(SW, t, 5, 6), bk) for t in range(-40, 400))
    assert d >= 3, k
    assert first_difference([bk, glider(SW, -40, 5, 6)], max_gen=440) is None
print()
print("-- R6: the test glider ofRows 5 6 [2, 1, 7] (SW) stays at Chebyshev distance >= 3 from")
print("-- counter k for every k = 1..39 at every generation -40..400, and evolves freely")
print("-- (numerical observation)")

# ---- 6. unconditional zero test: a salvo of three SW gliders (same frame)
salvo = [(SW, 0, 6, 6), (SW, 0, 5, 0), (SW, 2, 13, -3)]
parts = [("block", block)] + [("glider%d" % (i + 1), glider(*g)) for i, g in enumerate(salvo)]
assert parts[1][1] == W(6, 6, [2, 1, 7]) and parts[2][1] == W(5, 0, [2, 1, 7]) \
    and parts[3][1] == W(13, -2, [1, 5, 3])
show("R7 unconditional zero test: three SW gliders are destroyed by the block at position 0, "
     "which is at position 0 again afterwards",
     parts, 33, block, "frame of SlidingBlock.lean: the block is counter 0", True)
dmin = {}
for k in range(1, 40):
    bk = translate(block, k, k)
    back = [glider(d, p - 160, x, y) for (d, p, x, y) in salvo]
    assert first_difference([bk] + back, max_gen=700) is None, k
    dmin[k] = [min(distance(glider(d, p + t, x, y), bk) for t in range(-160, 540))
               for (d, p, x, y) in salvo]
assert all(min(dmin[k]) >= 3 for k in range(2, 40))
print()
print("-- R7: for every k = 1..39 the three gliders, started 160 generations earlier, evolve freely")
print("-- past counter k for 700 generations.  Smallest Chebyshev distance of gliders 1, 2, 3 from")
print("-- counter k:  k = 1: %s;  k = 2: %s;  k = 3: %s;  at least 3 for all k = 2..39." % (
    dmin[1], dmin[2], dmin[3]))
print("-- So for k = 1 a glider passes at distance 2 without effect: this needs its own certificate,")
print("-- the separation lemma (distance > 2) does not apply.")
print("-- (numerical observation)")
print()
print("all recommended reactions re-checked")
