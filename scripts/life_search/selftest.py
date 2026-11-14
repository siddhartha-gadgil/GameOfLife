"""Cross-checks of the simulator `life.py`.  Run:  python3 selftest.py

The facts checked are either elementary (glider, blinker, still lifes) or are
theorems already proved in the Lean project (`pull_zero`, `push_zero`,
`pull_misplaced_block_ne` of Theory/Life/SlidingBlock.lean, `gosperGun_evolve_thirty`
of Theory/Life/Guns.lean); the windows below are copied from those Lean files.
"""
import random
from life import *


def check(name, cond):
    print("%-68s %s" % (name, "ok" if cond else "FAILED"))
    if not cond:
        raise SystemExit(1)


# glider: period 4, displacement (1, 1); the other directions
check("catalogue glider: 4 generations = translate (1,1)",
      evolve(GLIDER, 4) == translate(GLIDER, 1, 1))
check("catalogue glider: not a translate of itself after 1, 2, 3 generations",
      all(normalize(evolve(GLIDER, k)) != normalize(GLIDER) for k in (1, 2, 3)))
for d in DIRS:
    check("glider direction (%+d,%+d): 4 generations = translate by the direction" % d,
          evolve(glider(d), 4) == translate(glider(d), d[0], d[1]))
    check("glider direction (%+d,%+d): glider(d, t) = evolve t (glider(d, 0)), t = 0..11" % d,
          all(evolve(glider(d, 0, 5, 7), t) == glider(d, t, 5, 7) for t in range(12)))
    check("glider direction (%+d,%+d): negative times" % d,
          all(evolve(glider(d, -t, 5, 7), t) == glider(d, 0, 5, 7) for t in range(12)))
    check("glider direction (%+d,%+d): identify_glider inverts glider" % d,
          all(identify_glider(glider(d, r, 3, -8)) == (d, r, 3, -8) for r in range(4)))
check("glider(SE, 0, 0, 0) is the catalogue glider", glider((1, 1)) == set(GLIDER))
check("glider_at_time_zero", glider_at_time_zero(identify_glider(evolve(glider((-1, 1), 3, 4, 9), 30)), 30)
      == ((-1, 1), 3, 4, 9))

# blinker, block, eater
blinker = from_window(0, 0, [7])
check("blinker: one generation gives the vertical blinker",
      step(blinker) == {(1, -1), (1, 0), (1, 1)})
check("blinker: period 2", evolve(blinker, 2) == blinker)
check("block is a still life", step(BLOCK) == set(BLOCK))
check("eater 1 is a still life", step(EATER1) == set(EATER1))
check("eater 1 has 8 distinct orientations", len(set(all_symmetries(EATER1))) == 8)
check("glider has 8 distinct images", len(set(all_symmetries(GLIDER))) == 8)

# windows
check("window of the catalogue glider", to_window(GLIDER) == (0, 0, [2, 4, 7]))
check("parse_plaintext", parse_plaintext(".O.\n..O\nOOO") == set(GLIDER))
rnd = random.Random(1)
ok = True
for _ in range(200):
    c = {(rnd.randrange(-20, 20), rnd.randrange(-20, 20)) for _ in range(rnd.randrange(1, 60))}
    ok &= from_window(*to_window(c)) == c
    ok &= from_window(*to_window(c, (-25, -30))) == c
    ok &= parse_plaintext(to_plaintext(c), bbox(c)[0], bbox(c)[1]) == c
check("window and plaintext round trips (200 random configurations)", ok)

# facts proved in Lean: Theory/Life/SlidingBlock.lean
pull = from_window(0, 5, [2, 4, 647, 768, 256, 0, 384, 384])
check("pull_zero: evolve 26 (pullSalvo ∪ counter 0) = counter (-1)",
      evolve(pull, 26) == from_window(6, 10, [3, 3]))
push = from_window(0, 0, [4, 8, 14, 0, 0, 2, 4, 647, 768, 256, 0, 384, 384])
check("push_zero: evolve 32 (pushSalvo ∪ counter 0) = counter 1",
      evolve(push, 32) == from_window(8, 12, [3, 3]))
check("pull_misplaced_block_ne",
      evolve(from_window(0, 5, [2, 4, 647, 768, 256, 0, 768, 768]), 26) != from_window(7, 10, [3, 3]))
check("pullSalvo: 4 generations = translate (1,1)",
      evolve(from_window(0, 5, [2, 4, 647, 768, 256]), 4) == from_window(1, 6, [2, 4, 647, 768, 256]))

# fact proved in Lean: Theory/Life/Guns.lean
gun = from_window(0, 0, [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539,
                         16843776, 34816, 12288])
gun_glider = from_window(23, 9, [1, 6, 3])
check("gosperGun_evolve_thirty: evolve 30 gun = gun ∪ gunGlider", evolve(gun, 30) == gun | gun_glider)
check("gunGlider is glider (SE, phase 3) at (22, 8)",
      identify_glider(gun_glider) == ((1, 1), 3, 22, 8))

# bit-parallel engine against the set-based one
grid = BitGrid(40, 36)
ok = True
for trial in range(300):
    c = {(rnd.randrange(8, 32), rnd.randrange(8, 28)) for _ in range(rnd.randrange(1, 120))}
    g = grid.pack(c)
    for _ in range(40):
        if grid.near_edge(g):
            break
        g, c = grid.step(g), step(c)
        ok &= grid.unpack(g) == c
check("BitGrid.step agrees with step (300 random soups, up to 40 generations)", ok)

# settle
res = settle(glider((1, 1)) | translate(BLOCK, 30, 3))
check("settle: a glider that misses a block is seen as block + 1 escaping glider",
      res["rest"] == frozenset(translate(BLOCK, 30, 3)) and len(res["gliders"]) == 1)
res = settle(set(GLIDER) | translate(BLOCK, 40, 40), max_gen=100)
check("settle: a glider still approaching a block is not settled",
      res["rest"] is None or res["gen"] > 100)
print("all checks passed")
