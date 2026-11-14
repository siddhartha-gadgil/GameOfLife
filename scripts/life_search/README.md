# scripts/life_search/

An untrusted search tool ("oracle") for elementary reactions in Conway's Game of Life, written
for design D1 of research note `N-15` (guns, eaters, blocks and gliders only). It uses no
pattern files and no collision tables from the literature: the only patterns written down by
hand are the glider, the block and eater 1; everything else is found by exhaustive enumeration.

**Status of every result: numerical observation (own search), not verified in Lean.** The
scripts propose reactions; a reaction enters the library only through an evolution certificate
(`life_cert`) for the statement the script prints. A bug here can cost time, but cannot make a
false statement pass Lean.

Python 3 standard library only (tested with Python 3.12); no virtual environment is needed.

| Script | Purpose | Run time |
| --- | --- | --- |
| [`life.py`](life.py) | The simulator: set-based `step`/`evolve` (reference), `BitGrid` (bit-parallel on a bounded grid, for the large enumerations), plaintext parsing, the 8 symmetries, gliders in 4 directions and 4 phases (`glider`, `identify_glider`, `lane`), windows (`to_window`, `from_window`, `lean_window`), detection of a settled state as still lifes or oscillators plus escaping gliders (`settle`, `analyse`), and `reaction_record`, which prints a reaction as a Lean-ready record | – |
| [`selftest.py`](selftest.py) | Cross-checks of the simulator: glider, blinker, still lifes, window round trips, the bit engine against the set engine on random soups, and the facts already proved in Lean (`pull_zero`, `push_zero`, `pull_misplaced_block_ne`, `gosperGun_evolve_thirty`) | 1 s |
| [`two_glider.py`](two_glider.py) | (a) all collisions of two gliders (perpendicular, both cases, and head-on), classified; (b) which annihilations and one-glider outcomes survive when the gliders are members of period-30 streams | 20 s |
| [`eater.py`](eater.py) | (c) a glider against eater 1 in all 8 orientations and all lanes; absorption of a period-30 stream | 45 s |
| [`block_salvo.py`](block_salvo.py) | (d) a block and a salvo of 1, 2 or (`--three`) 3 gliders from one direction leaving only a block; displacement table; comparison with `pullSalvo` and `pushSalvo` of `Theory/Life/SlidingBlock.lean`; `--dump FILE` writes every hit that moves the block by at most 2 cells | 15 s; with `--three` about 3 hours of CPU time, divided by the number of cores |
| [`zero_test.py`](zero_test.py) | (e) one glider against a block from every direction; gliders restoring the block; free passage when the block is at `(k, k)`, `k ≥ 1`; search for an unconditional zero test with two gliders from any directions | 6 min of CPU time |
| [`zero_salvo.py`](zero_salvo.py) | (e) search for an unconditional zero test made of three gliders from one direction, all on lanes that pass a block one or more steps away | 25 min of CPU time, divided by the number of cores |
| [`recommended.py`](recommended.py) | Re-checks the recommended reactions of report `R-19` by direct simulation and prints their records; the cell data quoted in the report comes from here | 1 s |

The search scripts take `--records` to print the Lean-ready records of their notable reactions,
and the parallel ones (`block_salvo.py`, `zero_test.py`, `zero_salvo.py`) take `--jobs N`
(default: all cores). Typical use:

```bash
cd scripts/life_search
python3 selftest.py
python3 two_glider.py --records  > results/two_glider.txt
python3 eater.py --records       > results/eater.txt
python3 block_salvo.py --three --records --dump results/block_salvo_hits.txt > results/block_salvo.txt
python3 zero_test.py --records   > results/zero_test.txt
python3 zero_salvo.py --records  > results/zero_salvo.txt
python3 recommended.py           > results/recommended.txt
```

The outputs of the runs behind report `R-19`
(`notes/research/reports/R-19-elementary-reactions.md`) are kept in [`results/`](results/): one
text file per script, and `block_salvo_hits.txt`, the list of all block-moving salvos of two or
three gliders that displace the block by at most 2 cells in each coordinate (one per line:
displacement, duration, box, the gliders as lane/delay and as positions in the normal form).

## Conventions

Those of the Lean project. A cell is `(x, y)` with `x` to the right and `y` **downward**. A
window is `(x0, y0, rows)`: `rows` lists natural numbers, top row first, and bit `j` of
`rows[i]` (least significant bit = leftmost cell) is the cell `(x0 + j, y0 + i)`; this is
`ofRows x0 y0 rows`. The catalogue glider `ofRows 0 0 [2, 4, 7]` travels `(+1, +1)` every 4
generations.

A glider is `(d, phase, x, y)`: `d` is its direction (`SE = (1, 1)`, `SW = (-1, 1)`,
`NE = (1, -1)`, `NW = (-1, -1)`); phase 0 is the mirror image of the catalogue glider that
travels in direction `d`, with the upper left corner of its 3×3 box at `(x, y)`; phase `r` is
phase 0 evolved `r` generations. Its **lane** is `x - y` for `SE`, `NW` and `x + y` for `SW`,
`NE`. An output glider seen at generation `t` is also reported "at generation 0": the phase-0-to-3
glider that would have flown freely into it.

A **normal form** of a reaction fixes the starting generation: the largest multiple of 4 below
the first generation at which the configuration differs from its freely flying parts. Durations
`n` are counted from the normal form, so `n` is at most 4 more than the true length of the
interaction.

## Record format

`reaction_record` prints, for a list of labelled parts and a number of generations `n`, each part
and the union as `ofRows x0 y0 [rows]` in one frame (translated so that the bounding box of all
generations `0..n` has corner `(0, 0)`), the final configuration, the footprint box, and a
candidate statement `conway.evolve n (ofRows …) = ofRows …`. Positions and lanes of gliders in a
record refer to the frame of that record. The final configuration is recomputed by the set-based
engine when the record is printed.

## What "exhaustive" means here

Each script states its ranges in its docstring and prints a check that the extreme values of
the transverse parameter give no interaction. The bounded searches of `block_salvo.py`, of part 4 of
`zero_test.py` and of `zero_salvo.py` are exhaustive only within their stated ranges of lanes,
delays, duration and bounding box.
