# scripts/life_machine/

Untrusted oracle (plain Python 3, standard library only) that searches for the next components of
the register machine of design D1 (research note `N-15`): fan-out, reflector, salvo generators.
Results are **numerical observations (own search), not verified in Lean**; the report is
[`notes/research/reports/R-21-salvo-generators.md`](../../notes/research/reports/R-21-salvo-generators.md).

Nothing is taken from pattern collections. Inputs: the gun window of `Guns.lean`, the glider and
eater 1 of `Patterns.lean`, `blockedStream` of `Gates.lean`, the salvos of `SlidingBlock.lean`,
their symmetric images, translates and time shifts, and the catalogue of gate reactions computed
by `scripts/life_gates/s3_gate.py` (read-only; `results/s3_gate_4_90_1_0.json.gz` and
`results/s4_series_4_90_1_0.json.gz` there). The simulator and the gate code of
`scripts/life_gates` (`life.py`, `gates.py`) are imported, not copied.

Conventions: as in `scripts/life_gates/README.md` (cells `(x, y)`, `y` downward; windows
`ofRows x0 y0 [rows]`; symmetries `sym_k`; glider world lines `(d, lane, tau)` with
`lane = dy x - dx y`, `tau = t - 4 dx x`). An *assembly* `(k, vx, vy, s)` is `blockedStream`
transformed by `sym_k`, translated by `(vx, vy)` and delayed by `s` generations
(`machine.asm_cells`); a *reflector* `(k, p, q, s)` is the same for the reflector `RF0`.

## Files

| File | Purpose |
| --- | --- |
| `common.py` | imports of `life_gates`, data of the Lean files, cross-checks (`python3 common.py`) |
| `recipes.py`, `reactions.py` | settling of small configurations; the kickback and the side step as templates on world lines |
| `machine.py` | assemblies, composites, control gliders inserted at their entry time (`run_scheduled`), re-check with the set simulator on the unbounded plane (`verify_scheduled`) |
| `r0_obstruction.py` | which lanes parallel to its stream a gun leaves free |
| `r1_recipes.py` | slow free-glider recipes with one lane per direction (tree search) |
| `r2_three.py` | all collisions of three gliders SE + SW + NE |
| `r3_headon.py` | two head-on gated streams |
| `r4_stream.py` | one or two gliders against a free-running period-30 stream (shows that such a stream cannot be crossed at a right angle) |
| `r5_synth.py` | the pulling salvo from 3 gun gliders and 7 kicker gliders (free gliders) |
| `b1_single_lane.py` | single-lane salvos against the block |
| `q1_reflector.py` | period-30 reflector: queen bee shuttle of the gun + one stabiliser + one glider |
| `s1_shifter.py` | lane shifter from two terminated guns (negative: a period-30 stream cannot be crossed) |
| `f1_fanout.py` | fan-out with a second assembly on the line of the control glider (negative: 0 candidates) |
| `f2_roundtrip.py` | fan-out by a round trip through the source gate (77 verified) |
| `g1_pull.py`, `g2_pull.py` | pull-salvo generator from the fan-out and reflectors only (negative: parity) |
| `g4_pull3.py` | pull-salvo generator from one control glider: fan-out + third gate + three reflectors |
| `g5_clearance.py` | clearances of the flight segments of the recommended generator |
| `report_data.py` | windows of the recommended designs, each statement re-checked with the set simulator |
| `results/` | outputs quoted in `R-21` |

## Results in one paragraph

A gun shadows the parallel lanes `-23 .. +24` around its stream, and a period-30 stream cannot be
crossed at a right angle; so the gliders of a salvo (lanes 6 apart) cannot come from one gate
each. Found instead: the reflector `RF0` (queen bee shuttle + eater, right-angle turn, period 30);
a fan-out by a round trip through the source gate (`results/f2_roundtrip.txt`, 77 placements); and
the pull-salvo generator `PG1` (`results/pg1.json`): `blockedStream`, two more copies of it and
three reflectors, `evolve 1170 (R ∪ C) = R ∪ translate (51, 143) pullSalvo`, reuse spacing 330.
Push salvo and continue glider: not done.

## Reproducing the runs of R-21

```bash
cd scripts/life_machine
python3 common.py                                  # cross-checks against the Lean files
python3 r0_obstruction.py   > results/r0_obstruction.txt      # 3.5 min
python3 r1_recipes.py 5     > results/r1_recipes_5.txt        # 1 min
python3 r1_recipes.py 9 sides
python3 r2_three.py         > results/r2_three.txt            # 42 min
python3 r3_headon.py 4      > results/r3_headon_4.txt         # 1 min
python3 r4_stream.py one
python3 r5_synth.py         > results/r5_synth.txt            # 4 min
python3 b1_single_lane.py   > results/b1_single_lane.txt      # 1 min
python3 q1_reflector.py     > results/q1_reflector.txt        # 20 s
python3 s1_shifter.py 24    > results/s1_shifter_24.txt
python3 f1_fanout.py 41 24  > results/f1_fanout_41_24.txt     # 4 min
python3 f2_roundtrip.py     > results/f2_roundtrip.txt        # 35 s
python3 g1_pull.py; python3 g2_pull.py > results/g2_pull.txt
python3 -u g4_pull3.py 130  > results/g4_pull3.txt            # see the note below
python3 g5_clearance.py     > results/g5_clearance.txt
python3 report_data.py reflector            > results/report_reflector.txt
python3 report_data.py fanout 0 35 62 25 420 450   > results/report_fanout.txt
python3 report_data.py fanout 7 90 132 25 300 330  > results/report_fanout_k7.txt
python3 report_data.py generator 300 330 360       > results/report_generator.txt
```

All searches are deterministic. `r4_stream.py two` (two gated gliders against a stream) is
implemented but was not run.

Note on `g4_pull3.py`: enumeration (30 s) and the geometric filters (60 s) leave 130 candidates,
written to `results/g4_candidates.json.gz`; the simulations print one line each. The first 45
finish within 80 s and are all verified; after that the run makes no visible progress (not
investigated) and was stopped, so the last lines of the script (summary, writing
`results/g4_pull3.json.gz`) were not reached: that file was assembled from the log
(`results/g4_pull3.txt`) and the candidate file. The recommended design `PG1`
(`results/pg1.json`) is one of the 130 candidates; it was verified in an earlier run of the same
search and every statement about it is asserted again by `report_data.py generator` (set
simulator on the unbounded plane, including the block for `k = 0 .. 3` and the reuse test).

## What a search accepts

* *Composite reaction* (`machine.run_scheduled`, `verify_scheduled`): the union of the pieces is
  periodic with period 30 (asserted); each control glider is inserted just before it comes within
  4 cells of the bounding box of the whole composite; gliders are removed once they are more than
  13 cells outside it and fly away; the run succeeds when the configuration equals the cycle
  again. Then, with the set simulator on the unbounded plane: cycle at a time `T ≡ 0 (mod 30)`
  plus all control gliders (in free flight) evolves in `N ≡ 0 (mod 30)` generations to the cycle
  plus exactly the recorded gliders, each at distance at least 3 from every other live cell.
* *Reuse* with spacing `T`: the same with a second control glider `T` generations later; the
  result must be the two sets of output gliders, `T` generations apart.
* *Block test*: the same with a block `counter k` (translated) added; the result must be the
  cycle and the block at `k - 1`, and nothing else.
