# scripts/life_gates/

Untrusted oracle (plain Python 3, standard library only) that searches for components built from
Gosper glider guns for design D1 of research note `N-15`: a terminated gun, blocked streams and
gates. Results are **numerical observations (own search), not verified in Lean**; the report is
[`notes/research/reports/R-20-gun-gates.md`](../../notes/research/reports/R-20-gun-gates.md).

Nothing here is taken from pattern collections: the only inputs are the gun window of
`LeanTheory/Theory/Life/Guns.lean`, the glider, the block and eater 1 of
`LeanTheory/Theory/Life/Patterns.lean`, their 8 symmetric images and their time shifts.

## Conventions

A cell is `(x, y)`, `x` to the right, `y` downward. A window is `(x0, y0, rows)`: `rows` lists
naturals, top row first, bit `j` of `rows[i]` (least significant bit = leftmost) is the cell
`(x0 + j, y0 + i)`; printed as `ofRows x0 y0 [rows]`.

Symmetries `sym_k`, `k = 0 .. 7` (`life.SYMS`), with the image of the stream direction `(1, 1)`:

| k | map | direction | k | map | direction |
| --- | --- | --- | --- | --- | --- |
| 0 | `(x, y)` | `(1, 1)` | 4 | `(-x, y)` | `(-1, 1)` |
| 1 | `(-y, x)` | `(-1, 1)` | 5 | `(x, -y)` | `(1, -1)` |
| 2 | `(-x, -y)` | `(-1, -1)` | 6 | `(y, x)` | `(1, 1)` |
| 3 | `(y, -x)` | `(1, -1)` | 7 | `(-y, -x)` | `(-1, -1)` |

A glider is described by its **world line** `(d, lane, tau)`: `d = (dx, dy)` is the direction,
and if at time `t` the glider is the canonical glider `S_d` (the image of `Pattern.glider` under
the coordinate flips taking `(1, 1)` to `d`, bounding box origin at `(x, y)`), then
`lane = dy * x - dx * y` and `tau = t - 4 * dx * x`. Both are constant in flight;
`life.glider_at(d, lane, tau, t)` gives the cells at time `t`. The gliders of the gun of
`Guns.lean` have `d = (1, 1)`, `lane = 14`, `tau ≡ -61 ≡ 29 (mod 30)`.

## Files

| File | Purpose |
| --- | --- |
| [`life.py`](life.py) | Simulator: `step_cells` (sets of cells, unbounded plane, the reference) and `Board` (bit-parallel on a rectangle, one Python integer per configuration; faithful while no live cell is on the outer ring, which every search checks). Windows, symmetries, glider world lines, `run_periodic`. `python3 life.py` runs the self test, including `gosperGun_evolve_thirty`: gun after 30 generations = gun + window `(23, 9, [1, 6, 3])` |
| [`s1_eater.py`](s1_eater.py) | Search 1: gun + one eater 1, period 30 |
| [`s2_blocked.py`](s2_blocked.py) | Search 2: two guns whose streams annihilate (`right`, `centered`, `headon`) |
| [`s2_summary.py`](s2_summary.py) | Tables of R-20 from a result file of `s2_blocked.py` (classes, generic region, most compact solutions) |
| [`gates.py`](gates.py) | Common code for gates: the periodic cycle as a reference, insertion of control gliders, removal and classification of escaping gliders, independent re-check with the set simulator |
| [`s3_gate.py`](s3_gate.py) | Search 3: all control glider world lines for one blocked stream |
| [`s4_series.py`](s4_series.py) | Search 4: repeated control gliders (30 and 60 generations later) and two gates in series |
| [`report_data.py`](report_data.py) | Windows of the recommended designs, each statement re-checked with the set simulator |
| `results/` | Outputs of the runs quoted in `R-20`: `.txt` summaries, `_tables.txt` (from `s2_summary.py`) and `.json.gz` full data. The three largest data files (`s2_right_15_60`, `s2_centered_5_60`, `s2_headon_30_120_10`, 1 – 5 MB each) are not kept; the commands below regenerate them |

## Reproducing the runs of R-20

```bash
cd scripts/life_gates
python3 life.py                                   # self test
python3 s1_eater.py > results/s1_eater.txt
python3 s2_blocked.py right 15 60      > results/s2_right_15_60.txt       # 10 min
python3 s2_blocked.py centered 5 60    > results/s2_centered_5_60.txt     # 35 min
python3 s2_blocked.py centered 0 8     > results/s2_centered_0_8.txt
python3 s2_blocked.py centered -6 3    > results/s2_centered_-6_3.txt
python3 s2_blocked.py headon 30 120 10 > results/s2_headon_30_120_10.txt  # 11 min
python3 s2_blocked.py headon 2 30 10   > results/s2_headon_2_30_10.txt
python3 s2_summary.py results/s2_centered_5_60.json.gz > results/s2_centered_5_60_tables.txt   # etc.
python3 s3_gate.py 4 90 1 0   > results/s3_gate_4_90_1_0.txt      # blocked stream (k, dx, dy, p)
python3 s4_series.py 4 90 1 0 > results/s4_series_4_90_1_0.txt    # needs the s3 result file
python3 s3_gate.py summary results/s3_gate_4_90_1_0.json.gz       # print a summary again
python3 report_data.py blocked 4 90 1 0                           # windows; see R-20, section 7
```

The searches use up to 20 processes (`multiprocessing`); they are deterministic. Run times are
given in `R-20` (wall times on a shared 22-thread machine).

A blocked stream is named `(k, dx, dy, p)`: gun A is the gun of `Guns.lean` at generation
`max(0, -p)`, gun B is `sym_k` of the gun at generation `max(0, p)`, translated by `(dx, dy)`.
The recommended one is `(4, 90, 1, 0)`: `gosperGun` and its mirror image translated by `(90, 1)`.

## What a search accepts

* *Periodic*: `state(t0) = state(t0 + 30)` for a transient `t0`, hence for all later times; the
  equality is also compared explicitly up to generation 3000, no live cell ever reaches the outer
  ring of the board, and the least period is 30. `gun intact` means that on the rows of the gun
  body the configuration agrees with the free gun during a whole cycle.
* *Gate*: after the control glider is inserted at a time when it is at Chebyshev distance at
  least 3 from every live cell (so it has not interacted), the configuration becomes exactly the
  periodic cycle again, apart from gliders that fly away; these are removed once they are more
  than 13 cells outside the envelope and recorded with their world lines. The result is then
  re-checked from scratch with the set simulator on the unbounded plane.
