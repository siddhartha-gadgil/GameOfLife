# R-20: Terminated gun, blocked streams and gates from Gosper guns (own search)

**Status of every result in this report: numerical observation (own search), not verified in
Lean.** The data were produced on 2026-11-14 by the untrusted oracle
[`scripts/life_gates/`](../../../scripts/life_gates/README.md), written for this report; the
only inputs are the gun window of `LeanTheory/Theory/Life/Guns.lean`, `Pattern.glider`,
`Pattern.block` and `Pattern.eater1` of `Patterns.lean`, their 8 symmetric images and time
shifts. No pattern file, placement or collision table from the literature was used. The report
serves design D1 of `N-15` (blocked stream, gate, fan-out).

## Summary

| Item | Result | Recommended design |
| --- | --- | --- |
| 1. Terminated gun | 96 placements of one eater absorb every glider with period 30 and leave the gun untouched (48 on each of two diagonals); 5 closer placements also give period 30 but change a few cells of the gun during glider formation | `gosperGun ∪ ofRows 25 11 [3, 5, 4, 12]`: an oscillator of period 30 **from generation 0**, box 36 × 15 |
| 2. Blocked stream, right angle | Period 30 is possible for every placement: for each of the 4 right-angle symmetries and each translation, 4 or 14 of the 59 relative timings annihilate (according to the parity of the placement); 212 348 solutions in the range searched, in 72 generic classes | `gosperGun ∪ ofRows 55 1 [mirror gun]` (both guns at generation 0), transient 81, box 91 × 33, collision of 5 generations per period; most compact: 37 × 23 with transient 0 |
| 2′. Blocked stream, head-on | Exists for 13 lane offsets, 32 580 clean solutions in the range | `gosperGun ∪` (gun rotated by 180°) translated by `(70, 38)`, box 71 × 39 |
| 3. Gate | 3 414 control world lines act as a gate on the recommended blocked stream (961 with the control glider arriving from infinity), in all 4 directions of the control glider; 51 kickbacks | control glider `ofRows 47 6 [2, 4, 7]` (= `Pattern.glider` translated): after 90 generations the cycle is restored and one glider of stream A has escaped |
| 4. Repetition, series | 712 of the 961 gates accept control gliders 30 and 60 generations apart; 228 translations of a second copy put two gates in series | second gate = first translated by `(9, 40)`, box 100 × 73, 240 generations |

Not found / negative: the kickback gates tested (one of each family) cannot be used again 30 or
90 generations later (the returning glider meets the next control glider); the exactly
mirror-symmetric right-angle pairs (`Δ = 0`) have period 60, not 30; only 2 of the 8 orientations
of the eater terminate a stream with period 30. Not searched: gates on head-on pairs (a surviving
glider stays on the lane of the opposite stream, so it cannot leave the assembly); gates with
two simultaneous control gliders; blocked streams other than the two named in section 6.

## 0. Method, conventions, cross-check

* **Simulators** (`scripts/life_gates/life.py`). `step_cells`: Conway's rule on finite sets of
  cells in the unbounded plane. `Board`: the same rule on a rectangle stored as one Python integer
  (bit-parallel); a run is rejected as soon as a live cell reaches the outer ring of the
  rectangle. The searches use `Board`; every recommended design and every gate reported in
  section 3 was re-checked with `step_cells`.
* **Cross-check against `Guns.lean`** (`python3 life.py`): the gun after 30 generations is the gun
  plus the window `(23, 9, [1, 6, 3])` (`gosperGun_evolve_thirty`); after 300 generations it is
  the gun plus the 10 gliders `evolve (30 j) gunGlider`, `j = 0 .. 9` (`gosperGun_evolve`); the two
  simulators agree on the gun at each of the 300 generations; `gunGlider` moves by `(1, 1)` in 4
  generations.
* **Conventions**: cells `(x, y)`, `y` downward; windows `ofRows x0 y0 [rows]` as in the project.
  Symmetries `sym_k` (matrix acting on `(x, y)`; image of the direction `(1, 1)`):
  `0` identity; `1` `(-y, x)` → `(-1, 1)`; `2` `(-x, -y)` → `(-1, -1)`; `3` `(y, -x)` → `(1, -1)`;
  `4` `(-x, y)` → `(-1, 1)`; `5` `(x, -y)` → `(1, -1)`; `6` `(y, x)` → `(1, 1)`; `7` `(-y, -x)` →
  `(-1, -1)`.
* **World line of a glider** `(d, lane, tau)`: `d = (dx, dy)` its direction; at the times
  `t ≡ tau (mod 4)` the glider is `ofRows x y S_d` with `x = dx (t - tau) / 4` and
  `y = dx (dy x - lane)`, where `S_(1,1) = [2, 4, 7]` (`Pattern.glider`), `S_(-1,1) = [2, 1, 7]`,
  `S_(1,-1) = [7, 4, 2]`, `S_(-1,-1) = [7, 1, 2]`. So `lane = dy x - dx y` and
  `tau = t - 4 dx x`. The stream of `gosperGun` is `d = (1, 1)`, `lane = 14`, `tau ≡ 29 (mod 30)`.
* **Periodicity** of a bounded run: the least `t0` with `state(t0) = state(t0 + 30)` is reported
  as the *transient* (then `state(t) = state(t + 30)` for all `t ≥ t0`); the equality was also
  compared explicitly for all `t` up to 3000, and the least period was checked to be 30.

## 1. Terminated gun (gun + one eater 1)

**Search** (`s1_eater.py`, 6 s): the 8 orientations `sym_k eater1` (translated so that the
bounding box starts at `(ex, ey)`), all `(ex, ey)` with `16 ≤ ex ≤ 72`, `ey ≥ 4`,
`|ex - ey - 14| ≤ 14` (a band of 29 lanes around the stream); 12 136 placements, of which 11 664
are at Chebyshev distance ≥ 3 from the gun at generation 0 and were simulated.

**Result.** 428 runs become periodic with period 30 and 189 with period 60; in the other 11 047 a
glider or debris leaves the box. Of the 428, 327 are wrecks (least period 1, 2 or 6), and 101
have least period 30:

* **96 proper terminations** (the rows `0 .. 8` of the gun agree with the free gun at every
  generation of the cycle; the eater is at rest during 24 of the 30 generations):
  * orientation `k = 0` (the eater exactly as `Pattern.eater1`) at `(25 + n, 11 + n)`,
    `n = 0 .. 47`; transient `0` for `n = 0` and `4 n - 1` for `n ≥ 1`;
  * orientation `k = 6` (the transposed eater, rows `[3, 1, 14, 8]`) at `(25 + n, 12 + n)`,
    `n = 0 .. 47`; transient `4 n + 1`.

  So an eater on the stream at any distance terminates it, on exactly one lane for each of the
  two orientations; the other six orientations never give period 30.
* **5 closer placements**, all with transient 0, in which the eater suppresses the glider while
  it forms (a few cells in the rows 7 and 8 differ from the free gun during the generations
  14 .. 27 of the cycle): `k = 0` at `(22, 9)`, `(23, 9)`, `(24, 10)`; `k = 6` at `(23, 10)`,
  `(24, 11)`. The smallest bounding box of all is `k = 0` at `(22, 9)` or `(23, 9)`: 36 × 13.
* Period 60 with the gun intact occurs for 186 placements in the orientations `k = 1, 2, 5, 7`
  (not needed; listed in `results/s1_eater.txt`).

**Recommended T1** (smallest box among the proper terminations, earliest periodicity):

```text
Terminated gun: gun + eater (orientation 0) at (25, 11)
  gun:                         ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  eater:                       ofRows 25 11 [3, 5, 4, 12]   -- 7 cells, box x 25..28, y 11..14
  whole (generation 0):        ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 0, 0, 100663296, 167772160, 134217728, 402653184]   -- 43 cells, box x 0..35, y 0..14
  checked: state(t) = state(t + 30) for 0 <= t <= 3000, least period 30; transient 0
  envelope over a cycle: x 0..35, y 0..14
........................O...........
......................O.O...........
............OO......OO............OO
...........O...O....OO............OO
OO........O.....O...OO..............
OO........O...O.OO....O.O...........
..........O.....O.......O...........
...........O...O....................
............OO......................
....................................
....................................
.........................OO.........
.........................O.O........
...........................O........
...........................OO.......
```

The reference configuration is the initial one: `evolve 30 (gosperGun ∪ eater) = gosperGun ∪ eater`.
Proposed Lean statement: `IsOscillator (gosperGun ∪ translate (25, 11) Pattern.eater1) 30`.

**Most compact T0** (the gun's rows 7, 8 are changed during glider formation):

```text
Terminated gun: gun + eater (orientation 0) at (22, 9)
  gun:                         ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  eater:                       ofRows 22 9 [3, 5, 4, 12]   -- 7 cells, box x 22..25, y 9..12
  whole (generation 0):        ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 12582912, 20971520, 16777216, 50331648]   -- 43 cells, box x 0..35, y 0..12
  checked: state(t) = state(t + 30) for 0 <= t <= 3000, least period 30; transient 0
  envelope over a cycle: x 0..35, y 0..12
```

**A termination at a distance** (example `n = 5`; the periodic configuration contains one glider
in flight, which is `gunGlider`):

```text
Terminated gun: gun + eater (orientation 0) at (30, 16)
  gun:                         ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  eater:                       ofRows 30 16 [3, 5, 4, 12]   -- 7 cells, box x 30..33, y 16..19
  whole (generation 0):        ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 0, 0, 0, 0, 0, 0, 0, 3221225472, 5368709120, 4294967296, 12884901888]   -- 43 cells, box x 0..35, y 0..19
  checked: state(t) = state(t + 30) for 19 <= t <= 3000, least period 30; transient 19
  envelope over a cycle: x 0..35, y 0..19
  periodic at generation 30:   ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 8388608, 50331648, 25165824, 0, 0, 0, 0, 3221225472, 5368709120, 4294967296, 12884901888]   -- 48 cells, box x 0..35, y 0..19
    glider in flight:          ofRows 23 9 [1, 6, 3]   -- 5 cells, box x 23..25, y 9..11
```

## 2. Blocked streams (two guns)

### 2.1 Enumeration

`s2_blocked.py`. The initial configuration for a signed phase `p` is

```text
evolve pA gosperGun  ∪  translate (dx, dy) (sym_k (evolve pB gosperGun)),
(pA, pB) = (0, p) if p ≥ 0,   (-p, 0) if p < 0.
```

Gun A has the stream direction `(1, 1)`. Right angle: `k = 1, 4` (stream of B in direction
`(-1, 1)`) and `k = 3, 5` (direction `(1, -1)`); head-on: `k = 2, 7`. With `cA = (24, 10)` the
centre of the first glider of A and `cB = sym_k (24, 10) + (dx, dy)` that of B, the lanes cross
at `P = cA + a (1, 1) = cB + b dB`; `a` and `b` (distances of the crossing point from the two
emission points, in diagonal cells) are both integers or both half-integers. A triple is a
*solution* if the run never leaves the box (guns and crossing point plus 14 cells), is periodic
with least period 30 up to generation 3000, and both gun bodies agree with the free gun during a
whole cycle.

Negative `p` is needed: with `0 ≤ p < 30` only, half of the annihilating timings start with one
unpaired glider that escapes. Three runs:

| Run | Range | Jobs | Period 30, guns intact | Wall time (20 processes, shared machine) |
| --- | --- | --- | --- | --- |
| `right 15 60` | `15 ≤ a, b ≤ 60`, 4 141 translations × 4 symmetries, `-30 < p < 30` | 977 276 | 44 030 | 622 s |
| `centered 5 60` | `5 ≤ a, b ≤ 60`, 6 161 translations × 4 symmetries, `|p - 4 (b - a)| < 30` | 1 453 996 | 212 348 | 2 089 s |
| `centered 0 8`, `centered -6 3` | very small distances | 34 220, 42 716 | 1 112, 102 | 15 s, 11 s |

The first run is the enumeration asked for (both guns within one period of generation 0); it
finds fewer solutions only because for `|b - a| > 7` no `p` with `|p| < 30` pairs the first
gliders. The second run moves the window of `p` with the placement and is exhaustive over the
periodic configurations. In it: 1 193 654 runs leave the box, 35 234 have period 60 with intact
guns, 11 085 are degenerate (a gun damaged; least period 1, 2, 6, or period 30 or 60 with a
disturbed gun), 1 653 placements overlap, and 22 were still aperiodic at generation 1800
(unresolved, all at small distances).

### 2.2 The classes: which timings annihilate

**Observation.** The outcome depends only on `k`, on the parity of `2a`, and on

```text
Δ = 4 (b - a) - p
```

(the arrival time of the first glider of B at the crossing point minus that of A), as long as
the guns are far enough apart: all translations with `min(a, b) > 7` (`k = 1, 3`), `> 12.5`
(`k = 4`), `≥ 5.5` (`k = 5`) behave identically. The annihilating values, each with the number of
generations per period during which something other than guns and gliders is present:

| `k` | parity | values of `Δ` giving period 30 (reaction length) |
| --- | --- | --- |
| 4, 5 | `a, b` integers | `±5` (6), `±6` (13), `±7` (10), `±8` (9), `±13` (13), `±14` (15), `±15` (7) |
| 4, 5 | half-integers | `±4` (5), `±11` (6) |
| 1 | integers | `-13` (6), `-6` (5), `2` (5), `9` (6) |
| 1 | half-integers | `-17` (7), `-16` (15), `-15` (13), `-10` (9), `-9` (10), `-8` (13), `-7` (6), `3` (6), `4` (13), `5` (10), `6` (9), `11` (13), `12` (15), `13` (7) |
| 3 | integers | `-9` (6), `-2` (5), `6` (5), `13` (6) |
| 3 | half-integers | the negatives of the list for `k = 1` |

So for every symmetry and every placement of two guns at a right angle there are 4 or 14
annihilating timings with `|Δ| < 30` (4 or 13 residues of `Δ` mod 30): **period 30 is always
possible**; a period 60 or 120 clock is not needed. In all 212 348 solutions each pair of
gliders annihilates completely before the next pair arrives (no permanent debris).

Further observations:

* **Two cycles for the same guns** (surprising). `Δ` and `Δ ± 30` describe the same streams,
  paired differently. Both annihilate for `k = 4, 5`: `Δ = 15` and `-15`; `k = 1`: `13` and
  `-17`; `k = 3`: `17` and `-13`. There the same two guns with the same relative phase have two
  different period-30 cycles (each glider of A is hit by the glider of B arriving 15 generations
  after it, or by the one arriving 15 generations before it), and which one occurs depends on
  which gun fires first. Checked directly for `(4, 108, 0, 15)` and `(4, 108, 0, -15)`: the two
  cycles have no configuration in common (here they are mirror images of each other). For all
  other annihilating `Δ` the timing `Δ ± 30` lets the first glider escape.
* **Period 60** with intact guns occurs for `Δ = 0` (`k = 4, 5`, integers; this includes the
  exactly mirror-symmetric pairs), `Δ = ±12` (`k = 4, 5`, half-integers), `Δ = -14, 10` and `-2`
  (`k = 1`), `-10, 14` and `2` (`k = 3`); something other than guns and gliders is present
  during 27 or 41 of the 60 generations.
* **Both guns at generation 0** (`p = 0`) requires `Δ = 4 (b - a)`: for `k = 4, 5` this means
  `b = a ± 1` (half-integers, `Δ = ±4`, the shortest reaction) or `b = a ± 2` (integers,
  `Δ = ±8`).
* A special class `Δ = ±22` (`k = 5`) occurs only for `a = 5` or `b = 5` (56 solutions each).

### 2.3 Compact solutions

From `results/s2_centered_*_tables.txt` (envelope = bounding box of the whole cycle):

| Design | `(k, dx, dy, p)` | `a, b` | Transient | Envelope | Remark |
| --- | --- | --- | --- | --- | --- |
| most compact found | `(5, 1, 22, 0)` or `(5, -1, 22, 0)` | 1.5, 0.5 | 0 | 37 × 23 | the gliders are destroyed while forming; no glider in free flight |
| | `(5, 0, 23, ±4)` | 1.5, 1.5 | 0 | 36 × 24 | same |
| most compact, `a, b ≥ 5` | `(5, 0, 30, ±15)`, `(5, 0, 30, ±5)`, … | 5, 5 | 12 – 61 | 36 × 31 | 16 timings at this placement |
| `p = 0`, `a, b ≥ 5` | `(5, 1, 32, 0)` | 6.5, 5.5 | 19 | 37 × 33 | B is the gun reflected in a horizontal line, below A |
| `k = 4`, most compact | `(4, 74, ±1, 0)`, `(4, 74, ±1, ∓8)` | 13.5, 12.5 | 49, 45 | 75 × 25 | B is the mirror image, beside A |
| `k = 1`, most compact | `(1, 47, -11, -21)`, `(1, 47, -11, -14)` | 8, 5 | 13, 15 | 48 × 36 | B rotated by 90° |
| `k = 3`, most compact | `(3, 11, 47, 21)`, `(3, 11, 47, 14)` | 5, 8 | 13, 15 | 36 × 48 | |
| **recommended for gates** | `(4, 90, 1, 0)` | 21.5, 20.5 | 81 | 91 × 33 | section 2.4 |

**Most compact blocked pair BS0** (period 30 from generation 0; proposed statement
`IsOscillator (gosperGun ∪ ofRows 1 14 [...]) 30`):

```text
Blocked stream (k, dx, dy, p) = (5, 1, 22, 0)
 initial configuration (generation 0): gun A at generation 0 of its cycle, gun B = sym_5 of the gun at generation 0, translated by (1, 22)
  gun A:                       ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  gun B:                       ofRows 1 14 [12288, 34816, 16843776, 21185539, 3212291, 51542788096, 51542765568, 20971520, 16777216]   -- 36 cells, box x 1..36, y 14..22
  whole (generation 0):        ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 0, 0, 0, 0, 0, 24576, 69632, 33687552, 42371078, 6424582, 103085576192, 103085531136, 41943040, 33554432]   -- 72 cells, box x 0..36, y 0..22
 transient 0 (state(t) = state(t + 30) exactly from generation 0 on; least period 30)
 periodic configuration R0 at the reference generation tref = 0 (set simulator: evolve 0 of the initial configuration = R0, evolve 30 R0 = R0)
  R0 (whole):                  ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 0, 0, 0, 0, 0, 24576, 69632, 33687552, 42371078, 6424582, 103085576192, 103085531136, 41943040, 33554432]   -- 72 cells, box x 0..36, y 0..22
    gun A (gun at generation 0): ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
    gun B (sym_5 of the gun at generation 0): ofRows 1 14 [12288, 34816, 16843776, 21185539, 3212291, 51542788096, 51542765568, 20971520, 16777216]   -- 36 cells, box x 1..36, y 14..22
  envelope over a cycle: x 0..36, y 0..22  (37 x 23)
  streams (direction, lane, tau mod 30): [((1, -1), -35, 25), ((1, 1), 14, 29)]
........................O............
......................O.O............
............OO......OO............OO.
...........O...O....OO............OO.
OO........O.....O...OO...............
OO........O...O.OO....O.O............
..........O.....O.......O............
...........O...O.....................
............OO.......................
.....................................
.....................................
.....................................
.....................................
.....................................
.............OO......................
............O...O....................
...........O.....O.......O...........
.OO........O...O.OO....O.O...........
.OO........O.....O...OO..............
............O...O....OO............OO
.............OO......OO............OO
.......................O.O...........
.........................O...........
```

**Compact pair with free gliders BS2**, `(5, 1, 32, 0)`:

```text
Blocked stream (k, dx, dy, p) = (5, 1, 32, 0)
 initial configuration (generation 0): gun A at generation 0 of its cycle, gun B = sym_5 of the gun at generation 0, translated by (1, 32)
  gun A:                       ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  gun B:                       ofRows 1 24 [12288, 34816, 16843776, 21185539, 3212291, 51542788096, 51542765568, 20971520, 16777216]   -- 36 cells, box x 1..36, y 24..32
  whole (generation 0):        ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24576, 69632, 33687552, 42371078, 6424582, 103085576192, 103085531136, 41943040, 33554432]   -- 72 cells, box x 0..36, y 0..32
 transient 19 (state(t) = state(t + 30) exactly from generation 19 on; least period 30)
 periodic configuration R0 at the reference generation tref = 30 (set simulator: evolve 30 of the initial configuration = R0, evolve 30 R0 = R0)
  R0 (whole):                  ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 8388608, 50331648, 25165824, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50331648, 100663296, 16777216, 24576, 69632, 33687552, 42371078, 6424582, 103085576192, 103085531136, 41943040, 33554432]   -- 82 cells, box x 0..36, y 0..32
    gun A (gun at generation 0): ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
    gun B (sym_5 of the gun at generation 0): ofRows 1 24 [12288, 34816, 16843776, 21185539, 3212291, 51542788096, 51542765568, 20971520, 16777216]   -- 36 cells, box x 1..36, y 24..32
    glider (1, 1) lane 14 tau -91: ofRows 23 9 [1, 6, 3]   -- 5 cells, box x 23..25, y 9..11
    glider (1, -1) lane -45 tau -95: ofRows 24 21 [3, 6, 1]   -- 5 cells, box x 24..26, y 21..23
  envelope over a cycle: x 0..36, y 0..32  (37 x 33)
  streams (direction, lane, tau mod 30): [((1, -1), -45, 25), ((1, 1), 14, 29)]
```

**Most compact side-by-side pair BS3**, `(4, 74, 1, 0)`:

```text
Blocked stream (k, dx, dy, p) = (4, 74, 1, 0)
 initial configuration (generation 0): gun A at generation 0 of its cycle, gun B = sym_4 of the gun at generation 0, translated by (74, 1)
  gun A:                       ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  gun B:                       ofRows 39 1 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792, 12582912]   -- 36 cells, box x 39..74, y 1..9
  whole (generation 0):        ofRows 0 0 [16777216, 1125899927814144, 5629551076978688, 6944552326215534592, 9826856036193076227, 28352960893265517954051, 28354236537859966305280, 18736100349768140800, 9799832789158211584, 6917529027641081856]   -- 72 cells, box x 0..74, y 0..9
 transient 49 (state(t) = state(t + 30) exactly from generation 49 on; least period 30)
 periodic configuration R0 at the reference generation tref = 60 (set simulator: evolve 60 of the initial configuration = R0, evolve 30 R0 = R0)
  R0 (whole):                  ofRows 0 0 [16777216, 1125899927814144, 5629551076978688, 6944552326215534592, 9826856036193076227, 28352960893265517954051, 28354236537859966305280, 18736100349768140800, 9799832789158211584, 6917529027649470464, 2251799864016896, 1688849885429760, 3377699720527872, 0, 0, 0, 0, 5368709120, 21996675006464, 13196287016960, 8796093022208]   -- 92 cells, box x 0..74, y 0..20
    gun A (gun at generation 0): ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
    gun B (sym_4 of the gun at generation 0): ofRows 39 1 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792, 12582912]   -- 36 cells, box x 39..74, y 1..9
    glider (1, 1) lane 14 tau -91: ofRows 23 9 [1, 6, 3]   -- 5 cells, box x 23..25, y 9..11
    glider (1, 1) lane 14 tau -121: ofRows 30 17 [5, 6, 2]   -- 5 cells, box x 30..32, y 17..19
    glider (-1, 1) lane 59 tau 167: ofRows 42 18 [5, 3, 2]   -- 5 cells, box x 42..44, y 18..20
    glider (-1, 1) lane 59 tau 197: ofRows 49 10 [4, 3, 6]   -- 5 cells, box x 49..51, y 10..12
  envelope over a cycle: x 0..74, y 0..24  (75 x 25)
  streams (direction, lane, tau mod 30): [((-1, 1), 59, 17), ((1, 1), 14, 29)]
```

### 2.4 Recommended blocked stream BS1 = `(4, 90, 1, 0)`

Gun B is the mirror image `sym_4` of the gun, translated by `(90, 1)`; both guns are at
generation 0 of their cycle at time 0. It is chosen because (i) `p = 0`; (ii) the collision is
the shortest one (`Δ = -4`, 5 generations per period); (iii) there are 20 cells of free stream on
each side of the crossing point, enough for control gliders arriving from infinity between the
guns (a control glider parallel to stream A must pass on a lane `≥ 39` to clear gun A); (iv) all
coordinates are non-negative.

```text
Blocked stream (k, dx, dy, p) = (4, 90, 1, 0)
 initial configuration (generation 0): gun A at generation 0 of its cycle, gun B = sym_4 of the gun at generation 0, translated by (90, 1)
  gun A:                       ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  gun B:                       ofRows 55 1 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792, 12582912]   -- 36 cells, box x 55..90, y 1..9
  whole (generation 0):        ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485940514816]   -- 72 cells, box x 0..90, y 0..9
 transient 81 (state(t) = state(t + 30) exactly from generation 81 on; least period 30)
 periodic configuration R0 at the reference generation tref = 90 (set simulator: evolve 90 of the initial configuration = R0, evolve 30 R0 = R0)
  R0 (whole):                  ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744]   -- 102 cells, box x 0..90, y 0..27
    gun A (gun at generation 0): ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
    gun B (sym_4 of the gun at generation 0): ofRows 55 1 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792, 12582912]   -- 36 cells, box x 55..90, y 1..9
    glider (1, 1) lane 14 tau -91: ofRows 23 9 [1, 6, 3]   -- 5 cells, box x 23..25, y 9..11
    glider (1, 1) lane 14 tau -121: ofRows 30 17 [5, 6, 2]   -- 5 cells, box x 30..32, y 17..19
    glider (1, 1) lane 14 tau -151: ofRows 38 24 [1, 6, 3]   -- 5 cells, box x 38..40, y 24..26
    glider (-1, 1) lane 75 tau 201: ofRows 50 25 [4, 3, 6]   -- 5 cells, box x 50..52, y 25..27
    glider (-1, 1) lane 75 tau 231: ofRows 58 18 [5, 3, 2]   -- 5 cells, box x 58..60, y 18..20
    glider (-1, 1) lane 75 tau 261: ofRows 65 10 [4, 3, 6]   -- 5 cells, box x 65..67, y 10..12
  envelope over a cycle: x 0..90, y 0..32  (91 x 33)
  streams (direction, lane, tau mod 30): [((-1, 1), 75, 21), ((1, 1), 14, 29)]
........................O..................................................................
......................O.O.........................................O........................
............OO......OO............OO..............................O.O......................
...........O...O....OO............OO...................OO............OO......OO............
OO........O.....O...OO.................................OO............OO....O...O...........
OO........O...O.OO....O.O............................................OO...O.....O........OO
..........O.....O.......O.........................................O.O....OO.O...O........OO
...........O...O..................................................O.......O.....O..........
............OO.............................................................O...O...........
.......................O.....................................................OO............
........................OO.........................................O.......................
.......................OO........................................OO........................
..................................................................OO.......................
...........................................................................................
...........................................................................................
...........................................................................................
...........................................................................................
..............................O.O..........................................................
...............................OO.........................O.O..............................
...............................O..........................OO...............................
...........................................................O...............................
...........................................................................................
...........................................................................................
...........................................................................................
......................................O....................................................
.......................................OO...........O......................................
......................................OO..........OO.......................................
...................................................OO......................................
```

In `R0` gun A is `gosperGun`, gun B its mirror image, the three gliders of stream A are
`evolve (30 j) gunGlider` for `j = 0, 1, 2` and those of B their mirror images: `R0` is the union
of the two free guns after 90 generations with the gliders older than 60 generations removed.

Proposed Lean statements (unverified):

```lean
def gunB : Finset Cell :=
  ofRows 55 1 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792,
    12582912]
def blockedR0 : Finset Cell := ofRows 0 0 [...]            -- "R0 (whole)" above
theorem blocked_start : conway.evolve 90 (gosperGun ∪ gunB) = blockedR0
theorem blocked_period : conway.evolve 30 blockedR0 = blockedR0
```

### 2.5 The annihilation itself

The pair of gliders that collides next in `R0` is `ofRows 38 24 [1, 6, 3]` (stream A, age 60) and
`ofRows 50 25 [4, 3, 6]` (stream B). Alone, they annihilate in 21 generations:

```text
evolve 21 (ofRows 38 24 [1, 6, 3] ∪ ofRows 50 25 [4, 3, 6]) = ∅
  generation 16: ofRows 42 28 [1, 70, 51, 96]   (10 cells, the two gliders about to touch)
  generation 18: ofRows 42 29 [13, 86, 58, 32]  (12 cells)
  generation 19: ofRows 42 29 [12, 1, 74, 32]   (7 cells)
  generation 20: ofRows 43 30 [5]               (2 cells)
  generation 21: empty
```

### 2.6 Head-on pairs

`s2_blocked.py headon`: `k = 2, 7`; `cB - cA = (u, w)`, distance `s = (u + w) / 2` between the
emission points along the lane, lane offset `q = u - w`; `0 ≤ p < 30` (exhaustive here, the
first two gliders always meet). Runs: `30 ≤ s ≤ 120`, `|q| ≤ 10`: 114 060 jobs, 675 s;
`2 ≤ s ≤ 30`: 35 940 jobs, 59 s.

**Result** (`30 ≤ s ≤ 120`): 40 430 solutions of period 30 with intact guns, for the lane
offsets `-7 ≤ q ≤ 5` (`k = 2`) and `-6 ≤ q ≤ 6` (`k = 7`); 32 580 of them are clean, the other
7 850 keep permanent debris between the guns (transients up to 538). For most lane offsets every
admissible timing class gives period 30; period 60, 90 and 120 also occur (3 135, 2 715, 1 357
solutions). Table per lane offset: `results/s2_headon_30_120_10_tables.txt`.

**Recommended head-on pair HO1** = `(2, 70, 38, 0)` (gun B = the gun rotated by 180°, both guns
at generation 0; `s = 20`, `q = 4`; 4 generations of reaction per period):

```text
Blocked stream (k, dx, dy, p) = (2, 70, 38, 0)
 initial configuration (generation 0): gun A at generation 0 of its cycle, gun B = sym_2 of the gun at generation 0, translated by (70, 38)
  gun A:                       ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
  gun B:                       ofRows 35 30 [12582912, 17825792, 34080768, 51576055808, 51573735424, 17874947, 12632067, 10240, 2048]   -- 36 cells, box x 35..70, y 30..38
  whole (generation 0):        ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 432345564227567616, 612489549322387456, 1171006271860506624, 1772139783616246841344, 1772060055829093548032, 614178502261866496, 434034517167046656, 351843720888320, 70368744177664]   -- 72 cells, box x 0..70, y 0..38
 transient 40 (state(t) = state(t + 30) exactly from generation 40 on; least period 30)
 periodic configuration R0 at the reference generation tref = 60 (set simulator: evolve 60 of the initial configuration = R0, evolve 30 R0 = R0)
  R0 (whole):                  ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 8388608, 50331648, 25165824, 0, 0, 0, 0, 0, 5368709120, 6442450944, 551903297536, 824633720832, 1374389534720, 0, 0, 0, 0, 0, 211106232532992, 105553116266496, 140737488355328, 432345564227567616, 612489549322387456, 1171006271860506624, 1772139783616246841344, 1772060055829093548032, 614178502261866496, 434034517167046656, 351843720888320, 70368744177664]   -- 92 cells, box x 0..70, y 0..38
    gun A (gun at generation 0): ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
    gun B (sym_2 of the gun at generation 0): ofRows 35 30 [12582912, 17825792, 34080768, 51576055808, 51573735424, 17874947, 12632067, 10240, 2048]   -- 36 cells, box x 35..70, y 30..38
    glider (1, 1) lane 14 tau -91: ofRows 23 9 [1, 6, 3]   -- 5 cells, box x 23..25, y 9..11
    glider (1, 1) lane 14 tau -121: ofRows 30 17 [5, 6, 2]   -- 5 cells, box x 30..32, y 17..19
    glider (-1, -1) lane -18 tau 151: ofRows 38 19 [2, 3, 5]   -- 5 cells, box x 38..40, y 19..21
    glider (-1, -1) lane -18 tau 181: ofRows 45 27 [6, 3, 4]   -- 5 cells, box x 45..47, y 27..29
  envelope over a cycle: x 0..70, y 0..38  (71 x 39)
  streams (direction, lane, tau mod 30): [((-1, -1), -18, 1), ((1, 1), 14, 29)]
........................O..............................................
......................O.O..............................................
............OO......OO............OO...................................
...........O...O....OO............OO...................................
OO........O.....O...OO.................................................
OO........O...O.OO....O.O..............................................
..........O.....O.......O..............................................
...........O...O.......................................................
............OO.........................................................
.......................O...............................................
........................OO.............................................
.......................OO..............................................
.......................................................................
.......................................................................
.......................................................................
.......................................................................
.......................................................................
..............................O.O......................................
...............................OO......................................
...............................O.......O...............................
......................................OO...............................
......................................O.O..............................
.......................................................................
.......................................................................
.......................................................................
.......................................................................
.......................................................................
..............................................OO.......................
.............................................OO........................
...............................................O.......................
.........................................................OO............
.......................................................O...O...........
..............................................O.......O.....O..........
..............................................O.O....OO.O...O........OO
.................................................OO...O.....O........OO
...................................OO............OO....O...O...........
...................................OO............OO......OO............
..............................................O.O......................
..............................................O........................
```

More compact head-on pairs exist down to 52 × 22 (`(2, 51, 21, 0)`, transient 4; the gliders
are destroyed while forming). Head-on pairs were not searched for gates: a glider that survives
stays on the lane of the opposite stream (the lane offset is at most 7), so it meets the next
glider of that stream or the opposite gun instead of leaving the assembly. A head-on pair is
therefore a termination of two streams, not a gate.

## 3. Gates on BS1

### 3.1 Search

`s3_gate.py 4 90 1 0` (135 s). *Gate time* 0 is the generation 90 of BS1, so the configuration at
gate time `t` is `evolve (t mod 30) R0`. One control glider `C` is added. Exhaustive over all
world lines of `C`: 4 directions × 146 lanes (all lanes meeting the envelope enlarged by 5 cells)
× 30 phases `tau = 0 .. 29` = 17 520 world lines (`tau + 30` is the same experiment one period
later). `C` is *free* at a time when it is at Chebyshev distance ≥ 3 from every live cell of the
cycle. It is inserted at the end of its first free interval (`C` arrives from infinity), and
also at the end of each later free interval that is not the continuation of an earlier run (`C`
is created beyond an obstacle on its lane: *not from infinity*).

A run counts as *restored* when the configuration is exactly the cycle again after removal of
gliders flying away (recorded with their world lines once more than 13 cells outside the
envelope). Runs are abandoned after 900 generations (`timeout`), when a live cell reaches the
border, or when something other than a single glider is found more than 13 cells outside the
envelope (`debris`).

| Outcome | Runs |
| --- | --- |
| `C` never comes near anything | 5 140 |
| `C` passes unchanged | 3 133 |
| **gate**: cycle restored, exactly one glider flies away, a stream glider; `C` destroyed | **3 414** |
| **kickback**: cycle restored, one stream glider and one other glider fly away | **51** |
| cycle restored, nothing flies away (`C` absorbed) | 561 |
| cycle restored, other sets of gliders (2 to 14 stream gliders released, `C` turned, …) | 1 852 |
| not restored: debris far outside / timeout | 12 245 / 9 149 |

All 3 414 gates and 51 kickbacks were re-checked from scratch with the set simulator on the
unbounded plane. The released glider is always on the world line of its stream (`A`:
`((1, 1), 14, ≡ 29 mod 30)`; `B`: `((-1, 1), 75, ≡ 21 mod 30)`), i.e. **re-timed to the clock of
the guns**, whatever the phase of `C`.

### 3.2 Families of gates

`released` = the stream whose glider escapes (A escapes when `C` deletes a glider of B, and
conversely). `repeatable` = also works with a second control glider 30 and 60 generations later
and with three in a row (section 4). Duration = generations from the last free time of `C` to
the return to the cycle (with the released glider in free flight).

| Direction of `C` | Released | From infinity | World lines | Lanes | Duration | Repeatable |
| --- | --- | --- | --- | --- | --- | --- |
| `(1, 1)` (parallel to A) | A | yes | 63 | 8 (39 .. 46) | 52 .. 140 | 59 |
| `(1, 1)` | A | no | 318 | 46 (9 .. 58) | 11 .. 191 | |
| `(1, 1)` | B | yes / no | 1 / 132 | 1 (19) / 8 (8 .. 21) | 108 / 16 .. 110 | 1 |
| `(-1, 1)` (parallel to B) | B | yes | 79 | 10 (41 .. 50) | 48 .. 132 | 74 |
| `(-1, 1)` | B | no | 299 | 43 (29 .. 72) | 12 .. 168 | |
| `(-1, 1)` | A | yes / no | 1 / 137 | 1 (70) / 11 (63 .. 79) | 108 / 16 .. 176 | 1 |
| `(-1, -1)` (against A) | A | yes | 339 | 53 (-62 .. -8) | 12 .. 158 | 279 |
| `(-1, -1)` | A | no | 87 | 39 (-58 .. -17) | 21 .. 97 | |
| `(-1, -1)` | B | yes / no | 45 / 705 | 10 (-16 .. -6) / 15 (-27 .. -7) | 8 .. 189 / 14 .. 114 | 3 |
| `(1, -1)` (against B) | B | yes | 345 | 56 (-80 .. -25) | 12 .. 118 | 292 |
| `(1, -1)` | B | no | 90 | 39 (-70 .. -29) | 17 .. 115 | |
| `(1, -1)` | A | yes / no | 88 / 685 | 12 (-83 .. -71) / 13 (-82 .. -70) | 8 .. 189 / 14 .. 114 | 3 |

The complete list (every lane with its values of `tau`) is in
`scripts/life_gates/results/s3_gate_4_90_1_0.txt`, every record in the `.json.gz` beside it.

Structure of the main family (`C` in direction `(1, 1)`, from infinity, releases A): `C` crosses
stream B between gun B and the crossing point and annihilates one glider of B; the hole in
stream B lets one glider of A through.

```text
lane 39: tau 0 7 8 9 10 18 20 21 22 23 28 29      lane 40: tau 0 7 15 22
lane 41: tau 0 1 2 10 12 13 14 15 20 21 22 29     lane 42: tau 7 14 22 29
lane 43: tau 2 4 5 6 7 12 13 14 21 22 23 24       lane 44: tau 6 14 21 29
lane 45: tau 4 5 6 13 14 15 16 24 26 27 28 29     lane 46: tau 6 13 21
```

Going 2 lanes to the right (one cell up stream B) shifts the admissible phases by `-8`. On odd
lanes 12 of the 30 phases give a gate (on lane 41 the other phases that interact are `tau = 24`,
a kickback, `4, 17, 19`, releasing two gliders, and `5`, releasing four); on even lanes 4 phases
give a gate and 11 release two to four gliders. **A control glider with an arbitrary phase is
not accepted; the phase of the input must be designed** — this is the phase constraint anticipated as risk (i) in `N-15`. The lower
limit, lane 39, is forced by the body of gun A; the upper limit grows with the distance `b` of
gun B (for the pilot blocked stream `(4, 108, 0, 5)` with `a = b = 30` the lanes are 39 .. 65,
211 world lines, and 4 956 gates in all; `results/s3_gate_4_108_0_5.json.gz`).

Consequences for the design: inputs can arrive from all four directions; outputs leave only on
the two stream lanes (down-right for A, down-left for B), so the other output directions need the
rotated and reflected copies of the assembly.

### 3.3 Recommended gates

Each statement below has the form `evolve N (R0 ∪ C) = R0 ∪ G` with `N` a multiple of 30, so the
assembly is in the same configuration `R0` before and after; it was checked with the set
simulator. `R0` is the window of section 2.4.

**G-S, straight gate** (input direction `(1, 1)`, output direction `(1, 1)`; fastest repeatable
gate of its family). The control glider is `Pattern.glider` translated by `(47, 6)`:

```text
 Gate: control glider(s) [((1, 1), 41, 22)]
  gate times: control gliders free until 239, interaction, back in the cycle (with the released gliders in free flight) from 291 on: 52 generations
  statement checked with the set simulator:  evolve 90 (R0 ∪ C) = R0 ∪ G   (start = gate time 210, end = gate time 300, both ≡ 0 mod 30)
  C1  (1, 1) lane 41 tau 22:   ofRows 47 6 [2, 4, 7]   -- 5 cells, box x 47..49, y 6..8
  G1  (1, 1) lane 14 tau 119 A: ofRows 45 32 [5, 6, 2]   -- 5 cells, box x 45..47, y 32..34
  start R0 ∪ C:                ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745471122902680576, 1227889073085352547223552, 642241842655434167562240, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744]   -- 107 cells, box x 0..90, y 0..27
  end R0 ∪ G:                  ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 175921860444160, 211106232532992, 70368744177664]   -- 107 cells, box x 0..90, y 0..34
```

```text
........................O..................................................................
......................O.O.........................................O........................
............OO......OO............OO..............................O.O......................
...........O...O....OO............OO...................OO............OO......OO............
OO........O.....O...OO.................................OO............OO....O...O...........
OO........O...O.OO....O.O............................................OO...O.....O........OO
..........O.....O.......O.......................C.................O.O....OO.O...O........OO
...........O...O.................................C................O.......O.....O..........
............OO.................................CCC.........................O...O...........
.......................O.....................................................OO............
........................OO.........................................O.......................
.......................OO........................................OO........................
..................................................................OO.......................
...........................................................................................
...........................................................................................
...........................................................................................
...........................................................................................
..............................O.O..........................................................
...............................OO.........................O.O..............................
...............................O..........................OO...............................
...........................................................O...............................
...........................................................................................
...........................................................................................
...........................................................................................
......................................O....................................................
.......................................OO...........O......................................
......................................OO..........OO.......................................
...................................................OO......................................
```

(`C` marks the control glider.) The released glider `G1 = ofRows 45 32 [5, 6, 2]` is
`evolve 90 gunGlider`: the glider of A that would have been annihilated simply continues.
Proposed Lean statement:

```lean
theorem gateS :
    conway.evolve 90 (blockedR0 ∪ ofRows 47 6 [2, 4, 7]) = blockedR0 ∪ ofRows 45 32 [5, 6, 2]
```

**G-M, mirror gate** (input `(-1, 1)`, output `(-1, 1)`: `C` deletes a glider of A, a glider of B
escapes):

```text
 Gate: control glider(s) [((-1, 1), 48, 22)]
  gate times: control gliders free until -117, interaction, back in the cycle (with the released gliders in free flight) from -69 on: 48 generations
  statement checked with the set simulator:  evolve 60 (R0 ∪ C) = R0 ∪ G   (start = gate time -120, end = gate time -60, both ≡ 0 mod 30)
  C1  (-1, 1) lane 48 tau 22:  ofRows 36 13 [1, 5, 3]   -- 5 cells, box x 36..38, y 13..15
  G1  (-1, 1) lane 75 tau 111 B: ofRows 43 33 [5, 3, 2]   -- 5 cells, box x 43..45, y 33..35
  start R0 ∪ C:                ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 68719476736, 343597383680, 206158430208, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744]   -- 107 cells, box x 0..90, y 0..27
  end R0 ∪ G:                  ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 43980465111040, 26388279066624, 17592186044416]   -- 107 cells, box x 0..90, y 0..35
```

**G-U, U-turn from below** (input `(-1, -1)`, output `(1, 1)`; `C` meets stream B just before
the crossing point; the whole reaction takes 14 generations):

```text
 Gate: control glider(s) [((-1, -1), -21, 6)]
  gate times: control gliders free until -203, interaction, back in the cycle (with the released gliders in free flight) from -189 on: 14 generations
  statement checked with the set simulator:  evolve 30 (R0 ∪ C) = R0 ∪ G   (start = gate time -210, end = gate time -180, both ≡ 0 mod 30)
  C1  (-1, -1) lane -21 tau 6: ofRows 54 33 [7, 1, 2]   -- 5 cells, box x 54..56, y 33..35
  G1  (1, 1) lane 14 tau -361 A: ofRows 45 32 [5, 6, 2]   -- 5 cells, box x 45..47, y 32..34
  start R0 ∪ C:                ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 126100789566373888, 18014398509481984, 36028797018963968]   -- 107 cells, box x 0..90, y 0..35
  end R0 ∪ G:                  ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 175921860444160, 211106232532992, 70368744177664]   -- 107 cells, box x 0..90, y 0..34
```

**G-U′** (input `(1, -1)`, output `(-1, 1)`; 12 generations):

```text
 Gate: control glider(s) [((1, -1), -69, 10)]
  gate times: control gliders free until 159, interaction, back in the cycle (with the released gliders in free flight) from 171 on: 12 generations
  statement checked with the set simulator:  evolve 30 (R0 ∪ C) = R0 ∪ G   (start = gate time 150, end = gate time 180, both ≡ 0 mod 30)
  C1  (1, -1) lane -69 tau 10: ofRows 35 34 [7, 4, 2]   -- 5 cells, box x 35..37, y 34..36
  G1  (-1, 1) lane 75 tau 351 B: ofRows 43 33 [5, 3, 2]   -- 5 cells, box x 43..45, y 33..35
  start R0 ∪ C:                ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 0, 240518168576, 137438953472, 68719476736]   -- 107 cells, box x 0..90, y 0..36
  end R0 ∪ G:                  ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 43980465111040, 26388279066624, 17592186044416]   -- 107 cells, box x 0..90, y 0..35
```

Right-angle turns at the crossing point exist too (`(-1, -1)` releasing B, `(1, -1)` releasing
A; 45 and 88 world lines from infinity) but only 3 of each are repeatable and those take 187
generations; a right-angle turn is better made with a rotated copy of G-S or G-U.

### 3.4 Kickbacks

In 51 runs (47 with `C` from infinity) the cycle is restored, one stream glider is released and a
second glider leaves: the control glider sent back. The four families from infinity:

| `C` | Lanes, phase | Released | Returned glider |
| --- | --- | --- | --- |
| `(1, 1)` | lane 41 `tau` 24; lane 43 `tau` 16; lane 45 `tau` 8 | A | `(-1, -1)`, lane `2 - lane(C)` (the same diagonal, 2 lanes off) |
| `(-1, 1)` | lanes 42, 44, 46, 48 with `tau` 0, 8, 16, 24 | B | `(1, -1)`, lane `-2 - lane(C)` |
| `(-1, -1)` | lanes -59, -57, …, -23 with `tau` 8 (and lane -57 `tau` 16) | A | `(1, 1)`, lane `-lane(C)` |
| `(1, -1)` | lanes -64, -62, …, -28 with `tau` 16 (and lane -30 `tau` 24) | B | `(-1, 1)`, lane `-lane(C)` |

The returned glider flies back along the diagonal on which `C` came (displaced by 0 or 2 lanes),
so it can open a second gate placed behind the source of `C`. **Recommended kickback K1**:

```text
 Gate: control glider(s) [((1, 1), 41, 24)]
  gate times: control gliders free until 242, interaction, back in the cycle (with the released gliders in free flight) from 291 on: 49 generations
  statement checked with the set simulator:  evolve 60 (R0 ∪ C) = R0 ∪ G   (start = gate time 240, end = gate time 300, both ≡ 0 mod 30)
  C1  (1, 1) lane 41 tau 24:   ofRows 54 13 [2, 4, 7]   -- 5 cells, box x 54..56, y 13..15
  G1  (1, 1) lane 14 tau 119 A: ofRows 45 32 [5, 6, 2]   -- 5 cells, box x 45..47, y 32..34
  G2  (-1, -1) lane -39 tau 476 X: ofRows 44 5 [7, 1, 2]   -- 5 cells, box x 44..46, y 5..7
  start R0 ∪ C:                ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 36028797018963968, 72057594037927936, 126100789566373888, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744]   -- 107 cells, box x 0..90, y 0..27
  end R0 ∪ G:                  ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101170741544698883, 1858223245745207240112014336, 1227889072557586965891072, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 175921860444160, 211106232532992, 70368744177664]   -- 112 cells, box x 0..90, y 0..34
```

Restriction: a kickback gate cannot be used at the clock rate. Tested on one kickback of each
family (`((1, 1), 41, 24)`, `((-1, 1), 48, 24)`, `((-1, -1), -23, 8)`, `((1, -1), -64, 16)`):
with a second control glider 30 or 90 generations later the run does not return to the cycle
(debris, or no return within 1500 generations), and with one 60 generations later the returned
glider annihilates the second control glider (only one stream glider is released). Control
gliders for a kickback gate must be spaced so that the returned glider has left the lane.

Other restored outcomes, possibly useful: one control glider releasing 2 to 6 gliders of one
stream (643 runs with `C` from infinity), and 8 runs in which `C` is turned by the crossing
streams without releasing anything (e.g. `C = ((-1, -1), -12, 19)` returns as `((1, 1), 12, …)`
after 7 generations); see the result file.

## 4. Repetition and gates in series

`s4_series.py 4 90 1 0` (50 s).

**Repetition.** For each of the 961 gates with `C` from infinity, a second control glider on
the same lane 30 `m` generations later (`m = 1, 2`) and three control gliders (`m = 0, 1, 2`)
were tested; success = the cycle restored with exactly 2 (3) released gliders of the same
stream, 30 `m` generations apart, re-checked with the set simulator. `m = 1`: 713 gates;
`m = 2`: 851; three in a row: 713; all three tests: **712** (by family in the table of section
3.2). Most failures are in the families in which `C` releases the stream it runs against at the
crossing point (`(1, -1)` releasing A: 85 of 88 fail; `(-1, -1)` releasing B: 42 of 45). For G-S
with three control gliders:

```text
 Gate: control glider(s) [((1, 1), 41, 22), ((1, 1), 41, 52), ((1, 1), 41, 82)]
  gate times: control gliders free until 239, interaction, back in the cycle (with the released gliders in free flight) from 351 on: 112 generations
  statement checked with the set simulator:  evolve 150 (R0 ∪ C) = R0 ∪ G   (start = gate time 210, end = gate time 360, both ≡ 0 mod 30)
  C1  (1, 1) lane 41 tau 22:   ofRows 47 6 [2, 4, 7]   -- 5 cells, box x 47..49, y 6..8
  C2  (1, 1) lane 41 tau 52:   ofRows 39 -1 [4, 5, 6]   -- 5 cells, box x 39..41, y -1..1
  C3  (1, 1) lane 41 tau 82:   ofRows 32 -9 [2, 4, 7]   -- 5 cells, box x 32..34, y -9..-7
  G1  (1, 1) lane 14 tau 119 A: ofRows 60 47 [5, 6, 2]   -- 5 cells, box x 60..62, y 47..49
  G2  (1, 1) lane 14 tau 149 A: ofRows 53 39 [1, 6, 3]   -- 5 cells, box x 53..55, y 39..41
  G3  (1, 1) lane 14 tau 179 A: ofRows 45 32 [5, 6, 2]   -- 5 cells, box x 45..47, y 32..34
  start R0 ∪ C:                ofRows 0 -9 [8589934592, 17179869184, 30064771072, 0, 0, 0, 0, 0, 2199023255552, 2748795846656, 73786979593394061312, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745471122902680576, 1227889073085352547223552, 642241842655434167562240, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744]   -- 117 cells, box x 0..90, y -9..27
  end R0 ∪ G:                  ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 175921860444160, 211106232532992, 70368744177664, 0, 0, 0, 0, 9007199254740992, 54043195528445952, 27021597764222976, 0, 0, 0, 0, 0, 5764607523034234880, 6917529027641081856, 2305843009213693952]   -- 117 cells, box x 0..90, y 0..49
```

**Series.** Gate 2 is BS1 translated by `v = (vx, vy)` (same phase of the cycle); the glider
released by gate 1 must be, in the coordinates of gate 2, a repeatable control glider of the
family "`(1, 1)` from infinity, releases A": `lane = 14 - (vx - vy)`, `tau ≡ 29 + 4 vx (mod 30)`
must be in the list of section 3.2. All `0 ≤ vx, vy ≤ 160` with the two envelopes at least 6
cells apart were enumerated: 228 translations satisfy the condition, and **all 228 work**: the
union of the two cycles has period 30 and one control glider for gate 1 (G-S) produces exactly
one released glider of gate 2 and the union of the two cycles again (re-checked with the set
simulator). The translations have `vy ≥ 40`, e.g. `(9, 40)`, `(11, 40)`, `(13, 40)`, `(15, 40)`,
`(11, 42)`, `(11, 43)`, `(13, 42)`, …; the full list is in
`results/s4_series_4_90_1_0.json.gz`. **Recommended (smallest envelope) S1: `v = (9, 40)`**:

```text
Two gates in series: blocked stream [4, 90, 1, 0] and its translate by (9, 40)
  R0 ∪ translate R0 (whole):   ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8589934592, 37778931862967899127808, 188894659341175704518656, 233020507070978384460775424, 329734572640122330174457344, 951367498291736369276102641152, 951410301821537099738096599040, 628679205131470128026746880, 328827822935179135526371328, 232113757366008805838553088, 75557863725940093222912, 56668397794448627466240, 113336795588871485128704, 0, 0, 0, 0, 2748779069440, 737869766246916947968, 442721858868540866560, 295147905179352825856, 0, 0, 0, 140737488355328, 2306687434143825920, 1729804469375336448, 3458764513820540928]   -- 204 cells, box x 0..99, y 0..67
    gun A (gun at generation 0): ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 0..35, y 0..8
    gun B (sym_4 of the gun at generation 0): ofRows 55 1 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792, 12582912]   -- 36 cells, box x 55..90, y 1..9
    gun A' (gun at generation 0): ofRows 9 40 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288]   -- 36 cells, box x 9..44, y 40..48
    gun B' (sym_4 of the gun at generation 0): ofRows 64 41 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792, 12582912]   -- 36 cells, box x 64..99, y 41..49
    glider (1, 1) lane 14 tau -91: ofRows 23 9 [1, 6, 3]   -- 5 cells, box x 23..25, y 9..11
    glider (1, 1) lane 14 tau -121: ofRows 30 17 [5, 6, 2]   -- 5 cells, box x 30..32, y 17..19
    glider (1, 1) lane -17 tau -127: ofRows 32 49 [1, 6, 3]   -- 5 cells, box x 32..34, y 49..51
    glider (1, 1) lane 14 tau -151: ofRows 38 24 [1, 6, 3]   -- 5 cells, box x 38..40, y 24..26
    glider (1, 1) lane -17 tau -157: ofRows 39 57 [5, 6, 2]   -- 5 cells, box x 39..41, y 57..59
    glider (1, 1) lane -17 tau -187: ofRows 47 64 [1, 6, 3]   -- 5 cells, box x 47..49, y 64..66
    glider (-1, 1) lane 75 tau 201: ofRows 50 25 [4, 3, 6]   -- 5 cells, box x 50..52, y 25..27
    glider (-1, 1) lane 75 tau 231: ofRows 58 18 [5, 3, 2]   -- 5 cells, box x 58..60, y 18..20
    glider (-1, 1) lane 124 tau 237: ofRows 59 65 [4, 3, 6]   -- 5 cells, box x 59..61, y 65..67
    glider (-1, 1) lane 75 tau 261: ofRows 65 10 [4, 3, 6]   -- 5 cells, box x 65..67, y 10..12
    glider (-1, 1) lane 124 tau 267: ofRows 67 58 [5, 3, 2]   -- 5 cells, box x 67..69, y 58..60
    glider (-1, 1) lane 124 tau 297: ofRows 74 50 [4, 3, 6]   -- 5 cells, box x 74..76, y 50..52
  envelope over a cycle: x 0..99, y 0..72  (100 x 73)
  streams (direction, lane, tau mod 30): [((-1, 1), 75, 21), ((-1, 1), 124, 27), ((1, 1), -17, 23), ((1, 1), 14, 29)]
 Series: control glider ((1, 1), 41, 22) for gate 1
  gate times: control gliders free until 239, interaction, back in the cycle (with the released gliders in free flight) from 441 on: 202 generations
  statement checked with the set simulator:  evolve 240 (R0 ∪ C) = R0 ∪ G   (start = gate time 210, end = gate time 450, both ≡ 0 mod 30)
  C1  (1, 1) lane 41 tau 22:   ofRows 47 6 [2, 4, 7]   -- 5 cells, box x 47..49, y 6..8
  G1  (1, 1) lane -17 tau 233 A: ofRows 54 72 [5, 6, 2]   -- 5 cells, box x 54..56, y 72..74
  start R0 ∪ C:                ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745471122902680576, 1227889073085352547223552, 642241842655434167562240, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8589934592, 37778931862967899127808, 188894659341175704518656, 233020507070978384460775424, 329734572640122330174457344, 951367498291736369276102641152, 951410301821537099738096599040, 628679205131470128026746880, 328827822935179135526371328, 232113757366008805838553088, 75557863725940093222912, 56668397794448627466240, 113336795588871485128704, 0, 0, 0, 0, 2748779069440, 737869766246916947968, 442721858868540866560, 295147905179352825856, 0, 0, 0, 140737488355328, 2306687434143825920, 1729804469375336448, 3458764513820540928]   -- 209 cells, box x 0..99, y 0..67
  end R0 ∪ G:                  ofRows 0 0 [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952, 644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920, 1227889072522402593802240, 642241841670271749074944, 453347182355485948903424, 147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8589934592, 37778931862967899127808, 188894659341175704518656, 233020507070978384460775424, 329734572640122330174457344, 951367498291736369276102641152, 951410301821537099738096599040, 628679205131470128026746880, 328827822935179135526371328, 232113757366008805838553088, 75557863725940093222912, 56668397794448627466240, 113336795588871485128704, 0, 0, 0, 0, 2748779069440, 737869766246916947968, 442721858868540866560, 295147905179352825856, 0, 0, 0, 140737488355328, 2306687434143825920, 1729804469375336448, 3458764513820540928, 0, 0, 0, 0, 90071992547409920, 108086391056891904, 36028797018963968]   -- 209 cells, box x 0..99, y 0..74
```

Picture of the start configuration of S1 (guns A, B above, A′, B′ below, control glider at
`(47, 6)`):

```text
........................O...........................................................................
......................O.O.........................................O.................................
............OO......OO............OO..............................O.O...............................
...........O...O....OO............OO...................OO............OO......OO.....................
OO........O.....O...OO.................................OO............OO....O...O....................
OO........O...O.OO....O.O............................................OO...O.....O........OO.........
..........O.....O.......O.......................O.................O.O....OO.O...O........OO.........
...........O...O.................................O................O.......O.....O...................
............OO.................................OOO.........................O...O....................
.......................O.....................................................OO.....................
........................OO.........................................O................................
.......................OO........................................OO.................................
..................................................................OO................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
..............................O.O...................................................................
...............................OO.........................O.O.......................................
...............................O..........................OO........................................
...........................................................O........................................
....................................................................................................
....................................................................................................
....................................................................................................
......................................O.............................................................
.......................................OO...........O...............................................
......................................OO..........OO................................................
...................................................OO...............................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
.................................O..................................................................
...............................O.O.........................................O........................
.....................OO......OO............OO..............................O.O......................
....................O...O....OO............OO...................OO............OO......OO............
.........OO........O.....O...OO.................................OO............OO....O...O...........
.........OO........O...O.OO....O.O............................................OO...O.....O........OO
...................O.....O.......O.........................................O.O....OO.O...O........OO
....................O...O..................................................O.......O.....O..........
.....................OO.............................................................O...O...........
................................O.....................................................OO............
.................................OO.........................................O.......................
................................OO........................................OO........................
...........................................................................OO.......................
....................................................................................................
....................................................................................................
....................................................................................................
....................................................................................................
.......................................O.O..........................................................
........................................OO.........................O.O..............................
........................................O..........................OO...............................
....................................................................O...............................
....................................................................................................
....................................................................................................
....................................................................................................
...............................................O....................................................
................................................OO...........O......................................
...............................................OO..........OO.......................................
............................................................OO......................................
```

The glider released by gate 1 (lane 14) is the control glider of gate 2 (in its coordinates:
lane 45, `tau` 5) and deletes a glider of stream B′; the output is `ofRows 54 72 [5, 6, 2]`, a
glider of stream A′ (lane -17). Since `vx` enters the phase condition through `4 vx mod 30`, for
a fixed lane (fixed `vx - vy`) the admissible translations repeat with period 15 in `vx` and are
restricted to a few residues: **the position of a second gate along the signal lane is
quantised by the clock**, which is the form the phase constraint takes in a layout.

## 5. Observations relevant to design D1

1. Period 30 suffices for blocked streams, at a right angle and head-on; no parity obstruction
   to annihilation was found. The parity of the placement only selects which timings work (4 or
   14 of them).
2. Two guns at generation 0 simultaneously (`p = 0`) work when `b = a ± 1` or `a ± 2`
   (`k = 4, 5`); the exactly mirror-symmetric placement has period 60.
3. For 8 of the 72 classes the cycle is not determined by the guns and their phases alone
   (section 2.2, two cycles); the recommended designs avoid these classes (`Δ = -4`).
4. A gate re-times its output to the guns' clock, but accepts only 12 or 4 of the 30 input
   phases per lane; chaining by translation therefore quantises positions (section 4).
5. Gates exist for all four input directions on one assembly; G-S and G-M need the input to pass
   between the guns (lanes 39 .. 46 resp. 41 .. 50), G-U and G-U′ take the input from below and
   are the fastest (12 – 14 generations).
6. The eater terminates a stream only in 2 of its 8 orientations and on one lane each.
7. The kickback exists but is a single-shot device at clock spacing.

## 6. Search ranges and run times

All runs: Python 3.12, standard library only, up to 20 processes on a 22-thread machine shared
with other jobs (wall times are therefore upper bounds).

| Script and arguments | Range | Runs | Wall time |
| --- | --- | --- | --- |
| `life.py` | self test against `Guns.lean` | | < 1 s |
| `s1_eater.py` | 8 orientations, `16 ≤ ex ≤ 72`, `ey ≥ 4`, `|ex - ey - 14| ≤ 14`, 3000 generations | 11 664 | 6 s |
| `s2_blocked.py right 15 60` | `k = 1, 3, 4, 5`; `15 ≤ a, b ≤ 60`; `-30 < p < 30` | 977 276 | 622 s |
| `s2_blocked.py centered 5 60` | `5 ≤ a, b ≤ 60`; `|p - 4 (b - a)| < 30` | 1 453 996 | 2 089 s |
| `s2_blocked.py centered 0 8`, `centered -6 3` | small distances | 34 220, 42 716 | 15 s, 11 s |
| `s2_blocked.py headon 30 120 10`, `headon 2 30 10` | `k = 2, 7`; `|q| ≤ 10`; `0 ≤ p < 30` | 114 060, 35 940 | 675 s, 59 s |
| `s3_gate.py 4 90 1 0` | 4 directions × 146 lanes × 30 phases | 17 520 world lines | 135 s |
| `s4_series.py 4 90 1 0` | 961 gates × 3 repetition tests; `0 ≤ vx, vy ≤ 160` | 228 series runs | 50 s |
| `s3_gate.py 4 108 0 5`, `s4_series.py 4 108 0 5` (pilot) | 4 × 173 × 30 | 20 760 world lines | 202 s, 134 s |

Limits of the searches (what "exhaustive" does not cover): periodicity must set in before
generation 1800 (22 + 95 runs unresolved, all at small distances or head-on); gate runs are cut
at 900 generations and abandoned when non-glider debris is 13 cells outside the envelope; one
control glider at a time (plus the repetition tests); only the blocked streams `(4, 90, 1, 0)`
and `(4, 108, 0, 5)` were searched for gates.

## 7. Files

`scripts/life_gates/`: `life.py`, `s1_eater.py`, `s2_blocked.py`, `s2_summary.py`, `gates.py`,
`s3_gate.py`, `s4_series.py`, `report_data.py`, `README.md`, `results/`. The windows in this
report were printed by `report_data.py` (which asserts each statement with the set simulator):

```bash
python3 report_data.py eater 0 25 11
python3 report_data.py blocked 4 90 1 0
python3 report_data.py gate 4 90 1 0  1 1 41 22          # G-S
python3 report_data.py gate 4 90 1 0  -1 1 48 22         # G-M
python3 report_data.py gate 4 90 1 0  -1 -1 -21 6        # G-U
python3 report_data.py gate 4 90 1 0  1 -1 -69 10        # G-U'
python3 report_data.py gate 4 90 1 0  1 1 41 24          # K1
python3 report_data.py gate 4 90 1 0  1 1 41 22  1 2     # G-S, three control gliders
python3 report_data.py series 4 90 1 0  9 40  1 1 41 22  # S1
```
