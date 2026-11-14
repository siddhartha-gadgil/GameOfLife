# R-25: Supplying the zero test from one control glider (own search) — obstruction

**Status of every result in this report: numerical observation (own search), not verified in
Lean.** Produced on 2026-11-14 by the untrusted oracle `scripts/life_zero/` (new; it imports
`scripts/life_machine` and `scripts/life_gates` read-only). Inputs: `zeroTestInput`, `zeroEaters`,
`zOut`, `nzOut` of `ZeroTestLogic.lean`, `counter` of `SlidingBlock.lean`, the reflector `RF0`
(R-21), the gate catalogue of `blockedStream` (R-20), the fan-outs of R-21 and the method of
`g7_push.py` (R-23). Nothing from pattern collections or the literature. Conventions as in
R-21 .. R-23: cells `(x, y)`, `y` down; world lines `(d, lane, tau)`, `lane = dy x - dx y`,
`tau = t - 4 dx x` (SW: `lane = x + y`, SE: `lane = x - y`); "lane offset" is the difference of
lanes in these coordinates.

## Summary

| Goal | Result |
| --- | --- |
| zero-test supply producing exactly `zeroTestInput` | **Not achieved — obstruction (two independent ones, O1 and O2, below).** With the available components (gun gates of `blockedStream`, the reflector `RF0`, two-glider collisions) no supply exists, whatever the search effort. |
| single-glider variant z1 (`zeroTestGlider` + detector + conditional restore) | **Also obstructed** by O2 (its `NZ` is the same kickback of the detector). |
| best next idea | A new decision logic **without kickback** (detector annihilated, a passing test glider is `NZ`) and a test salvo whose gliders are either on one lane 30·m apart (one reflector or one multi-release gate serves them) or ≥ 7 lanes apart. A first candidate (salvo `(SW,12,0), (SW,12,30), (SW,8,53)`, 732 detector placements) was found and its supply equations are solvable (8 910 exact solutions of the invariant equation, insertion order allowed, 154 multi-release gate orientations), **but** its two NZ-case survivors are 4 lanes apart and no eater 1 fits between them (distance 1). See §4. |

Key numbers: `zeroTestInput` = `T2 (SW,5,20)`, `T3 (SW,10,50)`, `T1 (SW,12,24)`, `D (SE,-20,107)`;
`nzOut = (NW, 22, 55)` (re-checked: `zeroTest_decision` for `k = 0,1,2,3,40`, `results/z3_obstruction.txt`).

## 1. The four target gliders (`z3_obstruction.py`)

```text
zeroTestInput (time 0) = 4 gliders: (SW, lane 5, tau 20), (SW, lane 10, tau 50), (SW, lane 12, tau 24), (SE, lane -20, tau 107)
zOut  at time 196: (SE, lane -20, tau 107)          nzOut at time 196: (NW, lane 22, tau 55)
zeroTest_decision re-checked for k = 0, 1, 2, 3, 40 (evolve 196): ok
(O1) SW test gliders, lanes: [5, 10, 12] -> pairwise lane offsets [2, 5, 7]
(O2) detector D = (SE, -20, 107); nzOut = (NW, 22, 55); mean (x - y) of the cells: nzOut - D = -0.8;
     lane offset (SE lane of a NW glider = - its NW lane): -2
```

## 2. Obstruction O1: T1 and T3 are parallel and only 2 lanes apart

Every glider of a supply is emitted by a *stationary* emitter on its own lane (a gun gate releases
it on the gun's stream lane, `RF0` emits it at its reflection point) or created by a collision of
free gliders. `T1 = (SW,12,24)` and `T3 = (SW,10,50)` fly forever in parallel, 2 lanes apart, so the
one emitted further upstream passes the emitter of the other at lane offset 2.

* **`RF0` cannot be passed at lane offset ≤ 3.** `z0_rfpass.py` (`results/z0_rfpass.txt`): idle `RF0`
  (copies emitting `(SE,0,0)` from an input flying NE or SW), one glider on a parallel lane at
  offset −10 … 10, all 120 relative phases (30 reflector phases × 4 glider phases):
  ```text
  input NE, passing parallel (SE): passes for all phases at offsets -10..-4, for no phase at -3..+10
  input SW, passing parallel (SE): passes for all phases at offsets +4..+10, for no phase at -10..+3
  ```
  (consistent with R-21 §3.1 "far side, at least 4 lanes"; the scan of `insertion_ok` with an active
  reflector, `dt = -120..120`, offsets ±1..3, also passes nowhere.)
* **A gun gate cannot be passed** within its shadow of about 24 lanes (R-21, `r0_obstruction.py`).
* **Two-glider collisions** (`z0_pairs.py`, `results/z0_pairs.txt`, all SE + SW and SE + NW
  pairs, lanes −14 … 14, taus −60 … 60): the clean outcomes are annihilation (302 + 670), the
  kickback (13 + 13: one glider *reversed*, output 2 lanes beside the reversed input) and the
  head-on side step (30 + 30: output parallel to one input, 2 lanes beside the *other*, antiparallel,
  input). So a free collision that creates `T3` (or `T1`) needs a glider flying **NE** on a lane 2
  beside the output, i.e. on SW lane 8 or 12 (for `T3`; 10 or 14 for `T1`). That glider is
  antiparallel to `T1`/`T3` at lane offset 0 or 4 and must cross it. **Head-on window**
  (`z0_headon.py`, `results/z0_headon.txt`): two antiparallel gliders interact for every timing iff
  the lane offset is in −5 … 7 (13 lanes) and pass for every timing otherwise. Offsets 0 and 4 are in
  the window: impossible.

Hence neither of `T1`, `T3` can be emitted by `RF0`, a gun gate or a two-glider collision while the
other is in flight. (Remaining, not explored: three-glider syntheses, or a new reflector that can be
passed at 2 lanes.)

## 3. Obstruction O2: `nzOut` returns along the detector's path

`nzOut` is the kickback of `D`: it flies **NW, 2 lanes beside the line on which `D` came** (mean
`x − y` of its cells differs from `D`'s by 0.8 cells). Whatever emitted `D` sits on `D`'s line
upstream (NW) of the kick, so `nzOut` meets it:

* **`RF0` emitting `D`** (`z0_rfpass.py`, antiparallel rows): a glider flying antiparallel to the
  output passes an idle `RF0` for all phases only at offsets ≤ −5 (input NE) or ≥ +3 (input SW),
  and for **no** phase at offset −2 (`nzOut`'s offset, either reflector orientation).
* **A gun gate** releasing `D` has its stream on `D`'s lane: `nzOut` meets the stream head-on at
  offset 2, inside the head-on window.
* **A free collision creating `D`** (kickback or side step, §2) needs a NW-flying partner from the
  SE, on a lane 2 – 4 beside `D`'s; its own emitter lies on that lane further SE, where `D` (case Z)
  flies on and must first be diverted by a reflector on `D`'s lane — which the partner would have to
  pass antiparallel to the reflector's input lane at offset ≤ 4: the scan finds **no** passing lane
  within ±10 of an input lane. Circular, hence impossible.

The single-glider variant z1 (R-22 §4) uses the same kickback (`NZ = (NW, ·)` 2 lanes beside `D`):
the same obstruction applies, so the alternative of the task does not help.

**Conclusion.** `zeroTestInput` cannot be supplied with the components of R-20 .. R-23, and the
certified decision `zeroTest_decision` cannot be used inside a gun-built machine as it stands:
O2 alone excludes any design in which an output glider is a kickback of an input glider (it always
returns 2 lanes beside the input's path, i.e. to the input's emitter).

## 4. Best next idea: a decision logic without kickback (`z1_salvo.py`, `z2_detector.py`, `z4_feasible.py`, `z5_logic.py`)

Design rules read off O1 and O2: (i) parallel input gliders either on one lane, `30 m` generations
apart (one `RF0` turns several inputs 30, 60, 90 apart; and the gate catalogue contains
*multi-release gates*: one control glider releases 2 – 6 consecutive stream gliders, 30 apart —
409 verified two-glider records), or at least 4 lanes apart and outside the insertion window;
(ii) no output glider may run back towards an emitter: the detector is **annihilated** by a passing
test glider (case NZ) instead of being kicked; `NZ` is a surviving test glider flying on SW; `Z` is
`D` flying on SE.

**Salvo** (`z1_salvo.py`: three SW gliders, two on lane `a` at taus `0, 30 m`, one on lane `b`,
`|a − b| ≥ 4`; block at 0 must destroy all three and stay; blocks `k = 1..12` must let all pass).
Found (the search was stopped after it had confirmed this one; the hit agrees with the mirror image
of the R-19 salvo `5/0, 5/30, 9/61`):

```text
S = A1 (SW, 12, 0), A2 (SW, 12, 30), B (SW, 8, 53)     (frame of SlidingBlock.lean, time 0)
block at 0: all destroyed, block stays (settled);  blocks k = 1..12: all three pass unchanged
```

**Detector** (`z2_detector.py`, `results/z2_detector.txt`): `D = (SE, L, tau)` with `L ∈ −44 … −10`
placed by every clean SE + SW annihilation template so that one test glider meets it beyond the
register: **732** placements (killer A1: 273, A2: 169, B: 290) for which, with the set simulator,
`k = 0`: `S + D + counter 0 → counter 0 + D` and `k = 1..12, 40`: `→ counter k + (the two other
test gliders)`.

**Supply equations** (`z4_feasible.py`, `results/z4_feasible.txt`; mirror frame `x → −x`, where
the salvo flies SE as in R-23): `A1' (SE,−14,8)`, `A2' (SE,−14,38)`, `B' (SE,−10,61)`. With the
plan "upstream fan-out U (its SW continue glider is `D'` directly) + core `S, K`; path 1 (`RF1`,
`RF2`) gives `B'`; path 2: `G2` controls a two-glider multi-release gate whose two outputs are
turned by `RF3` into `A1', A2'`": the invariant equation `I_a(m) = I_d − J` (`I_a = tau + 4 lane`
of `B'`, depends on the leg lane `m` only; `I_d = tau − 4 lane` of `U`'s continue glider, independent
of `u`, values 615 … 1575; `J` the translation invariant of the target) has **8 910** exact
solutions `(D, core, m, U)` (27 of the 273 A1-killer detectors, e.g. `D = (SE,−29,64)`, `J = −73`,
core fan-out 0, `m = 8`, `U` type 0); insertion: `B'` first (by `RF2`), then `A1', A2'` beside it
(type R for both, outside the window), which needs gate outputs flying SW: **154** symmetric images
of two-glider multi-release gates have control SW and outputs SW.

**Why it is not yet a design.** In case NZ the two survivors (`A2, B` or `A1, B`) fly in parallel
4 lanes apart; every eater 1 that absorbs one of them is at Chebyshev distance 1 from the other's
path (`z5_logic.py`, `results/z5_logic.txt`: 170 absorbing placements for `(SW,12,30)` at
`j = 25, 30, …, 70`, maximum distance 1 to the path of `(SW,8,53)`; for `(SW,8,53)` at `j = 40`:
17 placements, all at distance 1), and
`RF0` cannot take one of two parallel gliders 4 lanes apart either (no passing lane within ±10 of
an input lane). With killer `B` the survivors `A1, A2` are on one lane (one eater would absorb both,
leaving no `NZ`). So this salvo fails rule (iii): **the glider to be eaten in case NZ must be ≥ 7
lanes from `NZ`.** A search for salvos with `|a − b| ≥ 7` (`Z1_GAP=7`, lanes 2 … 12, `m = 1..4`,
`tb = −160 … 280`) was **stopped after about 95 minutes on 8 processes without any hit**
(`results/z1_salvo_gap7.txt`; partial, the finished jobs were not logged) — consistent with R-19,
where all five three-glider unconditional tests have their lanes within 9 of each other and only
one has a same-lane pair 30 apart.

Recommended next step: (1) find an unconditional test salvo satisfying (i) and (iii) — most
promising: **four** test gliders as two same-lane pairs (each pair from one multi-release gate +
one reflector) on lanes ≥ 7 apart, so that in case NZ one pair member kills `D`, its partner is
`NZ` and the other pair goes into one eater; or three gliders with longer delays; (2) re-run
`z2_detector.py` / `z5_logic.py` on it; (3) adapt `g7_push.py` as in `z4_feasible.py` (multi-release
gate in path 2, `D'` = continue glider of `U`) and simulate; (4) certify the new decision in Lean
(replacing `zeroTest_decision`, whose kickback output is unusable by O2).

## 5. Search ranges, run times

| Script | Range | Time |
| --- | --- | --- |
| `z0_pairs.py` | SE (0,0) + SW / NW, lanes −14 … 14, taus −60 … 60 | 25 min, 1 process |
| `z0_headon.py` | SE + NW, lanes −12 … 12, taus 0 … 15 | 1 min |
| `z0_rfpass.py` | 2 reflector orientations × 4 passing families × offsets −10 … 10 × 120 phases | 5 min, 8 processes |
| `z3_obstruction.py` | decoding + `zeroTest_decision` re-check | 10 s |
| `z1_salvo.py` | lanes −4 … 12, gap ≥ 4, `m = 1..4`, `tb = −160 … 280` (stopped early; one hit confirmed separately) | — |
| `z1_salvo.py` (`Z1_GAP=7`) | lanes 2 … 12, gap ≥ 7, `m = 1..4`, `tb = −160 … 280` | stopped after ≈ 95 min (8 processes), no hit, partial |
| `z2_detector.py` | 1 salvo × 3 killers × 302 templates × lanes −44 … −10 | 15 min, 8 processes |
| `z4_feasible.py` | 273 detectors × 38 core × 39 upstream fan-outs × `m` | 20 s |

## 6. Files (`scripts/life_zero/`)

`z0_pairs.py`, `z0_headon.py`, `z0_rfpass.py`, `z3_obstruction.py` (obstructions);
`z1_salvo.py`, `z2_detector.py`, `z4_feasible.py`, `z5_logic.py` (alternative logic); results in
`scripts/life_zero/results/`. Reproduce: `cd scripts/life_zero; python3 z0_pairs.py >
results/z0_pairs.txt; python3 z0_headon.py > results/z0_headon.txt; python3 z0_rfpass.py >
results/z0_rfpass.txt; python3 z3_obstruction.py > results/z3_obstruction.txt; python3
z2_detector.py SALVO.json > results/z2_detector.txt; python3 z4_feasible.py > results/z4_feasible.txt`.
