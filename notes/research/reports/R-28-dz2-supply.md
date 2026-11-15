# R-28: DZ2 completed — one control glider, no free inputs (own search)

**Status of every result in this report: numerical observation (own search), not verified in
Lean.** Produced on 2026-11-15 by the untrusted oracle `scripts/life_zero/` (new scripts
`f0_frozen.py` … `f10_sep.py`; `scripts/life_machine`, `scripts/life_gates` and their results are
imported read-only). Inputs: R-27's DZ2, REG1 (R-24), the gate catalogue of `blockedStream`, the
round-trip fan-outs of R-21 (`f2_roundtrip`), the reflector `RF0`. Nothing from pattern collections
or the literature. Conventions as in R-21 … R-27 (world frame of REG1; world lines
`(d, lane, tau)`; pieces `('asm'|'rf', sym, x, y, delay)`).

## Summary

| Goal | Result |
| --- | --- |
| supply of the unconditional glider `O` | **done**: fan-out `F_B` in series upstream of the frozen front + reflector `RF_O` + **re-timing gate `G_O`** |
| Z branch (`R_in`, `C_I`, Z output) | **done**: two fan-outs `F_Z1`, `F_Z2` + 2 reflectors (to `R_in`) + 3 reflectors (to `C_I`); no gate needed (reversal routes, §3) |
| full DECJZ from **one control glider** `C' = (SE, 41, 4444)` | **verified by exact simulation** (set simulator, unbounded plane): k = 0 → B_0 + Z; k = 1, 2, 3, 40, **100** → B_(k−1) + NZ; nothing else |
| frozen pieces (REG1, F_A, RF_a, RF_b, G_N) | **unchanged** (same placements and delays). The whole design now runs 2190 generations (= 73·30) later than in R-27, because `C` is now released by `F_B`; `RF_R` (Z part, not frozen) is re-phased: delay 24 → 28 |
| error found in R-27 | R-27's `O = (SW, 596, 7435)` crossed the register diagonal at block position ≈ 95: DZ2 of R-27 fails for k ≳ 95. Fixed: `O` now flies NE and every unconditional piece/segment is kept ≥ 12 from all block positions B_−1 … B_600 (k = 100 verified) |
| reuse spacing | not measured (the Z path is ≈ 27 000 generations) |

## 1. The complete design (world frame of REG1)

| piece | placement | role |
| --- | --- | --- |
| REG1 | 22 pieces of `register.json` | register, DEC and INC inputs (R-24) |
| `F_A` | `('asm',6,−560,−587,22)`, `('asm',6,−498,−552,17)` | frozen (R-27) |
| `RF_a`, `RF_b` | `('rf',2,−252,−796,17)`, `('rf',3,461,−47,10)` | frozen (R-27) |
| `G_N` | `('asm',3,−29,440,4)` | frozen (R-27) |
| `RF_R` | `('rf',4,50,374,28)` | R-27's restore reflector, delay 24 → 28 |
| `F_B` | `('asm',0,−1100,−1100,22)`, `('asm',0,−945,−918,17)` | fan-out 74 of `f2_roundtrip`: link = `C` (SE, −13, 2446 + 2190) |
| `RF_O` | `('rf',7,−1385,−716,21)` | SW → SE |
| `G_O` | `('asm',2,11,659,26)` | re-timing gate: control `E = (SE,−654,8584)` (record `(NW,−6,14)` of the catalogue), releases `O` |
| `F_Z1` | `('asm',5,543,9,1)`, `('asm',5,578,−53,26)` | fan-out 0, image sym 5 (control NE): link = **Z output**, 2nd output → `F_Z2` |
| `F_Z2` | `('asm',2,−718,−1370,12)`, `('asm',2,−753,−1432,7)` | fan-out 0, image sym 2 (control NW) |
| `RF_R1`, `RF_R2` | `('rf',5,−835,−1479,8)`, `('rf',7,−1319,−959,15)` | `F_Z2` output → NW → SW → SE = `R_in` |
| `RF_C1`, `RF_C2`, `RF_C3` | `('rf',2,−678,−1466,25)`, `('rf',3,−653,−1405,26)`, `('rf',7,−876,−1175,11)` | `F_Z2` output → … → SE = `C_I` |

Gliders (all produced by the pieces from `C'`): `C' = (SE, 41, 4444)` → `F_B` → `C = (SE,−13,4636)`
→ frozen front → REG1 DEC control `(SE, 41, 4612)` and detector `D = (SW, 397, 8739)` (local
`τ_D = 1825`); `F_B`'s second output → `RF_O` → `E` → `G_O` → **`O = (NE, −591, 8801)`**.
Case NZ: `G_N` releases `N1 = (SE, −391, 8779)` (**NZ output**) and `N2`, which annihilates `O`.
Case Z: `O` → `F_Z1` → **Z output `(NE, −537, 8993)`** and the branch → `F_Z2` →
`R_in = (SE, −345, 24784)` (→ `RF_R` → `R`, local time 19 049) and `C_I = (SE, 314, 22468)`
(= REG1's INC control `(SE,314,−2222)` delayed by 30·823; the INC push reaches the block at local
time ≈ 19 402, i.e. 353 generations after `R`).

Envelope of all pieces: x −1395 … 668, y −1489 … 659. Separations (`f10_sep.py`): every new piece
≥ 19 from every other piece (pairs inside one fan-out excluded; those are the verified R-21
fan-outs), ≥ 25 from the frozen pieces (`RF_R`), ≥ 60 for all other new pieces. Search filters:
new pieces ≥ 15 from everything and from all block positions B_−1 … B_600; flight segments ≥ 8
from the pieces they do not use; unconditional segments ≥ 6–20 from the frozen glider paths.

## 2. Exact simulation (`f8_full.py`, `results/f8_full_k*.txt`)

Cycle of all 41 pieces at world time −300, plus `C'`, plus `B_k`; nothing else:

```text
k =   0: evolve 27540 = cycle ∪ B_0  ∪ Z  ofRows 4562 -4025 [3, 6, 1]: checked; box x -1395..4559, y -4020..659
k =   1: evolve 11490 = cycle ∪ B_0  ∪ NZ ofRows 603 994 [1, 6, 3]: checked; box x -1395..668, y -1489..988
k =   2: evolve 11490 = cycle ∪ B_1  ∪ NZ ofRows 603 994 [1, 6, 3]: checked
k =   3: evolve 11490 = cycle ∪ B_2  ∪ NZ ofRows 603 994 [1, 6, 3]: checked
k =  40: evolve 11490 = cycle ∪ B_39 ∪ NZ ofRows 603 994 [1, 6, 3]: checked
k = 100: evolve 11490 = cycle ∪ B_99 ∪ NZ ofRows 603 994 [1, 6, 3]: checked
```

(The NZ window is `ofRows 603 994 [1, 6, 3]` at world time 11 190; the Z window
`ofRows 4562 -4025 [3, 6, 1]` at world time 27 240.) Intermediate check with `O`, `R_in`, `C_I`
still free (`f4_full.py`, `results/f4_full_k*.txt`): k = 0, 1, 2, 3, 40, 100 checked.
Both outputs fly away freely (Z: NE, its line clear for 1500 cells beyond `F_Z1`; NZ: SE, clear),
neither flies back into an emitter.

## 3. How the supply was found

* **Timing invariants.** A route of 90° reflections that never reverses arrives on a target lane
  at a time fixed by the source glider (taxicab invariant); its lane parity is also fixed. For `O`
  (exact world line) the plain route "fan-out + 2 reflectors" misses every required time (R-27
  §5). A **re-timing gate** (`f2_route.py`): `O` is the released stream glider of a copy of
  `blockedStream`; its control `E` comes from the route. Placing the gate along `O`'s line moves
  `E` linearly, so each (O, catalogue record, symmetry, fan-out family) gives at most one position;
  291 456 exact solutions for 300 `O`'s, then geometry (`f3_place.py`).
* **Unbounded register** (`f1_req.py`): `O` must not cross the register diagonal before the decision;
  only NE-flying `O`'s from the south-west qualify (in case Z it crosses the diagonal after the
  decision, when the block is at 0).
* **Z branch.** From `O`, every non-reversing route reaches `C_I`'s lane with phase
  `tau − (−2222) ∈ {2, 6, 8, …, 28} (mod 30)`, never 0, and `R_in`'s lane only with the wrong
  parity from some outputs (`f5_zbranch.py`, `f6_zbranch.py`). Routes with a **reversal**
  (e.g. NE → SE → SW → SE) are not invariant: the arrival moves by 8 generations per two lanes of
  the turning point, so every even phase is reachable and `R` can be placed before the INC push
  (`f9_zbranch.py`). Gates were not needed in the Z branch (`f7_zbranch.py`, the gate version,
  was superseded).

## 4. Files (`scripts/life_zero/`)

`f0_frozen.py` (frozen data), `f1_req.py` (admissible `O`), `f2_route.py` (re-timing gate
solutions), `f3_place.py` (geometry of the `O` supply), `f4_full.py` (check with free Z inputs),
`f5_zbranch.py` (world model, route search; shows the phase obstruction), `f6_zbranch.py`,
`f7_zbranch.py` (gate versions, superseded), `f9_zbranch.py` (Z branch found), `f8_full.py`
(complete design, exact simulation), `f10_sep.py` (separations). Results: `f1_req.json`,
`f2_route.json`, `f3_place.json`, `f4_full_k*.txt`, `f9_zbranch.json`, `f8_full_k*.txt`,
`f10_sep.txt` (all < 500 KB). Reproduce: `python3 f1_req.py; F2_ANY=1 python3 f2_route.py 300;
python3 f3_place.py; python3 f9_zbranch.py 1324; F8_KS=0 python3 f8_full.py` (k = 0: ≈ 40 min;
k ≥ 1: ≈ 15 min each).
