# R-27: DECJZ at REG1 by decrement from zero, restore through REG1's INC input (own search)

**Status of every result in this report: numerical observation (own search), not verified in
Lean.** Produced on 2026-11-15 by the untrusted oracle `scripts/life_zero/` (new scripts
`e0_push.py` … `e10_osupply.py`; `scripts/life_machine` and its results are imported read-only).
Inputs: `counter`, `pullSalvo` (`SlidingBlock.lean`), the register `REG1` of R-24
(`scripts/life_machine/results/register.json`), the gate catalogue of `scripts/life_gates`, the
round-trip fan-outs of R-21 (`results/f2_roundtrip.json.gz`), the reflector `RF0`, and the
detector / move tables of R-26. Nothing from pattern collections or the literature.
Conventions as in R-21 … R-26 (cells `(x, y)`, `y` down; world lines `(d, lane, tau)`,
`lane = dy x − dx y`, `tau = t − 4 dx x`; piece `('asm'|'rf', sym, x, y, delay)`).
"Local" = frame of `SlidingBlock.lean` (`counter k` at `(7+k, 11+k)`); REG1 world = local
translated by `(148, 240)`; with REG1's DEC control delayed by `n30 = 2400`, local time =
world time − 4132.

## Summary

| Goal | Result |
| --- | --- |
| DECJZ at REG1 with the k = 0 restore through REG1's INC | **design DZ2, partly built**: one control glider `C` drives REG1's DEC input *and* the detector (front: transposed fan-out + 2 reflectors, built); NZ gate `G_N` (built); restore reflector `RF_R` (built). **Full simulation, set simulator, unbounded plane: k = 0, 1, 2, 3, 40 exact** — with three further inputs still free gliders: `O` (unconditional) and, in case Z only, `R_in` and `C_I` |
| NZ output | `N1 = (SE, −391, 6589)`, released by `G_N`, flies SE into free space (no emitter ahead) |
| Z output | in the verified runs the Z-only glider `O = (SW, 596, 7435)` (flies SW, free); in the full design `O` feeds the Z branch (2 fan-outs) which emits `R_in`, `C_I` and the Z glider — **not built** |
| supply of `O` | **open**: the simplest route (second fan-out + 2 reflectors) misses every required timing (§5); next: a re-timing gate |
| reuse spacing | not measured (the Z path is ≈ 12 000 generations long) |

## 1. Logic (local frame; `e1_core.py --sw9`, `results/e1_core_sw9.txt`)

* Detector `D = (SW, 9, τ)` (R-26): valid for every `τ ≥ 61` (scanned 61 … 199; DZ2 uses 1825).
  k = 0: pull → `counter (−1)`, `D` → block `ofRows 7 8 [3,3]`; k ≥ 1: `counter (k−1)`, `D` flies on.
* Restore: `R = (NE, −20, τ_R)` moves `ofRows 7 8 [3,3]` → `counter (−1)` (single-glider move
  `(−1, +2)`), valid for `τ_R ≥ τ_D − 37`; then REG1's push salvo (local
  `(SE,−10,1034+P), (SE,1,983+P), (SE,8,1010+P)`) gives `counter 0` for every `P ≥ −910` after `R`
  (scanned to 1990).
* No detector product is restored by the push alone (`e0_push.py`: one or two pushes on any of the
  four detector products give debris), so `R` is needed; it must be Z-only (it is not harmless).
* NZ / Z conversion: `D` (case NZ) is the control of a copy of `blockedStream` that releases
  **two** stream gliders `N1, N2` (one lane, 30 apart; catalogue records of kind "other");
  `N1` = NZ; `N2` annihilates the unconditional glider `O`; in case Z `G_N` stays idle and `O`
  survives = the Z signal.

## 2. Pieces of DZ2 (world frame of REG1)

| piece | value | found by |
| --- | --- | --- |
| REG1 | 22 pieces of `register.json` | R-24 |
| `F_A` | `('asm', 6, −560, −587, 22)`, `('asm', 6, −498, −552, 17)` — transposed image of fan-out 0 of `f2_roundtrip` | `e5_front.py` |
| `RF_a` | `('rf', 2, −252, −796, 17)` (NE → SE, lane 530) | `e5_front.py` |
| `RF_b` | `('rf', 3, 461, −47, 10)` (SE → SW onto the detector line) | `e5_front.py` |
| `G_N` | `('asm', 3, −29, 440, 4)` | `e2_gate.py SW 397 6549` with `E2_RFR_J=50` |
| `RF_R` | `('rf', 4, 50, 374, 24)` (SE → NE, emits `R`) | `e8_rfr.py` |

Gliders: control `C = (SE, −13, 2446)`; `F_A` turns it into REG1's DEC control
`C0 = (SE, 41, 22 + 2400)` and `Y = (NE, ., .)`, which `RF_a, RF_b` turn into
`D = (SW, 397, 6549)` (local `τ_D = 1825`). Front alone (`e5_front.py --sim`, Net.react + set
simulator): `REG1 ∪ F_A ∪ RF_a ∪ RF_b ∪ C` → cycle + pull salvo (delayed 2400) + `D`, world
times 180 → 5910. `G_N` alone with `D`: releases `N1 = (SE, −391, 6589)`, `N2 = (SE, −391, 6619)`
(world times 6510 → 6690). Free inputs: `O = (SW, 596, 7435)` (unconditional);
`R_in = (SE, −345, 9930)` (Z only; `RF_R` turns it into `R = (NE, −408, 9925)`, local
`τ_R = 6385`, after the Z decision); `C_I = (SE, 314, 12778)` (Z only; REG1's INC control
`(SE, 314, −2222)` delayed by 30·500).

Clearances guaranteed by the filters: `F_A`, `RF_a`, `RF_b`, `RF_R` ≥ 15 from the REG1 envelope;
`G_N` ≥ 40 from REG1, ≥ 25 from the blocks `B_−1 … B_80`, ≥ 12 from `RF_R` and the paths of `R`
and `R_in`; `RF_R` ≥ 8 from the blocks, 5 from the line of `D`; flight segments of the front ≥ 10
from the pieces they do not use; `O`'s whole line ≥ 20 from REG1, ≥ 10 from `G_N` and the front,
≥ 15 from the blocks, ≥ 8 from the paths of `D`, `R`, `R_in`; `N1, N2` lines ≥ 25 from REG1,
≥ 10 from the blocks.

## 3. Full simulation (`e6_full.py`; `results/e6_full_k*.txt`)

Cycle of all pieces at world time 180, plus `C`, plus `B_k`; the free inputs are inserted 240
generations before they reach their target (each then ≥ 3 from everything; their lines are clear
as above):

```text
k =  1: evolve 8970  = cycle ∪ B_0  ∪ N1 (NZ) ofRows 640 1032 [5, 6, 2]: checked; box x -564..627, y -806..1018
k =  2: evolve 8970  = cycle ∪ B_1  ∪ N1 (NZ): checked
k =  3: evolve 8970  = cycle ∪ B_2  ∪ N1 (NZ): checked
k = 40: evolve 8970  = cycle ∪ B_39 ∪ N1 (NZ): checked
k =  0: evolve 17070 = cycle ∪ B_0  ∪ O (Z) ofRows -2454 3050 [4, 3, 6]: checked; box x -3147..471, y -3460..3044
        (R_in = (SE,-345,9930), C_I = (SE,314,12778); also checked with the early timing
         R_in = (SE,-345,5430), C_I = (SE,314,2938): evolve 7230, box x -687..471, y -1000..580)
```

In case Z the sequence is: pull (B_0 → B_−1), `D` → `ofRows 155 248 [3,3]` (world), `G_N` idle,
`O` passes, `R` → B_−1, INC push (≈ 3570 generations after `C_I`) → B_0. REG1's DEC→INC spacing
(≥ 60) is respected by thousands of generations.

## 4. What is still free, and the plan

1. **`O`** (unconditional, exact world line): a second round-trip fan-out `F_B` in series upstream
   of `F_A` (its link = `C`), its other output turned by two reflectors onto `O`'s lane — see §5.
2. **Z branch** (after `O` has passed `G_N`'s lane, i.e. Z only): `O` → fan-out `F_Z1` → fan-out
   `F_Z2`, three outputs routed by reflectors to `R_in` (`SE`, lane −345, any time after the
   decision, before the push), `C_I` (`SE`, lane 314, any `tau ≡ −2222 (mod 30)` late enough —
   it enters REG1 from above, `(−90, −403)`), and the Z glider (free lane). Only `C_I` has a
   mod-30 constraint; route arrival times are fixed per route type and fan-out family (taxicab
   invariant, steps 8 and 120 between families, §5), so the residue can be chosen by the family.
3. Then all inputs come from `C` alone: `C` → `F_B` → (`F_A` → REG1 + `D`) + `O`.

## 5. Obstacles met, and the supply of `O`

* **Parity / invariant of reflector routes.** A route of 90° turns from a fixed source to a fixed
  target lane has a fixed arrival time (independent of the turning points) and a fixed lane parity.
  With the plain fan-out the detector parity forced `D = SW9` (not `NE−10`); with the plain fan-out
  and route `SW → SE → SW` the detector arrived 131 generations *before* the pull
  (`e4_front.py`); route families differ by 8 / 120 generations
  (`f2_roundtrip` fan-outs 0–76). The transposed fan-out with route `NE → SE → SW` (around REG1's
  east side) gives `τ_D = 1825` (fine: any `τ ≥ 61` works).
* **`G_N` vs `R`.** `R` must come from the SW side along `x + y = 408`, 11 lanes beside `D`'s line;
  every `G_N` (and every reflector turning `D`) on `D`'s line crosses `R`'s line. Solution: `R`
  is emitted close to the register by `RF_R` (input from the NW), and `G_N` stands beyond it (188
  cells down `D`'s line).
* **Supply of `O`** (`e10_osupply.py`, `results/e10_osupply.txt`): **no exact match**. For the six
  verified `G_N` placements, every crossing point 25 … 199 cells beyond the gate and both
  directions, 38 016 world lines of `O` give a clean `N2 + O` annihilation with `N1` passing; the
  route "fan-out `F_B` (any of the 39 two-output families of `f2_roundtrip`, plain or transposed)
  whose link is `C`, then two reflectors" reaches each target lane at a small fixed set of times
  (e.g. lane `SW 597`: 5201, 5209, 5321, …, 6161, 8453, …, 9413), and none coincides with a
  required time (`O` needs e.g. `(SW, 597, 7435 … 7438)`). **Next step**: put a re-timing gate in
  `O`'s route (a copy of `blockedStream` whose release is timed by its gun — as R-24 did for its
  glider `c`), which adds a free delay, or enlarge the `G_N` set (`e2_gate.py` keeps only the first
  position per catalogue record).

## 6. Files

`e0_push.py`, `e1_core.py [--sw9]`, `e2_gate.py DIR LANE TAU` (`E2_RFR_J`), `e3_dz2.py` (first
version, superseded by `e6_full.py`), `e4_front.py` (plain fan-out; obstruction by the invariant),
`e5_front.py [--sim]`, `e6_full.py GATE O_DIR O_LANE O_TAU` (`E6_KS`, `E6_RDELAY`, `E6_MI`),
`e7_rfd.py` (reflector on `D`'s line: none clear of `R`), `e8_rfr.py`, `e9_O.py GATE RFR_J`,
`e10_osupply.py`; `dcat.Near` (fast distance). Results: `results/e1_core_sw9.txt`,
`e2_gate.json/.txt`, `e5_front.json/.txt`, `e8_rfr.json/.txt`, `e6_full_k0.txt`,
`e6_full_k0_late.txt`, `e6_full_k1.txt`, `e6_full_k2.txt`, `e6_full_k3.txt`, `e6_full_k40.txt`,
`e10_osupply.txt`.
Reproduce: `python3 e5_front.py --sim; E2_RFR_J=50 python3 e2_gate.py SW 397 6549` (after
`python3 e8_rfr.py`); `python3 e9_O.py 0 50`; `E6_KS=1 python3 e6_full.py 0 SW 596 7435`
(≈ 10 min per k); `E6_KS=0 E6_RDELAY=4500 E6_MI=500 python3 e6_full.py 0 SW 596 7435` (≈ 25 min).
