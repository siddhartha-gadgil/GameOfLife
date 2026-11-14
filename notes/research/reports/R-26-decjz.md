# R-26: DECJZ by decrement from zero — decision logic DZ1 (own search)

**Status of every result in this report: numerical observation (own search), not verified in
Lean.** Produced on 2026-11-14 by the untrusted oracle `scripts/life_zero/` (new scripts `d0_single.py`
… `d18_data.py`, `dcat.py`; they import `scripts/life_machine` read-only). Inputs: `counter`,
`pullSalvo` (`SlidingBlock.lean`), the glider and eater 1 (`Patterns.lean`), the register `REG1`
of R-24 (`scripts/life_machine/results/register.json`), and our own enumerations. Nothing from
pattern collections or the literature.

Conventions as in R-21 … R-25: cells `(x, y)`, `y` down; `ofRows x0 y0 [rows]`; world lines
`(d, lane, tau)`, `lane = dy x − dx y`, `tau = t − 4 dx x` (SE/NW: `lane = ±(x − y)`, SW: `x + y`,
NE: `−(x + y)`). "Local frame" = frame of `SlidingBlock.lean` (`counter k` = block at
`(7 + k, 11 + k)`, `pullSalvo` at time 0 = `(SE, −5, 0), (SE, 1, −29)`).

## Summary

| Goal | Result |
| --- | --- |
| full DECJZ supplied from one control glider | **not achieved** |
| decision part with free gliders (deliverable (d)) | **achieved: DZ1** — pull salvo + 6 free gliders + one eater 1; exactly one output glider (`Z` or `NZ`, distinct lanes, both fly away freely), block at `k − 1` (k ≥ 1) or back at `0` (k = 0); checked exactly for k = 0..7 and 40 (local frame) and **inside REG1** for k = 0, 1, 2, 3, 40 (set simulator, unbounded plane) |
| suppliability of DZ1 | partly: the detector and two restore gliders are **one lane, 30 apart** (one 3-release gate); `S`, `V`, `O` single gliders on free lines. **Remaining obstruction O3**: the NZ output `A` flies NE 2 lanes beside the incoming line of `S`, i.e. into `S`'s emitter (the R-25 O2 pattern); no alternative restore programme of our catalogue avoids it (§5) |
| reuse spacing | none ≤ 870 (O3 again: `A` of one use meets `S` of the next) |

## 1. Elementary facts (local frame)

* **Detectors** (`d0_single.py`): single gliders that react with `counter (−1)` but pass every
  `counter k`, `k ≥ 0`: exactly four lanes. `(SW, 9)` → block `ofRows 7 8 [3,3]`;
  `(SW, 10)` → four beehives; `(NE, −10)` → block `ofRows 4 11 [3,3]` (`X3`); `(NE, −11)` → beehives.
  (`(SW, 9)` is the translate by `(−1,−1)` of `zeroTestGlider`.) SW lanes 12 … 17 annihilate glider and block.
* **Single-glider block moves** (`d3_moves.py`): only knight moves (`(−2,−1)`, `(−1,−2)` for SE,
  `(1,−2)`, `(2,−1)` SW, `(2,1)`, `(1,2)` NW, `(−1,2)`, `(−2,1)` NE). Parity: `counter (−1)` →
  `counter 0` needs an even number of them; **the last move into `counter 0` is never made by a
  glider that passes all blocks `k ≥ 0`** (BFS finds none). No single glider restores the
  detector products (`d1_restore.py`), no detector + one passing glider gives `counter 0`
  (`d2_pair.py`, 0 hits), and no glider meeting the pull reaction at `k = 0` in progress gives
  anything but the four detectors (`d14_hitpull.py`).
* **Two-glider catalogue** (`d4_block2.py`, `results/d4_block2.txt.gz`, closed under the 8
  symmetries in `dcat.py`): block + 2 gliders → one block anywhere + ≤ 1 glider; 86 792 records.
  Units with an output glider return it along an input's line (unusable). **One-step restore
  units** whose two gliders both pass all `k ≥ 0` (`d5_harmless.py`): 4, all head-on pairs that
  annihilate each other when the block is not there:
  `SW9: (NW,−3,24)+(SE,3,−32)`, `SW9: (NE,−10,−28)+(SW,10,20)`, `NE−10: (SW,9,−6)+(NE,−11,−6)`,
  `NE−10: (NW,12,−6)+(SE,−10,−6)`. Each misses a rule **by one lane**: an NW glider must be on
  `x − y ≤ −13` or `≥ 7` to pass the salvo head-on for large `k` (`results/z0_headon.txt`;
  `−12` fails at `k = 40`, `d8_core.py`; in the mirrored generator the bound is `≥ 4`, `3` fails,
  `d10_core.py`), the other two put a glider 1 lane beside the detector.

## 2. DZ1 (local frame; `d16_logic.py`, `d18_data.py`)

Gliders (time 0 world lines; windows at time −120):

| name | world line | `ofRows` at t = −120 | role |
| --- | --- | --- | --- |
| a, b | `(SE,−5,0)`, `(SE,1,−29)` | `ofRows −30 −25 [2,4,7]`, `ofRows −23 −23 [5,6,2]` | `pullSalvo` |
| D | `(NE,−10,19)` | `ofRows −35 44 [2,6,5]` | detector |
| A | `(NE,−10,49)` | `ofRows −42 52 [3,6,1]` | restore step 1 / NZ output |
| B | `(NE,−10,79)` | `ofRows −50 59 [2,6,5]` | restore step 2 / kills O |
| S | `(SW,8,58)` | `ofRows 45 −36 [1,5,3]` | restore step 1 |
| V | `(NW,13,87)` | `ofRows 52 64 [2,3,5]` | restore step 2 |
| O | `(SE,60,73)` | `ofRows −48 −108 [1,6,3]` | Z output |
| E | eater 1 `ofRows −12 1 [3,2,10,12]` | — | eats V in case NZ |

`D, A, B` are **one lane, 30 apart**. Every pair of inputs flies freely for 1 500 generations
before t = −600 (`free_pairs`). Minimum distance between the inputs, `E` and `counter 0` at
t = −120: 5.

How it works. k = 0: the pull leaves `counter (−1)` (t = 26); `D` → block `(4,11)`; `S + A` →
block `(3,10)`; `V + B` → `counter 0`; `O` flies on = **Z**. k ≥ 1: `counter (k−1)`; `S + D`
annihilate head-on; `B + O` annihilate; `V` is eaten by `E`; `A` flies on = **NZ**.
(The restore programme `(4,11) →[S, A]→ (3,10) →[V, B]→ counter 0` is from `d12_programs.py --reg`.)

Exact results (`results/d18_data.txt`, set simulator, inputs at t = −120):

```text
k =  0: evolve 360 (inputs ∪ E ∪ counter 0)  = E ∪ counter 0  ∪ Z  ofRows 42 -18 [1, 6, 3]   box x -50..54, y -108..66
k =  1: evolve 360 (inputs ∪ E ∪ counter 1)  = E ∪ counter 0  ∪ NZ ofRows 48 -38 [3, 6, 1]   (same box)
k =  2: evolve 360 (inputs ∪ E ∪ counter 2)  = E ∪ counter 1  ∪ NZ ofRows 48 -38 [3, 6, 1]
k =  3: evolve 360 (inputs ∪ E ∪ counter 3)  = E ∪ counter 2  ∪ NZ ofRows 48 -38 [3, 6, 1]
k = 40: evolve 520 (inputs ∪ E ∪ counter 40) = E ∪ counter 39 ∪ NZ ofRows 88 -78 [3, 6, 1]   box x -50..90, y -108..66
```

So `Z = (SE, 60, 73)`, `NZ = (NE, −10, 49)` (different lanes and directions); also checked for
k = 4 … 7 (`d16_logic.py`). In case NZ the decision takes no account of `k` (all events after the
pull happen at fixed places and times near `counter (−1)`).

## 3. DZ1 at the register REG1 (`d17_reg1.py`, `results/d17_reg1.txt`)

Local → world: translate `(148, 240)`, time `+1732` (R-24: salvo `(SE,−97,1140), (SE,−91,1111)`).
World lines: `D (NE,−398,1159)`, `A (NE,−398,1189)`, `B (NE,−398,1219)`, `S (SW,396,2382)`,
`V (NW,105,2411)`, `O (SE,−32,1213)`; eater `ofRows 136 241 [3,2,10,12]` (109 from the REG1
envelope). Each DZ1 glider is inserted 160 (O: 200) generations before it reaches the register,
when it is ≥ 10 from the REG1 envelope. With REG1's cycle at T_s = −1410 and its DEC control
`C0 = (SE, 41, 22)`:

```text
k =  0: evolve 4650 (R ∪ C0 ∪ inputs ∪ E ∪ B_0)  = R ∪ E ∪ B_0  ∪ Z : checked; box x -358..509, y -399..541
k =  1: evolve 4650 (R ∪ C0 ∪ inputs ∪ E ∪ B_1)  = R ∪ E ∪ B_0  ∪ NZ: checked; box x -358..515, y -399..297
k =  2: evolve 4680 ...                           = R ∪ E ∪ B_1  ∪ NZ: checked
k =  3: evolve 4680 ...                           = R ∪ E ∪ B_2  ∪ NZ: checked
k = 40: evolve 4830 ...                           = R ∪ E ∪ B_39 ∪ NZ: checked; box x -358..560, y -399..297
```

The lines of `D, A, B, S` (whole lines) stay ≥ 90 from the REG1 envelope; `V`'s line beyond `E`
and `O`'s line upstream cross it (V is eaten first; O needs an emitter between REG1 and the
register, there is room: the eater spot is 109 from the envelope). The INC input of REG1 is not
used. **Not verified in Lean.**

## 4. Supply plan and the remaining obstruction

* `D, A, B`: one lane, 30 apart, from the free SW side: one copy of `blockedStream` releasing three
  consecutive stream gliders (the gate catalogue contains such 3-release records, e.g. control
  `(NW, −16, 24)` → A-stream gliders at taus −271, −241, −211), or one reflector fed by such a gate.
* `S` from the free NE side, `V` from the free SE side, `O` (SE) from an emitter NE of REG1; all
  triggered by fan-outs of `C0` (R-21 `F1` type, R-23 `g7_push.py` method).
* **O3 (blocks DZ1 as it stands).** In case NZ the output `A` flies NE on `x + y = 10` (local), 2
  lanes beside the line `x + y = 8` on which `S` arrives; `S`'s emitter (reflector or gate) lies
  upstream on that line, and an antiparallel glider passes an idle `RF0` only at offsets ≤ −5 (input NE) or
  ≥ +3 (input SW), never at ±2 (R-25, `results/z0_rfpass.txt`) and crosses a gun stream never — `A` would destroy it. Killing `A`
  instead needs an extra NZ-only glider (all two-glider products return to an emitter, R-25). The
  same collision kills reuse (`A` of one use meets `S` of the next): no reuse spacing ≤ 870.
* Search for programmes without O3 (`d12_programs.py`, both detectors, REG1 rules: SE gliders
  harmless and ≥ 4 lanes from the salvo, NE/SW harmless, NW in the head-on pass window, parallel
  gliders same lane or ≥ 4 apart): 68 + 57 programmes, only 2 without SE gliders (DZ1 is one);
  requiring antiparallel NE/SW gliders ≥ 5 lanes apart (`D12_ANTI=5`): 4 + 1, all with SE gliders
  on lanes that collide with REG1's salvo lanes (`a, b, e, c`; none on lanes ≤ −14 or ≥ 12).

**Best next ideas.** (1) Widen the two-glider catalogue (`d4_block2.py`: lanes ±13, delays ±60) and
add three-glider units, then re-run `d12_programs.py` with `D12_ANTI=5`; (2) make the NZ output a
gate output: `A` as the control of a 2-release gate placed *before* `S`'s line diverges (needs `S`
synthesised near the register from two gliders on free lines); (3) restore through REG1's INC
input (the coordinator's option): needs a harmless step back to `counter (−1)`, which by the move
table is `X3 + (SW, rel 4)` — a glider from the NE side on `x + y = 19`, not harmless, so it must be
Z-conditional (Z-only glider → INC control, with a fan-out for the Z output).

## 5. Files and runs (`scripts/life_zero/`)

`d0_single.py`, `d1_restore.py`, `d2_pair.py` (1 min, 8 proc.), `d3_moves.py`, `d4_block2.py`
(≈ 40 min, 8 proc.), `dcat.py`, `d5_harmless.py`, `d6_chain.py`, `d7_unitnz.py`, `d8_core.py`,
`d9_select.py`, `d10_core.py`, `d11_bfs.py`, `d12_programs.py [--reg] [--sw] [--mirror]`,
`d13_eval.py`, `d14_hitpull.py [--mirror]`, `d15_eval2.py` (found the delays of DZ1: `s1 = 68`,
`s2 = 33`), `d16_logic.py search|…` (O and eater search), `d17_reg1.py` (REG1 integration, 3 min),
`d18_data.py` (cell data). Results in `results/` (`d4_block2.txt.gz`, `d6_chain.txt.gz` gzipped).
