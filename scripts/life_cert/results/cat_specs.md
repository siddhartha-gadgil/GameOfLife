# The 13 remaining R-31 catalogue entries: exact specifications

Produced by `scripts/life_cert/cat_stations.py`, `cat_bodies.py` and `cat_module.py` (shared code
in `cat_common.py`). Each script checks every fact by exact simulation and asserts it.
`cat_specs.py` collects the results into `cat_specs.json`: 13 catalogue entries plus their
sub-stages. These are untrusted extractor outputs, and Lean remains the check.

## Conventions (also in `cat_specs.json` → `conventions`)

* **Cells:** cells are `(x, y)` with `y` pointing down. Stations and the module use the world frame of REG1. Bodies use the unit-template frame, where the last entry copy is `('asm', 0, 0, 0, 0)`.
* **Windows:** `{x0, y0, rows}` follows the `ofRows` convention: bit `j` of `rows[i]` is the cell `(x0 + j, y0 + i)`. Big rows are stored as decimal strings.
* **World lines:** `(dir, lane, tau)` follows `life.glider_at`. `tau + s` is the same glider `s` generations later.
* **Pieces:** `('asm'|'rf', sym, x, y, delay)` is read by `net.piece_cells`. `asm` is blockedStream, i.e. the OR-gate piece, and `rf` is RF0.
* **Every fact gives:**
  * `t0` (a multiple of 30, so every piece is at phase 0 of the common clock);
  * `G`, both as `G_by_piece` (piece windows at `t0`) and as the full window when small;
  * `eater_cells`;
  * `In` (per glider: world line and cell window at `t0`) and `In_union`;
  * `Delta`;
  * `Out` (cells at `t0 + Delta`) and `Out_union`;
  * `B` (box of `G` over its 30-cycle; period 30 is checked);
  * `R` (hull of the evolution boxes over `[t0, t0 + Delta]` and `B`). `R_tight` and `B_in_R_tight` are also given; `R_tight` already contains `B` in every case except where the flag says otherwise.
* **Checked equation:** `evolve Delta (G ∪ In) = (pieces at t0 + Delta) ∪ Out`. This is checked exactly on the unbounded plane with the set simulator. Free arrival of the inputs from `t0 − 600` is also checked.
* **Distances:** `In` and `Out` are at least 3 (Chebyshev) from the *whole envelope* (all phases) of the pieces, which is stronger than the requirement.

## Dispatch stations (8 facts)

* **Pieces and frame:**
  * NZ station 0: gate `('asm', 6, 380, 829, 7)`, `RF_S` `('rf', 3, 429, 913, 16)`, eater `E_T`.
  * Z station 0: gate `('asm', 5, 889, -293, 17)`, `RF_S` `('rf', 2, 973, -342, 26)`, eater `E_T`.
  * Coordinates are in the module frame.
* **Answer gliders:** the answers come from DZ2:
  * `X_NZ = (SE, −391, 8779)`;
  * `X_Z = (NE, −537, 8993)`.
* **Timing:** everything is timed for `C' = (SE, 41, 4444)`. All times shift by `+30 m` with `C'`.
* **Tokens:** the nominal tokens are `K_NZ = (NE, −1256, 8806)` and `K_Z = (NW, −1230, 16088)`. R-31's token delays are applied:
  * NZ: `δ = 0`, token `(NE, −1256, 8806)`;
  * Z: `δ = −1`, token `(NW, −1230, 16087)`.
* **Translation between stations:** station `j` is station 0 translated by `(72 j, 72 j)` on NZ or `(72 j, −72 j)` on Z, with all times `+288 j`. This was checked for `j < 3` on the pieces, eater, token, `X` and output. `X` itself is invariant under that shift, so every station fact for station `j` is the translate of the one for station 0.

| entry | format | t0 | Δ | In | Out | B | R |
|---|---|---|---|---|---|---|---|
| capture NZ (δ=0) | reaction, 2 inputs | 10350 | 492 | K_NZ + X_NZ | `(SW, 1325, 12547)` | (380,820)–(467,919) | (380,784)–(467,919) |
| capture Z (δ=−1) | reaction, 2 inputs | 12390 | 472 | K_Z(−1) + X_Z | `(SE, 1301, 9025)` | (880,−380)–(979,−293) | (849,−380)–(979,−293) |
| pass NZ | Stage | 10380 | 397 | X_NZ | X_NZ | as capture NZ | (380,792)–(501,919) |
| pass Z | Stage | 12390 | 403 | X_Z | X_Z | as capture Z | (849,−413)–(979,−293) |
| unpaired token NZ | reaction, Out = ∅ | 10350 | 292 | K_NZ | ∅ | as above | = B |
| unpaired token Z | reaction, Out = ∅ | 12390 | 272 | K_Z(−1) | ∅ | as above | = B |
| line end NZ | reaction, Out = ∅ | 11010 | 13 | X_NZ | ∅ | eater (563,954)–(566,957) | (558,949)–(566,957) |
| line end Z | reaction, Out = ∅ | 13020 | 19 | X_Z | ∅ | eater (1013,−478)–(1016,−475) | (1007,−478)–(1016,−468) |

* **Capture outputs:** the dispatched glider for `δ = −1` is the same as the nominal `S'`; the gate re-times it.
* **Pass:** `t0` and `Δ` are chosen so that `X` enters before and leaves after the station box. `X`'s path stays at least 16 from the station envelope, so a "free flight beside an idle piece" lemma would also do.
* **Line-end eater:** for `M(D)`, the eater is the `D = 1` eater translated by `(72(D−1), ±72(D−1))`, with times `+288(D−1)`. This was checked for `D ≤ 3`.
* **What the reactions mean:**
  * A *capture* needs two inputs: the token and `X` meet at different places.
  * *Unpaired token* and *line end* have `Out = ∅`.
  * These are "reactions" with the Stage fields; they are not single-input Stages.

## Unit bodies (2 entries)

The input is the chain output `(SE, 14, 119)` of the last entry copy. It does not depend on `n` or on the copy. Final outputs:

* **dec:** L `(SE, −155, 2155)`, R `(SE, 127, 711)`, D′ `(SE, 188, 277)`.
* **inc:** R `(SE, 157, 519)`, D `(SE, 68, 95)`.

These equal the template I/O table (`p0_units.json`) shifted by −510.

* **Whole-body facts:** each body is verified as one reaction, all checked.
  * `dec` (F_B + F_A + 4 RF0): `t0 = 690`, `Δ = 2984`.
  * `inc` (F_A + RF0): `t0 = 690`, `Δ = 742`.
* **Every RF0 is an instance of a certified image stage:** it equals the image translated by the given vector and started at the given time, with exact cells for both piece and glider.
  * dec, turning L: `rf0SWSE`, translated by `(71, 241)`, starting at `t = 2416`.
  * dec, turning R: `rf0NESE`, translated by `(753, 612)`, starting at `t = 3642`.
  * dec, jog step 1: `rf0SENE`, translated by `(776, 741)`, starting at `t = 3305`.
  * dec, jog step 2: `rf0NESE`, translated by `(863, 661)`, starting at `t = 3648`.
  * inc, turning R: `rf0NESE`, translated by `(242, 71)`, starting at `t = 1406`.
* **inc is sequential:** fan-out F_A (`t0 = 690`, `Δ = 505`; outputs raw R `(NE, −290, 524)` and D) is followed by the RF0 stage. R is free of F_A at `t = 1195` and reaches its RF0 at `t = 1408`.
* **dec is not "fan-out, then reflectors":** the raw outputs leave F_B + F_A at different times. Free from / within 3 of its RF0 at:
  * L: 2153 / 2418;
  * D: 3206 / 3307;
  * R: 3383 / 3644.

  So L and D reach their RF0s before R is out.
* **dec sequential decomposition (verified):** in JSON order, `sequential_stages` lists `dec_stageA`, `dec_rf_R0` (`rf0NESE`) and `dec_rf_D1` (`rf0NESE`).
  * `dec_stageA` = F_B + F_A + RF0(L) + RF0(jog step 1). It runs from `t0 = 690` with `Δ = 2693`, ending at `t = 3383`, before the next RF0 contact at 3644. Its outputs are `(SE, −155, 2155)`, raw R `(NE, −1342, 716)` and the jog's NE leg `(NE, −1501, 282)`.
  * `dec_rf_R0` (RF0 turning R) and `dec_rf_D1` (RF0 jog step 2) are separate stages.

  The fan-out-only fact is kept for reference (it is correct, but cannot be composed in time).

## Register-module operations (3 entries, interface)

### Module contents

* **Pieces:** `M(D) = l0_module.module(D)` is R-29's circuit (REG1 + DZ2′ + G_I, 42 pieces) plus:
  * `RF_J` `('rf', 4, −850, −1044, 5)`;
  * the INC chain: 1 OR gate `('asm', 0, −1132, −1291, 14)`;
  * the DEC chain: 2D OR gates, step `(35, 64)`;
  * D stations per line, each a gate + `RF_S` + eater;
  * 2 line-end eaters.
* **Other data:** full lists for D = 1, 2, 3, the ports and the tokens are under `module_contents_D1_D2_D3`.
* **Check against Lean:** the Lean data `dz2gR*`, `dz2mk0R*`, `dz2mk1R*` and `dz2iR*` were parsed. Each set equals R-29's circuit at world time −300 (dz2g, dz2mk0, dz2mk1) or 2970 (dz2i), cell for cell.

### Time alignment (Lean ↔ world)

* **DEC runs:** Lean time 0 of `dz2gAll`, `dz2mk0Run_rest` and `dz2mk1Run_rest` is world time `−300 + 30 m` when `C' = (SE, 41, 4444 + 30 m)`.
* **Gliders in the DEC certificates:**
  * `ofRows (−1186) (−1227) [2,4,7]` is `C'` at that time.
  * NZ output: `translate (k,k) (ofRows 603 994 [1,6,3])` at `4k + 11490` is `X_NZ`, independent of k.
  * Z output: `ofRows 4562 (−4025) [3,6,1]` at 27540 is `X_Z`.
* **INC run:** `dz2iAll`'s Lean time 0 is world time 2970, and its input `ofRows (−855) (−1055) [7,4,2]` is `(NE, 1910, 6390)`.
* **Register block:** `reg1Block k` = `translate (148,240) (counter k)`.

### DEC chain

The DEC port of copy `t` (copies counted from upstream; caller `j` uses copy `2j`) maps as follows, for every R-29 window residue `r = 1..13`:

* D = 1, copy 0: `(NE, 3450, 6942 + r − 1 + 30m)` → `C' = (SE, 41, 7084 + 30m)`;
* D = 1, copy 1: `(NE, 3351, 6816 + r − 1 + 30m)` → `C' = (SE, 41, 6844 + 30m)`;
* D = 2: copies 0 and 1 are `(NE, 3648, 7224 …)` → 7594 and `(NE, 3549, 7098 …)` → 7354; copies 2 and 3 are the D = 1 ones.

Each is checked with the chain alone. It is the merge chain (side input then relays), already covered by `MergeSide` / `MergeChain`.

### The three operations

* **DEC k = 0 (Z):**
  1. `C'` → `dz2mk0Run_rest` (27540 generations; block 0 stays).
  2. `X_Z` passes Z stations `0..j−1` (pass Z).
  3. It is captured at Z station `j` (capture Z) → `S'_Z,j`.
  4. The NZ token of caller `j` is absorbed (unpaired token NZ).
* **DEC k ≥ 1 (NZ):**
  1. `C'` → `dz2gAll` (k ≥ 2) or `dz2mk1Run_rest` (k = 1), taking `4k + 11490` generations; block k → k − 1.
  2. `X_NZ` passes stations `0..j−1` and is captured at NZ station `j`.
  3. The Z token is absorbed (unpaired token Z).
* **INC:**
  1. INC port `(NE, 2347, 4543 + r − 1 + 30m)` → INC OR gate → `RF_J` → G_I control `(NE, 1910, 4566 + 30m)`.
  2. G_I releases `(SE, 314, ·)`.
  3. Block k → k + 1, with no output (`dz2iAll`, `4k + 6990` generations).

### Does not fit directly: the INC bridge

The module drives G_I at gate time `tau ≡ 7 (mod 30)`; its gate-frame control is `(NE, −76, 1177)`. `dz2iAll`'s control is at `tau ≡ 1`, i.e. `(NE, −76, 3001)`. That is a different residue of the same side window, and the module's control is not `dz2iAll`'s control plus a multiple of 30.

Both release the same glider `(SE, 314, ·)`: 4588 for the module and 6418 for dz2i, which differ by 1830 = 61·30. Each is given as a verified Stage (`GI_bridge.facts`, G = G_I, `Δ = 59`).

So using `dz2iAll` for the module needs a bridge:

* G_I's side fact at the module residue. In `side_data.py`'s numbering, R-29 residue r means gate tau ≡ r − 1, so the module's tau ≡ 7 is residue 8 (`orSide8`) and dz2i's tau ≡ 1 is residue 2. Residue 8 is not among the certified residues 5, 6, 9;
* then `dz2iAll` restarted after the release, or a dz2i certificate re-emitted from the module's control.

### Whole-module runs

The module was run exactly with gsim on the unbounded plane, with the core box peeled, from the port input with the caller's tokens (NZ `δ = 0`, Z `δ = −1`) — 7 runs:

* D = 1: DEC with k = 0, 1, 2 (caller j = 0), and INC with k = 0, 1;
* D = 2: DEC with k = 0, 1 (caller j = 1, so X passes station 0 first).

Each ends with everything back in its cycle, the right block, and exactly the dispatched glider at the nominal tau plus the `C'` shift (none for INC).

## Housekeeping

Before a path fix, an earlier run wrote copies of the results to `scripts/life_route/results/cat_{bodies,module,module_quick,stations}.json`. Those files are stale duplicates and should be deleted; the current results are only in `scripts/life_cert/results/`.
