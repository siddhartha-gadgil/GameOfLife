# R-29: Sharing one register between several instructions — merge, dispatch, INC continue, reuse (own search)

**Status of every result in this report: numerical observation (own search), not verified in
Lean.** Produced on 2026-11-15 by the untrusted oracle `scripts/life_route/` (new scripts
`gsim.c`, `gsim.py`, `gcommon.py`, `g0_pairs.py` … `g17_sep.py`; `scripts/life_gates`,
`scripts/life_machine`, `scripts/life_zero` and their results are imported read-only). Inputs:
REG1 (R-24), DZ2 (R-27, R-28), the catalogue of one-control reactions of `blockedStream`
(`life_gates/results/s3_gate_4_90_1_0.json.gz`, `s4_series…`), the reflector `RF0`, the round-trip
fan-out 0 of `f2_roundtrip` (R-21), eater 1 of `Patterns.lean`. Nothing from pattern collections
or the literature. Conventions as in R-21 … R-28 (world frame of REG1; cells `(x, y)`, `y` down;
world lines `(d, lane, tau)`, `lane = dy x − dx y`, `tau = t − 4 dx x`; pieces
`('asm'|'rf', sym, x, y, delay)`; "gate coordinates" = `blockedStream` itself at phase 0, crossing
point `(45, 31)`, gun-A glider `A = (SE, 14, ·)`, gun-B glider `B = (SW, 75, ·)`).

## Summary

| Goal | Result |
| --- | --- |
| fast exact simulator | `gsim.c` (bit-packed, run on a grid whose border is checked never to be reached, escaping gliders peeled off only when provably gone): R-28's checks reproduced, k = 0 in 14 s instead of ≈ 40 min (`g1_check_dz2.py`; k = 0, 1, 2, 3, 40, 100, **300** checked) |
| 1. MERGE (2-way OR gate, N-way chain) | **found and verified.** OR gate = one copy of `blockedStream`: through input `T = (SE, 43, ·)` (12 residues mod 30 release `A`), side input `S = (NE, −76, ·)` (residues 1 … 13, 18, 28 release `A`). Through direction = output direction, so copies chain by translation `(35, 64)` per copy (relay: each copy re-emits). DEC chain of 3 copies ending in DZ2's `C'`: every input verified alone and with DZ2 (k = 0 → Z, k = 1 → NZ). Re-use spacing of one gate ≤ 74 generations |
| INC lane 314 | **obstruction found:** DZ2's own reflector `RF_C3` emits DZ2's restore `C_I` on lane 314 from the NW; no INC control can come down lane 314 and no gate releasing on 314 fits behind `RF_C3`. **Fixed:** OR gate `G_I` on lane 314 (through input = DZ2's `C_I`, re-emitted by `RF_C3` moved to `RF_C3'`; side input = external INC, fed by a translation chain of the same OR gates through one reflector `RF_J`). DZ2' re-verified k = 0, 1, 2, 3, 40; external INC through `G_I` verified k = 0, 1, 2, 3, 40 |
| 2. DISPATCH | **obstruction:** every two-glider collision leaving exactly one glider sends it back within 2 lanes of one input line (kickback / side step, `g0_pairs.py`). **Station found:** the token releases a gate's gun-B glider `T`; `T` meets the returning output `X` (kickback); the kicked-back glider re-enters the same gate as a catalogued control and releases its gun-A glider `S`, turned by one reflector towards the caller; unpaired `T` → eater 1; unpaired `X` passes. Stations chain by translation `(72, 72)` (delay 288) along the line. Verified on both DZ2 lines (2 stations each + end eaters), k = 0, 1, 2, 40, both callers and no caller |
| 3. INC continue | **confirmed:** the transposed fan-out 0 of `f2_roundtrip` (the image used for DZ2's `F_A`) gives REG1's INC control and a free NE continue glider; k = 0, 1, 2, 3, 40, 100 checked. The continue leaves F_I ≈ 4260 + 4k generations before the block is at `B_(k+1)` for good (at `tau(C_I) + 3269 + 4k`); INC→INC (450) and INC→DEC spacings are **independent of k** |
| 4. REUSE | measured by exact simulation for k = 0, 1, 2, 3, 40 (§4): DEC after NZ: `C''` ≥ 1860 after `C'`; DEC after Z: ≥ 19 470; INC after INC: ≥ 450; INC after NZ / Z, DEC after INC: §4. **The Z output needs ≈ 8 600 generations of delay** (after passing `F_Z1`) before the next DEC control enters, ≈ 11 400 before an external INC control passes REG1's INC input |
| full assembly | REG1 + DZ2' + `G_I` + `RF_J` + INC chain + DEC chain + 4 dispatch stations + 4 eaters (57 pieces): **every DEC-chain input × callers 0, 1 × k = 0, 1, 2, 40 and every INC-chain input × k = 0, 1, 2, 3, 40 verified** (exact simulation, nothing else left over) |

## 0. Simulator (`gsim.c`, `gsim.py`, `gcommon.py`)

Bit-packed Life on a 64-bit-word grid (bit-sliced neighbour count). A run aborts if a live cell
comes within 64 cells (words) of the grid border, so a completed run equals the evolution on the
unbounded plane. `run_peel` additionally removes a component outside a fixed box containing all
pieces and the register diagonal when it is a free glider moving away from the box with no cell
within distance 2 (it can never come back), records its world line, and checks all removed
gliders pairwise never to meet. Cross-checks: 6 random soups with gliders against the set
simulator of `life_gates` (300 generations, `python3 gsim.py`), and R-28's full DZ2 runs
(`g1_check_dz2.py`, `results/g1_check_dz2.txt`):

```text
k =   0: evolve 27540 = cycle ∪ B_0 ∪ Z: checked  (14 s)      k = 1, 2, 3, 40, 100, 300: evolve 11490 = cycle ∪ B_(k-1) ∪ NZ: checked (3 s each)
```

## 1. MERGE

### 1.1 The 2-input OR gate (`g3_orcat.py`, `g4_or.py`; `results/g3_orcat.txt`, `results/g4_or_43_-76.txt`)

The catalogue lists, for the released gun-A glider `A = (SE, 14, ·)`, controls from four
directions; the SE controls (lanes 39 … 46) have the **same direction as `A`**, which makes a
copy chainable by translation. Chosen: through input `T = (SE, 43, τ)`, side input
`S = (NE, −76, τ)` (gate coordinates, re-checked by simulation for all 30 residues):

```text
T (SE, 43, τ):  τ mod 30 ∈ {2, 4, 5, 6, 7, 12, 13, 14} -> exactly A = (SE, 14, 119 + 30m);  {21, 22, 23, 24} -> (SE, 14, 149 + 30m);  others: debris / two gliders
S (NE, -76, τ): τ mod 30 ∈ {1, …, 13} -> exactly (SE, 14, 29 + 30m);  {18, 28} -> (SE, 14, 59 + 30m)
```

Both outputs are the same stream glider class (`≡ 29 mod 30`), and the gate is back in its cycle.
Re-use (two controls, both from the far side, gap = difference of their nearest-approach times to
the crossing `(45, 31)`; all gaps 1 … 600 with a releasing residue tested): failing gaps
`T then T`: ≤ 49; `T then S`: ≤ 73; `S then T`: none; `S then S`: ≤ 42. **Re-use spacing
≤ 74 generations** for any pair of inputs.

### 1.2 Chain by translation (`g5_chain.py`, `g6_chain_sim.py`; `results/g5_chain.json`, `results/g6_chain_sim.txt`)

Copy `i + 1` = copy `i` translated by `(35, 64)` (lane shift −29 = output lane − through lane;
along-line spacing `A = 64`), its delay chosen so that the output of copy `i` arrives at residue 5
of the through window of copy `i + 1`; the output of copy `i` is consumed by copy `i + 1`, which
re-emits it (relay latency 270 generations per copy). `A = 44` (envelopes 12 apart) **fails** (`results/g6_chain_sim_A44.txt`: side inputs into copies 1, 2 give debris): the
side line of copy `i` runs into copy `i + 1`; the smallest `A` with all side lines ≥ 12 from the
other copies is 64. DEC chain (world frame), last copy releasing DZ2's `C'` class
`(SE, 41, 4444 + 30m)`:

| copy | piece | side input (NE, lane, τ); all of τ … τ + 12 (+ 30m) release |
| --- | --- | --- |
| `G_1` | `('asm', 0, −1770, −1855, 17)` | `(NE, 3549, 7098)`; through input `(SE, 128, 7102 + {−3, −1, 0, 1, 2, 7, 8, 9})` |
| `G_2` | `('asm', 0, −1735, −1791, 1)` | `(NE, 3450, 6942)` |
| `G_3` | `('asm', 0, −1700, −1727, 15)` | `(NE, 3351, 6816)` |

```text
chain alone, T into G_1 (SE, 128, 7102) -> (SE, 41, 7444): ok          S into G_1 (residues 1, 7, 13) -> (SE, 41, 7354): ok
S into G_2 (residues 1, 7, 13) -> (SE, 41, 7084): ok                   S into G_3 (residues 1, 7, 13) -> (SE, 41, 6844): ok
chain + DZ2, every input, k = 0: cycle ∪ B_0 ∪ Z (delayed with C'): ok (evolve ≈ 30 300);  k = 1: cycle ∪ B_0 ∪ NZ: ok (evolve ≈ 14 300)
```

A chain of any length: add copies by the same translation upstream; each new copy's side line
is ≥ 12 from all other copies (the side lines run to the SW, away from the chain, which proceeds
SE). Side lines of the DEC chain are ≥ 12 from every other piece over 1500 cells (copies 1 and 2
pass copy 3 at 12) and ≥ 99 from the register diagonal (§5).

### 1.3 INC input: the lane-314 obstruction and the gate `G_I` (`g10_inc_or.py`, `g11_inc_check.py`)

DZ2's last Z-branch reflector `RF_C3 = ('rf', 7, −876, −1175, 11)` sits **on REG1's INC lane 314**
and emits DZ2's restore control `C_I = (SE, 314, 22468)`. Hence (i) an INC control coming down
lane 314 from the NW hits `RF_C3`; (ii) a gate releasing on lane 314 has its gun A on lane 314
upstream of its crossing, so it cannot stand downstream of `RF_C3` while `RF_C3` still emits on
lane 314. Fix: an OR gate `G_I` on lane 314 between `RF_C3` and REG1 whose **through** input is
DZ2's `C_I`, re-emitted by `RF_C3` moved along its input line (SW, −2075, 15429) onto the gate's
through lane. Parity: `RF_C3` reaches only even lane offsets, so the through record must be one
of the SE lanes 40, 42, 44, 46; all four have a matching residue (sym 0); sym 6 gives two more.
Chosen (record lane 40, residue 15 of its window {0, 7, 15, 22}):

| piece | placement |
| --- | --- |
| `RF_C3'` | `('rf', 7, −863, −1188, 19)` (replaces `RF_C3`; emits `(SE, 340, 22364)`) |
| `G_I` | `('asm', 0, −843, −1143, 17)`; output = DZ2's `C_I` **unchanged** `(SE, 314, 22468)`; side input `(NE, 1910, 3396 … 3408)` (+ 30m) |

```text
DZ2' (RF_C3 -> RF_C3', + G_I), C' on B_k: k = 0 -> B_0 + Z (NE, -537, 8993); k = 1, 2, 3, 40 -> B_(k-1) + NZ: ok   (results/g11_inc_check_0.txt)
external INC (NE, 1910, 6390 / 6396 / 6402) through G_I's side input on B_k, k = 0, 1, 2, 3, 40 -> B_(k+1): ok
```

Since `C_I` is unchanged, DZ2' has the same timing as DZ2 (Z restore ends at 27 540).

### 1.4 INC merge chain (`g12_inc_chain.py`, `g16_trace.py`; `results/g12_inc_chain.{txt,json}`)

The INC chain is the DEC chain's construction (same OR gate, translation `(35, 64)` per copy,
relays) whose last output is turned by one reflector `RF_J` (SE → NE) onto `G_I`'s side line:

| piece | placement | inputs (the side windows are `τ … τ + 12`, + 30m) |
| --- | --- | --- |
| `RF_J` | `('rf', 4, −850, −1044, 5)` | in `(SE, 173, 3401)` → out `(NE, 1910, 3396)` = `G_I`'s side input |
| INC copy 1 | `('asm', 0, −1202, −1419, 16)` | through `(SE, 260, 4829)`; side `(NE, 2545, 4825)` |
| INC copy 2 | `('asm', 0, −1167, −1355, 0)` | side `(NE, 2446, 4669)` |
| INC copy 3 | `('asm', 0, −1132, −1291, 14)` | side `(NE, 2347, 4543)` |

Search filters: envelopes ≥ 15 from all pieces and ≥ 12 from DZ2's **flight trace** (all cells
visited by DZ2's gliders in the k = 0 and k = 1 runs, `g16_trace.py`), segments and side lines
(1500 cells) ≥ 12 from the pieces they do not use and from `B_−1 … B_600`. The first search,
without the trace filter, put copy 3 on DZ2's segment `RF_R1 → RF_R2` (Z branch): the full k = 0
run then left a permanently opened gun-B stream — the trace filter fixed it.
INC instruction with continue (§3): its fan-out stands at the instruction; its link output is sent
to one side input of this chain.


## 2. DISPATCH

### 2.1 Obstruction (`g0_pairs.py`, `results/g0_pairs.txt`)

All collisions of `X = (SE, 0, 0)` with a glider `T` from SW, NE (both parities, τ −60 … 60) or
NW (head-on, lanes −12 … 12, τ −60 … 60): the only results consisting of exactly one glider and
nothing else are the kickbacks `SW (0, ±17) → NW (2, ·) / NE (−2, ·)`, `NE (0, ±17) → NW (0, ·) /
SW (0, ·)` and the head-on side steps `NW (−4) → SE (6) / NW (2)`, `NW (6) → SE (−6) / NW (0)`.
**In every case the output flies back on, or within 2 lanes of, the line of one input glider**
(so it runs into whatever emitted that input, or upstream along the shared line). A bare
two-glider collision cannot be a station.

### 2.2 The station (`g7_station.py`, `g8_station.py`; `results/g7_station.txt`, `results/g8_station_36.{txt,json}`)

Gate coordinates. Gate `G` = `blockedStream`. Token `K = (SW, 46, 305)` (any τ with residue in
{2, 4, 5, 6, 7, 12, 13, 14}, same period) releases `T = (SW, 75, 411)` (gun B). The register output
`X = (SE, −57, 322)` meets `T` at `P = (9, 67)`, `D = 36` diagonal steps beyond the crossing; the
kickback output `Y = (NE, −77, 327)` flies back **into `G`**, where it is a catalogued repeatable
control: `G` releases `S = (SE, 14, 359)`; the reflector `RF_S = ('rf', 4, 84, 49, 9)` turns it
into the dispatched glider `S' = (NE, −117, 354)` (away from the shared line, towards the
callers). The unpaired token is eaten by `E_T` = eater 1 `ofRows −9 84 [12, 8, 7, 1]`.

```text
(a) G + RF_S + E_T + K + X -> station + S'   (b) K alone -> station   (c) X alone -> station + X: all ok
distances to the path of X: gate 25, RF_S 30, eater 16
```

Valid `D` (variant above): `D ≡ 6, 7 (mod 15)`, `D ≥ 21`; the mirror variant (X flying NW) works
for `D ≡ 5, 6, 11 (mod 15)` (`g7_station.txt`: 70 verified positions for `D ≤ 120`).
**Chaining:** station `j` = station 0 translated by `(72 j, 72 j)` and delayed by `288 j` — the same
`X` then meets every station in the same phase. Checked with two stations: token at station 1
(X passes station 0), token at station 0, both tokens without X, X without tokens: all ok;
`a = 72` is the smallest spacing (scanned from 60 in steps of 2) with all station envelopes ≥ 12 apart.

### 2.3 On DZ2's output lines (`g9_dispatch.py`; `results/g9_dispatch.{txt,json}`)

| line | station `j` gate, `RF_S`, eater | token `K_j` (for `C' = (SE, 41, 4444)`; delay with `C'`) | dispatched |
| --- | --- | --- | --- |
| NZ `(SE, −391, 8779)`, gate sym 6 (station SW of the line, away from the register) | `('asm', 6, 380, 829, 7)`, `('rf', 3, 429, 913, 16)`, `ofRows 464 820 [12, 4, 5, 3]` | `(NE, −1256, 8806)` | `(SW, 1325, 12547)` |
| | `('asm', 6, 452, 901, 25)`, `('rf', 3, 501, 985, 4)`, `ofRows 536 892 [12, 4, 5, 3]` | `(NE, −1400, 8806)` | `(SW, 1469, 13123)` |
| Z `(NE, −537, 8993)`, gate sym 5 (SE side) | `('asm', 5, 889, −293, 17)`, `('rf', 2, 973, −342, 26)`, `ofRows 880 −380 [1, 7, 8, 12]` | `(NW, −1230, 16088)` | `(SE, 1301, 9025)` |
| | `('asm', 5, 961, −365, 5)`, `('rf', 2, 1045, −414, 14)`, `ofRows 952 −452 [1, 7, 8, 12]` | `(NW, −1374, 16664)` | `(SE, 1445, 9025)` |

Line ends: eater 1 `ofRows 635 1026 [3, 5, 4, 12]` (NZ line) and `ofRows 1085 −550 [8, 14, 1, 3]`
(Z line). Each token may be delayed by `δ ∈ {−3, −1, 0, 1, 2, 7, 8, 9}`. A calling instruction emits
both tokens (NZ and Z); exactly one finds its partner, the other is eaten. Exact runs (DZ2 + 4
stations + 4 eaters, `C'` and the two tokens of caller `j`, end state compared with the cycle):

```text
k = 0,  caller 0: Z -> (SE, 1301, 9025) only: ok      caller 1: (SE, 1445, 9025) only: ok      no tokens: nothing (Z eaten at the line end): ok
k = 1, 2, 40, caller 0: NZ -> (SW, 1325, 12547) only: ok   caller 1: (SW, 1469, 13123) only: ok   no tokens: nothing: ok
```

Separations: new pieces ≥ 15 from all other pieces, ≥ 128 from `B_−1 … B_600`; token lines
(2000 cells before insertion) ≥ 80 from the other pieces and ≥ 129 from the eaters.

## 3. INC continue (`g13_inc_continue.py`, `results/g13_inc_continue.txt`)

`F_I` = the transposed round-trip fan-out 0 (the image of DZ2's `F_A`) translated by
`(t + 273, t)`: `F_I = ('asm', 6, −437, −737, 10), ('asm', 6, −375, −702, 5)`; input
`K_I = (SE, 260, 1972)` → link `(SE, 314, 1948)` (= REG1's INC control delayed by 30·139) and the
free continue `(NE, 1098, 2377)` (its path ≥ 64 from REG1 and from `B_−1 … B_600` over 1500 cells).
REG1 alone:

```text
k = 0, 1, 2, 3, 40, 100: cycle ∪ K_I ∪ B_k -> cycle ∪ B_(k+1) ∪ continue (NE, 1098, 2377): ok
the continue leaves F_I at t ≈ 955; the block region changes from t = C_I tau + 3186 + 4k, the block is at B_(k+1) for good from
t = tau(C_I) + 3269 + 4k  (k = 0: 5217; k = 1: 5221; k = 40: 5377; k = 100: 5617)
```

So the continue is ≈ 4260 + 4k generations ahead of the completed increment and cannot wait for
it. It does not need to: the next operation on the same register only needs the spacings of §4,
and **INC→INC (450) and INC→DEC are the same for k = 0, 1, 2, 3, 40** (both salvos travel the same
extra 4k along the diagonal). In the shared design `F_I` stands at the instruction and its link
feeds a side input of the INC chain (it is shown here on lane 314 of REG1 alone; with DZ2' present
lane 314 belongs to `G_I`).

## 4. REUSE (`g2_reuse.py`; `results/g2_coarse.txt`, `g2_fine*.txt`)

REG1 + DZ2 (41 pieces), two control gliders, the second delayed by `30 m`; expected end state =
cycle ∪ the right block, plus exactly the expected output gliders. External `C_I` is inserted on
lane 314 downstream of `RF_C3` (see §1.3). Entry times: `C'` passes `F_B` (≈ (−1055, −1069)) at
`tau − 4166`; `C_I` passes REG1's `U` (≈ (−121, −394)) at `tau − 402`; NZ leaves `G_N` at `C'`
entry + 8541; Z passes `F_Z1` at `C'` entry + 10 857.

| first → second | k tested | failing m | minimum (all larger m tested pass) | as entry-time gap |
| --- | --- | --- | --- | --- |
| DEC → DEC after NZ (`C'`, `C' + 30m`) | 1, 2, 3, 40 | k = 1: 1 … 61; k = 2: 1 … 46, 59 … 61; k = 3, 40: 1 … 46, 60, 61 | `m = 62`: `C'' = (SE, 41, 6304)` | 1860 after `C'` |
| DEC → DEC after Z (k = 0) | 0 | 400 … 648 (step 10 to 630, then 1) | `m = 649`: `(SE, 41, 23914)` | 19 470 |
| INC → INC (`C_I`, `C_I + 30m`) | 0, 1, 2, 3, 40 | 1 … 14 | `m = 15`: 450 | 450 (as R-24) |
| DEC (NZ) → INC (`C'`, `(SE, 314, −2222 + 30m)`) | 1, 2, 3, 40 | 157, 158, 165, 167, 168, 175 … 178 | `m = 179`: `C_I = (SE, 314, 3148)` | `C_I` entry 2468 after `C'` entry |
| DEC (Z) → INC | 0 | ≤ 837 | `m = 838`: `(SE, 314, 22918)` = DZ2's own `C_I` + 450 | 22 238 |
| INC → DEC (`C_I = (SE, 314, 3778)`, `(SE, 41, 4444 + 30m)`) | 0, 1, 2, 3, 40 | k ≥ 1: −42, −38, −36, 22 … 25, 32, 33, 35, 42, 43 (k = 0 also −60 … −36) | `m = 44`: `C' = (SE, 41, 5764)` | `C'` entry may be 1778 *before* the `C_I` entry (the pull path is longer) |

(Coarse steps 5 / 10, then step 1 near the threshold; between tested values monotonicity is
assumed, not proved; `m ≥ 44` for INC→DEC checked to m = 299 in steps of 7.)

**Delay the Z output needs.** The Z output passes `F_Z1` 10 857 generations after `C'` entered;
the next DEC control may enter `F_B` only 19 470 after `C'`, i.e. **≥ 8 613 generations after the Z
output passed `F_Z1`**; an INC control may pass REG1's INC input only ≥ 11 381 after that (it must
come ≥ 450 after DZ2's own restore `C_I`). After NZ no delay is needed: the next DEC may enter
1860 after `C'`, the next INC 2468 after, both before NZ is even emitted (8541). The spacings for
k ≥ 1 are the same for k = 1 (NZ then Z), 2, 3, 40.

## 5. The whole shared register (`g14_full.py`, `g17_sep.py`; `results/g14_full_{inc,dec0,dec1}.txt`, `results/g17_sep.txt`)

57 pieces = REG1 (22) + DZ2' (19: DZ2 with `RF_C3'`) + `G_I` + `RF_J` + INC chain (3) + DEC chain (3)
+ 2 + 2 dispatch stations (gate + `RF_S` each), and 4 eaters (2 token eaters, 2 line-end eaters).
Each control is inserted as a free glider 250 generations before its gate (its line from 3000 cells
away checked clear, §1.2, §2.3); end state compared cell by cell with the cycle of all pieces, the
eaters and the expected block; removed (escaped) gliders compared with the expected list:

```text
DEC, every input of the DEC chain (T into copy 1, S into copies 1, 2, 3; C' delayed by 6000 / 5910 / 5640 / 5400),
     with both tokens of caller 0 resp. 1 (delayed like C'):
     k = 0        -> B_0      and exactly the glider dispatched at Z station 0 / 1, e.g. (SE, 1301, 15025): ok (8 runs)
     k = 1, 2, 40 -> B_(k-1)  and exactly the glider dispatched at NZ station 0 / 1, e.g. (SW, 1325, 18547): ok (24 runs)
INC, every input of the INC chain (T into copy 1 (SE, 260, 7829), S into copies 1, 2, 3), k = 0, 1, 2, 3, 40 -> B_(k+1), nothing else: ok (20 runs)
```

Separations (`g17_sep.py`; capped at 99): new envelopes to other pieces: DEC / INC chain copies
32, `RF_J` 69, `RF_C3'` / `G_I` 46, station pieces ≥ 15 (`RF_S` of station j to the gate of station
j + 1), eaters 53; to `B_−1 … B_600`: all ≥ 99. To DZ2's flight trace: chain copies ≥ 13, stations
≥ 25, `RF_J` 61 (`G_I`, `RF_C3'` and the line-end eaters lie on DZ2's own paths by design). Input
lines: DEC side lines ≥ 12 from all pieces (copies 1, 2 pass copy 3 of the chain at 12), INC side
lines ≥ 12, through inputs ≥ 44; the side line of INC copy 3 crosses a DZ2 flight path (allowed:
one control at a time; verified in the runs above).


## 6. Obstructions found

* **O5 (two-glider dispatch).** No collision of two gliders leaves a single glider that does not
  return along (≤ 2 lanes from) one of the input lines (§2.1); a station needs a gate: the
  returning kickback glider is used as a control of the very gate that emitted the token.
* **O6 (INC lane 314).** DZ2's `RF_C3` emits on REG1's INC lane; external INC controls cannot use
  lane 314 behind it, and a gate on lane 314 cannot stand in front of it. Resolved by `G_I` +
  `RF_C3'` (§1.3); `RF_C3'` reaches only even through lanes (parity).
* **O7 (chain spacing).** In the merge chain the side line of each copy passes just beside the next
  copy: along spacing 44 (envelopes 12 apart) fails by collision, 64 is needed.
* **O8 (continue timing).** The INC continue is emitted ≈ 4260 + 4k generations before the block is
  in place; correctness relies on the k-independent spacings (INC→INC 450, INC→DEC §4) instead.
* **O9 (Z reuse).** After Z the register is busy ≈ 19 500 generations after `C'` (restore ends at
  27 540 from `Ts`); a calling instruction must delay the dispatched Z glider by ≥ 8 613 (next DEC)
  or ≥ 11 381 (next INC) before the next operation on the same register.
* **A trap met:** the first INC chain placement (filters on piece envelopes only) sat on DZ2's
  flight segment `RF_R1 → RF_R2`: in the full run the gun-B stream of a chain copy escaped. The
  search now also keeps envelopes ≥ 12 from DZ2's flight trace (`g16_trace.py`).

## 7. Files (`scripts/life_route/`)

`gsim.c`, `gsim.py` (simulator, self-test), `gcommon.py` (DZ2 / REG1 data, `run`, `run_peel`,
`run_events`, eater search), `g0_pairs.py`, `g1_check_dz2.py`, `g2_reuse.py` (+ `g2_scan.sh`,
`g2_scan2.sh`), `g3_orcat.py`, `g4_or.py`, `g5_chain.py`, `g6_chain_sim.py`, `g7_station.py`,
`g8_station.py`, `g9_dispatch.py`, `g10_inc_or.py`, `g11_inc_check.py`, `g12_inc_chain.py`,
`g13_inc_continue.py`, `g14_full.py`, `g16_trace.py`, `g17_sep.py`. Results in `results/` (all
< 500 KB). Reproduce: `python3 gsim.py; python3 g1_check_dz2.py; python3 g4_or.py 43 -76;
python3 g5_chain.py 3; python3 g6_chain_sim.py 0,1; python3 g7_station.py; python3 g8_station.py 36;
python3 g9_dispatch.py; python3 g10_inc_or.py; python3 g11_inc_check.py 0; python3 g12_inc_chain.py 3;
python3 g13_inc_continue.py; python3 g14_full.py; ./g2_scan.sh; ./g2_scan2.sh` (minutes each; the
reuse scans ≈ 1 h with 16 processes).
