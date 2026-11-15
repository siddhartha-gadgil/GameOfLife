# R-31: A provable program layout LP — closed formulas, separation by inequalities, timing by residues (own search)

**Status of every result in this report: numerical observation (own search), not verified in
Lean.** Produced on 2026-11-15 by the untrusted oracle `scripts/life_lp/` (new scripts `psim.c`,
`psim.py`, `lpcommon.py`, `p0_parts.py` … `p6_catalogue.py`, `runall.sh`); `scripts/life_layout`
(R-30), `scripts/life_route` (R-29), `scripts/life_machine`, `scripts/life_zero`,
`scripts/life_gates` are imported read-only. Nothing from pattern collections or the literature.
Conventions as in R-21 … R-30: world frame of REG1, cells `(x, y)` with `y` down, world lines
`(d, lane, tau)`, pieces `('asm'|'rf', sym, x, y, delay)`, rotated coordinates **`u = x − y`,
`v = x + y`** (an SE/NW glider keeps `u`, an NE/SW glider keeps `v`, 2 units of `(u, v)` per
4 generations). The Chebyshev cell distance of two cells is `(|Δu| + |Δv|) / 2`.

## Summary

| Goal | Result |
| --- | --- |
| layout rule | **`p1_layout.layout(program)` = LP**: every position is an affine formula in the indices (instruction `i`, register `r`, caller `j` / `q = D − 1 − j`, entry copy `t`, sub-band `b`, slot `s`) and the global parameters `N, R, D, P`, with parity corrections `π ∈ {0, 1}` and residue corrections `e` given by `mod 15` formulas (§2) |
| separation | 17 pair classes, each one linear inequality with a stated margin (§3, table); the route rule "every corner at (own column, own track), all columns and tracks of a region pairwise ≥ 61 apart" gives every corner ≥ 61 (in `u` or `v`) from every foreign segment; register diagonals free for every `k` (nothing foreign within 60 in `u` below `v = 344`; the module's own pieces near the diagonal end at `v ≤ 218`) |
| timing | route time `= 2 · (Manhattan length in (u, v)) − 5 · (turns)` (exact, 538 links); all pitches `≡ 0 (mod 30)`, so the arrival residue of every link class is a fixed affine function mod 30 of `(j, q)` only (§4.1, fitted on 25 random layouts, no exception); **one residue per receiving input**: `e = 2 (ρ* − r0) mod 15` hairpin steps; the decJz tokens are exact by closed formulas (`δ_NZ = 0`, `δ_Z = −1` always); minimum-delay rules for the INC continue (by formula) and the Z answer (automatic, slack ≥ 26 646) |
| certificates | finite catalogue (§4.4): OR-gate side input at 3 residues, OR-gate relay, 8 `RF0` images (one phase each), 2 unit bodies, 8 station facts, 3 register operations — 25 local certificates for every program, plus the generic lemmas (flight, chains by induction, idle bundle) |
| concurrency | at any time only the gliders of one instruction activation are in flight (+ the unpaired token, consumed ≥ 2 463 generations before anything else can come near); decJz trio: **no crossing** (nested U-routes); inc: one crossing (continue × INC link), ≥ 69 000 generations apart by the delay rule; token × answer crossings ≥ 40 000 apart (§5) |
| HALT | the halt glider flies SW on the top track `v = OUT_0` for ever; HALT cell 600 left (in `u`) of every piece: ≥ 300 cells from every piece and every other route (§6) |
| verification | static checks `p2` on the three test layouts: 0 failures; `p5` on 25 random layouts (`N ≤ 9, R ≤ 4, D ≤ 4, P ≤ 4`): residue formulas, token formulas, slacks, gaps all as claimed; **exact runs (psim) of `add` (r0 = 0 … 3), `share` (r0 = 0, 1, 2) and a random 7-instruction, 3-register program (4 inputs): all 11 runs halt correctly (§7)** |

## 1. Parts

### 1.1 Simulator `psim` (`psim.c`, `psim.py`)

Sparse tiled bit-packed Life (64 × 64 tiles; only live tiles and their neighbours are computed;
a live cell within two tiles of the tile array border aborts the run, so a completed run is exact
on the unbounded plane). Cross-checked against R-29's `gsim` (6 random soups, 1 372 generations,
cell-equal) and against R-30's machine. ≈ 0.4 ms per generation for a 21 000 × 16 000 machine
(R-30's dense `gsim`: 4.5–8 ms for 11 000 × 8 000); this is what makes the long, spacious LP layouts
simulable.

### 1.2 Unit templates `U(kind, n)` (`p0_parts.py`, `results/p0_units.txt`)

R-30's templates (entry chain of `n = 2P` OR-gate copies, last copy at the local origin, copy `t` at
`(u, v) = (29t, −99t)` with side line `v_t = 76 − 99t`; bodies: `dec` = `F_B + F_A` + two turning
`RF0`, `inc` = `F_A` + one `RF0`, `halt`/`merge` = none) with two changes:

* **input columns by formula** `c_in(t) = C0 − 61t` (`C0 = −237` dec, `−91` inc, `−67` halt/merge;
  `C0 + 76` odd), so the corner `(c_in(t), v_t)` has `u + v` odd for every `t`;
* **jog of the decJz `D` output**: `D = (SE, u = 14)` is turned NE at `v = 1501` and SE again at
  `u = 188` (two `RF0`); the jog crosses `R`'s column 429 generations before the `R` glider (inside
  the template certificate). Source columns: `dec` `L = −155` (odd), `R = 127` (odd), `D' = 188`
  (even); `inc` `D = 68`, `R = 157`; `halt`, `merge` `D = 14`.

Every template, `n = 2, 4, 6`, every copy `t`, window residues 1, 5, 13 (R-29 numbering): exactly
the listed outputs, everything back in its cycle, and the outputs **independent of the residue**
(the unit re-times; output residues `L 25, R 21, D' 7` (dec), `R 9, D 5` (inc), `D 29`).
Slab (local `u`): `[−206 − 122P, max(238, 86 + 58P)]`, rows `v ∈ [4 − 99(2P − 1), 1523]`.

### 1.3 Uniform register module `M(D)` with zones (`p1_layout.module_frame`)

Every register gets the **same** module `M(D)` (R-30's module with `D` callers, `D = max(1,
max_r #decJz on r)`; unused stations, DEC copies and the INC copy just idle), so every per-module
offset is a constant and registers differ only by translation. Module frame `(u, v)` (REG1 at the
origin); `uvbox = (−733, −3324 − 198D, 1350 + 144D, 1379 + 144D)` (exactly affine, checked).
Channel zones (all with pitch 62; `π ∈ {0,1}` makes `u + v` odd at the corner):

* left zone, `uL = −793`: DEC copy `t` at `uL − 62t − π`, INC at `uL − 124D − π`, NZ token `j` at
  `uL − 62(2D + 1 + 2j) − π`, NZ answer `j` at `uL − 62(2D + 2 + 2j) − π`; port lines DEC `t`:
  `v = −3351 − 99(2D − 1 − t)`, INC `v = −2347`, NZ token `v = 1256 + 144j`, NZ answer
  `v = 1325 + 144j` — the nearer channel is the shallower one;
* right zone, `uR = 1410 + 144D`, `q = D − 1 − j`: Z answer `j` channel `uR + 124q − π`, turn depth
  `v_d = 1500 + 180q (+π)`; Z token `j` channel `uR + 124q + 62 − π`, depth `w_d = v_d + 61`;
  station columns `u = 1301 + 144j` (Z answer, SE) and `1230 + 144j` (Z token, NW). All module
  pieces right of `u = 900` end at `v ≤ 681`, so the depths need not grow with `D`.

Extent with zones: `u ∈ [−823 − 248D, 1378 + 268D]`.

### 1.4 Pieces of a machine

Only `blockedStream` copies (OR gates, fan-outs, stations), `RF0` (8 images), eater 1 and the
register blocks. `add`: 263 pieces + 84 eater cells; `share`: 179 + 42; `rand`: 374 + 126.

## 2. The layout rule LP (all coordinates `(u, v)`)

**Program** (normal form): `inc r`, `decJz r z`, exactly one `halt` (any program is brought to this
form by replacing further `halt`s by jumps). Units `a = 0 … N − 1` (instruction `a`) and
`a = N + r` (merge unit of register `r`, collecting its `inc` callers). **Predecessors** of unit `a`
(fixed order): `start` (unit 0), then for each source instruction in increasing order its
continue / NZ answer / Z answer, or (merge units) its INC links; `P = max(1, max #predecessors)`.

**Global parameters**: `N`, `R = 1 + max r`, `D`, `P`, `NB = 2 + N + R` (sub-bands).

| object | formula |
| --- | --- |
| unit `a` (local origin) | `(A_a, V_U)`, `A_a = P_U · a`, `P_U = 540 + 180P` |
| band top | `V_T = −30 ⌈(3444 + 198D + 660 NB) / 30⌉`; `V_U = V_T − 1644` |
| module `r` | `u`-shift `U_r = U_0 + P_M · r`, `v`-shift 0; `P_M = 2400 + 540D`; `U_0 = 30 ⌈(P_U(N + R − 1) + max(238, 86 + 58P) + 943 + 248D) / 30⌉` |
| register `r` holding `k` | block `translate (148 + U_r/2, 240 − U_r/2) (counter k)`; diagonal `u = U_r − 96`, `v ≥ 404` |
| hairpin base | `H_I = 30 ⌊(−716 − 122P) / 30⌋` |
| sub-band | `b = 0` halt; `b = 1 + i` instruction `i`; `b = 1 + N + r` merge `r` |
| tracks of link `(b, s)` | `OUT = V_T + 660b + 62s + π`, `BACK = V_T + 660b + 62(9 − s) + π`, `π = 1 − (source column mod 2)` |
| hairpin of link `(b, s)` | `H = H_I + 90s − 2e − π'` (slots ≥ 1, merge); INC continue `H_I − 62 − G − 2e − π'`; KNZ `H_C − 62 − 2E_N` (§4) |
| entry copy | predecessor number `e` of unit `a` uses copy `t = 2e + β`, `β ∈ {0, 1}` with `c_in(t) ≡ source column (mod 2)` (a constant per link class) |
| DEC copy | caller `j` uses DEC copy `t = 2j` |

**Links** (slot `s` in the sub-band of the source instruction):

| link | slot | source column | destination | turns |
| --- | --- | --- | --- | --- |
| INC continue | 0 | `A_i + 68` | unit `i + 1`, `c_in(t)` | SW `OUT`, SE `H`, NE `BACK`, NW `c_in`, NE `v_t` |
| INC link | 1 | `A_i + 157` | merge unit `N + r` | same |
| KNZ (NZ token) | 0 | `A_i − 155` | NZ token `j` port | SW `OUT`, SE `H`, NE `BACK`, SE channel, NE port line |
| C | 1 | `A_i + 127` | DEC copy `2j` | same |
| KZ (Z token) | 2 | `A_i + 188` | Z token `j` | SW, SE, NE, SE channel, SW `w_d`, NW `1230 + 144j` |
| NZ answer | 3 | NZ answer channel `j` (up) | unit `i + 1` | NW channel, SW `OUT`, SE, NE, NW, NE |
| Z answer | 4 | station column `1301 + 144j` | unit `z` | NE `v_d`, NW channel, SW `OUT`, SE, NE, NW, NE |
| merge | 0 (`b = 1+N+r`) | `A_{N+r} + 14` | INC port | as KNZ |
| halt | `b = 0` | `A_i + 14` | — | SW `OUT_0`, then for ever |

Every turn is one `RF0` at the point (line of the incoming glider, line of the outgoing glider),
placed in phase with its glider (`net.reflect`). **Start**: a glider on the side line of unit 0's
start copy at window residue 4 (R-29 numbering 5). **HALT cell**: on the halt line, `u` = (least
`u` of all pieces) − 600.

## 3. Separation: pair classes and their inequalities

Ingredients of the proof plan: (1) every piece belongs to one region — unit slab `a`, module `r`
with its zones, or a route corner; (2) every route segment is a `u`-line (column) or a `v`-line
(track) with an interval; (3) **every corner lies at (own column, own track)** and all columns of a
region / all tracks of a sub-band are pairwise ≥ 61 apart, so a corner (`RF0` envelope ≤ 23 from
its corner point) is ≥ 61 in `u` or `v` from every foreign segment that passes it. Each row below
is one `omega` goal (indices bounded by `N, R, D, P`); products `P_U · a`, `P_M · r` enter only
through `A_{a+1} − A_a = P_U`, `U_{r+1} − U_r = P_M` (one monotonicity lemma `a < a' → A_a + P_U ≤
A_{a'}`, then `omega`).

| # | pair class | inequality | margin (`u` / `v` units; cells = half) |
| --- | --- | --- | --- |
| 1 | unit slab `a` / slab `a+1` | `A_a + max(238, 86+58P) + 60 ≤ A_{a+1} − 206 − 122P` | `36 + 58P` (P ≤ 2), 188 (P ≥ 3) |
| 2 | unit row / band | `V_U + 1523 ≤ V_T − 120` | 1 (+120 built in) |
| 3 | band / modules | `V_T + 660 NB ≤ −3324 − 198D − 120` | 0 … 29 (+120) |
| 4 | sub-band `b` / `b + 1` | tracks in `V_T + 660b + [0, 559]` | 41 (+60) |
| 5 | track / track (one sub-band) | `|62s − 62s'| − 1 ≥ 60` | 1 (+60) |
| 6 | units / module 0 with zones | `A_{N+R−1} + right + 120 ≤ U_0 − 823 − 248D` | 0 … 29 (+120) |
| 7 | module `r` / `r + 1` (with zones) | `U_r + 1378 + 268D + 60 ≤ U_{r+1} − 823 − 248D` | `139 + 24D` |
| 8 | regular hairpins / unit 0 | `H_I + 360 ≤ A_0 − 206 − 122P − 120` | 30 … 59 |
| 9 | hairpin / hairpin (one sub-band) | slots ≥ 1: `H_I + 90s − [0, 28]`; slot 0 and C further left (`− 62 − …`) | ≥ 62 |
| 10 | column / column (unit slab) | sources `−155, 127, 188` / `68, 157` / `14`; inputs `C0 − 61t` | ≥ 61 |
| 11 | channel / channel (zones) | pitch 62, parity −1 | ≥ 61 |
| 12 | right-zone depths | `v_d(q) = 1500 + 180q`, `w_d = v_d + 61`; Z stations end at `v ≤ 681` | ≥ 61; 819 |
| 13 | corner / foreign segment spanning it | own column, own track (#4, 5, 9, 10, 11) | ≥ 61 (checked: min 61 on 25 + 3 layouts) |
| 14 | diagonal of `r` / left zone of `r` | `U_r − 96 − 60 ≥ U_r − 793` | 637 |
| 15 | diagonal / right zone, Z-station columns | `U_r + 1230 ≥ U_r − 96 + 60` | 1 266 |
| 16 | diagonal of `r + 1` / right zone of `r` | `U_{r+1} − 96 − 60 ≥ U_r + 1378 + 268D` | `866 + 272D` |
| 17 | diagonal / band, units, hairpins | all at `v < V_T + 660 NB < −3324` | > 3 700 |

The register's own module: its pieces within 60 (in `u`) of the diagonal end at `v ≤ 218`
(`D = 1, 2, 3` checked), the blocks `B_k` sit at `v ≈ 406 + 2k`, and R-29's distances
(≥ 99 for `B_−1 … B_600`) hold; so **every** `B_k`, `k ≥ −1`, is clear of every piece and every
route for ever. Inside a unit or a module the separations are those of the template / module
certificates (R-28, R-29, §1.2).

**Nesting lemma (concurrent links).** Two links `o` (outer) and `n` (inner) of one sub-band with
source columns `s_o < s_n`, destination columns `d_o < d_n` (both destinations going down),
hairpins `H_o < H_n` and tracks `OUT_o < OUT_n < BACK_n < BACK_o` (mirror order `62s` /
`62(9 − s)`) have **no crossing**: each vertical segment of one meets the `v`-range of a horizontal
segment of the other only outside its `u`-interval (8 linear cases). The decJz trio is
`KNZ (s = 0) ⊃ C (1) ⊃ KZ (2)` with sources `L < R < D'` and destinations NZ token (left zone, far)
`<` DEC copy (left zone, near) `<` Z token (right zone): nested. This is why `D` is jogged right of
`R` (`KZ` needs an even source column: its NW leg is on `u = 1230 + 144j + U_r`, even).

## 4. Timing by formula

### 4.1 Route time and residues

* **Route law** (exact, checked on all 538 links of 25 random layouts): the time between the first
  and the last corner is `2 · Σ |Δ|` (Manhattan length in `(u, v)`) `− 5 ·` (number of turns
  after the first). For a down-going destination (`OUT`, `BACK` and the channel cancel) the length
  is `v_port − v_src + s + u_gate − 2H`; for an up-going one `2 BACK − v_src − v_t + s + u_gate −
  2H`.
* **Invariance**: `P_U`, `P_M`, `660`, `H_I`, `V_T`, `U_0` are `≡ 0 (mod 30)`, so the arrival residue
  of a link does not depend on `i, r, b, N, R, P`; it depends only on the link class and, through the
  module geometry, on `j, q` (`q = D − 1 − j`). Fitted on 25 random layouts (488 window links),
  no exception (`results/p5_formulas.txt`), residue `r0` at `e = 0` relative to the window base
  `τ_t` of the receiving copy (R-29 numbering = `r0 + 1`):

  | class | receiving input | `r0 (mod 30)` |
  | --- | --- | --- |
  | INC continue | entry copy | 7 |
  | INC link | entry copy of the merge unit | 21 |
  | merge | INC chain copy | 5 |
  | NZ answer | entry copy | `14 + 6j` |
  | Z answer | entry copy | `17 + 6j + 22q` |
  | C | DEC chain copy `2j` | `4 + 18q` |

* **Window rule (one residue per input)**: a hairpin moved by `−2` adds 8 generations, so with
  `ρ* = 4` (`r0` even) or `5` (`r0` odd), `e = 2 (ρ* − r0) mod 15` gives `r0 + 8e ≡ ρ* (mod 30)`
  (`8 · 2 = 16 ≡ 1` on the half residues mod 15). Every window input therefore arrives at
  residue 4 or 5 of its window (R-29 numbering 5, 6), the C input at `4 + 2σ ∈ {4, 8}` (§4.2).

### 4.2 The decJz tokens (exact, closed formulas)

The tokens must arrive at R-29's token world lines shifted with `C'` plus `δ ∈ {−3, −1, 0, 1, 2, 7,
8, 9}`. With `C` at a fixed residue, `C' = (arrival of C) + const`, and all of `i, r, D` cancel in
the token-minus-target differences (both tokens and `C` start at unit `i` and end at module `r`):

* `e_C = 9q mod 15` (= `2 (4 − r0_C) mod 15`);
* for `e_KNZ = e_KZ = 0`: `dN0 = −3936 − 228q`, `dZ0 = 367 + 1564q − 8 e_C` (token minus target);
* **σ = 2 (q mod 2)**: `C` is moved by `4σ` more hairpin steps (+32σ generations: one slot later
  per `σ`, residue `+2σ`); this makes `dN ≡ 0` and `dZ ≡ 7 (mod 8)`;
* **x = max(0, ⌈(368 + 1564q − 8e_C − 30σ) / 120⌉)**: `C` moved by `15x` more steps (+120x =
  4x whole periods, residue kept) so that the Z token is not late;
* `C` hairpin: `H_C = H_I + 90 − 2(e_C + 4σ + 15x)`; KNZ hairpin `H_C − 62 − 2E_N`,
  **E_N = (3936 + 228q − 2σ) / 8** (`δ_NZ = 0`); KZ hairpin `H_I + 180 − 2e_KZ`,
  **e_KZ = (−1 − dZ0 + 30σ + 120x) / 8 ∈ [0, 14]** (`δ_Z = −1`).

KZ gets its large lag from its route below the module (`w_d`), KNZ from its far-left hairpin (it
is the outer link). Matched on 74 decJz instructions of 25 random layouts (`D ≤ 4`) and on the
three test layouts; `δ` is **always** `(0, −1)`.

### 4.3 Minimum delays

* **INC continue**: `G = 30 ⌈max(0, T_INC + 500 − T⁰_corner) / 120⌉`, where `T_INC` is the (formula)
  time of the INC control at the INC chain copy and `T⁰_corner` the continue's time at its up-turn
  corner `(c_in, BACK)` for `G = 0`; `G ≡ 0 (mod 30)` keeps the residue. Then the continue reaches
  its corner ≥ `T_INC + 500` (slack 6 … 119 in the sweep). This gives R-29's INC → INC ≥ 450 and
  INC → DEC, and the time separation of §5.
* **Z answer**: arrival at the next gate ≥ (end of DZ2's Z restore) + 300 holds without extra delay:
  slack ≥ 26 646 on all 74 + 7 decJz (the Z answer must reach the hairpin zone left of all units
  and come back).
* **After NZ**: R-29's DEC → DEC 1 860, DEC → INC 2 468 after `C'` are implied: the NZ answer is
  emitted 8 541 after `C'` and flies ≥ 2 (U_0 − H_I) more.

### 4.4 Catalogue of local certificates (`p6_catalogue.py`)

| piece / process | input | residues / phases | count |
| --- | --- | --- | --- |
| OR gate (entry copies, DEC chain, INC chain copy) | side input `(NE, −76)` | R-29 residues 5, 6, 9 | 3 |
| OR gate | through input (relay `(35, 64)`, `orGate_relay`) | 1 | 1 |
| `RF0` | 8 images (SW→NW, NW→NE, NE→SE, SE→SW, SE→NE, NW→SW, NE→NW, SW→SE) | one relative phase each | 8 |
| unit bodies | chain output | `dec` (F_B + F_A + 4 `RF0`), `inc` (F_A + `RF0`) | 2 |
| dispatch station (by translation `(72, ±72)`) | capture NZ (`δ = 0`), capture Z (`δ = −1`), pass NZ, pass Z, unpaired token NZ / Z, line end NZ / Z | | 8 |
| register module | DEC `k = 0` (Z), DEC `k ≥ 1` (NZ) from `C'`; INC through `G_I` (`dz2gAll`, `reg1_increment`, R-29) | | 3 |

25 local certificates, independent of the program; everything else is generic (free flights,
idle bundle, chains of any length by `chain_reaction`, translation and time shift). Unit templates
are chains of `2P` copies + a body: one lemma per kind, parametric in `P`.

## 5. Sequential operation: what is in flight together

An activation of instruction `i` starts when a glider enters an entry copy of unit `i` and ends when
the glider for the next instruction enters its unit. In between, only:

* **decJz**: `KNZ`, `C`, `KZ` (emitted together, nested: **no crossing**); then `C'` and DZ2 inside
  module `r`; one token meets the register output at its station and becomes the answer; the other
  token is consumed at its station (unpaired Z token: ≥ 41 733 generations before the NZ answer
  reaches unit `i + 1`; unpaired NZ token: 2 463 before the Z answer leaves its station). Crossings:
  NZ answer (left-zone channel, going up) × KZ's `BACK` track: KZ passed ≥ 41 944 generations
  earlier; Z answer (final column) × KNZ's `OUT` track: KNZ passed ≥ 101 000 earlier — in both
  cases the token has left the band before the answer exists (causality).
* **inc**: continue and INC link (nested in their sub-band), then the merge unit and the merge link
  (own sub-band below all instruction sub-bands: no crossing with the continue); the only crossing,
  continue's final column × the link's `BACK` track, is passed by the continue ≥ 69 055 generations
  later (it reaches its corner only after `T_INC + 500`).
* register processes inside module `r` (REG1 salvo after INC, DZ2 restore after Z) overlap the next
  activation only within R-29's measured spacings (§4.3), and only module `r`'s own paths.

Every other pair of links belongs to different activations and is separated in time by
causality; geometrically such paths may cross, but no corner lies within 61 of a foreign segment
(§3), so crossing paths never meet a piece.

## 6. HALT

The halt unit's output goes down to the top track `OUT_0 = V_T + π` (sub-band 0, no hairpin) and
turns SW; it flies SW for ever. The HALT cell is the point of that line with `u = u_min − 600`
(`u_min` = least `u` of all pieces): `add` `(u, v) = (−17 625, −9 599)`, `share` `(−15 315, −8 459)`,
`rand` `(−25 905, −11 759)`; distance ≥ 300 cells to every piece and every other route (635 …
967 measured). Nothing else is ever at `v = OUT_0` (sub-band 0 has no other link, all hairpin
verticals and corners lie in their own sub-bands, ≥ 61 deeper), and in every run the halt glider
is the only glider that leaves the machine.

## 7. Verification

**Static** (`p2_check.py`; `results/p2_{add,share,rand}.txt`): (F) the 17 inequalities, (S) corners
vs foreign segments (min gap 61), (C) route segments vs pieces they do not interact with (none
within 13 cells), piece envelopes of different regions (min 31 cells), HALT cell, (D) diagonals,
(T) residues, token formulas, slacks, unpaired tokens, (X) concurrent crossings — **0 failures**
on all three layouts. **Sweep** (`p5_formulas.py 25`): 25 random programs (`3 ≤ N ≤ 9`,
`R ≤ 4`, `D ≤ 4`, `P ≤ 4`, up to 529 pieces): residue table §4.1, token formulas §4.2 (74
decJz), continue slack ≥ 6, Z slack ≥ 26 646, route law on 538 links, corner gap ≥ 61.

**Exact runs** (`p3_run.py`, psim; `results/p3_*.txt`). Random program (`p4_random.py`, seed 1):
`rand = [inc 2, decJz 0 → 4, inc 1, decJz 1 → 6, inc 0, decJz 1 → 3, halt]` (3 registers; register
1 used by `inc` and two `decJz` callers `j = 0, 1`; register 0 by `decJz` and `inc`; jumps forward
and backward). "ok" = exactly one escaped glider, on the HALT line, passing the HALT cell, and 30 000
generations after it left, the whole plane equals the cycle of all pieces + eaters + blocks at the
interpreter's final values.

| program | input | instruction trace | halt glider leaves core at (from start) | final registers | result |
| --- | --- | --- | --- | --- | --- |
| `add` | {0: 0, 1: 0, 2: 0} | [0, 3] | 143340 | {0: 0, 1: 0, 2: 0} | ok (1 escaped glider, HALT cell passed: yes) |
| `add` | {0: 1, 1: 0, 2: 0} | [0, 1, 2, 0, 3] | 446940 | {0: 0, 1: 1, 2: 0} | ok (1 escaped glider, HALT cell passed: yes) |
| `add` | {0: 2, 1: 0, 2: 0} | [0, 1, 2, 0, 1, 2, 0, 3] | 751140 | {0: 0, 1: 2, 2: 0} | ok (1 escaped glider, HALT cell passed: yes) |
| `add` | {0: 3, 1: 0, 2: 0} | [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 3] | 1055340 | {0: 0, 1: 3, 2: 0} | ok (1 escaped glider, HALT cell passed: yes) |
| `rand` | {0: 0, 1: 0, 2: 0} | [0, 1, 4, 5, 3, 6] | 722940 | {0: 1, 1: 0, 2: 1} | ok (1 escaped glider, HALT cell passed: yes) |
| `rand` | {0: 1, 1: 0, 2: 0} | [0, 1, 2, 3, 4, 5, 3, 6] | 965340 | {0: 1, 1: 0, 2: 1} | ok (1 escaped glider, HALT cell passed: yes) |
| `rand` | {0: 1, 1: 2, 2: 1} | [0, 1, 2, 3, 4, 5, 6] | 812340 | {0: 1, 1: 1, 2: 2} | ok (1 escaped glider, HALT cell passed: yes) |
| `rand` | {0: 2, 1: 1, 2: 0} | [0, 1, 2, 3, 4, 5, 6] | 812340 | {0: 2, 1: 0, 2: 1} | ok (1 escaped glider, HALT cell passed: yes) |
| `share` | {0: 0} | [0, 1, 2, 3] | 305940 | {0: 0} | ok (1 escaped glider, HALT cell passed: yes) |
| `share` | {0: 1} | [0, 1, 2, 3] | 297540 | {0: 0} | ok (1 escaped glider, HALT cell passed: yes) |
| `share` | {0: 2} | [0, 1, 2, 3] | 297540 | {0: 1} | ok (1 escaped glider, HALT cell passed: yes) |

All 11 runs: ok. Run times 3–17 min each (11 in parallel, ≈ 1 ms per generation per process under load, < 30 MB each); the longest run (`add`, r0 = 3) is 1 085 010 generations.

## 8. Caveats and obstructions

* **O13 (KZ must be the inner link).** The Z token needs the even source column and the rightmost
  destination; nesting then forces it innermost, so its large lag (≈ 1 564 per `q`) cannot come
  from a hairpin; it comes from the depth below the module and from moving `C` later by whole
  periods (`15x` steps), which the KNZ hairpin follows.
* **O14 (residue classes mod 8).** The token deltas allowed by the stations cover only the classes
  `{0, 1, 2, 5, 7} (mod 8)`; `σ = 2 (q mod 2)` (one or two slots of `C`) is necessary for odd `q`.
* **Sizes.** LP is about 2–3 times wider than R-30 (continue hairpins far left: `G` ≈ 4 000 –
  25 000); an `inc` costs ≈ 70 000 – 140 000 generations. Exact runs need the sparse simulator.
* **Assumptions not re-verified here**: R-29's module facts (stations by translation for any `D`,
  DEC chain of `2D` copies, reuse spacings, the `k`-independence above `k = 300`), and R-30's
  clearance of the port legs inside the module (1 500–2 000 cells); the residue table is fitted
  on 25 + 3 layouts, not derived symbolically; the unit templates are checked for `n ≤ 6` only.

## 9. Files (`scripts/life_lp/`)

`psim.c`, `psim.py` (simulator; self-test), `lpcommon.py`, `p0_parts.py` (templates,
`results/p0_units.{txt,json}`), `p1_layout.py` (the rule LP), `p2_check.py` (static checks),
`p3_run.py` (exact runs), `p4_random.py` (test program, `results/prog_rand.json`,
`results/p4_random.txt`), `p5_formulas.py` (sweep), `p6_catalogue.py` (certificate catalogue),
`runall.sh` (all runs in parallel). Reproduce: `python3 psim.py; python3 p0_parts.py 1 2 3;
python3 p4_random.py 1; for p in add share rand; do python3 p2_check.py $p; done;
python3 p5_formulas.py 25; python3 p6_catalogue.py; ./runall.sh` (static parts minutes; runs
5–40 min each, 11 in parallel, < 100 MB each).
