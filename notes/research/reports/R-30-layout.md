# R-30: Program layout — a counter machine laid out by a rule, simulated to halting (own search)

**Status of every result in this report: numerical observation (own search), not verified in
Lean.** Produced on 2026-11-15 by the untrusted oracle `scripts/life_layout/` (new scripts
`lcommon.py`, `l0_module.py` … `l6_jog.py`; `scripts/life_route` (R-29: `gsim`, `gcommon`, OR gate,
chains, stations, `G_I`), `scripts/life_zero` (DZ2), `scripts/life_machine` (pieces, fan-outs, `RF0`)
and `scripts/life_gates` are imported read-only). Nothing from pattern collections or the
literature. Conventions as in R-21 … R-29 (world frame of REG1; cells `(x, y)`, `y` down; world
lines `(d, lane, tau)`; pieces `('asm'|'rf', sym, x, y, delay)`). New here: the rotated
coordinates **`u = x − y`, `v = x + y`**. An SE / NW glider keeps `u` (its SE lane) and moves in
`v`; an NE / SW glider keeps `v` (= minus its NE lane) and moves in `u`; every glider covers
2 units of `(u, v)` per 4 generations. Glider routing is therefore Manhattan routing in `(u, v)`.

## Summary

| Goal | Result |
| --- | --- |
| layout rule | **`l2_layout.layout(program)`**: a computable rule placing register modules, instruction units, merge units and all routes for any well-formed program (`inc r`, `decJz r z`, `halt`, `CounterMachine.lean`); only three piece types (`blockedStream` copies, reflector `RF0`, eater 1) besides the register blocks |
| registers | one **module `M(nd)`** per register (`nd` = number of `decJz` instructions on it): REG1 + DZ2' + `G_I` + `RF_J` + one INC chain copy + a DEC chain of `2 nd` copies + `nd` dispatch stations per answer line (R-29), placed side by side along `u`; the block diagonal of register `r` is the ray `u = U_r − 96`, `v ≥ 404`, and nothing of another register, no route and no unit comes within 13 cells of `B_−1 … B_600` (check (c)) |
| instruction units | `inc`: entry merge chain + transposed fan-out `F_I` (INC link + continue); `decJz`: entry chain + the DZ2 front `F_B + F_A` (three outputs: DEC control `C`, NZ token, Z token); `halt`: entry chain, its output flies SW forever on the **HALT line**; one merge unit per register collects its `inc` callers |
| routing | every link: source column → OUT track (SW) → hairpin at `u = H` → BACK track (NE) → destination column; columns in reserved channel zones (modules) or unit slabs, tracks in a band above all modules; **the hairpin position `H` is the delay knob** (`H → H − 2`: +8 generations) |
| timing | rules (§4): residue windows of the receiving OR gates (13 residues), exact token windows (R-29 `δ`) solved through the slot of `C`, minimum delays (Z answer ≥ end of DZ2's Z restore + 300; INC continue ≥ INC control at the register + 500) |
| static checks (`l3_check.py`) | both test layouts: envelopes of different groups ≥ 28 cells; every route leg ≥ 13 from all pieces it does not use; diagonals clear; concurrent links cross ≥ 151 generations apart; HALT cell left of everything |
| exact simulation (`l4_run.py`, gsim) | **addition program (3 registers, 4 instructions, 247 pieces), r0 = 0, 1, 2, 3; sharing program (1 register used by `inc` and two `decJz`, 159 pieces), r0 = 0, 1, 2: every run halts with exactly one escaped glider (on the HALT line) and, cell by cell, the cycle of all pieces + eaters + the blocks at the interpreter's final values** (table §6) |

## 1. Parts

### 1.1 Register module `M(nd)` (`l0_module.py`)

Module-local = world frame of REG1 (R-24 … R-29). Pieces:

* REG1 (22), DZ2' (19: DZ2 of R-28 with `RF_C3 → RF_C3'`), `G_I`, `RF_J` (R-29 §1.3, §1.4);
* INC: **one** INC chain copy `('asm', 0, −1132, −1291, 14)` (R-29's copy 3); its side input
  `(NE, 2347, 4543 … 4555) + 30m` is the module's INC port (several `inc` callers are merged in a
  merge unit, §1.2);
* DEC chain of `2 nd` copies `g5_chain.chain(2 nd, 64, −1700)` (translation `(35, 64)` per copy;
  side input of copy `t` at `v = −3351 − 99 (2 nd − 1 − t)`; consecutive side lines differ by 99,
  i.e. in parity, which the router needs, §3.3); caller `j` uses copy `2j` or `2j + 1`;
* stations `j = 0 … nd − 1` on the NZ and Z lines (`g9_dispatch.line_stations`, translation
  `(72, ±72) j`), token eaters, and the two line-end eaters 120 cells beyond the last station.

DEC copy `t` → DZ2's `C'`: input at `τ_t + 5 + 600` gives `C' = (SE, 41, 4444 + 30 q_t)` (exact run,
`Net.react`; e.g. `nd = 1`: copy 0 `q = 108`, copy 1 `q = 100`); with `C' = (SE, 41, 4444 + 30q)`
every R-29 datum (tokens `K`, dispatched answers `S'`) is shifted by `30q`.
Footprint in `(u, v)`: `u ∈ [−733, 1350 + 144 nd]`, `v ∈ [−3324 − 198 nd, 1379 + 144 nd]` (`nd ≥ 1`;
`nd = 0`: `[−733, 1498] × [−2419, 1529]`).

### 1.2 Unit templates (`l1_parts.py`, `results/l1_units.json`)

Local frame: last entry copy `('asm', 0, 0, 0, 0)`.

* **Entry chain** of `n = 2 max(1, p)` copies (`p` = number of predecessors; the start counts as one):
  copy `t` = `('asm', 0, −35t, −64t, s_t)` with `g5_chain`'s relay delays, side input
  `(NE, −76 + 99t, τ_t … τ_t + 12) + 30 m` (`v = 76 − 99t`), output `(SE, 14, ·)`; every copy re-times
  to the unit's clock (output residue independent of the input copy and residue).
* **Body**: `dec` = `F_B + F_A` of R-28 translated by `(1193, 1220)` (input = the chain output), outputs
  `L` (SW, `v = 288`), `R` (NE, `v = 1342`), `D` (SE, `u = 14`); `inc` = `F_A` translated by
  `(694, 667)`, outputs `R` (NE, `v = 290`, continue) and `D` (SE, `u = 68`, link); `halt`, `merge`:
  output `D` = the chain output.
* `L`, `R` are turned down (SE) by one `RF0` each at `c_L` = body's left `u` − 70, `c_R` = right `u` + 70
  (parity-fixed): `dec` columns `u = −155, 14, 127`; `inc` `68, 157`; `halt`/`merge` `14`.
* **Input columns** `c_in(t)` = unit's left `u` − 60 − 60t (parity-fixed, so that the router's
  NW → NE reflector at `(c_in(t), v_t)` exists); they alternate in parity with `t`.
* Exact runs (gsim, every template `kind × n = 1 … 4`, every input copy): input → exactly the listed
  outputs, all pieces back in their cycle (`l1_parts.py`).

### 1.3 Pieces of a machine

Only `blockedStream` (8 images), `RF0` (8 images), eater 1 (8 images) and the register blocks. Addition
program: 247 pieces + 70 eater cells; sharing program: 159 pieces + 42 eater cells
(`results/l5_{add,share}.json`: complete piece lists, eaters, register shifts, start glider, halt line).

## 2. The layout rule (`l2_layout.py`; all coordinates `(u, v)`)

Given a program `P` (indices `0 … N−1`, `P` well formed: targets in range, last instruction `halt`):

1. **Registers** `r` used by `P`, in increasing order; `nd_r` = number of `decJz r`. Module `r` is
   `M(nd_r)` translated by xy `(U_r / 2, −U_r / 2)` (`u`-shift `U_r`, `v`-shift 0), with
   `U_0 = 733 + 100 + 60 (4 nd_0 + 1) + 60` and
   `U_{r'} = U_r + right_r + 100 + 120 nd_r + 60 + 733 + 100 + 60 (4 nd_{r'} + 1) + 60` for the next
   register `r'` (rounded up to even); `right_r = 1350 + 144 nd_r`. Register `r` holding `k` is the
   block `translate (148 + U_r/2, 240 − U_r/2) (counter k)`; its diagonal is `u = U_r − 96`, `v ≥ 404`.
2. **Channel zones.** Left of module `r`, at `L0 = U_r − 833`: DEC copy `t` at `L0 − 60 t`
   (`t = 0 … 2 nd − 1`), INC at `L0 − 120 nd`, NZ token `j` at `L0 − 60 (2 nd + 1 + 2j)`, NZ answer `j`
   at `L0 − 60 (2 nd + 2 + 2j)`. Right of the module, at `R0 = U_r + right_r + 100`: for
   `j = nd − 1, …, 0` the Z answer `j` and Z token `j` at `R0 + 60 idx`, with bottom legs at depths
   `v_d(j) = 900 + 160 (nd − 1 − j)` (answer) and `v_d(j) + 80` (token). Every column value is lowered
   by one where needed for the parity of its corner (§3.3). In each zone the channel nearer the module
   is the shallower one, so no leg into or out of the module crosses another channel of its zone;
   zones of neighbouring modules do not interleave, so no channel leg of one register crosses a
   channel of another.
   Port legs (module side): DEC/INC/NZ-token: down the channel, `SE → NE` at the side line; NZ answer:
   `SW → NW` at the channel; Z answer: `SE → NE` at `v_d(j)`, `NE → NW` at the channel; Z token: down,
   `SE → SW` at `v_d(j) + 80`, `SW → NW` at the token line `u = 1230 + 144 j + U_r`.
3. **Links** in this order: for each instruction `i`: `inc`: link (to merge unit of `r`), continue (to
   `i + 1`); `decJz`: `C`, `K_NZ`, `K_Z`, NZ answer (to `i + 1`), Z answer (to `z`); `halt`: halt line;
   then one link per merge unit (to the INC port). `N_L` links.
4. **Band.** `V_B = min_r top_r − 200`; link `k` has OUT track `h_k = V_B − 170 (N_L − k)` and BACK track
   `h_k + 100`.
5. **Units** (instructions `0 … N−1`, then the merge units) in a row, slabs 160 apart, the row ending
   300 left of the leftmost channel; unit `v`: bottom 200 above the band
   (`V_unit = h_0 − 200 − max height`, ±1 for parity). Merge units are shifted by one in `u` if needed so
   that their output column has the parity of the INC port channel.
6. **Input copies.** Each predecessor of a unit takes a free entry copy whose input column has the
   parity of the predecessor's source column (`n = 2p` copies always suffice). DEC: caller `j` takes the
   one of copies `2j, 2j+1` of the right parity. `decJz` outputs: the token whose port column has the
   parity of `D` gets `D`, the other token `R`, and `C` gets `L` (the token lines of all stations have
   one parity, `144` being even, the two tokens' channels have opposite parities, so this always works).
7. **Route of a link:** source prefix → `(SW, h_k)` → `(SE, H_k)` → `(NE, h_k + 100)` →
   `(NW` or `SE, c_dst)` → destination suffix (each turn one `RF0`, placed by `net.reflect` from the
   exact world line, so its phase is that of the link's glider).
8. **`H_k`** = the first value, scanning from `min(c_src, c_dst) − 70` leftwards in steps of 2, that is
   free (no column within 70 in `u` whose `v`-span meets `[h_k − 50, h_k + 150]`) and satisfies the
   timing condition of the link (§4). Fallback (never needed in the tests): a token route may make one
   jog in its hairpin (two more reflectors, +230 generations, checked in `l6_jog.py`).
9. **Halt:** the halt unit's output goes down to its track and turns SW; it flies SW for ever. The
   **HALT cell** is a cell of that line 300 cells left of every piece and route corner, visited by the
   glider in each of its four phases: addition `(−6252, 2190)`, sharing `(−6351, 2091)`. Nothing else
   ever comes near it: all pieces and corners are at `u ≥ −7859`, and in every run the halt glider is
   the only glider that leaves the machine.
10. **Start:** a glider on instruction 0's start copy side line (residue 5 of the window) at its input
   column.

Steps 1–7 are closed formulas in the program; step 8 is a finite scan (terminates: far enough left
everything is free, and the arrival moves by 8 per step, §4).

## 3. Why routes do not collide

1. **Pieces vs pieces / paths** (by construction, checked): units above the band, modules below,
   channels in their zones, hairpins in free places, tracks 70 apart in `v`, columns ≥ 60 apart.
   Check (a): envelopes of different groups ≥ 31 (addition), ≥ 28 (sharing); (b): every route leg
   (until the receiving gate; the HALT line to `u = −9000`) ≥ 13 from every piece and eater it does
   not use.
2. **Diagonals:** every module is entered only through its channels; the rays `u = U_r − 96`,
   `v ≥ 404` lie inside module `r`'s zone; check (c): `B_−1 … B_600` of every register ≥ 13 from all
   foreign pieces, eaters and legs.
3. **Parity:** a reflector corner needs `u + v` odd (bbox-origin lines; `net.reflect` measured for
   all 8 images: output lane parity = 1 − input lane parity, latency −5 for every turn), so in one
   route all `u`-lines have one parity and all `v`-lines the other; a band route joins two `u`-lines
   of **equal** parity. Handled by the two copies per input (§2.6) and the token assignment.
4. **Signal crossings.** Only one instruction is active at a time; links of different activations
   may cross (they are timing-disjoint by causality: an activation starts only when the previous
   one's answer / continue has arrived). Concurrent gliders are only (i) `C`, `K_NZ`, `K_Z` of one
   `decJz` and (ii) INC link, merge link and continue of one `inc`: check (d) computes every crossing
   point of concurrent legs exactly: ≥ 151 (addition) / ≥ 159 (sharing) generations apart. The INC
   continue waits until the INC control has entered the register (rule §4), so no INC glider is in
   flight when the next instruction starts; a token not used (the Z token of an NZ call) is in its
   own channel zone, which no other link enters. Hazard checked (`l5_summary.py`): an unpaired Z token
   passes its station 12 279 (12 567) generations after `C'`; the next call on the same register
   can produce a Z output at a station only ≥ 12 457 generations after its own `C'`, which comes after
   the NZ answer has left (≥ 10 697 after the first `C'`): margin 10 875.

## 4. Timing rules

* **Route time** (measured): `2 · (Manhattan (u, v) length) − 5 · (turns)`; a plain hairpin shifts the
  arrival by `+8` per step `H → H − 2`; the parity of the arrival is fixed by the endpoints.
* **Units re-time**: an input anywhere in the 13-residue window of a copy (`τ_t … τ_t + 12` mod 30)
  gives the unit's outputs at fixed residues; units, modules and route reflectors have no free
  phase left after placement (`delay` of every piece is determined).
* **Window rule** (continues, answers, INC link, merge link, `C`): choose `H` so that the arrival on
  the receiving side line has residue `τ … τ + 12` (mod 30). Since steps of 8 run through all 15
  residues of the arrival's parity and the window contains 6–7 of each parity, at most 15 steps are
  needed.
* **Token rule** (exact): `C` arrives in its window, which fixes `C' = (SE, 41, 4444 + 30q)` (module
  frame); `K_NZ` and `K_Z` must arrive at `R-29`'s token world lines shifted by `30q`, plus
  `δ ∈ {−3, −1, 0, 1, 2, 7, 8, 9}`. Scan the slots `q` of `C` (each later slot `+30 ≡ 6 mod 8`), for each
  find `H` of both tokens. With one optional jog (+230 ≡ 6 mod 8) both tokens are solvable within 4
  consecutive slots; without jogs (pass 1, at most 12 slots) all 4 `decJz` units of the tests were solved (achieved
  `δ`: 0 for `K_NZ`, −3 for `K_Z`).
* **Z answer**: arrival at the next unit's gate ≥ (end of DZ2's Z restore = `Ts + 27 540`, `Ts` as in
  `f8_full.py`) + 300. Stronger than R-29's spacings (19 470 / 22 238); it also keeps every DZ2 flight
  path idle while other instructions run. In the tests the natural route already exceeded it by
  12 762 … 28 182.
* **INC continue**: arrival at the next unit's gate ≥ arrival of the INC control (through the merge
  unit) at the INC copy + 500. This gives INC → INC ≥ 450 (R-29, `k`-independent) and INC → DEC
  trivially. It is the costly rule: the continue hairpin goes far left (24 301 / 29 381 generations of
  flight).
* **After NZ** nothing is needed: R-29's DEC → DEC 1860, DEC → INC 2468 are implied by causality (the
  answer leaves the station 10 697 after `C'` passes `F_B`).

## 5. Layouts of the test programs (`results/l5_add.txt`, `results/l5_share.txt`)

Addition `add = [decJz 0 → 3, inc 1, decJz 2 → 0, halt]` (register 2 is a zero register: `decJz 2 → 0`
is the jump back; `r1 += r0`): modules at `U = 1194, 3922, 6774`; band `v = −6102 … −3722`; units at
`v = −7762`; 14 links, 5–7 reflectors each; flights 9 445 (INC link) … 41 995 (Z answer of the jump).
Sharing `share = [inc 0, decJz 0 → 3, decJz 0 → 3, halt]` (register 0 in both roles, two DEC
callers, two stations per line, INC → DEC and DEC(NZ) → DEC on one register; result `max(r0 − 1, 0)`):
one module at `U = 1434`, 14 links.

## 6. Exact simulation (`l4_run.py`, `results/l4_*.txt`)

gsim on the unbounded plane (core box ≈ 11 300 × 8 000 cells for `add`, 9 400 × 5 500 for `share`);
a glider is removed only when it is outside the box containing every piece and moves away. Run until
the halt glider leaves, then 30 000 more generations; the final state is compared cell by cell with
the cycle of all pieces + eaters + the register blocks at the values of the interpreter.

| program | input | instruction trace | halt glider leaves at | final registers | result |
| --- | --- | --- | --- | --- | --- |
| `add` | r0 = 0 | 0, 3 | 82 740 | (0, 0, 0) | ok |
| `add` | r0 = 1 | 0, 1, 2, 0, 3 | 262 740 | (0, 1, 0) | ok |
| `add` | r0 = 2 | 0, 1, 2, 0, 1, 2, 0, 3 | 442 740 | (0, 2, 0) | ok |
| `add` | r0 = 3 | 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 3 | 622 740 | (0, 3, 0) | ok |
| `share` | r0 = 0 | 0, 1, 2, 3 (NZ at station 0, Z at station 1) | 168 540 | 0 | ok |
| `share` | r0 = 1 | 0, 1, 2, 3 (NZ, NZ) | 161 340 | 0 | ok |
| `share` | r0 = 2 | 0, 1, 2, 3 (NZ, NZ) | 161 340 | 1 | ok |

(Generations from the start glider until the halt glider leaves the core box; registers `(r0, r1, r2)`.
"ok": exactly one escaped glider, on the HALT line, and after 30 000 more generations the whole
plane equals the cycle of all pieces + eaters + blocks at the interpreter's values.) One loop of the
addition program (`decJz 0` NZ, `inc 1`, `decJz 2` Z) takes exactly 180 000 generations here; the
runs used 4.5–8 ms per generation (up to 7 runs in parallel, < 60 MB each).

## 7. Obstructions and caveats

* **O10 (lane parity of routes).** Reflector routes can only join `u`-lines of equal parity
  (corner rule `u + v` odd). Fixed by two entry copies per predecessor (side lines 99 apart), two
  DEC copies per caller, the token assignment, and one-cell shifts of merge units.
* **O11 (route-time granularity).** A hairpin changes the arrival only by multiples of 8 and keeps
  its parity; the exact token windows are met through the slot of `C` (+30 ≡ 6 mod 8) and, if needed,
  one jog (+230 ≡ 6 mod 8).
* **O12 (cost of the conservative INC rule).** Waiting for the INC control to reach the register
  before the next instruction makes every `inc` cost ≈ 25 000–30 000 generations; a finer rule
  (exact crossing checks against the successor's routes) would save most of it.
* **Not proved for every program:** checks (a)–(d) are run per layout (they hold by construction
  for (a)–(c) except for the `free` margin choices; (d) — crossings of the three concurrent `decJz`
  outputs and of the INC trio — is a computed property, not a theorem; a violation of a window-timed link would be repaired
  by moving its hairpin by 30 in `u` (+120 generations, every residue kept); not implemented).
* **DEC chain length.** `2 nd` copies by translation: geometry checked only up to `nd = 2` in runs;
  R-29's side-line clearance argument (each side line passes only the next copy, at 12) holds for
  any length. The INC side is a single copy for every register (callers merged in a merge unit), so
  a long INC chain at the module (whose upstream copies would run into the DEC chain's side lines after
  ≈ 10 copies, by the geometry of §1.1; not simulated) is never needed.
* **Speed.** ≈ 4.5–8 ms per generation for 11 000 × 8 000 cells; the 3-iteration addition run took
  ≈ 57 min for 652 260 generations.

## 8. Files (`scripts/life_layout/`)

`lcommon.py` (coordinates, imports), `l0_module.py` (module `M(nd)`), `l1_parts.py` (unit templates,
exact I/O runs, cache `results/l1_units.json`), `l2_layout.py` (the rule), `l3_check.py` (static
checks; `results/l3_{add,share}.txt`), `l4_run.py` (exact runs; `results/l4_*.txt`), `l5_summary.py`
(timing table and export; `results/l5_{add,share}.{txt,json}`), `l6_jog.py` (jog hairpin;
`results/l6_jog.txt`). Reproduce: `python3 l1_parts.py; python3 l3_check.py add; python3 l3_check.py
share; python3 l5_summary.py add; python3 l5_summary.py share; python3 l6_jog.py;
python3 l4_run.py add r0=3` (and `r0=0,1,2`; `share r0=0,1,2`): minutes for the checks, 10–60 min
per run.
