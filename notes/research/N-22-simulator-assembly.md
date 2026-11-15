# N-22: Assembling the simulator

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-22` |
| Title | Construction of `Simulator P` for every well-formed program |
| Kind | formalization plan |
| Addresses | `G-7`, `N-21` |
| Depends on | `N-19`, `N-20`, `N-21`; Lean: `Simulator`, `LayoutLP`, `Network`, `Chain`, `MergeSide`, `Route`, `Rf0Images`, `StationFacts`, `Gen/Body*`, `Gen/Dz2*`, `Diagonal`, `Salvos` |
| Dependency requirement | all compiled |
| Produces | the remaining work list of `G-7` |
| Difficulty | hard (assembly at scale, every statement generic in the program) |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-15: created |

## Why generic

The program of `exists_program_halts_not_computable` is not explicit, so the construction must
work for every well-formed program; concrete generated certificates apply only to the finitely many
*kinds* of local situations (the 25 certificates of `R-31`), placed by translation and time shift.

## Layers

1. **Placed pieces.** `Piece.place g v p`: a piece translated by `v` at phase `p` (rest reaction,
   box moved). The machine `Mach P` as a list of placed pieces (units, modules, route reflectors,
   eaters) from the formulas of `LayoutLP`.
2. **Regions.** For each part (unit, module, link) a region box; every piece of the part lies in
   it; distinct parts' regions are far apart (`LayoutLP` inequalities); pieces inside a part are far
   apart (template facts, chains by translation). Hence `MachPieces_sep : (Mach P).Pairwise Sep`.
3. **Activations.** For each instruction kind a list of processes (generic lemmas):
   entry chain (`chain_side_reaction` placed), body (`bodyIncRun_rest` / `bodyDecRun_rest` placed),
   routes (`Stage.route_reaction` with the reflector stages and flights of symbolic length), module
   chain and run (`orChainSide*`, `dz2gAll` / `dz2mk1Run_rest` / `dz2mk0Run_rest` / `dz2jAll`
   placed, the diagonal by `diag_add`), stations (pass / capture by translation and induction),
   with the rest of the machine as one idle bundle. Separation of the active processes from the
   idle bundle by the region facts.
4. **Encoding.** `enc s`: the machine pieces at phase `φ`, the control glider at the entrance of
   `pc`, and the diagonals of the registers (`N-20`). `Inv s`: validity of the queues, phase and
   timing facts.
5. **Step and halt lemmas** from 3 and 4; then `Simulator P`; then the corollary with the start
   family `n ↦ Mach P ∪ block₀ n` (computable in `n`).

## Order of work

1 → 2 → the `inc` activation → the `decJz` activations (value 0, 1, ≥ 2) → halt → encoding and
`Simulator` → corollary. The `decJz` activation with value `≥ 2` needs the zero test regenerated
with the register diagonal as a generic process (`emit_generic` with `diag_add`, `diag_near`).

## Progress

* 2026-11-15: `dz2dNZ` (`Gen/Dz2dRun.lean`): the `decJz` activation at the register for value `≥ 1`
  with any queue of salvos in flight (the diagonal a generic process; the detector separated from
  every block at position `≥ 0` in `x + y`, `UVBox`); the pull salvo joins the queue
  (`diagW_add`) once past `REG1`. Station chains (`StationChain`), placed pieces (`Placed`), one
  circuit for all operations (`RegisterCircuit`). Placements of the whole machine: `LayoutPieces.lean` (sub-agent, checked here): `LP.machPieces`,
  `LP.machPieces_sep` for every well-formed program (layers 1 and 2 done). Notes: Lean boxes slightly
  larger than R-31's measured boxes (absorbed by the margins); module/template timing constants are
  fitted formulas, cross-checked for `D, P ≤ 4`; several `halt` instructions are placed but their
  dynamics is not yet addressed.
* 2026-11-15: `diag_arrived` (zero case), `dz2eOp` (increment with the diagonal).
* 2026-11-15: `MachineState.lean`, `ActivationInc.lean` (sub-agent, checked here): the encoding
  `encM`, `InvM`, region and halt cell; building blocks of the `inc` activation (reflections and
  routes on world lines through the idle machine, body, RF_J, `dz2eOp` at a module). **Open**:
  (1) phase mod 4: activation times are fixed only mod 30, `dz2eOp`/`dz2dOp` need the merge time
  `≡ 0 (mod 4)` relative to the diagonal; (2) separation of route flights and relay boxes from all
  other pieces (R-31 #13, segment vs piece); (3) `T ≤ meetT` and arrival residues; (4) entry and merge
  chains on the way; (5) footprints of the body and register runs; (6) concurrent active processes;
  (7) other registers' strips vs pieces; then the step and `Simulator`.
* 2026-11-15: phase mod 4 resolved: the salvos at all four phases (`SalvoPhases`), queue parameters
  widened (`N = 40`, `U₂ = 23`, gap `30`), the register operations with the diagonal regenerated for
  each phase (`dz2dOp`, `dz2d1Op` … `dz2d3Op`, `dz2eOp`, `dz2e1Op` … `dz2e3Op`).
* 2026-11-15: `ActivationIncLinks` (lines and timing of the `inc` and merge links for every program:
  `unitLink_timed`, `mergeCorners_lines`, `routeOK_of`), `ActivationIncModule` (`dz2eAny_module`: the
  increment at a module for every phase; `RegS.val_pushAny`, `RegS.inv_pushAny`). Open for `inc_step`:
  route separation (segments vs pieces), entry chains at the destination, merge link to the module
  input, footprints of body and register runs, concurrent processes, other registers' strips,
  composition.
* 2026-11-15: footprints of the generated runs (`RunFoot.lean`, `Gen/*RunR.lean`, generated by
  `scripts/life_cert/emit_runr.py` from the segment files): `bodyIncRun_restR`,
  `bodyDecRun_restR`, `dz2dOpR` … `dz2d3OpR`, `dz2eOpR` … `dz2e3OpR`, `dz2mk1Run_restR`,
  `dz2mk0Run_restR` — each run as a `Reaction` with the constant footprint `Box U` (the run's
  bounding box), together with `regLanes` (lanes of the register diagonal, `x + y ≥ 354`) for the
  runs with the diagonal. Caveat: the box of `dz2mk0` (value 0) contains the whole flight of the
  Z answer (to `x = 4564`); the `decJz` activation should cut that run where the answer leaves
  the circuit, or use a lane for it.
* 2026-11-16: `ActivationIncEntry`, `ActivationIncArrive`, `Gen/ActSide` (sub-agent, checked here):
  entry chains at the destination for every copy `t` (`entry_reaction`, `entryRelay`,
  `orOut_flight_unit`, `entry_time`: the control reaches the body input at a time `≡ 0 (mod 30)`),
  the window rule as a theorem (`upCorners_tau`, `upLink_offset`, `incLink_offset`: arrivals at
  offset 4 or 5), `window_group` (a group of active pieces with the rest idle). Correction to
  `R-31`: "R-29 numbering = r0 + 1" should be `r0 + 2`; offset 5 needed new side certificates
  (`orSide7`, `orChainSide7`; also `orSide8`). Open: merge unit and module input, composition.
* 2026-11-16: `ActivationIncMerge` (sub-agent, checked here): merge unit output on the merge line
  (`mergeStart_eq`), merge link route law and offset (`downCorners_tau`, `mergeLink_offset`,
  `mergeLink_timed`), the module's INC gate (`incWin_eq`, `module_side_arrival`,
  `incGate_reaction`, `incGate_out`), RF_J as a route corner (`rfJ_reflect`, `rfJ_meet`) and the
  hand-over to the increment (`rfJ_to_dz2e`: at `1140 + 30k` the glider is the input of `dz2eOp`
  at module `r`). Open: composition of `inc_step`; `DiagValid` for an appended salvo.
* 2026-11-16: `DiagAppend` (sub-agent, checked here): `diagValid_append` (a salvo appended at least
  `g` behind keeps the queue valid), `QBefore`, `joinVs`, the exact `hv'`/`hVs'` of the eight
  register operations (`dz2e_join` … `dz2d3_join`), `RegS.pushAny_join`, `RegS.inv_pushAny_join`.
  **Finding**: these need the value condition `hz` — the target value `w = K + qMove q` must be
  `≥ 16` (push) or `≥ 8` (pull), because the static reaction box of a salvo reaching a block near
  the circuit dips below `Vb = 18`. Small values are genuinely different: the reaction then
  happens near the circuit, inside the run. **Resolution (plan)**: for small `w` every salvo has
  already arrived at the start of the operation (generalized `diag_arrived`: each queued salvo is
  far along, and the block is near), so the register is a static block and the static-block
  certificates apply: `dz2jAll` (INC, every `k`), `dz2gAll` (`k ≥ 2`), `dz2mk1` (`k = 1`), `dz2mk0`
  (`k = 0`); their outputs are on the same world lines as `dz2dOp`'s (the circuit "in its cycle").
* 2026-11-16: `dz2jAllR` (`Gen/Dz2jRunR.lean`, `Gen/Dz2jAllR.lean`): the increment of a static
  block at any position `k` as a reaction inside `Box (-1395) 668 (-1489) 659 ∪ regLanes`
  (`dz2jPullG_sub`: the generic salvo and block in the box near the circuit, then in the lanes).
* 2026-11-16: `DiagSmall` (sub-agent, checked here): `diag_arrived_le` (value `≤ W` and every salvo
  `≥ N/4 + 4 + W` along ⇒ arrived), `diagW_static`, `QBeforeL` (kept by the increment with margin
  76 and by the pull with margin 1217), `RegS.push_dichotomy` / `RegS.pull_dichotomy` (either the
  value condition of the diagonal operation holds, or the register is a static block `≤ 15` / `≤ 7`),
  `RegS.block` after a static-block run.
* 2026-11-16: layout correction (found by the `inc_step` agent): with the continue delay
  `tinc + 500`, the continue could reach unit `i + 1` before the increment at module `r` ended
  (probe: up to 420 generations early). `incSpecs` now uses `tinc + 8500` (the increment ends about
  `8000` after `tinc`); only `G_nonneg` was used about `G`, so all layout facts are unchanged.
  Second finding: the constant box footprints of the register runs contain other module pieces
  (`RF_J`, the INC gate, possibly stations): the footprints are being refined to unions of
  diagonal-and-axis boxes.
* 2026-11-16: refined regions of the runs (`RunRegion.lean`, `Gen/*RunG.lean`, `Gen/Dz2jAllG.lean`,
  generator `scripts/life_cert/emit_rung.py`): each run (`bodyIncRun_restG`, `dz2eOpG`,
  `dz2dOpG`, …, `dz2jAllG`) is a reaction inside `<p>Region = unionL <p>RegL`, a list of components
  `BU` (box ∩ diagonal box; e.g. 46 for `dz2e`) and `regLanes`; `<p>Region_far` reduces
  separation from a piece to one linear check per component (`BU.farApart_box`,
  `regLanes_farApart_box`). Checked numerically: `RF_J` and the INC gate are far from every
  component of `dz2e`.
* 2026-11-16: probe of the run regions against all module pieces (stations, DEC chain, eaters,
  `j < 40`, `D ≤ 40`): `dz2e*` and `dz2j` are far from every piece; the `decJz` runs are not —
  `dz2mk0` carries the Z answer past all Z stations to the line-end eater (its 27540 generations
  are the long Z restore), and `dz2d*` / `dz2mk1` reach the NZ end eater when `D = 1`. In the
  machine the answer is handed to the stations while the circuit finishes. Tool:
  `Reaction.split` (`RunSplit.lean`): a far-apart flight is split off a joint run, leaving the
  circuit's own reaction. Needed next for `decJz`: emitted footprints of the answer flight and of
  the rest from a cut segment on.
* 2026-11-16: the `decJz` runs with the answer split off (`Gen/*Split.lean`, generator
  `scripts/life_cert/emit_split.py`, tools `FootInT`, `Reaction.seqT`, `Reaction.split`):
  `dz2dOpS` … `dz2d3OpS`, `dz2mk1Run_restS` (cut at 9503, the NZ answer `…A122/A150` flies alone
  for the last 1987 generations), `dz2mk0Run_restS` (cut at 11995, the Z answer flies alone for
  15545 generations of the Z restore): the run up to the cut inside `<p>Region`, then the circuit
  alone inside `<p>RestRegion` (components far from the answer's moving box `<p>AnsF`), ending
  exactly at the circuit at rest (and the register diagonal); `<p>AnsS` the answer's flight.
* 2026-11-16: **`inc_step_of_plan`** (`ActivationIncStep.lean` with `…Compose`, `…Reg`, `…Thread`,
  `…ModuleRun`; sub-agent, checked here): one `inc` instruction of any well-formed program is
  simulated (`conway.evolve τ (encM p s) = encM p s'`, `InvM p s'`, footprints in `machRegion`),
  for every register value (diagonal increment `dz2e*OpG` for `w ≥ 16`, static `dz2jAllG` below),
  conditional on three explicit structures: `IncPlan.Valid` (layout arithmetic of the three
  routes: lines, timing, arrival offsets, `late`, piece membership), `IncSep` (separation) and
  `IncRegion` (footprints in the region). The register needs `RegS.Ready` (`Inv`, `Vb = 18`,
  `QBeforeL 29`), returned for the new state — to be folded into `InvM`. Numerically the continue
  arrives ≥ 810 generations after the increment ends (with the `+8500` margin).
* 2026-11-16: static zero-test runs for values 2–7 (`Gen/Dz2mk2…7Run`, planned with
  `DZ2_MOD=1 DZ2_K=k`, 46 segments, 11490 generations, answer at `ofRows 603 994 [1, 6, 3]` like
  `dz2dOp`), their regions and splits (`dz2mkkRun_restG`, `dz2mkkRun_restS`, cut at 9503).
* 2026-11-16: **`inc_step`** (`ActivationIncPlan.lean`, sub-agent, checked here): the plan of an
  `inc` instruction is built from `incSpecs` / `mergeSpecs` (`incPlan`) and `incPlan_valid` proves
  all of `IncPlan.Valid` for every well-formed program; `inc_step` is conditional only on
  `IncSep` and `IncRegion` (and `RegS.Ready` of the register). Note: `late` holds with a margin of
  about 6400 more than needed (`Tend ≥ Tg + 14396`).
* 2026-11-16: **halt** (`ActivationHalt.lean`, sub-agent, checked here): `halt_everAlive`
  (`InvM`, `step = none` ⇒ the corrected halt cell `haltCellC` is ever alive), conditional on
  `HaltSep` (separation only; lines, times, reflector membership proved). Findings: (1) the old
  `haltCell` is never alive (`haltCell_not_hit`: the halt glider has `x + y ∈ [V_T+2, V_T+5]`);
  `haltCellC` keeps `u = uMin − 600` (outside the region) and is hit at `haltTime`.
  (2) **`RouteSep` / `RouteSepM` are unsatisfiable** as stated: the flight clause up to `meetT`
  includes the corner's own reflector, and one generation before the meeting the boxes touch
  (`not_far_before_meet`); so `inc_step`'s `IncSep` must be reformulated with an extended relay
  window (flight far from all pieces until `meetT − 20`, a 60-generation reaction of reflector and
  glider in an extended relay box — `rf3_early`, `reflect_early` for image 3 — then the outgoing
  flight from `meetT + 40`). (3) A program with several `halt`s: the halt corner of an earlier
  halt lies on the path of a later halt glider; normalize programs to a single `halt`.
* 2026-11-16: single halt (`CounterMachineSingleHalt.lean`, sub-agent, checked here):
  `exists_program_halts_not_computable_single` (a well-formed program with a single `halt`, the
  last instruction, whose halting from `Cfg.init n` is not computable); normalization
  `Program.singleHalt` (every earlier `halt` becomes `decJz freshReg (length − 1)` on a fresh,
  always-zero register; `halts_init_singleHalt`). The corollary will use this program, so
  `HaltSep` is needed only for the unique halt.
* 2026-11-16: **decJz building blocks** (`ActivationDec{Links,Timed,Module,Run,Station,Answers}`,
  `Gen/ActSideDec`, sub-agent, checked here), for every program: the dec body, routes of KNZ, KZ
  and C (lines, route law, closed-form final lines, tokens ending exactly on the station token
  lines), C at its DEC copy at offset `4 + 2σ` (offset 8 needed a new side certificate `orSide10`),
  the DEC chain and C' to the run input at `decShift − 300 ≡ 0 (mod 30)`, every run's answer at its
  cut on the module's answer lines (`runAnsNZ_eq`, `runAnsZ_eq`), passes and captures at the
  stations (`stationNZ_capture`, `stationZ_capture`: the dispatched answers are exactly `decSpecs`'
  answer routes), unpaired tokens, answer routes (lines, closed forms, offsets 4/5), and lateness
  of the next control (`decNZ_late`, `decZ_late`). Open: separation, `RouteTimed` of the answer
  routes, packaging of two free flights, the composition `decJz_step`.
* 2026-11-16: `ActivationIncRegion` (sub-agent, checked here): `IncPlan.region` and
  **`inc_step'`** — `IncRegion` is discharged (anchors `uMin_le_mod/chain/body/corner`, glider
  boxes between corners, run regions `u ≥ −738` in the module frame; every footprint at least 163
  inside the region); `inc_step'` is conditional only on `IncSep` (to be reformulated with the
  extended relay window).
* 2026-11-16: **the final assembly** (`StartFamily.lean`, `MainTheorem.lean`, sub-agent; root import
  pending the relay refactor): `exists_startFamily` (a computable window family with cells
  `encM p (startM n)`), `MInv`, `simulatorOf` (`Simulator p` from `MachineSteps p`),
  `not_computablePred_everAlive_of_machineSteps`, and **`exists_not_computablePred_everAlive`**:
  `(∀ p, p.WellFormed → p.SingleHalt → MachineSteps p) → ∃ c, ¬ ComputablePred fun w :
  WindowData => EverAlive c w.cells`. Remaining: the fields of `MachineSteps` — inc separation
  (`IncSep`; `IncRegion` is already dischargeable), the decJz step, `HaltSep` for the last
  instruction.
* 2026-11-16: **route separation corrected** (sub-agent, checked here): extended relay window at
  every corner — `Gen/RfEarly.lean` (generator `scripts/life_cert/rf_early.py`: 60-generation
  joint runs of each of the 8 reflector images with the glider, footprint `rfBoxE k ⊆ rxBox k`),
  `reflect_earlyX`, `RouteTimedX`, `routeEndX`, `routeFootX`, `route_window_footX`, and the
  satisfiable condition `RouteSepX` (from `RouteSep.lean`, the separation agent's definition: flight
  far from all pieces before `meetT − 20` and from `meetT + 40`). `IncSep.sepC/sepR/sepM` now use
  `RouteSepX`; `inc_step_of_plan`, `inc_step`, `inc_step'` also give `0 < τ` and the other
  registers unchanged; `MachineSteps.incSep` is `IncSep` only. Numerically the incoming glider
  first touches its reflector at `meetT − 12` / `− 10`, the outgoing last at `meetT + 30 / 32`.
  Open: `mergeLink_sep` starts at `T1 + 3` (gap of 3 generations to `sepM`); `entR` may fail for
  the merge unit at entry copy 0 (crude entry footprint vs the slab corner's reflector).
* 2026-11-16: **route separation for every link** (`RouteSep.lean` … `RouteSep7.lean`, sub-agent,
  checked here), in the satisfiable `RouteSepX` form, for every well-formed program and every delay
  `d ≡ 0 (mod 30)`: `incLinks_sep` (continue and INC link), `mergeLink_sep'` (from `T1`),
  `decLinks_sep` (KNZ, C, KZ; NZ and Z answers past their stations), `haltLink_sep`, `relay_ok`
  (every corner's extended relay box far from all other pieces), `corner_gap61`, column ownership
  (R-31 #13, the segment-vs-piece check). **Real defect found**: `IncSep.entR` is false for the
  first `inc` on a register (merge unit, entry copy 0): the crude entry footprint `Box 0 90 (-6) 60`
  overlaps the slab corner's reflector (x 0..7, y 54..60); a tighter certified footprint of the
  side reaction of copy 0 is needed. Open: register strips (#14–#17), the other `IncSep` fields.
* 2026-11-16: **entry footprint fixed** (sub-agent, checked here): the OR gate relays go into
  `Box 0 90 (-6) 38` until generation 166 / 46, then only the gate and its output glider in
  `Box 49 73 36 60` (`Gen/OrTight.lean` from `scripts/life_cert/or_tight.py`, `OrChainTight.lean`:
  `orFoot`, `orChainSideT` …); `entryFoot` now uses `orFoot`, and `incPlan_entC`, `incPlan_entR`
  (`ActivationIncEntrySep.lean`) hold for every program. Open: the DEC chain still uses the crude
  footprint; `IncSep.idle`.
* 2026-11-16: **register lanes** (`LaneSep.lean`, `LaneSep2.lean`, `LaneSep3.lean`, sub-agent,
  checked here): every register's lanes are far from every piece (`machBoxes_far`; the 28 groups of
  the register circuit — group 0 reaches `v ≤ 260`, not 218 as R-31 says, still clear), from every
  other register's lanes (`modLanes_far`), from every route and extended relay box
  (`lane_instrRoute`, `lane_mergeRoute`, `lane_relay_clear`), and the lane fields of `IncSep`
  (`incPlan_laneSep`) and `HaltSep` (`haltLanes`, `haltLaneMach`) are proved.
* 2026-11-16: name clashes between RouteSep* and ActivationDec* fixed (`_rs` suffixes); the whole
  library builds (3549 jobs); axiom audit: 99 622 declarations, only the standard axioms.
* 2026-11-16: **`hsep_haltSep`** (`HaltSepProof.lean`, sub-agent, checked here): `HaltSep p
  (p.length − 1)` for every well-formed single-halt program (the halt route is `haltLink_sep`
  with delay `−1080`; the outgoing glider is far in `v` from everything; the obstruction by other
  halt corners is excluded by `SingleHalt`). The `haltSep` field of `MachineSteps` is discharged.
* 2026-11-16: **`IncSep` is false for every plan** (`ActivationIncSepFalse.lean`, sub-agent,
  checked here: `isep_not_incSep`, `isep_not_all_machineSteps` — the hypothesis of the corollary is
  currently false, witnessed by `[inc 0, halt]`). Same defect as the corners, now at the OR-gate
  side inputs (`flyC`, `flyR`, `flyM`: the glider touches its gate in the last 10–11 generations
  before the side input) and at RF_J (`fl1`: generations 881–890, `fl2`: 921–923). Fix in
  progress: RF_J as a corner with the extended window (`reflect_earlyX`), and a joint certificate
  of each OR gate with its incoming side glider over the last 20 generations. True fields proved
  (`ActivationIncSepProof.lean`): `isep_sepC`, `isep_sepR`, `isep_sepM`. **Lesson**: every
  "far until it meets" clause must stop ≥ 20 generations before the interaction.
* 2026-11-16: **`DecSep` is false for every decJz** (`DecSepFalse.lean`: `dsep_not_decSep`; sub-agent
  with a numerical checker of every field). Causes: (1) before the cut the footprint was the region of
  the whole run (incl. the answer's whole flight) — fixes `zQZ`, `zLane`, `nIdle` (D = 1); now
  `Gen/*PreG.lean` (generator `scripts/life_cert/emit_preg.py`): each split run up to its cut, inside
  `<p>PreRegion` (probe: clear of the NZ end eater and the INC gate); (2) `zIdle`: a glider of the
  `dz2mk0` rest passes the empty corner of the INC gate's box (≥ 12 cells from its cells) — needs the
  gate's exact footprint (gate in the active group); (3) `sepAN/sepAZ`: the dispatched answer stays
  within reach of its station for ~96 generations after dispatch — capture windows to grow by ≥ 100.
  Proved fields: `dsep_sepC/N/Z`, `dsep_grpLane`, `dsep_lanes`, `dsep_laneBody`.
