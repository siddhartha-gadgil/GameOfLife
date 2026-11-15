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
