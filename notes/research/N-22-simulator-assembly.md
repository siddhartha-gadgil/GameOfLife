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
  circuit for all operations (`RegisterCircuit`). Placements of the whole machine: sub-agent running.
