# N-21: The final reduction: halting of one program as "a cell is ever alive"

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-21` |
| Title | Final reduction to the undecidability of `EverAlive` |
| Kind | formalization plan |
| Addresses | `G-7` |
| Depends on | `N-19`, `N-20`, `N-12`; Lean: `exists_program_halts_not_computable`, `not_computablePred_everAlive_of_family`, the component and diagonal theorems |
| Dependency requirement | a simulation theorem for every well-formed program |
| Produces | the top-level statement and its proof plan |
| Difficulty | hard (assembly at scale) |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-15: created |

## Observation: one program suffices

`exists_program_halts_not_computable` gives **one** well-formed program `P` (not explicit) whose
halting on the input `n` is undecidable. So the family of configurations is
`f n = Mach P ∪ block₀ n`: the machine of `P` (a fixed finite set) and the block of register `0` at
position `n`. For fixed `P` the map `n ↦ f n` (as `WindowData`) is computable without any work on
the layout function (it is a fixed window with one block moved by `n`). The simulation must still
hold for an arbitrary well-formed `P`, since `P` is not explicit.

## Target statements

* `Mach P : Finset Cell`: all pieces of the layout `LP` of `R-31` (units, modules, route
  reflectors, eaters) at phase `0`, and the control glider at the entrance of instruction `0`.
* `sim_halts`: `P.Halts (Cfg.init n) → EverAlive cH (Mach P ∪ block₀ n)`.
* `sim_never`: `¬ P.Halts (Cfg.init n) → ¬ EverAlive cH (Mach P ∪ block₀ n)`.
* Then `¬ ComputablePred (EverAlive cH)` for finite configurations by
  `not_computablePred_everAlive_of_family`.

## Proof plan

1. **Encoding** at step boundaries: the machine at phase `φ`, the control glider at the entrance of
   the unit of `pc`, and each register as its isolated diagonal (`N-20`: `evolve t (flights q ∪
   counter K)`, value `K + qMove q`).
2. **Step lemma** for each instruction (`inc`; `decJz` with value `0`, value `1`, value `≥ 2`):
   the encoding of `c` evolves into the encoding of `step c`, the footprint inside the machine
   region, which excludes the halt cell. Value `0` and `1`: the queue is empty by the time of the
   detector (timing of `LP`) and the concrete runs apply (`dz2mk0Run_rest`, `dz2mk1Run_rest`);
   value `≥ 2`: a generic run with the diagonal as a process (`diag_add`, `diag_near`, `diag_strip`).
3. **Halt lemma**: the halt unit sends a glider through the halt cell.
4. **Induction** over the run: `sim_halts` from the reachable halting configuration; `sim_never` from
   the invariant "every generation lies in the machine region" over all steps (each step finite,
   the run infinite).
