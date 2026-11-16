# N-23: Life computes every partial recursive function

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-23` |
| Title | The output decoding and the uniform computation theorem (`T2` of `N-12`) |
| Kind | formalization |
| Addresses | `G-7`; target `T2` of `N-12` |
| Depends on | `N-12`, `N-14`, `N-21`, `N-22`; Lean: `simulatorOf`, `MachineSteps`, `exists_goodStep`, `halt_reaction`, `HaltSep`, `hsep_haltSep`, `dsep_rest`, `machineSteps_of_decSepRest`, `diag_end`, `regStrip_subset`, `regsOn_reaction`, `window`, `pieces_region`, `modLanes_region`, `exists_startFamily`, `exists_computes_of_partrec`, `halts_singleHalt_iff` |
| Dependency requirement | all compiled |
| Produces | `life_universal`, `life_universal'`, `life_computes_of_computes`, `life_computes_single`, `readOut`, `DecodeComputable`, `Program.Computes.singleHalt` |
| Difficulty | moderate: no new certificates; the new mathematics is the behaviour of the machine for ever after the halt |
| Status | verified |
| Implementation status | complete |
| Implementation evidence | `LeanTheory/Theory/Computability/CounterMachineSingleHaltComputes.lean`, `LeanTheory/Theory/Life/ComputationDecode.lean`, `LeanTheory/Theory/Life/ComputationRun.lean`, `LeanTheory/Theory/Life/Computation.lean` |
| Lean evidence | `LeanTheory.Life.life_universal` (axioms `propext`, `Classical.choice`, `Quot.sound`) |
| Audit evidence | not audited; library axiom audit (`scripts/check_axioms.lean`) passes, 133 320 declarations |
| Last updated | 2026-11-16: created; everything compiled |

## Purpose and scope

`N-21` proved the undecidability half of "Life is Turing complete" (`T3`). This note proves the
computation half, `T2` of `N-12`, including the output decoding that `N-12` deferred: Life computes
every partial recursive function, with a computable input encoding and a computable output
decoding, both fixed once and for all (one universal machine).

Conventions: `Cell = ℤ × ℤ`, `conway` is B3/S23 on finite configurations (`Kernel/Life.lean`),
`EverAlive c S := ∃ t, c ∈ conway.evolve t S`, `WindowData = ℤ × ℤ × List ℕ` with
`WindowData.cells (x, y, rows) = ofRows x y rows` (bit `j` of row `i` is the cell
`(x + j, y + i)`).

## Exact statements

```lean
/-- Computable decoding: some computable function of window data agrees with `decode` on the
cells of every window (every finite set of cells is `w.cells` for some `w`). -/
def DecodeComputable (decode : Finset Cell → ℕ) : Prop :=
  ∃ g : WindowData → ℕ, Computable g ∧ ∀ w, g w = decode w.cells

/-- The first live cell of the ray `(x₀ + k, y₀ + k)`, or `0`. -/
def readOut (x₀ y₀ : ℤ) (S : Finset Cell) : ℕ :=
  if h : (rayHits x₀ y₀ S).Nonempty then (rayHits x₀ y₀ S).min' h else 0

theorem life_universal :
    ∃ (c : Cell) (f : Nat.Partrec.Code → ℕ → WindowData) (decode : Finset Cell → ℕ),
      Computable₂ f ∧ DecodeComputable decode ∧
      ∀ code n, ((code.eval n).Dom ↔ EverAlive c (f code n).cells) ∧
        ∀ m ∈ code.eval n, ∃ T, ∀ t ≥ T, decode (conway.evolve t (f code n).cells) = m

theorem life_universal' :
    ∃ (c : Cell) (x₀ y₀ : ℤ) (f : Nat.Partrec.Code → ℕ → WindowData),
      Computable₂ f ∧
      ∀ code n, ((code.eval n).Dom ↔ EverAlive c (f code n).cells) ∧
        ∀ m ∈ code.eval n, ∃ T, ∀ t ≥ T, readOut x₀ y₀ (conway.evolve t (f code n).cells) = m

theorem life_computes_of_computes {P : Program} (hp : P.WellFormed) {f : ℕ →. ℕ}
    (h : P.Computes f) :
    ∃ (c : Cell) (F : ℕ → WindowData) (decode : Finset Cell → ℕ),
      Computable F ∧ DecodeComputable decode ∧
      ∀ n, ((f n).Dom ↔ EverAlive c (F n).cells) ∧
        ∀ m ∈ f n, ∃ T, ∀ t ≥ T, decode (conway.evolve t (F n).cells) = m
```

(`rayHits x₀ y₀ S` is the set of `k` with `(x₀ + k, y₀ + k) ∈ S`, as a `Finset ℕ`.)

## Dependencies

All compiled: the simulator of every well-formed single-halt program (`N-22`), the halt activation
(`halt_reaction`, `hsep_haltSep`), the register diagonal (`diag_end`), the lanes (`LaneSep*`), the
start family (`exists_startFamily`), the universality of counter machines (`N-14`).

## Theory development

1. **`singleHalt` keeps outputs** (`CounterMachineSingleHaltComputes.lean`).
   `exists_eval_singleHalt`, `eval_singleHalt_regs`: from a configuration whose fresh register is
   zero, the final registers of `P.singleHalt` are those of `P` (an earlier `halt` becomes
   `decJz fresh last`, which changes no register). `Program.Computes.singleHalt`.
2. **Along the run** (`ComputationRun.lean`, `exists_evolve_of_reaches`): if the counter machine
   goes from `s.cfg` to `cf` and `MInv p s`, some generation of `encM p s` is `encM p s'` with
   `MInv p s'` and `s'.cfg = cf` (head induction on `Reaches`, with `exists_goodStep`).
3. **After the halt** (`evolve_late`). From a halted state, `halt_reaction` gives the
   configuration at `haltTime`; from then on, for every `n`, the configuration at `haltTime + n`
   is `lateConf`: the idle machine (`window`), the halt glider on its `SW` world line
   (`WL.flight`) and the registers' diagonals (`regsOn_reaction`), composed by `Reaction.par`.
   The separation of the glider for *all* later times is by `u = x - y`: the glider's box has
   `u ≤ u_min - 590` from `haltTime` on (`haltOut_box_u`; its `u` decreases along the world line,
   and at `haltTime` it covers `haltCellC`, at `u = u_min - 600`), while every piece box and every
   register lane lies in `u ≥ u_min - 300` (`pieces_region`, `modLanes_region`). This replaces
   the "monotone distance" argument suggested in the plan; no new certificate was needed. The
   lanes are separated from each other and from the machine by `HaltSep.lanes`,
   `HaltSep.laneMach` (at `j = 0`).
4. **Register `0` at rest** (`regAt_zero_late`): after `diagTime` every salvo has arrived
   (`diag_end`), and register `0` is `ofRows (blockX p + v) (blockY p + v) [3, 3]`, `v` its value.
5. **The ray** (`late_ray`): the cells `(blockX p + k, blockY p + k)` all lie in the lanes of
   register `0` (`ray_mem_modLanes`: in the module frame `u = -96`, `v = 406 + 2k ≥ 354`). The lanes
   of register `0` meet neither the machine boxes, nor the halt glider, nor the lanes of the other
   registers; so from `haltTime + diagTime` on, the live cells of the ray are exactly `k = v` and
   `k = v + 1` (`mem_block_ray`), and `readOut (blockX p) (blockY p)` is `v` (`readOut_late`).
6. **Decoding and its computability** (`ComputationDecode.lean`). `readOut` is defined on finite
   sets. On window data it is computed by `readRows`: a bounded search (`List.findIdx` over
   `List.range (rayBound y₀ w)`) of the first `k` whose cell has its bit set, with all integer
   offsets written through `Int.toNat` and `(-·).toNat`; `readRows_eq` proves agreement,
   `primrec_readRows` primitive recursiveness (with `primrec_int_toNat`,
   `primrec_int_neg_toNat` from the `Denumerable ℤ` encoding, which Mathlib does not provide).
   There is no `Primcodable (Finset (ℤ × ℤ))` in Mathlib, hence the `DecodeComputable` form.
7. **Assembly** (`Computation.lean`). `life_computes_single` (one single-halt program: the
   simulator's `everAlive_of_halts` / `not_everAlive_of_not_halts` for the domain, 2–5 for the
   value), `life_computes_of_computes` (through `singleHalt`), and the uniform form with the
   universal program `U` computing `k ↦ eval (ofNat k.unpair.1) k.unpair.2`
   (`nat_partrec_universal`, `exists_computes_of_partrec`), normalized by `singleHalt`:
   `f code n := F (Nat.pair (encode code) n)` with `F` the start family of `U.singleHalt`; `c` its
   halt cell `haltCellC`; `decode = readOut (blockX U') (blockY U')`.

**Deviation from the first draft in `N-12`.** `N-12` proposed to decode "the configuration at the
first generation at which `c` is alive". That is not what is proved: when the halt glider reaches
`c`, salvos may still be in flight towards register `0`. The decoding is instead correct at every
generation from some `T` on (the output is eventually stable), which is the form requested for
this note.

## Claims and evidence

* `life_universal`, `life_universal'`, `life_computes_of_computes`, `life_computes_single`:
  compiled Lean theorems, no hypotheses beyond those displayed; `#print axioms life_universal`:
  `propext, Classical.choice, Quot.sound`.
* `Program.Computes.singleHalt`, `Program.eval_singleHalt_regs`: compiled.
* `exists_evolve_of_reaches`, `evolve_late`, `regAt_zero_late`, `late_ray`, `readOut_late`:
  compiled.
* `readOut_computable`, `readRows_eq`, `primrec_readRows`: compiled. Sanity: `readOut_block_five`,
  `readOut_empty`.

## Difficulty, barriers and readiness

Done. Remaining, optional refinements:

* `T` is not given as a computable function of the run; one could state it explicitly
  (`haltTime + diagTime` after the last machine step).
* The decoding reads the ray at any late generation; a decoding at a *recognizable* generation
  (e.g. the first one at which `c` is alive, plus a fixed delay) would need a bound on `diagTime`
  at the halt in terms of the configuration; not needed for the target.
* A `Primcodable` structure on `Finset Cell` (sorted lists) would let one state `Computable decode`
  directly; `DecodeComputable` is equivalent for all practical purposes since `exists_ofRows`
  gives every finite set as a window.

## Outputs and next dependencies

Goal `G-7` is complete in both halves: undecidability (`exists_not_computablePred_everAlive'`,
`N-21`) and computation of every partial recursive function with computable encoding and
decoding (`life_universal`). Root import: `LeanTheory.Theory.Life.Computation` in
`LeanTheory.lean`.
