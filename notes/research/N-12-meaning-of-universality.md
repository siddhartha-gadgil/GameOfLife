# N-12: What "Turing complete" means for Life on finite configurations

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-12` |
| Title | Target statements for universality and the undecidability corollary |
| Kind | definition / research approach |
| Addresses | `G-7`; `Q-4` |
| Depends on | Mathlib computability (`S-17`); `N-01` for the type of configurations (statement level only) |
| Dependency requirement | the names and types of `Nat.Partrec.Code.eval`, `ComputablePred`, `ComputablePred.halting_problem`; the kernel type |
| Produces | precise candidate theorem statements, a recommendation among them, the list of library gaps (e.g. `Primcodable` for configurations), an entry in the model contracts |
| Difficulty | moderate: no hard mathematics, but the statement must exclude trivial "simulations" and must be provable by the planned construction |
| Status | stated: exact Lean statements fixed below and type-checked; the reduction between them compiled |
| Implementation status | complete: T3 (`exists_not_computablePred_everAlive'`) and T2 with decoding (`life_universal`, `N-23`) |
| Implementation evidence | `LeanTheory/Theory/Life/Decision.lean` |
| Lean evidence | `WindowData`, `WindowData.cells`, `EverAlive`, `not_computablePred_everAlive_of_family` |
| Audit evidence | not audited |
| Last updated | 2026-11-16: T2 with the output decoding compiled (`N-23`) |

## Purpose and scope

"Life is a Turing machine" is not a mathematical statement (correction `C-1`). This note fixes
what will be proved. It can be worked on immediately and independently of all Life-level
constructions, and its outcome shapes `N-14`–`N-16`.

## Dependencies

Mathlib declarations exist in the pinned checkout (located by `grep`; compiled in the cache):
`ComputablePred.halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom` in
`Mathlib/Computability/Halting.lean`; `Turing.TM0`, `TM1`, `TM2`; `Turing.ToPartrec`.

## Sources and prior work

- `S-14` (Durand–Róka, snippet only): distinguishes several universality notions for Life and
  gives precise definitions; reported to derive Turing universality from intrinsic universality.
  **Must be read** before this note is finalized.
- `S-05` (`URM`): "a universal computer may be either infinite or finite"; Rendell's 2000
  machine needs an infinite tape pattern, the 2011 version does not.
- `S-07`: a self-simulation theorem on arbitrary (possibly infinite) states; explicitly leaves
  the connection with traditional computability as future work.

## Theory development

Candidate statements, from weakest to strongest:

1. **Bounded simulation** (non-uniform): for each machine, input and step bound there is a finite
   pattern simulating that many steps. Too weak: gives no undecidability. Useful only as an
   intermediate rung.
2. **Simulation of a machine model.** For every program `M` of a fixed universal model (counter
   machines, `N-14`) there are a *computable* encoding `enc_M : Cfg M → Config` and a decoding
   such that one machine step corresponds to `evolve (τ c)` of the encoding, where the duration
   `τ` may depend on the configuration, and halting corresponds to a simple observable.
3. **Undecidability corollary.** A natural predicate on finite configurations is not computable,
   by reduction from `ComputablePred.halting_problem`. Candidates: "some cell of a fixed finite
   set is eventually alive"; "the configuration eventually becomes periodic"; "the configuration
   eventually dies out". The first is the easiest to arrange (the halt signal is routed to a
   marker cell).
4. **Computation of every partial recursive function**: for each `c : Nat.Partrec.Code` and
   input `n`, a computable finite pattern which reaches a decodable output configuration iff
   `c.eval n` is defined, with the decoded value equal to it.

Conditions that prevent trivial encodings: `enc` computable (in Mathlib's sense, which needs a
`Primcodable` structure on configurations — a library gap to fill, probably through sorted
lists of cells), the halting observable decidable on a single configuration, and the pattern for
`M` on input `x` obtained from a fixed pattern for `M` by a simple input placement.

Necessary feature (from `N-04` item 7): any such construction uses unbounded space; with sliding
block memory the population nevertheless stays bounded.

**Decided (user, 2026-11-14)**, following the recommendation: prove 2 for counter machines, derive 4 through `N-14`, and state 3
as the headline corollary because it mentions no machine model at all.

## Update from the source report `R-18` (2026-11-14)

Source: [`reports/R-18-source-report.md`](reports/R-18-source-report.md), written by a sub-agent
that read the primary sources (book `S-11` ch. 9 and parts of ch. 2, 6–8, 11, 12; Chapman's
archived pages `S-10`; Hickerson's 1990 description; Durand–Róka's research report `S-14`).
Its numerical observations are simulations, not proofs.

- Durand–Róka (`S-14`, research report read in full): "pattern" means finitely many live cells.
  Their definition of Turing universality has four parts: a recursive encoding (of the
  non-periodic part of an almost-everywhere periodic configuration), a recursive halting
  predicate, one automaton step per computation step, and a recursive decoding. Finite
  configurations are the all-dead-background case. This is compatible with candidates 2–4.
- Their own derivation goes through intrinsic universality on infinite periodic configurations;
  the register-machine construction on finite patterns is a ten-line sketch.
- They report an error in Conway's argument: free-running guns produce parasitic outputs that
  can disturb registers, with no formal repair for the finite case. This favours a design
  without free-running guns.
- They reject "the dynamics becomes stable" as a general halting condition. For a gun-free
  machine "eventually periodic" does not characterize halting (a loop with bounded registers is
  also eventually periodic). The halting observable of candidate 3 should therefore be a marker
  (a halt glider reaching a fixed place), as already preferred.
- The book's chapter 9 gives compiled finite patterns for individual programs and one sentence
  claiming Turing completeness, without definition or proof. No source read contains a proof
  that counter machines are universal (only citations of Minsky 1967, §15.1).

## Exact statements (2026-11-14)

With `WindowData := ℤ × ℤ × List ℕ`, `WindowData.cells w := ofRows w.1 w.2.1 w.2.2` and
`EverAlive c S := ∃ t, c ∈ conway.evolve t S` (all compiled in `Theory/Life/Decision.lean`), the
targets of `G-7` are:

- **T3 (headline, no machine model).** For a suitable cell `c`,
  `¬ ComputablePred fun w : WindowData => EverAlive c w.cells`: it is undecidable whether a
  given cell is ever alive in the evolution of a given finite configuration.
- **T1 (family form).** `∃ f : ℕ → WindowData, Computable f ∧
  ¬ ComputablePred fun n => EverAlive c (f n).cells`.
- **T2 (computation).** `∀ code : Nat.Partrec.Code, ∃ f : ℕ → WindowData, Computable f ∧
  ∀ n, (code.eval n).Dom ↔ EverAlive c (f n).cells`, with a computable decoding of the output
  from the configuration at the first generation at which `c` is alive (the decoding clause is
  still to be written; it needs the layout of the output register).
- **Simulation (`N-15`).** For every well-formed counter program `P`: an encoding of machine
  configurations as finite configurations, allowing salvos in flight, a fixed duration `τ`
  per instruction, `conway.evolve τ` of an encoding of `c` being an encoding of the successor
  of `c`, and the marker cell dead at every generation unless the machine has halted.

Compiled: T1 ⟹ T3 (`not_computablePred_everAlive_of_family`). Plan for T1: take the program
of `exists_program_halts_not_computable` (`N-14`); `f n` is its Life pattern with input `n`
(register 0 at position `n`); the marker is hit by the halt signal. "Halts ⟹ ever alive" needs
the simulation; "ever alive ⟹ halts" needs the marker to be dead at *every* generation of a
non-halting run, which is what the footprints of the reaction calculus (`N-08`) are for.
`Computable f` is a separate, routine obligation (the rows of the pattern are a primitive
recursive function of `n`).

T2 follows from the simulation and `exists_computes_code` in the same way.

## Progress

* 2026-11-16: **T2 with the output decoding is compiled, in uniform form** (`N-23`,
  `Theory/Life/Computation.lean`): `life_universal : ∃ (c : Cell)
  (f : Nat.Partrec.Code → ℕ → WindowData) (decode : Finset Cell → ℕ), Computable₂ f ∧
  DecodeComputable decode ∧ ∀ code n, ((code.eval n).Dom ↔ EverAlive c (f code n).cells) ∧
  ∀ m ∈ code.eval n, ∃ T, ∀ t ≥ T, decode (conway.evolve t (f code n).cells) = m`. The decoding is
  the explicit `readOut x₀ y₀` (the first live cell of the ray `(x₀ + k, y₀ + k)` of register `0`
  of one fixed universal machine; `life_universal'`), computable through window data
  (`DecodeComputable`, `readRows`). It is read at every late generation, not "at the first
  generation at which `c` is alive" as first drafted above: the halt glider reaches `c` before the
  last salvos have arrived at register `0`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Claims and evidence

No claims; this note produces definitions. Whether the Mathlib notions compose as hoped is
unchecked.

## Difficulty, barriers and readiness

Ready now as a research note: read `S-14`, then draft the candidate statements against the
Mathlib declarations. Unproved statements must not enter the library (no `sorry`); draft them
in this note or in the scratchpad. The user should confirm the headline statement (`A-4`).

## Outputs and next dependencies

Feeds `N-13`, `N-14`, `N-15`, `N-16`.
