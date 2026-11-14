# N-01: Kernel — finite configurations and the Life step

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-01` |
| Title | Kernel: finite configurations, the rule B3/S23, `step` and `evolve`, with the sanity suite |
| Kind | definition / formalization |
| Addresses | `G-1`; `Q-1`, `Q-2` |
| Depends on | Mathlib only (`Finset`, `ℤ × ℤ`) |
| Dependency requirement | none beyond the pinned Mathlib |
| Produces | `LeanTheory/Kernel/Life.lean`, `LeanTheory/Sanity/Life.lean`; decisions for `Q-1`, `Q-2`; contract entries in `notes/formalization/00-model-contracts.md` |
| Difficulty | routine to moderate: the definitions are short; the care is in choosing a representation that later notes can compute with, and in an independent characterization |
| Status | verified (compiled, axiom audit passed, strict kernel audit recorded in `implementation-plan.md` §4) |
| Implementation status | complete |
| Implementation evidence | `LeanTheory/Kernel/Life.lean`, `LeanTheory/Sanity/Life.lean`, commit `0ae423d` |
| Lean evidence | namespace `LeanTheory.Life`. Kernel: `Cell`, `nbrs`, `liveNbrs`, `Rule`, `conway`, `Rule.step`, `Rule.evolve`, `liveNbrsSet`, `stepSetCore`, `Rule.stepSet`, `mem_nbrs`, `notMem_nbrs_self`, `mem_nbrs_comm`, `liveNbrs_ne_zero`, `Rule.mem_step`, `Rule.evolve_zero`, `Rule.evolve_succ`, `Rule.evolve_succ'`, `Rule.evolve_one`, `Rule.evolve_add`. Sanity: see the table under "Claims and evidence" |
| Audit evidence | audited at commit `0ae423d` on 2026-11-14; no open findings |
| Last updated | 2026-11-14: implemented and audited |

## Purpose and scope

Fix the mathematical model that every other note refers to: an infinite grid `ℤ × ℤ`, a
configuration with **finitely many live cells** (user constraint `A-2`), and Conway's rule
(`A-1`). The kernel is a set of definitions; there is no empirical law, so there is no law
typeclass. The role played by "law instances" in the template is played here by an independent
specification on arbitrary sets, against which the computable definition is checked.

Out of scope: efficient simulation (`N-03`), serialization (`N-02`), named patterns (`N-05`–`N-07`).

## Dependencies

None unverified. Mathlib `Finset` API is compiled.

## Sources and prior work

- `S-07` §3.1: `adj`, `live_adj`, `step` on `Set (ℤ × ℤ)`, proved in HOL4 (not Lean evidence).
- `S-18`: a Lean tutorial that models Life on a finite torus; not suitable, since a torus changes
  the dynamics of anything that reaches the boundary.

## Theory development

Proposed interface (names provisional):

```lean
abbrev Cell := ℤ × ℤ
def nbrs (c : Cell) : Finset Cell            -- the 8 Moore neighbours
def liveNbrs (S : Finset Cell) (c : Cell) : ℕ := (nbrs c ∩ S).card
def step (S : Finset Cell) : Finset Cell :=
  (S ∪ S.biUnion nbrs).filter fun c =>
    if c ∈ S then liveNbrs S c = 2 ∨ liveNbrs S c = 3 else liveNbrs S c = 3
def evolve (n : ℕ) (S : Finset Cell) : Finset Cell := step^[n] S
-- independent specification on arbitrary sets (the HOL4 definition)
def stepSet (S : Set Cell) : Set Cell
```

**Decided (user, 2026-11-14):** `Q-1` — `Finset (ℤ × ℤ)`, `x` to the right and `y` downward as
in RLE; `Q-2` — option (b), a generic `Rule` with `conway` as the instance used everywhere. A
consequence to handle in the design: a rule with `0` in its birth set would create infinitely
many cells, so `Rule` must exclude it (a field or a hypothesis) and a sanity theorem should show
the exclusion is necessary. The options considered were:

- **`Q-1` representation and coordinates.** Proposal: `Finset (ℤ × ℤ)` as the specification
  type, coordinates `(x, y)` with `y` increasing **downward**, matching RLE and Golly so that
  imported patterns need no flip. Alternative: mathematical orientation (`y` up) with a flip in
  the importer. The choice changes the stated direction of every spaceship theorem, so it must be
  fixed once and recorded in the model contracts.
- **`Q-2` rule-generic kernel.** Option (a): only B3/S23. Option (b): a `Rule` structure
  (birth and survival sets `⊆ {0,…,8}`) with `conway : Rule` as the instance used everywhere.
  (b) costs little and lets `N-17` check a replicator definition against a rule that has a small
  replicator, and lets metacell statements mention the simulated rule; (a) keeps the kernel
  minimal. Provisional preference: (b) with all theorems stated for `conway`, unless the user
  prefers the minimal kernel.

Sanity suite (kernel audit requirements; each is a theorem to compile in `Sanity/Life.lean`):

1. *Independent characterization*: `(step S : Set Cell) = stepSet ↑S`, and the pointwise rule
   `c ∈ step S ↔ (c ∈ S ∧ liveNbrs S c ∈ {2,3}) ∨ (c ∉ S ∧ liveNbrs S c = 3)`.
2. *Degenerate cases*: `step ∅ = ∅`; a single cell dies; a domino dies.
3. *Concrete instances*: the block is fixed; the blinker has period exactly 2.
4. *Counterexamples to overbroad claims* (adversarial): `step` is not monotone
   (`S ⊆ T` does not give `step S ⊆ step T`); not injective (`∅` and a single cell have the same
   successor); not additive on adjacent patterns (two patterns whose union evolves differently
   from the union of their evolutions), which shows the separation hypothesis of `N-04` is needed.
5. *Symmetry*: `step` commutes with translations and with the 8 symmetries of the square.
6. *Speed of light*: `step S ⊆ S ∪ S.biUnion nbrs`, hence the bounding box grows by at most one
   cell per generation in each direction. This is also the formal content of "finitely many cells
   at each time".
7. *Neighbour count range*: `liveNbrs S c ≤ 8`; `c ∉ nbrs c`.

## Claims and evidence

Compiled Lean theorems (all in `LeanTheory.Life`, standard axioms only):

| Sanity item | Declarations |
| --- | --- |
| 1. Independent characterization | `Rule.mem_step` (cell-by-cell rule), `Rule.coe_step` (`↑(R.step S) = R.stepSet ↑S`), `liveNbrsSet_coe` |
| Specification itself | `liveNbrsSet_le_eight`, `conway_stepSet_univ` (the full plane dies) |
| Side condition of `Rule` is necessary | `stepSetCore_birth_zero_empty`, `not_finite_stepSetCore_birth_zero` |
| 2. Degenerate cases | `Rule.step_empty`, `Rule.evolve_empty`, `conway_step_eq_empty_of_card_lt_three`, `conway_step_singleton` |
| 3. Concrete instances | `conway_step_block`, `conway_step_blinkerH`, `conway_step_blinkerV`, `blinkerH_ne_blinkerV`, `conway_evolve_two_blinkerH` |
| 4. Counterexamples | `not_monotone_conway_step`, `not_injective_conway_step`, `not_additive_conway_step` |
| 5. Symmetry | `Rule.step_map` (any neighbour-preserving bijection), `Rule.step_translate`, `Rule.step_transpose`, `Rule.step_reflectX`, `conway_step_blinkerV_of_symmetry` |
| 6. Speed of light | `Rule.step_subset`, `Rule.exists_near_of_mem_step`, `Rule.exists_near_of_mem_evolve` |
| 7. Neighbourhood | `mem_nbrs_iff_max`, `nbrs_eq`, `card_nbrs`, `liveNbrs_le_eight`, `liveNbrs_le_card_erase`, `liveNbrs_eq`, `notMem_nbrs_self` |

Scope: these theorems concern the definitions only. Symmetry is proved for one step and for the
generators (translations, transposition, one reflection); the statements for `evolve` and for
the full symmetry group as a group action are left to `N-04`. Finite support is built into the
type; `Rule.exists_near_of_mem_evolve` is its quantitative form.

Design points settled during implementation:

- `Rule` carries the field `zero_notMem_birth`; without it the finite step would silently
  disagree with the specification (shown by `not_finite_stepSetCore_birth_zero`).
- Counts above eight in `birth` or `survive` are harmless but make two different `Rule` values
  define the same dynamics; `Rule` equality is therefore not equality of dynamics.
- Concrete steps of small patterns are proved by bounding the support with the speed of light,
  `interval_cases` on the coordinates and `simp` with `liveNbrs_eq`. This is adequate for
  patterns of a few cells only; anything larger needs `N-03`.

## Difficulty, barriers and readiness

No mathematical barrier. Risks: (i) a definition that is awkward for kernel computation — this
is mitigated by keeping `step` as the specification and proving refinement of a fast
implementation in `N-03`; (ii) an orientation convention that later conflicts with pattern
sources. The note can generate Lean as soon as `Q-1` and `Q-2` are decided; both can be decided
by the agent with the stated defaults, or by the user.

## Outputs and next dependencies

Unblocks `N-02`, `N-03`, `N-04` directly and everything else transitively. After implementation
the strict audit must be re-run on the new kernel (every declaration, triad and adversarial
checks) before any dependent note is marked verified.
