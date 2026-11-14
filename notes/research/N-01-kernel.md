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
| Status | lean-ready (`Q-1`, `Q-2` decided by the user on 2026-11-14) |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded; conventions decided |

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

| Claim | Status |
| --- | --- |
| The definitions above express Conway's rule | definition; to be checked by items 1–7 |
| Items 1–7 hold | conjecture with routine expected proofs; none compiled |
| Finite support is preserved by `step` | immediate from the type once `step` is defined; item 6 gives the quantitative form |

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
