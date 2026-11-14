# N-04: Locality, symmetry and composition of evolutions

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-04` |
| Title | Light cones, independence of separated patterns, equivariance |
| Kind | proof / formalization |
| Addresses | `G-3`; supports `G-4`, `G-5`, `G-7` |
| Depends on | `N-01` |
| Dependency requirement | compiled `step`, `evolve`, `nbrs`; symmetry and speed-of-light sanity theorems of `N-01` (may be proved here if not there) |
| Produces | `LeanTheory/Theory/Life/Locality.lean`: the theorems listed below |
| Difficulty | moderate: elementary combinatorics; the work is choosing statements that compose well over many generations |
| Status | stated; mathematical proofs are elementary (proof sketches below) |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

General theorems that turn finite simulations into statements about patterns placed in a larger
configuration and about unbounded time: the mathematical core of every "this component works
inside the machine" argument.

## Dependencies

`N-01`, unverified until compiled.

## Sources and prior work

- `S-07` §3.2: `infl S ∩ infl S' = ∅ ⇒ step (S ∪ S') = step S ∪ step S'` (proved in HOL4). They
  note it is sufficient but not the weakest condition.

## Theory development

Target statements (Chebyshev distance `d∞` on `ℤ²`; `N_r S` the radius-`r` neighbourhood):

1. **Locality.** If `S` and `T` agree on `N_n(R)` then `evolve n S` and `evolve n T` agree on
   `R`. *Sketch*: induction on `n`; one step depends only on the radius-1 neighbourhood.
2. **Speed of light.** `evolve n S ⊆ N_n S`.
3. **Independence.** If `N_1 S ∩ N_1 T = ∅` then `step (S ∪ T) = step S ∪ step T`; if
   `d∞(S, T) > 2n + 1` (precise constant to be fixed in the proof) then
   `evolve n (S ∪ T) = evolve n S ∪ evolve n T`. *Sketch*: from 1 and 2.
4. **Independence along a run.** If for all `k < n` the evolved parts stay influence-disjoint,
   then `evolve n (S ∪ T) = evolve n S ∪ evolve n T`. This is the form needed for a glider
   travelling past a distant still life indefinitely.
5. **Equivariance.** `evolve n (g • S) = g • evolve n S` for `g` a translation or one of the 8
   symmetries of the square; hence each orientation and phase of a pattern inherits the theorems
   of one representative.
6. **Periodicity algebra.** `evolve p S = S ⇒ evolve (k·p) S = S`;
   `evolve p S = v +ᵥ S ⇒ evolve (k·p) S = (k·v) +ᵥ S`.
7. **Bounded implies eventually periodic.** If all `evolve n S` lie in a fixed finite region then
   the orbit is eventually periodic (pigeonhole). Consequence used by `N-12`: a universal
   construction with finite support must use unbounded space.

Adversarial checks: explicit pairs showing that 3 fails without the separation hypothesis (shared
with `N-01` item 4), and that the constant in the multi-step version is sharp or at least not
improvable to `n`.

## Claims and evidence

All seven statements: proof sketch, not compiled. No conjectural mathematics.

## Difficulty, barriers and readiness

Blocked on `N-01` only. The design question that remains open is the *interface* form of these
results for components exchanging signals (`Q-8`), which is `N-08`.

## Outputs and next dependencies

Unblocks `N-06` (orientations), `N-07` (gun for all `n`), `N-08`, `N-11`. Item 7 feeds `N-12`.
