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
| Status | verified |
| Implementation status | complete |
| Implementation evidence | `LeanTheory/Theory/Life/Locality.lean` (written by a sub-agent, checked and integrated by the coordinator), commit `584f5bb` |
| Lean evidence | `translate`, `Near`, `nbhd`, `AgreeOn`, `Sep`; `Rule.mem_step_congr`, `Rule.mem_evolve_congr`, `Rule.agreeOn_evolve`, `Rule.coe_evolve_subset_nbhd`, `Rule.step_union_of_sep`, `Rule.evolve_union_of_forall_sep`, `Rule.evolve_union_of_sep`, `Rule.evolve_union_of_sep_of_step_eq`, `Rule.evolve_map`, `Rule.evolve_translate`, `Rule.evolve_transpose`, `Rule.evolve_reflectX`, `Rule.evolve_mul_of_evolve_eq`, `Rule.evolve_mod_of_evolve_eq`, `Rule.evolve_mul_of_evolve_eq_translate`, `Rule.exists_evolve_eq_of_bounded`, `Rule.eventually_periodic_of_bounded`; adversarial `not_step_union_of_sep_one` |
| Audit evidence | build and axiom audit at `47f841c`; statements of all main theorems read against this note by the coordinator |
| Last updated | 2026-11-14: implemented |

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

## Results (2026-11-14)

All seven statements are compiled. Exact constants: `Sep r S T` means every cell of `S` is at
Chebyshev distance **greater than** `r` from every cell of `T`.

- One step: `Sep 2 S T` (distance ≥ 3) gives `step (S ∪ T) = step S ∪ step T`; sharp, by the
  compiled counterexample `not_step_union_of_sep_one` at distance 2.
- `n` steps from time 0: `Sep (2 * n) S T` (distance ≥ 2n + 1) suffices. This is better than
  the tentative "> 2n + 1" written above.
- Along a run: `∀ k < n, Sep 2 (evolve k S) (evolve k T)` suffices.
- Next to a still life `T`: `Sep (n + 1) S T` suffices for `n` steps.
- Bounded ⇒ eventually periodic, with the explicit bound `i + p ≤ 2 ^ B.card`.

## Claims and evidence

All seven statements: compiled Lean theorems (declarations in the metadata).

## Difficulty, barriers and readiness

Blocked on `N-01` only. The design question that remains open is the *interface* form of these
results for components exchanging signals (`Q-8`), which is `N-08`.

## Outputs and next dependencies

Unblocks `N-06` (orientations), `N-07` (gun for all `n`), `N-08`, `N-11`. Item 7 feeds `N-12`.
