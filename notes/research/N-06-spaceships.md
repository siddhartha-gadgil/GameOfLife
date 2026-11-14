# N-06: Spaceships

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-06` |
| Title | Glider and the light-, middle- and heavy-weight spaceships |
| Kind | definition / formalization |
| Addresses | `G-4` |
| Depends on | `N-01`, `N-03`, `N-04` |
| Dependency requirement | compiled `evolve`; evolution certificates; equivariance (`N-04` item 5) and periodicity algebra (item 6) |
| Produces | `LeanTheory/Theory/Life/Patterns/Spaceships.lean`: `IsSpaceship P p v`, glider, LWSS, MWSS, HWSS in all phases and orientations |
| Difficulty | routine |
| Status | verified (items listed under Lean evidence; extensions noted below remain open) |
| Implementation status | complete for the initial list |
| Implementation evidence | `LeanTheory/Theory/Life/Patterns.lean`, commit `47f841c` |
| Lean evidence | `IsSpaceship`, `IsSpaceship.evolve_mul`, `IsSpaceship.translate`, `translate_ofRows`; `Pattern.glider_isSpaceship : IsSpaceship glider 4 (1, 1)`, `lwss_isSpaceship`, `mwss_isSpaceship`, `hwss_isSpaceship` (period 4, displacement `(-2, 0)`), `Pattern.glider_evolve_mul_four` |
| Audit evidence | build and axiom audit at `47f841c` |
| Last updated | 2026-11-14: implemented |

## Purpose and scope

User outcome: "prove the properties these have, such as … translation in k steps".

## Dependencies

All unverified until compiled.

## Sources and prior work

Glider: period 4, one cell diagonally (`S-04`; `S-07` §1.1). LWSS/MWSS/HWSS: period 4, two cells
orthogonally (`S-04`; `S-07`). The direction of travel in coordinates depends on `Q-1`.

## Theory development

- `IsSpaceship P p v : v ≠ 0 ∧ evolve p P = v +ᵥ P`, with minimal-period variant.
- Glider: the four phases, `evolve 4 glider = (1, 1) +ᵥ glider` for the chosen representative,
  then all four directions by `N-04` item 5 and `evolve (4k) glider = (k, k) +ᵥ glider` by item 6.
- A parameterized family `gliderAt (dir) (phase) (pos)` so that streams (`N-07`) and reactions
  (`N-09`) can refer to gliders uniformly, with a lemma that any two members are related by a
  symmetry and a time shift.
- Sanity: the glider is not a spaceship with a smaller period; the *isolated* hypothesis matters
  (a glider next to a block does not translate) — a small counterexample certificate.

## Results (2026-11-14)

Compiled: the glider (period exactly 4, displacement `(1, 1)`: right and down in the `y`-down
convention) and the LWSS, MWSS and HWSS (period exactly 4, displacement `(-2, 0)`), each for one
orientation and phase; exactness means that no earlier generation is a translate of the
pattern. Other orientations follow from `Rule.evolve_transpose` and `Rule.evolve_reflectX`
but are not yet stated; the parameterized family `gliderAt` is left to `N-07`. Pattern data
written from memory, validated by the theorems.

## Claims and evidence

All: sourced, uncompiled; proofs are small certificates plus general lemmas.

## Difficulty, barriers and readiness

Blocked on `N-01`, `N-03`, `N-04`. The glider × 4 theorem alone needs only `N-01` and a minimal
certificate and is a natural first end-to-end test.

## Outputs and next dependencies

Feeds `N-07`, `N-09`, `N-10`, `N-11`.
