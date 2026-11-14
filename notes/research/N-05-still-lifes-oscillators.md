# N-05: Still lifes and oscillators

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-05` |
| Title | Catalogue of still lifes and oscillators, including the traffic light |
| Kind | definition / formalization |
| Addresses | `G-4` |
| Depends on | `N-01`, `N-03`; `N-02` for import (convenience only) |
| Dependency requirement | compiled `evolve`; a working evolution certificate tactic for small windows |
| Produces | `LeanTheory/Theory/Life/Patterns/Basic.lean`: predicates `IsStillLife`, `IsOscillator P p` (exact period), named patterns and their theorems |
| Difficulty | routine once `N-03` exists |
| Status | verified (items listed under Lean evidence; extensions noted below remain open) |
| Implementation status | complete for the initial list |
| Implementation evidence | `LeanTheory/Theory/Life/Patterns.lean`, commit `47f841c` |
| Lean evidence | `IsStillLife`, `IsOscillator`, `IsStillLife.evolve`, `IsOscillator.evolve_mod`, `IsOscillator.translate`; `Pattern.block_isStillLife`, `beehive_`, `loaf_`, `boat_`, `pond_`, `eater1_isStillLife`; `Pattern.blinker_isOscillator`, `toad_`, `beacon_`, `trafficLight_isOscillator` (period 2), `pulsar_isOscillator` (3), `pentadecathlon_isOscillator` (15) |
| Audit evidence | build and axiom audit at `47f841c` |
| Last updated | 2026-11-14: implemented |

## Purpose and scope

Define the basic stationary patterns and prove their periods. User outcome: "define the basic
configurations like … traffic lights … and prove the properties these have, such as periodicity".

Initial list: block, beehive, loaf, boat, pond, eater 1 (fishhook) as still lifes; blinker,
toad, beacon (period 2), traffic light (period 2), pulsar (period 3), pentadecathlon (period 15).
Extend on demand from the components needed by `N-09`–`N-11`.

## Dependencies

`N-01`, `N-03`: unverified until compiled.

## Sources and prior work

`sources.md` claims table: periods from `S-04`; traffic light data from `S-05` (mirror page
`Traffic_light`): 12 cells, 9 × 9, RLE `2b3o2$o5bo$o5bo$o5bo2$2b3o!`. Cell-exact data for the
other patterns must be recorded with a locator when retrieved (`N-18`).

## Theory development

- `IsStillLife P : step P = P ∧ P ≠ ∅`.
- `IsOscillator P p : evolve p P = P ∧ ∀ k, 0 < k → k < p → evolve k P ≠ P` (minimal period; a
  still life is excluded by `p ≥ 2`). State the weaker `evolve p P = P` separately, since it is
  what downstream composition uses.
- For each named pattern: the definition as explicit cells, the period theorem, population and
  bounding box of each phase as sanity lemmas.
- Traffic light: also the decomposition into four blinkers and the fact that the four blinkers
  do not interact (an application of `N-04` item 3 if they are far enough apart; otherwise a
  direct certificate — check which holds, since the blinkers of a traffic light are close).
- Optional theorem: the T-tetromino evolves into a traffic light (sourced claim: two known
  sequences of 27 and 28 generations, `S-05`); a good end-to-end test of `N-03`.

## Results (2026-11-14)

All twelve patterns of the initial list are compiled with exact periods. Pattern data: the
traffic light is from the LifeWiki mirror (`S-05`); the others were written from memory and are
validated only by the theorems proved about them (a wrong cell would make the period theorem
fail), not by a source locator. Not done: the decomposition of the traffic light into four
blinkers; the T-tetromino evolution; a link between `Pattern.block` and the explicit
`Finset` `block` of `Sanity/Life`.

## Claims and evidence

All periods and statistics: sourced, uncompiled. Minimality of periods: routine by certificate.

## Difficulty, barriers and readiness

Blocked on `N-01`, `N-03`. No research content.

## Outputs and next dependencies

Feeds `N-09` (eaters, blocks as reaction partners) and `N-11` (block).
