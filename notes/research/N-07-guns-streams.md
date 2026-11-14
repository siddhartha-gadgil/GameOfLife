# N-07: Guns and glider streams

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-07` |
| Title | The Gosper glider gun and the definition of a gun on finite configurations |
| Kind | definition / proof / formalization |
| Addresses | `G-4`; `Q-8` (statements over unbounded time) |
| Depends on | `N-03`, `N-04`, `N-06` |
| Dependency requirement | certificates for a 30-generation window; independence along a run (`N-04` item 4); the glider family and its translation theorem |
| Produces | `LeanTheory/Theory/Life/Patterns/Guns.lean`: `stream`, `IsGun`, `gosperGun`, the emission theorem for all `n` |
| Difficulty | moderate: the first statement that combines a finite certificate with an unbounded-time induction |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

User outcome: define guns and prove their properties. With finite support a gun is **not**
periodic as a configuration: its population grows without bound (correction `C-4`). The precise
statement is an invariant of the form "gun plus `n` emitted gliders evolves in `p` generations to
gun plus `n + 1` emitted gliders".

## Dependencies

All unverified until compiled.

## Sources and prior work

Gosper glider gun (`S-05`, mirror page `Gosper_glider_gun`): 36 cells, 36 × 9, period 30,
Gosper 1970, two queen bee shuttles stabilized by blocks. RLE as shown on that page (a stray
space in the sixth row was removed by the retrieval tool; **re-check against a pattern file**):

```
24bo11b$22bobo11b$12b2o6b2o12b2o$11bo3bo4b2o12b2o$2o8bo5bo3b2o14b$2o8bo3bob2o4bobo11b$10bo5bo7bo11b$11bo3bo20b$12b2o!
```

The page does not state the direction of the emitted gliders.

## Theory development

- `stream d φ pos gap n`: the union of `n` gliders of direction `d`, phase `φ`, spaced `gap`
  apart starting at `pos` (finite, so allowed by `A-2`).
- `IsGun G p (d, φ, pos, gap)`: for every `n`,
  `evolve p (G ∪ stream … n) = G ∪ stream … (n + 1)` with the stream shifted appropriately, and
  `G` influence-disjoint from all gliders but the newest.
- Theorem `gosperGun_isGun`: proof plan — (i) a certificate for the gun together with the most
  recent one or two gliders over 30 generations in a window; (ii) older gliders are far enough
  to evolve independently (`N-04` item 4) and translate by `N-06`; (iii) induction on `n`.
- Corollaries: `evolve (30 n) gosperGun = gosperGun ∪ stream … n` (up to the start-up
  transient, to be determined by simulation); population is unbounded; the gun is not eventually
  periodic (sanity check against `N-04` item 7).
- Gun plus eater: a bounded, genuinely periodic configuration; useful degenerate case.

## Claims and evidence

| Claim | Status |
| --- | --- |
| The RLE above is the Gosper gun with period 30 | sourced (`S-05` mirror), uncompiled; data needs re-checking |
| The invariant holds for all `n` | proof sketch; depends on the exact window and separation constants |

## Difficulty, barriers and readiness

Blocked on `N-03`, `N-04`, `N-06`. This note is the smallest instance of the general problem
`Q-8` (how to state and prove behaviour of a component that emits signals forever), so its
solution should inform `N-08` rather than be ad hoc.

## Outputs and next dependencies

Feeds `N-08`, `N-09`, `N-10`.
