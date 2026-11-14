# N-11: Sliding block memory

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-11` |
| Title | An unbounded counter stored as the position of a block |
| Kind | definition / formalization / certificate |
| Addresses | `G-5`; `Q-6` |
| Depends on | `N-03`, `N-04`, `N-05`, `N-06`, `N-08`; data from `N-18` |
| Dependency requirement | certificates for the push, pull and test reactions; translation equivariance to transfer one certificate to every block position; the component format |
| Produces | `LeanTheory/Theory/Life/Memory/SlidingBlock.lean`: `counter k` (block at diagonal offset `k`), `inc`, `dec`, `isZero` specifications valid for every `k : ℕ` |
| Difficulty | moderate: three small reactions plus a uniform-in-`k` argument; the zero test and the salvo generators are the delicate parts |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

With finite support (`A-2`) and no construction arm, the simplest known unbounded memory is a
block whose distance from the machine encodes a natural number. Population stays bounded while
the bounding box grows without bound, which is exactly what `N-04` item 7 requires of a
universal machine.

## Dependencies

All unverified until compiled.

## Sources and prior work

`S-05` (mirror page `Sliding_block_memory`): Conway's original pulls a block three diagonal
cells with 2 gliders and pushes it three with 30 gliders; Hickerson's version pulls by one with
2 gliders and pushes by one with 3; reading needs a zero test (Conway) or detection of the
transition from one to zero (Hickerson). Used by Chapman's URM (`S-10`), Goucher's pi calculator
and Spartan universal computer-constructor, and Bell's Collatz 5N+1 simulator. Exact salvo
geometries: **not retrieved**.

## Theory development

- `counter k := block translated by k·(1,1)` relative to a fixed origin (direction per `Q-1`).
- `pull`: block at offset `k + 1` plus a 2-glider salvo at a fixed offset *relative to the
  block* evolves to block at offset `k`, with nothing else left. One certificate at one position
  plus translation equivariance gives all `k`.
- `push`: likewise with a 3-glider salvo, `k ↦ k + 1`.
- The salvos are emitted from the machine at a fixed place, so they must travel a distance
  proportional to `k` before meeting the block; the travel is covered by `N-06` and `N-04`
  item 4, and the duration of an operation depends on `k` (time is not uniform; statements must
  quantify durations accordingly).
- `isZero`: a test signal that returns on one path when `k = 0` and on another when `k > 0`.
  Understand from the sources whether the test is a separate probe or a by-product of the pull
  salvo, and what happens when pulling at zero.
- Negative fixtures: a salvo with wrong spacing destroys or misplaces the block.

## Update from the source report `R-18` (2026-11-14)

Source: [`reports/R-18-source-report.md`](reports/R-18-source-report.md), written by a sub-agent
that read the primary sources (book `S-11` ch. 9 and parts of ch. 2, 6–8, 11, 12; Chapman's
archived pages `S-10`; Hickerson's 1990 description; Durand–Róka's research report `S-14`).
Its numerical observations are simulations, not proofs.

- The block reactions exist cell-exactly (book Fig. 8.37, data in `R-18` §4.1): a one-glider
  (2,1) pull (8 generations), a two-glider pull by one diagonal cell (26 generations, Hickerson)
  and a three-glider push by one (32 generations, credited to Chapman 2004). Hickerson's own
  1990 push is a different salvo. The statement "Hickerson pushes with 3 gliders" above
  conflates the two.
- Zero handling differs by design: Hickerson detects the 1 → 0 transition and a pull at zero
  destroys the register; the book (Goucher's design) performs a separate non-destructive test
  before the pull, packaged as `TDEC` ("test, then decrement unless zero") with a return glider
  on a `Z` or an `NZ` lane; `INC` returns nothing.
- **Correction to the difficulty estimate.** The reactions are small, but the register that a
  machine uses is a stable circuit of 2316 cells in a 391 × 327 box whose `INC` takes about
  1 700 generations and whose `TDEC` takes about 2 900–4 000 (observations). The salvo
  generators and the test circuit, not the block reactions, are the bulk of the work. By the
  benchmark of `N-03` a certificate of one operation at one block position is expected to be
  feasible; the uniform-in-`k` argument (translation of the block and of the travelling salvo)
  is still needed.
- Decision to take when this note is worked on: formalize the book's `TDEC` semantics, which
  matches the `decJz` instruction of `N-14`.
- Licence of the pattern files: not stated by the sources (`Q-9` stays open).

## Claims and evidence

| Claim | Status |
| --- | --- |
| 2-glider pull by one and 3-glider push by one exist (Hickerson) | sourced (`S-05`), geometry not retrieved, uncompiled |
| One certificate per operation suffices for all `k` | proof sketch (translation equivariance and independence along a run) |

## Difficulty, barriers and readiness

Blocked on `N-03`, `N-04`, `N-08` and on data. Before formalization, reproduce the reactions in
an external simulator (numerical observation) and record exact offsets.

## Outputs and next dependencies

Feeds `N-15`. If the reactions cannot be obtained or verified, `Q-6` must reconsider the
alternatives (a tape built by a construction arm as in `S-09`), which are much heavier.
