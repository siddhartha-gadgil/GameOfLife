# N-02: Snapshots, finite evolutions and serialization

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-02` |
| Title | `Snapshot` and `Evolution` types with `Repr`, `ToJson`, `FromJson`; RLE import |
| Kind | definition / formalization |
| Addresses | `G-2`; `Q-11`, `Q-9` (import format) |
| Depends on | `N-01` |
| Dependency requirement | compiled `Cell`, `step`, `evolve` and the coordinate convention of `Q-1` |
| Produces | `LeanTheory/Bridge/LifeIO.lean` (or similar): `Snapshot`, `Evolution`, instances, validity predicate for evolutions, RLE parser/printer; fixtures |
| Difficulty | routine; the only open point is how strong a round-trip guarantee is provable for Lean's `Json` |
| Status | verified, with the gaps listed under "Results" |
| Implementation status | complete |
| Implementation evidence | `LeanTheory/Bridge/LifeIO.lean` (written by a sub-agent, checked and integrated by the coordinator) |
| Lean evidence | `Snapshot`, `Snapshot.cells`, `toCellList`, `ofCellList`, `cells_ofCellList`, `trim`, `cells_trim`, `Snapshot.step`, `cells_step`, `Snapshot.evolve`, `cells_evolve`; `Evolution`, `Evolution.valid`, `Evolution.cells_getElem_of_valid`, `Evolution.run`, `valid_run`; instances `Repr`, `ToJson`, `FromJson` for both; `Snapshot.toRLE`, `Snapshot.ofRLE?`; `Snapshot.fromJson?_toJson`, `Snapshot.cells_fromJson?_toJson`, `Evolution.fromJson?_toJson`; elaborators `rle%`, `cells%` |
| Audit evidence | build (0 warnings) and axiom audit (7225 declarations) after integration; module docstring and main statements read by the coordinator |
| Last updated | 2026-11-14: implemented |

## Purpose and scope

User constraint `A-3`: build `Repr`, `ToJson` and `FromJson` instances for snapshots and finite
time evolutions. These are the exchange format between Lean, external simulators (Golly) and
oracle scripts, and the way large pattern data enters the library.

## Dependencies

`N-01` (not yet compiled). `Lean.Data.Json` from core Lean (available; already imported by
template `meta` code, but not yet used at the object level in this repository).

## Sources and prior work

RLE and macrocell are the community formats (`S-05`, Golly; format specification not yet
retrieved — record its locator when `N-18` fetches it).

## Theory development

Proposed design:

- `Snapshot`: a canonical, duplicate-free, sorted `List (Int × Int)` (or `Array`) of live cells
  with a proof-free computable normal form, plus `Snapshot.toFinset` and
  `Snapshot.ofFinset`, with `toFinset (ofFinset S) = S`. A canonical form makes `Repr` output and
  JSON deterministic and makes equality of snapshots decidable by list equality.
- `Evolution`: an initial snapshot, a number of generations and the list of snapshots, with a
  Boolean validity check `Evolution.valid` meaning "each snapshot is `step` of the previous one",
  and a theorem `valid e = true → ∀ i, e.frames[i] = evolve i e.init`. A deserialized evolution
  is untrusted data until `valid` is certified (`N-03` tactics).
- JSON schema (proposal): `{"cells": [[x,y],…]}` for a snapshot;
  `{"init": …, "generations": n, "frames": […]}` for an evolution; optional `"rle"` string as an
  alternative encoding. Decide whether to store a bounding box or generation index explicitly.
- `Repr`: an ASCII grid of the bounding box for small patterns, falling back to the cell list.
- RLE reader/printer as plain functions (untrusted import path; anything proved about an
  imported pattern is proved about the resulting `Snapshot` value).

`Q-11` (assurance level): the ideal is a theorem
`fromJson? (toJson s) = .ok s`. Whether this is provable depends on whether the relevant
`Lean.Json` functions reduce or have usable lemmas; if not, the fallback is a proved round trip
for the intermediate `Json` *value* built by our own encoder/decoder (structural, no string
parsing), plus executable fixtures for the string level. Record which level was achieved.

## Results (2026-11-14)

User requirement `A-3` is met: `Repr`, `ToJson` and `FromJson` instances exist for `Snapshot`
and `Evolution`.

- A snapshot is a window `(x₀, y₀, rows)` in the encoding of `ofRows` (not a sorted cell list as
  proposed above; cell lists are a derived view). JSON schema as built:
  `{"x", "y", "rle", "cells"}` for a snapshot (written for the trimmed form; `"cells"` preferred
  on input) and `{"generations", "frames"}` for an evolution, with the initial snapshot as the
  first frame. Rows are never written as JSON numbers.
- `Snapshot.step`/`evolve` are proved to compute `conway.step`/`conway.evolve`;
  `Evolution.valid` is a Boolean check with a soundness theorem, so deserialized evolutions can
  be checked inside Lean.
- **Answer to `Q-11`** (assurance level): the round trip is *proved at the level of JSON values*
  (`Snapshot.cells_fromJson?_toJson`: decoding the encoding of `s` succeeds and gives the cells
  of `s`), proved by `rfl` on fixtures for RLE and plaintext, and *tested only* (`#guard`) at
  the string level through `Json.compress`/`Json.parse`. Lean's own `Json.mkObj` and friends are
  not exposed to proofs, so the encoders use the constructors of `Lean.Json` directly; a test
  checks agreement with Lean's encoder.
- Pattern literals `rle% "…"` and `cells% "…"` elaborate to explicit lists of rows.

Gaps (not proved): `Snapshot.trim` is a normal form (hence completeness of `Evolution.valid` and
the exact form of the JSON round trip); `toCellList` sorted and duplicate-free; anything about
strings in general. `ofRows_inj` in `Certificates/LifeSim` (uniqueness of trimmed windows) was
proved independently and could close the first gap.

## Claims and evidence

| Claim | Status |
| --- | --- |
| A canonical sorted-list snapshot is in bijection with `Finset Cell` | conjecture, routine |
| Value-level JSON round trip is provable | conjecture; depends on `Lean.Json` being a plain inductive type (expected) |
| String-level round trip (`Json.parse ∘ Json.compress`) is provable | unknown; likely not worth the cost |

## Difficulty, barriers and readiness

Blocked only on `N-01`. No research content. Under the module system the instances must be
`public` and the file needs `public import Lean.Data.Json`; check that this import is compatible
with the `module` setup used by the library before committing to a file layout.

## Outputs and next dependencies

Used by `N-05`–`N-11` for pattern import and by oracle scripts. Not a logical prerequisite of any
theorem: no proof may depend on deserialized data without a certified check.
