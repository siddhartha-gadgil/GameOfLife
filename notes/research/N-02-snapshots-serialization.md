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
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

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
