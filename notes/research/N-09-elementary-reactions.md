# N-09: Elementary reactions

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-09` |
| Title | Glider collisions, eaters and reflectors as verified reactions |
| Kind | definition / formalization / certificate |
| Addresses | `G-5` |
| Depends on | `N-03`, `N-05`, `N-06`, `N-08`; data from `N-18` |
| Dependency requirement | certificates for windows of a few tens of cells and generations; pattern definitions; the component specification format; cell-exact reaction geometries with provenance |
| Produces | `LeanTheory/Theory/Life/Reactions/*.lean`: one theorem per reaction in the `N-08` format |
| Difficulty | routine per reaction once the format exists; the effort is in selecting the minimal set and obtaining exact geometries |
| Status | stated (inventory provisional) |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

User outcome: "prove all the properties of ingredients that are needed for Turing machines". This
note covers the two-body reactions; gates (`N-10`) and memory (`N-11`) are built from them.

## Dependencies

All unverified until compiled.

## Sources and prior work

- Eater 1 absorbs a glider and recovers (four generations, per a Lexicon mirror snippet; `S-06`).
- Two-glider collisions: 71 in total; several annihilate cleanly (`S-05`, `S-06` snippets).
- Kickback reaction: one glider returned in the opposite direction (`S-06` snippet); the Lexicon
  says it matters for the universal-constructor argument.
- Glider + LWSS collision destroying the glider and leaving the LWSS (`S-07` Fig. 2).
- Three gliders can synthesize an LWSS (`S-07` §1.1, stated without geometry).
- Reflectors and duplicators named in `S-05` (page `URM`) for Loizeau's computer: buckaroo
  (90° glider reflector), a period-30 glider duplicator, period-60 gun ("twogun").

No reaction geometry has been retrieved yet; each must be recorded cell-exactly with a locator.

## Theory development

Provisional inventory, to be pruned to what the chosen route (`N-13`, `Q-7`) needs:

| Reaction | Specification shape |
| --- | --- |
| Glider into eater 1 | eater ∪ glider at offset `δ` → eater after `t` generations |
| Head-on / right-angle glider annihilation | two gliders at offset `δ` → `∅` after `t` |
| Stream inhibition (the NOT reaction) | stream crossing a gun stream at the right phase deletes matching gliders |
| Kickback | two gliders → one glider reversed, with exact output position and phase |
| Reflector (buckaroo or a stable reflector) | glider in → glider out at 90°, component restored after `t` |
| Duplicator / fan-out | one glider in → two out |
| Block + glider salvo | handled in `N-11` |

For each: the positive theorem, and a *negative fixture* with a wrong offset or phase showing
the stated geometry matters (for example, a glider that damages the eater).

## Claims and evidence

All reactions: sourced by name, geometry not retrieved, uncompiled.

## Difficulty, barriers and readiness

Blocked on `N-03`, `N-06`, `N-08` and on data (`N-18`). Individual reactions can be explored
with an external simulator before the Lean engine exists; such runs are numerical observations.

## Outputs and next dependencies

Feeds `N-10`, `N-11`.
