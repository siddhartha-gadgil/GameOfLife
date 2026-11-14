# N-12: What "Turing complete" means for Life on finite configurations

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-12` |
| Title | Target statements for universality and the undecidability corollary |
| Kind | definition / research approach |
| Addresses | `G-7`; `Q-4` |
| Depends on | Mathlib computability (`S-17`); `N-01` for the type of configurations (statement level only) |
| Dependency requirement | the names and types of `Nat.Partrec.Code.eval`, `ComputablePred`, `ComputablePred.halting_problem`; the kernel type |
| Produces | precise candidate theorem statements, a recommendation among them, the list of library gaps (e.g. `Primcodable` for configurations), an entry in the model contracts |
| Difficulty | moderate: no hard mathematics, but the statement must exclude trivial "simulations" and must be provable by the planned construction |
| Status | stated in outline: headline decided by the user on 2026-11-14 (candidates 2, 3 and 4 below); exact Lean statements open |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded; headline decided |

## Purpose and scope

"Life is a Turing machine" is not a mathematical statement (correction `C-1`). This note fixes
what will be proved. It can be worked on immediately and independently of all Life-level
constructions, and its outcome shapes `N-14`–`N-16`.

## Dependencies

Mathlib declarations exist in the pinned checkout (located by `grep`; compiled in the cache):
`ComputablePred.halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom` in
`Mathlib/Computability/Halting.lean`; `Turing.TM0`, `TM1`, `TM2`; `Turing.ToPartrec`.

## Sources and prior work

- `S-14` (Durand–Róka, snippet only): distinguishes several universality notions for Life and
  gives precise definitions; reported to derive Turing universality from intrinsic universality.
  **Must be read** before this note is finalized.
- `S-05` (`URM`): "a universal computer may be either infinite or finite"; Rendell's 2000
  machine needs an infinite tape pattern, the 2011 version does not.
- `S-07`: a self-simulation theorem on arbitrary (possibly infinite) states; explicitly leaves
  the connection with traditional computability as future work.

## Theory development

Candidate statements, from weakest to strongest:

1. **Bounded simulation** (non-uniform): for each machine, input and step bound there is a finite
   pattern simulating that many steps. Too weak: gives no undecidability. Useful only as an
   intermediate rung.
2. **Simulation of a machine model.** For every program `M` of a fixed universal model (counter
   machines, `N-14`) there are a *computable* encoding `enc_M : Cfg M → Config` and a decoding
   such that one machine step corresponds to `evolve (τ c)` of the encoding, where the duration
   `τ` may depend on the configuration, and halting corresponds to a simple observable.
3. **Undecidability corollary.** A natural predicate on finite configurations is not computable,
   by reduction from `ComputablePred.halting_problem`. Candidates: "some cell of a fixed finite
   set is eventually alive"; "the configuration eventually becomes periodic"; "the configuration
   eventually dies out". The first is the easiest to arrange (the halt signal is routed to a
   marker cell).
4. **Computation of every partial recursive function**: for each `c : Nat.Partrec.Code` and
   input `n`, a computable finite pattern which reaches a decodable output configuration iff
   `c.eval n` is defined, with the decoded value equal to it.

Conditions that prevent trivial encodings: `enc` computable (in Mathlib's sense, which needs a
`Primcodable` structure on configurations — a library gap to fill, probably through sorted
lists of cells), the halting observable decidable on a single configuration, and the pattern for
`M` on input `x` obtained from a fixed pattern for `M` by a simple input placement.

Necessary feature (from `N-04` item 7): any such construction uses unbounded space; with sliding
block memory the population nevertheless stays bounded.

**Decided (user, 2026-11-14)**, following the recommendation: prove 2 for counter machines, derive 4 through `N-14`, and state 3
as the headline corollary because it mentions no machine model at all.

## Claims and evidence

No claims; this note produces definitions. Whether the Mathlib notions compose as hoped is
unchecked.

## Difficulty, barriers and readiness

Ready now as a research note: read `S-14`, then draft the candidate statements against the
Mathlib declarations. Unproved statements must not enter the library (no `sorry`); draft them
in this note or in the scratchpad. The user should confirm the headline statement (`A-4`).

## Outputs and next dependencies

Feeds `N-13`, `N-14`, `N-15`, `N-16`.
