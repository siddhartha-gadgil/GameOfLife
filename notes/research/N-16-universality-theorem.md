# N-16: The universality theorem and undecidability

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-16` |
| Title | Life computes every partial recursive function; an undecidable property of finite patterns |
| Kind | proof / formalization |
| Addresses | `G-7` |
| Depends on | `N-12`, `N-14`, `N-15`; Mathlib `ComputablePred.halting_problem` |
| Dependency requirement | compiled simulation theorem (`N-15`); compiled counter-machine universality (`N-14`); the statement chosen in `N-12`; computability of the compile and encode maps |
| Produces | the top-level theorems of the project and their scope statement |
| Difficulty | moderate once the dependencies exist: composition of simulations and a many-one reduction; computability side conditions (`Primcodable` structure on configurations) may be laborious |
| Status | blocked on `N-15`; targets fixed in `N-12`; the reduction from a family to the general problem is compiled |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | `not_computablePred_everAlive_of_family` (`Theory/Life/Decision.lean`); `exists_program_halts_not_computable` (`N-14`) |
| Audit evidence | not audited |
| Last updated | 2026-11-14: targets and available pieces recorded |

## Purpose and scope

Assemble the final statements of `G-7`:

1. for every `c : Nat.Partrec.Code` and input `n`, a computable finite configuration whose
   evolution reaches a halting configuration iff `(c.eval n).Dom`, with decodable output;
2. a predicate on finite configurations (chosen in `N-12`) that is not computable.

## Dependencies

All unverified.

## Sources and prior work

No formal proof of either statement for Life is known to this project: `S-07` (2025) states the
connection of Life with traditional computability as future work. This is a statement about the
literature seen so far, not a priority claim.

## Theory development

- Compose `N-14` (code → counter program) with `N-15` (program → pattern).
- Show the composite map `Code × ℕ → Config` is computable in Mathlib's sense; this needs an
  encoding of configurations (through canonical cell lists of `N-02`).
- Reduction: if the chosen predicate were computable, so would be halting.
- Scope statement to accompany the theorem: finite support at all times; unbounded space and
  time; no claim about efficiency; no claim of intrinsic universality.

## Available pieces (2026-11-14)

- Target statements T1–T3: `N-12` ("Exact statements").
- `exists_program_halts_not_computable`: a well-formed counter program `P₀` whose halting problem
  on inputs `n` is not computable (`N-14`).
- `not_computablePred_everAlive_of_family`: T1 ⟹ T3.

Still needed for T1: the Life pattern `f n` of `P₀` on input `n` with `Computable f`; "halts ⟹
marker ever alive" from the simulation theorem of `N-15`; "marker ever alive ⟹ halts" from the
footprints of all reactions of a non-halting run.

## Claims and evidence

None compiled. The implication structure is a proof sketch conditional on `N-14` and `N-15`.

## Difficulty, barriers and readiness

Blocked on `N-14`, `N-15`.

## Outputs and next dependencies

Completes `G-7`. Satisfies part of the activation rule of `G-8`.
