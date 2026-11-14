# N-14: Counter machines in Lean and their universality

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-14` |
| Title | A counter (Minsky register) machine model and its link to Mathlib computability |
| Kind | definition / proof / formalization |
| Addresses | `G-6`; `Q-12`; supports `G-7` |
| Depends on | Mathlib (`S-17`); `N-13` for the choice of model; `N-12` for the form of the statement |
| Dependency requirement | compiled Mathlib declarations (`Nat.Partrec.Code`, `Turing.TM2`, `Turing.ToPartrec`); a recorded route decision (conditional start is acceptable, see readiness) |
| Produces | `LeanTheory/Theory/Computability/CounterMachine.lean`: syntax, semantics, sanity programs, and a universality theorem relative to `Nat.Partrec.Code.eval` |
| Difficulty | hard: a standard result, but a complete formal compiler-correctness proof; no Life content |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

Under route R1 (`N-13`) Life simulates counter machines. To conclude anything about
computability, counter machines must be shown universal in Lean. Mathlib has no such model: a
search of `Mathlib/` for `minsky`, `counter machine` and `register machine` returned nothing
(2026-11-14).

## Dependencies

Mathlib: compiled. `N-13`: undecided; this note is useful under R1 only.

## Sources and prior work

- Mathlib `Turing.ToPartrec`: partial recursive codes are evaluated by `TM2` machines with
  several stacks (located by `grep`; statement details to be read when work starts).
- `S-07` references formalizations of register machines in other provers (its refs. [3], [11]);
  not retrieved.
- Minsky's theorem that two counters suffice is classical; it is **not needed**: a Life pattern
  can hold any fixed finite number of sliding blocks, so a machine with finitely many counters
  per program is enough.

## Theory development

- Model: a program is a finite list of instructions `inc r`, `decJz r l` (decrement register
  `r`, or jump to `l` if it is zero), `halt`, over `Fin k` registers holding naturals;
  configuration `(pc, regs)`; `step : Cfg → Option Cfg`; `eval` as a `Part`.
  The instruction set should mirror exactly what `N-11` provides, so that `N-15` is a
  one-to-one translation.
- Sanity: programs for addition, copying, and a non-terminating loop; determinism; a program
  that would need a missing instruction is rejected by the syntax.
- Universality, two possible proofs (`Q-12`):
  1. compile `Nat.Partrec.Code` (primitive recursion plus minimization) directly to counter
     programs with a register allocation discipline;
  2. simulate `Turing.TM2` by storing each stack as a number in base `|Γ| + 1`; push and pop
     become multiplication and division by a constant, implemented with an auxiliary counter.
  Choose after reading the Mathlib statements; (2) reuses `ToPartrec`, (1) avoids Gödel
  numbering of stacks.
- Target: for every `c : Nat.Partrec.Code` there is a counter program `P` with
  `P.eval (input n) = (c.eval n).map output`.

## Claims and evidence

| Claim | Status |
| --- | --- |
| Counter machines with finitely many registers compute every partial recursive function | classical theorem; no source retrieved; not compiled |
| Mathlib lacks this model | observation on the pinned checkout |

## Difficulty, barriers and readiness

Independent of every Life note. It can start as soon as the instruction set is fixed; starting
before `N-13` is confirmed risks only the instruction-set details, since every route except R2
passes through a register-like model. Statement and definitions are routine; the universality
proof is a substantial work item and may deserve sub-notes.

## Outputs and next dependencies

Feeds `N-15` (source language of the Life compiler) and `N-16`.
