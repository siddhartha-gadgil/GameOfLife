# N-15: A register machine in Life

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-15` |
| Title | Compiling counter programs to finite patterns and proving the simulation |
| Kind | design / proof / formalization |
| Addresses | `G-7` |
| Depends on | `N-08`, `N-10`, `N-11`, `N-12`, `N-13`, `N-14` |
| Dependency requirement | compiled component specifications (memory operations, routing or gates) in a common format with a composition theorem; the counter-machine model; the chosen target statement |
| Produces | `LeanTheory/Design/LifeMachine.lean`: `compile : Program → Config`, `enc : Cfg → Config`, the simulation theorem |
| Difficulty | research-level engineering: the mathematics is known informally, but no formal proof exists in any prover; layout, timing and non-interference for an arbitrary program |
| Status | blocked (prerequisites not started) |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

The central construction under route R1: for every counter program a finite pattern, and a
proof that the pattern's evolution follows the program. Nothing here is specific to one program;
the proof is by composition over the program's instructions.

## Dependencies

All unverified. This note is conditional on the R1 decision of `N-13`.

## Sources and prior work

- Chapman's Minsky register machine and universal register machine patterns (`S-10`, not
  retrieved; described via `S-05`, `S-19` snippets as composed of five parts).
- Conway's argument (`S-02`, not retrieved).
- `S-07` for the method of building a large verified layout from specified components
  (their `floodfill` lemmas, §4.5–§4.6).

## Theory development

Sketch of the intended design, to be corrected against the sources:

- One sliding block per register, placed on well-separated diagonals.
- One component per instruction. A single control signal (a glider or a small salvo) enters an
  instruction component, which emits the salvo for `inc` or `dec`/test toward the register and,
  on completion, forwards the control signal to the component of the next instruction (two
  exits for `decJz`).
- `enc (pc, regs)`: the static machine, blocks at offsets `regs`, and the control signal at the
  entrance of instruction `pc`.
- Simulation theorem in the form fixed by `N-12`: `evolve (τ c) (enc c) = enc c'` whenever
  `step c = some c'`, with `τ c` depending on the register value involved.
- Obligations beyond the components: a layout function with a proof that components are
  pairwise separated; routing of control signals between arbitrary instruction pairs (crossings
  or delays); return signalling from the memory operation; that stray gliders are absorbed.

Open design questions: whether the control can be purely asynchronous (`N-10` technology 3) or
needs a clock; how salvos are generated on demand (a one-shot gun triggered by a signal); how
signals from far-away blocks return.

## Claims and evidence

No claims beyond the sourced existence of Chapman's pattern.

## Difficulty, barriers and readiness

Blocked. The smallest step that changes readiness: `N-13` decision plus reading `S-10` and
`S-11` ch. 9 to replace the sketch by an actual component list.

## Outputs and next dependencies

Feeds `N-16`.
