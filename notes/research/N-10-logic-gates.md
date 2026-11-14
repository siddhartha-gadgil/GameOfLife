# N-10: Logic gates and wiring

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-10` |
| Title | Choice of circuit technology; NOT, AND, OR, crossing, fan-out and delay |
| Kind | source synthesis / research approach, then formalization |
| Addresses | `G-5`; `Q-7` |
| Depends on | `N-08`, `N-09`; `N-13` (which control logic the machine needs); data from `N-18` |
| Dependency requirement | the component format and composition theorem; verified reactions; the route decision |
| Produces | a recorded technology decision; `LeanTheory/Theory/Life/Circuits/*.lean` with gate specifications and a theorem that a combinational circuit description compiles to a pattern computing it |
| Difficulty | hard: timing and routing across many components; mitigated by reusing a published, already verified design |
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

The finite control of any machine in Life is a logic circuit. Decide which family of gate
designs to formalize and prove a compositional circuit theorem.

## Dependencies

All unverified.

## Sources and prior work

Three candidate technologies (`Q-7`):

1. **Clocked LWSS streams in square tiles** (Carlini `S-08`; verified in HOL4, `S-07`):
   150 × 150 tiles, period-60 streams, crossovers for free, AND/OR/NOT/half-adder, a latch and a
   clock. Strength: an existing end-to-end formal proof to follow, with specifications already
   stated (`S-07` §4.1, §4.4). Weakness: tiles are large for kernel simulation (`A-7`), and
   interfacing LWSS logic with glider-salvo memory (`N-11`) is not covered by `S-07`.
2. **Period-30 glider streams** (Gosper guns, eaters, buckaroos, duplicators; the technology of
   the classical proofs and of Chapman's and Loizeau's machines per `S-05`). Strength: small
   components, native glider signals for the sliding block memory. Weakness: no retrieved
   source with exact geometries yet; glider streams cannot cross freely.
3. **Stable circuitry** (Herschel conduits, stable reflectors; `S-11` ch. 7 by title only).
   Strength: asynchronous one-shot signals suit a register machine (a single "program counter"
   glider moving between components, no global clock). Weakness: not yet read; components may
   be larger.

## Theory development

Decision criteria: (a) component window size against the `N-03` benchmark; (b) availability of
cell-exact data with provenance; (c) fit with the memory component of `N-11`; (d) whether the
machine needs general logic at all. For a register machine with one active signal the control
is a routing network (each instruction is a component that receives the signal, acts on a
register and forwards the signal on one of two outputs); AND/OR/NOT on synchronized streams may
then be unnecessary. This observation, if confirmed in `N-13`, favours technology 3 or a hybrid
and shrinks this note considerably.

Regardless of the choice, the user outcome asks for gates as ingredients; a minimal verified
NOT/AND/OR set in one technology is a deliverable in its own right.

## Claims and evidence

| Claim | Status |
| --- | --- |
| LWSS-tile gates satisfy the specifications of `S-07` §4 | proved in HOL4; not Lean evidence |
| A single-signal register machine needs only routing, increment/decrement and zero-test components | conjecture (design observation); to be examined in `N-13` |

## Difficulty, barriers and readiness

Not ready: needs `N-13`, `N-08` and sources (`S-11` ch. 6–9, `S-10`, `S-08` parts 1–3). The
source-synthesis half can start once `N-18` has retrieved them.

## Outputs and next dependencies

Feeds `N-15`.
