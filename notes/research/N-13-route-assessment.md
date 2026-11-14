# N-13: Route to universality — direct Turing machine, register machine or Lisp interpreter

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-13` |
| Title | Assessment of the routes to a universality proof, including the user's Lisp-interpreter idea |
| Kind | research approach (decision note) |
| Addresses | `G-7`; `Q-5`, `Q-6`; informs `Q-7` |
| Depends on | `N-12` (what must be proved); sources `S-05`, `S-07`, `S-09`, `S-10`, `S-11`, `S-12` |
| Dependency requirement | the candidate target statements; enough of the sources read to compare component counts and proof obligations |
| Produces | a recorded decision for `Q-5` and `Q-6`, with reasons; revisions of `N-10`, `N-14`, `N-15` to match |
| Difficulty | moderate: a comparison of proof-engineering cost under incomplete information |
| Status | decided: route R1 (user, 2026-11-14, accepting the preliminary recommendation); confirmation against `S-10` and `S-11` ch. 9 outstanding |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded with preliminary assessment; decision recorded |

## Purpose and scope

User idea (`A-5`): "Instead of building a physical Turing machine, assess whether it is better
to build an interpreter for a small, self-hosting dialect of Lisp and use that to build a Turing
machine. Choose this or a direct approach based on what is easier and more transparent."

## Dependencies

No verified dependencies. Source access is partial (see `sources.md`): `S-09`, `S-10`, `S-11`
have not been read, so the comparison of the classical constructions rests on catalogue
summaries.

## Sources and prior work

- `S-12`: an existing Lisp interpreter in Life. Tower: Lisp interpreter in C → QFTASM →
  VarLife (8-state automaton) → OTCA metapixels → Life. RAM addresses are 10 bits and ROM
  addresses 12 bits; one VarLife generation costs 35 328 Life generations.
- `S-08` part 4: a register-machine CPU with 16 four-bit registers.
- `S-05` (`URM`, `Sliding_block_memory`): finite universal computers by Conway (argument, 1982)
  and Chapman (pattern, 2002) use sliding block memory; Rendell's Turing machine has a tape that
  is infinite (2000) or grows by construction (2011).
- `S-07`: a verified circuit layer in HOL4 (≈ 9 500 lines) for clocked LWSS logic.

## Theory development

**Separation of layers.** Any route has two parts.

- *Life layer*: a family of finite patterns proved to simulate some machine model `X`.
- *Software layer*: a proof, entirely outside Life, that `X` is universal (computes every
  partial recursive function, or simulates Mathlib's Turing machines).

A Lisp interpreter belongs to the software layer. It does not remove any Life-layer obligation:
an interpreter needs a processor and memory in Life exactly as a Turing machine does.

**Unbounded memory is the crux.** The existing Lisp-in-Life and CPU constructions have bounded
memory (10-bit RAM addresses; 16 four-bit registers). As built they are finite-state machines
and do not establish universality (correction `C-2`). Under the finite-support constraint the
known sources of unbounded memory are (a) sliding blocks — counters; (b) a tape or stack
extended by a construction arm. So the Life layer of *any* route reduces to (a) or (b).

**Routes compared (preliminary).**

| Route | Life layer | Software layer | Preliminary view |
| --- | --- | --- | --- |
| R1: register (counter) machine with sliding block memory | Per instruction: increment, decrement-or-branch-on-zero, routing. Memory verified once per operation (`N-11`). Possibly no clocked logic at all (`N-10`). | Counter machines are universal: not in Mathlib (`S-17`); `N-14`. | Smallest Life layer known. Preferred. |
| R2: direct Turing machine with a tape built by construction (Rendell 2011) | Finite-state control from stream logic, stack cells, and a universal-construction mechanism to extend the tape. | None: connects directly to `Turing.TM0`. | Software layer free, Life layer far larger (glider synthesis of stack cells). Not preferred. |
| R3: metacell tiling simulating a universal automaton (`S-07`, OTCA) | A verified metacell. | A universal cellular automaton or Turing machine embedded in a tiling. | The tiling is infinite: violates `A-2` unless the metacell has an empty off state (0E0P), which is very large. Rejected under the constraint. |
| R4: Lisp machine as the simulated model | A stored-program processor with unbounded memory: at least the machinery of R1 or R2, plus an instruction decoder. | Interpreter correctness, then a Turing machine simulator written in Lisp and its correctness. | Adds obligations to both layers. Not preferred as the proof route. |
| R1 + Lisp as an optional software layer | As R1. | A small Lisp with a Lean semantics, compiled to counter machines, used to *exhibit* programs (including a Turing machine simulator) readably. | Possible later as a transparency demonstration; not needed for the theorem. |

**Why Lisp does not shorten the software layer either.** The theorem needs "model `X` is
universal". Mathlib already proves that partial recursive functions are computed by its `TM2`
stack machines (`Turing.ToPartrec`). The shortest software layer is a single simulation into
counter machines (of `Nat.Partrec.Code` directly, or of `TM2` by Gödel-numbered stacks). Going
through a Lisp interpreter means proving an interpreter and a compiler correct in addition.
Self-hosting is a property that plays no role in the universality theorem.

**Where the user's idea has real merit.** Transparency for a reader: a universal machine given
as a readable program rather than a state table; and a single fixed universal pattern whose
input is a program. Both are obtainable on top of R1 after the main theorem and can be a
separate, later goal.

**Decision (user, 2026-11-14): the recommendation below is adopted.**

**Recommendation.** R1 for the Life layer; software layer by a direct simulation
linking counter machines to Mathlib (`N-14`); keep "Lisp on top" as an optional later goal
(`G-9`, inactive). This recommendation must be re-examined after reading `S-10` and `S-11`
ch. 9, because it relies on the unverified expectation that a register machine needs only
single-signal routing components.

## Update from the source report `R-18` (2026-11-14)

Source: [`reports/R-18-source-report.md`](reports/R-18-source-report.md), written by a sub-agent
that read the primary sources (book `S-11` ch. 9 and parts of ch. 2, 6–8, 11, 12; Chapman's
archived pages `S-10`; Hickerson's 1990 description; Durand–Róka's research report `S-14`).
Its numerical observations are simulations, not proofs.

**Route R1 is consistent with every source read**, with these corrections to the assessment:

- The component list is: sliding block register with `INC` and `TDEC` (returning on a `Z` or
  `NZ` lane), a pair of latches (demultiplexers) per state, splitters, transparent merges,
  reflectors, eaters. The program counter is one glider on one of `n` state lanes.
- "Possibly no clocked logic" holds for the book's design only after replacing its single clock
  gun by path delay (the book says this is possible) and for an undocumented file of Chapman's.
- "Only single-signal routing" must add the latches and one inhibition.
- The register is a large circuit (2316 cells, thousands of generations per operation), so the
  Life layer of R1 is larger than this note assumed, though still far smaller than R2.
- The reported gap in Conway's argument (parasitic gun outputs) is a further reason to prefer a
  gun-free design.

## Claims and evidence

| Claim | Status |
| --- | --- |
| Existing Lisp-in-Life and CPU patterns have bounded memory | sourced (`S-12`, `S-08` summaries) |
| Every finite-support universal construction needs unbounded space | proof sketch (`N-04` item 7) |
| R1 has the smallest Life-layer proof obligation | judgement from catalogue summaries; unverified |
| A Lisp layer adds rather than removes proof obligations | argument above; no formal content |

## Difficulty, barriers and readiness

Ready now. To turn the preliminary assessment into a decision: read `S-10`, `S-11` ch. 9 and
`S-09` (`N-18`), list the distinct component types each of R1 and R2 needs, and obtain the
user's agreement, since the route was explicitly left open by the user.

## Outputs and next dependencies

Fixes the scope of `N-10`, `N-11`, `N-14`, `N-15`. If R1 is confirmed, `N-14` is unblocked
without regret.
