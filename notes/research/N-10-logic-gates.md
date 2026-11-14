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
| Status | partly verified: terminated stream, blocked stream and one gate are compiled; fan-out and placement rules open |
| Implementation status | in progress |
| Implementation evidence | `LeanTheory/Theory/Life/Gates.lean`; search oracle `scripts/life_gates/`; report `reports/R-20-gun-gates.md` |
| Lean evidence | `terminatedGun_isOscillator`, `terminatedGun_eq_union`, `gunB`, `blockedStream`, `blockedStream_start`, `blockedStream_isOscillator`, `blockedStream_eq_union`, `glider_pair_annihilate`, `gate`, `gateControl_eq_translate`, `gateOutput_eq_evolve`, `gate_wrong_lane_ne` |
| Audit evidence | not audited |
| Last updated | 2026-11-14: first components certified |

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

## Update from the source report `R-18` (2026-11-14)

Source: [`reports/R-18-source-report.md`](reports/R-18-source-report.md), written by a sub-agent
that read the primary sources (book `S-11` ch. 9 and parts of ch. 2, 6–8, 11, 12; Chapman's
archived pages `S-10`; Hickerson's 1990 description; Durand–Róka's research report `S-14`).
Its numerical observations are simulations, not proofs.

- Neither explicit register-machine design uses Boolean gate networks. The components needed
  are: reflectors and delay paths, splitter (fan-out), merge (transparent reflector), a one-bit
  latch per branch target (demultiplexer with a boat, or a block latch), an eater, and one
  inhibition of one signal by another inside the register. This confirms the conjecture recorded
  below, with the addition of latches.
- Chapman's documented 2002 machine is clocked throughout (period 30/60/120 guns, LWSS signals);
  the book's design is stable except for one clock gun that the text says can be replaced by
  path delay; an undocumented 2005 file of Chapman's is entirely gun-free.
- "Asynchronous" is not "timing-free": both designs rely on ordering constraints between
  signals, which a proof must state as explicit timing inequalities.
- Consequence: the technology choice `Q-7` leans to stable circuitry (technology 3). Verified
  NOT/AND/OR gates remain a deliverable of `G-5` in their own right but are not on the path to
  `G-7`.

## Decision (2026-11-14)

`Q-7` is decided by the user's choice of an own design: technology 2 (period-30 glider streams of
Gosper guns), in the form of *blocked streams and gates* described in `N-15` (design D1), with
every stream terminated. A gate with two inputs is at the same time the classical NOT/AND
element (`a ∧ ¬ b` on streams), so the verified gates that `G-5` asks for come out of the same
components. Stable reflectors and conduits are not used. First deliverables: the annihilation
and absorption reactions, then one blocked stream as a certified oscillator, then one gate.

## First components (2026-11-14)

Found by our own search (`scripts/life_gates`, report `R-20`, a sub-agent's work; observations
until certified) and certified in `Theory/Life/Gates.lean`:

- `terminatedGun = gosperGun ∪ translate (25, 11) eater1`: an oscillator of period exactly 30.
- `blockedStream`: `gosperGun` and a mirror image `gunB` whose streams annihilate each other;
  reached from the bare guns in 90 generations; an oscillator of period exactly 30; equal to the
  two guns plus three gliders of each stream.
- `gate`: `conway.evolve 90 (blockedStream ∪ gateControl) = blockedStream ∪ gateOutput`, with
  the control a translate of the catalogue glider and the output the gun's own glider at age
  90 (so the output is re-timed to the gun).

Observations of `R-20` not yet certified, relevant for the layout:

- a gate accepts only 12 of the 30 input phases on odd lanes and 4 on even lanes; along a signal
  lane the admissible positions of a translated copy repeat with period 15 (the parity risk of
  `N-15` is real but leaves solutions);
- 712 of 961 gates found also work with controls 30 and 60 generations apart; two gates in
  series work for all 228 translations tried;
- outputs leave only on the two stream lanes; other directions need rotated or reflected
  copies; kickbacks (control survives and releases a glider — a fan-out) exist but fail when
  used again 30 or 90 generations later;
- exactly mirror-symmetric gun pairs have period 60; some gun pairs have two different cycles.

Next: the gate as a `Reaction` with a box footprint; a fan-out; the salvo generators.

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
