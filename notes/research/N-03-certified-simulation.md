# N-03: Certified simulation engine

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-03` |
| Title | Kernel-checked evolution certificates: a fast representation, its refinement proof and a tactic |
| Kind | certificate / formalization / computation |
| Addresses | `G-3`; `Q-3`; supports `G-4`, `G-5` |
| Depends on | `N-01`; template tactics `kernel_fact`, `bool_cert`, the SubsetSum pattern (`LeanTheory/SubsetSum.lean`, compiled) |
| Dependency requirement | compiled `step`/`evolve`; the certificate tactics as they exist in the audited template |
| Produces | `LeanTheory/Certificates/LifeSim.lean`: bit-row representation, `fastStep`, refinement theorem, inductive certificate `Evolves`, tactic (working name `life_cert`); a benchmark table answering `Q-3` |
| Difficulty | moderate: bit-level refinement proof and `meta` builder; the risk is performance at scale |
| Status | stated (approach chosen provisionally; feasibility is conjecture `A-7`) |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

Every concrete pattern fact ("the glider returns translated after 4 generations", "this gate
tile maps these inputs to these outputs in 60 generations") is a closed computation. Project
policy forbids every form of `decide` and `native_decide`; concrete checks must be explicit proof
terms whose leaves the kernel evaluates. This note designs the certificate format for
`evolve n P = Q` and measures how far it scales.

## Dependencies

`N-01` unverified (not yet written). The kernel accelerates `Nat` operations (`land`, `lor`,
`xor`, `shiftLeft`, `shiftRight`, comparisons) with GMP: stated in
`.claude/skills/lean-proofs/SKILL.md`; relied on by existing compiled certificate modules.

## Sources and prior work

- `S-07` §5.1: HOL4 symbolic simulation where each cell holds a Boolean expression over input
  variables; relied on HOL4's fast in-logic computation. Their per-gate method: several ticks of
  external simulation, then **one** in-prover tick showing the symbolic state reproduces itself
  with every variable aged by one.

## Theory development

Proposed design:

1. **Window representation.** A pattern inside a `W × H` window is a list of `H` naturals, bit
   `x` of row `y` meaning cell `(x₀ + x, y₀ + y)` is alive. One generation of a row is computed
   from the three neighbouring rows by a bit-parallel adder network (a fixed number of `Nat`
   bit operations per row), with a one-cell margin so that nothing leaves the window unnoticed.
2. **Refinement theorem** (proved once): if the margin of the window is empty before and after,
   `decode (fastStep rows) = step (decode rows)`. Proof by `Nat.testBit` reasoning.
3. **Certificate predicate** in the SubsetSum pattern: `Evolves rows n rows'` with one
   constructor per generation whose premise is a per-row kernel fact (`Eq.refl` on closed `Nat`
   terms). Soundness: `Evolves rows n rows' → evolve n (decode rows) = decode rows'`.
4. **Tactic** building the proof term from an untrusted simulation run in `meta` code, splitting
   long runs over several declarations.
5. **Symbolic inputs** (needed by `N-10`): either enumerate the `2^k` input cases of a gate
   (k ≤ 4 in `S-07`) as separate concrete certificates, or carry Boolean-expression cells as in
   `S-07`. Start with case enumeration.

Benchmarks to record (this is the answer to `Q-3`): glider × 4; Gosper gun (36 × 9 window grown
to fit emitted gliders) × 30 and × 120; a 150 × 150 window × 60; 300 × 300 × 240; and the
largest size that stays within the laptop budget (6 GB per Lean process). Report build time,
memory and term size per case.

## Claims and evidence

| Claim | Status |
| --- | --- |
| A bit-parallel row step refines `step` when the window margin stays empty | conjecture, proof expected to be routine but tedious |
| 150 × 150 × 60 certificates check within the laptop budget | conjecture `A-7`; **untested** |
| Whole-machine direct simulation (e.g. a metacell, ≈ 10⁷ cells × 10⁴ generations) is infeasible this way | expectation, not measured; motivates the compositional theory `N-04`, `N-08` |

## Difficulty, barriers and readiness

Blocked on `N-01`. The benchmark is the inexpensive test of a risky assumption: if gate-sized
windows are too slow, the component strategy in `N-09`–`N-11` must change (smaller components,
more composition) before effort is invested there.

## Outputs and next dependencies

Unblocks `N-05`, `N-06`, `N-07`, `N-09`, `N-10`, `N-11`. Records the benchmark table in
`notes/implementation-plan.md` §12.
