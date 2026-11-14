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
| Status | verified (engine compiled; benchmark recorded below; `Q-3` answered) |
| Implementation status | complete |
| Implementation evidence | `LeanTheory/Certificates/LifeSim.lean`, `LeanTheory/Certificates/LifeCert.lean`, commits `584f5bb`, `47f841c` |
| Lean evidence | `ofRows`, `mem_ofRows`, `nextRow`, `nextBit_eq_ruleB`, `step_ofRows`, `RowsStep`, `Padded`, `Tagged`, `Evolves`, `Evolves.sound`, `trimmedB`, `ofRows_inj`, `ofRows_ne`; tactics `life_cert`, `life_eval`; fixtures `glider_evolve_four`, `blinker_evolve_two`, `domino_evolve_one`, `glider_evolve_two_ne` |
| Audit evidence | build and axiom audit at `47f841c` (0 warnings, standard axioms); semantic review by the author of the work unit; see plan §4 |
| Last updated | 2026-11-14: implemented, benchmarked |

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

## Results (2026-11-14)

**Design as built.** As proposed, with two changes.

- The window is **enlarged** by one cell on every side at each generation instead of being
  checked for an empty margin, so the refinement theorem `step_ofRows` has no side condition;
  a `Padded` certificate then trims the window back.
- Rows are stored in certificates as **tagged literals** (`untag e = e >>> 64`, low 64 bits
  arbitrary). Reason, found by measurement: Lean hashes a `Nat` literal by its low 64 bits, so
  rows of a wide sparse window (nothing in the 64 leftmost columns) all had the same hash and
  kernel checking became quadratic or worse (Gosper gun, 600 generations: 134 s of type
  checking; with tags: 1.6 s). Soundness does not depend on the tags.

**Benchmark** (laptop, one `lake env lean` process per case; total wall-clock time including
≈ 1.5 s of start-up; peak memory of the process):

| Case | Initial window | Generations | Final window | Time | Memory |
| --- | --- | --- | --- | --- | --- |
| Glider, blinker, catalogue (16 patterns, all periods) | ≤ 13 × 13 | ≤ 15 each | — | 1.6 s for the whole file | 1.9 GB |
| Gosper gun | 36 × 9 | 30 | 36 × 12 | 1.6 s | 1.9 GB |
| Gosper gun | 36 × 9 | 120 | 48 × 35 | 1.8 s | 1.9 GB |
| Gosper gun | 36 × 9 | 600 | 168 × 155 | 5.1 s | 2.2 GB |
| Random soup (density 0.35) | 150 × 150 | 60 | 177 × 177 | 5.1 s | 2.3 GB |
| Random soup | 300 × 300 | 240 | 385 × 410 | 56 s | 5.2 GB |
| Random soup | 64 × 64 | 1000 | 490 × 433 | 109 s | 5.1 GB |
| Tall sparse window, 800 rows, 1 generation | 78 × 800 | 1 | — | 2.4 s | 1.9 GB |

Cost is roughly linear in (rows × generations): about 0.5–1 ms per row-generation for dense
windows a few hundred bits wide. Memory, not time, is the limit for one declaration (≈ 5 GB at
≈ 10⁵ row-generations of dense 400-bit rows); longer runs must be split over several
declarations and chained with `Rule.evolve_add`.

**Answer to `Q-3`.** Gate-sized windows (150 × 150 for 60 generations) are easy. A window of the
size of the register circuit reported in `R-18` (391 × 327, a few thousand generations per
operation) is about 10⁶ row-generations: expected to be feasible in minutes when split over
some tens of declarations. This last statement is an extrapolation, not a measurement.

**Not done.** Symbolic inputs (item 5): to be handled by case enumeration when `N-09` needs it.
The `meta` simulation runs in the interpreter; precompiling it (`LeanTheoryMeta`) is an
available optimization.

## Claims and evidence

| Claim | Status |
| --- | --- |
| A bit-parallel row step refines `step` | compiled: `step_ofRows` (unconditional, enlarged window) |
| 150 × 150 × 60 certificates check within the laptop budget | confirmed by measurement (5 s, 2.3 GB); `A-7` holds |
| Whole-machine direct simulation (e.g. a metacell, ≈ 10⁷ cells × 10⁴ generations) is infeasible this way | expectation, not measured; motivates the compositional theory `N-04`, `N-08` |

## Difficulty, barriers and readiness

Blocked on `N-01`. The benchmark is the inexpensive test of a risky assumption: if gate-sized
windows are too slow, the component strategy in `N-09`–`N-11` must change (smaller components,
more composition) before effort is invested there.

## Outputs and next dependencies

Unblocks `N-05`, `N-06`, `N-07`, `N-09`, `N-10`, `N-11`. Records the benchmark table in
`notes/implementation-plan.md` §12.
