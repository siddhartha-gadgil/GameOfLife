# Theory development and verification plan

This is the project index and plan of record for the formal theory of **Conway's Game of Life**.
Identifiers are stable; detailed work lives in the notes under `notes/research/`, which follow
`notes/note-template.md`. Sources and assumptions are in [`sources.md`](sources.md).

## 0. Current status

*As of 2026-11-14 (evening): foundations, catalogue, counter machines and the first machine
components are compiled; the Life machine itself is being designed.*

**Domain.** Conway's Game of Life on the infinite grid `ℤ × ℤ`, restricted to configurations
with finitely many live cells at every time. Aims: a coherent, fully formalized theory from the
basic patterns (still lifes, oscillators, gliders, guns) through the ingredients of computation
to a proof that Life is Turing complete, and ultimately self-replication.

**Verified foundation (compiled; see §4 for the checks).**

| Module | Note | Content |
| --- | --- | --- |
| `Kernel/Life`, `Sanity/Life` | `N-01` | The model: rule, `step`, `evolve`; agreement with the set-level specification; sanity suite |
| `Certificates/LifeSim`, `LifeCert` | `N-03` | Tactics `life_cert`, `life_eval`: `conway.evolve n W = W'` for explicit windows, kernel-checked, no `decide`; uniqueness of trimmed windows |
| `Theory/Life/Locality` | `N-04` | Independence of separated patterns, equivariance, periodicity algebra, bounded ⇒ eventually periodic |
| `Theory/Life/Patterns` | `N-05`, `N-06` | Six still lifes, six oscillators (exact periods), glider and three larger spaceships (exact period and displacement) |
| `Theory/Life/Guns` | `N-07` | The Gosper gun for all time (`gosperGun_evolve`, `IsGun`) |
| `Bridge/LifeIO` | `N-02` | `Snapshot`, `Evolution` with `Repr`, `ToJson`, `FromJson`; RLE; pattern literals |
| `Theory/Life/SlidingBlock`, `Register` | `N-11` | `pull`, `push` for every block position; `pipeline` for trains of salvos |
| `Theory/Life/Reactions`, `Boxes` | `N-08` | Reactions with footprints: parallel and sequential composition, placement; rectangular footprints |
| `Theory/Life/Collisions` | `N-09`, `N-11` | Absorption, annihilation, kickback, turn-round; the zero test (`zeroTest_hit`, `zeroTest_pass`) |
| `Theory/Life/Gates` | `N-10` | `terminatedGun`, `blockedStream` (oscillators of period exactly 30), `gate`, both as reactions with boxes |
| `Theory/Life/BoxCert`, `SalvoGenerator` | `N-08`, `N-15` | `life_reaction` (certificates with a box for every generation); `reflector`; `pullGenerator_reaction`: one control glider yields the pulling salvo |
| `Theory/Life/Decision` | `N-12` | `WindowData`, `EverAlive`, reduction from a computable family to the general decision problem |
| `Theory/Computability/*` | `N-14` | Counter machines; `exists_computes_code`; an undecidable halting problem |

Goals achieved: `G-1`, `G-2`, `G-4`, `G-6`. **Not verified:** a salvo generator, a fan-out, the
logic of the zero test, the layout of a machine, the simulation theorem, any undecidability
statement about Life (`G-7`), self-replication (`G-8`).

**Decisions taken by the user (2026-11-14).**

- Kernel conventions (`Q-1`, `Q-2`): `Finset (ℤ × ℤ)`, `y` downward, generic `Rule` with `conway`.
- Meaning of "Turing complete" (`Q-4`): an undecidable predicate on finite configurations plus
  computation of every partial recursive code; exact statements in `N-12`.
- Route (`Q-5`, `Q-6`): a register machine with sliding block memory; not a direct Turing
  machine and not a Lisp interpreter.
- Circuitry (`Q-7`, `Q-9`): designed in this project from verified elementary reactions, found
  by our own search; the literature is used for ideas only and nothing is copied exactly.
  Design D1 (`N-15`): gated, terminated streams of Gosper guns, eaters, blocks and gliders.
- Commits go directly to `main`.

**Sourced, unverified.** Pattern statistics and the history of universal constructions
(`sources.md`). The salvo generator has been worked out in the literature (Conway's
side-tracking; Hickerson's shotgun with suppression, 1990; Chapman 2002; stable conduits in
`S-11`), see `N-15`. One formal precedent: verified Life circuits in HOL4 (`S-07`), which proves
self-simulation on generally infinite states and leaves the link to computability open.

**Latest result.** The search `scripts/life_machine` (report `R-21`) found a fan-out, a
reflector and a generator of the pulling salvo from one control glider; the reflector and the
generator are certified (`SalvoGenerator.lean`). Not found yet: a generator of the pushing salvo
and a "continue" glider.

**Main barriers.** (i) The push-salvo generator, the continue signal and the zero-test logic are
not yet designed. (ii) The layout
of a whole machine and its proof by the reaction calculus (`N-15`) is a large piece of work not
yet started; timing constraints between signals are not yet formalized. (iii) Gates accept only
some input phases (12 of 30 on odd lanes, 4 on even), which quantizes placements. (iv)
Self-replication is far beyond direct simulation (`Q-10`).

**Ready choices.** Certification of whatever `R-21` delivers; the gate with repeated controls and
two gates in series (observed in `R-20`, not certified); the passage of the three-glider zero
test for `k ≥ 1`; the train of operations as a `Reaction`; optional catalogue extensions. See §7.

## 1. Goal registry

| ID | Goal and success criterion | Supports / supported by | Status | Evidence needed |
| --- | --- | --- | --- | --- |
| `G-1` | **Kernel.** Life on finite configurations: compiled definitions of cells, neighbours, `step`, `evolve`, with an independent set-level specification proved equivalent, and the full sanity suite (degenerate, concrete, counterexample, symmetry, speed of light). | supports all goals | **achieved** (2026-11-14, commit `0ae423d`) | `N-01` compiled; strict kernel audit passed (§4) |
| `G-2` | **Serialization.** `Repr`, `ToJson`, `FromJson` instances for snapshots and finite time evolutions, a certified validity check for evolutions, and a recorded round-trip guarantee. | supported by `G-1`; tooling for `G-4`, `G-5` | **achieved** (2026-11-14) at the assurance level recorded in `N-02` | `N-02` compiled; round-trip theorem or documented fallback (`Q-11`) |
| `G-3` | **Compositional theory and certified simulation.** Locality, independence of separated patterns, equivariance; a certificate tactic proving `evolve n P = Q` with standard axioms only; a component interface with a composition theorem. | supported by `G-1`; supports `G-4`, `G-5`, `G-7`, `G-8` | **achieved in a first form** (2026-11-14): `N-03`, `N-04` verified; reaction calculus with footprints compiled (`Reactions`, `Boxes`) and used for `pull_reaction`, `gate_reaction`; timing constraints and a multi-component example still open | `N-03`, `N-04`, `N-08` compiled; benchmark table for `Q-3` |
| `G-4` | **Pattern catalogue.** Named definitions and theorems: still lifes (block, beehive, loaf, boat, pond, eater 1) fixed; oscillators (blinker, toad, beacon, traffic light, pulsar, pentadecathlon) with exact periods; spaceships (glider, LWSS, MWSS, HWSS) with period and displacement in every orientation; the Gosper gun emitting one glider per 30 generations for all time. | supported by `G-1`, `G-3`; supports `G-5` | **achieved** for the stated list (2026-11-14): `N-05`, `N-06`, `N-07` compiled | `N-05`, `N-06`, `N-07` compiled |
| `G-5` | **Ingredients of computation.** Verified specifications, in one composable format, of the reactions, signal routing, logic and unbounded memory needed by the machine of `G-7` (including NOT/AND/OR gates in at least one technology and the sliding block counter for every value). | supported by `G-3`, `G-4`; supports `G-7` | partly achieved: block reactions for every position, pipelining, zero test, absorption, annihilation, kickback, terminated gun, blocked stream, one gate. Open: fan-out, salvo generators, zero-test logic, and gates in the classical NOT/AND/OR sense | `N-09`, `N-10`, `N-11` compiled |
| `G-6` | **Universal machine model in Lean.** A counter-machine model with compiled proof that it computes every partial recursive function in Mathlib's sense. Independent of Life. | supports `G-7` | **achieved** (2026-11-14): `exists_computes_code` | `N-14` compiled |
| `G-7` | **Turing completeness of Life.** For every program of the model of `G-6` a computable finite pattern with a compiled simulation theorem; corollaries: every `Nat.Partrec.Code` is computed by a finite pattern, and a stated natural predicate on finite configurations is not computable. Exact statement fixed by `N-12`. | supported by `G-5`, `G-6`; top-level | open; target statements fixed (`N-12`, `Decision.lean`); machine model done (`G-6`); the Life machine is being designed (`N-15`) | `N-15`, `N-16` compiled; scope statement; user confirmation of the statement (`A-4`) |
| `G-8` | **Self-replication.** A precise definition and a compiled proof that an explicit finite pattern satisfies it. | supported by `G-3`, `G-5`; top-level | postponed (activation rule in `N-17`: after `G-7` or its component theory, and once an explicit decomposable pattern is identified, or by user decision) | definition with sanity instances; compositional proof |
| `G-9` | **Readable universal programs (optional).** A small Lisp with Lean semantics compiled to the model of `G-6`, used to exhibit a universal program transparently. | supported by `G-6`; would decorate `G-7` | inactive, pending `Q-5` and user decision | to be defined if activated |

## 2. Question registry

| ID | Question | Needed by | Status | Current best answer / barrier |
| --- | --- | --- | --- | --- |
| `Q-1` | Which representation and coordinate convention does the kernel use? | `N-01`, then all | answered (user decision 2026-11-14) | `Finset (ℤ × ℤ)` as specification; `x` to the right, `y` downward as in RLE |
| `Q-2` | Should the kernel be parameterized by a Life-like rule (B/S sets) or fix B3/S23? | `N-01`, `N-17` | answered (user decision 2026-11-14) | Generic `Rule` with `conway` as the instance used everywhere |
| `Q-3` | What window size and number of generations can kernel-checked certificates (no `decide`) handle within the laptop budget? | `N-03`; `N-05`–`N-11` | answered (measured 2026-11-14) | 150 × 150 × 60 in 5 s; 300 × 300 × 240 in 56 s and 5.2 GB; cost ≈ linear in rows × generations; memory limits one declaration. Table in `N-03` |
| `Q-4` | What precisely is proved under "Life is Turing complete" on finite configurations? | `G-7`; `N-12`, `N-15`, `N-16` | answered in outline (user decision 2026-11-14) | Headline: an undecidable predicate on finite configurations plus computation of every partial recursive code, via simulation of counter machines. Exact Lean statements still to be fixed in `N-12` (read `S-14`) |
| `Q-5` | Direct Turing machine, register machine, or Lisp interpreter (user idea): which is easier and more transparent? | `G-7`; `N-13`, `N-10`, `N-14`, `N-15` | answered (user decision 2026-11-14) | Register machine (route R1 of `N-13`). Lisp is at most an optional top layer (`G-9`, inactive). Re-examine if `S-10` or `S-11` ch. 9 contradict the expected component list |
| `Q-6` | How is unbounded memory obtained with finite support? | `N-11`, `N-13`, `N-15` | answered (sources read, `R-18`) | Sliding block register with `INC` and `TDEC` (test, then decrement unless zero), as in the book `S-11` ch. 9; cell-exact reactions in `R-18` §4 |
| `Q-7` | Which circuit technology: clocked LWSS tiles (HOL4-verified design), period-30 glider streams, or stable circuitry? Is general logic needed at all for a register machine? | `N-10`, `N-15` | answered (user decision 2026-11-14) | Own design D1: gated, terminated period-30 streams of Gosper guns; no stable conduits; no transcription of the book's circuits (`N-15`, `N-10`) |
| `Q-8` | How are components specified and composed, and how are unbounded-time behaviours (a gun emitting forever) stated on finite configurations? | `N-07`, `N-08`, `N-09`–`N-11`, `N-15` | answered in a first form | Reaction records with footprints (`Reaction P Q n F`), composed in parallel when footprints are `FarApart 2`, in sequence, and placed by translation; invariants for unbounded time (`IsGun`, `pipeline`). Open: timing side conditions between signals, symmetries other than translation |
| `Q-9` | Where does cell-exact pattern data come from, with what provenance and licence? | `N-05`–`N-11`, `N-18` | answered (user decision 2026-11-14) | Patterns are found by our own search and certified; sources give guidance only. The two block salvos transcribed earlier are to be re-derived |
| `Q-10` | What is the right definition of self-replication, which explicit pattern would be proved, and is it feasible? | `G-8`; `N-17` | open | Definitions disputed in the sources; known patterns are ≈ 3 × 10⁵ cells with period ≈ 2 × 10⁸ |
| `Q-11` | What JSON schema, and what level of round-trip assurance (theorem at string level, at `Json` value level, or tests)? | `N-02` | answered | Round trip proved for JSON values, by `rfl` on RLE/plaintext fixtures, tested only at string level; schema in `N-02` |
| `Q-12` | How is counter-machine universality linked to Mathlib: from `Nat.Partrec.Code` directly or via `Turing.TM2`? | `N-14` | answered | Via Mathlib's vector basis `Nat.Partrec'` and a structured loop language compiled to counter programs; no pairing or Gödel numbering needed (`N-14`) |

## 3. Note registry and dependency graph

| ID | Note | Addresses | Depends on | Difficulty | Status / Lean readiness | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| `N-01` | [Kernel](research/N-01-kernel.md) | `G-1`; `Q-1`, `Q-2` | Mathlib | routine–moderate | **verified** (commit `0ae423d`) | none; re-audit on any kernel change |
| `N-02` | [Snapshots and serialization](research/N-02-snapshots-serialization.md) | `G-2`; `Q-11` | `N-01` | routine | **verified** with stated gaps | optional: prove `trim` is a normal form using `ofRows_inj` |
| `N-03` | [Certified simulation engine](research/N-03-certified-simulation.md) | `G-3`; `Q-3` | `N-01`; template tactics (compiled) | moderate | **verified** (commits `584f5bb`, `47f841c`) | none; precompile the `meta` simulation if runs get long |
| `N-04` | [Locality and composition](research/N-04-locality-composition.md) | `G-3` | `N-01` | moderate | **verified** (commit `584f5bb`) | none |
| `N-05` | [Still lifes and oscillators](research/N-05-still-lifes-oscillators.md) | `G-4` | `N-01`, `N-03` | routine | **verified** for the initial list (commit `47f841c`) | optional extensions (traffic light as four blinkers, T-tetromino) |
| `N-06` | [Spaceships](research/N-06-spaceships.md) | `G-4` | `N-01`, `N-03`, `N-04` | routine | **verified** for one orientation each (commit `47f841c`) | other orientations and the `gliderAt` family, with `N-07` |
| `N-07` | [Guns and streams](research/N-07-guns-streams.md) | `G-4`; `Q-8` | `N-03`, `N-04`, `N-06` | moderate | **verified** | gun with eater; other orientations (optional) |
| `N-08` | [Component interfaces](research/N-08-component-interfaces.md) | `G-3`, `G-5`; `Q-8` | `N-04`; informed by `N-07` | hard | first form **verified**: `Reaction` calculus, boxes, and certificates that deliver boxes (`life_reaction`) | timing side conditions; symmetries in `Reaction` |
| `N-09` | [Elementary reactions](research/N-09-elementary-reactions.md) | `G-5` | `N-03`, `N-05`, `N-06`, `N-08`, `N-18` | routine each | **verified** for absorption, annihilation, kickback, zero test (`Collisions.lean`) | stream versions as reactions with footprints |
| `N-10` | [Logic gates and wiring](research/N-10-logic-gates.md) | `G-5`; `Q-7` | `N-08`, `N-09`, `N-13`, `N-18` | hard | partly **verified**: terminated gun, blocked stream, gate, reflector (`Gates.lean`, `SalvoGenerator.lean`) | fan-out as a separate certified component; gates with repeated controls |
| `N-11` | [Sliding block memory](research/N-11-sliding-block-memory.md) | `G-5`; `Q-6` | `N-03`, `N-04`, `N-05`, `N-06`, `N-08`, `N-18` | moderate | partly **verified**: `pull`, `push`, `pipeline`, zero test (`zeroTest_hit`, `zeroTest_pass`); generators open | salvo generators (search running); zero-test logic |
| `N-12` | [Meaning of universality](research/N-12-meaning-of-universality.md) | `G-7`; `Q-4` | Mathlib (compiled); `N-01` (types only) | moderate | stated: exact Lean targets fixed and type-checked; `Decision.lean` compiled (definitions and reduction) | decoding clause of T2; `Computable` for the pattern family, when the layout exists |
| `N-13` | [Route assessment](research/N-13-route-assessment.md) | `G-7`; `Q-5`, `Q-6` | `N-12`; sources | moderate | decided: route R1 (user), confirmed against the sources (`R-18`); circuitry by own design (user) | none |
| `N-14` | [Counter machines](research/N-14-counter-machines.md) | `G-6`; `Q-12` | Mathlib (compiled); `N-13` (conditional) | hard | **verified** | none |
| `N-15` | [Register machine in Life](research/N-15-register-machine-in-life.md) | `G-7` | `N-08`, `N-10`, `N-11`, `N-12`, `N-13`, `N-14` | research-level engineering | exploratory: design D1; **certified** components include a generator of the pulling salvo (`pullGenerator_reaction`); push generator, continue signal, zero-test logic, layout open | decrement instruction with the block for every `k`; then push generator |
| `N-16` | [Universality theorem](research/N-16-universality-theorem.md) | `G-7` | `N-12`, `N-14`, `N-15` | moderate | blocked on `N-15`; the reduction step is compiled (`not_computablePred_everAlive_of_family`) | — |
| `N-17` | [Self-replication](research/N-17-self-replication.md) | `G-8`; `Q-10` | `N-01`, `N-04` (types); sources | research | exploratory; sources surveyed (`R-18` §E); formal goal postponed | Draft definitions when `G-8` is activated |
| `N-18` | [Source acquisition](research/N-18-source-acquisition.md) | `Q-9` | none | routine | largely done: reports `R-18` (sources), `R-19`, `R-20` (own searches); literature check on salvo generators in `N-15` | licences only matter if external patterns are ever used; remaining unread sources (`S-02`, `S-03`, `S-09`) only if needed |

Dependency graph (an arrow means "is needed by"). Edges out of `N-01`–`N-07` and `N-14` are
**established** (compiled); edges out of `N-08`–`N-12` are established for the parts listed as
verified above; every edge into `N-15` and `N-16` is unverified:

```text
N-01 ──► N-02
N-01 ──► N-03 ──► N-05 ──► N-09 ──► N-10 ──► N-15 ──► N-16
N-01 ──► N-04 ──► N-06 ──► N-07 ──► N-08 ──► N-09, N-10, N-11, N-15
N-03 ──► N-06, N-07, N-09, N-11        N-04 ──► N-07, N-08, N-11, N-17
N-06 ──► N-09, N-11                    N-05 ──► N-11        N-11 ──► N-15
N-12 ──► N-13 ──► N-10, N-14, N-15     N-12 ──► N-15, N-16
N-14 ──► N-15, N-16                    N-18 ──► N-09, N-10, N-11, N-13, N-17 (data and sources)
```

A dependency is established only when its required output is a compiled Lean declaration that
has passed the required audit. A note may explore a conditional dependency, but the edge and all
downstream status remain marked unverified.

## 4. Strict audit status

The canonical first command is `start`. Record the audit before new theory builds on the checkout.

| Audit | Value |
| --- | --- |
| Audited commit | Kernel: `0ae423d` (unchanged since). Later modules are checked after each work unit by a full build and the axiom audit; last full check: see the progress log entry "notes update" below. First audit: `bf3e472` (template) |
| Scope | Full startup audit of the template at `bf3e472`; then every change since: the new modules `Kernel/Life.lean` and `Sanity/Life.lean` (no existing module was modified apart from the import list in `LeanTheory.lean`) |
| Kernel coverage | Complete. **`Kernel/Life.lean`**: every declaration reviewed (`Cell`, `nbrs`, `liveNbrs`, `Rule`, `conway`, `Rule.step`, `Rule.evolve`, `liveNbrsSet`, `stepSetCore`, `Rule.stepSet`, `mem_nbrs`, `notMem_nbrs_self`, `mem_nbrs_comm`, `liveNbrs_ne_zero`, `Rule.mem_step`, the `evolve` lemmas). Red-team points: neighbourhood shape checked three ways (`mem_nbrs_iff_max`, `nbrs_eq`, `card_nbrs`); the filter over `S ∪ S.biUnion nbrs` loses no cell because `Rule` excludes birth at zero neighbours (`Rule.mem_step`; necessity shown by `not_finite_stepSetCore_birth_zero`); the totalized `ncard` in the specification is always applied to a finite set (`liveNbrsSet_le_eight`); the specification is exercised on an infinite set (`conway_stepSet_univ`); `conway` is B3/S23 by definition. **`Kernel/Example.lean`** (template) (`OscParams`, `energy`, `OscillatorLaw`, `energy_nonneg`, `hasDerivAt_energy`, `energy_conserved`, `potential_le_energy`); every declaration reviewed. Fields consistent (`m > 0`, `k ≥ 0`), no division by an unguarded quantity (`k / m` with `m > 0`), law quantified over all `t`, conclusions match docstrings |
| Commands run | At `bf3e472`: `lake exe cache get` (Mathlib cache fetched; Lean 4.35.0 already installed); `lake build`: 3241 jobs, success, 0 warnings; `lake env lean scripts/check_axioms.lean`: passed for 6013 declarations; repo grep: no `axiom`/`sorry`/`admit`/`native_decide`; `decide` occurs only as the Bool function inside computable checkers. At `0ae423d`: `lake build`: 3243 jobs, success, 0 warnings; axiom audit passed for 6178 declarations (only `propext`, `Classical.choice`, `Quot.sound`); `#print axioms` on `Rule.mem_step`, `Rule.coe_step`, `conway_step_block`, `conway_step_blinkerH`, `Rule.step_map`, `Rule.exists_near_of_mem_evolve`; grep of the two new files: no `sorry`/`admit`/`axiom`/`decide` |
| Open findings | None (no critical/major/minor findings). Observation, not a defect: two `Rule` values differing only in counts above eight define the same dynamics. Note: the general certificate/theory library (KAM, Kronecker, Suydam, …) is domain-independent template machinery, checked by build and axiom audit but not semantically re-audited against a domain since none is defined |
| Missing sanity checks | None for the example kernel: triad (`free_velocity_const`, `instOscillatorLawCos`, `not_oscillatorLaw_exp`) plus risk-specific symmetry/linearity checks (`OscillatorLaw.shift/add/smul`) and certificate fixtures (`initialStates_energy_le` / `initialStates_not_le_small`). For the Life kernel: degenerate cases, concrete instances, counterexamples and the adversarial checks of `N-01` items 1–7 are all compiled (list in `N-01`). Deferred to `N-04` (not kernel defects): symmetry and locality for `evolve` rather than one step |

Changes since the kernel audit (`0ae423d`): no kernel or sanity file changed. New non-kernel
modules, each checked at `47f841c` by `lake build` (3250 jobs, 0 warnings) and the axiom audit
(6677 declarations, standard axioms only):

- `Certificates/LifeSim.lean`, `Certificates/LifeCert.lean`: certificate soundness theorems
  (`step_ofRows`, `RowsStep.eq`, `Padded.ofRows_eq`, `Tagged.eq`, `Evolves.sound`, `ofRows_inj`)
  reviewed; fixtures include an accepted, a rejected and an empty-result case; the encoding is
  checked against explicit cells (`mem_ofRows_glider`) and the bit formula against the rule in
  all 512 cases (`nextBit_eq_ruleB`). The `meta` builder is untrusted.
- `Theory/Life/Locality.lean` (sub-agent work): statements of all main theorems read against
  `N-04`; sharpness counterexample present.
- `Theory/Life/Patterns.lean`: definitions of the three classes reviewed; each has a negative
  instance or an exactness clause.

- `Theory/Life/Guns.lean`, `SlidingBlock.lean`, `Reactions.lean`: main statements reviewed;
  each has negative fixtures (`not_isGun_block`, `pull_misplaced_block_ne`,
  `not_reaction_blinker`).
- `Bridge/LifeIO.lean`, `Theory/Computability/*.lean` (sub-agent work): compiled and audited
  for axioms by the coordinator; definitions and main statements read; proofs not re-read line
  by line.

- `Theory/Life/Collisions.lean`, `Gates.lean`, `Boxes.lean`, `Decision.lean` (coordinator) and
  `Register.lean` (sub-agent): compiled; main statements reviewed; negative fixtures present
  (`gate_wrong_lane_ne`, `zeroTest_hit_displaces`, `two_ops_inc_inc_ten_ne`,
  `boxCheck_fixture_false`). The geometries in `Collisions` and `Gates` come from untrusted
  search scripts; their only authority is the certificate.

Observation recorded for later audits: pattern data other than the traffic light and the Gosper
gun were written from memory; they are validated by the theorems about them, not by a source.

Previous code is in scope. A full startup audit inventories and red-teams every kernel declaration,
then traces findings into dependent results. After a kernel or foundational change, update the
audited commit only after rechecking affected code. Unresolved kernel findings block dependent
items from verified status.

## 5. Corrections and assumption ledger

The assumption ledger (`A-1`–`A-8`) and the table of sourced claims are in
[`sources.md`](sources.md). Corrections to loose starting claims:

| ID | Loose claim | Precise replacement |
| --- | --- | --- |
| `C-1` | "Life is a Turing machine" | Life is a dynamical system. The claim to prove: every program of a universal machine model is simulated by a computable family of finite configurations, and consequently a stated predicate on finite configurations is undecidable (`N-12`) |
| `C-2` | "Computers built in Life (Lisp in Life, CPUs) show Turing completeness" | The retrieved descriptions give bounded memory (10-bit RAM addresses in `S-12`; 16 four-bit registers in `S-08`). They are finite-state demonstrations; universality needs unbounded memory |
| `C-3` | "Rendell built a Turing machine in Life" | The 2000 pattern needs an infinite tape pattern (or has a finite tape); only the 2011 version is reported to start from a finite pattern, growing its tape by construction (`S-05`, snippet) |
| `C-4` | "A gun has period 30" | A gun on a finite configuration is not periodic: population grows without bound. Statement: gun plus `n` emitted gliders evolves in 30 generations to gun plus `n + 1` (`N-07`) |
| `C-5` | "A glider moves one cell diagonally every 4 generations" | True for an isolated glider with a stated orientation convention; in a larger configuration it needs a separation hypothesis (`N-04`, `N-06`) |
| `C-6` | "Life can simulate itself / any automaton via metacells, hence is universal" | Metacell tilings are infinite configurations (dead OTCA or HOL4 mega-cells still contain circuitry), excluded by the finite-support requirement `A-2`; `S-07` proves self-simulation, not Turing completeness |
| `C-7` | "Self-replication in Life is proved" | Conway's argument is reported as an existence sketch; explicit patterns are a self-constructing spaceship (Gemini), a disputed linear propagator, and metacell-based designs. A definition must be fixed first (`N-17`) |
| `C-8` | "Only finitely many cells are filled at each time" as an extra hypothesis on evolutions | It is a property of the initial configuration alone: `step` preserves finiteness (speed of light, `N-01` item 6). It restricts which constructions are admissible, not the dynamics |
| `C-9` | "Finite pattern" suggests bounded | A universal finite-support construction must use unbounded space: a configuration confined to a fixed region is eventually periodic (`N-04` item 7). Population may stay bounded (sliding block memory) |

## 6. Theory tracks and model ladder

| Track | Notes | Verified frontier | First useful deliverable |
| --- | --- | --- | --- |
| A. Foundations | `N-01`–`N-04` | all verified: `Rule.mem_step`, `Rule.coe_step`, `step_ofRows`, `Evolves.sound`, `Rule.evolve_union_of_forall_sep`, `Rule.evolve_translate`, `Rule.eventually_periodic_of_bounded`; serialization | optional: `trim` as a normal form |
| B. Pattern catalogue | `N-05`–`N-07` | all verified: `Pattern.glider_isSpaceship`, `Pattern.pentadecathlon_isOscillator`, `gosperGun_evolve` | optional extensions |
| C. Components | `N-08`–`N-11` | `Reaction.par`, `pull`, `push`, `pipeline`, `zeroTest_pass`, `eater_absorbs_glider`, `glider_kickback`, `blockedStream_isOscillator`, `gate`, `gate_reaction` | a salvo generator from one control glider |
| D. Computation | `N-12`–`N-16` | `exists_computes_code`, `exists_program_halts_not_computable`, `not_computablePred_everAlive_of_family` | one instruction of the Life machine as a reaction |
| E. Self-replication | `N-17` | none | Definitions with negative instances (postponed) |
| F. Sources and searches | `N-18` | reports `R-18`, `R-19`, `R-20` | `R-21` (salvo generators) |

Model ladder (each arrow needs a compiled theorem):

1. `stepSet` on arbitrary `Set (ℤ × ℤ)` (specification) ⇄ `step` on `Finset (ℤ × ℤ)` (kernel):
   equality on finite sets (`N-01`).
2. `step` ⇄ bit-row `stepRows` in a window enlarged by one cell on each side: unconditional
   refinement `step_ofRows` (`N-03`).
3. Window certificates ⇒ behaviour inside larger configurations: locality and independence
   (`N-04`), then reactions with footprints (`N-08`).
4. Components ⇒ counter machine: compilation and simulation (`N-15`).
5. Counter machine ⇒ partial recursive functions: `N-14`.
6. Simulation ⇒ undecidability: `N-16`.

## 7. Work selection

Interactive mode: after each work unit report status and ask the user to choose a ready note, a
goal/question or a topic for discussion. Record user ideas and sources in the affected notes
(`add notes`/`modify notes` for a discussion, `update notes from ...` for files or URLs); changes to
implemented notes become separate code patch notes.

Autonomous mode (`keep working`): choose the highest-value ready note, preferring work that
unblocks several dependants, closes a validity gap, tests a risky conjecture or produces a reusable
theorem. Continue across work units without waiting for a choice; stop for a genuine user decision,
missing authorization or absence of useful ready work.

Current priority order (provisional):

1. Salvo generator and fan-out: certify the outcome of the running search (`R-21`), or redirect
   it (always-firing shotgun with suppression, a period-120 clock, a reflector found by search).
2. The zero-test logic: turning "test glider survived / was consumed" into a glider on an `NZ`
   or a `Z` lane, with the restoring glider sent only after a positive test (or the three-glider
   test, whose passage for `k ≥ 1` still needs a certificate).
3. One complete instruction (`inc r`, then `decJz r l`) as a `Reaction`, with boxes.
4. Layout of a program and the simulation theorem (`N-15`); then `N-16`.
5. Side work that is ready at any time: gate with repeated controls and gates in series
   (observed in `R-20`), the train of operations as a `Reaction`, `trim` as a normal form.

## 8. Running a work unit

1. Resolve the selected `G-*`, `Q-*`, `N-*` or discussion topic to one coherent task.
2. Check dependency evidence and read the relevant notes, sources and compiled declarations.
3. Perform literature study, discovery, proof, counterexample search, computation, formalization or
   certification as appropriate to readiness.
4. Compile and strictly audit Lean output. For foundational changes, include existing affected
   code and add risk-specific or regression sanity checks. Do not promote an output to verified on
   informal evidence or on compilation alone.
5. Update the note graph, registries, barriers and this progress log.
6. Report verified and unverified outcomes separately and identify ready next work.

## 9. Definition of done

For a research note: claims and evidence are classified, dependencies and barriers are current,
outputs are recorded, and the next readiness-changing action is explicit.

For a verified result: declarations compile with docstrings and sanity theorems, zero warnings,
the axiom audit passes, semantic audit findings are resolved, entry points are registered, and the
note gives an honest scope statement. Kernel laws have the sanity triad plus risk-specific checks.

For a goal: all required contracts hold for compatible witnesses and models, and every claimed
dependency is backed by the recorded level of evidence. A formal theorem alone does not validate
the physical model.

## 10. Evidence gates

There are no empirical inputs; every gate is a compiled proof.

| Goal | Contracts that must hold together | Evidence |
| --- | --- | --- |
| `G-1` | `step` equals the set-level specification; sanity suite of `N-01` | compiled theorems; strict kernel audit |
| `G-4` | Each named pattern's theorem refers to the kernel `evolve` (not to a window model) | certificate plus refinement theorem (`N-03`) for the same cells |
| `G-5` | Each component theorem is in the `N-08` format, so that the composition theorem applies; all components of one machine use one coordinate and timing convention | compiled theorems; negative fixtures |
| `G-7` | The same `compile` and `enc` functions appear in the simulation theorem, the computability proof and the undecidability reduction; the machine model is the one proved universal in `G-6` | compiled theorems; axiom audit; user-confirmed statement |
| `G-8` | The pattern satisfies the fixed definition, which is shown to exclude spaceships and guns | compiled theorems |

## 11. Progress log

- **2026-11-14 — startup audit.** Fetched the Mathlib cache; full build (3241 jobs, 0 warnings);
  axiom audit passed (6013 declarations); complete review of the example kernel; no findings.
  Recorded in §4.
- **2026-11-14 — project seeded.** Read the user's seed request. Retrieved sources: `S-07` read
  in full (arXiv v1); `S-04`, `S-12`, `S-08` part 4 and four LifeWiki mirror pages by summary;
  others by snippet (levels recorded in `sources.md`). `conwaylife.com` and the UWE repository
  refused automated access. Checked the pinned Mathlib: Turing machine and halting-problem
  results present; no counter machine or cellular automaton development. Created goals
  `G-1`–`G-9`, questions `Q-1`–`Q-12`, corrections `C-1`–`C-9`, assumptions `A-1`–`A-8`, notes
  `N-01`–`N-18`. Recorded a preliminary (undecided) assessment of the Lisp route in `N-13`.
  No Lean code written; nothing verified. Ready: `N-01`, `N-12`, `N-13`, `N-18`; conditionally
  `N-14`; survey part of `N-17`.
- **2026-11-14 — decisions.** The user accepted the recommendations for the open ambiguities:
  `Q-1`, `Q-2` (kernel conventions), `Q-4` (headline statement), `Q-5`/`Q-6` (register machine
  with sliding block memory; Lisp route not taken, `G-9` stays inactive), `Q-9` (mirror and
  provenance rule). `Q-3` remains to be measured in `N-03`. Notes `N-01`, `N-12`, `N-13`
  updated; no Lean code yet.
- **2026-11-14 — `N-01` kernel.** Wrote `LeanTheory/Kernel/Life.lean` and
  `LeanTheory/Sanity/Life.lean` (commit `0ae423d`). Compiled: the rule cell by cell
  (`Rule.mem_step`), agreement with the set-level specification (`Rule.coe_step`), block still
  life, blinker of period two, three counterexamples, one-step symmetry, speed of light. Design
  change found while proving: `Rule` needs the field `zero_notMem_birth`, with a compiled
  theorem showing it is necessary. Checks: full build 0 warnings, axiom audit 6178
  declarations. `G-1` achieved; `N-02`, `N-03`, `N-04` are now ready. Small patterns were
  proved by `interval_cases` and `simp`, which will not scale: `N-03` is the next priority.
- **2026-11-14 — `N-03` simulation engine** (autonomous mode). `Certificates/LifeSim.lean`,
  `LifeCert.lean`; tactics `life_cert`, `life_eval`. Finding: Lean hashes `Nat` literals by
  their low 64 bits; wide sparse rows made kernel checking superlinear (gun × 600: 134 s);
  fixed by storing rows as tagged literals (1.6 s). `Q-3` answered by the benchmark in `N-03`.
- **2026-11-14 — `N-04` locality** (sub-agent, checked by the coordinator).
  `Theory/Life/Locality.lean`; separation constants: `Sep 2` for one step (sharp), `Sep (2n)`
  for `n` steps.
- **2026-11-14 — `N-05`, `N-06` catalogue.** `Theory/Life/Patterns.lean`: 16 patterns with
  exact periods and displacements; `ofRows_inj` (uniqueness of trimmed windows) added to prove
  exactness.
- **2026-11-14 — `N-18` sources** (sub-agent). Report `reports/R-18-source-report.md`: route R1
  confirmed; the register is a 2316-cell stable circuit (`INC`, `TDEC`), no gate network is
  needed, latches are; Durand–Róka report a gap in Conway's argument concerning free-running
  guns. Notes `N-10`–`N-13`, `N-17` and `sources.md` updated. Sub-agents started for `N-02`
  and `N-14`.
- **2026-11-14 — `N-07` Gosper gun.** `Theory/Life/Guns.lean`: `gosperGun_evolve` (the gun with
  its `n` emitted gliders after `30 n` generations, for all `n`), `IsGun`, `gosperGun_isGun`,
  `gosperGun_not_bounded`. First theorem combining certificates, a signal-in-flight lemma and
  independence along a run; `G-4` achieved for its stated list.
- **2026-11-14 — `N-02` serialization** (sub-agent, checked by the coordinator).
  `Bridge/LifeIO.lean`: `Snapshot`, `Evolution`, `Repr`/`ToJson`/`FromJson`, RLE, plaintext,
  `rle%`/`cells%`; `G-2` achieved; `Q-11` answered.
- **2026-11-14 — `N-11` block reactions.** `Theory/Life/SlidingBlock.lean`: `pull` and `push`
  for every block position, via the flight lemma `evolve_flight`. First compiled ingredient of
  `G-5`.
- **2026-11-14 — `N-14` counter machines** (sub-agent, checked by the coordinator).
  `Theory/Computability/CounterMachine*.lean`: `exists_computes_code` (every
  `Nat.Partrec.Code` is computed by a counter program with `inc`, `decJz`, `halt`) and
  `exists_program_halts_not_computable`. `G-6` achieved; `Q-12` answered.
- **2026-11-14 — `N-08` first calculus.** `Theory/Life/Reactions.lean`: reactions with
  footprints, parallel and sequential composition, placement; `pull_reaction`.
- **State at the end of this autonomous run.** Verified: `N-01`–`N-07`, `N-14`, parts of `N-08`
  and `N-11`. Goals `G-1`, `G-2`, `G-4`, `G-6` achieved. Full build 3268 jobs, 0 warnings;
  axiom audit 7800 declarations. Stopped for a user decision on how to obtain the register and
  control circuitry (see §0).
- **2026-11-14 — decision.** The user chose an own design (no copying from the book). Design D1
  recorded in `N-15`; `Q-7`, `Q-9` answered; search for the elementary reactions started.
- **2026-11-14 — `N-12` statements; boxes; pipelining.** `Theory/Life/Decision.lean` (exact
  targets `EverAlive`, reduction lemma); `Theory/Life/Boxes.lean` (rectangular footprints);
  `Theory/Life/Register.lean` (sub-agent): `pipeline`, operations launched at least 13 cells
  apart act on the block in order.
- **2026-11-14 — first components of design D1.** Own search (`scripts/life_gates`, report
  `R-20`, sub-agent) found, and `Theory/Life/Gates.lean` certifies: the gun terminated by an
  eater and the blocked stream of two guns (oscillators of period exactly 30) and a gate
  (`gate`: a control glider releases exactly one glider).
- **2026-11-14 — elementary reactions.** Own exhaustive search (`scripts/life_search`, report
  `R-19`, sub-agent); `Theory/Life/Collisions.lean` certifies absorption, annihilation,
  kickback and the zero test, including `zeroTest_pass` for every position `k ≥ 1`. The block
  salvos were rediscovered by the search (provenance updated).
- **2026-11-14 — gate footprints; literature check.** `blockedStream_reaction` and
  `gate_reaction` (boxes). At the user's request a web search established that the salvo
  generator exists in the literature in three technologies (recorded in `N-15`); the ideas, not
  the patterns, were passed to the running search.
- **2026-11-14 — salvo generator.** `Theory/Life/BoxCert.lean` (certificates that deliver a box
  for every generation; tactic `life_reaction`) and `Theory/Life/SalvoGenerator.lean`:
  `reflector` and `pullGenerator_reaction` (one control glider ⟶ the pulling salvo in 1170
  generations, generator back in its cycle, all inside a stated box), from the search report
  `R-21` (sub-agent). The search also reports obstructions that shape the layout: gun shadow,
  uncrossable period-30 streams, parity.
- **2026-11-14 — notes update** (user request). Registries, §0, §6, §7, `sources.md`, the
  model contracts and the notes `N-13`, `N-16`, `N-18` brought in line with the state of the
  library. Full check at this point: `lake build` 3273 jobs, 0 warnings; axiom
  audit passed for 8137 declarations (standard axioms only), at commit `11ca127` plus
  documentation.

## 12. Implementation and workstation log

- 2026-11-14: Lean 4.35.0, Mathlib `v4.35.0`. Full template build ≈ 1.5 min wall-clock on the
  laptop (22 cores, 23 GB) with the Mathlib cache. Workstation pipeline not used.
- 2026-11-14: `Sanity/Life.lean` builds in ≈ 3 s; the block and blinker proofs enumerate 12–16
  cells each by `interval_cases` and `simp`.
- Benchmark table for `Q-3`: in `research/N-03-certified-simulation.md` ("Results").
- Kernel performance note: every `Nat` literal in a large proof term should have distinguishing
  low 64 bits (see `Certificates/LifeSim.lean`, section on certificates).
