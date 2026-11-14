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
| Status | exploratory: own design D1 drafted (2026-11-14); components not yet found or verified |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: user decision (own design); architecture D1 drafted |

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

## User decision and design D1 (2026-11-14)

**Decision (user).** The circuitry is to be designed in this project from verified elementary
reactions; the book (`S-11`) is used for inspiration and guidance, and nothing is copied
exactly. Consequences: the book's register circuit and its stable conduits are not transcribed;
every component is found by our own search (an untrusted oracle under `scripts/`) and enters
the library only through a certificate.

**Design D1: guns, eaters, blocks and gliders only.** The elementary objects are the ones
already verified (`Pattern.glider`, `Pattern.block`, `Pattern.eater1`, `gosperGun`), and the
reactions needed are few:

1. *absorption*: an eater destroys a glider and recovers (ends every stream);
2. *annihilation*: two gliders meeting at a right angle (or head-on) destroy each other;
3. *kickback*: a collision of two gliders leaving one glider that travels back;
4. *block pull and push* (compiled: `pull`, `push`) and a *zero test* at the fixed zero
   position (a glider is consumed by the block there and passes when the block is elsewhere).

Components built from them:

- **Blocked stream** (a period-30 or period-60 bounded assembly): gun `A` fires at a target,
  gun `B` fires across and annihilates every glider of `A`; all streams end in annihilation
  or in an eater. One certificate over a period shows it is an oscillator.
- **Gate**: a control glider deletes one glider of `B`; the corresponding glider of `A`
  escapes. This re-times the signal to the clock of the guns, turns it in any of the four
  directions and moves it to any lane, so no separate reflector is needed.
- **Fan-out**: the control glider is kicked back from one `B`-stream to the next, releasing one
  glider at each; or a released glider gates a further blocked stream.
- **Salvo generator**: a fan-out whose released gliders are aligned, by the positions of the
  guns, to the pulling or pushing salvo.
- **Zero test**: test gliders aimed at the zero position; presence or absence of the survivor
  is turned into a glider on a `Z` or an `NZ` lane by one more gate (an absent glider fails to
  delete a blocking glider).
- **Instruction**: `inc r` = salvo generator for register `r` plus a released glider that goes
  on to the next instruction; `decJz r l` = zero test, then on `NZ` a pull salvo and the next
  instruction, on `Z` a glider to instruction `l`.
- **Program counter**: one glider (one occupied slot of the clock lattice).

Signals are therefore synchronous with the period of the guns, in the manner of the classical
argument and of Chapman's first machine, but every stream is terminated, which answers the
objection of Durand–Róka (`S-14`) about parasitic outputs.

**Timing does not depend on the register contents.** An operation on a block at position `k`
takes `4 k + 26` or `4 k + 32` generations, but the control signal need not wait for it: salvos
fly at the same speed one behind the other and arrive in the order of launch, and the zero test
looks only at the fixed zero position. The invariant to prove is: *logical value = block
position + pending pushes − pending pulls, and whenever the logical value is 0 there is no
pending salvo* — which holds if consecutive operations on a register are launched more than
about 30 generations apart (a pull that brings the block to 0 completes in 30 generations).
The simulation theorem can then use a duration per instruction that is independent of the
configuration; the encoding of a configuration must allow salvos in flight.

**Proof structure.** Each component is an oscillator (certificate) together with a reaction
(certificate) "component + input glider at the right phase ⟶ component + output gliders"; the
machine is the union of translated components with the reaction calculus of `N-08` (which needs
rectangular footprints for this). Layout and timing are computed by a function of the program
and proved correct by induction on the program.

**What must be found by search** (`scripts/`, results as numerical observations until
certified): the collision geometries 1–3, a zero-test reaction, relative placements of two guns
whose streams annihilate, the gate geometry, and placements realizing the two salvos.

**Risks.** (i) Phase and parity constraints: gliders of a period-30 stream alternate between
two phases, and path lengths change delays in steps of a few generations, so some required
alignments may be impossible without a period-60 or period-120 clock or an extra component.
(ii) The size of the layout proof. (iii) The salvos now in `Theory/Life/SlidingBlock.lean` were
transcribed from the book's Fig. 8.37 via `R-18`; they are two- and three-glider collisions with
a block (facts about the rule rather than a design), but to respect the decision they should be
re-derived by our own search and their provenance comment updated.

## Literature check on the salvo generator (2026-11-14, at the user's request)

Question: has the part "one signal in, a block salvo out" been worked out publicly? Yes, at
least three times, in different technologies (web search plus the sources read for `R-18`):

1. **Conway, 1982** (*Winning Ways*, outline only; not retrieved). Gliders are put on any lane
   with any timing by *side-tracking*, built on the kickback reaction (LifeWiki mirror page
   "Side-tracking"; Life Lexicon). No explicit pattern was published; secondary sources call
   the resulting guns slow and complicated.
2. **Hickerson, 1990** (`S-21`, read for `R-18` §B2). An explicit gun-based design: a
   "shotgun" of four period-120 guns, four period-30 guns, four buckaroos (period-30
   reflectors made from the queen bee shuttle) and two rephaser blocks fires, every 120
   generations, a four-glider salvo containing both the increment and the decrement salvo;
   suppressor streams delete all of it unless an external signal removes a suppressor glider;
   a detector glider reports the transition from 1 to 0. Test pattern: 1685 cells, 240 × 192.
   He notes that the period-120 guns used are obsolete.
3. **Chapman, 2002** (`S-10`). His register wraps Hickerson's unit with period-60-to-120
   converters, buckaroo ladders and signal duplicators.
4. **Johnston–Greene / Goucher** (`S-11` ch. 9): the same function with stable conduits and no
   guns.

Not accessible this time: Hickerson's page directly (TLS error; it was read earlier for
`R-18`), Rendell's thesis (HTTP 403), *Winning Ways*.

Relevance to design D1. Our own search hit exactly the obstruction these designs deal with: two
guns cannot fire on lanes only six apart, so not every salvo glider can come straight from a
gun. The literature's answers are (a) a reflector that brings a glider in from the side, (b)
side-tracking by kickbacks, (c) a slower clock (period 120), and (d) an always-firing shotgun
with suppression instead of generation on demand — which is our certified `gate` applied to the
salvo. In keeping with the user's decision these are used as ideas only; geometries are found
by our own search. The running search has been given these four ideas.

## Claims and evidence

No claims beyond the sourced existence of Chapman's pattern.

## Difficulty, barriers and readiness

Blocked. The smallest step that changes readiness: `N-13` decision plus reading `S-10` and
`S-11` ch. 9 to replace the sketch by an actual component list.

## Outputs and next dependencies

Feeds `N-16`.
