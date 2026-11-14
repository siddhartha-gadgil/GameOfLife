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
| Status | exploratory: design D1; certified so far: blocked stream, gate, reflector, zero test, block operations, and a generator of the pulling salvo; push generator, continue signal, zero-test logic and the layout are open |
| Implementation status | in progress (components only) |
| Implementation evidence | `LeanTheory/Theory/Life/Gates.lean`, `Collisions.lean`, `SalvoGenerator.lean`, `SlidingBlock.lean`, `Register.lean` |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: push generator and `increment` certified |

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

## Salvo generator: found and certified (2026-11-14)

The search `scripts/life_machine` (report `R-21`, sub-agent) found, and
`Theory/Life/SalvoGenerator.lean` certifies:

- `reflector`: the queen bee shuttle of the gun with an eater, period exactly 30, turning a
  glider by a right angle (`reflector_reflects`). Its eight images give all right-angle turns
  (observation).
- `pullGenerator`: six guns (three blocked pairs) and three reflectors in a 177 × 133 box,
  period 30. `pullGenerator_reaction`: one control glider gives, 1170 generations later, the
  generator back in its cycle together with exactly `translate (51, 143) pullSalvo`, and during
  that time the whole configuration stays in the box `-86 ≤ x ≤ 90`, `-9 ≤ y ≤ 152`.

How the design differs from the draft D1 above (findings of `R-21`, observations):

1. *Gun shadow*: no glider can pass a gun within about 24 lanes of its stream, so "one gate
   per salvo glider" is impossible (the salvo lanes are 6 apart).
2. *A period-30 stream cannot be crossed at a right angle* by a glider, so signal routing is
   planar; a kicked-back glider can only return to its source gate, which is why the fan-out is
   a round trip through the first gate (77 placements verified by simulation; not yet certified
   separately — it is part of `pullGenerator`).
3. *Parity*: kickbacks keep the timing parity and a reflection flips lane and timing parity
   together, so two fan-out outputs cannot be brought to the salvo by reflectors alone; a third
   gate re-times one path.
4. A period-60 or 120 clock was not needed for the pulling salvo.
5. By simulation the generator can be used again after 330 generations (not after 300), and
   with a block at `translate (100, 192) (counter k)`, `k = 0..3`, the block ends at `k - 1`.

**Decrement for every position (compiled, `Theory/Life/Decrement.lean`).** With
`registerBlock k := translate (51, 143) (counter k)`:

`decrement : ∀ k ≥ 1, conway.evolve (1170 + 4 * (k + 8))
  (pullGenerator ∪ pullGeneratorControl ∪ registerBlock k) =
  conway.evolve (4 * (k + 8)) pullGenerator ∪ registerBlock (k - 1)`.

One control glider, the generator and a block arbitrarily far away: the block moves one step
closer, the generator stays in its cycle, nothing else is left; `decrement_reaction` adds a
footprint for all intermediate generations. It is assembled by `Reaction.par` and `Reaction.seq`
from `pullGenerator_reaction`, the resting block, the generator at rest
(`reaction_of_periodic`) and the salvo's flight and reaction (`Op.reaction`). This is the first
use of the calculus on a real multi-component configuration. `k = 0` is excluded (the block
would be within two rows of the generator's box).

Still open for one complete instruction: repeated use; a generator for
the pushing salvo (three gliders; estimated by the search at about ten guns and five or six
reflectors); a "continue" glider; the zero-test logic.

## Continue glider, push generator, zero-test logic (2026-11-14, report `R-22`)

Search `scripts/life_machine` (sub-agent), observations by full simulation, not yet certified:

- **Continue glider: found (`CG1`).** A fan-out (`F1` of `R-21`, translated by `(-162, -216)`)
  placed in front of `pullGenerator`: one control glider `ofRows (-130) (-225) [2, 4, 7]` gives,
  after 2010 generations, the generator back in its cycle, the pulling salvo, and a continue
  glider `ofRows (-479) 177 [5, 3, 2]` travelling down-left. 8 guns, 3 reflectors; reuse after
  450 generations; with the block, `k → k - 1` for `k = 1..4` and `40`. The new pieces are at
  least 113 cells from the box of `pullGenerator_reaction`, so a proof can compose the fan-out,
  the flight of the linking glider and the certified generator.
- **Push generator: not found.** Of the 176 three-glider pushes only 31 can be assembled by
  reflectors at all (an insertion rule found by the search), and `pushSalvo` is not among them.
  A comb fan-out (three outputs, 2611 placements) was found, but every exact lane/timing
  solution of the generator search has overlapping pieces: one reflection cannot re-time a
  glider, and the comb's outputs are 600–800 generations apart. Next ideas: paths with two or
  more turns for every salvo glider; a PG1-type generator for two gliders of an assemblable push
  plus the third from a continue glider; a period-60 clock.
- **Zero-test logic: decision part found with free gliders.** The three-glider test of
  `zeroTestSalvo_hit` plus a detector glider and two eaters: at `k = 0` the block is restored and
  only the detector flies on (`Z`); at `k ≥ 1` (checked `1..12`, `40`) a test glider kicks the
  detector back (`NZ`) and the others are eaten. Generating the four gliders from one control
  glider is a salvo-generation problem like the push.

**Continue glider certified (2026-11-14).** `Theory/Life/ContinueGlider.lean`:
`fanOut_reaction` (new certificate, 840 generations in seven parts) and
`continueGenerator_reaction`: `pullGenerator ∪ fanOut` with one control glider evolves in 2010
generations into itself, the pulling salvo and the continue glider `contEnd`, inside a stated
box. Proved by composition: the fan-out beside the generator at rest, then
`pullGenerator_reaction` beside the fan-out at rest and the continue glider in flight. Not yet
combined with the register block (the footprint of `Op.reaction` bounds rows only; the continue
glider crosses those rows far to the left, so columns are needed).

## Push generator and increment (2026-11-14)

Search report `R-23` (sub-agent, design `PSG1`): idea (A) worked — a PG1-type core produces two
salvo gliders and an upstream fan-out stage supplies the third through one reflector. The
timing was solved exactly by invariants of reflection (`tau + 4 lane` resp. `tau` are kept), so
the push fixes the leg lane. The salvo is a three-glider push from our own search, not
`pushSalvo`. Also found (not certified): a variant with a continue glider (`PSG1C`). Not found:
serving the same block as `pullGenerator` (a reflector passes parallel gliders on one side only;
the insertion stages of the two generators exclude each other) — needs a joint design with
shared final reflectors.

Certified in `Theory/Life/Increment.lean`: `push3_reaction` (the salvo pushes the block from
every position `k`), `pushGenerator_reaction` (one control glider ⟶ the salvo, 1650 generations,
in eleven parts, with a box), and

`increment : ∀ k, conway.evolve (1650 + (k * 4 + 32))
  (pushGenerator ∪ pushGeneratorControl ∪ pushRegister k) =
  conway.evolve (k * 4 + 32) pushGenerator ∪ pushRegister (k + 1)`.

With `decrement` this gives both register operations triggered by a single glider, each for its
own register block. Open: one block served by both; continue gliders composed with the block
(needs column bounds in the footprints of the salvo reactions); zero-test logic; layout.

## Claims and evidence

No claims beyond the sourced existence of Chapman's pattern.

## Difficulty, barriers and readiness

Blocked. The smallest step that changes readiness: `N-13` decision plus reading `S-10` and
`S-11` ch. 9 to replace the sketch by an actual component list.

## Outputs and next dependencies

Feeds `N-16`.
