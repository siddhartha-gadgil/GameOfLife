# R-18: Source report for N-18 (primary sources for the register-machine route R1)

Date of all retrievals and experiments: 2026-11-14.
Scope: what the primary sources say about register machines in Life, sliding block memory,
universality notions and self-replication; cell-exact pattern data; contradictions with the notes.
Nothing here is Lean evidence. Three kinds of statement are kept apart throughout:

- **[FT]** read in full text in this session (locator given);
- **[SUM]** seen only as a summary, caption or secondary description;
- **[OBS]** a numerical observation made in this session with a throw-away simulator on
  source pattern files (section 5). An observation is not a claim of any source and not a proof.

Anything marked **recalled, unverified** comes from memory and must not be relied on. There are
no such items in the answers below.

Page numbers for the book are the printed page numbers; the PDF page index is the printed
number plus 14 (printed 271 = PDF page 285).

---

## 1. Sources obtained, access level, failures

| ID | What was obtained | Access | Locator / provenance |
| --- | --- | --- | --- |
| `S-11` | Johnston & Greene, *Conway's Game of Life: Mathematics and Construction* (2022), free PDF, 494 PDF pages, 95 665 702 bytes | [FT] for the pages listed below; text by `pdftotext -layout`; two figure pages (273, 274) also rendered and viewed | `https://conwaylife.njohnston.ca/book/conway_life_book.pdf`; sha256 `09bcafc4…ae7617ba` |
| `S-11` patterns | 1020 pattern files embedded in the PDF as attachments (`patterns/<chapter>/<name>.txt`, RLE). Chapters 1–11 are embedded; chapter 12 files are separate zips on the landing page (not downloaded) | [FT] for the files quoted in section 4 | extracted with `pdfdetach -save N`; landing page text: "All patterns for Chapters 1–11 are embedded right in the PDF" |
| `S-10` | P. Chapman, "Life Universal Computer" main page, "Minsky Register Machine" page, 4-state CA page | [FT] all three pages | Wayback `https://web.archive.org/web/20230716132432/http://www.igblan.free-online.co.uk/igblan/ca/` (+ `minsky.html`, `camrm.html`) |
| `S-10` patterns | `IgblanMRM.zip` (509 786 bytes; 6 `.lif` files dated 2005-03-25 and a 3-line ReadMe) | files parsed and partly simulated [OBS] | Wayback `…/web/20230603144954id_/http://www.igblan.free-online.co.uk/igblan/ca/zip/IgblanMRM.zip`; sha256 `64b3ea07…b7962762` |
| Hickerson | D. Hickerson, "Description of sliding block memory" (dated 1-Mar-90), hosted on P. Callahan's page; pattern `sbmem.lif` (Life 1.05 format, 198 `#P` blocks) | [FT] description; pattern file retrieved, not simulated | Wayback `…/web/20230604030349/http://www.radicaleye.com/lifepage/patterns/sbm/sbm.html`; `…/web/20150918215951id_/http://www.radicaleye.com/lifepage/patterns/sbmem.lif` (sha256 `237b789c…811dcf57d`) |
| `S-14` | Durand & Róka, "The Game of Life: universality revisited", **LIP Research Report 98-01, January 1998** (25 PDF pages, 23 numbered) | [FT] whole report | copy on a Utrecht course page `https://www.phil.uu.nl/~iemhoff/College/LogCom/2010/gameoflife.pdf`; sha256 `7ffb0989…a7346e24`. The Kluwer 1999 book chapter was **not** retrieved; differences between the two versions are unknown |
| `S-05` | LifeWiki mirror pages `Sliding_block_memory`, `Universal_computer` (= `URM`, `Universal_register_machine`), `Block_pusher`, `Register`, `APGsembly`, `Replicator`, `Linear_propagator`, `0E0P_metacell`, `Gemini`, `Spartan_universal_computer-constructor`, `Universal_constructor`, `Demultiplexer`, `Pi_calculator` | [FT] raw HTML fetched with `curl` and converted to text (not through a summarizer) for the first eleven; last two fetched, not read | `https://conwaylife.njohnston.ca/wiki/<Page>`; wiki text licence shown on the pages: GNU FDL 1.2 |
| `S-06` | Life Lexicon entries: sliding block memory, block pull, block pusher, universal computer, universal constructor, universal regulator, URM, unit Life cell, replicator | [FT] | `https://playgameoflife.com/lexicon/sliding_block_memory`, `…/block_pusher`; Wayback copies of `conwaylife.com/ref/lexicon/lex_{b,u}.htm` (2024–25 captures), `lex_{r,s}.htm` (2022 captures). Licence stated on playgameoflife.com: CC BY-SA 3.0 |

Book pages read in full: 41–42 (Fig. 2.20), 174–178 (§6.5 end, §6.6), 190–192 (§7.3–7.4),
206–207 and 219 (§7.8 factories, demultiplexer, Exercise 7.39), 245–247 (§8.6), **271–288
(§9.1–§9.4.1)**, 289–297 and 301–303 (parts of §9.4.2–§9.7, Table 9.1), **306–310 (§9.8 and
exercises)**, 345–347 and 377–380 (ch. 11 opening and §11.8), 385–388, 394–395, 422–424 (ch. 12
opening, §12.3 overview, §12.9). Not read: the rest of ch. 5–8, pp. 298–300, 304–305, the
bodies of ch. 10–12, appendix B.

### Access failures (all on 2026-11-14)

- `https://conwaylife.com/ref/lexicon/lex_s.htm`: HTTP 403 (as the notes already record for the wiki).
- `https://conwaylife.njohnston.ca/wiki/Minsky_register_machine`, `…/Sliding_block_register`,
  `…/Minsky_Register_Machine`, `…/Universal_register_machine_(URM)`: HTTP 404 (no such pages on the mirror).
- `https://playgameoflife.com/lexicon/{replicator, universal_computer, universal_constructor, universal_register_machine, URM, block-pusher}`: HTTP 404 (that site carries only part of the Lexicon).
- Wayback captures of `lex_r.htm` from 2023–2025 returned a bot-challenge page ("One moment, please…"); the 2022 capture worked.
- `http://eprints.uwe.ac.uk/22323/1/thesis.pdf` (Rendell's thesis, URL from the Lexicon): DNS resolution failed. `S-09` remains unread.
- `pdfdetach -saveall` failed on the book ("Error saving embedded file") because attachment names contain `/`; saving the 1020 files one by one worked.
- Not attempted or not obtainable: *Winning Ways* ch. 25 (`S-02`), *The Recursive Universe* (`S-03`), Goucher's 2010 book chapter (the book's [Gou10]), Wainwright 1974 ([Wai74]), Minsky 1967, Carlini's posts and the HOL4 repository (`S-08`, item 4 of N-18).

### Licence facts found (for the data-provenance rule in N-18)

- Book: only "Copyright © 2022 Nathaniel Johnston and Dave Greene" (PDF page 2). No licence
  statement for the embedded pattern files was found in the pages read or on the landing page;
  the landing page invites readers to "copy and paste" the RLE into Life software. **Licence of
  the book's pattern files: not found.**
- Life Lexicon (playgameoflife.com copy): CC BY-SA 3.0. LifeWiki mirror: GNU FDL 1.2.
- Chapman's zip and Hickerson's pattern: no licence statement found.

---

## 2. Answers

### A. Components of a register machine in Life; program counter; logic

Three complete designs were found. None uses general AND/OR/NOT gates.

#### A1. Book ch. 9 = Goucher's APGsembly toolkit (2009–2010, rebuilt with modern stable parts)

"Life computers built from APGsembly … consist of three main parts: a computer …, a component
stack …, and a clock gun" (§9.2, p. 279 [FT]).

| Component | Role | Size / period | Clocked or stable | Locator |
| --- | --- | --- | --- | --- |
| Sliding block register `Un` | Counter: value = diagonal position of one block. Inputs `INC`, `TDEC` (one glider each, travelling NW in the figures); outputs `Z`, `NZ` (one glider, travelling NE); output lanes transparent so registers stack side by side | Embedded file `universal_computation/sliding_block_register.txt`: 391 × 327, 2316 cells [OBS: it is a still life, 277 8-connected objects] | Stable: no oscillator or gun inside | §9.1.1 pp. 272–274, Fig. 9.2 [FT] |
| – inside the register: INC shotgun | "aqua and magenta conduits split it into three gliders" (Fig. 8.37(c) salvo) | — | stable conduits ("techniques of Chapter 7") | Fig. 9.2 caption [FT] |
| – inside the register: DEC shotgun | the magenta conduit alone "creates two gliders to pull" (Fig. 8.37(b) salvo); these two gliders are also two of the three INC gliders | — | stable | p. 273, Fig. 9.2 caption [FT] |
| – inside the register: TEST circuit | splits the TDEC glider, sends a trial glider past the zero position, uses a **demultiplexer** to route the second glider to `Z` or to `NZ`+DEC | demultiplexer file: 33 × 23 (Brice Due 2006) | stable | Fig. 9.1, Fig. 9.2 caption, §7.8 p. 206–207 [FT] |
| Computer: state = pair of demultiplexers "that have a boat" | Program counter (see below). One Z-demultiplexer and one NZ-demultiplexer per state | — | stable | §9.2.1 p. 279 [FT] |
| Computer: splitters | "glider duplicators that create a perpendicular glider while also sending another glider to continue along the exact same lane"; one per action of the line | — | stable | §9.2.1 p. 279 [FT] |
| Computer: merge circuits | "a reflector that is transparent to signals passing through it on its output lane"; implements "jump to"; several lines may jump to the same state | — | stable | §9.2.1 p. 279 [FT] |
| Computer: input conduit | puts the Z/NZ glider from the clock on the right lane and "produces an extra cleanup glider on each computer input lane so as to reset the demultiplexers" | — | stable | Fig. 9.3 caption p. 280 [FT] |
| Clock gun | Delays/synchronizes the Z/NZ return glider so that it cannot reach the computer before the next state's demultiplexers are set | "period 2^20" gun = p256 "machine gun" + 6 quadri-Snarks (file `p2to_the_20_gun.txt`, 96 × 90) feeding **two** stable universal regulators (file `stable_universal_regulator.txt`, 97 × 131; "Constructed by Jormungant in April 2020"; the text credits Louis-François Handfield) | **Periodic** — the only periodic part | §9.2.3 pp. 281–282, Figs. 9.3–9.5 [FT] |
| `HALT_OUT` | "stops the computer … and emits an output glider" | — | — | p. 277 [FT] |
| `NOP` | "emit a Z return value" and do nothing | — | — | p. 287 [FT] |
| Optional: binary register `Bn`, `ADD`, `SUB`, `MUL`, digit printer `OUTPUT`, 2D register `B2D` | convenience/speed; not needed for universality (p. 283) | binary register file 3005 × 2817 | stable; `B2D` needs clock period ≥ 2^22 | §9.4–9.7, Table 9.1 p. 303 [FT/SUM] |

Whole compiled machines in the PDF: adder `add_computer.txt` 1828 × 1482, 9709 cells [OBS count];
multiplier `mult_computer.txt` 2201 × 1770.

**The clock is a convenience, not a logical necessity, according to the text**: "To delay the
component stack's output glider, we could simply extend the length of the path that it must
follow back to the computer. However, we instead make use of a very high-period universal
regulator" — chosen so that HashLife runs fast (§9.2.3, p. 281 [FT]). If a register is slow
(large value), "the clock gun simply waits for one or more clock ticks" (footnote 19, p. 282).

**Program counter and control flow** (§9.1.2, §9.2.1, pp. 275–279 [FT]): the machine is a
finite-state machine realized as "a single glider traversing a set of n parallel lanes". At
rest the current state is the pair of demultiplexers that hold a boat. The Z or NZ glider
returning from the clock hits the Z or the NZ demultiplexer of the current state and is
reflected onto the lane of exactly one substate (= one APGsembly line); the unused boat "is
cleaned up by a following glider". On that lane the glider passes the splitters (one action
glider each, sent NW to the component stack) and then a merge circuit which routes it around
the perimeter to "trigger the pair of demultiplexers for the next target state". The initial
Z input is "hard-coded into the Life pattern" as two start gliders.

Constraints stated by the source: all actions of a line fire "simultaneously, rather than
sequentially"; the same action may not occur twice in a line; each line must contain "exactly
one action that produces a return value" (pp. 277–278).

**Logic**: "we no longer really need logical instructions … at all" (p. 276). What exists
instead of gates: (i) the demultiplexer, a one-bit latch (Herschel sets a boat; a later glider
is reflected if the boat is present and passes "unharmed" otherwise; p. 206–207); (ii) inside
the TEST circuit, suppression of the Z signal by the NZ signal ("block Z if NZ comes from
northwest (e.g., glider stopper)", Fig. 9.1); (iii) the regulator.

#### A2. Chapman's Minsky register machine / URM, version 0 (11 Nov 2002) [FT, archived page]

"Seven components are used in the construction: Register, Latch, Split Left, Split Right,
Merge Left, Merge Right, and Eater."

| Component | Role | Clocked? |
| --- | --- | --- |
| Register | 4 inputs (INC, DEC, and pass-through NZ, Z), 2 outputs (NZ, Z). Built around "Dean Hickerson's P120 Sliding Block Memory", with P60-to-P120 converters, buckaroo ladders, P8 reflectors, signal duplicators | P30/P60/P120 guns throughout |
| Latch | 3 inputs (set, read, clear), 3 outputs. State = presence of a block synthesized by two gliders. Set is "actually a toggle" (unused feature) | P30/P60 guns, pentadecathlon, clock |
| Split Left / Right | 1 input, 2 outputs (Heisenburp deletes a glider from a P60 stream) | P60 |
| Merge Left / Right | 2 inputs, 1 output (input LWSS removes a suppressing glider of a P30 LWSS gun) | P30 |
| Eater | 1 input, no output; "just a standard eater" | stable |

- Signals are LWSS "pulses" on a "lattice of 30x30 squares"; components "have P60 logic (except
  for Registers)". Each component "is quiescent until a single input pulse arrives"; "Only one
  input pulse at a time is processed by each component"; pulses to one component "are never
  required to arrive synchronously" but must be "sufficiently well-spaced and in the correct order".
- Sizes: URM v0 "268,096 live cells in an area of 4,558 x 21,469"; adder "3-instruction MRM"
  1,378 × 1,369; multiplier "11-instruction MRM" 2,098 × 3,289.
- **Program counter**: the "sole initial pulse is an execution pulse". Each instruction emits an
  execution pulse and a loopback pulse. INC and NOP: the loopback pulse generates the branch pulse
  to the next instruction immediately ("in effect 'pipelined'"). DEC: the loopback pulse sets two
  Latches (one NZ latch, one Z latch) for the two possible successors; the Register later returns
  an NZ or Z pulse; the Latch Header turns it into a Latch-read pulse for one column and a
  Latch-clear pulse for the other; the single set latch in the read column emits the execution
  pulse of the next instruction. HALT: execution pulse eaten; "the final state of the machine
  should not be read before the absence of all pulses".
- An instruction "may have an NZ Latch or a Z Latch but not both"; the builder inserts NOPs to
  ensure this.
- Machine model ("Minsky Register Machine" page): finite number of registers holding unbounded
  nonnegative integers; instructions INC (one successor), DEC (if nonzero decrement and go to
  "pass", else leave unchanged and go to "fail"), HALT; NOP only as a pattern-building device.
- Universality: the URM "can emulate any other MRM by encoding its instructions and register
  contents as initial values of the URM's registers", using Gödel numbers in six registers
  (`registers`, `opcodes`, `operands`, `passaddresses`, `failaddresses`, `base`); a worked example
  is given. No proof of universality of register machines is given; "equivalent in power to the
  Turing Machine" is asserted.
- The design was prototyped in a 4-state CA described as "globally asynchronous … no
  synchronization of pulses over long distances is required, as long as in certain cases some
  pulses beat others by a decent margin" (`camrm.html`).

#### A3. Chapman's "P1" files in the same zip (2005) — undocumented

The zip contains `Igblan P1 MRM Adder.lif`, `Igblan P1 MRM Multiplier.lif`, `Igblan P1 URM.lif`
next to the `P30` versions. The archived web page describes only the P30 design; **no
description of the P1 design was found.** [OBS]: the P1 adder is a still life (13 717 cells) plus
exactly one glider; see section 5.3. Measured sizes [OBS]: P1 adder 13 722 cells, 2460 × 1724;
P1 multiplier 41 447 cells, 4904 × 4168; P1 URM 261 937 cells, 21 276 × 19 400; P30 adder
15 305 cells, 1318 × 1309; P30 multiplier 44 034 cells, 2038 × 3229; P30 URM 233 724 cells,
3807 × 18 867 (the P30 URM in the zip is therefore not the "version 0" whose statistics the web
page quotes).

#### A4. Conway's original scheme, as reported by others (primary source not read)

Durand–Róka §3.1 list what "a real machine" needs — pulses, wires, a clock, "logical gates and,
or and not", and "auxiliary storage registers" — and realize them by gliders, lanes, a glider
gun, gun-based gates, and (citing Conway) sliding blocks [FT]. That route **does** use Boolean
gates and guns; Chapman's and Goucher's do not.

#### A5. Direct answer

- Component types needed (union of A1/A2): counter register (block + push shotgun + pull
  shotgun + zero detection); one-bit latch (demultiplexer or block latch) per branch target;
  splitter (fan-out); merge (fan-in / transparent reflector); reflectors and delay paths;
  eater; start signal; halt sink or halt output. Optionally a clock/regulator.
- Clocked vs stable: Chapman 2002 is clocked throughout (P30/P60/P120). The book's machine is
  stable except for one clock gun with two regulators, which the text says could be replaced by
  path delay. Chapman's 2005 P1 adder file contains no periodic object at all [OBS].
- General AND/OR/NOT logic: **not needed** in either explicit design.

### B. How sliding block memory works

#### B1. The three block reactions used by the book (Fig. 8.37, p. 245 [FT]; file in §4.1)

- (a) one glider: block moves "left 1, up 2" in 8 generations — "the (2,1) block pull from Figure 2.20".
- (b) two gliders: "left 1, up 1" in 26 generations — "found by Dean Hickerson no later than March 1990". This is the pull (DEC).
- (c) three gliders: "right 1, down 1" in 32 generations — "found by Paul Chapman in 2004"; "(c) is exactly the same as (b) except with an additional input glider that changes the direction". This is the push (INC).

In all three the gliders travel SE and the block is to the SE of them, so (b) moves the block
toward the glider source and (c) away from it. [OBS, §5.1: all three reproduce exactly, with the
stated generation counts, and leave only the displaced block.]

The book contrasts these synchronized recipes with slow salvos: pushing a block diagonally by 1
needs "3 synchronized gliders, whereas we required 6 gliders in a slow salvo" (p. 245; files
`glider_synthesis/block_move_6_gliders.txt`, `block_move_1_neg1.txt`).

#### B2. Hickerson's original memory (1990) [FT]

- Pull: "a 2-glider salvo which can pull a block 1 unit"; push: "a 3-glider salvo which can push
  it 1 unit". Cell-exact figures 0 and 1 are in §4.3.
- The push in Hickerson's Figure 1 is **not** the book's (c): it uses gliders P, Q, R, where R
  "prevents" a boat and a traffic light from forming and is "on the same flight path as one of
  the decrement gliders". Hickerson's shotgun fires "a 4-glider salvo containing both the
  increment and decrement salvos" every 120 generations; suppressor streams D and I delete all
  four gliders unless told otherwise; deleting D releases the decrement salvo (R, S), deleting I
  releases the increment salvo (P, Q, R).
- Zero handling: "there is no separate test for zero. Instead, the device automatically reports
  the transition from 1 to 0": a detector glider Z crosses the diagonal; it "is destroyed in the
  process" when R and S pull the block from 1 to 0 and "will escape unharmed" otherwise. "The
  register should not be decremented if it already contains 0; doing so would destroy it." To ask
  whether the register is 0: "send an increment command followed by a decrement command".
- Releasing both salvos at once: "the block is first pushed and then destroyed".
- Size of his test pattern: population 1685 in 240 × 192.

#### B3. Chapman's register (2002) [FT]

Uses Hickerson's unit unchanged but shifts the interpretation by one: "what Hickerson interprets
as a transition from one to zero, I interpret as a transition from zero to minus one". A DEC at
zero therefore really pulls the block to "minus one"; the missing detector glider then (a)
interrupts the increment-suppression stream, "immediately causing the SBM to be incremented,
thus restoring its value to zero", and (b) releases a Z pulse and cancels the NZ pulse. If the
detector glider survives, an NZ pulse is released. INC returns no signal.

#### B4. The book's register (Goucher design) [FT, pp. 272–274]

- INC: one input glider → stable conduits → the three-glider salvo of Fig. 8.37(c); the block
  moves one cell away. No return signal (Table 9.1: "no return value").
- TEST: "a glider just barely grazes a block": the trial glider "performs this (2, 1) block pull
  if the sliding block is in the 'zero' position, and it simply passes by the block without any
  interaction at all if it is in any other position". If it passes, it is the NZ evidence. If it
  is destroyed, a second signal split off from the TEST input, not suppressed by NZ, produces
  the Z output "as well as a glider that resets the sliding block" by "the opposite (2,1) block
  pull" "from the opposite direction".
- A bare DEC at zero is unsafe: "the TEST mechanism would fail catastrophically, because the
  glider that's supposed to graze the block … would instead run right into it." Hence the
  register has only two inputs, `INC` and `TDEC` = TEST-then-DEC: "The circuit itself will then
  ignore the DEC input if the block is already at the Z position."
- Semantics of `TDEC` (Table 9.1, p. 303): "returns Z if Un = 0 and NZ otherwise, and then
  decreases the value of the register by 1 if NZ". The return value reflects the value
  *before* decrementing: decrementing "from 1 to 0, the return value will be NZ, not Z" (p. 278).
- What comes back and how: exactly one glider, on the register's Z lane or on its NZ lane; in
  the implemented circuit (Fig. 9.2 caption) the choice is made by a demultiplexer: at zero "the
  glider passes through the demultiplexer … on the Z output path, and otherwise the
  demultiplexer creates a boat … that redirects the glider … on the NZ output path", and "the
  NZ output glider is also fed into the magenta conduit that creates two gliders to pull".
- Duration is not uniform: a far-away block "will take a long time to INC or TDEC" (footnotes
  19, 21).
- "INC operations will never cause problems" (footnote 3); a sliding block register cannot be
  damaged by any sequence of single action signals (p. 286, contrast with the binary register).
  The source warns, however, against two actions on one component in the same line.

[OBS, §5.2: the embedded register file behaves exactly as described; input lanes, the zero
position, the salvo geometries at the block, the Z/NZ output gliders and timings were measured.]

#### B5. Conway's original memory (secondary reports only)

- Lexicon / LifeWiki [FT]: two gliders "pull the block inwards by three diagonal spaces" (pattern
  in §4.4), "thirty gliders … push it out by the same amount". Lexicon "block pull": the single
  glider (2,1) pull, done twice, gives the diagonal pull by three.
- Durand–Róka §4.2 [FT]: "two gliders are used to pull a block back three diagonal places and ten
  gliders are used to move up a block just one diagonal place."
- Hickerson [FT]: Conway's zero test is "A glider fired across the diagonal at the zero
  position … (If so, the block is destroyed by the test and must then be rebuilt using 2 more
  gliders.)"; "of course it has never been built."
- Cell-exact geometry of Conway's push salvo: **not found.**

### C. What book chapter 9 constructs and claims

- Opening (p. 271): universality of Life "has been known since the early days … [Wai74, BCG82]",
  but the original constructions "were monstrously large and only mostly pieced together"; the
  chapter presents "one particularly flexible computation toolkit" "Developed by Adam P. Goucher
  in 2009 and 2010 [Gou10]".
- Machine model (§9.1.2–9.2, pp. 274–281): a finite-state machine, each state split into Z and NZ
  substates, acting on a stack of components through actions; the language is "APGsembly". With
  only `Un` components this is a counter machine with `INC` and `TDEC`.
- Constructed patterns: adder (APGsembly 9.2, Fig. 9.3, p. 280), multiplier (APGsembly 9.3,
  Fig. 9.6, p. 284), binary ruler (Fig. 9.8, p. 288), character printer (§9.5), π calculator
  (§9.6, Fig. 9.15), a Θ(√log t)-diameter pattern (Fig. 9.17, p. 307).
- **The universality statement** (§9.3, p. 283), in full: "sliding block registers and the
  computational framework that we have introduced so far are already Turing complete—they can
  compute anything that can be computed." It is asserted without proof, without a definition of
  "Turing complete", and without a citation at that point. The chapter contains no theorem
  environment about universality.
- Finite or not: every compiled pattern is a finite pattern. The program is wired into the
  pattern (one pattern per program); register contents are initial block positions set by the
  `#REGISTERS` header (p. 278). The chapter does not exhibit a single universal machine pattern
  (no analogue of Chapman's URM), nor an input convention beyond `#REGISTERS`.
- Halting: `HALT_OUT` "stops the computer" and "emits an output glider that could then be used by
  another pattern" (p. 277). The chapter does not discuss what the halted pattern looks like.
  (Inference, not in the source: the clock gun is a gun and keeps running after a halt, so a
  halted machine of this design is periodic rather than stationary, and its halt glider escapes.)
- History (§9.8, pp. 306–308): Rendell, April 2000, Turing machine "based on period 30 circuitry";
  extended "to a universal Turing machine … in February 2010". Chapman 2002: "a register
  machine that, at a high level, functions much like the universal computation toolkit that we
  introduced", but "used lightweight spaceships to transmit information instead of gliders, it
  made use of period 30 circuitry instead of stable circuitry". Goucher's toolkit 2010. Loizeau's
  8-bit computer 2016 ("cannot compute quantities larger than 2^8 − 1").
- Chapter 6 (p. 178): Conway and Gosper "used little more than some basic period 30 circuitry …
  [BCG82, Chapter 25] to demonstrate that the Game of Life is universal"; their proofs "require
  sending gliders across absolutely vast distances" and "Actually arranging components as
  required … would typically be infeasible in practice".

### D. Durand–Róka (LIP RR 98-01) [FT]

- "Definition 1. We call pattern a configuration that contains only a finite number of live cells."
- Three notions: universality for Boolean circuits (§3), Turing-universality (§4),
  intrinsic universality = simulating every 2D cellular automaton (§5).
- Why a definition is needed (§4.1): for cellular automata "the initial configuration is
  infinite", so one must say which encodings of a finite word are allowed. Requiring only that
  the encoding be given by a recursive function is too weak: their counter-example encodes the
  halting information into the configuration, so that "a trivial cellular automaton as the shift
  is universal".
- Their definition of an acceptable computation model on a cellular automaton (§4.1):
  1. Encoding: "map a word w onto an almost everywhere periodic configuration"; "The non-periodic
     part of the initial configuration should be obtained recursively from w".
  2. Halting: "a total recursive function from the non-periodic part of the current configuration
     to the pair {halt, continue}" (they reject "a special state appears" and "the dynamics
     becomes stable" as too restrictive).
  3. Step: "each iteration of the considered cellular automaton" is a computation step.
  4. Decoding: maps the non-periodic part of the current configuration "recursively to a word".
  They add: "We are not sure that this definition is the most general."
- On finite configurations specifically: "The first idea is to define the encoding as a
  transformation from words to finite configurations … (i.e. to almost everywhere quiescent
  configurations)"; they generalize because not all automata have quiescent states and "in many
  simulations a periodic media … is needed at infinity". So finite configurations are the
  special case "periodic background = all dead" of their definition; they make no separate
  claim about that special case for Life.
- Simulation between automata (Definition 3): `B` simulates `A` if there are an injective,
  "UL-defined" (commuting with two independent shifts) `f : C_A → C_B` and a constant `T` with
  `f(A(c)) = B^T(f(c))` for all `c`. Theorem 3 gives the embedding of any 2D automaton into Life
  by a tiling of squares containing a Boolean circuit for the local rule (an infinite, periodic
  arrangement of guns and gates).
- What they actually prove about Turing-universality: §4.2 is ten lines — Conway "chooses to
  simulate 2-Registers Machines … that are Turing-universal [8]" (Minsky 1967) — and ends "The
  precise construction is very complex." Their own route to Turing-universality is through
  intrinsic universality, "without the difficult construction of the memory stack" (§1). That
  route uses infinite periodic configurations, not finite ones.
- **Caveat about Conway's proof** (§3.3): because gun streams are dense, a circuit emits
  "parasitic outputs" at times other than its traversal time; for a register machine "these
  parasitic outputs can induce some extra modifications on registers". Curing this needs guns
  whose period exceeds the traversal length of the circuit, but in Conway's construction the
  size of such guns "is proportional to the period". "In this particular point lies the error of
  Conway's construction — as far as we understood it." Three repairs are proposed: a family of
  guns with size `o(period)` ("We were told that this construction exists but could not get any
  reference"); simulate one fixed small universal 2-register machine and pick a suitable gun
  ("We agree that this does not constitute a formal proof!"); or use intrinsic universality.
- Other definitions: "Definition 2 (von Neumann). A cellular automaton is construction-universal
  for a set of configurations A if and only if any configuration of A is the image of a
  configuration"; with A = all configurations this is surjectivity, hence "Corollary 1 … Life is
  not construction-universal" (from the Garden of Eden theorem).
- Self-reproduction is mentioned once: a definition of universality "can even be extremely
  difficult to establish when combined with self-reproduction which is also hard to define".

### E. Self-replication

Definitions in the sources:

- Lexicon "replicator" (2022 capture) [FT]: "A finite pattern which repeatedly creates copies of
  itself. Such objects are known to exist (see universal constructor), but no concrete example
  is known. The linear propagator may be considered to be the first example … but this is
  debatable as each of its copies replicates itself only once, allowing no possibility of
  superlinear growth."
- LifeWiki "Replicator" [FT]: "any pattern that produces an arbitrary number of copies of itself.
  There is currently no precise definition." It lists properties commonly required (parity-rule
  behaviour, no debris) and a classification by Okanishi (classes S, R, Q, X, U; failed classes
  A, D, F).
- Book p. 386 [FT]: "a simple replicator: a pattern that produces arbitrarily many copies of
  itself" (said of HighLife). The book gives no formal definition.
- Universal constructor: book p. 345: a pattern that "can build any Life pattern that is
  synthesizable via gliders"; Lexicon: "capable of constructing almost any pattern that has a
  glider synthesis. This definition is a bit vague. A precise definition seems impossible".

Explicit patterns:

| Pattern | Statistics | Status as replicator | Source |
| --- | --- | --- | --- |
| Linear propagator (D. Greene, 23 Nov 2013), three versions | v1: 290 096 cells, bounding box 14 826 990 × 14 826 908; child appears "directly to the north, offset by (0,-256)"; v2 period 118 614 724; v3 period 88 965 198, box 3 707 102 × 3 707 020 | wiki: "arguably the first explicit example of a replicator …, depending on the exact definition"; classified in its infobox as a puffer. Book p. 379: "repeatedly makes copies of itself"; p. 387 calls it the first replicator constructed in Life. **Period of v1: the wiki infobox says 237 228 617, its text says 237 228 340** (the text also mentions a 277-tick delay between parent and child) | LifeWiki `Linear_propagator` [FT]; book §11.8 [FT] |
| 0E0P metacell (A. P. Goucher, 2014–Nov 2018) | each metacell 2^18 × 2^18; one metageneration = 2^36 generations (book p. 385); wiki infobox: 18 650 000 cells, bounding box 261 841 × 261 841, period 68 719 476 736; nucleus is a glider loop "with a period of exactly 2^29" holding "over three million gliders" (p. 395) | "off" state is empty space; a live metacell builds its neighbours by single-channel construction and self-destructs when off | book ch. 12 opening, §12.3 [FT]; wiki [FT] |
| 0E0P-based replicator (book Fig. 12.3) | twelve 0E0P metacells programmed for HighLife (B36/S23), copying the HighLife replicator every 12 × 2^36 generations | a replicator in Life in the HighLife sense (copies annihilate pairwise: after n cycles there are 2^B(n) copies, B = binary weight) | book pp. 386–387 [FT] |
| Gemini (A. J. Wade, 2010) | 846 278 cells, 4 217 807 × 4 220 191, displacement (5120, 1024) per 33 699 586 generations | a self-constructing spaceship, not a replicator | wiki [FT]; book §11.1 [SUM] |
| Spartan universal computer-constructor (Goucher 2009) | 481 672 cells, 84 625 × 72 374; 11 sliding block registers, 3 tapes, construction arm | "a sufficient program tape would allow the machine to self-replicate"; no such tape exists; estimated "up to 10^18 generations"; known glider leak in the memory tapes | wiki [FT] |
| Chapman–Greene universal constructor (2004) | — | prototype; "It likely that it could be programmed to construct itself, but the necessary program would be very large" | book p. 378 [FT]; Lexicon "universal constructor" [FT] |

No source read states or proves a theorem of the form "a replicator exists" with a precise
definition; the Lexicon and wiki attribute existence to Conway's argument in *Winning Ways*
(not read).

### F. Contradictions with, or corrections to, the notes

1. **N-11 / `sources.md`: "Hickerson's … pushes 1 with 3".** Two different three-glider pushes
   exist. Hickerson's (1990, gliders P, Q, R) shares *one* glider with his pull salvo. The one in
   the book's Fig. 8.37(c), used by the book's register, is the pull salvo plus one extra glider
   and is credited to **Paul Chapman, 2004**. Both are in section 4; both reproduce [OBS].
2. **N-11: "whether the test is a separate probe or a by-product of the pull salvo, and what
   happens when pulling at zero."** Both variants exist. Hickerson: by-product (detector glider
   deleted on the 1→0 transition); pulling at zero "would destroy it". Chapman: same hardware,
   reinterpreted as 0→−1 followed by an automatic re-increment. Book/Goucher: separate,
   non-destructive TEST *before* the pull, by a (2,1) block pull at the zero position and a
   restoring glider; a pull at zero is prevented by the circuit. Conway (reported): destructive
   test and rebuild.
3. **N-11's reaction statements** ("block at offset k+1 plus a 2-glider salvo … evolves to block
   at offset k, with nothing else left") are confirmed for the book's salvos [OBS], with 26 and
   32 generations. But the *register operation* the machine uses is not this small reaction: it
   is a 2316-cell stable circuit whose INC takes about 1 700 generations and whose TDEC takes
   about 2 900–4 000 generations in a 391 × 327 box [OBS §5.2], built from many Herschel
   conduits. N-11's difficulty estimate ("three small reactions plus a uniform-in-k argument")
   covers the block reactions only; the salvo generators and the test circuitry are the larger
   part and are not listed as a dependency.
4. **N-13: "Possibly no clocked logic at all"** — supported, with qualifications. Chapman's
   documented 2002 machine is clocked throughout (P30/P60/P120 guns, LWSS on a 30 × 30 lattice).
   The book's machine is stable except for the clock gun, which the text presents as a
   simulation-speed convenience. Chapman's 2005 P1 adder file is a still life plus one glider
   [OBS]. So an entirely gun-free register machine exists as a pattern, but the only written
   description of a design is for the clocked versions.
5. **N-13: "a register machine needs only single-signal routing components"** — nearly right.
   Besides routing (reflect, split, merge, eat) every design needs a one-bit *latch* per branch
   target (demultiplexer with boat; block latch) and, inside the register, one signal inhibiting
   another (Z suppressed by NZ). No Boolean gate network is needed.
6. **Asynchronous does not mean timing-free.** Both designs rely on ordering constraints: the
   return signal must not arrive "before the next state's demultiplexers are set" (book p. 281);
   Chapman's layout "ensures that a Latch set pulse arrives before its associated Latch read and
   clear pulses". The cleanup glider in the book's computer follows the Z/NZ glider. A proof for
   a clock-free machine needs these race conditions as explicit timing inequalities (the slow,
   value-dependent register delay acts in the safe direction).
7. **N-12 on `S-14`: "reported to derive Turing universality from intrinsic universality."**
   Correct as far as it goes, but (a) that derivation lives on almost-everywhere-periodic
   *infinite* configurations; (b) the register-machine construction on finite patterns is only
   sketched in ten lines; (c) the paper claims an **error in Conway's proof** (parasitic outputs
   of gun-clocked circuits acting on registers) and offers no formal repair for the finite
   case. Point (c) is an argument for a design without free-running guns.
8. **N-12, candidate 3 (halting observables).** D–R reject "the dynamics becomes stable" as a
   general halting condition and use a recursive predicate on the non-periodic part. For the
   project (inferences from the designs, not statements of the sources): in the book's design a
   halt emits a glider and the clock gun keeps running; in Chapman's P30 design the guns keep
   running; in the P1 adder the halted pattern is a still life [OBS]. "Eventually periodic" does not characterize halting for a gun-free machine (a
   non-halting loop with bounded registers is also eventually periodic); "eventually a still
   life" might, but no source states this.
9. **`sources.md` history row.** The Lexicon says Rendell "In February 2010 … completed a
   universal Turing machine design with an unlimited tape"; the book says he extended it "to a
   universal Turing machine … in February 2010"; the wiki says "In 2010 … a universal version …
   followed in 2011 by a fully universal version". The note's "2011" follows the wiki only.
10. **`sources.md`: "Conway's version … pushes it 3 with 30".** Consistent with the Lexicon; D–R
    describe the same thing as ten gliders per diagonal step.
11. **Terminology trap for N-17.** D–R's "construction-universal" (von Neumann's surjectivity
    notion) is false for Life (Corollary 1), while the Life community's "universal constructor"
    means "builds everything that has a glider synthesis" and is, by the Lexicon's own words,
    not precisely definable at present.
12. **`A-6`** ("the classical constructions work as described in the catalogues") now has
    numerical support for the block reactions, for the book's register and for Chapman's P1
    adder (section 5), still no Lean support.
13. **Minsky's bound.** Hickerson cites "Sec. 15.1 of Minsky's 'Computation: Finite and Infinite
    Machines'" for "just 2 such registers suffice"; D–R cite Minsky for 2-register machines. This
    is the classical reference N-14 needs; it was not read.

---

## 3. Things not found

- Any proof, in the sources read, that counter/register machines are universal (only citations of Minsky 1967).
- A precise statement of "Turing complete" in the book; a proof of the claim on p. 283.
- A written description of Chapman's stable "P1" register machine (components, operation).
- Cell-exact data for Conway's 30-glider (or 10-glider) push and for his zero test.
- Named-component decomposition of the book's register beyond the Fig. 9.2 caption (which conduits, how many Snarks/syringes).
- A licence for the book's pattern files, for Chapman's files and for Hickerson's file.
- A precise definition of "replicator" (the sources say there is none) and any precise theorem on self-replication.
- The published 1999 version of Durand–Róka; *Winning Ways*; *The Recursive Universe*; Rendell's thesis/book; Goucher's 2010 chapter; Minsky 1967; `S-08` and the HOL4 repository (not attempted).
- The 0E0P pattern files (chapter 12 zip, 27 MB) were not downloaded.

---

## 4. Cell-exact pattern data (verbatim from the sources)

Conventions of RLE: `x` to the right, `y` downward, `b` dead, `o` alive, `$` end of row.

### 4.1 Book Fig. 8.37 — single-glider (2,1) pull, two-glider pull by one, three-glider push by one

Source: PDF attachment `patterns/glider_guns/synchronized_block_movers.txt` (linked from
Fig. 8.37, p. 245). Three panels side by side: (a) `x` 0–3, (b) `x` 23–32, (c) `x` 53–62; in
each the block is in rows 11–12.

```
#C Some ways of moving a block via just a few gliders.
x = 63, y = 13, rule = B3/S23
55bo$56bo$54b3o3$24bo29bo$25bo29bo$bobo19b3o4bobo20b3o4bobo$2b2o27b2o
28b2o$2bo28bo29bo2$2o28b2o28b2o$2o28b2o28b2o!
```

Explicit cells (file coordinates):

- (a) block (0..1, 11..12); glider (1,7) (3,7) (2,8) (3,8) (2,9).
- (b) block (30..31, 11..12); gliders (24,5) (25,6) (23,7) (24,7) (25,7) and (30,7) (32,7) (31,8) (32,8) (31,9).
- (c) block (60..61, 11..12); gliders (55,0) (56,1) (54,2) (55,2) (56,2); (54,5) (55,6) (53,7) (54,7) (55,7); (60,7) (62,7) (61,8) (62,8) (61,9).

### 4.2 Book Fig. 2.20 — (2,1) block pull and its inverse

Source: PDF attachment `patterns/still_lifes/glider_block_move.txt` (p. 42).

```
#C A glider moves a block, and then it is moved back by another glider.
x = 13, y = 4, rule = B3/S23
4b2o$o3b2o5bo$b2o7b2o$2o8bobo!
```

Lexicon "block pull" (same reaction, other orientation; `lex_b.htm`):

```
OO.
OO.
...
...
...
...
OOO
O..
.O.
```

### 4.3 Hickerson's figures (1990), verbatim

Source: "Description of sliding block memory", Figures 0 and 1. Letters mark gliders, `o` the block.

Figure 0, decrement (R and S pull the block one unit; Z is the zero-detector glider, destroyed
exactly when the block is in the drawn position):

```
.........s.....
.......s.s.....
........ss.....
...............
...............
...............
...............
.........r...oo
..........rr.oo
zz.......rr....
.zz............
z..............
```

Figure 1, increment (P, Q, R):

```
r..................
.rr................
rr.................
...................
...................
...................
...................
...................
...............q.q.
................qq.
................q..
...................
...................
.................oo
.............p...oo
..............pp...
.............pp....
```

Hickerson's Figure 3 (the 4-glider union salvo with suppressor gliders D, I and the
pentadecathlon) and the full unit `sbmem.lif` were retrieved; they are not reproduced here
(Figure 3 is in the archived page; `sbmem.lif` has sha256 `237b789c…811dcf57d`).

### 4.4 Conway's two-glider pull by three

Source: LifeWiki mirror `Sliding_block_memory`; identical picture in the Lexicon.

```
x = 12, y = 9, rule = B3/S23
2o$2o4$9b3o$3o6bo$o9bo$bo!
```

### 4.5 Lexicon "block pusher": three gliders push a block one cell diagonally

Source: Wayback copy of `conwaylife.com/ref/lexicon/lex_b.htm`.

```
...................O.O
...................OO.
....................O.
......................
......................
......................
...O..................
..O...................
..OOO.................
......................
......................
......................
......................
OO...O................
OO...O.O..............
.....OO...............
```

The LifeWiki `Block_pusher` page additionally carries Hickerson's April 1991 block pusher
(137 × 145 RLE, a 3-glider salvo pushing a block 10 units with two return gliders); retrieved,
not reproduced here.

### 4.6 Demultiplexer (the latch of the book's computer and TEST circuit)

Source: PDF attachment `patterns/stationary_circuitry/demultiplexer.txt` (Fig. 7.30(b), p. 207).

```
#N Demultiplexer
#O Brice Due, 2006
#C www.conwaylife.com/wiki/Demultiplexer
x = 33, y = 23, rule = B3/S23
27bo$8b2o17bobo$9bo17b2o$9bobo$10b2o$23b2o$23bobo$24bo3$29b2o$10bo18bo
bo$10bobo18bo$10b3o12b2o4b2o$12bo12bobo$27bo$27b2o3$2b2o$bobo$bo$2o!
```

(The file includes the input Herschel and the test glider.)

### 4.7 The book's sliding block register (Fig. 9.2)

Source: PDF attachment `patterns/universal_computation/sliding_block_register.txt`, 6398 bytes,
sha256 `4b5d4e14…98f487a5`. Licence not found (section 1).

```
#C A sliding block register.
x = 391, y = 327, rule = B3/S23
161bo$160bobo$161bo$148b2o$148b2o6$235b2o$61b2o153b2obob2o12b2o$61b2o
12b2obob2o133bo2b2obo2bob2obo$68bob2obo2bob2o2bo131bobo4bob2obob2o$68b
2obob2obo4bobo131bob5o$76b5obo94b2o38bo4bob2o$72b2obo4bo96bo38bo3bobob
2o$72b2obobo3bo28b2o15b2o43bo5b3o34bo3bobo$76bobo3bo27bobo14b2o42bobo
6bo34b2o3bo$77bo3b2o29bo59bo$106b2o3bob2o85bo$97bo9bo3bo3bo39b2o29bo
13b3o$95b3o9bob2ob2obo40bo27b3o16bo$94bo13bobobobo38b3o27bo18b2o23b2o$
69b2o23b2o57bo29b2o42b2o$69b2o171b2o$54b2o185bo2bo$53bo2bo185b2obo$52b
ob2o189bo$52bo192b2o$51b2o177b2o$66b2o125b2o36bo$66bo126b2o33b3o$67b3o
146b2o10bo$69bo10b2o134bobo$79bobo136bo$79bo76b2o21b2o25b2o10b2o$78b2o
10b2o7b2o55b2o21bobo24bo$91bo7b2o61b2o17bo14b2o9b3o$88b3o71b2o17b2o14b
o11bo$76b2o10bo105b3o$69b2o5b2o116bo$69b2o89b2o$160b2o5b2o$167b2o$71b
2o17b2o5bo$71b2o17bo6b3o$65b2o21bobo9bo$65b2o21b2o9b2o$114b2o$114bo$
111b2obo$110bo2bo$111b2o$96b2o$96b2o5$62bo21b2o3bo$62b3o19bo3bobo$65bo
19bo3bobob2o$64b2o20bo4bob2o$84bob5o$83bobo4bob2obob2o$84bo2b2obo2bob
2obo122b2o$85b2obob2o12b2o44b2o68bobo$104b2o45bo62b2o4bo$82b2o67bobo
58bo2bo2b2ob4o$82bo54b2o13b2o58b2obobobobo2bo$80bobo54b2o76bobobobo$
80b2o14bo118bobob2o$96b3o117bo$3b2o94bo31b2o40b2o$4bo58b2o33b2o31b2o
40b2o54b2o$2bo60b2o15b2o53b2o83b2o7bo$2b5o14b2o57bobo52b2o83b2o5bobo$
7bo13bo8b2o6bo11b2o30bo7b2o83b2o50b2o$4b3o12bobo7bo2bo4bobo10b2o30b2o
6bo83bo2bo$3bo15b2o4bo3b3obo3bobo47b2obo83bobo$3b4o16b3o6bobob2ob2o46b
o2b3o4b2o31b2o40b2o2b2o23bo$b2o3bo3b2o10bo6b2o3bobo51b2o3bo3b2o31b2o
39bo2b2o25b3o$o2b3o4b2o10b2o5bob4o2bob2o22b2o25b4o77b2o3b2o26bo$2obo
27bo3bobob2o22bo26bo15b2o68bo26b2o$3bo26bo3bobo24bobo27b3o12bobo68bo
39b2o$3b2o24bo3bobo25b2o31bo13bo65b3o41bo$29b2o3bo54b5o14b2o64bo40b3o$
89bo65bo59bo$11b2o78bo58b2o2bobo6b2o$12bo65b2o10b2o58bobo2bobo5b2o$9b
3o30b2o34bobo72b2o2bo55b2o$9bo32b2o36bo73bobo49b2o5bobo$57b2o12b2o7b2o
55b2o12bo2bob2o33b2o13b2o7bo$56bo2bo11b2o50bo14bo11bobobo36b2o22b2o$
57b2obo60b3o11b3o13bo2b4o$10b2o48bo59bo14bo16b2o3bo17b2o25bo$10b2o48b
2o58b2o33bo20bo24bobob2o$45b2o105b2ob2o19bobo22bobobobo$46bo105b2o23b
2o19b2obobobobo2bo$43b3o15bo31b2o33b2o25b2o41bo2bo2b2ob4o5b2o$31b2o10b
o17b3o29bobo33bo14b2o10bo43b2o4bo10bo$31bobo30bo30bo4b2o27bob2o2b2o7b
2o9bo35b2o13bobo6bo7b2o3b2o$33bo29b2o26b4ob2o2bo2bo17b2o4b3o2bo3bo18b
2o34bobo13b2o4b4o6b2o3b2o$33b2o56bo2bobobobob2o17b2o3bo3b2o4bobo54bo
18bo$94bobobobo25b4o7b2o54b2o16bo2b3o$95b2obobo11b2o15bo82b2o2bo$99bo
11bobo12b3o85b2o$82bo28bo13bo88bo$80b3o2b2o23b2o14b5o26b2o56bo26b2o$
79bo6bo7b2o34bo26b2o9bo43b3o27b2o$79b2o5bobo5b2o32bo38bobo2b2o38bo$87b
2o39b2o36bobo2bobo14b2o$166bo2b2o17bo$122b2o43bobo19b3o$123bo18bo23b2o
bo2bo18bo$121bo19bobo25bobobo$121b5o14bo2bo22b4o2bo$126bo13bobo23bo3b
2o$97b2o24b3o12bobobobo23bo$97bo24bo15b2o3b2o22b2ob2o50b2o$98b3o21b4o
44b2o51bo$100bo19b2o3bo3b2o36b2o51b3o$119bo2b3o4b2o36bo10b2o40bo$119b
2obo45bo9b2o7b2o87b2o$69b2o51bo44b2o18bo88bo$70bo18bo32b2o61bobo90bo$
67b3o19b3o93b2o71b2o14b5o$67bo24bo166bo13bo$72b2o17b2o37b2o81b2o44bobo
12b3o$73bo57bo82bo45b2o15bo$70b3o55b3o34b2o47bobo15b2o40b4o$70bo57bo
36b2o25bo22b2o15b2o35b2o3bo3b2o$192b3o61bo12b2o4b3o2bo$195bo58b3o20bob
2o$194b2o57bo23bo$101b2o150b2o21b2o$94b2o5bobo77bo$94b2o7bo76bobo$103b
2o75bobo85b2o$181bo86bo$90bo91b3o84b3o$89bobob2o89bo19b2o65bo$89bobobo
bo101b2o5bobo6bo29b2o$86b2obobobobo2bo98b2o7bo5bobo2b2o14b2o7bobo5b2o$
86bo2bo2b2ob4o107b2o3bobo2bobo14bobo6bo7b2o$88b2o4bo116bo2b2o19bo5b2o$
94bobo96bo18bobo20b2o$95b2o95bobob2o13b2obo2bo37bo$192bobobobo15bobobo
32b2obobo$189b2obobobobo2bo9b4o2bo32bobobobo$189bo2bo2b2ob4o9bo3b2o30b
o2bobobobob2o$191b2o4bo15bo33b4ob2o2bo2bo27b2o$197bobo12b2ob2o34bo4b2o
10b2obob2o12b2o$198b2o15b2o32bobo15bo2b2obo2bob2obo$212b2o35b2o15bobo
4bob2obob2o$212bo10b2o42bob5o$213bo9b2o7b2o35bo4bob2o$212b2o18bo5b2o
28bo3bobob2o$230bobo4bobo27bo3bobo$230b2o5bo29b2o3bo$235b2obo3b2o$234b
o3bo3bo9bo$234bob2ob2obo9b3o$210b2o23bobobobo13bo$210b2o42b2o23b2o$
279b2o$294b2o$293bo2bo$294b2obo$226bo70bo$225bobo69b2o$225bobo54b2o$
226bo56bo$227b3o50b3o$229bo38b2o10bo$268bobo$270bo$249b2o7b2o10b2o$
249b2o7bo$259b3o$261bo3$260b2o$260bo$262bo$211b2o29b2o14b5o$211bo31bo
13bo$213bo29bobo12b3o$193b2o14b5o30b2o15bo$194bo13bo49b4o$194bobo12b3o
41b2o3bo3b2o$195b2o15bo40b2o4b3o2bo$209b4o48bob2o$204b2o3bo3b2o46bo$
204b2o4b3o2bo19b2o23b2o$212bob2o19b2o$212bo$211b2o39b2o$252bo$223b2o
28b3o$203b2o9b2o7b2o24b2o4bo$203bo11bo33bo$204b3o8bobo29bobo$206bo9b2o
29b2o13b2o$262b2o2$338b2o$268b2o68bo$268b2o70bo$264b2o54b2o14b5o$225bo
38b2o25b2o11bo6b2o8bo13bo$221b2obobo64b2o10bobo4bo2bo7bobo12b3o$222bob
ob3o74bobo3bob3o3bo4b2o15bo$220bo4bo3bo72b2ob2obobo6b3o16b4o$220b4obo
2bo40b2o35bobo3b2o6bo10b2o3bo3b2o$223bobobo7b2o32b2o31b2obo2b4obo5b2o
10b2o4b3o2bo$164b2o54b3o3bo4b2o2b2o65b2obobo3bo27bob2o$165bo54bo9bobo
73bobo3bo26bo$163bo66bo76bobo3bo24b2o$163b5o14b2o45b2o77bo3b2o$168bo
13bo$165b3o12bobo62bo84b2o$164bo15b2o62bobo2b2o79bo$164b4o75bobo2bobo
48b2o30b3o$162b2o3bo3b2o70bo2b2o51b2o32bo$161bo2b3o4b2o71bobo37b2o$
161b2obo78b2obo2bo12b2o19bo2bo$164bo22bo58bobobo11bo19bob2o$164b2o21b
3o53b4o2bo13b3o16bo48b2o$190bo52bo3b2o16bo15b2o48b2o$189b2o54bo50b2o$
172b2o70b2ob2o47bo$173bo73b2o48b3o$170b3o71b2o53bo10b2o$170bo73bo10b2o
52bobo$245bo9b2o7b2o43bo$244b2o18bo43b2o$199b2o61bobo$192b2o5bobo60b2o
49bo$192b2o7bo111b3o$201b2o113bo$315b2o$188bo53b2o$187bobob2o49b2o$
187bobobobo113b2o$184b2obobobobo2bo110bo$184bo2bo2b2ob4o107b2obo$186b
2o4bo111bo2b3o4b2o$192bobo63bo46b2o3bo3b2o$193b2o62bobo47b4o$257bobo
47bo15b2o$258bo49b3o12bobo$259b3o49bo13bo$261bo44b5o14b2o$306bo$256bo
51bo$254b3o50b2o$253bo$253b2o7$243b2o$242bobo5b2o$242bo7b2o$241b2o2$
255bo$251b2obobo91bo$250bobobobo89b3o$247bo2bobobobob2o85bo$247b4ob2o
2bo2bo85b2o$251bo4b2o72b2o$249bobo79bo$249b2o80bob2o$332bo2bo$333b2o$
348b2o13b2o$348b2o13b2o21b2o$386b2o6$351b2obo31b2o$351b2ob3o30bo$357bo
29bob2o$351b2ob3o27b2ob2obo$352bobo30bo$340b2o10bobo25b2obobo$242bo97b
2o11bo26b2ob2o$242b3o29bo$245bo28b3o103b2ob2o$244b2o31bo103bobo$276b2o
103bobo$264b2o116bo$265bo$223bo41bobo$221b3o42b2o$220bo67b2o$220b2o66b
2o$205b2o$206bo$206bob2o$207bo2bo$208b2o$223b2o60b2o$223b2o60bo$286b3o
$288bo$278b2o$232bo3b2o40b2o2b2o$231bobo3bo44bobo$230bobo3bo22b2o23bo$
226b2obobo3bo17b2o5bo23b2o$226b2obo2b4obo15bobob3o$230bobo3b2o8b2o7bob
o$226b2ob2obobo11b2o7b2o$227bobo3bob3o$215b2o10bobo4bo2bo$215b2o11bo6b
2o!
```

### 4.8 Other files located but not reproduced here

All are PDF attachments of the book (names relative to `patterns/`):
`universal_computation/add_computer.txt` (1828 × 1482; sha256 `b0f58968…f32819c223`),
`mult_computer.txt`, `stable_universal_regulator.txt` (97 × 131), `p2to_the_20_gun.txt` (96 × 90),
`binary_register.txt`, `pi_calculator.txt`; `stationary_circuitry/syringe.txt` (34 × 24),
`oscillators/snark.txt` (32 × 25), `stationary_circuitry/quadri_snark.txt`;
`glider_guns/synchronized_block_reflectors.txt` (Fig. 8.38);
`glider_synthesis/block_move_6_gliders.txt`, `block_move_1_neg1.txt`, `block_move_1_glider.txt`,
`block_move_11_0.txt`; `universal_construction/gemini_push.txt`, `gemini_pull.txt`,
`construction_arm.txt`.

---

## 5. Numerical observations made in this session [OBS]

Method: a set-based Life simulator in Python and a bit-parallel one in C, both written for
this session (scratchpad only, not kept); rule B3/S23; patterns parsed from the source files
quoted above. These are observations for orientation. They are not proofs, were not
cross-checked against an independent simulator such as Golly, and must be redone inside Lean
or by a certified checker before use.

### 5.1 Block reactions

| Reaction (source) | Observed result |
| --- | --- |
| Fig. 8.37(a), one glider | stable from generation 8; only a block remains, displaced by (−1, −2) |
| Fig. 8.37(b), two gliders (pull) | stable from generation 26; only a block remains, displaced by (−1, −1) (toward the glider source) |
| Fig. 8.37(c), three gliders (push) | stable from generation 32; only a block remains, displaced by (+1, +1) |
| Fig. 2.20, both gliders | stable from generation 26 with the block back at its original cells and nothing else; left glider alone: block displaced by (−2, −1), stable from generation 8 |
| Hickerson Fig. 0, R + S + block | only a block remains, displaced by (−1, −1) |
| Hickerson Fig. 0, with Z | block as drawn: Z destroyed. Block shifted SE by 1, 2 or 3 cells (salvo unchanged): block pulled by one and Z survives as a glider |
| Hickerson Fig. 1, P + Q + R | stable from generation 40; only a block remains, displaced by (+1, +1) |
| Hickerson Fig. 1 without R | block displaced by (+1, +1) plus a 17-cell residue (consistent with his "boat and a traffic light") |
| Conway's pull (wiki/Lexicon) | stable from generation 27; only a block remains, displaced by (+3, +3) |
| Lexicon block pusher | stable from generation 68; only a block remains, displaced by (−1, +1) |

### 5.2 The book's register file (`sliding_block_register.txt`, section 4.7)

Coordinates are those of the RLE (origin = top-left of the bounding box).

1. The file is a still life: 2316 cells, 277 8-connected objects.
2. The sliding block is the block at cells (127..128, 17..18). (The block at (148..149, 3..4)
   and the tub at (160..162, 0..2) are other objects; their role was not identified.)
3. Input lanes were found by trying a NW-travelling glider (`ooo / o.. / .o.`) on every one of
   741 lanes. Exactly two lanes give a clean operation:
   - **INC**: glider cells (347,332) (348,332) (349,332) (347,333) (348,334) at generation 0.
   - **TDEC**: glider cells (396,189) (397,189) (398,189) (396,190) (397,191) at generation 0.
   (Any earlier position on the same lane and phase is equivalent, the circuit being stable.
   One further lane crosses the whole pattern without interaction; every other lane that meets the pattern damages it.)
4. **Zero position**: block at (129..130, 19..20). The file as shipped therefore holds the
   value 2; value `v` means block at (129−v..130−v, 19−v..20−v) (increasing values go NW).
5. Outcomes, with `v` the value before the operation (tested for v = 0, 1, 2, 5; TDEC also for 3, 4):
   - INC: the block moves by (−1, −1); nothing else remains. For v = 0 the only differences from
     the initial still life after generation 1670 are the block displacement and a 3-cell dying
     remnant, gone by generation 1710; the time grows by 4 generations per unit of `v`.
   - TDEC, v ≥ 1: the block moves by (+1, +1) and one glider leaves travelling NE (the NZ
     output). For v = 1, from generation 4013 the only differences are the block displacement and
     the glider at (646,10) (647,10) (647,11) (648,11) (646,12); +4 generations per unit of `v`.
   - TDEC, v = 0: the block is unchanged at the end and one glider leaves travelling NE on a
     different lane (the Z output): at generation 2985 the only difference from the initial
     still life is the glider (294,292) (295,292) (293,293) (295,293) (295,294).
   - At most 100 cells differ from the initial still life at any time during an operation.
6. Geometry at the block during TDEC (generation numbers for the input above):
   - Trial glider, generation 1019: cells (140,13) (142,13) (140,14) (141,14) (141,15),
     travelling SW. With the block at zero these five cells plus the block, run in isolation,
     give a block at (131..132, 18..19) after 38 generations and nothing else — a (2,1) pull by
     (+2, −1). With the block at value 1 the same glider passes and continues SW.
   - Restoring glider (v = 0), generation 2357: cells (118,25) (119,25) (119,26) (120,26)
     (118,27), travelling NE, with the displaced block at (131..132, 18..19); in isolation the
     block is back at (129..130, 19..20) after 44 generations and nothing else remains.
   - DEC salvo (v = 1), generation 3987: block (128..129, 18..19); gliders (128,21) (127,22)
     (128,22) (127,23) (129,23) and (134,23) (135,23) (136,23) (134,24) (135,25). In isolation:
     block at (129..130, 19..20) after 26 generations. This is Fig. 8.37(b) rotated by 180°.
   - INC salvo (v = 0), generation 1640: block (129..130, 19..20); gliders (129,22) (128,23)
     (129,23) (128,24) (130,24); (135,24) (136,24) (137,24) (135,25) (136,26); (134,29) (135,29)
     (136,29) (134,30) (135,31). In isolation: block at (128..129, 18..19) after 32 generations.
     This is Fig. 8.37(c) rotated by 180°; its first two gliders are the DEC salvo.
7. States "below zero" (block further SE than the zero position) are not valid: with the block
   one cell beyond zero, TDEC produced a 581-cell mess. They are unreachable through INC/TDEC
   from a valid state, as the book says.

### 5.3 Chapman's `Igblan P1 MRM Adder.lif`

- Header `x = -1, y = -106, rule = S23/B3`; 13 722 cells; bounding box 2460 × 1724.
- The pattern is a still life of 13 717 cells plus one glider (cells, relative to the bounding
  box corner: (806,613) (807,614) (805,615) (806,615) (807,615), travelling SE).
- Run from this state it becomes **completely stationary at generation 42 689**. The final
  still life differs from the initial one in exactly 12 cells: the block at (1978..1979,
  625..626) has moved by (+1, −1) and the block at (2358..2359, 1005..1006) by (−1, +1); the
  glider is gone. This is what an adder with one unit to transfer would do (one register
  decremented to zero, the other incremented, then HALT); which block is which register, and
  the initial register values, were not determined.
- The `P30` files, by contrast, change in thousands of cells per generation (guns).

---

## 6. Consequences for the notes (proposals only; no note was edited)

1. `sources.md`: `S-10`, `S-11` (listed pages), `S-14` (research-report version) and the listed
   `S-05`/`S-06` pages can be upgraded to "read"; add Hickerson's description and `sbmem.lif` as a
   new source; record the book's embedded pattern files as the primary pattern source and the
   missing licence statement.
2. `N-13`: R1 is consistent with every source read. The component list of section 2.A5 replaces
   the "unverified expectation". The cheapest documented architecture is the book's (one glider
   as program counter, demultiplexer latches, splitters, transparent merges, registers with
   `INC`/`TDEC`), with the clock replaced by path delay as the book itself suggests; Chapman's
   P1 adder shows such a gun-free machine can exist, but its design is undocumented.
3. `N-11`: record both push salvos and the three zero-handling schemes; decide which register
   semantics to formalize (the book's `TDEC`, "test then decrement, never below zero", matches
   Minsky's DEC with pass/fail). Add the salvo generators and the TEST circuit as dependencies:
   they, not the block reactions, dominate the size (2316 cells, thousands of generations per
   operation in the book's implementation).
4. `N-10`: no Boolean gates are required by R1; the needed stable parts are reflector, splitter,
   transparent merge, latch (demultiplexer), glider-to-salvo conduits, eater.
5. `N-12`: Durand–Róka's four-part definition (recursive encoding of the non-periodic part,
   recursive halting predicate, one automaton step per computation step, recursive decoding),
   specialized to the all-dead background, is compatible with candidates 2–4; their warning
   about trivial encodings is the same as the note's. Their reported gap in Conway's proof
   concerns free-running guns and does not arise in a gun-free design.
6. `N-17`: no source gives a definition of replicator precise enough to state a theorem; the
   explicit patterns have 10^5–10^7 cells and periods of 10^8–10^11 generations.
