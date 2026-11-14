# Source and assumption ledger

Stable source identifiers (`S-*`) for the Game of Life project, with what was actually read, on
which date, and what each source is used for. Nothing in this file is Lean evidence: every claim
taken from a source is **sourced, unverified** until a named Lean declaration compiles.

Access levels:

- **read**: the full text (or the stated pages) was retrieved and read in this project;
- **summary**: the page was retrieved through an automated summarizer; details need re-checking
  against the page before they are relied on;
- **snippet**: only search-result excerpts were seen;
- **not retrieved**: known by citation only; no content of the source may be relied on;
- **recalled**: bibliographic detail supplied from the agent's memory, not checked this session.

Retrieval date for all online sources below: 2026-11-14.

## Sources

| ID | Source | Access | Used for |
| --- | --- | --- | --- |
| `S-01` | M. Gardner, "Mathematical Games: The fantastic combinations of John Conway's new solitaire game 'life'", *Scientific American* 223 (Oct. 1970). Cited as ref. [13] of `S-07`. | not retrieved | Origin of the rule; historical only |
| `S-02` | E. Berlekamp, J. Conway, R. Guy, *Winning Ways for your Mathematical Plays* (1982), chapter "What is Life?" (chapter number recalled as 25). Cited by `S-04` and `S-05`. | not retrieved | Conway's universality and self-replication argument; sliding block memory (original version) |
| `S-03` | W. Poundstone, *The Recursive Universe* (1985). Cited by `S-04`, `S-05`. | not retrieved | Exposition of Conway's argument |
| `S-04` | A. Ghassaei, "The Recursive Universe", blog post, 2020-05-01, <https://blog.amandaghassaei.com/2020/05/01/the-recursive-universe/> (user-supplied). | summary | Pattern taxonomy; OTCA metapixel anatomy; pointers to other sources |
| `S-05` | LifeWiki, <https://conwaylife.com/wiki/Main_Page> (user-supplied). Direct automated retrieval returned HTTP 403. Mirror <https://conwaylife.njohnston.ca/wiki/> was readable; pages retrieved: `Sliding_block_memory`, `URM` (redirects to "Universal computer"), `Traffic_light`, `Gosper_glider_gun`. | summary (4 mirror pages); snippet (others) | Pattern data and statistics; history of universal-computer constructions |
| `S-06` | Life Lexicon (S. Silver and later maintainers), <https://playgameoflife.com/lexicon>, <https://bitstorm.org/gameoflife/lexicon/>. | snippet | Definitions of eater 1, kickback reaction, two-glider collisions |
| `S-07` | M. O. Myreen, M. Carneiro, "GOL in GOL in HOL: Verified Circuits in Conway's Game of Life", arXiv:2504.00263v1 (2025-03-31), 17 pp. A search result lists a published version in ITP 2025 (LIPIcs, doi 10.4230/LIPIcs.ITP.2025.25); only the arXiv v1 was read. | read (pp. 1–17 of v1) | Formal definition of Life on `Set (ℤ × ℤ)`; area of influence; GOL-IO interface semantics; gate specifications; symbolic simulation; the only known ITP verification of Life circuitry |
| `S-08` | N. Carlini, blog series on digital logic in Life (2020–2022): <https://nicholas.carlini.com/writing/2020/digital-logic-game-of-life.html> (part 1), `.../2020/intro-to-circuits-game-of-life.html` (2), `.../2021/improved-logic-gates-game-of-life.html` (3), `.../2021/unlimited-register-machine-game-of-life.html` (4), `.../2022/multiplexing-circuits-game-of-life.html` (5). | summary (part 4); snippet (others) | Gate designs used by `S-07`; a bounded register-machine CPU |
| `S-09` | P. Rendell: Turing machine pattern (2000), <http://rendell-attic.org/gol/tm.htm>; "Turing Universality of the Game of Life", in *Collision-Based Computing* (ed. Adamatzky, Springer 2002); "A fully universal Turing machine in Conway's Game of Life", *J. Cellular Automata* 8(1–2), 2013, pp. 19–38; PhD thesis *Turing Machine Universality of the Game of Life*, UWE Bristol, 2014, <https://uwe-repository.worktribe.com/output/822575>; book, Springer 2016 (ISBN 978-3-319-19841-5). Repository page returned HTTP 403. | snippet | Direct Turing-machine constructions; tape as two stacks; stack growth by collision-based construction |
| `S-10` | P. Chapman, "Life Universal Computer" (2002), originally <http://www.igblan.free-online.co.uk/igblan/ca/>; main, Minsky and CA pages and `IgblanMRM.zip` retrieved from the Wayback Machine (see `R-18` §1). | read (by sub-agent; report `R-18`) | Minsky register machine and universal register machine patterns built on Hickerson's sliding block memory |
| `S-11` | N. Johnston, D. Greene, *Conway's Game of Life: Mathematics and Construction* (2022), doi 10.5281/zenodo.6097284, free PDF at <https://conwaylife.njohnston.ca/book/> (≈ 91 MB). Chapters: 1 Early Life; 2 Still Lifes; 3 Oscillators; 4 Spaceships and Moving Objects; 5 Glider Synthesis; 6 Periodic Circuitry; 7 Stable Circuitry; 8 Guns and Glider Streams; 9 Universal Computation; 10 Self-Supporting Spaceships; 11 Universal Construction; 12 The 0E0P Metacell. | read in part (by sub-agent: ch. 9 §9.1–9.4.1, §9.8 and listed pages of ch. 2, 6, 7, 8, 11, 12; the PDF embeds 1020 RLE pattern files; report `R-18`) | Primary textbook source for patterns, circuitry, universal computation and construction; page locators in `R-18` |
| `S-12` | "woodrush" (GitHub handle; real name not confirmed this session), "A Lisp Interpreter Implemented in Conway's Game of Life", blog post 2022-01-12, <https://woodrush.github.io/blog/posts/2022-01-12-lisp-in-life.html>; repository <https://github.com/woodrush/lisp-in-life>. | summary (blog post) | Existing Lisp-in-Life tower; evidence for the route assessment `N-13` |
| `S-13` | The "Quest for Tetris" (QFT) project (QFTASM, VarLife, metafier). Referenced by `S-12`. | not retrieved | Computer architecture underlying `S-12` |
| `S-14` | B. Durand, Zs. Róka, "The Game of Life: universality revisited", in *Cellular Automata* (eds. Delorme, Mazoyer), Kluwer 1999, doi 10.1007/978-94-015-9153-9_2; LIP Research Report 98-01 (the version read). | read (research report, by sub-agent; report `R-18` §2.D) | Careful definitions of universality notions for Life; needed by `N-12` |
| `S-15` | A. P. Goucher: Spartan universal computer-constructor (2009, per `S-05`); "Fully self-directed replication", cp4space blog, 2018-11-12, <https://cp4space.hatsya.com/2018/11/12/fully-self-directed-replication/> (0E0P metacell; attribution of the post to Goucher not confirmed by the snippet). | snippet | Self-replication survey `N-17` |
| `S-16` | Gemini (A. Wade, May 2010) and the linear propagator (D. Greene, 2013-11-23), as described in `S-05` and Wikipedia "Replicator (cellular automaton)". | snippet | Self-replication survey `N-17` |
| `S-17` | Mathlib at tag `v4.35.0` (pinned in `lakefile.toml`): `Mathlib/Computability/` — `Partrec`, `PartrecCode`, `Halting` (`ComputablePred.halting_problem`, `rice`), `TuringMachine/PostTuringMachine` (`Turing.TM0`, `Turing.TM1`), `TuringMachine/StackTuringMachine` (`Turing.TM2`), `TuringMachine/ToPartrec`. | declarations located by `grep` in the pinned checkout; compiled as part of the Mathlib cache | Machine models and undecidability results that the universality theorem should connect to |
| `S-18` | S. Diehl, "From Zero to QED" (Lean tutorial), chapter on model checking, <https://sdiehl.github.io/zero-to-qed/21_model_checking.html>. | snippet | Prior Lean treatment: glider on a finite torus only |
| `S-19` | S. Ninagawa, G. J. Martínez, visualization study of the universal register machine in Life, arXiv:2104.02920. | snippet | Secondary description of the URM (five parts) |
| `S-20` | J.-P. Rennard, "Implementation of logical functions in the Game of Life", in *Collision-Based Computing* (Springer 2002). | recalled | Possible source for glider-stream gates; verify existence and content before use |

Additional source found by `R-18`: `S-21`, D. Hickerson, "Description of sliding block memory" (1990) with the pattern file `sbmem.lif` (locators in `R-18` §1, §4.3); access: read by sub-agent.

The detailed source report is [`research/reports/R-18-source-report.md`](research/reports/R-18-source-report.md). It contains cell-exact pattern data and numerical observations (simulations, not proofs). Licences of the pattern files were not found.

## Claims taken from sources (all unverified in Lean)

Each row names the source, the claim, and its kind. "Statistic" means a number reported by a
catalogue; it becomes a theorem only when the corresponding Lean statement is proved.

| Claim | Kind | Source |
| --- | --- | --- |
| Rule B3/S23 on the Moore neighbourhood: a live cell survives with 2 or 3 live neighbours; a dead cell is born with exactly 3 | definition | `S-07` §1.1, §3.1; `S-04` |
| Life state as a set `S ⊆ ℤ²`; `step S = {(i,j) | if (i,j) ∈ S then live_adj S i j ∈ {2,3} else live_adj S i j = 3}` | definition (HOL4) | `S-07` §3.1 |
| If `infl S ∩ infl S' = ∅` then `step (S ∪ S') = step S ∪ step S'`, where `infl` is the radius-1 neighbourhood | theorem proved in HOL4 (not in Lean) | `S-07` §3.2 |
| Block, loaf, boat, beehive are still lifes; blinker and beacon have period 2, pulsar 3, pentadecathlon 15 | statistic; **now compiled** (`LeanTheory/Theory/Life/Patterns.lean`) | `S-04` |
| Glider: period 4, displacement one cell diagonally per period (speed c/4); LWSS, MWSS, HWSS: period 4, orthogonal speed c/2 | statistic; **now compiled** (`Pattern.glider_isSpaceship`, `lwss_`, `mwss_`, `hwss_isSpaceship`) | `S-04`; `S-07` §1.1 |
| Traffic light: four blinkers, 12 cells, 9 × 9 bounding box, period 2 (from apgcode prefix `xp2`); RLE `2b3o2$o5bo$o5bo$o5bo2$2b3o!` | statistic | `S-05` (`Traffic_light`, mirror) |
| Gosper glider gun: 36 cells, 36 × 9, period 30, Gosper 1970; two queen bee shuttles stabilized by blocks; RLE recorded in `N-07` | statistic | `S-05` (`Gosper_glider_gun`, mirror) |
| There are 71 distinct two-glider collisions; many destroy both gliders cleanly | statistic | `S-05` snippet; `S-06` snippet |
| Kickback reaction: a two-glider collision producing one glider travelling opposite to one of the inputs | statistic | `S-06` snippet |
| Sliding block memory: Conway's version pulls a block 3 diagonal cells with 2 gliders and pushes it 3 with 30; Hickerson's version pulls 1 with 2 gliders and pushes 1 with 3; a zero test (or a one-to-zero transition test) suffices for reading | statistic | `S-05` (`Sliding_block_memory`, mirror) |
| Conway (1982) described a finite universal computer from glider logic and sliding block memory; Rendell's 2000 Turing machine needs an infinite tape pattern; Chapman (2002) built a Minsky register machine and a universal register machine with Hickerson's memory; Rendell's 2011 "fully universal" machine has a finite initial pattern | history | `S-05` (`URM`, mirror) |
| Rendell's tape is two stacks which grow by collision-based construction | history | `S-09` snippet |
| Carlini-style gates: LWSS streams of period 60 in 150 × 150 tiles; AND as `a ∧ ¬(¬b ∧ 1)`; period 60 allows crossovers | design description | `S-07` §1.1, §2 |
| HOL4 mega-cell: 21 × 21 tiles, 3150 × 3150 cells, clock period 586 ticks of 60 generations; theorem `step^n S = read_mega_cells (step^(n·60·586) (build_mega_cells S))`; ≈ 9 500 lines of HOL4; uses fast in-logic computation for symbolic simulation | theorem proved in HOL4 (not in Lean) | `S-07` §2, §5.2, §6 |
| OTCA metapixel: 2058 × 2058 cells, 35 328 generations per simulated step, programmable B/S rule; "off" metapixels are not empty | design description | `S-04` |
| Lisp in Life: Lisp interpreter in C → QFTASM → VarLife → OTCA metapixels; 16-bit words, RAM address space 10 bits, ROM 12 bits; one VarLife generation = 35 328 Life generations | design description | `S-12` |
| Carlini's "unlimited register machine" CPU physically has 16 registers of 4 bits and a 128-instruction ROM | design description | `S-08` part 4 |
| Linear propagator: 290 096 cells, period 237 228 617; whether it is a "true" replicator is disputed because the parent is destroyed | statistic / dispute | `S-05` snippet; Wikipedia snippet (`S-16`) |
| Gemini: self-constructing oblique spaceship, displacement (5120, 1024) per 33 699 586 generations, not a replicator | statistic | `S-16` snippet |
| The 0E0P metacell has an empty "off" state | design description | `S-15` snippet |
| Block reactions (book Fig. 8.37): one-glider (2,1) pull in 8 generations; two-glider pull by one in 26 (Hickerson); three-glider push by one in 32 (Chapman 2004) | statistic, reproduced by simulation in `R-18` §5.1 | `S-11` p. 245 |
| The book's sliding block register: 391 × 327, 2316 cells, stable; inputs `INC`, `TDEC`; outputs `Z`, `NZ`; `INC` ≈ 1 700 generations, `TDEC` ≈ 2 900–4 000 | design description; timings are observations of `R-18` §5.2 | `S-11` pp. 272–274 |
| Register machines in Life need registers, latches, splitters, merges, reflectors, eaters, and no Boolean gate network | design description | `S-11` ch. 9; `S-10` |
| Durand–Róka report an error in Conway's universality argument (parasitic outputs of free-running guns) | published claim | `S-14` (research report) |
| Rendell's universal Turing machine with unlimited tape is dated February 2010 by the book and the Lexicon, 2010/2011 by the wiki | history, sources disagree | `S-11`, `S-06`, `S-05` |
| Mathlib has no counter/register machine model (no match for `minsky`, `counter machine`, `register machine` in `Mathlib/`) and no cellular automaton or Game of Life development | observation on the pinned checkout | `S-17`, grep on 2026-11-14 |

## Assumption ledger

The project has **no empirical inputs and no model laws**: Life is a mathematical definition.
The assumptions are definitional choices, user requirements and proposed models.

| ID | Assumption | Kind | Origin | Validity / status |
| --- | --- | --- | --- | --- |
| `A-1` | The rule is Conway's B3/S23 on `ℤ × ℤ` with the Moore neighbourhood | definition | user; `S-07` §3.1 | Fixed; whether the kernel is also parameterized by a Life-like rule is `Q-2` |
| `A-2` | Configurations have finitely many live cells at every time | requirement | user constraint | Preserved automatically by `step` (to be proved in `N-01`); it restricts initial patterns and excludes constructions that tile the plane (`C-6`) |
| `A-3` | Snapshots and finite evolutions carry `Repr`, `ToJson`, `FromJson` instances | requirement | user constraint | `N-02`; assurance level is `Q-11` |
| `A-4` | "Turing machines can be built" is to be read as a simulation theorem for a universal machine model, plus an undecidability corollary | proposed model | this seeding (`N-12`) | Proposal; the exact statement is `Q-4` and needs user confirmation |
| `A-5` | A Lisp interpreter layer may be easier or more transparent than a direct machine | user idea | user | Unassessed conjecture about proof engineering; `Q-5`, `N-13` |
| `A-6` | The classical constructions (glider logic, sliding block memory, register machine) work as described in the catalogues | sourced, unverified | `S-05`, `S-02` (not retrieved) | Each component needs cell-exact data (`Q-9`) and a compiled theorem |
| `A-7` | Kernel-checked simulation without `decide` scales to gate-sized windows (≈ 150 × 150 cells for ≈ 60 generations) | confirmed by measurement | this seeding | 5 s and 2.3 GB for 150 × 150 × 60; benchmark in `N-03` |
| `A-8` | Self-replication in Life can be proved in Lean with feasible effort | conjecture | user goal | Doubtful with known patterns; `Q-10`, `N-17`; goal `G-8` is postponed with an activation rule |
