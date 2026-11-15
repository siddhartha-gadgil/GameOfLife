# N-19: Architecture of the simulation theorem (counter machines in Life)

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-19` |
| Title | Architecture of the simulation theorem |
| Kind | research approach / formalization plan |
| Addresses | `G-7`, `Q-4` |
| Depends on | `N-15` (design D1, `REG1`, `DZ2`, reports `R-24` … `R-30`), `N-16`, `N-12`; Lean: `Network.lean` (`Proc`, `Reaction.parList`, `Piece.bundle`, `flight_reaction`, `trajectory_reaction`, `salvo_world_all`), `dz2gAll`, `dz2mk1Run_rest`, `dz2mk0Run_rest`, `reg1_increment`, `exists_computes_code`, `not_computablePred_everAlive_of_family` |
| Dependency requirement | compiled component certificates in the network format; the layout rule of `R-30` (numerical) |
| Produces | the plan for the remaining Lean work of `G-7` |
| Difficulty | hard: proof engineering at scale, plus separation facts for every program |
| Status | stated |
| Implementation status | in progress (components) |
| Implementation evidence | `Theory/Life/Network.lean`, `Theory/Life/Gen/*`, `scripts/life_cert` |
| Lean evidence | `dz2gAll`, `dz2mk1Run_rest`, `dz2mk0Run_rest` |
| Audit evidence | axiom audit at commit `667ab3a` (28 351 declarations) |
| Last updated | 2026-11-15: created after `R-30` and the certification of `DZ2` for every `k` |

## Purpose and scope

`G-7` asks, for every counter-machine program, a computable finite pattern and a compiled
simulation theorem, and the corollary that "a fixed cell is ever alive" is undecidable for finite
configurations. `R-30` gives a layout rule and exact simulations of two programs; nothing of the
layout is verified. This note fixes how the Lean proof is organised.

## Method: networks of processes

A run is a chain of segments; in each segment the configuration is a list of independent processes
(idle periodic pieces as one bundle, local certificates, flights, generic processes with symbolic
parameters) whose footprints are pairwise far apart (`Reaction.parList`), glued at the boundaries by
equalities of finite sets. Concrete parts are generated (`scripts/life_cert/plan.py`, `emit.py`,
`emit_generic.py`) and checked by Lean; symbolic parameters (register values `k`, positions, delays)
enter through generic processes whose separations are linear arithmetic (`omega`).

Verified so far with this method: the zero test `DZ2` for every register value (`dz2gAll` for
`k ≥ 2`, concrete `k = 0, 1`).

## Plan

1. **Register module operations, every value.** DEC (done for the bare `DZ2`), INC for every `k`
   (same method: the push salvo `reg1IncLocal` as generic process), on the module of `R-29`/`R-30`
   (with chains and stations), and unify the three `DZ2` statements on one shared piece file.
2. **Parametric parts by translation and induction.** OR-gate chains (one relay lemma per copy,
   chains of any length by induction over the translation `(35, 64)`), dispatch stations (pass and
   capture lemmas, chains of stations by `(72, 72)`), reflector routes (one reflection lemma per
   reflector image, flights between), the HALT line. Each part is certified once in its own frame
   and placed by `Reaction.translate` and a time shift (phase bookkeeping mod 30).
3. **Layout for provability.** Re-state `R-30`'s rule so that separation is a consequence of simple
   inequalities (units in disjoint blocks of a coarse grid, tracks in streets between them), and
   prove: every active process of a step is far from every idle unit; register diagonals are free
   forever; concurrent gliders of one step are far apart or certified together.
4. **Step theorem.** `enc c` = all units at rest (phase `φ`), the blocks at the register values, the
   control glider at the entrance of instruction `pc`. For each instruction: a reaction of
   `τ c` generations from `enc c` to `enc c'`, footprint inside the machine region; proof = the
   chain of parametric parts of that instruction, in parallel with the bundle of all other units.
5. **Simulation theorem and corollaries** (`N-12`, `N-16`): induction over machine steps; the HALT
   cell is alive iff the machine halts (it lies outside every footprint of every step); the map
   from programs to window data is `Computable`; then `not_computablePred_everAlive_of_family`.

## Progress

* 2026-11-15: plan item 1 for the bare register circuit: `dz2gAll`, `dz2iAll` (every `k`).
* 2026-11-15: plan item 2, first part: `chain_reaction` (`Theory/Life/Chain.lean`), a generic
  induction for chains of relays, and `orChain` (`Theory/Life/MergeChain.lean`), the OR-gate merge
  chain for every length. Side inputs, stations and routes next.
* 2026-11-15: `Stage.route_reaction` (`Theory/Life/Route.lean`): routes of heterogeneous stages
  (reflectors, gates, flights) for any list of stages. A layout for provability is being designed
  (search `R-31`).

* 2026-11-15: report `R-31` (numerical): the layout LP with every position an affine formula in the
  indices, 17 separation pair classes each one linear inequality, a nesting lemma for concurrent
  links (no crossing, or crossings separated by causality), timing by residues (all pitches
  `≡ 0 mod 30`), and a catalogue of 25 local certificates for every program; 11 runs to halting.

## Barriers

* Separation for every program (step 3) is the main proof burden; the layout may need to be
  changed for provability (larger spacing, regular streets) rather than compactness.
* Phases mod 30: each unit accepts its input on some residues; the timing rules of `R-30` must be
  re-proved as arithmetic facts of the layout.
* `Computable` for the layout function (Mathlib's `Primrec` API on lists of windows) is laborious.
