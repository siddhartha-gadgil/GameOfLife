# Theory/

General, domain-independent mathematics used by bridges and certificates. Results here never
depend on a kernel law.

## KAM/ — strip algebras, Fourier analysis and Newton iterations

| Module | Content |
| --- | --- |
| `Diophantine`, `DiophantineB` | Diophantine frequencies, quadratic irrationals, explicit constants |
| `WeightedEll1Z2` | The Banach algebra `ℓ¹_r(ℤ²)` of analytic functions on the complex strip |
| `Cohomological` | The cohomological equation on the 2-torus in weighted `ℓ¹` norms |
| `Composition` | Composition of polynomials with Banach-algebra elements |
| `StripAlgebra`, `StripEval`, `StripSmooth` | Double Fourier series with bounds on several strips; evaluation; smoothness |
| `StripPaleyWiener`, `SampledBound` | Paley–Wiener bounds, certified aliasing, strip norms from samples |
| `FourierSumHolo`, `CauchyTwoVar`, `TorusFieldAna` | Joint holomorphy of Fourier series, two-variable Cauchy estimates, analytic fields along a complexified torus |
| `AnalyticComposition`, `AnalyticCompositionLip` | Analytic composition in Banach algebras and its Lipschitz bounds |
| `InvSqrt`, `InvSqrtApprox` | Inverse square roots in Banach algebras, a posteriori bounds |
| `PolyExprS`, `PolyExprSStrip`, `PolyExprSConstMono`, `PolyExprSMajQ`, `PolyExprSMajQG` | Expression trees with an inverse-square-root node and kernel-computable majorants |
| `ParamInterp` | Interpolation in a parameter with an analytic remainder bound |
| `KamSequence` | Convergence of KAM/Newton iterations with loss of analyticity |

## Computability/ — counter machines

Independent of the Game of Life; connects to Mathlib's `Nat.Partrec`.

| Module | Content |
| --- | --- |
| `CounterMachine` | Counter (Minsky register) machines with instructions `inc`, `decJz`, `halt`: semantics, determinism, relocation and embedding of subprograms, `Program.Computes`, sanity programs |
| `CounterMachineWhile` | A structured loop language on registers, verified macros, and a compiler to counter programs proved correct in both directions (`mem_eval_compile`) |
| `CounterMachineUniversal` | **Universality**: `exists_computes_code`, every `Nat.Partrec.Code` is computed by a well-formed counter program; `exists_program_halts_not_computable` |

## Life/ — general theory of the Game of Life

These modules build on `Kernel/Life` (definitions only; there is no law).

| Module | Content |
| --- | --- |
| `BoxCert` | Evolution certificates that deliver a box for every generation: `EvolvesIn`, `EvolvesIn.reaction`, tactic `life_reaction`; `Reaction.seq_const` |
| `Boxes` | Rectangular footprints: `Box`, `Box.farApart`, `boxCheck` with `coe_ofRows_subset_box`, flight with a moving box (`reaction_flight_box`), resting still lifes and oscillators |
| `Collisions` | Elementary reactions found by own search: eater absorbs glider, annihilations, kickback, turn-round, a shorter push, and the zero test (`zeroTest_hit`, `zeroTest_restore`, `zeroTest_pass` for every position `k ≥ 1`, `zeroTestSalvo_hit`) |
| `ContinueDecrement` | Decrement with a continue glider, for every position `k ≥ 1` (`continueDecrement`); salvo footprints bounding columns (`pull_reaction_quad`) |
| `ContinueIncrement` | Increment with a continue glider, for every position `k` (`continueIncrement`); push salvo footprint bounding columns (`push3_reaction_quad`) |
| `ContinueGlider` | A fan-out in front of the pull generator: one control glider ⟶ the pulling salvo and a continue glider, assembly back in its cycle after 2010 generations (`continueGenerator_reaction`, compositional proof) |
| `Decision` | Finite configurations as data (`WindowData`), the predicate `EverAlive`, and the reduction from a computable family to the general decision problem |
| `Decrement` | The first complete register operation: for every `k ≥ 1`, generator + one control glider + block at position `k` evolve into generator + block at `k - 1` (`decrement`, `decrement_reaction` with footprint) |
| `Gates` | Components of the machine design, found by own search: `terminatedGun` (gun + eater, period exactly 30), `blockedStream` (two guns annihilating each other's streams, period exactly 30), and `gate` (a control glider releases exactly one glider) |
| `Guns` | The Gosper glider gun for all time (`gosperGun_evolve`, `IsGun`), gliders in flight (`evolve_train`), window unions (`ofRows_orRows`, `ofRows_padRows`) |
| `Increment` | The push generator (ten guns, four reflectors) and the increment for every block position: `pushGenerator_reaction` (1650 generations), `push3_reaction`, `increment` |
| `IncrementContinue` | The push generator with a continue glider: `incrementContinue_evolve` (one control glider ⟶ pushing salvo + continue glider, 2100 generations) |
| `Invariant` | Evolution certificates with a check on every generation's window (`EvolvesW`); tactics `life_invariant` (predicate on cells) and `life_corner` (cheap `x ≤ X ∨ y ≤ Y`) |
| `Locality` | Translation, Chebyshev neighbourhoods, locality of `evolve`, independence of separated patterns (with sharp one-step constant), equivariance, periodicity algebra, bounded implies eventually periodic |
| `Patterns` | Classes `IsStillLife`, `IsOscillator`, `IsSpaceship` and a catalogue with proved behaviour: block, beehive, loaf, boat, pond, eater 1; blinker, toad, beacon, traffic light, pulsar, pentadecathlon; glider, LWSS, MWSS, HWSS |
| `SalvoGenerator` | Found by own search: `reflector` (period exactly 30, turns a glider by a right angle) and `pullGenerator` (six guns, three reflectors): one control glider yields exactly the pulling salvo in 1170 generations (`pullGenerator_reaction`, with a box footprint) |
| `SlidingBlock` | Sliding block memory: `counter k`, the two-glider `pull` and three-glider `push` for every position `k`, and the flight lemma `evolve_flight` |
| `ZeroTestLogic` | The decision part of the zero test: for every register position `k`, the test gliders and a detector give `zOut` if `k = 0` and `nzOut` otherwise, block unchanged (`zeroTest_decision`) |
| `Register` | Pipelined operations on the block: `Op`, `launch`, `SpacedLaunch`, `pipeline` (salvos launched at least 13 cells apart act in order), `two_ops` |
| `Register1`, `Register1Inc`, `Register1Ops` | The register `REG1`: one assembly (16 guns, 14 reflectors) serving one block with a decrement and an increment input; certified input reactions (3120 and 3570 generations); `reg1_decrement`, `reg1_increment` for every position; `salvo_quad_reaction` |
| `DecJzLocal` | The zero test `DZ2` at the block (decrement from zero): the detector turns block `-1` into `dz2DetectorBlock` and passes every block `j ≥ 0` (`dz2Detector_pass`); the restore glider returns it to `-1`; `reg1_increment_neg_one` moves `-1` to `0` |
| `Network` | Composition of many independent processes: `Proc`, `Reaction.parList` (pairwise far apart footprints), idle periodic pieces at any phase (`reaction_periodic_box`), a salvo on the block with a sharp moving footprint (`salvo_track_reaction`) |
| `Chain`, `MergeChain` | Chains of relays of any length by induction (`chain_reaction`: a periodic piece relaying its input to a translate of itself, three separation inequalities); the merge chain of OR gates of `R-29` for every length (`orChain`: copies every `(35, 64)`, `254` generations per copy) |
| `Route` | Routes as lists of relay stages (`Stage`: a period-30 piece turning an input into an output): `Stage.route_reaction` carries the input of the first stage to the output of the last, given pairwise separation of the stages' boxes; `Stage.idle` for a route at rest |
| `Diagonal` | The diagonal of a register (note `N-20`): salvos in flight (`flights_reaction`, `flights_evolve_mul`) and **`diag_strip`**: a block with a valid queue of salvos behind it stays in the strip of its diagonal at every generation |
| `Salvos` | The pulling and pushing salvos of the machine as `Salvo`s (`regPull`, `regPush`) and diagonal parameters for both (`regParams_good`: gap 28) |
| `Simulation` | From a simulation to undecidability (`N-21`): `Simulator P` (encoding, steps inside a region avoiding a halt cell, halting makes the cell alive), `everAlive_of_halts`, `not_everAlive_of_not_halts`, and `not_computablePred_everAlive_of_simulator` |
| `LayoutLP` | The layout `LP` of `R-31` as computable functions of a program (units, modules, tracks, hairpins, channels, stations, tokens) and its arithmetic: the 17 separation inequalities for all programs and indices (`sep01_unitSlabs` … `sep17_diagonal_band`), the nesting lemma `decJz_nested`, residues mod 30 of the routes, token formulas |
| `Placed` | Layer 1 of the assembly (`N-22`): pieces placed by translation and phase (`Piece.place`), and parts of the machine as single pieces (`Piece.ofList`) |
| `RegisterCircuit` | The four generated register-circuit certificates act on one circuit: `dz2mk0Rest_eq`, `dz2mk1Rest_eq`, `dz2jRest_eq` (all equal `dz2gRest`) |
| `RouteExamples` | Instances of stages: the reflector `rf0Stage`, `flightStage`, and a two-stage route `rf0_route` |
| `Rf0Images` | The eight images of the reflector as route stages (`rf0SWNW`, …, `rf0SWSE`): the corner pieces of every route of the layout `R-31` |
| `MergeSide` | The merge chain entered from the side input (residues 5, 6, 9 of `R-29`), for every length: `orChainSide5`, `orChainSide6`, `orChainSide9` (by `chain_side_reaction`) |
| `StationFacts` | The eight local facts of the dispatch station (`R-29`, `R-31`): capture of the answer by the token (NZ, Z), passage (as stages `stPassNZStage`, `stPassZStage`), absorption of an unpaired token, absorption at the line end |
| `Gen/BodyInc*`, `Gen/BodyDec*` | The unit bodies of `R-31` (generated network certificates): `bodyIncRun_rest` (930 generations: chain output to the INC link and the continue glider), `bodyDecRun_rest` (3 180 generations: chain output to the DEC control and the two tokens) |
| `Gen/Dz2mk1*`, `Gen/Dz2mk0*` | Generated certificates (`scripts/life_cert`): the complete zero test `DZ2` in the version of `R-29` (42 pieces, gate `G_I`, one control glider). `dz2mk1Run_rest`: register at `1`, 11 490 generations, block to `0` and the NZ glider out (46 segments). `dz2mk0Run_rest`: register at `0`, 27 540 generations, the block restored to `0` and the Z glider out (112 segments). The circuit ends at rest in both |
| `Gen/Dz2g*` | Generated certificate of `DZ2` (R-29 version) for **every** register position `k ≥ 2` (`dz2gAll`): in `4 k + 11 490` generations the circuit, its control glider and the block at `k` become the circuit in its cycle, the block at `k - 1` and the NZ glider. The block and the salvo are generic processes (`salvo_world_all`, `trajectory_reaction`); planned without the block (`scripts/life_cert/emit_generic.py`) |
| `Gen/Dz2j*` | Generated certificate of the increment of the same circuit (control through the side input of `G_I` at the time used by the layout `R-31`) for **every** `k ≥ 0` (`dz2jAll`): in `4 k + 6 990` generations the block moves from `k` to `k + 1`, the circuit back in its cycle |
| `Reactions` | Reactions with footprints: `Reaction P Q n F`, parallel and sequential composition, placement; the block decrement rebuilt from these rules (`pull_reaction`) |

## Stability/ — comparison and energy methods

| Module | Content |
| --- | --- |
| `Suydam` | Hardy inequality and a localized quadratic form (needed by `Newcomb`) |
| `Newcomb` | Picone–Riccati certificates for variable-coefficient radial quadratic forms |
| `RiccatiComparison` | Conditional Riccati comparison and exponential decay |
| `AbstractEnergy` | Conditional energy theorem on a real normed space |
| `BlockBounds` | Quantitative two-block and perturbation inequalities |

## Fields/ — vector calculus and ODE barriers

| Module | Content |
| --- | --- |
| `VectorCalculus` | `Space = ℝ³`, cross product, `divergence`, `curl`, the curl product rule, `IsForwardFieldLine`, complex vectors `CVec` |
| `LieGradient` | The Lie-derivative/gradient commutator |
| `InvariantBarrier` | Invariant level sets as all-time Grönwall barriers |
| `FieldLineExistence` | Global existence and uniqueness of solutions trapped in a compact set |
