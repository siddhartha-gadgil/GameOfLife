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
