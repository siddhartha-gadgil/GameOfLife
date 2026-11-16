/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ComputationRun
public import LeanTheory.Theory.Computability.CounterMachineSingleHaltComputes

/-!
# The Game of Life computes every partial recursive function

Research note `N-23`, the target `T2` of `N-12`, with the output decoding. Together with the
undecidability of `EverAlive` (`LP.exists_not_computablePred_everAlive'`, `DecSepAll.lean`) this
is the content of "the Game of Life is Turing complete" for finite configurations.

**The statement** (`life_universal`): there are one cell `c`, one computable encoding
`f : Nat.Partrec.Code → ℕ → WindowData` of a code and an input as a finite configuration, and one
computable decoding `decode : Finset Cell → ℕ`, such that for every code and input:

* `code.eval n` is defined iff the cell `c` is alive at some generation of the evolution of
  `(f code n).cells`;
* if `code.eval n` has the value `m`, then `decode` of every generation from some time on is `m`.

The encoding is the start family of the Life machine of one fixed universal counter program `U`
(it computes `k ↦ eval (ofNat k.unpair.1) k.unpair.2`), on the input `pair (encode code) n`. The
cell `c` is the halt cell of `U`'s machine, and `decode` is the explicit `readOut`: the first live
cell of the ray of register `0` (`life_universal'` states this form). Neither depends on the
code or the input.

* `life_computes_single`: for one well-formed single-halt program, its Life machine, halt cell
  and `readOut` on its register-`0` ray (the composition of the simulator,
  `exists_evolve_of_reaches` and `readOut_late`);
* `life_computes_of_computes`: for every well-formed program computing `f` (through
  `Program.singleHalt`, which keeps the output: `Program.Computes.singleHalt`);
* `life_universal'`, `life_universal`: the uniform form.
-/

@[expose] public section

namespace LeanTheory.Life

open LeanTheory.Computability LP

/-- **A single-halt program computed by its Life machine**: for a well-formed program `P` with a
single `halt` computing `f`, and the windows `F n` of its start configurations, `f n` is defined
iff the halt cell of the machine is ever alive, and its value is read by `readOut` on the ray of
register `0` at every late enough generation. -/
theorem life_computes_single {P : Program} (hp : P.WellFormed) (hs : P.SingleHalt)
    {f : ℕ →. ℕ} (h : P.Computes f) (F : ℕ → WindowData)
    (hF : ∀ n, (F n).cells = encM P (startM n)) (n : ℕ) :
    ((f n).Dom ↔ EverAlive (haltCellC P) (F n).cells) ∧
      ∀ m ∈ f n, ∃ T, ∀ t ≥ T,
        readOut (blockX P) (blockY P) (conway.evolve t (F n).cells) = m := by
  have M := machineSteps_of_decSepRest hp hs (dsep_rest hp)
  set Sim := simulatorOf hp hs M
  have hcfg : Sim.proj (startM n) = Cfg.init n := startM_cfg n
  have hinv : Sim.Inv (startM n) := startM_minv hp n
  refine ⟨?_, fun m hm => ?_⟩
  · rw [← h.halts_iff n, hF n]
    constructor
    · intro hh
      exact Sim.everAlive_of_halts hinv (hcfg ▸ hh)
    · intro he
      by_contra hn
      exact Sim.not_everAlive_of_not_halts hinv (hcfg ▸ hn) he
  · rw [← h n, Part.mem_map_iff] at hm
    obtain ⟨cf, hcf, rfl⟩ := hm
    obtain ⟨hr, hstop⟩ := Program.mem_eval.1 hcf
    obtain ⟨t₀, s, he, hi, hc⟩ :=
      exists_evolve_of_reaches hp M hr (startM n) (startM_cfg n) (startM_minv hp n)
    have hins : P[s.pc]? = some .halt := halt_of_step_none hi.1 (hc ▸ hstop)
    have hsep : HaltSep P s.pc := pc_of_halt hs hins ▸ M.haltSep
    obtain ⟨T, hT⟩ := readOut_late hp s hi.1 hins hsep
    refine ⟨T + t₀, fun t ht => ?_⟩
    rw [hF n, show t = (t - t₀) + t₀ by omega, Rule.evolve_add, he, hT _ (by omega), ← hc]
    rfl

/-- **Every counter-computable function is computed by Life**: for a well-formed counter program
`P` computing `f`, there are a cell `c`, a computable encoding `F` of the inputs as finite
configurations and a computable decoding such that `f n` is defined iff `c` is ever alive in the
evolution of `(F n).cells`, and then the decoding of every late enough generation is `f n`. -/
theorem life_computes_of_computes {P : Program} (hp : P.WellFormed) {f : ℕ →. ℕ}
    (h : P.Computes f) :
    ∃ (c : Cell) (F : ℕ → WindowData) (decode : Finset Cell → ℕ),
      Computable F ∧ DecodeComputable decode ∧
      ∀ n, ((f n).Dom ↔ EverAlive c (F n).cells) ∧
        ∀ m ∈ f n, ∃ T, ∀ t ≥ T, decode (conway.evolve t (F n).cells) = m := by
  set Q := P.singleHalt
  have hQ : Q.WellFormed := hp.singleHalt
  have hs : Q.SingleHalt := Program.singleHalt_singleHalt hp.length_pos
  obtain ⟨F, hFc, hF⟩ := exists_startFamily Q
  exact ⟨haltCellC Q, F, readOut (blockX Q) (blockY Q), hFc, readOut_computable _ _,
    life_computes_single hQ hs (h.singleHalt hp) F hF⟩

/-- The universal function `k ↦ eval (ofNat k.unpair.1) k.unpair.2` is partial recursive. -/
theorem nat_partrec_universal :
    Nat.Partrec fun k : ℕ =>
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code k.unpair.1) k.unpair.2 :=
  Partrec.nat_iff.1 (Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Nat.Partrec.Code).comp (Computable.fst.comp Primrec.unpair.to_comp))
    (Computable.snd.comp Primrec.unpair.to_comp))

/-- **The Game of Life computes every partial recursive function, uniformly, with the explicit
decoding `readOut`**: there are a cell `c`, a base cell `(x₀, y₀)` and a computable encoding
`f code n` of a code and an input as a finite configuration (the Life machine of one universal
counter program on the input `pair (encode code) n`) such that `code.eval n` is defined iff `c`
is ever alive, and then the first live cell of the ray `(x₀ + k, y₀ + k)` is at `k = code.eval n`
from some generation on. -/
theorem life_universal' :
    ∃ (c : Cell) (x₀ y₀ : ℤ) (f : Nat.Partrec.Code → ℕ → WindowData),
      Computable₂ f ∧
      ∀ code n, ((code.eval n).Dom ↔ EverAlive c (f code n).cells) ∧
        ∀ m ∈ code.eval n, ∃ T, ∀ t ≥ T, readOut x₀ y₀ (conway.evolve t (f code n).cells) = m := by
  obtain ⟨P, hp, h⟩ := exists_computes_of_partrec nat_partrec_universal
  set Q := P.singleHalt
  have hQ : Q.WellFormed := hp.singleHalt
  have hs : Q.SingleHalt := Program.singleHalt_singleHalt hp.length_pos
  obtain ⟨F, hFc, hF⟩ := exists_startFamily Q
  refine ⟨haltCellC Q, blockX Q, blockY Q, fun code n => F (Nat.pair (Encodable.encode code) n),
    ?_, fun code n => ?_⟩
  · exact hFc.comp (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd).to_comp
  · have e := life_computes_single hQ hs (h.singleHalt hp) F hF (Nat.pair (Encodable.encode code) n)
    simp only [Nat.unpair_pair, Denumerable.ofNat_encode] at e
    exact e

/-- **The Game of Life computes every partial recursive function** (the target `T2` of `N-12`,
uniform form): there are a cell `c`, a computable encoding `f` of a code and an input as a finite
configuration and a computable decoding `decode` of finite configurations, both independent of the
code and the input, such that `code.eval n` is defined iff `c` is alive at some generation of the
evolution of `(f code n).cells`, and then the decoding of every late enough generation is the
value `code.eval n`. The decoding is `readOut` (`life_universal'`). -/
theorem life_universal :
    ∃ (c : Cell) (f : Nat.Partrec.Code → ℕ → WindowData) (decode : Finset Cell → ℕ),
      Computable₂ f ∧ DecodeComputable decode ∧
      ∀ code n, ((code.eval n).Dom ↔ EverAlive c (f code n).cells) ∧
        ∀ m ∈ code.eval n, ∃ T, ∀ t ≥ T, decode (conway.evolve t (f code n).cells) = m := by
  obtain ⟨c, x₀, y₀, f, hf, h⟩ := life_universal'
  exact ⟨c, f, readOut x₀ y₀, hf, readOut_computable x₀ y₀, h⟩

end LeanTheory.Life
