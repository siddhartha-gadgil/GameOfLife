/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Decision
public import LeanTheory.Theory.Computability.CounterMachineUniversal

/-!
# From a simulation of a counter program to undecidability

Research note `N-21`. A *simulator* of a counter program `P` in Life is an encoding of (extended)
machine states as finite configurations such that every step of `P` is a finite piece of the
evolution, staying inside a region that avoids a fixed *halt cell*, and a halted machine makes the
halt cell alive. This module proves, for any such simulator:

* `Simulator.everAlive_of_halts`: if `P` halts, the halt cell is ever alive;
* `Simulator.not_everAlive_of_not_halts`: if `P` runs for ever, the halt cell is never alive;
* `not_computablePred_everAlive_of_simulator`: if the halting of `P` on the input `n` is
  undecidable and the start configurations form a computable family of window data, then whether a
  given cell is ever alive in the evolution of a given finite configuration is undecidable.

What remains for the goal `G-7` is to construct a simulator for every well-formed program (the
layout `R-31`, the components and the register diagonals).
-/

@[expose] public section

namespace LeanTheory.Life

open LeanTheory.Computability

/-- A simulator of the counter program `P` in Life. -/
structure Simulator (P : Program) where
  /-- Extended states of the simulation (the configuration of the machine and the bookkeeping
  of the pattern, such as salvos still in flight). -/
  S : Type
  /-- The configuration of the counter machine. -/
  proj : S → Cfg
  /-- The pattern encoding a state, at the start of a step. -/
  enc : S → Finset Cell
  /-- An invariant of the simulation. -/
  Inv : S → Prop
  /-- The next state. -/
  next : S → S
  /-- The duration of a step. -/
  dur : S → ℕ
  /-- The region of the machine. -/
  region : Set Cell
  /-- The halt cell. -/
  cH : Cell
  /-- The halt cell is outside the region of the machine. -/
  cH_notMem : cH ∉ region
  /-- A step takes at least one generation. -/
  dur_pos : ∀ s, 0 < dur s
  /-- **A step of the program is a piece of the evolution**, inside the region. -/
  step : ∀ s c', Inv s → P.step (proj s) = some c' →
    proj (next s) = c' ∧ Inv (next s) ∧ conway.evolve (dur s) (enc s) = enc (next s) ∧
      ∀ i ≤ dur s, (conway.evolve i (enc s) : Set Cell) ⊆ region
  /-- **A halted machine makes the halt cell alive.** -/
  halt : ∀ s, Inv s → P.step (proj s) = none → EverAlive cH (enc s)

namespace Simulator

variable {P : Program} (M : Simulator P)

/-- A configuration without a successor halts. -/
theorem halts_of_step_none {c : Cfg} (h : P.step c = none) : P.Halts c :=
  Part.dom_iff_mem.2 ⟨c, StateTransition.mem_eval.2 ⟨Relation.ReflTransGen.refl, h⟩⟩

/-- A configuration whose successor halts halts. -/
theorem halts_of_step_some {c c' : Cfg} (h : P.step c = some c') (h' : P.Halts c') :
    P.Halts c := by
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 h'
  obtain ⟨hr, hn⟩ := StateTransition.mem_eval.1 hb
  exact Part.dom_iff_mem.2 ⟨b, StateTransition.mem_eval.2
    ⟨Relation.ReflTransGen.head (by rw [h]; rfl) hr, hn⟩⟩

/-- Ever alive is preserved backwards along the evolution. -/
theorem everAlive_of_evolve {c : Cell} {S : Finset Cell} {n : ℕ}
    (h : EverAlive c (conway.evolve n S)) : EverAlive c S := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t + n, by rw [Rule.evolve_add]; exact ht⟩

/-- **If the program halts, the halt cell is ever alive.** -/
theorem everAlive_of_halts {s : M.S} (hs : M.Inv s) (h : P.Halts (M.proj s)) :
    EverAlive M.cH (M.enc s) := by
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 h
  obtain ⟨hr, hn⟩ := StateTransition.mem_eval.1 hb
  suffices key : ∀ c, StateTransition.Reaches P.step c b →
      ∀ s, M.proj s = c → M.Inv s → EverAlive M.cH (M.enc s) from key _ hr s rfl hs
  intro c hc
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s hs1 hs2
    exact M.halt s hs2 (hs1 ▸ hn)
  | @head a c1 h1 _ ih =>
    intro s hs1 hs2
    have hstep : P.step (M.proj s) = some c1 := by rw [hs1]; exact Option.mem_def.1 h1
    obtain ⟨hp, hi, he, -⟩ := M.step s _ hs2 hstep
    exact everAlive_of_evolve (he ▸ ih _ hp hi)

/-- **If the program runs for ever, the halt cell is never alive.** -/
theorem not_everAlive_of_not_halts {s : M.S} (hs : M.Inv s) (h : ¬ P.Halts (M.proj s)) :
    ¬ EverAlive M.cH (M.enc s) := by
  rintro ⟨t, ht⟩
  induction t using Nat.strong_induction_on generalizing s with
  | _ t ih =>
    cases hc : P.step (M.proj s) with
    | none => exact h (halts_of_step_none hc)
    | some c' =>
      obtain ⟨hp, hi, he, hreg⟩ := M.step s c' hs hc
      by_cases htd : t ≤ M.dur s
      · exact M.cH_notMem (hreg t htd (Finset.mem_coe.2 ht))
      · have hpos := M.dur_pos s
        refine ih (t - M.dur s) (by omega) hi (fun hh => h (halts_of_step_some hc (hp ▸ hh))) ?_
        rw [← he, ← Rule.evolve_add, show t - M.dur s + M.dur s = t by omega]
        exact ht

end Simulator

/-- **Undecidability from a simulator.** If the halting of `P` on the input `n` is undecidable,
and a simulator of `P` starts on the input `n` from the configuration `(f n).cells` of a computable
family of window data, then it is undecidable whether a given cell is ever alive in the evolution of
a given finite configuration. -/
theorem not_computablePred_everAlive_of_simulator {P : Program} (M : Simulator P)
    (hP : ¬ ComputablePred fun n : ℕ => P.Halts (Cfg.init n)) (start : ℕ → M.S)
    (hstart : ∀ n, M.proj (start n) = Cfg.init n) (hinv : ∀ n, M.Inv (start n))
    (f : ℕ → WindowData) (hf : Computable f) (hcells : ∀ n, (f n).cells = M.enc (start n)) :
    ¬ ComputablePred fun w : WindowData => EverAlive M.cH w.cells := by
  refine not_computablePred_everAlive_of_family M.cH f hf fun h => hP ?_
  have e : (fun n : ℕ => EverAlive M.cH (f n).cells) = fun n => P.Halts (Cfg.init n) := by
    funext n
    rw [hcells n, ← hstart n]
    exact propext ⟨fun h' => by
      by_contra hn
      exact M.not_everAlive_of_not_halts (hinv n) hn h', M.everAlive_of_halts (hinv n)⟩
  rwa [e] at h

end LeanTheory.Life
