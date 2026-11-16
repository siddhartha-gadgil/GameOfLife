/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Computability.CounterMachineSingleHalt

/-!
# The single-`halt` normalization preserves outputs

Research note `N-23`. `CounterMachineSingleHalt.lean` shows that `P.singleHalt` halts exactly when
`P` does. Here the registers of the final configurations are compared: an earlier `halt` of `P`
becomes the jump `decJz P.freshReg (P.length - 1)`, which leaves every register unchanged, so the
two runs end with the same registers.

* `Program.eval_singleHalt_regs`: from a configuration whose fresh register is zero, the final
  registers of `P.singleHalt` are those of `P` (as partial values);
* `Program.Computes.singleHalt`: if a well-formed `P` computes `f`, so does `P.singleHalt`.
-/

@[expose] public section

namespace LeanTheory.Computability

namespace Program

/-- The final registers of a halting run of `P` are those of a halting run of `P.singleHalt`
(from a configuration whose fresh register is zero). -/
theorem exists_eval_singleHalt {P : Program} (hP : P.WellFormed) {c d : Cfg}
    (hr : P.Reaches c d) (hd : P.step d = none) (hz : c.regs P.freshReg = 0) :
    ∃ e, P.singleHalt.eval c = Part.some e ∧ e.regs = d.regs := by
  revert hz
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hz
    rcases step_eq_none_iff.1 hd with hh | hl
    · by_cases hlast : d.pc + 1 = P.length
      · refine ⟨d, eval_eq_some (Reaches.refl d) ?_, rfl⟩
        have e : d = ⟨P.length - 1, d.regs⟩ := by ext <;> simp; omega
        rw [e]
        exact step_singleHalt_last hP _
      · have s := step_singleHalt_of_halt hP hh hlast hz
        exact ⟨_, eval_eq_some (Reaches.single s) (step_singleHalt_last hP _), rfl⟩
    · refine ⟨d, eval_eq_some (Reaches.refl d) (step_of_length_le ?_), rfl⟩
      rw [length_singleHalt hP.length_pos]
      exact hl
  | @head a b h1 _ ih =>
    intro hz
    have hs : P.step a = some b := h1
    have hne : P[a.pc]? ≠ some .halt := fun e => by rw [step_of_halt e] at hs; cases hs
    have hs' : P.singleHalt.step a = some b := by rw [step_singleHalt_of_ne hP hne, hs]
    have hz' : b.regs P.freshReg = 0 := by
      rw [step_regs_of_forall_ne hs (inc_freshReg_not_mem P) (decJz_freshReg_not_mem P), hz]
    obtain ⟨e, he, hre⟩ := ih hz'
    exact ⟨e, by rw [eval_eq_of_reaches (Reaches.single hs'), he], hre⟩

/-- **The normalization keeps the final registers**: from a configuration whose fresh register
is zero, the registers at the end of the run of `P.singleHalt` are those at the end of the run of
`P`, as partial values. -/
theorem eval_singleHalt_regs {P : Program} (hP : P.WellFormed) {c : Cfg}
    (hz : c.regs P.freshReg = 0) :
    (P.singleHalt.eval c).map Cfg.regs = (P.eval c).map Cfg.regs := by
  by_cases hh : P.Halts c
  · obtain ⟨d, hr, hd⟩ := halts_iff.1 hh
    obtain ⟨e, he, hre⟩ := exists_eval_singleHalt hP hr hd hz
    rw [he, eval_eq_some hr hd, Part.map_some, Part.map_some, hre]
  · have hh' : ¬ P.singleHalt.Halts c := fun h => hh ((halts_singleHalt_iff hP hz).1 h)
    rw [Part.eq_none_iff'.2 hh, Part.eq_none_iff'.2 hh']

/-- **The normalization computes the same function**: if a well-formed program `P` computes
`f`, so does `P.singleHalt`. -/
theorem Computes.singleHalt {P : Program} (hP : P.WellFormed) {f : ℕ →. ℕ}
    (h : P.Computes f) : P.singleHalt.Computes f := by
  intro n
  have e := eval_singleHalt_regs hP (init_regs_freshReg P n)
  have e2 : ∀ Q : Program, (Q.eval (Cfg.init n)).map (fun c => c.regs 0) =
      ((Q.eval (Cfg.init n)).map Cfg.regs).map (fun σ => σ 0) := fun Q => by
    rw [Part.map_map]
    rfl
  rw [e2, e, ← e2]
  exact h n

end Program

end LeanTheory.Computability
