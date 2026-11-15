/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Computability.CounterMachineUniversal

/-!
# Counter programs with a single `halt`

The Life realization of a counter program needs the program to have exactly one `halt`
instruction, its last one: a halt corner of an earlier `halt` would lie on the path of the glider
of a later one. This file shows that this is no loss of generality.

## Normalization

For a program `P`, the register `P.freshReg = max 1 (max over instructions of (register + 1))`
is mentioned by no instruction of `P` and differs from the input register `0`; it is therefore
zero along every run from an initial configuration `Cfg.init n`. The program `P.singleHalt`
keeps the last instruction of `P` (a `halt`, when `P` is well formed) and replaces every other
`halt` by the unconditional jump `decJz P.freshReg (P.length - 1)` to the last instruction. A
`halt` of `P` at `i` thus becomes one extra step followed by the final `halt`; every other step of
`P` is a step of `P.singleHalt`.

`P.freshReg` is, by definition, the quantity `LP.numRegs P` of the Life layout
(`LeanTheory.Theory.Life.LayoutLP`): when some `halt` is replaced, `P.singleHalt` mentions the
register `P.freshReg`, so `LP.numRegs P.singleHalt = P.freshReg + 1` counts it automatically.

## Main definitions

* `Instr.regBound`, `Instr.unhalt`, `Program.SingleHalt`, `Program.freshReg`,
  `Program.singleHalt`.

## Main results

* `Program.getElem?_singleHalt`: the instructions of `P.singleHalt`.
* `Program.WellFormed.singleHalt`, `Program.singleHalt_singleHalt`: `P.singleHalt` is well formed
  and has a single `halt`.
* `Program.halts_singleHalt_iff`, `Program.halts_init_singleHalt`: `P.singleHalt` halts exactly
  when `P` does.
* `exists_program_halts_not_computable_single`: a well-formed counter program with a single
  `halt` whose halting set is not computable.

## Sanity checks

* `singleHalt_twoHalts`: the normalization of `[halt, halt]` is `[decJz 1 1, halt]`.
-/

@[expose] public section

namespace LeanTheory.Computability

open Function

/-- One more than the register mentioned by an instruction; `0` for `halt`. -/
def Instr.regBound : Instr → ℕ
  | .inc r => r + 1
  | .decJz r _ => r + 1
  | .halt => 0

/-- The instruction with `halt` replaced by the jump `decJz z l`; other instructions unchanged. -/
def Instr.unhalt (z l : ℕ) : Instr → Instr
  | .inc r => .inc r
  | .decJz r l' => .decJz r l'
  | .halt => .decJz z l

/-- `unhalt` never produces `halt`. -/
theorem Instr.unhalt_ne_halt (z l : ℕ) (i : Instr) : i.unhalt z l ≠ .halt := by
  cases i <;> simp [Instr.unhalt]

/-- `unhalt` fixes every instruction other than `halt`. -/
theorem Instr.unhalt_of_ne {z l : ℕ} {i : Instr} (h : i ≠ .halt) : i.unhalt z l = i := by
  cases i with
  | inc r => rfl
  | decJz r l' => rfl
  | halt => exact absurd rfl h

namespace Program

/-- A program has a single `halt` when no instruction other than the last one is `halt`. -/
def SingleHalt (P : Program) : Prop := ∀ i < P.length - 1, P[i]? ≠ some .halt

/-- A register mentioned by no instruction of `P` and different from the input register `0`:
`max 1 (max over instructions of (register + 1))`. -/
def freshReg (P : Program) : ℕ := max 1 ((P.map Instr.regBound).foldr max 0)

/-- The normalization of `P`: every instruction but the last is kept, except that `halt` is
replaced by the jump `decJz P.freshReg (P.length - 1)` to the last instruction; the last
instruction is `halt`. -/
def singleHalt (P : Program) : Program :=
  P.dropLast.map (Instr.unhalt P.freshReg (P.length - 1)) ++ [.halt]

/-- The register bound of an instruction of `P` is at most the maximum over `P`. -/
theorem regBound_le_foldr {P : Program} {i : Instr} (h : i ∈ P) :
    i.regBound ≤ (P.map Instr.regBound).foldr max 0 := by
  induction P with
  | nil => cases h
  | cons a P ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The fresh register is not the input register `0`. -/
theorem one_le_freshReg (P : Program) : 1 ≤ P.freshReg := le_max_left _ _

/-- The fresh register is not incremented by `P`. -/
theorem inc_freshReg_not_mem (P : Program) : .inc P.freshReg ∉ P := by
  intro h
  have h₁ := regBound_le_foldr h
  have h₂ : (P.map Instr.regBound).foldr max 0 ≤ P.freshReg := le_max_right _ _
  simp only [Instr.regBound] at h₁
  omega

/-- The fresh register is not tested by `P`. -/
theorem decJz_freshReg_not_mem (P : Program) (l : ℕ) : .decJz P.freshReg l ∉ P := by
  intro h
  have h₁ := regBound_le_foldr h
  have h₂ : (P.map Instr.regBound).foldr max 0 ≤ P.freshReg := le_max_right _ _
  simp only [Instr.regBound] at h₁
  omega

/-- The fresh register is zero in every initial configuration. -/
theorem init_regs_freshReg (P : Program) (n : ℕ) : (Cfg.init n).regs P.freshReg = 0 := by
  have := P.one_le_freshReg
  simp [Cfg.init, update, show P.freshReg ≠ 0 by omega]

/-- The normalization of a nonempty program has the same length. -/
theorem length_singleHalt {P : Program} (hP : 0 < P.length) :
    P.singleHalt.length = P.length := by
  simp [singleHalt]
  omega

/-- The instructions of the normalization of a nonempty program. -/
theorem getElem?_singleHalt {P : Program} (hP : 0 < P.length) (pc : ℕ) :
    P.singleHalt[pc]? = if pc + 1 = P.length then some .halt
      else P[pc]?.map (Instr.unhalt P.freshReg (P.length - 1)) := by
  have hlen : (P.dropLast.map (Instr.unhalt P.freshReg (P.length - 1))).length =
      P.length - 1 := by simp
  unfold singleHalt
  by_cases h₁ : pc < P.length - 1
  · rw [List.getElem?_append_left (by omega), List.getElem?_map, List.getElem?_dropLast,
      ite_eq_left h₁, ite_eq_right (by omega)]
  · rw [List.getElem?_append_right (by omega), hlen]
    by_cases h₂ : pc + 1 = P.length
    · rw [ite_eq_left h₂, show pc - (P.length - 1) = 0 by omega]
      rfl
    · rw [ite_eq_right h₂, List.getElem?_eq_none (show P.length ≤ pc by omega),
        List.getElem?_eq_none (by simp; omega)]
      rfl

/-- The last instruction of a well-formed program is `halt`. -/
theorem WellFormed.getElem?_last {P : Program} (hP : P.WellFormed) :
    P[P.length - 1]? = some .halt := by
  rw [← List.getLast?_eq_getElem?]
  exact hP.2

/-- A well-formed program is nonempty. -/
theorem WellFormed.length_pos {P : Program} (hP : P.WellFormed) : 0 < P.length := by
  rcases P with _ | ⟨a, P⟩
  · simp [WellFormed] at hP
  · simp

/-- The normalization of a well-formed program is well formed. -/
theorem WellFormed.singleHalt {P : Program} (hP : P.WellFormed) : P.singleHalt.WellFormed := by
  refine ⟨fun r l h => ?_, by simp [Program.singleHalt]⟩
  rw [length_singleHalt hP.length_pos]
  simp only [Program.singleHalt, List.mem_append, List.mem_map, List.mem_singleton,
    reduceCtorEq, or_false] at h
  obtain ⟨i, hi, he⟩ := h
  cases i with
  | inc r' => cases he
  | decJz r' l' =>
    simp only [Instr.unhalt, Instr.decJz.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hP.1 _ _ (List.dropLast_subset _ hi)
  | halt =>
    simp only [Instr.unhalt, Instr.decJz.injEq] at he
    obtain ⟨-, rfl⟩ := he
    have := hP.length_pos
    omega

/-- The normalization of a nonempty program has a single `halt`. -/
theorem singleHalt_singleHalt {P : Program} (hP : 0 < P.length) : P.singleHalt.SingleHalt := by
  intro i hi
  rw [length_singleHalt hP] at hi
  rw [getElem?_singleHalt hP, ite_eq_right (by omega)]
  rcases P[i]? with _ | a
  · simp
  · simp [Instr.unhalt_ne_halt]

/-- Away from a `halt` of `P`, the normalization of a well-formed `P` steps as `P` does. -/
theorem step_singleHalt_of_ne {P : Program} (hP : P.WellFormed) {c : Cfg}
    (h : P[c.pc]? ≠ some .halt) : P.singleHalt.step c = P.step c := by
  have hget : P.singleHalt[c.pc]? = P[c.pc]? := by
    rw [getElem?_singleHalt hP.length_pos]
    by_cases h₁ : c.pc + 1 = P.length
    · rw [show c.pc = P.length - 1 by omega] at h
      exact absurd hP.getElem?_last h
    · rw [ite_eq_right h₁]
      rcases hi : P[c.pc]? with _ | a
      · rfl
      · rw [hi] at h
        simp [Instr.unhalt_of_ne (fun e => h (e ▸ rfl))]
  simp only [step, hget]

/-- The normalization of a well-formed program stops at its last instruction. -/
theorem step_singleHalt_last {P : Program} (hP : P.WellFormed) (σ : ℕ → ℕ) :
    P.singleHalt.step ⟨P.length - 1, σ⟩ = none := by
  have := hP.length_pos
  exact step_of_halt (by rw [getElem?_singleHalt this, ite_eq_left (by simp; omega)])

/-- At a `halt` of `P` other than the last instruction, the normalization jumps to the last
instruction, provided the fresh register is zero. -/
theorem step_singleHalt_of_halt {P : Program} (hP : P.WellFormed) {c : Cfg}
    (h : P[c.pc]? = some .halt) (hne : c.pc + 1 ≠ P.length) (hz : c.regs P.freshReg = 0) :
    P.singleHalt.step c = some ⟨P.length - 1, c.regs⟩ := by
  refine step_of_decJz_zero ?_ hz
  rw [getElem?_singleHalt hP.length_pos, ite_eq_right hne, h]
  rfl

/-- **Simulation.** From a configuration whose fresh register is zero, the normalization of a
well-formed program halts exactly when the program does. -/
theorem halts_singleHalt_iff {P : Program} (hP : P.WellFormed) {c : Cfg}
    (hc : c.regs P.freshReg = 0) : P.singleHalt.Halts c ↔ P.Halts c := by
  constructor
  · intro h
    refine Halts.induction (C := fun d => P.Halts d) h ?_
    rintro d - IH
    rcases hs : P.step d with _ | d'
    · exact halts_of_step_eq_none hs
    · have hne : P[d.pc]? ≠ some .halt := fun e => by rw [step_of_halt e] at hs; cases hs
      have hs' : P.singleHalt.step d = some d' := by rw [step_singleHalt_of_ne hP hne, hs]
      exact (halts_iff_of_reaches (Reaches.single hs)).2 (IH d' (Reaches₁.single hs'))
  · intro h
    refine Halts.induction (C := fun d => d.regs P.freshReg = 0 → P.singleHalt.Halts d) h ?_ hc
    rintro d - IH hz
    rcases hs : P.step d with _ | d'
    · by_cases hh : P[d.pc]? = some .halt
      · by_cases hl : d.pc + 1 = P.length
        · have e : d = ⟨P.length - 1, d.regs⟩ := by ext <;> simp; omega
          rw [e]
          exact halts_of_step_eq_none (step_singleHalt_last hP _)
        · have s := step_singleHalt_of_halt hP hh hl hz
          exact (halts_iff_of_reaches (Reaches.single s)).2
            (halts_of_step_eq_none (step_singleHalt_last hP _))
      · exact halts_of_step_eq_none (by rw [step_singleHalt_of_ne hP hh, hs])
    · have hne : P[d.pc]? ≠ some .halt := fun e => by rw [step_of_halt e] at hs; cases hs
      have hs' : P.singleHalt.step d = some d' := by rw [step_singleHalt_of_ne hP hne, hs]
      have hz' : d'.regs P.freshReg = 0 := by
        rw [step_regs_of_forall_ne hs (inc_freshReg_not_mem P) (decJz_freshReg_not_mem P), hz]
      exact (halts_iff_of_reaches (Reaches.single hs')).2 (IH d' (Reaches₁.single hs) hz')

/-- On every input, the normalization of a well-formed program halts exactly when the program
does. -/
theorem halts_init_singleHalt {P : Program} (hP : P.WellFormed) (n : ℕ) :
    P.singleHalt.Halts (Cfg.init n) ↔ P.Halts (Cfg.init n) :=
  halts_singleHalt_iff hP (init_regs_freshReg P n)

end Program

open Program

/-- **An undecidable halting problem for one counter program with a single `halt`.** There is a
well-formed counter program `P` whose only `halt` is its last instruction, such that no algorithm
determines, given `n`, whether `P` halts on the input `n`. -/
theorem exists_program_halts_not_computable_single :
    ∃ P : Program, P.WellFormed ∧ P.SingleHalt ∧
      ¬ComputablePred fun n : ℕ => P.Halts (Cfg.init n) := by
  obtain ⟨P, hP, hnc⟩ := exists_program_halts_not_computable
  refine ⟨P.singleHalt, hP.singleHalt, singleHalt_singleHalt hP.length_pos, ?_⟩
  have e : (fun n : ℕ => P.singleHalt.Halts (Cfg.init n)) = fun n => P.Halts (Cfg.init n) :=
    funext fun n => propext (halts_init_singleHalt hP n)
  rwa [e]

/-- Sanity check: the normalization of `[halt, halt]` jumps over register `1` to the final
`halt`. -/
theorem singleHalt_twoHalts : Program.singleHalt [.halt, .halt] = [.decJz 1 1, .halt] := rfl

end LeanTheory.Computability
