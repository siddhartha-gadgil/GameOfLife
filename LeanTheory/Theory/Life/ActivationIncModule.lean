/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncLinks
public import LeanTheory.Theory.Life.Gen.Dz2e1Run
public import LeanTheory.Theory.Life.Gen.Dz2e2Run
public import LeanTheory.Theory.Life.Gen.Dz2e3Run

/-!
# The increment at the module for every arrival phase

The register operation `dz2eOp` needs the merge time of the pushing salvo to be `≡ 0 (mod 4)` on
the clock of the register diagonal; `dz2e1Op`, `dz2e2Op`, `dz2e3Op` (salvos `regPushP1 … 3`,
`SalvoPhases`) cover the other three phases. This module chooses the variant by the residue:

* `incPhase m`: the variant for a diagonal `m` generations after its reference time;
* `RegS.pushAny`: the register after the increment, with the salvo of that variant;
* `dz2eAny_module`: the increment at module `r` for **every** `m`;
* `RegS.val_pushAny`, `RegS.inv_pushAny`: the value grows by one and the invariant is kept.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- The register circuit of the run `dz2e1` is the one of `dz2e`. -/
theorem dz2e1Rest_eq : dz2e1Rest = dz2eRest := by
  simp only [dz2e1Rest, dz2eRest]
  rfl

/-- The register circuit of the run `dz2e2` is the one of `dz2e`. -/
theorem dz2e2Rest_eq : dz2e2Rest = dz2eRest := by
  simp only [dz2e2Rest, dz2eRest]
  rfl

/-- The register circuit of the run `dz2e3` is the one of `dz2e`. -/
theorem dz2e3Rest_eq : dz2e3Rest = dz2eRest := by
  simp only [dz2e3Rest, dz2eRest]
  rfl

/-- The variant of the increment for a diagonal `m` generations after its reference time: the
`j` with `m + 6653 + j ≡ 0 (mod 4)`. -/
def incPhase (m : ℕ) : ℕ := (4 - (m + 6653) % 4) % 4

/-- The pushing salvo of variant `j`. -/
def pushSalvo : ℕ → Salvo
  | 0 => regPush
  | 1 => regPushP1
  | 2 => regPushP2
  | _ => regPushP3

/-- The offset base of the pushing salvo of variant `j`. -/
def pushBase : ℕ → ℤ
  | 0 => 7
  | 1 => 7
  | _ => 6

/-- Every pushing salvo moves the block forward by one. -/
theorem pushSalvo_d (j : ℕ) : (pushSalvo j).d = 1 := by
  rcases j with _ | _ | _ | j <;> rfl

/-- The salvo appended by the increment of a register `m` generations after its reference. -/
def pushOf (m : ℕ) : Salvo × ℤ :=
  (pushSalvo (incPhase m), pushBase (incPhase m) + (((m + 6653 + incPhase m) / 4 : ℕ) : ℤ))

/-- The register after the increment, for every arrival phase. -/
def RegS.pushAny (R : RegS) (Vs' : ℤ) : RegS :=
  ⟨R.q ++ [pushOf R.m], R.K, R.m + 6990, Vs', R.Vb⟩

/-- **The increment raises the value of the register by one** (every phase). -/
theorem RegS.val_pushAny (R : RegS) (hR : R.Inv) (Vs' : ℤ) : (R.pushAny Vs').val = R.val + 1 := by
  have := hR.2.2.2
  simp only [RegS.val, RegS.pushAny, pushOf, qMove_append, pushSalvo_d]
  omega

/-- The register after the increment satisfies the invariant (every phase). -/
theorem RegS.inv_pushAny {R : RegS} (hR : R.Inv) {Vs' : ℤ}
    (hv' : DiagValid regParams Vs' R.Vb R.K (R.q ++ [pushOf R.m]))
    (hVs' : -34 ≤ Vs' + 2 * (((R.m + 6653 + incPhase R.m) / 4 : ℕ) : ℤ)) :
    (R.pushAny Vs').Inv := by
  obtain ⟨-, h2, -, h4⟩ := hR
  have hj : incPhase R.m < 4 := Nat.mod_lt _ (by norm_num)
  refine ⟨hv', h2, ?_, ?_⟩
  · have : (R.m + 6653 + incPhase R.m) / 4 + 83 ≤ (R.m + 6990) / 4 := by omega
    simp only [RegS.pushAny]
    omega
  · simp only [RegS.pushAny, pushOf, qMove_append, pushSalvo_d]
    omega

/-- **The increment at module `r`, for every arrival phase**: the variant `incPhase R.m` of the
register run (`dz2eOp`, `dz2e1Op`, `dz2e2Op`, `dz2e3Op`) placed at module `r`. -/
theorem dz2eAny_module (p : Program) (r : ℕ) {R : RegS} (hR : R.Inv) {Vs' : ℤ}
    (hv' : DiagValid regParams Vs' R.Vb R.K (R.q ++ [pushOf R.m]))
    (hVs' : -34 ≤ Vs' + 2 * (((R.m + 6653 + incPhase R.m) / 4 : ℕ) : ℤ)) :
    conway.evolve 6990
        (translate (modDX p r, modDY p r) (dz2eRest ∪ incInWL.cells 0) ∪ regAt p r R) =
      translate (modDX p r, modDY p r) dz2eRest ∪ regAt p r (R.pushAny Vs') := by
  rw [regAt, regAt, ← translate_union, Rule.evolve_translate, incInWL_cells]
  simp only [RegS.pushAny, pushOf] at hv' hVs' ⊢
  have h4 : (R.m + 6653) % 4 = 0 ∨ (R.m + 6653) % 4 = 3 ∨ (R.m + 6653) % 4 = 2 ∨
      (R.m + 6653) % 4 = 1 := by omega
  rcases h4 with h | h | h | h
  · rw [show incPhase R.m = 0 by simp only [incPhase]; omega] at hv' hVs' ⊢
    simp only [pushSalvo, pushBase, add_zero] at hv' hVs' ⊢
    rw [dz2eOp R.q R.K R.Vs R.Vb Vs' R.m hR.1 hv' h hR.2.1 hR.2.2.1 hVs', translate_union]
  · rw [show incPhase R.m = 1 by simp only [incPhase]; omega,
      show R.m + 6653 + 1 = R.m + 6654 by omega] at hv' hVs' ⊢
    simp only [pushSalvo, pushBase] at hv' hVs' ⊢
    rw [← dz2e1Rest_eq, dz2e1Op R.q R.K R.Vs R.Vb Vs' R.m hR.1 hv' (by omega) hR.2.1 hR.2.2.1
      hVs', translate_union]
  · rw [show incPhase R.m = 2 by simp only [incPhase]; omega,
      show R.m + 6653 + 2 = R.m + 6655 by omega] at hv' hVs' ⊢
    simp only [pushSalvo, pushBase] at hv' hVs' ⊢
    rw [← dz2e2Rest_eq, dz2e2Op R.q R.K R.Vs R.Vb Vs' R.m hR.1 hv' (by omega) hR.2.1 hR.2.2.1
      hVs', translate_union]
  · rw [show incPhase R.m = 3 by simp only [incPhase]; omega,
      show R.m + 6653 + 3 = R.m + 6656 by omega] at hv' hVs' ⊢
    simp only [pushSalvo, pushBase] at hv' hVs' ⊢
    rw [← dz2e3Rest_eq, dz2e3Op R.q R.K R.Vs R.Vb Vs' R.m hR.1 hv' (by omega) hR.2.1 hR.2.2.1
      hVs', translate_union]

end LP

end LeanTheory.Life
