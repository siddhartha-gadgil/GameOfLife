/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepI5

/-!
# The fields `nIdle` and `zIdle` of `DecSep`

Research note `N-22`. Every part of the footprints of the threads of a `decJz` activation is far
from every piece of the machine outside a list of pieces of the threads (`DecSepI1` … `DecSepI5`);
the pieces of the lists are pieces of the threads, and the boxes of the pieces of the threads are
far from the other pieces of the machine (`machPieces_sep`). Hence:

* `dsepI_nIdle`: the field `nIdle`;
* `dsepI_zIdle`: the field `zIdle` (the INC gate runs inside its box, `gateFoot_subset`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- The boxes of a list of pieces of the machine inside a list `L` are far from the pieces
outside `L`. -/
theorem dsepI_boxes (hp : p.WellFormed) {A L : List Piece} (hA : ∀ x ∈ A, x ∈ machPieces p)
    (hAL : ∀ x ∈ A, x ∈ L) : dsepIFar p (boxesOf A) L :=
  (dsepI_boxesOf hp hA).mono subset_rfl hAL

/-- The INC gate of a module is a piece of the machine. -/
theorem dsepI_gate_mem (hi : p[i]? = some (.decJz r z)) : gateP p r ∈ machPieces p :=
  decModule_mem (lt_numRegs_of_dec hi) (by simp [moduleSpecs, incGateSpec])

/-! ### The thread of an NZ activation -/

/-- **`DecSep.nIdle`**: the threads of an NZ activation are far from every idle piece. -/
theorem dsepI_nIdle (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decEndN p i r → ∀ g ∈ machPieces p,
      g ∉ decLMN p i r ++ decLZu p i r →
      FarApart 2 (footMN p i r t ∪ (boxesOf (decLZu p i r) ∪ unpFootZ p i r t)) g.box := by
  intro t h0 h1
  have hr := lt_numRegs_of_dec hi
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  -- the lists of the threads inside `L`
  have mLC : ∀ x ∈ decLC p i r, x ∈ decLMN p i r ++ decLZu p i r := fun x hx =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ hx))))
  have mG : ∀ x ∈ modGroup p r, x ∈ decLMN p i r ++ decLZu p i r := fun x hx =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hx))))
  have mSN : ∀ x ∈ decLSN p i r, x ∈ decLMN p i r ++ decLZu p i r := fun x hx =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hx)))
  have mNu : ∀ x ∈ decLNu p i r, x ∈ decLMN p i r ++ decLZu p i r := fun x hx =>
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx)))
  have mF0 : ∀ x ∈ decLF0N p i r, x ∈ decLMN p i r ++ decLZu p i r := fun x hx =>
    (List.mem_append_left _ (List.mem_append_right _ hx))
  have mZu : ∀ x ∈ decLZu p i r, x ∈ decLMN p i r ++ decLZu p i r := fun x hx =>
    List.mem_append_right _ hx
  have mN : ∀ x ∈ decLN p i r, x ∈ decLMN p i r ++ decLZu p i r := fun x hx =>
    mNu x (mem_dd.2 (List.mem_append_left _ (mem_dd.1 hx)))
  have mFN : ∀ x ∈ decLFN p i r, x ∈ decLMN p i r ++ decLZu p i r := by
    intro x hx
    rcases List.mem_append.1 (mem_dd.1 hx) with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact mNu x (mem_dd.2 (List.mem_append_right _ hx))
      · exact mF0 x (mem_dd.2 (List.mem_append_left _ hx))
    · exact mF0 x (mem_dd.2 (List.mem_append_right _ hx))
  have mAN : ∀ x ∈ dsepILAN p i r, x ∈ decLMN p i r ++ decLZu p i r := by
    intro x hx
    simp only [dsepILAN, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact mSN x hx
    · exact mNu x hx
    · exact mG x hx
  -- the lists of the threads are pieces of the machine
  have pLC := decLC_mem hi
  have pG := modGroup_mem hr
  have pSN := decLSN_mem hi
  have pNu := decLNu_mem hi
  have pZu := decLZu_mem hi
  have pFN := decLFN_mem hp hi
  have pF0 : ∀ x ∈ decLF0N p i r, x ∈ machPieces p := fun x hx => pFN x (by
    rcases List.mem_append.1 (mem_dd.1 hx) with hx | hx
    · exact mem_dd.2 (List.mem_append_left _ (List.mem_append_right _ hx))
    · exact mem_dd.2 (List.mem_append_right _ hx))
  have pN := decLN_mem hi
  have hfar : dsepIFar p (footMN p i r t ∪ (boxesOf (decLZu p i r) ∪ unpFootZ p i r t))
      (decLMN p i r ++ decLZu p i r) := by
    refine dsepIFar.union ?_ (dsepIFar.union (dsepI_boxes hp pZu mZu)
      ((dsepI_unpFootZ_far hp hi h0).mono subset_rfl mZu))
    unfold footMN
    split_ifs with hc
    · refine dsepIFar.union (dsepI_boxes hp pF0 mF0) (dsepIFar.union ?_ (dsepIFar.union
        (dsepI_boxes hp pNu mNu) ((dsepI_tokFootN_far hp hi h0 hc).mono subset_rfl mNu)))
      unfold qFootN
      split_ifs with h2 h3
      · rw [boxesOf_append]
        refine dsepIFar.union (dsepIFar.union (dsepI_boxes hp pG mG) (dsepI_boxes hp pSN mSN))
          (dsepIFar.union (dsepIFar.union (dsepI_boxes hp pLC mLC) ?_)
            ((dsepI_lanes_far hp r).mono subset_rfl (by simp)))
        exact (dsepI_footC_far hp hi h0 h2).mono subset_rfl fun x hx => by
          rcases List.mem_append.1 hx with hx | hx
          · exact mLC x hx
          · exact mG x hx
      · rw [boxesOf_append]
        exact dsepIFar.union (dsepIFar.union (dsepI_boxes hp pLC mLC)
          (dsepI_boxes hp pSN mSN))
          (dsepIFar.mono (S := modImg p r decRunRegNZ) (dsepT_runNZ_far hp hr) subset_rfl mG)
      · exact dsepIFar.union (dsepI_boxes hp pLC mLC) (dsepIFar.union
          ((dsepI_restFootN_far hp hi t).mono subset_rfl mG) (dsepIFar.union
            (dsepI_boxes hp pSN mSN)
            ((dsepI_ansFootN_far hp hi (by omega)).mono subset_rfl mAN)))
    · rw [boxesOf_append, boxesOf_append]
      exact dsepIFar.union (dsepIFar.union (dsepIFar.union (dsepI_boxes hp pLC mLC)
        (dsepI_boxes hp pSN mSN)) (dsepI_boxes hp pN mN)) (dsepIFar.union
          ((dsepI_restFootN_far hp hi t).mono subset_rfl mG) (dsepIFar.union
            (dsepI_boxes hp pFN mFN)
            ((dsepI_finFootN_far hp hi (by omega) h1).mono subset_rfl mFN)))
  exact hfar

/-! ### The thread of a Z activation -/

/-- **`DecSep.zIdle`**: the threads of a Z activation and the INC gate are far from every idle
piece. -/
theorem dsepI_zIdle (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z → ∀ g ∈ machPieces p,
      g ∉ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] →
      FarApart 2 (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪ unpFootN p i r t) ∪ gateFoot p r)
        g.box := by
  intro t h0 h1
  have hr := lt_numRegs_of_dec hi
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  -- the lists of the threads inside the list of the field
  have mLC : ∀ x ∈ decLC p i r, x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] :=
    fun x hx => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx)))))
  have mG : ∀ x ∈ modGroup p r, x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] :=
    fun x hx => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx)))))
  have mSZ : ∀ x ∈ decLSZ p i r, x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] :=
    fun x hx => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hx))))
  have mZu : ∀ x ∈ decLZu p i r, x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] :=
    fun x hx => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hx)))
  have mF0 : ∀ x ∈ decLF0Z p i r z, x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] :=
    fun x hx => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx))
  have mNu : ∀ x ∈ decLNu p i r, x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] :=
    fun x hx => List.mem_append_left _ (List.mem_append_right _ hx)
  have mGt : ∀ x ∈ [gateP p r], x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] :=
    fun x hx => List.mem_append_right _ hx
  have mGG : ∀ x ∈ modGroup p r ++ [gateP p r],
      x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact mG x hx
    · exact mGt x hx
  have mZ : ∀ x ∈ decLZ p i r, x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] := fun x hx =>
    mZu x (mem_dd.2 (List.mem_append_left _ (mem_dd.1 hx)))
  have mFZ : ∀ x ∈ decLFZ p i r z, x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] := by
    intro x hx
    rcases List.mem_append.1 (mem_dd.1 hx) with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact mZu x (mem_dd.2 (List.mem_append_right _ hx))
      · exact mF0 x (mem_dd.2 (List.mem_append_left _ hx))
    · exact mF0 x (mem_dd.2 (List.mem_append_right _ hx))
  have mAZ : ∀ x ∈ dsepILAZ p i r, x ∈ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] := by
    intro x hx
    simp only [dsepILAZ, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact mSZ x hx
    · exact mZu x hx
    · exact mG x hx
  -- the lists of the threads are pieces of the machine
  have pLC := decLC_mem hi
  have pG := modGroup_mem hr
  have pSZ := decLSZ_mem hi
  have pNu := decLNu_mem hi
  have pZu := decLZu_mem hi
  have pFZ := decLFZ_mem hp hi
  have pF0 : ∀ x ∈ decLF0Z p i r z, x ∈ machPieces p := fun x hx => pFZ x (by
    rcases List.mem_append.1 (mem_dd.1 hx) with hx | hx
    · exact mem_dd.2 (List.mem_append_left _ (List.mem_append_right _ hx))
    · exact mem_dd.2 (List.mem_append_right _ hx))
  have pZ := decLZ_mem hi
  have pGt : ∀ x ∈ [gateP p r], x ∈ machPieces p := fun x hx => by
    rw [List.mem_singleton.1 hx]
    exact dsepI_gate_mem hi
  have hfar : dsepIFar p (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪ unpFootN p i r t) ∪
      gateFoot p r) (decLMZ p i r z ++ decLNu p i r ++ [gateP p r]) := by
    refine dsepIFar.union (dsepIFar.union ?_ (dsepIFar.union (dsepI_boxes hp pNu mNu)
      ((dsepI_unpFootN_far hp hi h0).mono subset_rfl mNu)))
      ((dsepI_boxes hp pGt mGt).mono (fun x hx => mem_boxesOf.2
        ⟨gateP p r, List.mem_singleton_self _, gateFoot_subset p r hx⟩) fun _ h => h)
    unfold footMZ
    split_ifs with hc
    · refine dsepIFar.union (dsepI_boxes hp pF0 mF0) (dsepIFar.union ?_ (dsepIFar.union
        (dsepI_boxes hp pZu mZu) ((dsepI_tokFootZ_far hp hi h0 hc).mono subset_rfl mZu)))
      unfold qFootZ
      split_ifs with h2 h3
      · rw [boxesOf_append]
        refine dsepIFar.union (dsepIFar.union (dsepI_boxes hp pG mG) (dsepI_boxes hp pSZ mSZ))
          (dsepIFar.union (dsepIFar.union (dsepI_boxes hp pLC mLC) ?_)
            ((dsepI_lanes_far hp r).mono subset_rfl (by simp)))
        exact (dsepI_footC_far hp hi h0 h2).mono subset_rfl fun x hx => by
          rcases List.mem_append.1 hx with hx | hx
          · exact mLC x hx
          · exact mG x hx
      · rw [boxesOf_append]
        exact dsepIFar.union (dsepIFar.union (dsepI_boxes hp pLC mLC)
          (dsepI_boxes hp pSZ mSZ))
          (dsepIFar.mono (S := modImg p r decRunRegZ) (dsepT_runZ_far hp hr) subset_rfl mG)
      · exact dsepIFar.union (dsepI_boxes hp pLC mLC) (dsepIFar.union
          ((dsepI_restFootZ_far hp hi t).mono subset_rfl mGG) (dsepIFar.union
            (dsepI_boxes hp pSZ mSZ)
            ((dsepI_ansFootZ_far hp hi (by omega)).mono subset_rfl mAZ)))
    · rw [boxesOf_append, boxesOf_append]
      exact dsepIFar.union (dsepIFar.union (dsepIFar.union (dsepI_boxes hp pLC mLC)
        (dsepI_boxes hp pSZ mSZ)) (dsepI_boxes hp pZ mZ)) (dsepIFar.union
          ((dsepI_restFootZ_far hp hi t).mono subset_rfl mGG) (dsepIFar.union
            (dsepI_boxes hp pFZ mFZ)
            ((dsepI_finFootZ_far hp hi (by omega) h1).mono subset_rfl mFZ)))
  exact hfar

end LP

end LeanTheory.Life
