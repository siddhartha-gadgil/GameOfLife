/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepI3

/-!
# The idle fields of `DecSep`: the answers

Research note `N-22`. The moving footprints of the answers from the cut to their capture
(`decAnsFootN`, `decAnsFootZ`) are far from every piece of the machine outside the stations
`0 … j`, the thread of the token and the circuit (`dsepI_ansFootN_far`, `dsepI_ansFootZ_far`):
on its line the answer is far from every piece of the module (module frame, `dsepT_ansN_sub`,
`dsepT_ansZ_sub`), and its station footprint lies in the hulls of the stations `k < j`
(`dsepT_chainNZ_hull`, `dsepT_chainZ_hull`), `144` cells from the stations `≥ k + 2`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The stations before station `j` -/

/-- A station `j' < j` of the line NZ belongs to the stations `0 … j - 1`. -/
theorem dsepI_stNZ_LSN {j' : ℕ} (h : j' < callerIdx p r i) :
    ∀ x ∈ stNZOne p r j', x ∈ decLSN p i r := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  exact mem_dd.2 (List.mem_map.2 ⟨s, List.mem_flatMap.2 ⟨j', List.mem_range.2 h, hs⟩, rfl⟩)

/-- A station `j' < j` of the line Z belongs to the stations `0 … j - 1`. -/
theorem dsepI_stZ_LSZ {j' : ℕ} (h : j' < callerIdx p r i) :
    ∀ x ∈ stZOne p r j', x ∈ decLSZ p i r := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  exact mem_dd.2 (List.mem_map.2 ⟨s, List.mem_flatMap.2 ⟨j', List.mem_range.2 h, hs⟩, rfl⟩)

/-- The own pieces of the NZ answer: the stations `0 … j - 1`, the `KNZ` thread, the circuit. -/
noncomputable def dsepILAN (p : Program) (i r : ℕ) : List Piece :=
  decLSN p i r ++ decLNu p i r ++ modGroup p r

/-- The own pieces of the Z answer: the stations `0 … j - 1`, the `KZ` thread, the circuit. -/
noncomputable def dsepILAZ (p : Program) (i r : ℕ) : List Piece :=
  decLSZ p i r ++ decLZu p i r ++ modGroup p r

/-- **A set of the module frame in the zone, far from the module pieces other than the groups and
the stations `≤ j` of the line NZ**, is far from every piece outside `dsepILAN`. -/
theorem dsepI_ansN_local (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {S : Set Cell}
    (hZ : S ⊆ dsepTZone p)
    (hJ : FarApart 2 S ((dsepTBase (.rf 4)).mv (-850) (-1044)).set)
    (hI : FarApart 2 S ((dsepTBase .orGate).mv (-1132) (-1291)).set)
    (hDm : ∀ m : ℤ, 0 ≤ m → m < 2 * D p →
      FarApart 2 S ((dsepTBase .orGate).mv (-1700 - 35 * m) (-1727 - 64 * m)).set)
    (hN : ∀ j : ℤ, (callerIdx p r i : ℤ) < j → j < D p → ∀ i' < 3,
      FarApart 2 S ((dsepTBase (.stNZ i')).mv (72 * j) (72 * j)).set)
    (hZs : ∀ j : ℤ, 0 ≤ j → j < D p → ∀ i' < 3,
      FarApart 2 S ((dsepTBase (.stZ i')).mv (72 * j) (-72 * j)).set)
    (hEN : FarApart 2 S ((dsepTBase .eatNZ).mv (72 * (D p - 1)) (72 * (D p - 1))).set)
    (hEZ : FarApart 2 S ((dsepTBase .eatZ).mv (72 * (D p - 1)) (-72 * (D p - 1))).set) :
    dsepIFar p (modImg p r S) (dsepILAN p i r) := by
  have hr := lt_numRegs_of_dec hi
  refine dsepT_zone_far hp hZ (fun x hx => ?_) (dsepT_mod_cls
    (own := fun B => ∃ x ∈ dsepILAN p i r, dsepTB x = B) ?_ (fun _ => hJ)
    (fun _ => hI) (fun m h0 h1 _ => hDm m h0 h1) ?_
    (fun j h0 h1 i' hi' _ => hZs j h0 h1 i' hi') (fun _ => hEN) (fun _ => hEZ))
  · simp only [dsepILAN, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact decLSN_mem hi x hx
    · exact decLNu_mem hi x hx
    · exact modGroup_mem hr x hx
  · intro i' hi' hn
    exact absurd (dsepT_grp_own r i' hi' fun x hx => List.mem_append_right _ hx) hn
  · intro j h0 h1 i' hi' hn
    by_cases hj : j ≤ (callerIdx p r i : ℤ)
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      obtain ⟨x, hx, e⟩ := dsepI_own_stNZ p r n hi'
      refine absurd ⟨x, ?_, e⟩ hn
      simp only [dsepILAN, List.mem_append]
      rcases lt_or_eq_of_le (show n ≤ callerIdx p r i by omega) with hlt | rfl
      · exact Or.inl (Or.inl (dsepI_stNZ_LSN hlt x hx))
      · exact Or.inl (Or.inr (mem_dd.2 (List.mem_append_right _ hx)))
    · exact hN j (by omega) h1 i' hi'

/-- **A set of the module frame in the zone, far from the module pieces other than the groups and
the stations `≤ j` of the line Z**, is far from every piece outside `dsepILAZ`. -/
theorem dsepI_ansZ_local (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {S : Set Cell}
    (hZ : S ⊆ dsepTZone p)
    (hJ : FarApart 2 S ((dsepTBase (.rf 4)).mv (-850) (-1044)).set)
    (hI : FarApart 2 S ((dsepTBase .orGate).mv (-1132) (-1291)).set)
    (hDm : ∀ m : ℤ, 0 ≤ m → m < 2 * D p →
      FarApart 2 S ((dsepTBase .orGate).mv (-1700 - 35 * m) (-1727 - 64 * m)).set)
    (hN : ∀ j : ℤ, 0 ≤ j → j < D p → ∀ i' < 3,
      FarApart 2 S ((dsepTBase (.stNZ i')).mv (72 * j) (72 * j)).set)
    (hZs : ∀ j : ℤ, (callerIdx p r i : ℤ) < j → j < D p → ∀ i' < 3,
      FarApart 2 S ((dsepTBase (.stZ i')).mv (72 * j) (-72 * j)).set)
    (hEN : FarApart 2 S ((dsepTBase .eatNZ).mv (72 * (D p - 1)) (72 * (D p - 1))).set)
    (hEZ : FarApart 2 S ((dsepTBase .eatZ).mv (72 * (D p - 1)) (-72 * (D p - 1))).set) :
    dsepIFar p (modImg p r S) (dsepILAZ p i r) := by
  have hr := lt_numRegs_of_dec hi
  refine dsepT_zone_far hp hZ (fun x hx => ?_) (dsepT_mod_cls
    (own := fun B => ∃ x ∈ dsepILAZ p i r, dsepTB x = B) ?_ (fun _ => hJ)
    (fun _ => hI) (fun m h0 h1 _ => hDm m h0 h1) (fun j h0 h1 i' hi' _ => hN j h0 h1 i' hi') ?_
    (fun _ => hEN) (fun _ => hEZ))
  · simp only [dsepILAZ, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact decLSZ_mem hi x hx
    · exact decLZu_mem hi x hx
    · exact modGroup_mem hr x hx
  · intro i' hi' hn
    exact absurd (dsepT_grp_own r i' hi' fun x hx => List.mem_append_right _ hx) hn
  · intro j h0 h1 i' hi' hn
    by_cases hj : j ≤ (callerIdx p r i : ℤ)
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
      obtain ⟨x, hx, e⟩ := dsepI_own_stZ p r n hi'
      refine absurd ⟨x, ?_, e⟩ hn
      simp only [dsepILAZ, List.mem_append]
      rcases lt_or_eq_of_le (show n ≤ callerIdx p r i by omega) with hlt | rfl
      · exact Or.inl (Or.inl (dsepI_stZ_LSZ hlt x hx))
      · exact Or.inl (Or.inr (mem_dd.2 (List.mem_append_right _ hx)))
    · exact hZs j (by omega) h1 i' hi'


/-! ### The NZ answer -/

/-- **The NZ answer on its line, before station `0`**, is far from every piece outside
`dsepILAN`. -/
theorem dsepI_ansLineN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCutN p i r ≤ t) (h2 : t ≤ decSt0N p i r) :
    dsepIFar p ((decAnsWLN p i r).box t) (dsepILAN p i r) := by
  have hj := dsepM_j_lt hi
  have hb := base_boxes
  have hD := one_le_D p
  have hq : (((t - decCutN p i r) / 4 : ℕ) : ℤ) ≤ 287 := by
    unfold decSt0N at h2; unfold decCutN at h1 ⊢; omega
  have hmem : ∀ x ∈ Box (104 + (((t - decCutN p i r) / 4 : ℕ) : ℤ))
      (111 + (((t - decCutN p i r) / 4 : ℕ) : ℤ)) (495 + (((t - decCutN p i r) / 4 : ℕ) : ℤ))
      (502 + (((t - decCutN p i r) / 4 : ℕ) : ℤ)),
      ∃ k : ℤ, 0 ≤ k ∧ k ≤ 287 ∧ 104 + k ≤ x.1 ∧ x.1 ≤ 111 + k ∧ 495 + k ≤ x.2 ∧
        x.2 ≤ 502 + k := by
    rintro x ⟨x1, x2, x3, x4⟩
    exact ⟨_, by omega, hq, x1, x2, x3, x4⟩
  refine (dsepI_ansN_local hp hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).mono (dsepT_ansN_sub hi h1)
    fun _ h => h
  · intro x hx
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  all_goals first
    | (refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       simp only [dsepTBase, BoxT.mv] at *
       omega)
    | (intro m h1 h2
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)
    | (intro j h0 h1 i' hi'
       have := stNZ_cases i' hi'
       have := stZ_cases i' hi'
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)

/-- **The NZ answer at the stations `0 … j - 1`** is far from every piece outside
`dsepILAN`. -/
theorem dsepI_ansStN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    dsepIFar p (modImg p r (chainFoot stNZRY (72, 72) (callerIdx p r i))) (dsepILAN p i r) := by
  have hj := dsepM_j_lt hi
  have hb := base_boxes
  have hD := one_le_D p
  have hmem : ∀ x ∈ chainFoot stNZRY (72, 72) (callerIdx p r i),
      ∃ k : ℤ, 0 ≤ k ∧ k < (callerIdx p r i : ℤ) ∧ 380 + 72 * k ≤ x.1 ∧ x.1 ≤ 467 + 72 * k ∧
        784 + 72 * k ≤ x.2 ∧ x.2 ≤ 919 + 72 * k := by
    intro x hx
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := dsepT_chainNZ_hull hx
    exact ⟨k, hk0, hk1, x1, x2, x3, x4⟩
  refine dsepI_ansN_local hp hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  all_goals first
    | (refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       simp only [dsepTBase, BoxT.mv] at *
       omega)
    | (intro m h1 h2
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)
    | (intro j h0 h1 i' hi'
       have := stNZ_cases i' hi'
       have := stZ_cases i' hi'
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)

/-- **The moving footprint of the NZ answer** from the cut to the capture is far from every piece
outside `dsepILAN`. -/
theorem dsepI_ansFootN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCutN p i r ≤ t) : dsepIFar p (decAnsFootN p i r t) (dsepILAN p i r) := by
  unfold decAnsFootN
  split_ifs with h2
  · exact dsepI_ansLineN_far hp hi h1 h2
  · exact dsepI_ansStN_far hp hi

/-! ### The Z answer -/

/-- **The Z answer on its line, before station `0`**, is far from every piece outside
`dsepILAZ`. -/
theorem dsepI_ansLineZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCutZ p i r ≤ t) (h2 : t ≤ decSt0Z p i r) :
    dsepIFar p ((decAnsWLZ p i r).box t) (dsepILAZ p i r) := by
  have hj := dsepM_j_lt hi
  have hb := base_boxes
  have hD := one_le_D p
  have hq : (((t - decCutZ p i r) / 4 : ℕ) : ℤ) ≤ 174 := by
    unfold decSt0Z at h2; unfold decCutZ at h1 ⊢; omega
  have hmem : ∀ x ∈ Box (673 + (((t - decCutZ p i r) / 4 : ℕ) : ℤ))
      (680 + (((t - decCutZ p i r) / 4 : ℕ) : ℤ)) (-142 - (((t - decCutZ p i r) / 4 : ℕ) : ℤ))
      (-135 - (((t - decCutZ p i r) / 4 : ℕ) : ℤ)),
      ∃ k : ℤ, 0 ≤ k ∧ k ≤ 174 ∧ 673 + k ≤ x.1 ∧ x.1 ≤ 680 + k ∧ -142 - k ≤ x.2 ∧
        x.2 ≤ -135 - k := by
    rintro x ⟨x1, x2, x3, x4⟩
    exact ⟨_, by omega, hq, x1, x2, x3, x4⟩
  refine (dsepI_ansZ_local hp hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).mono (dsepT_ansZ_sub hi h1)
    fun _ h => h
  · intro x hx
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  all_goals first
    | (refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       simp only [dsepTBase, BoxT.mv] at *
       omega)
    | (intro m h1 h2
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)
    | (intro j h0 h1 i' hi'
       have := stNZ_cases i' hi'
       have := stZ_cases i' hi'
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)

/-- **The Z answer at the stations `0 … j - 1`** is far from every piece outside `dsepILAZ`. -/
theorem dsepI_ansStZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    dsepIFar p (modImg p r (chainFoot stZR (72, -72) (callerIdx p r i))) (dsepILAZ p i r) := by
  have hj := dsepM_j_lt hi
  have hb := base_boxes
  have hD := one_le_D p
  have hmem : ∀ x ∈ chainFoot stZR (72, -72) (callerIdx p r i),
      ∃ k : ℤ, 0 ≤ k ∧ k < (callerIdx p r i : ℤ) ∧ 849 + 72 * k ≤ x.1 ∧ x.1 ≤ 979 + 72 * k ∧
        -385 - 72 * k ≤ x.2 ∧ x.2 ≤ -293 - 72 * k := by
    intro x hx
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := dsepT_chainZ_hull hx
    exact ⟨k, hk0, hk1, x1, x2, x3, x4⟩
  refine dsepI_ansZ_local hp hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  all_goals first
    | (refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       simp only [dsepTBase, BoxT.mv] at *
       omega)
    | (intro m h1 h2
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)
    | (intro j h0 h1 i' hi'
       have := stNZ_cases i' hi'
       have := stZ_cases i' hi'
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)

/-- **The moving footprint of the Z answer** from the cut to the capture is far from every piece
outside `dsepILAZ`. -/
theorem dsepI_ansFootZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCutZ p i r ≤ t) : dsepIFar p (decAnsFootZ p i r t) (dsepILAZ p i r) := by
  unfold decAnsFootZ
  split_ifs with h2
  · exact dsepI_ansLineZ_far hp hi h1 h2
  · exact dsepI_ansStZ_far hp hi
end LP

end LeanTheory.Life
