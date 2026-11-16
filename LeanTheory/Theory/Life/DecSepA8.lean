/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepA7

/-!
# The fields `zQZ` and `zQF` of `DecSep`

Research note `N-22`. Before the capture of a Z activation, the control, the zero test and the
answer (`qFootZ`) are far from `KZ` (its reflectors, station `j` of the line Z and its footprint),
and all of them are far from the pieces of the Z answer link. As for the NZ activation
(`DecSepA5`), with:

* `KZ` in a loop inside the loop of the control (slot `2`: `OUT` track `T₀ + 125`, `BACK` track
  `T₀ + 435`, hairpin `≥ 61` right of the hairpin of `C`), then in the right zone of the module;
* the route of the control and of `KZ` far from the pieces of the Z answer link by their route
  separation (the entry chain of unit `z` may lie anywhere among the units).

`dsepA_zQZ`, `dsepA_zQF`: the fields, verbatim.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Against `KZ` -/

/-- **The hull of the module is far from `KZ`.** -/
theorem dsepA_mh_Z (hi : p[i]? = some (.decJz r z)) {X : Set Cell}
    (hX : ∀ x ∈ X, dsepAMHat p r x) {t : ℕ} (h0 : 4260 ≤ t) (h1 : t < decCapZ p i r) :
    FarApart 2 X (boxesOf (decLZu p i r) ∪ tokFootZ p i r t) := by
  obtain ⟨-, -, -, -, hO2, hB2, -, -, -, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdD : decD = 188 := rfl
  refine dsepT_far_union_r (farApart_boxesOf fun g hg => ?_) ?_
  · refine dsepA_far hX (dsepA_LZu_cells g hg) fun a b ha hb => ?_
    simp only [dsepAMHat, dsepACB] at ha hb
    omega
  · refine dsepA_far hX (dsepA_tokZ_hull hi h0 h1) fun a b ha hb => ?_
    simp only [dsepAMHat, dsepAZtok, Set.mem_ofPred_eq] at ha hb
    omega

/-- **The Z stations `0 … j - 1` are far from `KZ`.** -/
theorem dsepA_LSZ_Z (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (h1 : t < decCapZ p i r) :
    FarApart 2 (boxesOf (decLSZ p i r)) (boxesOf (decLZu p i r) ∪ tokFootZ p i r t) := by
  obtain ⟨-, -, -, -, hO2, hB2, -, -, -, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdD : decD = 188 := rfl
  refine FarApart.symm' (farApart_boxesOf fun g hg => ?_)
  refine FarApart.symm' (dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_)
  · refine dsepA_far (fun x hx => dsepA_LSZ_cells hg hx) (dsepA_LZu_cells h hh)
      fun a b ha hb => ?_
    obtain ⟨k, hk0, hk1, ha⟩ := ha
    simp only [dsepACB] at hb
    omega
  · refine dsepA_far (fun x hx => dsepA_LSZ_cells hg hx) (dsepA_tokZ_hull hi h0 h1)
      fun a b ha hb => ?_
    obtain ⟨k, hk0, hk1, ha⟩ := ha
    simp only [dsepAZtok, Set.mem_ofPred_eq] at hb
    omega

/-- **The pieces of the control thread are far from `KZ`.** -/
theorem dsepA_LC_Z (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (h1 : t < decCapZ p i r) :
    FarApart 2 (boxesOf (decLC p i r)) (boxesOf (decLZu p i r) ∪ tokFootZ p i r t) := by
  obtain ⟨-, -, hO1, hB1, hO2, hB2, -, hcC, hvC, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs,
    hj0, hjD, hD1, hA0, hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdD : decD = 188 := rfl
  have hdR : decR = 127 := rfl
  have hm := decM_cast p hi
  refine FarApart.symm' (farApart_boxesOf fun g hg => ?_)
  refine FarApart.symm' (dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_)
  · refine dsepA_far (fun x hx => dsepA_LC_cells hg hx) (dsepA_LZu_cells h hh)
      fun a b ha hb => ?_
    simp only [dsepACB] at hb
    rcases ha with ha | ha | ha | ha | ha | ⟨m, hm0, hm1, ha⟩ <;>
      (try simp only [dsepACB] at ha) <;> omega
  · refine dsepA_far (fun x hx => dsepA_LC_cells hg hx) (dsepA_tokZ_hull hi h0 h1)
      fun a b ha hb => ?_
    simp only [dsepAZtok, Set.mem_ofPred_eq] at hb
    rcases ha with ha | ha | ha | ha | ha | ⟨m, hm0, hm1, ha⟩ <;>
      (try simp only [dsepACB] at ha) <;> omega

/-- **The control before the register run is far from `KZ`.** -/
theorem dsepA_C_Z (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t ≤ decTS p i r) (h1 : t < decCapZ p i r) :
    FarApart 2 (decFootC p i r t) (boxesOf (decLZu p i r) ∪ tokFootZ p i r t) := by
  obtain ⟨-, -, hO1, hB1, hO2, hB2, -, hcC, hvC, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs,
    hj0, hjD, hD1, hA0, hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdD : decD = 188 := rfl
  have hdR : decR = 127 := rfl
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_
  · refine dsepA_far (dsepA_footC_hull hi h0 ht) (dsepA_LZu_cells h hh) fun a b ha hb => ?_
    simp only [dsepACB, dsepADown, Set.mem_ofPred_eq] at ha hb
    omega
  · refine dsepA_far (dsepA_footC_hull hi h0 ht) (dsepA_tokZ_hull hi h0 h1)
      fun a b ha hb => ?_
    simp only [dsepADown, dsepAZtok, Set.mem_ofPred_eq] at ha hb
    omega

/-- **The Z answer after the cut is far from `KZ`.** -/
theorem dsepA_ansZ_Z (hi : p[i]? = some (.decJz r z)) {t : ℕ} (hc : decCutZ p i r ≤ t)
    (h1 : t < decCapZ p i r) :
    FarApart 2 (decAnsFootZ p i r t) (boxesOf (decLZu p i r) ∪ tokFootZ p i r t) := by
  obtain ⟨-, -, -, -, hO2, hB2, -, -, -, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdD : decD = 188 := rfl
  have h0 : 4260 ≤ t := by
    obtain ⟨-, -, h⟩ := decTS_facts p hi; unfold decCutZ decTS at hc; omega
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_
  · refine dsepA_far (dsepA_ansZ_hull hi hc) (dsepA_LZu_cells h hh) fun a b ha hb => ?_
    simp only [dsepACB] at hb
    rcases ha with ha | ⟨k, hk0, hk1, ha⟩ <;> omega
  · refine dsepA_far (dsepA_ansZ_hull hi hc) (dsepA_tokZ_hull hi h0 h1) fun a b ha hb => ?_
    simp only [dsepAZtok, Set.mem_ofPred_eq] at hb
    rcases ha with ha | ⟨k, hk0, hk1, ha⟩ <;> omega

/-- **`DecSep.zQZ`**: before the capture, the control, the zero test and the answer are far from
the pieces and the footprint of `KZ`. -/
theorem dsepA_zQZ (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decCapZ p i r →
      FarApart 2 (qFootZ p i r t) (boxesOf (decLZu p i r) ∪ tokFootZ p i r t) := by
  intro t h0 h1
  unfold qFootZ
  split_ifs with hA hB
  · rw [boxesOf_append]
    exact dsepT_far_union (dsepT_far_union
      (dsepA_mh_Z hi (fun x hx => dsepA_grpLanes_mh x (Or.inl hx)) h0 h1) (dsepA_LSZ_Z hi h0 h1))
      (dsepT_far_union (dsepT_far_union (dsepA_LC_Z hi h0 h1) (dsepA_C_Z hi h0 hA h1))
        (dsepA_mh_Z hi (fun x hx => dsepA_grpLanes_mh x (Or.inr hx)) h0 h1))
  · rw [boxesOf_append]
    exact dsepT_far_union (dsepT_far_union (dsepA_LC_Z hi h0 h1) (dsepA_LSZ_Z hi h0 h1))
      (dsepA_mh_Z hi (dsepA_modImg_mh dsepA_runZ_mh) h0 h1)
  · exact dsepT_far_union (dsepA_LC_Z hi h0 h1) (dsepT_far_union
      (dsepA_mh_Z hi (dsepA_restZ_mh' t) h0 h1)
      (dsepT_far_union (dsepA_LSZ_Z hi h0 h1) (dsepA_ansZ_Z hi (by omega) h1)))

/-! ### Against the Z answer link -/

/-- The pieces of the Z answer link are pieces of the machine. -/
theorem dsepA_LF0Z_mach (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLF0Z p i r z, g ∈ machPieces p := by
  intro g hg
  simp only [decLF0Z, mem_dd, List.mem_append] at hg
  refine decLFZ_mem hp hi g (mem_dd.2 ?_)
  rcases hg with hg | hg
  · exact List.mem_append_left _ (List.mem_append_right _ hg)
  · exact List.mem_append_right _ hg

/-- **The hull of the module is far from the pieces of the Z answer link.** -/
theorem dsepA_mh_FZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {X : Set Cell}
    (hX : ∀ x ∈ X, dsepAMHat p r x) : ∀ g ∈ decLF0Z p i r z, FarApart 2 X g.box := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hsA, hvd, hcA1, hcA2, hOA1, hOA2, hBA1, hBA2, hHA1, hHA2, hdV⟩ := dsepA_layAZ hp hi
  intro g hg
  refine dsepA_far hX (dsepA_LF0Z_cells g hg) fun a b ha hb => ?_
  simp only [dsepAMHat, dsepACB] at ha hb
  omega

/-- **The Z stations `0 … j - 1` are far from the pieces of the Z answer link.** -/
theorem dsepA_LSZ_FZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLF0Z p i r z, FarApart 2 (boxesOf (decLSZ p i r)) g.box := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hsA, hvd, hcA1, hcA2, hOA1, hOA2, hBA1, hBA2, hHA1, hHA2, hdV⟩ := dsepA_layAZ hp hi
  intro g hg
  refine FarApart.symm' (farApart_boxesOf fun h hh => ?_)
  refine dsepA_far (dsepA_LF0Z_cells g hg) (fun x hx => dsepA_LSZ_cells hh hx)
    fun a b ha hb => ?_
  obtain ⟨k, hk0, hk1, hb⟩ := hb
  simp only [dsepACB] at ha
  omega

/-- **The pieces of the control thread are far from the pieces of the Z answer link.** -/
theorem dsepA_LC_FZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLF0Z p i r z, FarApart 2 (boxesOf (decLC p i r)) g.box := by
  obtain ⟨hO0, hB0, hO1, hB1, -, -, hcN, hcC, hvC, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hsA, hvd, hcA1, hcA2, hOA1, hOA2, hBA1, hBA2, hHA1, hHA2, hdV⟩ := dsepA_layAZ hp hi
  have hdR : decR = 127 := rfl
  have hm := decM_cast p hi
  intro g hg
  refine FarApart.symm' (farApart_boxesOf fun h hh => ?_)
  refine dsepA_far (dsepA_LF0Z_cells g hg) (fun x hx => dsepA_LC_cells hh hx)
    fun a b ha hb => ?_
  simp only [dsepACB] at ha
  rcases hb with hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩ <;>
    (try simp only [dsepACB] at hb) <;> omega

/-- **The control before the register run is far from the pieces of the Z answer link**: its
route by route separation, the rest by the hulls. -/
theorem dsepA_C_FZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t ≤ decTS p i r) : ∀ g ∈ decLF0Z p i r z, FarApart 2 (decFootC p i r t) g.box := by
  intro g hg
  by_cases hre : t ≤ routeEndX (unitWL p i decRWL) (decCornC p i r) 4260
  · have hTA := (decTA_facts p hi).2.1
    have e : decFootC p i r t = flyFoot (unitWL p i decRWL) (decCornC p i r) 4260 t := by
      simp only [decFootC, show t ≤ decTA p i r - 20 by omega, ↓reduceIte]
    rw [e]
    refine dsepA_routeC_far hp hi h0 hre (dsepA_LF0Z_mach hp hi g hg) ?_
    simp only [decLF0Z, mem_dd, List.mem_append] at hg
    rcases hg with hg | hg
    · exact dsepA_refl_other hp hi (dsepM_specs hi).2.1 (dsepM_specs hi).2.2.2.2
        dsepA_tags_C_AZ g hg
    · exact dsepA_not_refl_wide (dsepA_E_wide hg).1 (dsepA_E_wide hg).2
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
      hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
    obtain ⟨hsA, hvd, hcA1, hcA2, hOA1, hOA2, hBA1, hBA2, hHA1, hHA2, hdV⟩ := dsepA_layAZ hp hi
    refine dsepA_far (dsepA_footC_after hi ht (by omega)) (dsepA_LF0Z_cells g hg)
      fun a b ha hb => ?_
    simp only [dsepACB] at hb
    omega

/-- **The Z answer after the cut is far from the pieces of the Z answer link.** -/
theorem dsepA_ansZ_FZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (hc : decCutZ p i r ≤ t) : ∀ g ∈ decLF0Z p i r z, FarApart 2 (decAnsFootZ p i r t) g.box := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hsA, hvd, hcA1, hcA2, hOA1, hOA2, hBA1, hBA2, hHA1, hHA2, hdV⟩ := dsepA_layAZ hp hi
  intro g hg
  refine dsepA_far (dsepA_ansZ_hull hi hc) (dsepA_LF0Z_cells g hg) fun a b ha hb => ?_
  simp only [dsepACB] at hb
  rcases ha with ha | ⟨k, hk0, hk1, ha⟩ <;> omega

/-- **The pieces of `KZ` are far from the pieces of the Z answer link.** -/
theorem dsepA_LZu_FZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLF0Z p i r z, FarApart 2 (boxesOf (decLZu p i r)) g.box := by
  obtain ⟨-, -, -, -, hO2, hB2, -, -, -, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hsA, hvd, hcA1, hcA2, hOA1, hOA2, hBA1, hBA2, hHA1, hHA2, hdV⟩ := dsepA_layAZ hp hi
  have hdD : decD = 188 := rfl
  intro g hg
  refine FarApart.symm' (farApart_boxesOf fun h hh => ?_)
  refine dsepA_far (dsepA_LF0Z_cells g hg) (dsepA_LZu_cells h hh) fun a b ha hb => ?_
  simp only [dsepACB] at ha hb
  omega

/-- **`KZ` before its capture is far from the pieces of the Z answer link**: its route by route
separation, the rest by the hulls. -/
theorem dsepA_tokZ_FZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (h1 : t < decCapZ p i r) :
    ∀ g ∈ decLF0Z p i r z, FarApart 2 (tokFootZ p i r t) g.box := by
  intro g hg
  by_cases hre : t ≤ decCapZ p i r - 90 ∧
    t ≤ routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260
  · have e : tokFootZ p i r t = flyFoot (unitWL p i decDWL) (decCornZ p i r) 4260 t := by
      simp only [tokFootZ, hre.1, ↓reduceIte]
    rw [e]
    refine dsepA_routeZ_far hp hi h0 hre.2 (dsepA_LF0Z_mach hp hi g hg) ?_
    simp only [decLF0Z, mem_dd, List.mem_append] at hg
    rcases hg with hg | hg
    · exact dsepA_refl_other hp hi (dsepM_specs hi).2.2.1 (dsepM_specs hi).2.2.2.2
        dsepA_tags_Z_AZ g hg
    · exact dsepA_not_refl_wide (dsepA_E_wide hg).1 (dsepA_E_wide hg).2
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
      hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
    obtain ⟨hsA, hvd, hcA1, hcA2, hOA1, hOA2, hBA1, hBA2, hHA1, hHA2, hdV⟩ := dsepA_layAZ hp hi
    refine dsepA_far (dsepA_tokZ_after hi h1 hre) (dsepA_LF0Z_cells g hg) fun a b ha hb => ?_
    simp only [dsepACB] at hb
    omega

/-- **`DecSep.zQF`**: before the capture, the control, the zero test, the answer and `KZ` are far
from the pieces of the Z answer link. -/
theorem dsepA_zQF (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decCapZ p i r → ∀ g ∈ decLF0Z p i r z,
      FarApart 2 (qFootZ p i r t ∪ (boxesOf (decLZu p i r) ∪ tokFootZ p i r t)) g.box := by
  intro t h0 h1 g hg
  refine dsepT_far_union ?_
    (dsepT_far_union (dsepA_LZu_FZ hp hi g hg) (dsepA_tokZ_FZ hp hi h0 h1 g hg))
  unfold qFootZ
  split_ifs with hA hB
  · rw [boxesOf_append]
    exact dsepT_far_union (dsepT_far_union
      (dsepA_mh_FZ hp hi (fun x hx => dsepA_grpLanes_mh x (Or.inl hx)) g hg)
      (dsepA_LSZ_FZ hp hi g hg))
      (dsepT_far_union (dsepT_far_union (dsepA_LC_FZ hp hi g hg) (dsepA_C_FZ hp hi h0 hA g hg))
        (dsepA_mh_FZ hp hi (fun x hx => dsepA_grpLanes_mh x (Or.inr hx)) g hg))
  · rw [boxesOf_append]
    exact dsepT_far_union (dsepT_far_union (dsepA_LC_FZ hp hi g hg) (dsepA_LSZ_FZ hp hi g hg))
      (dsepA_mh_FZ hp hi (dsepA_modImg_mh dsepA_runZ_mh) g hg)
  · exact dsepT_far_union (dsepA_LC_FZ hp hi g hg) (dsepT_far_union
      (dsepA_mh_FZ hp hi (dsepA_restZ_mh' t) g hg)
      (dsepT_far_union (dsepA_LSZ_FZ hp hi g hg) (dsepA_ansZ_FZ hp hi (by omega) g hg)))

end LP

end LeanTheory.Life
