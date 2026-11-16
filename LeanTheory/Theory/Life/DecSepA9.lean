/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepA8

/-!
# The end of a Z activation: the fields `zA2a` and `zA2b` of `DecSep`

Research note `N-22`. As for the NZ activation (`DecSepA6`): the route of the Z answer stays in
the right zone of the module (`u ≥ U_r + 1250`) or in the bands (`dsepA_routeAZ_hull`); the end
(`finFootZ`) lies in the capture box at station `j` of the line Z, the route or the unit row of
unit `z` (`dsepA_finZ_hull`); the route is far from the pieces of the control, of the Z stations
`0 … j - 1` and of `KZ` by its route separation.

`dsepA_zA2a`, `dsepA_zA2b`: the fields, verbatim.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The route of the Z answer -/

/-- **The route of the Z answer** (from its dispatch at station `j` of the line Z) stays in the
right zone of the module or in the bands. -/
theorem dsepA_routeAZ_hull (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k : ℕ, decDispZ p i r + k ≤ routeEndX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) →
    ∀ x ∈ routeFootX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) k,
      U p r + 1250 ≤ x.1 - x.2 ∨ x.1 + x.2 ≤ VT p + 660 * instrBand i + 404 := by
  intro k hk x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hsA, hvd, hcA1, hcA2, hOA1, hOA2, hBA1, hBA2, hHA1, hHA2, hdV⟩ := dsepA_layAZ hp hi
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have hD : ((decDispZ p i r : ℕ) : ℤ) = decShift p i r + 13062 + 288 *
      (callerIdx p r i : ℤ) := by
    simp only [decDispZ]; push_cast; omega
  obtain ⟨hl, htim, -, -, -⟩ := decAnsZ_plan hp hi _ hD
  have hU := U_even p r
  have hpA := zAnsChan_parity p (callerIdx p r i)
  have hpo := trackOut_par p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))
  have hpb := trackBack_par p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))
  have hpH := hairReg_par p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i))
  have hpT := decTZ_par p i r z
  change RouteTimedX (decGZ p i r) (decCsZ p i r z) _ at htim
  change RouteLines (decGZ p i r) (decCsZ p i r z) at hl
  simp only [decCsZ, decMkZ, zAnsCorners, upCornersK, bandCorners, List.cons_append,
    List.nil_append] at htim hl hk hx
  refine isep2_rfoot_sub (Z := {x : Cell | U p r + 1250 ≤ x.1 - x.2 ∨
      x.1 + x.2 ≤ VT p + 660 * instrBand i + 404}) _ _ _ _ htim hl ?_ ?_ ?_ ?_ k hk hx
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by norm_num, ?_⟩ <;> simp only [CPar, rfCU, rfCV] <;> omega
  · intro c' hc' y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      have := isep2_rx_uv (by norm_num) (by simp only [CPar, rfCU, rfCV]; omega) hy <;>
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2] at this <;>
      simp only [Set.mem_ofPred_eq] <;> omega
  · refine ⟨fun cu cv r1 r2 y hy => ?_, fun cu cv r1 r2 y hy => ?_,
      fun cu cv r1 r2 y hy => ?_, fun cu cv r1 r2 y hy => ?_, fun cu cv r1 r2 y hy => ?_,
      fun cu cv r1 r2 y hy => ?_, trivial⟩ <;>
      simp only [Ray, outD, behindIn] at r1 r2 <;>
      obtain ⟨y1, y2, y3, y4⟩ := hy <;> simp only [Set.mem_ofPred_eq] <;> omega
  · intro t' h1 h2 y hy
    obtain ⟨y1, y2, y3, y4⟩ := hy
    simp only [decGZ, modWL, zAnsWL, WL.shift, WL.px, WL.py, WL.qt] at y1 y2 y3 y4
    simp only [Set.mem_ofPred_eq]
    omega

/-! ### The end of a Z activation -/

/-- **The end of a Z activation**: the capture box at station `j` of the line Z, the route of the
answer, or the unit row of unit `z`. -/
theorem dsepA_finZ_hull (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h2 : t < decEndZ p i r z) : ∀ x ∈ finFootZ p i r z t,
    (849 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
      x.1 ≤ 1011 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
      -380 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
      x.2 ≤ -289 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) ∨
    (U p r + 1250 ≤ x.1 - x.2 ∨ x.1 + x.2 ≤ VT p + 660 * instrBand i + 404) ∨
    x.1 + x.2 ≤ VU p + 216 := by
  intro x hx
  have hdV := (dsepA_layAZ hp hi).2.2.2.2.2.2.2.2.2.2
  have hc := decCap_cast p hi
  obtain ⟨hD, -, hT0, -, -, hDT⟩ := decZ_times hp hi
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  unfold finFootZ at hx
  split_ifs at hx with ha hb
  · left
    have := dsepM_image_box ((stationZ_captureE p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapZ p i r) hc.2).subset (t - decCapZ p i r)
      (by unfold decDispZ at ha; unfold decCapZ; omega) hx)
    simp only at this
    omega
  · unfold linkFootW at hx
    split_ifs at hx with hc1 hc2
    · right; left
      exact dsepA_routeAZ_hull hp hi (t - decDispZ p i r) hc1 x hx
    · right; right
      have e := dsep_csZ_eq hp hi
      obtain ⟨-, htim, -, -, -⟩ := decAnsZ_plan hp hi _ hD
      change RouteTimedX (decGZ p i r) (decCsZ p i r z) _ at htim
      rw [e] at htim hc1 hx
      have hpT := decTZ_par p i r z
      obtain ⟨cu, cv, hr, hsub⟩ := dsepA_final_ray _ _ (decGZ p i r) (decDispZ p i r)
        (by simp [isep2SlabC]) (by simp only [CPar, rfCU, rfCV, isep2SlabC]; rw [htN]; omega)
        htim (t := t) (by omega)
      rw [show ((decDispZ p i r : ℕ) : ℤ) + ((t - decDispZ p i r : ℕ) : ℤ) = ((t : ℕ) : ℤ) by
        push_cast [Nat.cast_sub (show decDispZ p i r ≤ t by omega)]; ring] at hx
      obtain ⟨y1, y2, y3, y4⟩ := hsub hx
      simp only [Ray, outD, isep2SlabC] at hr
      rw [htN] at hr
      omega
    · right; right
      have := isep2_entryFoot_xy hx
      omega
  · right; right
    have := isep2_mem_outC p z (j := t - (decT0Z p i r z + (134 + decTZn p i r z * 254)))
      (by unfold decEndZ at h2; omega) hx
    omega

/-- The pieces of the end of a Z activation: station `j` or the pieces of the answer link. -/
theorem dsepA_LFZ_cases {g : Piece} (hg : g ∈ decLFZ p i r z) :
    g ∈ stZOne p r (callerIdx p r i) ∨ g ∈ decLF0Z p i r z := by
  simp only [decLFZ, mem_dd, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact Or.inl hg
  · exact Or.inr (mem_dd.2 (List.mem_append_left _ hg))
  · exact Or.inr (mem_dd.2 (List.mem_append_right _ hg))

/-- **`DecSep.zA2a`**: after the capture, the rest of the zero test is far from the end. -/
theorem dsepA_zA2a (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, decCapZ p i r ≤ t → t < decEndZ p i r z →
      FarApart 2 (restFootZ p i r t) (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t) := by
  intro t _ h2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  refine dsepT_far_union_r (farApart_boxesOf fun g hg => ?_) ?_
  · rcases dsepA_LFZ_cases hg with hg | hg
    · refine dsepA_far (dsepA_restZ_mh' t) (fun x hx => dsepA_sjZ_cells hg hx)
        fun a b ha hb => ?_
      simp only [dsepAMHat] at ha
      omega
    · exact dsepA_mh_FZ hp hi (dsepA_restZ_mh' t) g hg
  · refine dsepA_far (dsepA_restZ_mh' t) (dsepA_finZ_hull hp hi h2) fun a b ha hb => ?_
    simp only [dsepAMHat] at ha
    omega

/-! ### Against the control, the stations and `KZ` -/

/-- The pieces of the control, of the Z stations `0 … j - 1` and of `KZ`. -/
theorem dsepA_CSZ_cases {g : Piece} (hg : g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r) :
    g ∈ decLC p i r ∨ g ∈ decLSZ p i r ∨ g ∈ reflP (unitWL p i decDWL) (decCornZ p i r) := by
  rcases List.mem_append.1 hg with hg | hg
  · rcases List.mem_append.1 hg with hg | hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl hg)
  · exact Or.inr (Or.inr (mem_dd.1 hg))

/-- **The pieces of the control, of the Z stations `0 … j - 1` and of `KZ` are not reflectors of
the Z answer.** -/
theorem dsepA_CSZ_notAZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g : Piece}
    (hg : g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r) :
    g ∉ reflP (decGZ p i r) (decCsZ p i r z) := by
  have hcs := dsepM_corner_mem hi (dsepM_specs hi).2.2.2.2
  rcases dsepA_CSZ_cases hg with hg | hg | hg
  · rcases dsepM_mem_decLC hg with hr | ⟨m', hm', rfl⟩
    · exact dsepA_refl_other hp hi (dsepM_specs hi).2.2.2.2 (dsepM_specs hi).2.1
        (fun c hc c' hc' => (dsepA_tags_C_AZ c' hc' c hc).symm) g hr
    · exact dsepA_not_refl_wide (dsepA_copy_wide p r m' _).1 (dsepA_copy_wide p r m' _).2
  · have hn := dsepT_mach_ne (decLSZ_mem hi g hg)
    have hx : (g.a, g.lo) ∈ g.box := ⟨le_rfl, hn.1, le_rfl, hn.2⟩
    obtain ⟨k, hk0, hk1, hb⟩ := dsepA_LSZ_cells hg hx
    have hu := modD_uv p r
    have hj := dsepM_j_lt hi
    refine dsepA_not_refl_zone hp r hcs hx ?_
    simp only at hb ⊢
    omega
  · exact dsepA_refl_other hp hi (dsepM_specs hi).2.2.2.2 (dsepM_specs hi).2.2.1
      (fun c hc c' hc' => (dsepA_tags_Z_AZ c' hc' c hc).symm) g hg

/-- The cells of the pieces of the control, of the Z stations `0 … j - 1` and of `KZ`. -/
theorem dsepA_CSZ_cells {g : Piece} (hg : g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r) :
    ∀ x ∈ g.box,
    (dsepACB (A p i + decR) (trackOut p (instrBand i) 1 (A p i + decR)) x ∨
    dsepACB (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
      (trackOut p (instrBand i) 1 (A p i + decR)) x ∨
    dsepACB (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
      (trackBack p (instrBand i) 1 (A p i + decR)) x ∨
    dsepACB (U p r + decChan p (2 * (callerIdx p r i))) (trackBack p (instrBand i) 1 (A p i + decR))
      x ∨
    dsepACB (U p r + decChan p (2 * (callerIdx p r i))) (decPortV p (2 * (callerIdx p r i))) x ∨
    ∃ m : ℤ, 0 ≤ m ∧ m ≤ (decM p i r : ℤ) ∧ modDX p r - 1700 - 35 * m ≤ x.1 ∧
      x.1 ≤ modDX p r - 1610 - 35 * m ∧ modDY p r - 1727 - 64 * m ≤ x.2 ∧
      x.2 ≤ modDY p r - 1695 - 64 * m) ∨
    (∃ k : ℤ, 0 ≤ k ∧ k < ((callerIdx p r i : ℕ) : ℤ) ∧
    ((889 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 979 + modDX p r + 72 * k ∧
      -325 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -293 + modDY p r - 72 * k) ∨
    (951 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 973 + modDX p r + 72 * k ∧
      -352 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -344 + modDY p r - 72 * k) ∨
    (880 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 883 + modDX p r + 72 * k ∧
      -380 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -377 + modDY p r - 72 * k))) ∨
    (dsepACB (A p i + decD) (trackOut p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
      (trackOut p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
      (trackBack p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (U p r + zTokChan p (callerIdx p r i)) (trackBack p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (U p r + zTokChan p (callerIdx p r i)) (zTokDepth p (callerIdx p r i)) x ∨
    dsepACB (U p r + zTokStation (callerIdx p r i)) (zTokDepth p (callerIdx p r i)) x) := by
  intro x hx
  rcases dsepA_CSZ_cases hg with hg | hg | hg
  · exact Or.inl (dsepA_LC_cells hg hx)
  · exact Or.inr (Or.inl (dsepA_LSZ_cells hg hx))
  · exact Or.inr (Or.inr (dsepA_LZ_cells hg hx))

/-- The rest of the zero test is far from the pieces of the control, of the Z stations
`0 … j - 1` and of `KZ`. -/
theorem dsepA_rest_CSZ (hi : p[i]? = some (.decJz r z)) (t : ℕ) {g : Piece}
    (hg : g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r) :
    FarApart 2 (restFootZ p i r t) g.box := by
  obtain ⟨-, -, hO1, hB1, hO2, hB2, -, hcC, hvC, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs,
    hj0, hjD, hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  have hdD : decD = 188 := rfl
  have hdR : decR = 127 := rfl
  have hm := decM_cast p hi
  refine dsepA_far (dsepA_restZ_mh' t) (dsepA_CSZ_cells hg) fun a b ha hb => ?_
  simp only [dsepAMHat] at ha
  rcases hb with (hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩) | ⟨k, hk0, hk1, hb⟩ | hb <;>
    (try simp only [dsepACB] at hb) <;> omega

/-- Station `j` of the line Z is far from the pieces of the control, of the Z stations
`0 … j - 1` and of `KZ`. -/
theorem dsepA_sjZ_CSZ (hi : p[i]? = some (.decJz r z)) {g h : Piece}
    (hg : g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r) (hh : h ∈ stZOne p r (callerIdx p r i)) :
    FarApart 2 h.box g.box := by
  obtain ⟨-, -, hO1, hB1, hO2, hB2, -, hcC, hvC, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs,
    hj0, hjD, hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  have hdD : decD = 188 := rfl
  have hdR : decR = 127 := rfl
  have hm := decM_cast p hi
  refine dsepA_far (fun x hx => dsepA_sjZ_cells hh hx) (dsepA_CSZ_cells hg) fun a b ha hb => ?_
  rcases hb with (hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩) | ⟨k, hk0, hk1, hb⟩ | hb <;>
    (try simp only [dsepACB] at hb) <;> omega

/-- The pieces of the Z answer link are far from the pieces of the control, of the Z stations
`0 … j - 1` and of `KZ`. -/
theorem dsepA_LF0Z_CSZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g h : Piece}
    (hg : g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r) (hh : h ∈ decLF0Z p i r z) :
    FarApart 2 h.box g.box := by
  rcases dsepA_CSZ_cases hg with hg | hg | hg
  · exact ((dsepA_LC_FZ hp hi h hh).mono (dsepA_box_sub hg) le_rfl).symm'
  · exact ((dsepA_LSZ_FZ hp hi h hh).mono (dsepA_box_sub hg) le_rfl).symm'
  · exact ((dsepA_LZu_FZ hp hi h hh).mono
      (dsepA_box_sub (mem_dd.2 (List.mem_append_left _ hg))) le_rfl).symm'

/-- A set in the unit row is far from the pieces of the control, of the Z stations `0 … j - 1`
and of `KZ`. -/
theorem dsepA_row_CSZ (hi : p[i]? = some (.decJz r z)) {X : Set Cell}
    (hX : ∀ x ∈ X, x.1 + x.2 ≤ VU p + 216) {g : Piece}
    (hg : g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r) : FarApart 2 X g.box := by
  obtain ⟨-, -, hO1, hB1, hO2, hB2, -, hcC, hvC, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs,
    hj0, hjD, hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  have hm := decM_cast p hi
  refine dsepA_far hX (dsepA_CSZ_cells hg) fun a b ha hb => ?_
  rcases hb with (hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩) | ⟨k, hk0, hk1, hb⟩ | hb <;>
    (try simp only [dsepACB] at hb) <;> omega

/-- **The end of a Z activation is far from the pieces of the control, of the Z stations
`0 … j - 1` and of `KZ`.** -/
theorem dsepA_fin_CSZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h2 : t < decEndZ p i r z) {g : Piece}
    (hg : g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r) :
    FarApart 2 (finFootZ p i r z t) g.box := by
  have hgm : g ∈ machPieces p := by
    rcases dsepA_CSZ_cases hg with hg | hg | hg
    · exact decLC_mem hi g hg
    · exact decLSZ_mem hi g hg
    · exact decLZ_mem hi g (mem_dd.2 hg)
  have hdV := (dsepA_layAZ hp hi).2.2.2.2.2.2.2.2.2.2
  have hc := decCap_cast p hi
  obtain ⟨hD, -, hT0, -, -, hDT⟩ := decZ_times hp hi
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  unfold finFootZ
  split_ifs with ha hb
  · obtain ⟨-, -, hO1, hB1, hO2, hB2, -, hcC, hvC, -, hHC, -, hHZ1, hHZ2, hzc1, hzc2, hzd, hzs,
      hj0, hjD, hD1, hA0, hHI, hP1, hAU, hT0', hT0'', hVU, hu1, hu2⟩ := dsepA_lay hi
    have hdD : decD = 188 := rfl
    have hdR : decR = 127 := rfl
    have hm := decM_cast p hi
    refine dsepA_far (fun x hx => dsepM_image_box ((stationZ_captureE p r (callerIdx p r i)
      (decShift p i r) (decShift_mod p i r) (decCapZ p i r) hc.2).subset (t - decCapZ p i r)
      (by unfold decDispZ at ha; unfold decCapZ; omega) hx)) (dsepA_CSZ_cells hg)
      fun a b ha hb => ?_
    simp only at ha
    rcases hb with (hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩) | ⟨k, hk0, hk1, hb⟩ | hb <;>
      (try simp only [dsepACB] at hb) <;> omega
  · unfold linkFootW
    split_ifs with hc1 hc2
    · exact dsepA_routeAZ_far hp hi hc1 hgm (dsepA_CSZ_notAZ hp hi hg)
    · refine dsepA_row_CSZ hi (fun x hx => ?_) hg
      have e := dsep_csZ_eq hp hi
      obtain ⟨-, htim, -, -, -⟩ := decAnsZ_plan hp hi _ hD
      change RouteTimedX (decGZ p i r) (decCsZ p i r z) _ at htim
      rw [e] at htim hc1 hx
      have hpT := decTZ_par p i r z
      obtain ⟨cu, cv, hr, hsub⟩ := dsepA_final_ray _ _ (decGZ p i r) (decDispZ p i r)
        (by simp [isep2SlabC]) (by simp only [CPar, rfCU, rfCV, isep2SlabC]; rw [htN]; omega)
        htim (t := t) (by omega)
      rw [show ((decDispZ p i r : ℕ) : ℤ) + ((t - decDispZ p i r : ℕ) : ℤ) = ((t : ℕ) : ℤ) by
        push_cast [Nat.cast_sub (show decDispZ p i r ≤ t by omega)]; ring] at hx
      obtain ⟨y1, y2, y3, y4⟩ := hsub hx
      simp only [Ray, outD, isep2SlabC] at hr
      rw [htN] at hr
      omega
    · exact dsepA_row_CSZ hi (fun x hx => by have := isep2_entryFoot_xy hx; omega) hg
  · exact dsepA_row_CSZ hi (fun x hx => by
      have := isep2_mem_outC p z (j := t - (decT0Z p i r z + (134 + decTZn p i r z * 254)))
        (by unfold decEndZ at h2; omega) hx
      omega) hg

/-- **`DecSep.zA2b`**: after the capture, the rest of the zero test and the end are far from the
pieces of the control, of the Z stations `0 … j - 1` and of `KZ`. -/
theorem dsepA_zA2b (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, decCapZ p i r ≤ t → t < decEndZ p i r z →
    ∀ g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r,
    FarApart 2 (restFootZ p i r t ∪ (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t)) g.box := by
  intro t _ h2 g hg
  refine dsepT_far_union (dsepA_rest_CSZ hi t hg)
    (dsepT_far_union ?_ (dsepA_fin_CSZ hp hi h2 hg))
  refine FarApart.symm' (farApart_boxesOf fun h hh => ?_)
  rcases dsepA_LFZ_cases hh with hh | hh
  · exact (dsepA_sjZ_CSZ hi hg hh).symm'
  · exact (dsepA_LF0Z_CSZ hp hi hg hh).symm'

end LP

end LeanTheory.Life
