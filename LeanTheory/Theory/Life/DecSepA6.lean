/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepA5

/-!
# The end of an NZ activation: the fields `nA2a` and `nA2b` of `DecSep`

Research note `N-22`. After the capture of an NZ activation, the rest of the register run (in the
hull of the module, `dsepAMHat`) is far from the end (the pieces of station `j` and of the answer
link, the capture, the answer link and the flight into unit `i + 1`), and the rest and the end are
far from the pieces of the control, of the stations `0 … j - 1` and of `KNZ`:

* `dsepA_routeAN_hull`: the route of the NZ answer stays left of its channel (`u ≤ cd_A + 29`),
  in the bands (`v ≤ T₀ + 404`) or on its port line left of the stations;
* `dsepA_finN_hull`: the end lies in the capture box, the route of the answer or the unit row;
* the route of the answer is far from the pieces of the control, the stations and `KNZ` by its
  route separation (`dsepA_routeAN_far`): none of them is a reflector of the answer (tags of the
  corners, zone of the module, width); its flight, the entry chain of unit `i + 1` and the flight to
  the body input by the strong forms `dsep_flyAN`, `dsep_entAN`, `dsep_outAN`.

`dsepA_nA2a`, `dsepA_nA2b`: the fields, verbatim.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Not a reflector of the answer -/

/-- A reflector of one route of an instruction is not a reflector of another route whose corners
have other tags. -/
theorem dsepA_refl_other (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g1 g2 : WL}
    {cs1 cs2 : List Corner} (h1 : (g1, cs1) ∈ instrSpecs p i) (h2 : (g2, cs2) ∈ instrSpecs p i)
    (htag : ∀ c ∈ cs1, ∀ c' ∈ cs2, c.tag ≠ c'.tag) : ∀ h ∈ reflP g2 cs2, h ∉ reflP g1 cs1 := by
  intro h hh
  obtain ⟨c', hc', hb⟩ := dsepM_reflP_mem hh
  exact dsepA_not_refl_tag hp (dsepM_corner_mem hi h1) (dsepM_corner_mem hi h2 c' hc')
    (fun c hc => htag c hc c' hc') hb

/-- The tags of the NZ answer and of the control differ. -/
theorem dsepA_tags_AN_C : ∀ c ∈ decCsN p i r, ∀ c' ∈ decCornC p i r, c.tag ≠ c'.tag := by
  intro c hc c' hc'
  have := one_le_D p
  simp only [decCsN, decMkN, nzAnsCorners, upCornersK, bandCorners, decCornC, downCorners,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl <;> first | (simp; done) | (simp; omega)

/-- The tags of the NZ answer and of `KNZ` differ. -/
theorem dsepA_tags_AN_N : ∀ c ∈ decCsN p i r, ∀ c' ∈ decCornN p i r, c.tag ≠ c'.tag := by
  intro c hc c' hc'
  have := one_le_D p
  simp only [decCsN, decMkN, nzAnsCorners, upCornersK, bandCorners, decCornN, downCorners,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl <;> simp

/-! ### The route of the NZ answer -/

/-- **The route of the NZ answer** (from its dispatch at station `j`) stays left of its channel,
in the bands, or on its port line left of the stations. -/
theorem dsepA_routeAN_hull (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k : ℕ, decDispN p i r + k ≤ routeEndX (decGN p i r) (decCsN p i r) (decDispN p i r) →
    ∀ x ∈ routeFootX (decGN p i r) (decCsN p i r) (decDispN p i r) k,
      x.1 - x.2 ≤ U p r + nzAnsChan p (callerIdx p r i) + 29 ∨
      x.1 + x.2 ≤ VT p + 660 * instrBand i + 404 ∨
      (x.1 - x.2 ≤ U p r - 300 ∧ nzAnsPortV (callerIdx p r i) - 26 ≤ x.1 + x.2 ∧
        x.1 + x.2 ≤ nzAnsPortV (callerIdx p r i) + 19) := by
  intro k hk x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hcA, hvA, hOA, hBA, hHA1, hHA2, hdU, hdV, hA1⟩ := dsepA_layAN hp hi
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have hD : ((decDispN p i r : ℕ) : ℤ) = decShift p i r + 11042 + 288 *
      (callerIdx p r i : ℤ) := by
    simp only [decDispN]; push_cast; omega
  obtain ⟨hl, htim, -, -, -⟩ := decAnsN_plan hp hi _ hD
  have hU := U_even p r
  have hpA := nzAnsChan_parity p (callerIdx p r i)
  have hpo := trackOut_par p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))
  have hpb := trackBack_par p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))
  have hpH := hairReg_par p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i))
  have hpT := decTN_par p i r
  change RouteTimedX (decGN p i r) (decCsN p i r) _ at htim
  change RouteLines (decGN p i r) (decCsN p i r) at hl
  simp only [decCsN, decMkN, nzAnsCorners, upCornersK, bandCorners, List.cons_append,
    List.nil_append] at htim hl hk hx
  refine isep2_rfoot_sub (Z := {x : Cell |
      x.1 - x.2 ≤ U p r + nzAnsChan p (callerIdx p r i) + 29 ∨
      x.1 + x.2 ≤ VT p + 660 * instrBand i + 404 ∨ (x.1 - x.2 ≤ U p r - 300 ∧
        nzAnsPortV (callerIdx p r i) - 26 ≤ x.1 + x.2 ∧
        x.1 + x.2 ≤ nzAnsPortV (callerIdx p r i) + 19)}) _ _ _ _ htim hl ?_ ?_ ?_ ?_ k hk hx
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by norm_num, ?_⟩ <;> simp only [CPar, rfCU, rfCV] <;> omega
  · intro c' hc' y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      have := isep2_rx_uv (by norm_num) (by simp only [CPar, rfCU, rfCV]; omega) hy <;>
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2] at this <;>
      simp only [Set.mem_ofPred_eq] <;> omega
  · refine ⟨fun cu cv r1 r2 y hy => ?_, fun cu cv r1 r2 y hy => ?_,
      fun cu cv r1 r2 y hy => ?_, fun cu cv r1 r2 y hy => ?_, fun cu cv r1 r2 y hy => ?_,
      trivial⟩ <;>
      simp only [Ray, outD, behindIn] at r1 r2 <;>
      obtain ⟨y1, y2, y3, y4⟩ := hy <;> simp only [Set.mem_ofPred_eq] <;> omega
  · intro t' h1 h2 y hy
    obtain ⟨y1, y2, y3, y4⟩ := hy
    simp only [decGN, modWL, nzAnsWL, WL.shift, WL.px, WL.py, WL.qt] at y1 y2 y3 y4
    simp only [Set.mem_ofPred_eq]
    omega

/-! ### The end of an NZ activation -/

/-- **The end of an NZ activation**: the capture box at station `j`, the route of the answer, or the
unit row (the flight into the entry copy, the entry chain, the flight to the body input). -/
theorem dsepA_finN_hull (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h2 : t < decEndN p i r) : ∀ x ∈ finFootN p i r t,
    (376 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
      x.1 ≤ 467 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
      784 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
      x.2 ≤ 951 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ)) ∨
    (x.1 - x.2 ≤ U p r + nzAnsChan p (callerIdx p r i) + 29 ∨
      x.1 + x.2 ≤ VT p + 660 * instrBand i + 404 ∨
      (x.1 - x.2 ≤ U p r - 300 ∧ nzAnsPortV (callerIdx p r i) - 26 ≤ x.1 + x.2 ∧
        x.1 + x.2 ≤ nzAnsPortV (callerIdx p r i) + 19)) ∨
    x.1 + x.2 ≤ VU p + 216 := by
  intro x hx
  obtain ⟨hdU, hdV⟩ := (dsepA_layAN hp hi).2.2.2.2.2.2
  have hc := decCap_cast p hi
  obtain ⟨hD, -, hT0, -, -, hDT⟩ := decN_times hp hi
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  unfold finFootN at hx
  split_ifs at hx with ha hb
  · left
    have := dsepM_image_box ((stationNZ_captureE p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapN p i r) hc.1).subset (t - decCapN p i r)
      (by unfold decDispN at ha; unfold decCapN; omega) hx)
    simp only at this
    omega
  · unfold linkFootW at hx
    split_ifs at hx with hc1 hc2
    · right; left
      exact dsepA_routeAN_hull hp hi (t - decDispN p i r) hc1 x hx
    · right; right
      have e := dsep_csN_eq hp hi
      obtain ⟨-, htim, -, -, -⟩ := decAnsN_plan hp hi _ hD
      change RouteTimedX (decGN p i r) (decCsN p i r) _ at htim
      rw [e] at htim hc1 hx
      have hpT := decTN_par p i r
      obtain ⟨cu, cv, hr, hsub⟩ := dsepA_final_ray _ _ (decGN p i r) (decDispN p i r)
        (by simp [isep2SlabC]) (by simp only [CPar, rfCU, rfCV, isep2SlabC]; rw [htN]; omega)
        htim (t := t) (by omega)
      rw [show ((decDispN p i r : ℕ) : ℤ) + ((t - decDispN p i r : ℕ) : ℤ) = ((t : ℕ) : ℤ) by
        push_cast [Nat.cast_sub (show decDispN p i r ≤ t by omega)]; ring] at hx
      obtain ⟨y1, y2, y3, y4⟩ := hsub hx
      simp only [Ray, outD, isep2SlabC] at hr
      rw [htN] at hr
      omega
    · right; right
      have := isep2_entryFoot_xy hx
      omega
  · right; right
    have := isep2_mem_outC p (i + 1) (j := t - (decT0N p i r + (134 + decTNn p i r * 254)))
      (by unfold decEndN at h2; omega) hx
    omega

/-- The pieces of the end of an NZ activation: station `j` or the pieces of the answer link. -/
theorem dsepA_LFN_cases {g : Piece} (hg : g ∈ decLFN p i r) :
    g ∈ stNZOne p r (callerIdx p r i) ∨ g ∈ decLF0N p i r := by
  simp only [decLFN, mem_dd, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact Or.inl hg
  · exact Or.inr (mem_dd.2 (List.mem_append_left _ hg))
  · exact Or.inr (mem_dd.2 (List.mem_append_right _ hg))

/-- **`DecSep.nA2a`**: after the capture, the rest of the NZ run is far from the end. -/
theorem dsepA_nA2a (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, decCapN p i r ≤ t → t < decEndN p i r →
      FarApart 2 (restFootN p i r t) (boxesOf (decLFN p i r) ∪ finFootN p i r t) := by
  intro t h1 h2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hcA, hvA, -⟩ := dsepA_layAN hp hi
  refine dsepT_far_union_r (farApart_boxesOf fun g hg => ?_) ?_
  · rcases dsepA_LFN_cases hg with hg | hg
    · refine dsepA_far (dsepA_restN_mh t) (fun x hx => dsepA_sjN_cells hg hx)
        fun a b ha hb => ?_
      simp only [dsepAMHat] at ha
      omega
    · exact dsepA_mh_F hp hi (dsepA_restN_mh t) g hg
  · refine dsepA_far (dsepA_restN_mh t) (dsepA_finN_hull hp hi h2) fun a b ha hb => ?_
    simp only [dsepAMHat] at ha
    omega

/-- The pieces of the control, of the NZ stations `0 … j - 1` and of `KNZ`: in the hulls of the
reflectors of the control, the DEC copies, the stations or the reflectors of `KNZ`. -/
theorem dsepA_CSN_cases {g : Piece} (hg : g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r) :
    g ∈ decLC p i r ∨ g ∈ decLSN p i r ∨ g ∈ reflP (unitWL p i decLWL) (decCornN p i r) := by
  rcases List.mem_append.1 hg with hg | hg
  · rcases List.mem_append.1 hg with hg | hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl hg)
  · exact Or.inr (Or.inr (mem_dd.1 hg))

/-- **The pieces of the control, of the stations `0 … j - 1` and of `KNZ` are not reflectors of
the NZ answer.** -/
theorem dsepA_CSN_notAN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g : Piece}
    (hg : g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r) :
    g ∉ reflP (decGN p i r) (decCsN p i r) := by
  have hcs := dsepM_corner_mem hi (dsepM_specs hi).2.2.2.1
  rcases dsepA_CSN_cases hg with hg | hg | hg
  · rcases dsepM_mem_decLC hg with hr | ⟨m', hm', rfl⟩
    · exact dsepA_refl_other hp hi (dsepM_specs hi).2.2.2.1 (dsepM_specs hi).2.1
        dsepA_tags_AN_C g hr
    · exact dsepA_not_refl_wide (dsepA_copy_wide p r m' _).1 (dsepA_copy_wide p r m' _).2
  · have hn := dsepT_mach_ne (decLSN_mem hi g hg)
    have hx : (g.a, g.lo) ∈ g.box := ⟨le_rfl, hn.1, le_rfl, hn.2⟩
    obtain ⟨k, hk0, hk1, hb⟩ := dsepA_LSN_cells hg hx
    have hu := modD_uv p r
    have hj := dsepM_j_lt hi
    refine dsepA_not_refl_zone hp r hcs hx ?_
    simp only at hb ⊢
    omega
  · exact dsepA_refl_other hp hi (dsepM_specs hi).2.2.2.1 (dsepM_specs hi).1
      dsepA_tags_AN_N g hg

/-- The cells of the pieces of the control, of the NZ stations `0 … j - 1` and of `KNZ`. -/
theorem dsepA_CSN_cells {g : Piece} (hg : g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r) :
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
    ((380 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 412 + modDX p r + 72 * k ∧
      829 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 919 + modDY p r + 72 * k) ∨
    (431 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 439 + modDX p r + 72 * k ∧
      891 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 913 + modDY p r + 72 * k) ∨
    (464 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 467 + modDX p r + 72 * k ∧
      820 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 823 + modDY p r + 72 * k))) ∨
    (dsepACB (A p i + decL) (trackOut p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
      (trackOut p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
      (trackBack p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (U p r + nzTokChan p (callerIdx p r i)) (trackBack p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (U p r + nzTokChan p (callerIdx p r i)) (nzTokPortV (callerIdx p r i)) x) := by
  intro x hx
  rcases dsepA_CSN_cases hg with hg | hg | hg
  · exact Or.inl (dsepA_LC_cells hg hx)
  · exact Or.inr (Or.inl (dsepA_LSN_cells hg hx))
  · exact Or.inr (Or.inr (dsepA_LN_cells hg hx))

/-- The rest of the NZ run is far from the pieces of the control, of the NZ stations `0 … j - 1`
and of `KNZ`. -/
theorem dsepA_rest_CSN (hi : p[i]? = some (.decJz r z)) (t : ℕ) {g : Piece}
    (hg : g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r) :
    FarApart 2 (restFootN p i r t) g.box := by
  obtain ⟨hO0, hB0, hO1, hB1, -, -, hcN, hcC, hvC, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  have hdL : decL = -155 := rfl
  have hdR : decR = 127 := rfl
  have hm := decM_cast p hi
  refine dsepA_far (dsepA_restN_mh t) (dsepA_CSN_cells hg) fun a b ha hb => ?_
  simp only [dsepAMHat] at ha
  rcases hb with (hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩) | ⟨k, hk0, hk1, hb⟩ | hb <;>
    (try simp only [dsepACB] at hb) <;> omega

/-- Station `j` of the line NZ is far from the pieces of the control, of the NZ stations
`0 … j - 1` and of `KNZ`. -/
theorem dsepA_sjN_CSN (hi : p[i]? = some (.decJz r z)) {g h : Piece}
    (hg : g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r) (hh : h ∈ stNZOne p r (callerIdx p r i)) :
    FarApart 2 h.box g.box := by
  obtain ⟨hO0, hB0, hO1, hB1, -, -, hcN, hcC, hvC, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  have hdL : decL = -155 := rfl
  have hdR : decR = 127 := rfl
  have hm := decM_cast p hi
  refine dsepA_far (fun x hx => dsepA_sjN_cells hh hx) (dsepA_CSN_cells hg) fun a b ha hb => ?_
  rcases hb with (hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩) | ⟨k, hk0, hk1, hb⟩ | hb <;>
    (try simp only [dsepACB] at hb) <;> omega

/-- The box of a piece of a list lies in the boxes of the list. -/
theorem dsepA_box_sub {L : List Piece} {g : Piece} (hg : g ∈ L) : g.box ⊆ boxesOf L :=
  fun _ hx => mem_boxesOf.2 ⟨g, hg, hx⟩

/-- The pieces of the NZ answer link are far from the pieces of the control, of the NZ stations
`0 … j - 1` and of `KNZ`. -/
theorem dsepA_LF0N_CSN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g h : Piece}
    (hg : g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r) (hh : h ∈ decLF0N p i r) :
    FarApart 2 h.box g.box := by
  rcases dsepA_CSN_cases hg with hg | hg | hg
  · exact ((dsepA_LC_F hp hi h hh).mono (dsepA_box_sub hg) le_rfl).symm'
  · exact ((dsepA_LSN_F hp hi h hh).mono (dsepA_box_sub hg) le_rfl).symm'
  · exact ((dsepA_LNu_F hp hi h hh).mono
      (dsepA_box_sub (mem_dd.2 (List.mem_append_left _ hg))) le_rfl).symm'

/-- A set in the unit row is far from the pieces of the control, of the NZ stations `0 … j - 1`
and of `KNZ`. -/
theorem dsepA_row_CSN (hi : p[i]? = some (.decJz r z)) {X : Set Cell}
    (hX : ∀ x ∈ X, x.1 + x.2 ≤ VU p + 216) {g : Piece}
    (hg : g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r) : FarApart 2 X g.box := by
  obtain ⟨hO0, hB0, hO1, hB1, -, -, hcN, hcC, hvC, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  have hm := decM_cast p hi
  refine dsepA_far hX (dsepA_CSN_cells hg) fun a b ha hb => ?_
  rcases hb with (hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩) | ⟨k, hk0, hk1, hb⟩ | hb <;>
    (try simp only [dsepACB] at hb) <;> omega

/-- **The end of an NZ activation is far from the pieces of the control, of the NZ stations
`0 … j - 1` and of `KNZ`.** -/
theorem dsepA_fin_CSN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h2 : t < decEndN p i r) {g : Piece}
    (hg : g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r) :
    FarApart 2 (finFootN p i r t) g.box := by
  have hgm : g ∈ machPieces p := by
    rcases dsepA_CSN_cases hg with hg | hg | hg
    · exact decLC_mem hi g hg
    · exact decLSN_mem hi g hg
    · exact decLN_mem hi g (mem_dd.2 hg)
  obtain ⟨hdU, hdV⟩ := (dsepA_layAN hp hi).2.2.2.2.2.2
  have hc := decCap_cast p hi
  obtain ⟨hD, -, hT0, -, -, hDT⟩ := decN_times hp hi
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  unfold finFootN
  split_ifs with ha hb
  · obtain ⟨hO0, hB0, hO1, hB1, -, -, hcN, hcC, hvC, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD,
      hD1, hA0, hHI, hP1, hAU, hT0', hT0'', hVU, hu1, hu2⟩ := dsepA_lay hi
    have hdL : decL = -155 := rfl
    have hdR : decR = 127 := rfl
    have hm := decM_cast p hi
    refine dsepA_far (fun x hx => dsepM_image_box ((stationNZ_captureE p r (callerIdx p r i)
      (decShift p i r) (decShift_mod p i r) (decCapN p i r) hc.1).subset (t - decCapN p i r)
      (by unfold decDispN at ha; unfold decCapN; omega) hx)) (dsepA_CSN_cells hg)
      fun a b ha hb => ?_
    simp only at ha
    rcases hb with (hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩) | ⟨k, hk0, hk1, hb⟩ | hb <;>
      (try simp only [dsepACB] at hb) <;> omega
  · unfold linkFootW
    split_ifs with hc1 hc2
    · exact dsepA_routeAN_far hp hi hc1 hgm (dsepA_CSN_notAN hp hi hg)
    · refine dsepA_row_CSN hi (fun x hx => ?_) hg
      have e := dsep_csN_eq hp hi
      obtain ⟨-, htim, -, -, -⟩ := decAnsN_plan hp hi _ hD
      change RouteTimedX (decGN p i r) (decCsN p i r) _ at htim
      rw [e] at htim hc1 hx
      have hpT := decTN_par p i r
      obtain ⟨cu, cv, hr, hsub⟩ := dsepA_final_ray _ _ (decGN p i r) (decDispN p i r)
        (by simp [isep2SlabC]) (by simp only [CPar, rfCU, rfCV, isep2SlabC]; rw [htN]; omega)
        htim (t := t) (by omega)
      rw [show ((decDispN p i r : ℕ) : ℤ) + ((t - decDispN p i r : ℕ) : ℤ) = ((t : ℕ) : ℤ) by
        push_cast [Nat.cast_sub (show decDispN p i r ≤ t by omega)]; ring] at hx
      obtain ⟨y1, y2, y3, y4⟩ := hsub hx
      simp only [Ray, outD, isep2SlabC] at hr
      rw [htN] at hr
      omega
    · exact dsepA_row_CSN hi (fun x hx => by have := isep2_entryFoot_xy hx; omega) hg
  · exact dsepA_row_CSN hi (fun x hx => by
      have := isep2_mem_outC p (i + 1) (j := t - (decT0N p i r + (134 + decTNn p i r * 254)))
        (by unfold decEndN at h2; omega) hx
      omega) hg

/-- **`DecSep.nA2b`**: after the capture, the rest of the NZ run and the end are far from the
pieces of the control, of the NZ stations `0 … j - 1` and of `KNZ`. -/
theorem dsepA_nA2b (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, decCapN p i r ≤ t → t < decEndN p i r →
    ∀ g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r,
    FarApart 2 (restFootN p i r t ∪ (boxesOf (decLFN p i r) ∪ finFootN p i r t)) g.box := by
  intro t h1 h2 g hg
  refine dsepT_far_union (dsepA_rest_CSN hi t hg)
    (dsepT_far_union ?_ (dsepA_fin_CSN hp hi h2 hg))
  refine FarApart.symm' (farApart_boxesOf fun h hh => ?_)
  rcases dsepA_LFN_cases hh with hh | hh
  · exact (dsepA_sjN_CSN hi hg hh).symm'
  · exact (dsepA_LF0N_CSN hp hi hg hh).symm'

end LP

end LeanTheory.Life
