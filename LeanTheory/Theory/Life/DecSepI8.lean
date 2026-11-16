/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepI7

/-!
# The lanes of the other registers: the parts of the threads

Research note `N-22`. Every part of the footprints of the threads of a `decJz` activation at
register `r` is clear of the lanes of every register `r' ≠ r`: the runs at the stations and the
answers in the zone of module `r`, the flights of the tokens in its `u`-band, the routes by
`RouteLane` (`lane_instrRoute`, started low from the unit or beside the lanes from the station),
the control and the flights into the entry copies low.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The runs at the stations -/

/-- The region of the runs at station `j` of the line NZ lies in the zone. -/
theorem dsepI_RN_zone {j : ℕ} (hj : j < numCallers p) :
    (fun c => ((72 * (j : ℤ), 72 * (j : ℤ)) : Cell) + c) '' dsepIRN ⊆ dsepTZone p := by
  have hD : D p = (numCallers p : ℤ) := rfl
  rintro _ ⟨d, hd, rfl⟩
  rw [dsepIRN, dsepI_mem_tight2] at hd
  dsimp only at hd
  simp only [dsepTZone, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
  omega

/-- The region of the runs at station `j` of the line Z lies in the zone. -/
theorem dsepI_RZ_zone {j : ℕ} (hj : j < numCallers p) :
    (fun c => ((72 * (j : ℤ), -72 * (j : ℤ)) : Cell) + c) '' dsepIRZ ⊆ dsepTZone p := by
  have hD : D p = (numCallers p : ℤ) := rfl
  rintro _ ⟨d, hd, rfl⟩
  rw [dsepIRZ, dsepI_mem_tight2] at hd
  dsimp only at hd
  simp only [dsepTZone, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
  omega

/-- The joint approach of `KNZ` and its station is clear of the lanes of the other registers. -/
theorem dsepI_winN_lane (hi : p[i]? = some (.decJz r z)) {r' : ℕ} (hr : r' ≠ r) :
    ∀ k ≤ 90, LaneClear p r' (conway.evolve k (decTokWStartN p i r) : Set Cell) := by
  intro k hk
  rw [decTokWStartN_eq hi]
  exact (dsepI_zone_lane (dsepI_RN_zone (callerIdx_lt_D p hi)) hr).mono
    (((dsepI_tokWNZ_tight.translate _) k hk).trans (dsepI_img_sub p r _ _ dsepI_RN_sub.1))

/-- The extended capture at station `j` of the line NZ is clear of the other lanes. -/
theorem dsepI_capN_lane (hi : p[i]? = some (.decJz r z)) {r' : ℕ} (hr : r' ≠ r) :
    ∀ k ≤ 692, LaneClear p r' (conway.evolve k (decCapStartN p i r) : Set Cell) := by
  intro k hk
  rw [dsepI_capStartN_eq hi]
  exact (dsepI_zone_lane (dsepI_RN_zone (callerIdx_lt_D p hi)) hr).mono
    (((dsepI_capNZ_tight.translate _) k hk).trans (dsepI_img_sub p r _ _ dsepI_RN_sub.2.1))

/-- The absorption of the unpaired `KNZ` is clear of the other lanes. -/
theorem dsepI_unpN_lane (hi : p[i]? = some (.decJz r z)) {r' : ℕ} (hr : r' ≠ r) :
    ∀ k ≤ 292, LaneClear p r' (conway.evolve k (decUnpStartN p i r) : Set Cell) := by
  intro k hk
  rw [dsepI_unpStartN_eq hi]
  exact (dsepI_zone_lane (dsepI_RN_zone (callerIdx_lt_D p hi)) hr).mono
    (((dsepI_unpNZ_tight.translate _) k hk).trans (dsepI_img_sub p r _ _ dsepI_RN_sub.2.2))

/-- The joint approach of `KZ` and its station is clear of the lanes of the other registers. -/
theorem dsepI_winZ_lane (hi : p[i]? = some (.decJz r z)) {r' : ℕ} (hr : r' ≠ r) :
    ∀ k ≤ 90, LaneClear p r' (conway.evolve k (decTokWStartZ p i r) : Set Cell) := by
  intro k hk
  rw [decTokWStartZ_eq hi, dsepI_neg72]
  exact (dsepI_zone_lane (dsepI_RZ_zone (callerIdx_lt_D p hi)) hr).mono
    (((dsepI_tokWZ_tight.translate _) k hk).trans (dsepI_img_sub p r _ _ dsepI_RZ_sub.1))

/-- The extended capture at station `j` of the line Z is clear of the other lanes. -/
theorem dsepI_capZ_lane (hi : p[i]? = some (.decJz r z)) {r' : ℕ} (hr : r' ≠ r) :
    ∀ k ≤ 672, LaneClear p r' (conway.evolve k (decCapStartZ p i r) : Set Cell) := by
  intro k hk
  rw [dsepI_capStartZ_eq hi, dsepI_neg72]
  exact (dsepI_zone_lane (dsepI_RZ_zone (callerIdx_lt_D p hi)) hr).mono
    (((dsepI_capZ_tight.translate _) k hk).trans (dsepI_img_sub p r _ _ dsepI_RZ_sub.2.1))

/-- The absorption of the unpaired `KZ` is clear of the other lanes. -/
theorem dsepI_unpZ_lane (hi : p[i]? = some (.decJz r z)) {r' : ℕ} (hr : r' ≠ r) :
    ∀ k ≤ 272, LaneClear p r' (conway.evolve k (decUnpStartZ p i r) : Set Cell) := by
  intro k hk
  rw [dsepI_unpStartZ_eq hi, dsepI_neg72]
  exact (dsepI_zone_lane (dsepI_RZ_zone (callerIdx_lt_D p hi)) hr).mono
    (((dsepI_unpZ_tight.translate _) k hk).trans (dsepI_img_sub p r _ _ dsepI_RZ_sub.2.2))

/-! ### The routes from the unit -/

/-- A route of the activation, started at `4260` from the `dec` unit with a band corner first,
is clear of the lanes of every register. -/
theorem dsepI_unitRoute_lane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {w : WL}
    {cs : List Corner} (hx : (unitWL p i w, cs) ∈ instrSpecs p i) (hd : w.Dir)
    (hl : RouteLines (unitWL p i w) cs) (hcv : (unitWL p i w).cv 4260 ≤ 343)
    (hc : ∀ c ∈ cs.head?, c.v ≤ 279) (r' : ℕ) :
    RouteLane p r' (unitWL p i w) cs ((4260 : ℕ) : ℤ) :=
  lane_instrRoute hp (List.getElem?_eq_some_iff.1 hi).1 hx (g := unitWL p i w) hd hl r'
    fun c h => lane_start_low (by exact_mod_cast hcv) (hc c h)


/-- The first corner of a route of the activation from the unit is a low band corner. -/
theorem dsepI_head_low (hi : p[i]? = some (.decJz r z)) {s c H cd : ℤ} {k0 k4 : ℕ}
    (hs : 0 ≤ s ∧ s ≤ 9) {tail : List Corner} :
    ∀ x ∈ (bandCorners p (instrBand i) s c H cd k0 k4 ++ tail).head?, x.v ≤ 279 := by
  have hl : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have hR := one_le_R p
  have hb : instrBand i ≤ N p + R p := by unfold instrBand N; omega
  intro x hx
  simp only [bandCorners, List.cons_append, List.head?_cons, Option.mem_def,
    Option.some.injEq] at hx
  subst hx
  have := lane_bandCorners_low (p := p) hb hs (c := c) (H := H) (cd := cd) (k0 := k0) (k4 := k4)
    _ List.mem_cons_self
  simp only at this ⊢
  omega

/-- The outputs of the `dec` unit start low. -/
theorem dsepI_unit_cv (p : Program) (i : ℕ) :
    (unitWL p i decLWL).cv 4260 ≤ 343 ∧ (unitWL p i decRWL).cv 4260 ≤ 343 ∧
      (unitWL p i decDWL).cv 4260 ≤ 343 := by
  have hu := unitD_uv p i
  have hV := lane_VT_low p
  simp only [WL.cv, unitWL, decLWL, decRWL, decDWL, WL.shift, WL.px, WL.py, WL.qt]
  refine ⟨by omega, by omega, by omega⟩

/-! ### The tokens -/

/-- **The moving footprint of `KNZ` is clear of the lanes of the other registers.** -/
theorem dsepI_tokFootN_lane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) {t : ℕ} (h0 : 4260 ≤ t) (h2 : t ≤ decCapN p i r) :
    LaneClear p r' (tokFootN p i r t) := by
  have hj := dsepM_j_lt hi
  have hu := modD_uv p r
  unfold tokFootN
  split_ifs with h3
  · unfold flyFoot
    split_ifs with h4
    · have hRL := dsepI_unitRoute_lane hp hi (dsepM_specs hi).1 ⟨Or.inl rfl, Or.inl rfl⟩
        (decKNZ_lines p i r).1 (dsepI_unit_cv p i).1 (dsepI_head_low hi (by norm_num)) r'
      have htim := decKNZ_timedX p hi
      obtain ⟨c, cs, hcs⟩ : ∃ c cs, decCornN p i r = c :: cs := ⟨_, _, rfl⟩
      rw [hcs] at hRL htim h4 ⊢
      exact dsepI_rfoot_lane cs c _ 4260 hRL htim _ (by omega)
    · rw [decKNZ_target]
      refine dsepI_band_lane (fun x hx => ?_) hr
      have := dsepI_flyN_mem hi (by omega) h3 hx
      omega
  · exact dsepI_winN_lane hi hr _ (by omega)

/-- **The moving footprint of `KZ` is clear of the lanes of the other registers.** -/
theorem dsepI_tokFootZ_lane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) {t : ℕ} (h0 : 4260 ≤ t) (h2 : t ≤ decCapZ p i r) :
    LaneClear p r' (tokFootZ p i r t) := by
  have hj := dsepM_j_lt hi
  have hu := modD_uv p r
  unfold tokFootZ
  split_ifs with h3
  · unfold flyFoot
    split_ifs with h4
    · have hRL := dsepI_unitRoute_lane hp hi (dsepM_specs hi).2.2.1 ⟨Or.inl rfl, Or.inl rfl⟩
        (decKZ_lines p i r) (dsepI_unit_cv p i).2.2 (dsepI_head_low hi (by norm_num)) r'
      have htim := decKZ_timedX p hi
      obtain ⟨c, cs, hcs⟩ : ∃ c cs, decCornZ p i r = c :: cs := ⟨_, _, rfl⟩
      rw [hcs] at hRL htim h4 ⊢
      exact dsepI_rfoot_lane cs c _ 4260 hRL htim _ (by omega)
    · rw [decKZ_target]
      refine dsepI_band_lane (fun x hx => ?_) hr
      have := dsepI_flyZ_mem hi h3 hx
      omega
  · exact dsepI_winZ_lane hi hr _ (by omega)

/-- **The moving footprint of the unpaired `KZ` is clear of the other lanes.** -/
theorem dsepI_unpFootZ_lane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) {t : ℕ} (h0 : 4260 ≤ t) : LaneClear p r' (unpFootZ p i r t) := by
  unfold unpFootZ
  split_ifs with h1 h2
  · exact dsepI_tokFootZ_lane hp hi hr h0 h1
  · exact dsepI_unpZ_lane hi hr _ (by omega)
  · exact fun _ h => h.elim

/-- **The moving footprint of the unpaired `KNZ` is clear of the other lanes.** -/
theorem dsepI_unpFootN_lane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) {t : ℕ} (h0 : 4260 ≤ t) : LaneClear p r' (unpFootN p i r t) := by
  unfold unpFootN
  split_ifs with h1 h2
  · exact dsepI_tokFootN_lane hp hi hr h0 h1
  · exact dsepI_unpN_lane hi hr _ (by omega)
  · exact fun _ h => h.elim

/-! ### The control -/

/-- The flight of `C'` is low. -/
theorem dsepI_cp_low (p : Program) (i r : ℕ) {t : ℕ} (h2 : t ≤ decTS p i r) :
    ∀ x ∈ decCpFoot p i r t, x.1 + x.2 ≤ -2000 := by
  have hu := modD_uv p r
  have e : decTS p i r = decTB p i r + 1771 := rfl
  have hs : ((t - decTB p i r : ℕ) : ℤ) ≤ 1771 := by omega
  rintro _ ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩
  simp only [cp0WL, WL.px, WL.py, WL.qt, Prod.fst_add, Prod.snd_add] at d1 d2 d3 d4 ⊢
  omega

/-- **The moving footprint of the control is clear of the lanes of every register.** -/
theorem dsepI_footC_lane (hi : p[i]? = some (.decJz r z)) {r' : ℕ} {t : ℕ} (h0 : 4260 ≤ t)
    (h2 : t ≤ decTS p i r) : LaneClear p r' (decFootC p i r t) := by
  have e : decTS p i r = decTB p i r + 1771 := rfl
  have hTB : decTA p i r ≤ decTB p i r := by unfold decTB; omega
  refine laneClear_of_le fun x hx => ?_
  unfold decFootC at hx
  split_ifs at hx with h3 h4 h5
  · have hl := dsep_footC_low hi h0 (show t < decTS p i r by omega) x
    unfold decFootC at hl
    simp only [h3, ↓reduceIte] at hl
    exact hl hx
  · have hl := dsep_footC_low hi h0 (show t < decTS p i r by omega) x
    unfold decFootC at hl
    simp only [h3, h4, ↓reduceIte] at hl
    exact hl hx
  · have hl := dsep_footC_low hi h0 (show t < decTS p i r by omega) x
    unfold decFootC at hl
    simp only [h3, h4, h5, ↓reduceIte] at hl
    exact hl hx
  · exact dsepI_cp_low p i r h2 x hx

/-! ### The answers -/

/-- **The moving footprint of the NZ answer is clear of the other lanes.** -/
theorem dsepI_ansFootN_lane (hi : p[i]? = some (.decJz r z)) {r' : ℕ} (hr : r' ≠ r) {t : ℕ}
    (h1 : decCutN p i r ≤ t) : LaneClear p r' (decAnsFootN p i r t) := by
  have hj := dsepM_j_lt hi
  have hD := one_le_D p
  unfold decAnsFootN
  split_ifs with h2
  · refine (dsepI_zone_lane (fun x hx => ?_) hr).mono (dsepT_ansN_sub hi h1)
    have hq : (((t - decCutN p i r) / 4 : ℕ) : ℤ) ≤ 287 := by
      unfold decSt0N at h2; unfold decCutN at h1 ⊢; omega
    obtain ⟨x1, x2, x3, x4⟩ := hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  · refine dsepI_zone_lane (fun x hx => ?_) hr
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := dsepT_chainNZ_hull hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega

/-- **The moving footprint of the Z answer is clear of the other lanes.** -/
theorem dsepI_ansFootZ_lane (hi : p[i]? = some (.decJz r z)) {r' : ℕ} (hr : r' ≠ r) {t : ℕ}
    (h1 : decCutZ p i r ≤ t) : LaneClear p r' (decAnsFootZ p i r t) := by
  have hj := dsepM_j_lt hi
  have hD := one_le_D p
  unfold decAnsFootZ
  split_ifs with h2
  · refine (dsepI_zone_lane (fun x hx => ?_) hr).mono (dsepT_ansZ_sub hi h1)
    have hq : (((t - decCutZ p i r) / 4 : ℕ) : ℤ) ≤ 174 := by
      unfold decSt0Z at h2; unfold decCutZ at h1 ⊢; omega
    obtain ⟨x1, x2, x3, x4⟩ := hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  · refine dsepI_zone_lane (fun x hx => ?_) hr
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := dsepT_chainZ_hull hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega

/-! ### The rest of the run -/

/-- The circuit and the lanes of register `r` are clear of the lanes of the other registers. -/
theorem dsepI_grpLanes_lane {r' : ℕ} (hr : r' ≠ r) :
    LaneClear p r' (boxesOf (modGroup p r) ∪ modLanes p r) :=
  (laneClear_boxesOf fun g hg => by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
    exact module_laneClear p r' (s := s) (r' := r) (by simp [moduleSpecs, hs])).union
    ((modLanes_near p r).laneClear hr)

/-- **The rest of the NZ run is clear of the other lanes.** -/
theorem dsepI_restFootN_lane {r' : ℕ} (hr : r' ≠ r) (t : ℕ) :
    LaneClear p r' (restFootN p i r t) := by
  unfold restFootN
  split_ifs
  · exact dsepI_zone_lane dsepI_restNZ_zone hr
  · exact dsepI_grpLanes_lane hr

/-- **The rest of the Z run is clear of the other lanes.** -/
theorem dsepI_restFootZ_lane {r' : ℕ} (hr : r' ≠ r) (t : ℕ) :
    LaneClear p r' (restFootZ p i r t) := by
  unfold restFootZ
  split_ifs
  · exact dsepI_zone_lane dsepI_restZ_zone hr
  · exact dsepI_grpLanes_lane hr
end LP

end LeanTheory.Life
