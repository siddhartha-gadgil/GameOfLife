/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepX5

/-!
# The moving parts of the threads against the pieces of the other thread

Research note `N-22`. For the fields `nThr`, `zThr` and `zGate` of `DecSep`:

* `dsepX_C_route_far`, `dsepX_N_route_far`, `dsepX_Z_route_far`, `dsepX_AN_route_far`,
  `dsepX_AZ_route_far`: the routes of a `decJz` activation are far from every piece of the
  machine other than their reflectors (`isep2_rfoot_far` under the route fields `sepC`, …);
* the moving parts split into the route and a part in coordinates (`dsepX_footC_split`,
  `dsepX_tokN_split`, `dsepX_unpN_split`, `dsepX_tokZ_split`, `dsepX_unpZ_split`);
* `dsepX_finN_far`, `dsepX_finZ_far`: the end of an activation (capture, answer link, entry
  chain, flight to the body) far from a piece of the machine outside it.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The routes far from the pieces outside them -/

/-- **The route of `C` is far from every piece of the machine but its reflectors.** -/
theorem dsepX_C_route_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {k : ℕ}
    (hk : 4260 + k ≤ routeEndX (unitWL p i decRWL) (decCornC p i r) 4260) {h : Piece}
    (hh : h ∈ machPieces p) (hn : h ∉ reflP (unitWL p i decRWL) (decCornC p i r)) :
    FarApart 2 (routeFootX (unitWL p i decRWL) (decCornC p i r) 4260 k) h.box := by
  have hs := dsep_sepC hp hi
  have ht : RouteTimedX (unitWL p i decRWL) (decCornC p i r) ((4260 : ℕ) : ℤ) :=
    decC_timedX p hi
  have hl := (decC_lines p i r).1
  have hk8 : ∀ c ∈ decCornC p i r, c.k < 8 := by rw [dsepX_cornC_eq]; simp
  obtain ⟨c, cs, e⟩ : ∃ c cs, decCornC p i r = c :: cs := ⟨_, _, rfl⟩
  rw [e] at hs ht hl hk8 hk hn ⊢
  exact isep2_rfoot_far cs c _ 4260 hs ht hl hk8 k hk h hh hn

/-- **The route of `KNZ` is far from every piece of the machine but its reflectors.** -/
theorem dsepX_N_route_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {k : ℕ}
    (hk : 4260 + k ≤ routeEndX (unitWL p i decLWL) (decCornN p i r) 4260) {h : Piece}
    (hh : h ∈ machPieces p) (hn : h ∉ reflP (unitWL p i decLWL) (decCornN p i r)) :
    FarApart 2 (routeFootX (unitWL p i decLWL) (decCornN p i r) 4260 k) h.box := by
  have hs := dsep_sepN hp hi
  have ht : RouteTimedX (unitWL p i decLWL) (decCornN p i r) ((4260 : ℕ) : ℤ) :=
    decKNZ_timedX p hi
  have hl := (decKNZ_lines p i r).1
  have hk8 : ∀ c ∈ decCornN p i r, c.k < 8 := by rw [dsepX_cornN_eq]; simp
  obtain ⟨c, cs, e⟩ : ∃ c cs, decCornN p i r = c :: cs := ⟨_, _, rfl⟩
  rw [e] at hs ht hl hk8 hk hn ⊢
  exact isep2_rfoot_far cs c _ 4260 hs ht hl hk8 k hk h hh hn

/-- **The route of `KZ` is far from every piece of the machine but its reflectors.** -/
theorem dsepX_Z_route_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {k : ℕ}
    (hk : 4260 + k ≤ routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260) {h : Piece}
    (hh : h ∈ machPieces p) (hn : h ∉ reflP (unitWL p i decDWL) (decCornZ p i r)) :
    FarApart 2 (routeFootX (unitWL p i decDWL) (decCornZ p i r) 4260 k) h.box := by
  have hs := dsep_sepZ hp hi
  have ht : RouteTimedX (unitWL p i decDWL) (decCornZ p i r) ((4260 : ℕ) : ℤ) :=
    decKZ_timedX p hi
  have hl := decKZ_lines p i r
  have hk8 : ∀ c ∈ decCornZ p i r, c.k < 8 := by rw [dsepX_cornZ_eq]; simp
  obtain ⟨c, cs, e⟩ : ∃ c cs, decCornZ p i r = c :: cs := ⟨_, _, rfl⟩
  rw [e] at hs ht hl hk8 hk hn ⊢
  exact isep2_rfoot_far cs c _ 4260 hs ht hl hk8 k hk h hh hn

/-- **The route of the NZ answer is far from every piece of the machine but its reflectors.** -/
theorem dsepX_AN_route_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {k : ℕ}
    (hk : decDispN p i r + k ≤ routeEndX (decGN p i r) (decCsN p i r) (decDispN p i r))
    {h : Piece} (hh : h ∈ machPieces p) (hn : h ∉ reflP (decGN p i r) (decCsN p i r)) :
    FarApart 2 (routeFootX (decGN p i r) (decCsN p i r) (decDispN p i r) k) h.box := by
  obtain ⟨hD, -⟩ := decN_times hp hi
  obtain ⟨hl, ht, -⟩ := decAnsN_plan hp hi _ hD
  have hs := dsep_sepAN hp hi
  change RouteLines (decGN p i r) (decCsN p i r) at hl
  change RouteTimedX (decGN p i r) (decCsN p i r) _ at ht
  have hk8 : ∀ c ∈ decCsN p i r, c.k < 8 := by
    rw [dsep_csN_eq hp hi]; simp [bandCorners, isep2SlabC]
  obtain ⟨c, cs, e⟩ : ∃ c cs, decCsN p i r = c :: cs := ⟨_, _, rfl⟩
  rw [e] at hs ht hl hk8 hk hn ⊢
  exact isep2_rfoot_far cs c _ _ hs ht hl hk8 k hk h hh hn

/-- **The route of the Z answer is far from every piece of the machine but its reflectors.** -/
theorem dsepX_AZ_route_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {k : ℕ}
    (hk : decDispZ p i r + k ≤ routeEndX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r))
    {h : Piece} (hh : h ∈ machPieces p) (hn : h ∉ reflP (decGZ p i r) (decCsZ p i r z)) :
    FarApart 2 (routeFootX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) k) h.box := by
  obtain ⟨hD, -⟩ := decZ_times hp hi
  obtain ⟨hl, ht, -⟩ := decAnsZ_plan hp hi _ hD
  have hs := dsep_sepAZ hp hi
  change RouteLines (decGZ p i r) (decCsZ p i r z) at hl
  change RouteTimedX (decGZ p i r) (decCsZ p i r z) _ at ht
  have hk8 : ∀ c ∈ decCsZ p i r z, c.k < 8 := by
    rw [dsep_csZ_eq hp hi]; simp [bandCorners, isep2SlabC]
  obtain ⟨c, cs, e⟩ : ∃ c cs, decCsZ p i r z = c :: cs := ⟨_, _, rfl⟩
  rw [e] at hs ht hl hk8 hk hn ⊢
  exact isep2_rfoot_far cs c _ _ hs ht hl hk8 k hk h hh hn


/-! ### The flights of the answers to their entry copies -/

/-- **The flight of the NZ answer to its entry copy**, up to `16` generations before the arrival
(included), is far from every piece of the machine. -/
theorem dsepX_flyAN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, routeEndX (decGN p i r) (decCsN p i r) (decDispN p i r) ≤ t →
      t + 16 ≤ decT0N p i r → ∀ h ∈ machPieces p,
        FarApart 2 ((route (decGN p i r) (decCsN p i r)).2.box t) h.box := by
  intro t h1 h2 h hh
  have hl : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨hD, -, hT0, -⟩ := decN_times hp hi
  obtain ⟨-, htim, hδ, hfin, -⟩ := decAnsN_plan hp hi _ hD
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  have e := dsep_csN_eq hp hi
  have hcS : isep2SlabC p (i + 1) ((decTNn p i r : ℕ) : ℤ) ∈ allCorners p :=
    instrRoute_corner hl (x := (decGN p i r, decMkN p i r (decEA p i r)))
      (by rw [dsep_instrSpecs hi]; simp) _ (by
        change _ ∈ decCsN p i r
        rw [e]; simp)
  change RouteTimedX (decGN p i r) (decCsN p i r) _ at htim
  change (route (decGN p i r) (decCsN p i r)).2 = _ at hfin
  rw [e] at htim hfin h1
  have := isep2_flyEntry hp (a := i + 1) (t := decTNn p i r) (by rw [htN]; exact ht.2) hcS htim
    hδ hfin (T0 := decT0N p i r) (by rw [hT0]; rfl) t h1 h2 h hh
  rw [e]
  exact this

/-- **The flight of the Z answer to its entry copy**, up to `16` generations before the arrival
(included), is far from every piece of the machine. -/
theorem dsepX_flyAZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, routeEndX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) ≤ t →
      t + 16 ≤ decT0Z p i r z → ∀ h ∈ machPieces p,
        FarApart 2 ((route (decGZ p i r) (decCsZ p i r z)).2.box t) h.box := by
  intro t h1 h2 h hh
  have hl : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨hD, -, hT0, -⟩ := decZ_times hp hi
  obtain ⟨-, htim, hδ, hfin, -⟩ := decAnsZ_plan hp hi _ hD
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  have e := dsep_csZ_eq hp hi
  have hcS : isep2SlabC p z ((decTZn p i r z : ℕ) : ℤ) ∈ allCorners p :=
    instrRoute_corner hl (x := (decGZ p i r, decMkZ p i r z (decEB p i r z)))
      (by rw [dsep_instrSpecs hi]; simp) _ (by
        change _ ∈ decCsZ p i r z
        rw [e]; simp)
  change RouteTimedX (decGZ p i r) (decCsZ p i r z) _ at htim
  change (route (decGZ p i r) (decCsZ p i r z)).2 = _ at hfin
  rw [e] at htim hfin h1
  have hT0' : (decT0Z p i r z : ℤ) = 180 + 30 * decKZ p i r z +
      16 * ((decTZn p i r z : ℕ) : ℤ) % 30 := by
    rw [hT0, htN]
  have := isep2_flyEntry hp (a := z) (t := decTZn p i r z) (by rw [htN]; exact ht.2) hcS htim
    hδ hfin (T0 := decT0Z p i r z) (by rw [hT0']; rfl) t h1 h2 h hh
  rw [e]
  exact this

/-! ### The ends of the activations far from a piece -/

/-- **The end of an NZ activation is far from a piece of the machine** outside the answer link,
far from the capture at station `j`. -/
theorem dsepX_finN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCapN p i r ≤ t) (h2 : t < decEndN p i r) {h : Piece} (hh : h ∈ machPieces p)
    (hn1 : h ∉ reflP (decGN p i r) (decCsN p i r))
    (hn2 : h ∉ chainPieces p (i + 1) (decTNn p i r))
    (hcap : FarApart 2 (dsepXMR p r ∩ {x | x.1 - x.2 ≤ U p r - 317 ∧ 1160 ≤ x.1 + x.2})
      h.box) : FarApart 2 (finFootN p i r t) h.box := by
  have eD : decCapN p i r + 692 = decDispN p i r := by unfold decCapN decDispN; omega
  unfold finFootN
  split_ifs with ha hb
  · exact hcap.mono (dsepX_capN_M hi (k := t - decCapN p i r) (by omega)) le_rfl
  · unfold linkFootW
    split_ifs with hc hd
    · exact dsepX_AN_route_far hp hi hc hh hn1
    · have e : ((decDispN p i r : ℕ) : ℤ) + ((t - decDispN p i r : ℕ) : ℤ) = ((t : ℕ) : ℤ) := by
        omega
      rw [e]
      exact dsepX_flyAN hp hi t (by omega) (by omega) h hh
    · exact dsep_entAN hp hi h hh hn2
  · unfold outFoot
    exact dsep_outAN hp (t - (decT0N p i r + (134 + decTNn p i r * 254)))
      (by unfold decEndN at h2; omega) h hh

/-- **The end of a Z activation is far from a piece of the machine** outside the answer link,
far from the capture at station `j`. -/
theorem dsepX_finZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCapZ p i r ≤ t) (h2 : t < decEndZ p i r z) {h : Piece} (hh : h ∈ machPieces p)
    (hn1 : h ∉ reflP (decGZ p i r) (decCsZ p i r z))
    (hn2 : h ∉ chainPieces p z (decTZn p i r z))
    (hcap : FarApart 2 (dsepXMZ p r ∩ {x | U p r + 1138 ≤ x.1 - x.2 ∧ 469 ≤ x.1 + x.2 ∧
      x.1 + x.2 ≤ 722}) h.box) : FarApart 2 (finFootZ p i r z t) h.box := by
  have eD : decCapZ p i r + 672 = decDispZ p i r := by unfold decCapZ decDispZ; omega
  unfold finFootZ
  split_ifs with ha hb
  · exact hcap.mono (dsepX_capZ_M hi (k := t - decCapZ p i r) (by omega)) le_rfl
  · unfold linkFootW
    split_ifs with hc hd
    · exact dsepX_AZ_route_far hp hi hc hh hn1
    · have e : ((decDispZ p i r : ℕ) : ℤ) + ((t - decDispZ p i r : ℕ) : ℤ) = ((t : ℕ) : ℤ) := by
        omega
      rw [e]
      exact dsepX_flyAZ hp hi t (by omega) (by omega) h hh
    · exact dsep_entAZ hp hi h hh hn2
  · unfold outFoot
    exact dsep_outAZ hp (t - (decT0Z p i r z + (134 + decTZn p i r z * 254)))
      (by unfold decEndZ at h2; omega) h hh

/-! ### The moving parts, split into the route and the rest -/

/-- **The control `C` before the register run**: on its route, or in the left-low part of the
module (the port line, the DEC chain at `v ≤ -3270`, the flight of `C'` on `u ∈ [U_r + 37,
U_r + 45]`). -/
theorem dsepX_footC_split (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t ≤ decTS p i r) {x : Cell} (hx : x ∈ decFootC p i r t) :
    (4260 + (t - 4260) ≤ routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ∧
      x ∈ routeFootX (unitWL p i decRWL) (decCornC p i r) 4260 (t - 4260)) ∨
    (-3360 - 198 * D p ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ -2350 ∧
      (x.1 + x.2 ≤ -3270 ∨ (U p r + 37 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + 45))) := by
  have hu := modD_uv p r
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  have hD := one_le_D p
  have hUe := U_even p r
  obtain ⟨-, hA20, hTA⟩ := decTA_facts p hi
  have hs := sigma_cases (qOf p (callerIdx p r i))
  unfold decFootC at hx
  split_ifs at hx with ha hb hc
  · unfold flyFoot at hx
    split_ifs at hx with hd
    · exact Or.inl ⟨by omega, hx⟩
    · right
      change x ∈ (decGC p i r).box t at hx
      obtain ⟨x1, x2, x3, x4⟩ := hx
      rw [decC_window] at x1 x2 x3 x4
      simp only [decWin, modWL, WL.shift, WL.px, WL.py, WL.qt, modDX, modDY] at x1 x2 x3 x4 hu
      omega
  · right
    obtain ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · right
    obtain ⟨d, ⟨j, hj', d1, d2, d3, d4⟩, rfl⟩ := hx
    rw [show chainV = (35, 64) from rfl] at d1 d2 d3 d4
    have : (j : ℤ) ≤ (decM p i r : ℤ) := by omega
    simp only [Prod.fst_add, Prod.snd_add] at *
    omega
  · right
    obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    have e1 : decTS p i r = decTB p i r + 1771 := by unfold decTS decTB; omega
    simp only [cp0WL, WL.px, WL.py, WL.qt] at *
    simp only [Prod.fst_add, Prod.snd_add]
    omega

/-- **The token `KNZ`** until its capture: on its route, or on its port line and at station `j`
(`u ∈ [U_r + c_N - 21, U_r - 300]`, `v ≥ 1150`). -/
theorem dsepX_tokN_split (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (h1 : t ≤ decCapN p i r) {x : Cell} (hx : x ∈ tokFootN p i r t) :
    (4260 + (t - 4260) ≤ routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ∧
      x ∈ routeFootX (unitWL p i decLWL) (decCornN p i r) 4260 (t - 4260)) ∨
    (U p r + nzTokChan p (callerIdx p r i) - 21 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r - 300 ∧
      1150 ≤ x.1 + x.2) := by
  unfold tokFootN at hx
  split_ifs at hx with ha
  · unfold flyFoot at hx
    split_ifs at hx with hb
    · exact Or.inl ⟨by omega, hx⟩
    · exact Or.inr (dsepX_nFly_sub hi (by omega) ha hx)
  · obtain ⟨-, -, -, l4, l5, l6, l7⟩ := dsepX_n_layout hi
    have hu := modD_uv p r
    have hj := dsepM_j_lt hi
    rw [decTokWStartN_eq hi, Rule.evolve_translate] at hx
    have := dsepM_translate_box (stTokWNZ.subset _ (by omega)) hx
    right
    have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
    omega

/-- **The unpaired `KNZ`**: on its route, or on its port line and at station `j`. -/
theorem dsepX_unpN_split (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t) {x : Cell}
    (hx : x ∈ unpFootN p i r t) :
    (4260 + (t - 4260) ≤ routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ∧
      x ∈ routeFootX (unitWL p i decLWL) (decCornN p i r) 4260 (t - 4260)) ∨
    (U p r + nzTokChan p (callerIdx p r i) - 21 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r - 300 ∧
      1150 ≤ x.1 + x.2) := by
  unfold unpFootN at hx
  split_ifs at hx with ha hb
  · exact dsepX_tokN_split hi h0 ha hx
  · obtain ⟨-, -, -, -, l5, -, -⟩ := dsepX_n_layout hi
    have hu := modD_uv p r
    have hj := dsepM_j_lt hi
    have hc := decCap_cast p hi
    have := dsepM_image_box ((stationNZ_unpaired p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapN p i r) hc.1).subset (t - decCapN p i r) (by omega) hx)
    right
    have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
    omega
  · exact hx.elim

/-- **The token `KZ`** until its capture: on its route, or in the right zone of the module
(`u ≥ U_r + 1150`, `v ≥ 450`). -/
theorem dsepX_tokZ_split (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (h1 : t ≤ decCapZ p i r) {x : Cell} (hx : x ∈ tokFootZ p i r t) :
    (4260 + (t - 4260) ≤ routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 ∧
      x ∈ routeFootX (unitWL p i decDWL) (decCornZ p i r) 4260 (t - 4260)) ∨
    (U p r + 1150 ≤ x.1 - x.2 ∧ 450 ≤ x.1 + x.2) := by
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
  unfold tokFootZ at hx
  split_ifs at hx with ha
  · unfold flyFoot at hx
    split_ifs at hx with hb
    · exact Or.inl ⟨by omega, hx⟩
    · have := dsepX_kzFly_sub hi ha x hx
      right
      omega
  · rw [decTokWStartZ_eq hi, Rule.evolve_translate] at hx
    have := dsepM_translate_box (stTokWZ.subset _ (by omega)) hx
    right
    omega

/-- **The unpaired `KZ`**: on its route, or in the right zone of the module. -/
theorem dsepX_unpZ_split (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t) {x : Cell}
    (hx : x ∈ unpFootZ p i r t) :
    (4260 + (t - 4260) ≤ routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 ∧
      x ∈ routeFootX (unitWL p i decDWL) (decCornZ p i r) 4260 (t - 4260)) ∨
    (U p r + 1150 ≤ x.1 - x.2 ∧ 450 ≤ x.1 + x.2) := by
  unfold unpFootZ at hx
  split_ifs at hx with ha hb
  · exact dsepX_tokZ_split hi h0 ha hx
  · have hu := modD_uv p r
    have hj := dsepM_j_lt hi
    have hc := decCap_cast p hi
    have := dsepM_image_box ((stationZ_unpaired p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapZ p i r) hc.2).subset (t - decCapZ p i r) (by omega) hx)
    right
    have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
    omega
  · exact hx.elim

/-- A route part or a part in coordinates far from a piece: the combination. -/
theorem dsepX_split_far {X R : Set Cell} {Q : Cell → Prop} {h : Piece}
    (hX : ∀ x ∈ X, x ∈ R ∨ Q x) (hR : FarApart 2 R h.box)
    (hQ : ∀ x, Q x → ∀ y ∈ h.box, x.1 - x.2 + 5 ≤ y.1 - y.2 ∨ y.1 - y.2 + 5 ≤ x.1 - x.2 ∨
      x.1 + x.2 + 5 ≤ y.1 + y.2 ∨ y.1 + y.2 + 5 ≤ x.1 + x.2) :
    FarApart 2 X h.box := by
  intro x hx y hy hn
  rcases hX x hx with h1 | h1
  · exact hR x h1 y hy hn
  · exact dsepT_far_cells (A := {x}) (B := h.box) (fun a ha b hb => by
      rw [Set.mem_singleton_iff] at ha; subst ha; exact hQ _ h1 b hb) x rfl y hy hn

end LP

end LeanTheory.Life
