/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepX1

/-!
# The token `KZ` of a `decJz` activation in a region

Research note `N-22`. For the fields `nThr` and `zThr` of `DecSep`:

* `dsepXLoop`: the region of a link in one sub-band (source column `c`, `OUT` track `O`, hairpin
  column `H`, `BACK` track `B` up to the column `d`), with the extended relay boxes of its band
  corners;
* `dsepX_ztok_sub`: the footprint of a Z token link (`ztokCorners`) lies in a set containing its
  legs and its extended relay boxes;
* `dsepXKZ`: the region of `KZ` (its loop in sub-band `i + 1`, everything right of its channel,
  and the right zone of the module above `v = 400`); `dsepX_tokZ_sub`, `dsepX_unpZ_sub`: the
  footprint of `KZ` (paired or unpaired) lies in it at every generation from `4260`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The region of a link in one sub-band -/

/-- **The region of a link in one sub-band**: the source column `c` (below the `OUT` track `O`),
the `OUT` track, the hairpin column `H`, the `BACK` track `B` up to the column `d`. -/
def dsepXLoop (c O H B d : ℤ) : Set Cell :=
  {x | (c - 29 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c + 16 ∧ x.1 + x.2 ≤ O + 31) ∨
    (H - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c + 16 ∧ O - 18 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ O + 31) ∨
    (H - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ H + 28 ∧ O - 18 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B + 30) ∨
    (H - 17 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ d + 24 ∧ B - 19 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B + 30)}

/-- The corners of a Z token link, listed. -/
theorem dsepX_ztok_eq (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) :
    ztokCorners p b c H r j = [⟨3, c, trackOut p b 2 c, .band b 2 false⟩,
      ⟨7, H, trackOut p b 2 c, .band b 2 true⟩, ⟨4, H, trackBack p b 2 c, .band b 7 true⟩,
      ⟨2, U p r + zTokChan p j, trackBack p b 2 c, .band b 7 false⟩,
      ⟨3, U p r + zTokChan p j, zTokDepth p j, .right r j 2⟩,
      ⟨0, U p r + zTokStation j, zTokDepth p j, .right r j 3⟩] := rfl

/-- **A Z token link inside a set** (source column `c`, `OUT` track, hairpin column `H`, `BACK`
track, the channel `cd` up to the depth `W`, the depth line to the station column `st`, with the
extended relay boxes of the six corners). -/
theorem dsepX_ztok_sub (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) {g : WL} {T : ℕ}
    (htim : RouteTimedX g (ztokCorners p b c H r j) T)
    (hlin : RouteLines g (ztokCorners p b c H r j))
    (hH : (H - c) % 2 = 0) (hd : (U p r + zTokChan p j - c) % 2 = 0) {Z : Set Cell}
    (zs : isep2InH Z (c - 4) (c + 4) (trackOut p b 2 c - 7))
    (z1 : isep2InR Z (c - 29) (c + 16) (trackOut p b 2 c - 18) (trackOut p b 2 c + 27))
    (z12 : isep2InR Z (H + 9) (c - 9) (trackOut p b 2 c - 2) (trackOut p b 2 c + 6))
    (z2 : isep2InR Z (H - 25) (H + 20) (trackOut p b 2 c - 14) (trackOut p b 2 c + 31))
    (z23 : isep2InR Z (H - 4) (H + 4) (trackOut p b 2 c + 11) (trackBack p b 2 c - 7))
    (z3 : isep2InR Z (H - 17) (H + 28) (trackBack p b 2 c - 19) (trackBack p b 2 c + 26))
    (z34 : isep2InR Z (H + 9) (U p r + zTokChan p j - 9) (trackBack p b 2 c - 2)
      (trackBack p b 2 c + 6))
    (z4 : isep2InR Z (U p r + zTokChan p j - 21) (U p r + zTokChan p j + 24)
      (trackBack p b 2 c - 15) (trackBack p b 2 c + 30))
    (z45 : isep2InR Z (U p r + zTokChan p j - 4) (U p r + zTokChan p j + 4)
      (trackBack p b 2 c + 11) (zTokDepth p j - 7))
    (z5 : isep2InR Z (U p r + zTokChan p j - 29) (U p r + zTokChan p j + 16)
      (zTokDepth p j - 18) (zTokDepth p j + 27))
    (z56 : isep2InR Z (U p r + zTokStation j + 9) (U p r + zTokChan p j - 9)
      (zTokDepth p j - 2) (zTokDepth p j + 6))
    (z6 : isep2InR Z (U p r + zTokStation j - 24) (U p r + zTokStation j + 21)
      (zTokDepth p j - 26) (zTokDepth p j + 19)) :
    ∀ k : ℕ, T + k ≤ routeEndX g (ztokCorners p b c H r j) T →
      routeFootX g (ztokCorners p b c H r j) T k ⊆ Z := by
  intro k hk
  have ho := trackOut_par p b 2 c
  have hb := trackBack_par p b 2 c
  have hU := U_even p r
  obtain ⟨-, h2, h3⟩ := zTokChan_parity p 0 r j
  rw [dsepX_ztok_eq] at htim hlin hk ⊢
  have l1 := hlin.1
  refine isep2_rfoot_sub _ _ g T htim hlin ?_ ?_ ?_ ?_ k hk
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by simp, ?_⟩ <;> simp only [CPar, rfCU, rfCV] <;> omega
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;> intro x hx
    · have := isep2_rx_uv (by simp) (by simp only [CPar, rfCU, rfCV]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2] at this
      exact z1 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp) (by simp only [CPar, rfCU, rfCV]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2] at this
      exact z2 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp) (by simp only [CPar, rfCU, rfCV]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2] at this
      exact z3 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp) (by simp only [CPar, rfCU, rfCV]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2] at this
      exact z4 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp) (by simp only [CPar, rfCU, rfCV]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2] at this
      exact z5 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp) (by simp only [CPar, rfCU, rfCV]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2] at this
      exact z6 x (by omega) (by omega) (by omega) (by omega)
  · refine ⟨fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_,
      fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_,
      trivial⟩ <;>
      simp only [Ray, outD, behindIn] at r1 r2 <;>
      obtain ⟨x1, x2, x3, x4⟩ := hx
    · exact z12 x (by omega) (by omega) (by omega) (by omega)
    · exact z23 x (by omega) (by omega) (by omega) (by omega)
    · exact z34 x (by omega) (by omega) (by omega) (by omega)
    · exact z45 x (by omega) (by omega) (by omega) (by omega)
    · exact z56 x (by omega) (by omega) (by omega) (by omega)
  · intro t' _ ht'
    refine isep2_start_of_ray l1 (by simp) (by simp only [CPar, rfCU, rfCV]; omega)
      (fun cu cv r x hx => ?_) t' (by omega)
    simp only [Ray, behindIn] at r
    obtain ⟨x1, x2, x3, x4⟩ := hx
    exact zs x (by omega) (by omega) (by omega)

/-! ### The region of `KZ` -/

/-- **The region of `KZ`**: its loop in sub-band `i + 1` (source column `A_i + 188`, slot `2`),
everything right of its channel (`u ≥ U_r + c_Z - 29`) and the right zone of the module above
`v = 400` (`u ≥ U_r + 1100`). -/
def dsepXKZ (p : Program) (i r : ℕ) : Set Cell :=
  dsepXLoop (A p i + decD) (trackOut p (instrBand i) 2 (A p i + decD))
    (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
    (trackBack p (instrBand i) 2 (A p i + decD)) (U p r + zTokChan p (callerIdx p r i)) ∪
  {x | U p r + zTokChan p (callerIdx p r i) - 29 ≤ x.1 - x.2} ∪
  {x | U p r + 1100 ≤ x.1 - x.2 ∧ 400 ≤ x.1 + x.2}

/-- The layout of the route of `KZ`: hairpin left of the source column and of the channel, the
`BACK` track above the `OUT` track, the depth and the station column. -/
theorem dsepX_kz_layout (hi : p[i]? = some (.decJz r z)) :
    hairKZ p (qOf p (callerIdx p r i)) (A p i + decD) + 40 ≤ A p i + decD ∧
      hairKZ p (qOf p (callerIdx p r i)) (A p i + decD) + 40 ≤
        U p r + zTokChan p (callerIdx p r i) ∧
      trackOut p (instrBand i) 2 (A p i + decD) + 40 ≤
        trackBack p (instrBand i) 2 (A p i + decD) ∧
      1561 ≤ zTokDepth p (callerIdx p r i) ∧
      U p r + 1230 ≤ U p r + zTokStation (callerIdx p r i) ∧
      U p r + zTokStation (callerIdx p r i) + 40 ≤ U p r + zTokChan p (callerIdx p r i) ∧
      U p r + 1410 + 144 * D p ≤ U p r + zTokChan p (callerIdx p r i) ∧
      trackBack p (instrBand i) 2 (A p i + decD) + 30 ≤ -4700 - 198 * D p := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hk := hairReg_le p (s := 2) (e := eKZ (qOf p (callerIdx p r i))) (c := A p i + decD)
    (by norm_num) (eKZ_spec hq).2.1
  have hz := zAnsDepth_eq p (callerIdx p r i)
  have hzc := fixp_bounds (uR p + 124 * qOf p (callerIdx p r i) + 62)
    (1 - zTokDepth p (callerIdx p r i) % 2)
  have hsl := le_max_left (238 : ℤ) (86 + 58 * P p)
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  have hV := lane_VT_low p
  have hil : (i : ℤ) < N p := by
    have := (List.getElem?_eq_some_iff.1 hi).1; unfold N; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold hairKZ decD at *; omega
  · unfold hairKZ zTokChan at *
    simp only [modLeft, slabR, U0, uR] at *; omega
  · simp only [trackOut, trackBack, track]; omega
  · unfold zTokDepth; omega
  · unfold zTokStation; omega
  · unfold zTokChan zTokStation; simp only [uR, qOf] at hzc ⊢; omega
  · unfold zTokChan; simp only [uR, qOf] at hzc ⊢; omega
  · simp only [trackBack, track, instrBand] at hb ⊢; unfold NB at *; omega

/-- **The route of `KZ` lies in its region.** -/
theorem dsepX_kzRoute_sub (hi : p[i]? = some (.decJz r z)) :
    ∀ k : ℕ, 4260 + k ≤ routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 →
      routeFootX (unitWL p i decDWL) (decCornZ p i r) 4260 k ⊆ dsepXKZ p i r := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := dsepX_kz_layout hi
  have hz := zAnsDepth_eq p (callerIdx p r i)
  refine dsepX_ztok_sub p _ _ _ r _ (decKZ_timedX p hi) (decKZ_lines p i r)
    (by unfold hairKZ; exact hairReg_par _ _ _ _) (zTokChan_parity p i r _).1 ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ <;> intro x <;> intros <;>
    simp only [dsepXKZ, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq] <;> omega

/-- The final world line of `KZ` is on the station column `U_r + 1230 + 144 j`, above `v = 650`
until `90` generations before the capture. -/
theorem dsepX_kzFly_sub (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (ht : t ≤ decCapZ p i r - 90) :
    ∀ x ∈ (route (unitWL p i decDWL) (decCornZ p i r)).2.box t,
      U p r + 1226 + 144 * (callerIdx p r i : ℤ) ≤ x.1 - x.2 ∧
      x.1 - x.2 ≤ U p r + 1234 + 144 * (callerIdx p r i : ℤ) ∧ 650 ≤ x.1 + x.2 := by
  have hc := (decCap_cast p hi).2
  have hm := modD_uv p r
  have hU := U_even p r
  have hc90 : 90 ≤ decCapZ p i r := by
    have := (decTS_facts p hi).2.2; unfold decCapZ decTS at *; omega
  intro x hx
  rw [decKZ_target] at hx
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [tokZWL, modWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
  have ht' : (t : ℤ) ≤ decCapZ p i r - 90 := by omega
  refine ⟨by omega, by omega, by omega⟩

/-- **The token `KZ` lies in its region** from `4260` to its capture time. -/
theorem dsepX_tokZ_sub (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (h1 : t ≤ decCapZ p i r) : tokFootZ p i r t ⊆ dsepXKZ p i r := by
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  intro x hx
  unfold tokFootZ at hx
  split_ifs at hx with ha
  · unfold flyFoot at hx
    split_ifs at hx with hb
    · exact dsepX_kzRoute_sub hi (t - 4260) (by omega) hx
    · have := dsepX_kzFly_sub hi ha x hx
      simp only [dsepXKZ, Set.mem_union, Set.mem_ofPred_eq]
      have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
      omega
  · rw [decTokWStartZ_eq hi, Rule.evolve_translate] at hx
    have := dsepM_translate_box (stTokWZ.subset _ (by omega)) hx
    simp only [dsepXKZ, Set.mem_union, Set.mem_ofPred_eq]
    have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
    omega

/-- **The unpaired `KZ` lies in its region** at every generation from `4260`. -/
theorem dsepX_unpZ_sub (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t) :
    unpFootZ p i r t ⊆ dsepXKZ p i r := by
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hc := decCap_cast p hi
  intro x hx
  unfold unpFootZ at hx
  split_ifs at hx with ha hb
  · exact dsepX_tokZ_sub hi h0 ha hx
  · have := dsepM_image_box ((stationZ_unpaired p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapZ p i r) hc.2).subset (t - decCapZ p i r) (by omega) hx)
    simp only [dsepXKZ, Set.mem_union, Set.mem_ofPred_eq]
    have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
    omega
  · exact hx.elim

/-! ### `KZ` after the window of its last band corner -/

/-- **Past a corner window**, the footprint of a route is that of the rest of the route, from
`40` generations after the corner is met. -/
theorem dsepX_rfoot_sub_drop {S : Set Cell} {g : WL} {c : Corner} {cs : List Corner} {T k : ℕ}
    (ht : (T : ℤ) + 20 ≤ meetT g c) (h : meetT g c + 40 < (T : ℤ) + k)
    (hS : ∀ T' k' : ℕ, T' + k' = T + k → (T' : ℤ) = meetT g c + 40 →
      routeEndX g (c :: cs) T = routeEndX (reflect g c).2 cs T' →
      routeFootX (reflect g c).2 cs T' k' ⊆ S) :
    routeFootX g (c :: cs) T k ⊆ S := by
  have e : ((meetT g c).toNat : ℤ) = meetT g c := Int.toNat_of_nonneg (by omega)
  rw [dsepX_rfoot_drop h]
  exact hS _ _ (by omega) (by push_cast; omega) rfl

/-- **In or past a corner window**, the footprint of a route is the extended relay box of the
corner or that of the rest of the route. -/
theorem dsepX_rfoot_sub_after {S : Set Cell} {g : WL} {c : Corner} {cs : List Corner} {T k : ℕ}
    (ht : (T : ℤ) + 20 ≤ meetT g c) (h : meetT g c - 20 < (T : ℤ) + k) (hrel : relayBoxX c ⊆ S)
    (hS : ∀ T' k' : ℕ, T' + k' = T + k → (T' : ℤ) = meetT g c + 40 →
      routeEndX g (c :: cs) T = routeEndX (reflect g c).2 cs T' →
      routeFootX (reflect g c).2 cs T' k' ⊆ S) :
    routeFootX g (c :: cs) T k ⊆ S := by
  by_cases h2 : meetT g c + 40 < (T : ℤ) + k
  · exact dsepX_rfoot_sub_drop ht h2 hS
  · rw [routeFootX]
    simp only [show ¬ ((T : ℤ) + k ≤ meetT g c - 20) by omega,
      show (T : ℤ) + k ≤ meetT g c + 40 by omega, ↓reduceIte]
    exact hrel

/-- **The meeting time of the last band corner of a Z token link**, from the final world line. -/
theorem dsepX_ztok_meet4 (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0)
    (hd : (U p r + zTokChan p j - c) % 2 = 0) :
    meetT (reflect (reflect (reflect g ⟨3, c, trackOut p b 2 c, .band b 2 false⟩).2
      ⟨7, H, trackOut p b 2 c, .band b 2 true⟩).2 ⟨4, H, trackBack p b 2 c, .band b 7 true⟩).2
      ⟨2, U p r + zTokChan p j, trackBack p b 2 c, .band b 7 false⟩ +
      2 * (U p r + zTokChan p j) + 4 * zTokDepth p j =
      (route g (ztokCorners p b c H r j)).2.tau + 2 * trackBack p b 2 c + 3 := by
  rw [ztokCorners_final p b c H r j hdx hdy hl hH hd]
  have ho := trackOut_par p b 2 c
  have hb := trackBack_par p b 2 c
  have hU := U_even p r
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl
  subst hdx hdy hl
  simp only [reflect, meetT, delayS, WL.shift, rfIn, rfOut, rfX, rfY, rfCU, rfCV]
  generalize trackOut p b 2 lane = O at *
  generalize trackBack p b 2 lane = B at *
  generalize zTokChan p j = cz at *
  omega

/-- **`KZ` meets its last band corner before the NZ answer is dispatched** (`20` generations
before the dispatch at the latest). -/
theorem dsepX_kz_meet4_le (hi : p[i]? = some (.decJz r z)) :
    meetT (reflect (reflect (reflect (unitWL p i decDWL)
      ⟨3, A p i + decD, trackOut p (instrBand i) 2 (A p i + decD), .band (instrBand i) 2 false⟩).2
      ⟨7, hairKZ p (qOf p (callerIdx p r i)) (A p i + decD),
        trackOut p (instrBand i) 2 (A p i + decD), .band (instrBand i) 2 true⟩).2
      ⟨4, hairKZ p (qOf p (callerIdx p r i)) (A p i + decD),
        trackBack p (instrBand i) 2 (A p i + decD), .band (instrBand i) 7 true⟩).2
      ⟨2, U p r + zTokChan p (callerIdx p r i), trackBack p (instrBand i) 2 (A p i + decD),
        .band (instrBand i) 7 false⟩ ≤ (decDispN p i r : ℤ) - 20 := by
  obtain ⟨h1, h2, h3⟩ := unitWL_dec_lane p i 188 787
  have e := dsepX_ztok_meet4 p (instrBand i) (A p i + decD)
    (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD)) r (callerIdx p r i) h1 h2 h3
    (by unfold hairKZ; exact hairReg_par _ _ _ _) (zTokChan_parity p i r _).1
  have ht := decKZ_target p i r
  rw [decCornZ] at ht
  rw [show (⟨1, 1, 188, 787⟩ : WL) = decDWL from rfl, ht] at e
  obtain ⟨-, -, -, l4, -, -, l7, l8⟩ := dsepX_kz_layout hi
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have hm := modD_uv p r
  have hU := U_even p r
  have hj := dsepM_j_lt hi
  simp only [tokZWL, modWL, WL.shift, modDX] at e
  simp only [decDispN]
  push_cast
  omega

/-- **After a corner window, a route with corners right of `M + 70` stays at `u ≥ M`**, when the
corner is right of `M + 70` too. -/
theorem dsepX_ulow_after (M : ℤ) {g : WL} {c : Corner} {cs : List Corner} {T' : ℕ}
    (hT' : (T' : ℤ) = meetT g c + 40) (hts : RouteTimedX (reflect g c).2 cs (meetT g c + 40))
    (hls : RouteLines (reflect g c).2 cs) (hcs : ∀ c' ∈ cs, M + 70 ≤ c'.u) (hc : M + 70 ≤ c.u) :
    ∀ k : ℕ, T' + k ≤ routeEndX (reflect g c).2 cs T' →
      routeFootX (reflect g c).2 cs T' k ⊆ {x | M ≤ x.1 - x.2} := by
  have h40 := (dsepX_u_out40 g c).2
  intro k hk x hx
  exact (dsepX_route_ulow M cs _ _ (reflect_dir g c) hls (by rw [hT']; exact hts) hcs
    (by rw [hT']; omega)).1 k hk x hx

/-- **After the dispatch of the NZ answer, the route of `KZ` is right of `u = U_r + 1150`**: it is
in the window of its last band corner (at the channel `U_r + c_Z`) or after it. -/
theorem dsepX_kzRoute_late (hi : p[i]? = some (.decJz r z)) {k : ℕ}
    (hk : 4260 + k ≤ routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260)
    (hlate : decDispN p i r < 4260 + k) :
    routeFootX (unitWL p i decDWL) (decCornZ p i r) 4260 k ⊆
      {x | U p r + 1150 ≤ x.1 - x.2} := by
  have hm4 := dsepX_kz_meet4_le hi
  obtain ⟨-, -, -, -, l5, -, l7, -⟩ := dsepX_kz_layout hi
  have hj := dsepM_j_lt hi
  have htim := decKZ_timedX p hi
  have hlin := decKZ_lines p i r
  unfold decCornZ at htim hlin hk ⊢
  rw [dsepX_ztok_eq] at htim hlin hk ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := htim
  obtain ⟨-, -, -, -, b5, b6, -⟩ := hlin
  refine dsepX_rfoot_sub_drop (by push_cast; omega) (by push_cast; omega)
    fun T1 k1 e1 c1 r1 => ?_
  refine dsepX_rfoot_sub_drop (by rw [c1]; omega) (by rw [c1]; omega)
    fun T2 k2 e2 c2 r2 => ?_
  refine dsepX_rfoot_sub_drop (by rw [c2]; omega) (by rw [c2]; omega)
    fun T3 k3 e3 c3 r3 => ?_
  refine dsepX_rfoot_sub_after (by rw [c3]; omega) (by omega)
    (fun x hx => ?_) fun T4 k4 e4 c4 r4 => ?_
  · have := dsepX_relay_u hx
    simp only [Set.mem_ofPred_eq] at this ⊢
    omega
  · rw [r1, r2, r3, r4] at hk
    refine dsepX_ulow_after (U p r + 1150) (cs := _ :: _ :: []) c4 ⟨a5, a6, trivial⟩
      ⟨b5, b6, trivial⟩ (fun c hc => ?_) (by simp only; omega) _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp only <;> omega

/-- **After the dispatch of the NZ answer, the unpaired `KZ` is right of `u = U_r + 1150`.** -/
theorem dsepX_unpZ_late (hi : p[i]? = some (.decJz r z)) {t : ℕ} (ht : decDispN p i r < t) :
    unpFootZ p i r t ⊆ {x | U p r + 1150 ≤ x.1 - x.2} := by
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hc := decCap_cast p hi
  have h0 : 4260 ≤ t := by
    have := (decTS_facts p hi).2.2; unfold decDispN decTS at ht; omega
  intro x hx
  simp only [Set.mem_ofPred_eq]
  have hj0 : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
  unfold unpFootZ at hx
  split_ifs at hx with ha hb
  · unfold tokFootZ at hx
    split_ifs at hx with hc1
    · unfold flyFoot at hx
      split_ifs at hx with hd
      · exact dsepX_kzRoute_late hi (k := t - 4260) (by omega) (by omega) hx
      · have := dsepX_kzFly_sub hi hc1 x hx
        omega
    · rw [decTokWStartZ_eq hi, Rule.evolve_translate] at hx
      have := dsepM_translate_box (stTokWZ.subset _ (by omega)) hx
      omega
  · have := dsepM_image_box ((stationZ_unpaired p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapZ p i r) hc.2).subset (t - decCapZ p i r) (by omega) hx)
    omega
  · exact hx.elim

end LP

end LeanTheory.Life
