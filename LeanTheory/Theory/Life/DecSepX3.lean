/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepX2

/-!
# The control `C` and the token `KNZ` of a `decJz` activation in regions

Research note `N-22`. For the fields `nThr` and `zThr` of `DecSep`:

* `dsepXC`: the region of the control `C` before the register run (its loop in sub-band
  `i + 1`, slot `1`, and the left-low part of the module: the channel, the port line, the DEC
  chain and the flight of `C'`); `dsepX_footC_sub`;
* `dsepXN`: the region of `KNZ` (its loop, slot `0`, its channel, its port line and station
  `j` of the line NZ); `dsepX_tokN_sub`, `dsepX_unpN_sub`;
* the three loops are nested (`KNZ ⊃ C ⊃ KZ`): `dsepX_C_KZ`, `dsepX_N_KZ`, `dsepX_N_C`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The region of `C` -/

/-- **The region of the control `C`** before the register run: its loop in sub-band `i + 1`
(source column `A_i + 127`, slot `1`) and the left-low part of the module (`u` from the channel
of DEC copy `2 j` to `U_r + 60 D + 300`, `v ≤ -2350`). -/
def dsepXC (p : Program) (i r : ℕ) : Set Cell :=
  dsepXLoop (A p i + decR) (trackOut p (instrBand i) 1 (A p i + decR))
    (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
    (trackBack p (instrBand i) 1 (A p i + decR)) (U p r + decChan p (2 * (callerIdx p r i))) ∪
  {x | U p r + decChan p (2 * (callerIdx p r i)) - 27 ≤ x.1 - x.2 ∧
    x.1 - x.2 ≤ U p r + 60 * D p + 300 ∧ trackBack p (instrBand i) 1 (A p i + decR) - 19 ≤
      x.1 + x.2 ∧ x.1 + x.2 ≤ -2350}

/-- The layout of the route of `C`. -/
theorem dsepX_c_layout (hi : p[i]? = some (.decJz r z)) :
    hairC p (qOf p (callerIdx p r i)) (A p i + decR) + 40 ≤ A p i + decR ∧
      hairC p (qOf p (callerIdx p r i)) (A p i + decR) + 40 ≤
        U p r + decChan p (2 * (callerIdx p r i)) ∧
      trackOut p (instrBand i) 1 (A p i + decR) + 40 ≤
        trackBack p (instrBand i) 1 (A p i + decR) ∧
      trackBack p (instrBand i) 1 (A p i + decR) + 40 ≤ decPortV p (2 * (callerIdx p r i)) ∧
      decPortV p (2 * (callerIdx p r i)) + 26 ≤ -3300 ∧
      -3353 - 198 * D p ≤ decPortV p (2 * (callerIdx p r i)) ∧
      U p r + decChan p (2 * (callerIdx p r i)) ≤ U p r - 793 ∧
      U p r + modLeft p ≤ U p r + decChan p (2 * (callerIdx p r i)) ∧
      trackBack p (instrBand i) 1 (A p i + decR) + 30 ≤ -4700 - 198 * D p := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hH := hairC_le p hq (A p i + decR)
  have hcl := leftChan_in_extent p (idx := 2 * (callerIdx p r i))
    (v := decPortV p (2 * (callerIdx p r i))) ⟨by omega, by omega⟩
  have hsl := slabR_ge p
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  have hf := layout_facts p
  have hR : decR = 127 := rfl
  have hV := lane_VT_low p
  have hil : (i : ℤ) < N p := by
    have := (List.getElem?_eq_some_iff.1 hi).1; unfold N; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · unfold decChan; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, decPortV, modTop, instrBand] at h3 hb ⊢; omega
  · unfold decPortV; omega
  · unfold decPortV; omega
  · unfold decChan uL at *; omega
  · unfold decChan at *; omega
  · simp only [trackBack, track, instrBand] at hb ⊢; unfold NB at *; omega

/-- **The route of `C` lies in its region.** -/
theorem dsepX_cRoute_sub (hi : p[i]? = some (.decJz r z)) :
    ∀ k : ℕ, 4260 + k ≤ routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 →
      routeFootX (unitWL p i decRWL) (decCornC p i r) 4260 k ⊆ dsepXC p i r := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := dsepX_c_layout hi
  have hp := decChan_parity p i r (callerIdx p r i)
  have hU := U_even p r
  have hD := one_le_D p
  refine isep2_down_sub p _ _ _ _ _ _ r _ (decC_timedX p hi) (decC_lines p i r).1
    (by unfold hairC; have := fixp_parity (HI p + 90 - 2 * eCtot (qOf p ↑(callerIdx p r i)))
          ((A p ↑i + decR) % 2); omega) hp.1 (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    intro x <;> intros <;> simp only [dsepXC, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq] <;>
    omega

/-- **The flight of `C` on the port line of DEC copy `m`** (from the end of its route to `20`
generations before the side input) lies in its region: `u` from `11` right of the channel to
`U_r + 37 + 29 m`, on the port line. -/
theorem dsepX_cFly_sub (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ≤ t) (h2 : t ≤ decTA p i r - 20) :
    (decGC p i r).box t ⊆ dsepXC p i r := by
  obtain ⟨-, -, -, l4, l5, l6, l7, l8, l9⟩ := dsepX_c_layout hi
  have hu := modD_uv p r
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  have hUe := U_even p r
  have hD := one_le_D p
  obtain ⟨-, hA20, hTA⟩ := decTA_facts p hi
  have hs := sigma_cases (qOf p (callerIdx p r i))
  have hp := decChan_parity p i r (callerIdx p r i)
  have he := routeEndX_snoc (bandCorners p (instrBand i) 1 (A p i + decR)
    (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
    (U p r + decChan p (2 * (callerIdx p r i))) 3 2) ⟨4, U p r + decChan p (2 * (callerIdx p r i)),
    decPortV p (2 * (callerIdx p r i)), .left r (2 * (callerIdx p r i))⟩ (unitWL p i decRWL) 4260
    (decC_timedX p hi)
  change (routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 : ℤ) =
    (decGC p i r).tau - _ + _ - _ at he
  intro x hx
  have hx' := hx
  obtain ⟨x1, x2, x3, x4⟩ := hx
  rw [decC_window] at x1 x2 x3 x4
  simp only [decWin, modWL, WL.shift, WL.px, WL.py, WL.qt, modDX, modDY] at x1 x2 x3 x4 hu
  obtain ⟨y1, y2, y3, y4⟩ := hx'
  rw [decGC_eq] at y1 y2 y3 y4 he
  simp only [WL.px, WL.py, WL.qt, rfOut, rfX, rfCU, rfCV] at y1 y2 y3 y4 he
  simp only [dsepXC, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq]
  right
  omega

/-- **The control `C` lies in its region** from `4260` to the start of the register run. -/
theorem dsepX_footC_sub (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t ≤ decTS p i r) : decFootC p i r t ⊆ dsepXC p i r := by
  obtain ⟨-, -, -, l4, l5, l6, l7, l8, l9⟩ := dsepX_c_layout hi
  have hu := modD_uv p r
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  have hD := one_le_D p
  intro x hx
  unfold decFootC at hx
  split_ifs at hx with ha hb hc
  · unfold flyFoot at hx
    split_ifs at hx with hd
    · exact dsepX_cRoute_sub hi (t - 4260) (by omega) hx
    · exact dsepX_cFly_sub hi (by omega) ha hx
  · obtain ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩ := hx
    simp only [dsepXC, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
    right
    omega
  · obtain ⟨d, ⟨j, hj', d1, d2, d3, d4⟩, rfl⟩ := hx
    rw [show chainV = (35, 64) from rfl] at d1 d2 d3 d4
    have : (j : ℤ) ≤ (decM p i r : ℤ) := by omega
    simp only [dsepXC, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
    right
    omega
  · obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    have e1 : decTS p i r = decTB p i r + 1771 := by unfold decTS decTB; omega
    simp only [cp0WL, WL.px, WL.py, WL.qt] at *
    simp only [dsepXC, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
    right
    omega

/-! ### The region of `KNZ` -/

/-- **The region of the token `KNZ`**: its loop in sub-band `i + 1` (source column `A_i - 155`,
slot `0`), its channel up from its `BACK` track, and its port line and station `j` of the line
NZ (`u ≤ U_r - 300`, `v ≥ 1150`). -/
def dsepXN (p : Program) (i r : ℕ) : Set Cell :=
  dsepXLoop (A p i + decL) (trackOut p (instrBand i) 0 (A p i + decL))
    (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
    (trackBack p (instrBand i) 0 (A p i + decL)) (U p r + nzTokChan p (callerIdx p r i)) ∪
  {x | U p r + nzTokChan p (callerIdx p r i) - 21 ≤ x.1 - x.2 ∧
    x.1 - x.2 ≤ U p r + nzTokChan p (callerIdx p r i) + 28 ∧
    trackBack p (instrBand i) 0 (A p i + decL) - 19 ≤ x.1 + x.2} ∪
  {x | U p r + nzTokChan p (callerIdx p r i) - 21 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r - 300 ∧
    1150 ≤ x.1 + x.2}

/-- The layout of the route of `KNZ`. -/
theorem dsepX_n_layout (hi : p[i]? = some (.decJz r z)) :
    hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL) + 40 ≤ A p i + decL ∧
      hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL) + 40 ≤
        U p r + nzTokChan p (callerIdx p r i) ∧
      trackOut p (instrBand i) 0 (A p i + decL) + 40 ≤
        trackBack p (instrBand i) 0 (A p i + decL) ∧
      trackBack p (instrBand i) 0 (A p i + decL) + 40 ≤ nzTokPortV (callerIdx p r i) ∧
      U p r + nzTokChan p (callerIdx p r i) + 186 ≤ U p r - 793 ∧
      U p r + modLeft p ≤ U p r + nzTokChan p (callerIdx p r i) ∧
      trackBack p (instrBand i) 0 (A p i + decL) + 30 ≤ -4700 - 198 * D p := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hH := hairC_le p hq (A p i + decR)
  have hK := hairKNZ_le p hq (A p i + decR) (A p i + decL)
  have hcl := leftChan_in_extent p (idx := 2 * D p + 1 + 2 * (callerIdx p r i))
    (v := nzTokPortV (callerIdx p r i)) ⟨by omega, by omega⟩
  have hfx := fixp_bounds (uL - 62 * (2 * D p + 1 + 2 * (callerIdx p r i)))
    (1 - nzTokPortV (callerIdx p r i) % 2)
  have hsl := slabR_ge p
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  have hf := layout_facts p
  have hL : decL = -155 := rfl
  have hR : decR = 127 := rfl
  have hV := lane_VT_low p
  have hil : (i : ℤ) < N p := by
    have := (List.getElem?_eq_some_iff.1 hi).1; unfold N; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold slabL at hf; omega
  · unfold nzTokChan; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, nzTokPortV, modTop, instrBand] at h3 hb ⊢; omega
  · unfold nzTokChan leftChan uL at *; omega
  · unfold nzTokChan at *; omega
  · simp only [trackBack, track, instrBand] at hb ⊢; unfold NB at *; omega

/-- **The route of `KNZ` lies in its region.** -/
theorem dsepX_nRoute_sub (hi : p[i]? = some (.decJz r z)) :
    ∀ k : ℕ, 4260 + k ≤ routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 →
      routeFootX (unitWL p i decLWL) (decCornN p i r) 4260 k ⊆ dsepXN p i r := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := dsepX_n_layout hi
  have hp := nzTokChan_parity p i r (callerIdx p r i)
  have hU := U_even p r
  refine isep2_down_sub p _ _ _ _ _ _ r _ (decKNZ_timedX p hi) (decKNZ_lines p i r).1
    (by unfold hairKNZ; have := fixp_parity (hairC p (qOf p ↑(callerIdx p r i)) (A p ↑i + decR)
          - 62 - 2 * eN (qOf p ↑(callerIdx p r i))) ((A p ↑i + decL) % 2); omega)
    hp.1 (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    intro x <;> intros <;> simp only [dsepXN, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq] <;>
    omega

/-- **The flight of `KNZ` on its port line** (from the end of its route to `90` generations before
the capture) lies in its region. -/
theorem dsepX_nFly_sub (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ≤ t)
    (h2 : t ≤ decCapN p i r - 90) :
    (route (unitWL p i decLWL) (decCornN p i r)).2.box t ⊆
      {x | U p r + nzTokChan p (callerIdx p r i) - 21 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r - 300 ∧
        1150 ≤ x.1 + x.2} := by
  obtain ⟨-, -, -, l4, l5, l6, l7⟩ := dsepX_n_layout hi
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hUe := U_even p r
  have hc := (decCap_cast p hi).1
  have hc90 : 90 ≤ decCapN p i r := by
    have := (decTS_facts p hi).2.2; unfold decCapN decTS at *; omega
  have hp := nzTokChan_parity p i r (callerIdx p r i)
  have he := routeEndX_snoc (bandCorners p (instrBand i) 0 (A p i + decL)
    (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
    (U p r + nzTokChan p (callerIdx p r i)) 3 2) ⟨4, U p r + nzTokChan p (callerIdx p r i),
    nzTokPortV (callerIdx p r i), .left r (2 * D p + 1 + 2 * (callerIdx p r i))⟩
    (unitWL p i decLWL) 4260 (decKNZ_timedX p hi)
  change (routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 : ℤ) =
    (route (unitWL p i decLWL) (decCornN p i r)).2.tau - _ + _ - _ at he
  rw [decKNZ_target] at he ⊢
  intro x hx
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [tokNZWL, modWL, WL.shift, WL.px, WL.py, WL.qt, rfOut, rfX, rfCU, rfCV,
    nzTokPortV, modDX, modDY] at x1 x2 x3 x4 he
  have h2' : (t : ℤ) ≤ decCapN p i r - 90 := by omega
  simp only [Set.mem_ofPred_eq]
  simp only [nzTokPortV] at hp
  omega

/-- **The token `KNZ` lies in its region** from `4260` to its capture time. -/
theorem dsepX_tokN_sub (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (h1 : t ≤ decCapN p i r) : tokFootN p i r t ⊆ dsepXN p i r := by
  obtain ⟨-, -, -, l4, l5, l6, l7⟩ := dsepX_n_layout hi
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  intro x hx
  unfold tokFootN at hx
  split_ifs at hx with ha
  · unfold flyFoot at hx
    split_ifs at hx with hb
    · exact dsepX_nRoute_sub hi (t - 4260) (by omega) hx
    · exact Or.inr (dsepX_nFly_sub hi (by omega) ha hx)
  · rw [decTokWStartN_eq hi, Rule.evolve_translate] at hx
    have := dsepM_translate_box (stTokWNZ.subset _ (by omega)) hx
    simp only [dsepXN, Set.mem_union, Set.mem_ofPred_eq]
    have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
    omega

/-- **The unpaired `KNZ` lies in its region** at every generation from `4260`. -/
theorem dsepX_unpN_sub (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t) :
    unpFootN p i r t ⊆ dsepXN p i r := by
  obtain ⟨-, -, -, l4, l5, l6, l7⟩ := dsepX_n_layout hi
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hc := decCap_cast p hi
  intro x hx
  unfold unpFootN at hx
  split_ifs at hx with ha hb
  · exact dsepX_tokN_sub hi h0 ha hx
  · have := dsepM_image_box ((stationNZ_unpaired p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapN p i r) hc.1).subset (t - decCapN p i r) (by omega) hx)
    simp only [dsepXN, Set.mem_union, Set.mem_ofPred_eq]
    have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
    omega
  · exact hx.elim

/-! ### The loops are nested -/

/-- The facts of the three loops of a `decJz` activation: source columns, tracks, hairpins and
channels. -/
theorem dsepX_loops (hi : p[i]? = some (.decJz r z)) :
    hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL) + 62 ≤
        hairC p (qOf p (callerIdx p r i)) (A p i + decR) ∧
      hairC p (qOf p (callerIdx p r i)) (A p i + decR) + 61 ≤
        hairKZ p (qOf p (callerIdx p r i)) (A p i + decD) ∧
      trackOut p (instrBand i) 0 (A p i + decL) + 61 ≤ trackOut p (instrBand i) 1 (A p i + decR) ∧
      trackOut p (instrBand i) 1 (A p i + decR) + 61 ≤ trackOut p (instrBand i) 2 (A p i + decD) ∧
      trackBack p (instrBand i) 2 (A p i + decD) + 61 ≤ trackBack p (instrBand i) 1 (A p i + decR) ∧
      trackBack p (instrBand i) 1 (A p i + decR) + 61 ≤
        trackBack p (instrBand i) 0 (A p i + decL) ∧
      U p r + nzTokChan p (callerIdx p r i) + 61 ≤ U p r + decChan p (2 * (callerIdx p r i)) ∧
      decL + 282 = decR ∧ decR + 61 = decD := by
  have hj := dsepM_j_lt hi
  have hD := one_le_D p
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have h9 := sep09_decJz p (cN := A p i + decL) (cC := A p i + decR) (cZ := A p i + decD)
    (cA := 0) (cB := 0) (eA := 0) (eB := 0) hq (by omega) (by omega)
  have hK := hairKNZ_le p hq (A p i + decR) (A p i + decL)
  have hd1 : nzTokChan p (callerIdx p r i) + 61 ≤ decChan p (2 * (callerIdx p r i)) :=
    sep11_leftChan (by omega)
  refine ⟨hK, h9.2.1, ?_, ?_, ?_, ?_, by omega, rfl, rfl⟩ <;>
    simp only [trackOut, trackBack, track, decL, decR, decD] <;> omega

/-- The units are left of the module: `A_i + 358 ≤ U_r + modLeft`. -/
theorem dsepX_AU (hi : p[i]? = some (.decJz r z)) :
    A p i + 358 ≤ U p r + modLeft p ∧ modLeft p = -823 - 248 * D p := by
  have hil : (i : ℤ) < N p := by
    have := (List.getElem?_eq_some_iff.1 hi).1; unfold N; omega
  have hR := one_le_R p
  have h := unit_module_gap p (a := i) (r := r) ⟨by omega, by omega⟩ (by omega)
  have hs := slabR_ge_rs p
  exact ⟨by omega, rfl⟩

/-- **The region of `C` is far from the region of `KZ`** (`C ⊃ KZ`). -/
theorem dsepX_C_KZ (hi : p[i]? = some (.decJz r z)) :
    FarApart 2 (dsepXC p i r) (dsepXKZ p i r) := by
  obtain ⟨-, -, -, -, -, -, l7, -, l9⟩ := dsepX_c_layout hi
  obtain ⟨k1, k2, k3, -, -, -, k7, k8⟩ := dsepX_kz_layout hi
  obtain ⟨-, h2, -, o2, b2, -, -, -, d2⟩ := dsepX_loops hi
  have hAU := dsepX_AU hi
  have hD := one_le_D p
  have hvals : decL = -155 ∧ decR = 127 ∧ decD = 188 := ⟨rfl, rfl, rfl⟩
  refine dsepT_far_cells fun a ha b hb => ?_
  simp only [dsepXC, dsepXKZ, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq] at ha hb
  rcases ha with (ha | ha | ha | ha) | ha <;> rcases hb with ((hb | hb | hb | hb) | hb) | hb <;>
    omega

/-- **The region of `KNZ` is far from the region of `KZ`** (`KNZ ⊃ KZ`). -/
theorem dsepX_N_KZ (hi : p[i]? = some (.decJz r z)) :
    FarApart 2 (dsepXN p i r) (dsepXKZ p i r) := by
  obtain ⟨-, -, -, -, n5, -, n7⟩ := dsepX_n_layout hi
  obtain ⟨k1, k2, k3, -, -, -, k7, k8⟩ := dsepX_kz_layout hi
  obtain ⟨h1, h2, o1, o2, b2, b1, -, d1, d2⟩ := dsepX_loops hi
  have hAU := dsepX_AU hi
  have hD := one_le_D p
  have hvals : decL = -155 ∧ decR = 127 ∧ decD = 188 := ⟨rfl, rfl, rfl⟩
  refine dsepT_far_cells fun a ha b hb => ?_
  simp only [dsepXN, dsepXKZ, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq] at ha hb
  rcases ha with ((ha | ha | ha | ha) | ha) | ha <;>
    rcases hb with ((hb | hb | hb | hb) | hb) | hb <;> omega

/-- **The region of `KNZ` is far from the region of `C`** (`KNZ ⊃ C`). -/
theorem dsepX_N_C (hi : p[i]? = some (.decJz r z)) :
    FarApart 2 (dsepXN p i r) (dsepXC p i r) := by
  obtain ⟨-, -, -, -, n5, -, n7⟩ := dsepX_n_layout hi
  obtain ⟨c1, c2, c3, c4, -, -, c7, -, c9⟩ := dsepX_c_layout hi
  obtain ⟨h1, h2, o1, o2, b2, b1, dd, d1, d2⟩ := dsepX_loops hi
  have hAU := dsepX_AU hi
  have hD := one_le_D p
  have hvals : decL = -155 ∧ decR = 127 ∧ decD = 188 := ⟨rfl, rfl, rfl⟩
  refine dsepT_far_cells fun a ha b hb => ?_
  simp only [dsepXN, dsepXC, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq] at ha hb
  rcases ha with ((ha | ha | ha | ha) | ha) | ha <;> rcases hb with (hb | hb | hb | hb) | hb <;>
    omega

/-! ### The module parts of the main threads -/

/-- **The module part of an NZ thread**: `u ∈ [U_r - 760, U_r + 830]`, `v ≥ -2420`. -/
def dsepXMR (p : Program) (r : ℕ) : Set Cell :=
  {x | U p r - 760 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + 830 ∧ -2420 ≤ x.1 + x.2}

/-- **The module part of a Z thread**: `u ≥ U_r - 760`, `v ≥ -2420`, and below `v = 730` or
right of `u = U_r - 113`. -/
def dsepXMZ (p : Program) (r : ℕ) : Set Cell :=
  {x | U p r - 760 ≤ x.1 - x.2 ∧ -2420 ≤ x.1 + x.2 ∧
    (x.1 + x.2 ≤ 730 ∨ U p r - 113 ≤ x.1 - x.2)}

/-- The module part of an NZ thread is far from the region of `KZ`. -/
theorem dsepX_MR_KZ (hi : p[i]? = some (.decJz r z)) :
    FarApart 2 (dsepXMR p r) (dsepXKZ p i r) := by
  obtain ⟨-, -, k3, -, -, -, k7, k8⟩ := dsepX_kz_layout hi
  have hD := one_le_D p
  refine dsepT_far_cells fun a ha b hb => ?_
  simp only [dsepXMR, dsepXKZ, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq] at ha hb
  rcases hb with ((hb | hb | hb | hb) | hb) | hb <;> omega

/-- The module part of a Z thread is far from the region of `KNZ`. -/
theorem dsepX_MZ_N (hi : p[i]? = some (.decJz r z)) :
    FarApart 2 (dsepXMZ p r) (dsepXN p i r) := by
  obtain ⟨-, -, n3, -, n5, -, n7⟩ := dsepX_n_layout hi
  have hD := one_le_D p
  refine dsepT_far_cells fun a ha b hb => ?_
  simp only [dsepXMZ, dsepXN, dsepXLoop, Set.mem_union, Set.mem_ofPred_eq] at ha hb
  rcases hb with ((hb | hb | hb | hb) | hb) | hb <;> omega

end LP

end LeanTheory.Life
