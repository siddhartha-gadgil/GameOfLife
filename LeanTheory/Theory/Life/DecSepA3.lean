/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepA2

/-!
# The footprints of the control and of the tokens of a `decJz` activation

Research note `N-22`. The numbers of the layout of a `decJz` activation (`dsepA_lay`: the tracks of
the three links in their sub-band, the channels and port lines, the hairpins, the right-zone corners
of `KZ`) and the hulls of the moving footprints before the capture:

* `dsepA_footC_hull`: the control (`decFootC`) up to the register run: the region of its route, then
  `u ≥ cd_C + 9`, `v ∈ [vp_C - 90, -2300]` (the port line, the DEC chain and the flight of `C'`);
* `dsepA_tokN_hull`: `KNZ` up to its capture: the region of its route, the flight on its port line
  (`u ≤ U_r - 520`) and the joint approach with its station (`dsepA_winN_foot`);
* `dsepA_tokZ_hull`: `KZ` up to its capture: the region of its route, the flight on its station
  column and the joint approach with its station (`dsepA_winZ_foot`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The numbers of the layout -/

/-- **The numbers of the layout of a `decJz` activation.** -/
theorem dsepA_lay (hi : p[i]? = some (.decJz r z)) :
    trackOut p (instrBand i) 0 (A p i + decL) = VT p + 660 * instrBand i ∧
    trackBack p (instrBand i) 0 (A p i + decL) = VT p + 660 * instrBand i + 558 ∧
    trackOut p (instrBand i) 1 (A p i + decR) = VT p + 660 * instrBand i + 62 ∧
    trackBack p (instrBand i) 1 (A p i + decR) = VT p + 660 * instrBand i + 496 ∧
    trackOut p (instrBand i) 2 (A p i + decD) = VT p + 660 * instrBand i + 125 ∧
    trackBack p (instrBand i) 2 (A p i + decD) = VT p + 660 * instrBand i + 435 ∧
    U p r + nzTokChan p (callerIdx p r i) =
      U p r - 855 - 124 * D p - 124 * ((callerIdx p r i : ℕ) : ℤ) ∧
    U p r + decChan p (2 * (callerIdx p r i)) = U p r - 793 - 124 * ((callerIdx p r i : ℕ) : ℤ) ∧
    decPortV p (2 * (callerIdx p r i)) = -3252 - 198 * D p + 198 * ((callerIdx p r i : ℕ) : ℤ) ∧
    nzTokPortV (callerIdx p r i) = 1256 + 144 * ((callerIdx p r i : ℕ) : ℤ) ∧
    hairC p (qOf p (callerIdx p r i)) (A p i + decR) ≤ HI p + 90 ∧
    hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL) + 62 ≤
      hairC p (qOf p (callerIdx p r i)) (A p i + decR) ∧
    HI p + 151 ≤ hairKZ p (qOf p (callerIdx p r i)) (A p i + decD) ∧
    hairKZ p (qOf p (callerIdx p r i)) (A p i + decD) ≤ HI p + 180 ∧
    U p r + 1471 + 144 * D p + 124 * (D p - 1 - ((callerIdx p r i : ℕ) : ℤ)) ≤
      U p r + zTokChan p (callerIdx p r i) ∧
    U p r + zTokChan p (callerIdx p r i) ≤
      U p r + 1472 + 144 * D p + 124 * (D p - 1 - ((callerIdx p r i : ℕ) : ℤ)) ∧
    zTokDepth p (callerIdx p r i) = 1561 + 180 * (D p - 1 - ((callerIdx p r i : ℕ) : ℤ)) ∧
    U p r + zTokStation (callerIdx p r i) = U p r + 1230 + 144 * ((callerIdx p r i : ℕ) : ℤ) ∧
    0 ≤ ((callerIdx p r i : ℕ) : ℤ) ∧ ((callerIdx p r i : ℕ) : ℤ) < D p ∧ 1 ≤ D p ∧
    0 ≤ A p i ∧ HI p ≤ -716 - 122 * P p ∧ 1 ≤ P p ∧ A p i + 358 ≤ U p r - 823 - 248 * D p ∧
    VT p + 660 * instrBand i + 1320 ≤ -3444 - 198 * D p ∧
    VT p + 660 ≤ VT p + 660 * instrBand i ∧ VU p = VT p - 1644 ∧
    modDX p r - modDY p r = U p r ∧ modDX p r + modDY p r = 0 := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  have hAm := A_mod p i
  have hUm := U_mod p r
  have hu := modD_uv p r
  have hsl := slabR_ge p
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have h6 := (sep06_units_module0 p (a := i) (by
    have := one_le_R p; unfold N; omega)).1
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hC := hairC_le p hq (A p i + decR)
  have hN := hairKNZ_le p hq (A p i + decR) (A p i + decL)
  have hKZ := eKZ_spec hq
  have hzd := zAnsDepth_eq p (callerIdx p r i)
  have hfz := fixp_bounds (uR p + 124 * qOf p (callerIdx p r i) + 62)
    (1 - zTokDepth p (callerIdx p r i) % 2)
  have hfk := fixp_bounds (HI p + 90 * 2 - 2 * eKZ (qOf p (callerIdx p r i)))
    ((A p i + decD) % 2)
  have hR := one_le_R p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, hC, hN, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hj,
    hD, hA, hHI, hP, ?_, ?_, ?_, rfl, hu.1, hu.2⟩
  · simp only [trackOut, track, decL]; omega
  · simp only [trackBack, track, decL]; omega
  · simp only [trackOut, track, decR]; omega
  · simp only [trackBack, track, decR]; omega
  · simp only [trackOut, track, decD]; omega
  · simp only [trackBack, track, decD]; omega
  · simp only [nzTokChan, leftChan, fixp, uL, nzTokPortV]; omega
  · simp only [decChan, leftChan, fixp, uL, decPortV]; omega
  · simp only [decPortV]; omega
  · unfold hairKZ hairReg at *; omega
  · unfold hairKZ hairReg at *; omega
  · unfold zTokChan at *; simp only [uR, qOf] at hfz ⊢; omega
  · unfold zTokChan at *; simp only [uR, qOf] at hfz ⊢; omega
  · unfold zTokDepth; rw [hzd]; simp only [qOf]; ring
  · simp only [zTokStation]; ring
  · simp only [modLeft] at hU2 h6; omega
  · simp only [NB, N, R, instrBand, modTop] at h3 hb hR ⊢; omega
  · simp only [instrBand]; omega

/-! ### The control -/

/-- **The control before the register run**: the region of its route, then the port line of DEC
copy `2 j`, the DEC chain and the flight of `C'` (`u ≥ cd_C + 9`, `v ∈ [vp_C - 90, -2300]`). -/
theorem dsepA_footC_hull (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t ≤ decTS p i r) : ∀ x ∈ decFootC p i r t,
    x ∈ dsepADown (A p i + decR) (trackOut p (instrBand i) 1 (A p i + decR))
      (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
      (trackBack p (instrBand i) 1 (A p i + decR)) (U p r + decChan p (2 * (callerIdx p r i)))
      (decPortV p (2 * (callerIdx p r i))) ∨
    (U p r - 784 - 124 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 - x.2 ∧
      x.1 - x.2 ≤ U p r + 160 + 58 * D p ∧
      -3342 - 198 * D p + 198 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ -2300) := by
  intro x hx
  obtain ⟨-, -, -, -, -, -, -, hcC, hvC, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, -, -, -, -, -,
    -, -, hu1, hu2⟩ := dsepA_lay hi
  have hm := decM_cast p hi
  have hU := U_even p r
  have hpar := decChan_parity p i r (callerIdx p r i)
  obtain ⟨-, hA20, hTA⟩ := decTA_facts p hi
  unfold decFootC at hx
  split_ifs at hx with ha hb hc
  · unfold flyFoot at hx
    split_ifs at hx with hd
    · left
      refine dsepA_down_sub p (instrBand i) 1 (A p i + decR) _ _ _ r _ (decC_timedX p hi)
        (decC_lines p i r).1 ?_ hpar.1 (by omega) (t - 4260)
        (show 4260 + (t - 4260) ≤ routeEndX _ (decCornC p i r) 4260 by omega) hx
      unfold hairC
      have := fixp_parity (HI p + 90 - 2 * eCtot (qOf p ↑(callerIdx p r i))) ((A p ↑i + decR) % 2)
      omega
    · right
      have hpc : CPar ⟨4, U p r + decChan p (2 * (callerIdx p r i)),
          decPortV p (2 * (callerIdx p r i)), .left r (2 * (callerIdx p r i))⟩ := by
        simp only [CPar, rfCU, rfCV]; omega
      obtain ⟨cu, cv, hr, hsub⟩ := dsepA_final_ray (bandCorners p (instrBand i) 1 (A p i + decR)
        (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
        (U p r + decChan p (2 * (callerIdx p r i))) 3 2) _ (unitWL p i decRWL) 4260
        (by norm_num) hpc (decC_timedX p hi) (le_of_lt (not_le.1 hd))
      have hx1 := hsub hx
      simp only [Ray, outD] at hr
      obtain ⟨y1, y2, y3, y4⟩ := hx1
      have hx2 : x ∈ (decGC p i r).box t := hx
      rw [decC_window] at hx2
      obtain ⟨x1, x2, x3, x4⟩ := hx2
      simp only [decWin, modWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
      have := sigma_bounds (qOf p (callerIdx p r i))
      simp only [decSlot] at hTA x1 x2 x3 x4
      generalize slot (decGC p i r) (decWin p r (2 * ↑(callerIdx p r i))) = k at *
      omega
  · right
    obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · right
    obtain ⟨d, ⟨j', hj', d1, d2, d3, d4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add] at d1 d2 d3 d4 ⊢
    have : (j' : ℤ) ≤ (decM p i r : ℤ) := by omega
    exact ⟨by omega, by omega, by omega, by omega⟩
  · right
    obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    have e1 : decTS p i r = decTB p i r + 1771 := by unfold decTS decTB; omega
    simp only [cp0WL, WL.px, WL.py, WL.qt, Prod.fst_add, Prod.snd_add] at *
    omega

/-! ### The tokens -/

/-- **`KNZ` before its capture**: the region of its route, the flight on its port line and the
joint approach with station `j` (`dsepA_winN_foot`). -/
theorem dsepA_tokN_hull (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t < decCapN p i r) : ∀ x ∈ tokFootN p i r t,
    x ∈ dsepADown (A p i + decL) (trackOut p (instrBand i) 0 (A p i + decL))
      (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
      (trackBack p (instrBand i) 0 (A p i + decL)) (U p r + nzTokChan p (callerIdx p r i))
      (nzTokPortV (callerIdx p r i)) ∨
    (x.1 - x.2 ≤ U p r - 520 ∧ 1254 + 144 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 + x.2 ∧
      x.1 + x.2 ≤ 1262 + 144 * ((callerIdx p r i : ℕ) : ℤ)) ∨
    ((362 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
        x.1 ≤ 467 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
        846 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
        x.2 ≤ 919 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ)) ∨
      (372 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
        x.1 ≤ 467 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
        820 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
        x.2 ≤ 919 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ))) := by
  intro x hx
  have hu := modD_uv p r
  have hU := U_even p r
  have hc := (decCap_cast p hi).1
  have hpar := nzTokChan_parity p i r (callerIdx p r i)
  unfold tokFootN at hx
  split_ifs at hx with h1
  · unfold flyFoot at hx
    split_ifs at hx with h2
    · left
      refine dsepA_down_sub p (instrBand i) 0 (A p i + decL) _ _ _ r _ (decKNZ_timedX p hi)
        (decKNZ_lines p i r).1 ?_ hpar.1 (by omega) (t - 4260)
        (show 4260 + (t - 4260) ≤ routeEndX _ (decCornN p i r) 4260 by omega) hx
      unfold hairKNZ
      have := fixp_parity (hairC p (qOf p ↑(callerIdx p r i)) (A p ↑i + decR) - 62 -
        2 * eN (qOf p ↑(callerIdx p r i))) ((A p ↑i + decL) % 2)
      omega
    · right; left
      rw [decKNZ_target] at hx
      obtain ⟨x1, x2, x3, x4⟩ := hx
      simp only [modWL, tokNZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
      have : (t : ℤ) + 90 ≤ decCapN p i r := by omega
      omega
  · right; right
    have hk : t - (decCapN p i r - 90) < 90 := by omega
    rw [decTokWStartN_eq hi, Rule.evolve_translate, mem_coe, mem_translate] at hx
    rcases dsepA_winN_foot _ hk (mem_coe.2 hx) with ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩
    · left
      simp only [Prod.fst_sub, Prod.snd_sub] at x1 x2 x3 x4
      exact ⟨by omega, by omega, by omega, by omega⟩
    · right
      simp only [Prod.fst_sub, Prod.snd_sub] at x1 x2 x3 x4
      exact ⟨by omega, by omega, by omega, by omega⟩

/-- **`KZ` before its capture**: the region of its route, the flight on its station column and the
joint approach with station `j` (`dsepA_winZ_foot`). -/
theorem dsepA_tokZ_hull (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t < decCapZ p i r) : ∀ x ∈ tokFootZ p i r t,
    x ∈ dsepAZtok (A p i + decD) (trackOut p (instrBand i) 2 (A p i + decD))
      (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
      (trackBack p (instrBand i) 2 (A p i + decD)) (U p r + zTokChan p (callerIdx p r i))
      (zTokDepth p (callerIdx p r i)) (U p r + zTokStation (callerIdx p r i)) ∨
    (U p r + 1226 + 144 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 - x.2 ∧
      x.1 - x.2 ≤ U p r + 1234 + 144 * ((callerIdx p r i : ℕ) : ℤ) ∧ 0 ≤ x.1 + x.2) ∨
    ((880 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
        x.1 ≤ 979 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
        -380 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
        x.2 ≤ -286 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) ∨
      (940 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
        x.1 ≤ 950 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
        -290 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
        x.2 ≤ -279 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ))) := by
  intro x hx
  have hu := modD_uv p r
  have hU := U_even p r
  have hc := (decCap_cast p hi).2
  have hpar := zTokChan_parity p i r (callerIdx p r i)
  unfold tokFootZ at hx
  split_ifs at hx with h1
  · unfold flyFoot at hx
    split_ifs at hx with h2
    · left
      exact dsepA_ztok_sub p (instrBand i) (A p i + decD) _ r _ (decKZ_timedX p hi)
        (decKZ_lines p i r) (by unfold hairKZ; exact hairReg_par _ _ _ _) hpar.1 (by omega)
        (by omega) (t - 4260)
        (show 4260 + (t - 4260) ≤ routeEndX _ (decCornZ p i r) 4260 by omega) hx
    · right; left
      rw [decKZ_target] at hx
      obtain ⟨x1, x2, x3, x4⟩ := hx
      simp only [modWL, tokZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
      have : (t : ℤ) + 90 ≤ decCapZ p i r := by omega
      omega
  · right; right
    have hk : t - (decCapZ p i r - 90) < 90 := by omega
    rw [decTokWStartZ_eq hi, Rule.evolve_translate, mem_coe, mem_translate] at hx
    rcases dsepA_winZ_foot _ hk (mem_coe.2 hx) with ⟨x1, x2, x3, x4⟩ | ⟨x1, x2, x3, x4⟩
    · left
      simp only [Prod.fst_sub, Prod.snd_sub] at x1 x2 x3 x4
      exact ⟨by omega, by omega, by omega, by omega⟩
    · right
      simp only [Prod.fst_sub, Prod.snd_sub] at x1 x2 x3 x4
      exact ⟨by omega, by omega, by omega, by omega⟩

end LP

end LeanTheory.Life
