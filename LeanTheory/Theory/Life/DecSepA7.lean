/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepA6

/-!
# Hulls for the Z activation

Research note `N-22`. The numbers of the Z answer link (`dsepA_layAZ`), the hulls of the pieces of
`KZ` and of the Z answer link, of the Z answer after the cut (`dsepA_ansZ_hull`), the tags of the
routes, and the footprints of the control and of `KZ` after the end of their routes
(`dsepA_footC_after`, `dsepA_tokZ_after`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- **The numbers of the Z answer link.** -/
theorem dsepA_layAZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    U p r + zAnsStation (callerIdx p r i) = U p r + 1301 + 144 * ((callerIdx p r i : ℕ) : ℤ) ∧
    zAnsDepth p (callerIdx p r i) = 1500 + 180 * (D p - 1 - ((callerIdx p r i : ℕ) : ℤ)) ∧
    U p r + 1409 + 144 * D p + 124 * (D p - 1 - ((callerIdx p r i : ℕ) : ℤ)) ≤
      U p r + zAnsChan p (callerIdx p r i) ∧
    U p r + zAnsChan p (callerIdx p r i) ≤
      U p r + 1410 + 144 * D p + 124 * (D p - 1 - ((callerIdx p r i : ℕ) : ℤ)) ∧
    VT p + 660 * instrBand i + 248 ≤
      trackOut p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i)) ∧
    trackOut p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i)) ≤
      VT p + 660 * instrBand i + 249 ∧
    VT p + 660 * instrBand i + 310 ≤
      trackBack p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i)) ∧
    trackBack p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i)) ≤
      VT p + 660 * instrBand i + 311 ∧
    HI p + 331 ≤ hairReg p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i)) ∧
    hairReg p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i)) ≤ HI p + 360 ∧
    destV p (decTZ p i r z) ≤ VU p + 76 := by
  have ht := decTZ_range hp hi
  have hz := zAnsDepth_eq p (callerIdx p r i)
  have hc := fixp_bounds (uR p + 124 * qOf p (callerIdx p r i))
    (1 - zAnsDepth p (callerIdx p r i) % 2)
  have he : 0 ≤ decEB p i r z ∧ decEB p i r z ≤ 14 := solveE_bounds _ _ _
  have hf := fixp_bounds (HI p + 90 * 4 - 2 * decEB p i r z)
    ((U p r + zAnsChan p (callerIdx p r i)) % 2)
  refine ⟨by simp only [zAnsStation]; ring, by rw [hz]; simp only [qOf], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · unfold zAnsChan; simp only [uR, qOf] at hc ⊢; omega
  · unfold zAnsChan; simp only [uR, qOf] at hc ⊢; omega
  · simp only [trackOut, track]; omega
  · simp only [trackOut, track]; omega
  · simp only [trackBack, track]; omega
  · simp only [trackBack, track]; omega
  · unfold hairReg; omega
  · unfold hairReg; omega
  · simp only [destV, sideV]; omega

/-- The cells of the pieces of the `KZ` thread: its reflectors and station `j` of the line Z. -/
theorem dsepA_LZu_cells : ∀ g ∈ decLZu p i r, ∀ x ∈ g.box,
    (dsepACB (A p i + decD) (trackOut p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
      (trackOut p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
      (trackBack p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (U p r + zTokChan p (callerIdx p r i)) (trackBack p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (U p r + zTokChan p (callerIdx p r i)) (zTokDepth p (callerIdx p r i)) x ∨
    dsepACB (U p r + zTokStation (callerIdx p r i)) (zTokDepth p (callerIdx p r i)) x) ∨
    ((889 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
      x.1 ≤ 979 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
      -325 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
      x.2 ≤ -293 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) ∨
    (951 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
      x.1 ≤ 973 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
      -352 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
      x.2 ≤ -344 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) ∨
    (880 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
      x.1 ≤ 883 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
      -380 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
      x.2 ≤ -377 + modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ))) := by
  intro g hg x hx
  simp only [decLZu, mem_dd, List.mem_append] at hg
  rcases hg with hg | hg
  · exact Or.inl (dsepA_LZ_cells hg hx)
  · exact Or.inr (dsepA_sjZ_cells hg hx)

/-- The cells of the pieces of the Z answer link: its reflectors and the entry copies of
unit `z`. -/
theorem dsepA_LF0Z_cells : ∀ g ∈ decLF0Z p i r z, ∀ x ∈ g.box,
    (dsepACB (U p r + zAnsStation (callerIdx p r i)) (zAnsDepth p (callerIdx p r i)) x ∨
    dsepACB (U p r + zAnsChan p (callerIdx p r i)) (zAnsDepth p (callerIdx p r i)) x ∨
    dsepACB (U p r + zAnsChan p (callerIdx p r i))
      (trackOut p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))) x ∨
    dsepACB (hairReg p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i)))
      (trackOut p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))) x ∨
    dsepACB (hairReg p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i)))
      (trackBack p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))) x ∨
    dsepACB (destU p z (decTZ p i r z))
      (trackBack p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))) x ∨
    dsepACB (destU p z (decTZ p i r z)) (destV p (decTZ p i r z)) x) ∨
    (A p z - 32 ≤ x.1 - x.2 ∧ x.1 + x.2 ≤ VU p + 122) := by
  intro g hg x hx
  simp only [decLF0Z, mem_dd, List.mem_append] at hg
  rcases hg with hg | hg
  · exact Or.inl (dsepA_LAZ_cells hg hx)
  · exact Or.inr (dsepA_E_cells hg hx)

/-- **The Z answer after the cut**: on its line `v = 537` left of station `0`, then in the
footprints of the stations `0 … j - 1` it passes. -/
theorem dsepA_ansZ_hull (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h1 : decCutZ p i r ≤ t) :
    ∀ x ∈ decAnsFootZ p i r t,
    (673 + modDX p r ≤ x.1 ∧ x.1 ≤ 853 + modDX p r ∧ -315 + modDY p r ≤ x.2 ∧
      x.2 ≤ -135 + modDY p r ∧ 531 ≤ x.1 - modDX p r + (x.2 - modDY p r) ∧
      x.1 - modDX p r + (x.2 - modDY p r) ≤ 545) ∨
    ∃ k : ℤ, 0 ≤ k ∧ k < ((callerIdx p r i : ℕ) : ℤ) ∧
      ((889 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 979 + modDX p r + 72 * k ∧
        -325 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -293 + modDY p r - 72 * k) ∨
      (951 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 973 + modDX p r + 72 * k ∧
        -352 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -344 + modDY p r - 72 * k) ∨
      (880 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 883 + modDX p r + 72 * k ∧
        -380 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -377 + modDY p r - 72 * k) ∨
      (849 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 924 + modDX p r + 72 * k ∧
        -385 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -311 + modDY p r - 72 * k ∧
        536 ≤ x.1 - modDX p r + (x.2 - modDY p r) ∧ x.1 - modDX p r + (x.2 - modDY p r) ≤ 541))
    := by
  intro x hx
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have hu := modD_uv p r
  unfold decAnsFootZ at hx
  split_ifs at hx with h2
  · left
    obtain ⟨x1, x2, x3, x4⟩ := hx
    simp only [decAnsWLZ, modWL, ansZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
    simp only [decCutZ, decSt0Z] at h1 h2
    omega
  · right
    obtain ⟨d, ⟨k, hk, hd⟩, rfl⟩ := hx
    refine ⟨k, by omega, by omega, ?_⟩
    simp only [Prod.fst_add, Prod.snd_add]
    rcases hd with (((⟨d1, d2, d3, d4⟩ | ⟨d1, d2, d3, d4⟩) | ⟨d1, d2, d3, d4⟩) |
      ⟨m, m0, m1, d1, d2, d3, d4⟩) <;> simp only at d1 d2 d3 d4
    · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega, by omega,
        by omega⟩))

/-! ### Tags -/

/-- The tags of the control and of the Z answer differ. -/
theorem dsepA_tags_C_AZ : ∀ c ∈ decCornC p i r, ∀ c' ∈ decCsZ p i r z, c.tag ≠ c'.tag := by
  intro c hc c' hc'
  simp only [decCsZ, decMkZ, zAnsCorners, upCornersK, bandCorners, decCornC, downCorners,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The tags of `KZ` and of the Z answer differ. -/
theorem dsepA_tags_Z_AZ : ∀ c ∈ decCornZ p i r, ∀ c' ∈ decCsZ p i r z, c.tag ≠ c'.tag := by
  intro c hc c' hc'
  simp only [decCsZ, decMkZ, zAnsCorners, upCornersK, bandCorners, decCornZ, ztokCorners,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-! ### After the routes -/

/-- **The control after the end of its route**: on the port line of DEC copy `2 j`, in the DEC
chain and in the flight of `C'` (`u ≥ cd_C + 9`, `v ∈ [vp_C - 90, -2300]`). -/
theorem dsepA_footC_after (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (ht : t ≤ decTS p i r) (hre : routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 < t) :
    ∀ x ∈ decFootC p i r t,
    U p r - 784 - 124 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 - x.2 ∧
      x.1 - x.2 ≤ U p r + 160 + 58 * D p ∧
      -3342 - 198 * D p + 198 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ -2300 := by
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
    · omega
    have hpc : CPar ⟨4, U p r + decChan p (2 * (callerIdx p r i)),
        decPortV p (2 * (callerIdx p r i)), .left r (2 * (callerIdx p r i))⟩ := by
      simp only [CPar, rfCU, rfCV]; omega
    obtain ⟨cu, cv, hr, hsub⟩ := dsepA_final_ray (bandCorners p (instrBand i) 1 (A p i + decR)
      (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
      (U p r + decChan p (2 * (callerIdx p r i))) 3 2) _ (unitWL p i decRWL) 4260
      (by norm_num) hpc (decC_timedX p hi) (le_of_lt hre)
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
  · obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · obtain ⟨d, ⟨j', hj', d1, d2, d3, d4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add] at d1 d2 d3 d4 ⊢
    have : (j' : ℤ) ≤ (decM p i r : ℤ) := by omega
    exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    have e1 : decTS p i r = decTB p i r + 1771 := by unfold decTS decTB; omega
    simp only [cp0WL, WL.px, WL.py, WL.qt, Prod.fst_add, Prod.snd_add] at *
    omega

/-- **`KZ` after the end of its route**: the flight on its station column and the joint approach
with station `j`. -/
theorem dsepA_tokZ_after (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (ht : t < decCapZ p i r)
    (hre : ¬ (t ≤ decCapZ p i r - 90 ∧ t ≤ routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260)) :
    ∀ x ∈ tokFootZ p i r t,
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
  have hc := (decCap_cast p hi).2
  unfold tokFootZ at hx
  split_ifs at hx with h1
  · unfold flyFoot at hx
    split_ifs at hx with hd
    · omega
    left
    rw [decKZ_target] at hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    simp only [modWL, tokZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
    have : (t : ℤ) + 90 ≤ decCapZ p i r := by omega
    omega
  · right
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
