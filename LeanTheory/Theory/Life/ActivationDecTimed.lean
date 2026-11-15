/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecLinks

/-!
# The route law for the links of a `decJz` activation

Research note `N-22`, layer 3: the corners of the control `C` and of the tokens `KNZ`, `KZ` of
`decJz r _` at instruction `i` are met in order (`RouteTimed`) from the end of the body (template
time `4260`), for every program (`decC_timed`, `decKNZ_timed`, `decKZ_timed`; the Z token link
needs `ztokCorners_timed`). Together with the lines (`ActivationDecLinks`) this is the time and
world-line part of `RouteOK` (`routeOK_of`); the separation part stays to be proved (route
separation).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- **The route law for the Z token link** (`ztokCorners`): from the `SE` glider `g` on the column
`c`, the first corner is met at `g.tau + 2 (c + OUT) - 10`, and the corners are met in order when
every leg is at least `40` long. -/
theorem ztokCorners_timed (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0)
    (hd : (U p r + zTokChan p j - c) % 2 = 0) (T : ℤ)
    (h0 : T ≤ g.tau + 2 * (c + trackOut p b 2 c) - 10) (hcH : H + 40 ≤ c)
    (hdH : H + 40 ≤ U p r + zTokChan p j)
    (hOB : trackOut p b 2 c + 40 ≤ trackBack p b 2 c)
    (hBW : trackBack p b 2 c + 40 ≤ zTokDepth p j)
    (hSt : U p r + zTokStation j + 40 ≤ U p r + zTokChan p j) :
    RouteTimed g (ztokCorners p b c H r j) T := by
  have ho := trackOut_par p b 2 c
  have hb := trackBack_par p b 2 c
  have hU := U_even p r
  obtain ⟨-, h2, h3⟩ := zTokChan_parity p 0 r j
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl h0
  subst hdx hdy hl
  simp only [ztokCorners, bandCorners, List.cons_append, List.nil_append, RouteTimed,
    reflect, meetT, delayS, WL.shift, rfIn, rfOut, rfX, rfY, rfCU, rfCV, zTokStation] at *
  generalize zTokChan p j = cz at *
  generalize zTokDepth p j = wd at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

/-- Facts of the layout used by the route law of the `decJz` links. -/
theorem dec_layout_facts (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    0 ≤ A p i ∧ U0 p ≤ U p r ∧ slabR p + 120 ≤ U0 p + modLeft p ∧ HI p ≤ -716 - 122 * P p ∧
      1 ≤ P p ∧ 1 ≤ D p ∧ (callerIdx p r i : ℤ) < D p ∧ VT p + 660 * NB p ≤ modTop p - 120 ∧
      instrBand i < NB p := by
  have hj := callerIdx_lt_D p hi
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  refine ⟨A_nonneg p (by omega), (U_ge p (r := r) (by omega)).1, (U_ge p (r := r) (by omega)).2,
    by unfold HI; omega, one_le_P p, one_le_D p, by unfold D; exact_mod_cast hj,
    (sep03_band_modules p).1, ?_⟩
  have := one_le_R p
  unfold instrBand NB N
  omega

/-- The hairpin of `C` is at most `H_I + 90`. -/
theorem hairC_le (p : Program) {q : ℤ} (hq : 0 ≤ q) (c : ℤ) : hairC p q c ≤ HI p + 90 := by
  have := fixp_bounds (HI p + 90 - 2 * eCtot q) (c % 2)
  have := eC_bounds q
  have := sigma_bounds q
  have := (xC_spec hq).2.2
  unfold hairC eCtot at *
  omega

/-- The hairpin of `KNZ` is at least `62` left of the hairpin of `C`. -/
theorem hairKNZ_le (p : Program) {q : ℤ} (hq : 0 ≤ q) (cC c : ℤ) :
    hairKNZ p q cC c + 62 ≤ hairC p q cC := by
  have := fixp_bounds (hairC p q cC - 62 - 2 * eN q) (c % 2)
  have := (eN_spec hq).2
  unfold hairKNZ at *
  omega

/-- The slab bound `slabR ≥ 238`. -/
theorem slabR_ge (p : Program) : 238 ≤ slabR p := le_max_left _ _

/-- **The control `C` meets its corners in order** from the end of the body (template time
`4260`), for every program. -/
theorem decC_timed (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    RouteTimed (unitWL p i decRWL) (decCornC p i r) 4260 := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  obtain ⟨h1, h2, h3'⟩ := unitWL_dec_lane p i 127 1221
  have hp := decChan_parity p i r (callerIdx p r i)
  have hR : decR = 127 := rfl
  have hu := unitD_uv p i
  have hVT := VT_mod p
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hH := hairC_le p hq (A p i + decR)
  have hcl := leftChan_in_extent p (idx := 2 * (callerIdx p r i))
    (v := decPortV p (2 * (callerIdx p r i))) ⟨by omega, by omega⟩
  have hsl := slabR_ge p
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  refine downCorners_timed p _ _ _ _ _ _ r _ h1 h2 h3'
    (by unfold hairC; have := fixp_parity (HI p + 90 - 2 * eCtot (qOf p ↑(callerIdx p r i)))
          ((A p ↑i + decR) % 2); omega) hp.1 (by have := U_even p r; omega) 4260 ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift, trackOut, track, VU] at hu ⊢; omega
  · omega
  · unfold decChan; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, decPortV, modTop, instrBand] at h3 hb ⊢; omega

/-- **The token `KNZ` meets its corners in order** from the end of the body, for every
program. -/
theorem decKNZ_timed (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    RouteTimed (unitWL p i decLWL) (decCornN p i r) 4260 := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  obtain ⟨h1, h2, h3'⟩ := unitWL_dec_lane p i (-155) 2665
  have hp := nzTokChan_parity p i r (callerIdx p r i)
  have hR : decR = 127 := rfl
  have hL : decL = -155 := rfl
  have hu := unitD_uv p i
  have hVT := VT_mod p
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hH := hairC_le p hq (A p i + decR)
  have hK := hairKNZ_le p hq (A p i + decR) (A p i + decL)
  have hcl := leftChan_in_extent p (idx := 2 * D p + 1 + 2 * (callerIdx p r i))
    (v := nzTokPortV (callerIdx p r i)) ⟨by omega, by omega⟩
  have hsl := slabR_ge p
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  refine downCorners_timed p _ _ _ _ _ _ r _ h1 h2 h3'
    (by unfold hairKNZ; have := fixp_parity (hairC p (qOf p ↑(callerIdx p r i)) (A p ↑i + decR)
          - 62 - 2 * eN (qOf p ↑(callerIdx p r i))) ((A p ↑i + decL) % 2); omega)
    hp.1 (by have := U_even p r; omega) 4260 ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift, trackOut, track, VU] at hu ⊢; omega
  · omega
  · unfold nzTokChan; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, nzTokPortV, modTop, instrBand] at h3 hb ⊢; omega

/-- **The token `KZ` meets its corners in order** from the end of the body, for every program. -/
theorem decKZ_timed (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    RouteTimed (unitWL p i decDWL) (decCornZ p i r) 4260 := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  obtain ⟨h1, h2, h3'⟩ := unitWL_dec_lane p i 188 787
  have hUe := U_even p r
  have hu := unitD_uv p i
  have hVT := VT_mod p
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hk := hairReg_le p (s := 2) (e := eKZ (qOf p (callerIdx p r i))) (c := A p i + decD)
    (by norm_num) (eKZ_spec hq).2.1
  have hz := zAnsDepth_eq p (callerIdx p r i)
  have hzc := fixp_bounds (uR p + 124 * qOf p (callerIdx p r i) + 62)
    (1 - zTokDepth p (callerIdx p r i) % 2)
  have hsl := le_max_left (238 : ℤ) (86 + 58 * P p)
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  refine ztokCorners_timed p _ _ _ r _ h1 h2 h3' (by unfold hairKZ; exact hairReg_par _ _ _ _)
    (zTokChan_parity p i r _).1 4260 ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift, trackOut, track, VU] at hu ⊢; omega
  · unfold hairKZ decD at *; omega
  · unfold hairKZ zTokChan at *
    simp only [modLeft, slabR, U0, uR] at *; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, zTokDepth, modTop, instrBand] at h3 hb hz ⊢; omega
  · unfold zTokChan zTokStation; simp only [uR, qOf] at hzc ⊢; omega

end LP

end LeanTheory.Life
