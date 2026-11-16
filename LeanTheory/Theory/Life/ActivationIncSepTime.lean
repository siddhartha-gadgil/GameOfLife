/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepProof4

/-!
# The continue meets its fourth corner after the increment has started

Research note `N-22`. The two threads of an `inc` activation cross once in space: the column of
the continue up to unit `i + 1` crosses the `BACK` track of the INC link (both in sub-band
`i + 1`). They do not meet in time: the far hairpin `G` of the continue (`incSpecs`) delays the
continue so that it reaches its fourth corner (the foot of that column) more than `8000`
generations after the increment arrives at the INC gate (`isep2_m4C`):

* `isep2_tinc`: the time `tinc` used by `incSpecs` is `Tg + 1 + δm`;
* `isep2_meet_six`: for a corner of image `6` met on its input line, `meetT = timeUV - 10`;
* `isep2_m4C`: `Tg + 966 ≤ meetT` of the fourth corner of the continue (the continue enters the
  window of its fourth corner only after the increment has started at `Tg + 946`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-- **The time `tinc` of `incSpecs`** is `Tg + 1 + δm` for the plan of an `inc` instruction. -/
theorem isep2_tinc (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    incTinc p i r = ((incPlan p i r).Tg : ℤ) + 1 + (incPlan p i r).δm := by
  have hv := incPlan_valid hp hins
  have htl := (incTl_range hins).1
  have htlN : (((incTl p i r).toNat : ℕ) : ℤ) = incTl p i r := Int.toNat_of_nonneg htl
  have hT0l := hv.T0lE
  have hTg := hv.TgE
  have hU := U_even p r
  have hA := A_even p ((p.length + r : ℕ) : ℤ)
  have hVU := VU_even p
  have hT1 : ((incPlan p i r).T1 : ℤ) = (incPlan p i r).T0l + 134 + incTl p i r * 254 := by
    simp only [IncPlan.T1]
    push_cast
    change _ + (134 + (((incTl p i r).toNat : ℕ) : ℤ) * 254) = _
    rw [htlN]
    ring
  have hgm : incGm p i r = (incPlan p i r).gM := by
    have hs : slot (incGl p i r) (destWin p (p.length + r) (incTl p i r)) = incXl p i r / 30 :=
      rfl
    have hkl : (incPlan p i r).kl = incXl p i r / 30 := rfl
    have htl' : ((incPlan p i r).tl : ℤ) = incTl p i r := htlN
    simp only [incGm, IncPlan.gM, mergeOutWL, WL.shift, unitWL, haltDWL, hs, mergeUnit,
      WL.mk.injEq, true_and]
    rw [htl'] at hT0l
    constructor <;> omega
  have hfin := hv.finM
  unfold incTinc
  rw [hgm]
  change timeUV (route (incPlan p i r).gM (incPlan p i r).csM).2 _ _ = _
  rw [hfin]
  simp only [timeUV, modWL, incWin, WL.shift, modDX, modDY]
  omega

/-- **The meeting time of a corner of image `6`**: for a glider on the input line of the corner
(with the parity of the image), `meetT = timeUV - 10` at the corner point. -/
theorem isep2_meet_six {g : WL} {c : Corner} (hl : OnLine g c) (hk : c.k = 6) (hpar : CPar c) :
    meetT g c = timeUV g c.u c.v - 10 := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only at hk
  subst hk
  have h := inWL_of_onLine hl
  unfold meetT
  generalize delayS g ⟨6, u, v, tag⟩ = s at h ⊢
  rw [h]
  simp only [CPar] at hpar
  simp only [inWL, timeUV, WL.shift, rfIn, rfX, rfY, rfCU, rfCV] at hpar ⊢
  omega

/-- The fourth corner of the continue of instruction `i` (image `6`, at the foot of the column of
its entry copy, on its `BACK` track). -/
def isep2C4 (p : Program) (i : ℕ) : Corner :=
  ⟨6, destU p (i + 1) (incTc p i), trackBack p (instrBand i) 0 (incCc p i),
    .band (instrBand i) (9 - 0) false⟩

/-- The first three corners of the continue. -/
def isep2C3 (p : Program) (i r : ℕ) : List Corner := (incPlan p i r).csC.take 3

/-- **The continue meets its fourth corner `≥ 966` generations after the arrival of the
increment at the INC gate** (in fact `≥ 8383`). -/
theorem isep2_m4C (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ((incPlan p i r).Tg : ℤ) + 966 ≤
      meetT (route (unitWL p i incDWL) (isep2C3 p i r)).2 (isep2C4 p i) := by
  have hv := incPlan_valid hp hins
  have hδ := hv.δmR
  have htinc := isep2_tinc hp hins
  -- the fourth corner is met on its input line
  have hl4 : OnLine (route (unitWL p i incDWL) (isep2C3 p i r)).2 (isep2C4 p i) :=
    hv.linesC.2.2.2.1
  have hdC := copyBeta_spec (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (incCc p i)
  have hAi := A_even p i
  have hAi1 := A_even p ((i + 1 : ℕ) : ℤ)
  have hC1 := unitC0_cases p (i + 1)
  have hVU := VU_even p
  have hd : (destU p (i + 1) (incTc p i) - incCc p i) % 2 = 0 := by
    simp only [destU, incTc, incCc, incD] at hdC ⊢
    omega
  have hvp : (destU p (i + 1) (incTc p i) + destV p (incTc p i)) % 2 = 1 := by
    have := inCol_side_odd (incTc p i)
    simp only [destU, destV, C0dec, C0inc, C0halt] at this ⊢
    rcases hC1 with h | h | h <;> rw [h] <;> omega
  have hb := trackBack_par p (instrBand i) 0 (incCc p i)
  have hpar : CPar (isep2C4 p i) := by
    simp only [CPar, isep2C4, rfCU, rfCV]
    omega
  have hm := isep2_meet_six hl4 rfl hpar
  rw [hm]
  -- the delayed continue in terms of the undelayed one
  have hGe2 : incG p i r % 2 = 0 := by unfold incG; omega
  have hGe := G_nonneg (incTinc p i r + 8500 - incT0 p i)
  have htau : (route (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r))).2.tau +
      4 * hairCont p (incG p i r) (incEc p i r) (incCc p i) =
      (route (unitWL p i incDWL) (incMkc p i 0 (incEc0 p i))).2.tau +
        4 * hairCont p 0 (incEc0 p i) (incCc p i) := upCorners_tau p (instrBand i) 0 (incCc p i)
    (hairCont p (incG p i r) (incEc p i r) (incCc p i)) (hairCont p 0 (incEc0 p i) (incCc p i))
    (i + 1) (incTc p i) (g := unitWL p i incDWL) rfl rfl (hairCont_par _ _ _ _)
    (hairCont_par _ _ _ _) hd
  have ht3 : (route (unitWL p i incDWL) (incMkc p i 0 (incEc0 p i))).2.tau =
      incT0 p i - 2 * destU p (i + 1) (incTc p i) + 2 * trackBack p (instrBand i) 0 (incCc p i) -
        4 * destV p (incTc p i) - 10 :=
    upCorners_tau_t3 p (instrBand i) 0 (incCc p i) _ (i + 1) (incTc p i) _
      (hairCont_par _ _ _ _) hd hvp
  have ht3G := upCorners_tau_t3 p (instrBand i) 0 (incCc p i)
    (hairCont p (incG p i r) (incEc p i r) (incCc p i)) (i + 1) (incTc p i) (unitWL p i incDWL)
    (hairCont_par _ _ _ _) hd hvp
  have hH := hairCont_G p (incG p i r) (incEc p i r) (incCc p i) hGe2
  have hH' := hairCont_G p 0 (incEc0 p i) (incCc p i) (by norm_num)
  have hec0 : 0 ≤ incEc0 p i ∧ incEc0 p i ≤ 14 := solveE_bounds _ _ _
  have hecB : 0 ≤ incEc p i r ∧ incEc p i r ≤ 14 := solveE_bounds _ _ _
  have hG4 : incTinc p i r + 8500 - incT0 p i ≤ 4 * incG p i r := by
    have := le_max_right 0 (incTinc p i r + 8500 - incT0 p i)
    have := le_max_left 0 (incTinc p i r + 8500 - incT0 p i)
    unfold incG ceil120
    omega
  have e1 : (route (unitWL p i incDWL) (isep2C3 p i r)).2 = (route (unitWL p i incDWL)
      ((upCorners p (instrBand i) 0 (incCc p i) (hairCont p (incG p i r) (incEc p i r)
        (incCc p i)) (i + 1) (incTc p i)).take 3)).2 := rfl
  rw [e1]
  simp only [isep2C4]
  simp only [incMkc] at htau ht3
  rcases hδ with h | h <;> rw [h] at htinc <;> omega

end LP

end LeanTheory.Life
