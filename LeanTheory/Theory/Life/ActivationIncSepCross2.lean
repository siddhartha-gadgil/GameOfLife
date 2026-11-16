/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepCross

/-!
# The two threads of an `inc` activation are far apart: the instances

Research note `N-22`. The regions `isep2SetS` (the continue before its fourth corner) and
`isep2SetJ` (the increment thread) of `ActivationIncSepCross`, instantiated for the plan
`incPlan p i r`, and the field `threads` of `IncSep`:

* `isep2_params`: the relations of the layout between the parameters of the two regions;
* `isep2_CMov_S`: the continue is in its region until the window of its fourth corner;
  `isep2_CMov_U`: the continue stays in the slabs of the units (`u ≤ A_{i+1} + 96 + 29 t_c`);
* `isep2_IMov_J`: the increment thread is in its region at every generation;
  `isep2_IMov_late`: after the start of the increment it is in module `r` (`u ≥ U_r - 760`);
* `isep2_cross`, `isep2_threads`: the moving parts of the two threads, hence the two threads,
  are far apart at every generation.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-- The region of the continue of instruction `i` before its fourth corner. -/
def isep2S (p : Program) (i r : ℕ) : Set Cell :=
  isep2SetS (incCc p i) (trackOut p (instrBand i) 0 (incCc p i))
    (hairCont p (incG p i r) (incEc p i r) (incCc p i)) (trackBack p (instrBand i) 0 (incCc p i))
    (destU p (i + 1) (incTc p i))

/-- The region of the increment thread of instruction `i`. -/
def isep2J (p : Program) (i r : ℕ) : Set Cell :=
  isep2SetJ (incCl p i) (trackOut p (instrBand i) 1 (incCl p i))
    (hairReg p 1 (incEl p i r) (incCl p i)) (trackBack p (instrBand i) 1 (incCl p i))
    (destU p (p.length + r) (incTl p i r)) (VT p + 660 * (instrBand i + 1) - 27)

/-- **The two regions are far apart** for every `inc` instruction of a well-formed program. -/
theorem isep2_SJ (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    FarApart 2 (isep2S p i r) (isep2J p i r) := by
  have hi1 := succ_lt_of_inc hp hins
  have hf := layout_facts p
  have hAi := A_even p i
  have hA0 := A_nonneg p (a := i) (by omega)
  have htc := incTc_range hp hins
  have htl := incTl_range hins
  have hC1 := unitC0_cases p (i + 1)
  have hGe := G_nonneg (incTinc p i r + 8500 - incT0 p i)
  have hec : 0 ≤ incEc p i r ∧ incEc p i r ≤ 14 := solveE_bounds _ _ _
  have hel : 0 ≤ incEl p i r ∧ incEl p i r ≤ 14 := solveE_bounds _ _ _
  have hHc : HI p - 62 - incG p i r - 2 * incEc p i r - 1 ≤
      hairCont p (incG p i r) (incEc p i r) (incCc p i) ∧
      hairCont p (incG p i r) (incEc p i r) (incCc p i) ≤
        HI p - 62 - incG p i r - 2 * incEc p i r := fixp_bounds _ _
  have hHl : HI p + 90 * 1 - 2 * incEl p i r - 1 ≤ hairReg p 1 (incEl p i r) (incCl p i) ∧
      hairReg p 1 (incEl p i r) (incCl p i) ≤ HI p + 90 * 1 - 2 * incEl p i r := fixp_bounds _ _
  have hcc : incCc p i = A p i + 68 := rfl
  have hHI : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hA := A_add_le p (a := ((i + 1 : ℕ) : ℤ)) (a' := ((p.length + r : ℕ) : ℤ))
    (by push_cast; omega)
  have hA' := A_add_le p (a := (i : ℤ)) (a' := ((i + 1 : ℕ) : ℤ)) (by push_cast; omega)
  have hG : incG p i r = 30 * ceil120 (max 0 (incTinc p i r + 8500 - incT0 p i)) := rfl
  unfold isep2S isep2J
  refine isep2_SJ_far ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold incCl incCc incR incD; ring
  · unfold trackOut track incCl incCc incR incD; omega
  · unfold trackOut trackBack track; omega
  · unfold trackOut trackBack track incCl incCc incR incD; omega
  · omega
  · omega
  · simp only [destU, inCol, unitC0_merge, C0halt] at *
    push_cast at hA ⊢
    omega
  · simp only [destU, inCol, unitC0_merge, C0halt, incCc, incD] at *
    push_cast at hA hA' ⊢
    omega
  · unfold trackBack track; omega

/-! ### The routes inside the regions -/

/-- **The continue is in its region until the window of its fourth corner.** -/
theorem isep2_contS (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j : ℕ, ((2010 : ℕ) : ℤ) + j ≤
      meetT (route (unitWL p i incDWL) (isep2C3 p i r)).2 (isep2C4 p i) - 20 →
      routeFootX (unitWL p i incDWL) (incPlan p i r).csC 2010 j ⊆ isep2S p i r := by
  have hv := incPlan_valid hp hins
  have hAi := A_even p i
  have hA0 := A_nonneg p (a := i) (by have := succ_lt_of_inc hp hins; omega)
  have hAi1 := A_even p ((i + 1 : ℕ) : ℤ)
  have htc := incTc_range hp hins
  have hC1 := unitC0_cases p (i + 1)
  have hf := layout_facts p
  have hdC := copyBeta_spec (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (incCc p i)
  have hd : (destU p (i + 1) (incTc p i) - incCc p i) % 2 = 0 := by
    simp only [destU, incTc, incCc, incD] at hdC ⊢
    omega
  have hGe := G_nonneg (incTinc p i r + 8500 - incT0 p i)
  have hG : incG p i r = 30 * ceil120 (max 0 (incTinc p i r + 8500 - incT0 p i)) := rfl
  have hec : 0 ≤ incEc p i r ∧ incEc p i r ≤ 14 := solveE_bounds _ _ _
  have hHc : HI p - 62 - incG p i r - 2 * incEc p i r - 1 ≤
      hairCont p (incG p i r) (incEc p i r) (incCc p i) ∧
      hairCont p (incG p i r) (incEc p i r) (incCc p i) ≤
        HI p - 62 - incG p i r - 2 * incEc p i r := fixp_bounds _ _
  have hcc : incCc p i = A p i + 68 := rfl
  have hHI : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hA' := A_add_le p (a := (i : ℤ)) (a' := ((i + 1 : ℕ) : ℤ)) (by push_cast; omega)
  have hdCv : A p ((i + 1 : ℕ) : ℤ) - 237 - 61 * (2 * P p) ≤ destU p (i + 1) (incTc p i) := by
    simp only [destU, inCol]
    omega
  have hB : trackBack p (instrBand i) 0 (incCc p i) =
      trackOut p (instrBand i) 0 (incCc p i) + 558 := by
    unfold trackOut trackBack track; omega
  intro j hj
  refine isep2_up_sub4 p (instrBand i) 0 (incCc p i)
    (hairCont p (incG p i r) (incEc p i r) (incCc p i)) (i + 1) (incTc p i) hv.timedC hv.linesC
    (hairCont_par _ _ _ _) hd ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ j hj <;>
    intro x h1 h2 h3 <;> try intro h4
  all_goals
    simp only [isep2S, isep2SetS, Set.mem_ofPred_eq]
    omega

/-- **The continue stays left of the column of its entry copy** (`u ≤ dC + 29`). -/
theorem isep2_contU (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j : ℕ, 2010 + j ≤ routeEndX (unitWL p i incDWL) (incPlan p i r).csC 2010 →
      routeFootX (unitWL p i incDWL) (incPlan p i r).csC 2010 j ⊆
        {x | x.1 - x.2 ≤ destU p (i + 1) (incTc p i) + 29} := by
  have hv := incPlan_valid hp hins
  have hAi := A_even p i
  have hA0 := A_nonneg p (a := i) (by have := succ_lt_of_inc hp hins; omega)
  have hAi1 := A_even p ((i + 1 : ℕ) : ℤ)
  have htc := incTc_range hp hins
  have hC1 := unitC0_cases p (i + 1)
  have hf := layout_facts p
  have hdC := copyBeta_spec (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (incCc p i)
  have hd : (destU p (i + 1) (incTc p i) - incCc p i) % 2 = 0 := by
    simp only [destU, incTc, incCc, incD] at hdC ⊢
    omega
  have hvp : (destU p (i + 1) (incTc p i) + destV p (incTc p i)) % 2 = 1 := by
    have hVU := VU_even p
    have := inCol_side_odd (incTc p i)
    simp only [destU, destV, C0dec, C0inc, C0halt] at this ⊢
    rcases hC1 with h | h | h <;> rw [h] <;> omega
  have hGe := G_nonneg (incTinc p i r + 8500 - incT0 p i)
  have hG : incG p i r = 30 * ceil120 (max 0 (incTinc p i r + 8500 - incT0 p i)) := rfl
  have hec : 0 ≤ incEc p i r ∧ incEc p i r ≤ 14 := solveE_bounds _ _ _
  have hHc : HI p - 62 - incG p i r - 2 * incEc p i r - 1 ≤
      hairCont p (incG p i r) (incEc p i r) (incCc p i) ∧
      hairCont p (incG p i r) (incEc p i r) (incCc p i) ≤
        HI p - 62 - incG p i r - 2 * incEc p i r := fixp_bounds _ _
  have hcc : incCc p i = A p i + 68 := rfl
  have hHI : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hA' := A_add_le p (a := (i : ℤ)) (a' := ((i + 1 : ℕ) : ℤ)) (by push_cast; omega)
  have hdCv : A p ((i + 1 : ℕ) : ℤ) - 237 - 61 * (2 * P p) ≤ destU p (i + 1) (incTc p i) := by
    simp only [destU, inCol]
    omega
  intro j hj
  refine isep2_up_sub5 p (instrBand i) 0 (incCc p i)
    (hairCont p (incG p i r) (incEc p i r) (incCc p i)) (i + 1) (incTc p i) hv.timedC hv.linesC
    (hairCont_par _ _ _ _) hd hvp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ j hj <;>
    intro x h1 h2 h3 <;> try intro h4
  all_goals
    simp only [Set.mem_ofPred_eq]
    omega

/-- The relations of the layout used for the region of the increment thread. -/
theorem isep2_J_facts (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    destU p (p.length + r) (incTl p i r) ≤ A p ((p.length + r : ℕ) : ℤ) - 67 ∧
      A p ((p.length + r : ℕ) : ℤ) + 299 ≤ U p r - 760 ∧
      VT p + 660 * (instrBand i + 1) - 27 ≤ -3444 ∧
      VT p + 660 * (instrBand i + 1) + 600 ≤ trackOut p (mergeBand p r) 0
        (A p ((p.length + r : ℕ) : ℤ) + haltD) := by
  have hi1 := succ_lt_of_inc hp hins
  have hr := lt_numRegs_of_inc hins
  have hf := layout_facts p
  have htl := incTl_range hins
  have hgap := unit_module_gap p (a := ((p.length + r : ℕ) : ℤ)) (r := r)
    ⟨by omega, by unfold N R; push_cast; omega⟩ (by omega)
  have hRs := slabR_ge_rs p
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [destU, inCol, unitC0_merge, C0halt]
    push_cast
    omega
  · unfold modLeft at hgap
    omega
  · unfold instrBand
    unfold N R at hf
    omega
  · unfold trackOut track mergeBand instrBand N
    omega

/-- **The INC link is in the region of the increment thread.** -/
theorem isep2_incJR (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j : ℕ, 2010 + j ≤ routeEndX (unitWL p i incRWL) (incPlan p i r).csR 2010 →
      routeFootX (unitWL p i incRWL) (incPlan p i r).csR 2010 j ⊆ isep2J p i r := by
  have hv := incPlan_valid hp hins
  have hAi := A_even p i
  have hA0 := A_nonneg p (a := i) (by have := succ_lt_of_inc hp hins; omega)
  have hAN := A_even p ((p.length + r : ℕ) : ℤ)
  have htl := incTl_range hins
  have hf := layout_facts p
  have hJ := isep2_J_facts hp hins
  have hdC := copyBeta_spec C0halt
    (predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0)) (incCl p i)
  have hd : (destU p (p.length + r) (incTl p i r) - incCl p i) % 2 = 0 := by
    simp only [destU, incTl, incCl, incR, unitC0_merge] at hdC ⊢
    omega
  have hvp : (destU p (p.length + r) (incTl p i r) + destV p (incTl p i r)) % 2 = 1 := by
    have hVU := VU_even p
    have := inCol_side_odd (incTl p i r)
    simp only [destU, destV, unitC0_merge, C0halt, C0dec, C0inc] at this ⊢
    omega
  have hel : 0 ≤ incEl p i r ∧ incEl p i r ≤ 14 := solveE_bounds _ _ _
  have hHl : HI p + 90 * 1 - 2 * incEl p i r - 1 ≤ hairReg p 1 (incEl p i r) (incCl p i) ∧
      hairReg p 1 (incEl p i r) (incCl p i) ≤ HI p + 90 * 1 - 2 * incEl p i r := fixp_bounds _ _
  have hcl : incCl p i = A p i + 157 := rfl
  have hHI : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hB : trackBack p (instrBand i) 1 (incCl p i) =
      trackOut p (instrBand i) 1 (incCl p i) + 434 := by
    unfold trackOut trackBack track; omega
  have hA := A_add_le p (a := (i : ℤ)) (a' := ((p.length + r : ℕ) : ℤ))
    (by have := succ_lt_of_inc hp hins; push_cast; omega)
  have hdI : A p ((p.length + r : ℕ) : ℤ) - 67 - 61 * (2 * P p) ≤
      destU p (p.length + r) (incTl p i r) := by
    simp only [destU, inCol, unitC0_merge, C0halt]
    push_cast at htl ⊢
    omega
  intro j hj
  refine isep2_up_sub5 p (instrBand i) 1 (incCl p i) (hairReg p 1 (incEl p i r) (incCl p i))
    (p.length + r) (incTl p i r) hv.timedR hv.linesR (hairReg_par _ _ _ _) hd hvp
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ j hj <;>
    intro x h1 h2 h3 <;> try intro h4
  all_goals
    simp only [isep2J, isep2SetJ, Set.mem_ofPred_eq]
    omega

/-- **The merge link is in the region of the increment thread.** -/
theorem isep2_incJM (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j : ℕ, (incPlan p i r).T1 + j ≤ (incPlan p i r).eM →
      routeFootX (incPlan p i r).gM (incPlan p i r).csM (incPlan p i r).T1 j ⊆
        isep2J p i r := by
  have hv := incPlan_valid hp hins
  have hJ := isep2_J_facts hp hins
  have hAN := A_even p ((p.length + r : ℕ) : ℤ)
  have hU := U_even p r
  have hc0 := incChan_even p
  have hpar := incChan_parity p (p.length + r) r
  have hcb : U p r + modLeft p + 29 ≤ U p r + incChan p ∧ U p r + incChan p ≤ U p r - 793 :=
    left_range p (r := r) (idx := 2 * D p) ⟨by have := one_le_D p; omega,
      by have := one_le_D p; omega⟩
      (by have := fixp_bounds (uL - 62 * (2 * D p)) (1 - incPortV % 2)
          unfold incChan leftChan uL at *; omega)
  have hB : trackBack p (mergeBand p r) 0 (A p ((p.length + r : ℕ) : ℤ) + haltD) =
      trackOut p (mergeBand p r) 0 (A p ((p.length + r : ℕ) : ℤ) + haltD) + 558 := by
    unfold trackOut trackBack track; omega
  have hm := modD_uv p r
  intro j hj
  refine isep2_down_sub p (mergeBand p r) 0 (A p ((p.length + r : ℕ) : ℤ) + haltD)
    (hairReg p 0 (mergeE p r) (A p ((p.length + r : ℕ) : ℤ) + haltD)) (U p r + incChan p)
    incPortV r (2 * D p) hv.timedM hv.linesM (hairReg_par _ _ _ _)
    (by simp only [haltD] at hpar ⊢; omega) (by simp only [incPortV] at hpar ⊢; omega)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ j hj <;>
    intro x h1 h2 h3 <;> try intro h4
  all_goals
    simp only [isep2J, isep2SetJ, Set.mem_ofPred_eq, haltD, incPortV] at *
    unfold modLeft at hcb
    omega

/-! ### The moving parts inside the regions -/

/-- The fourth corner of the continue is met at least `40` generations before the end of its
route. -/
theorem isep2_m4_end (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    meetT (route (unitWL p i incDWL) (isep2C3 p i r)).2 (isep2C4 p i) + 40 ≤
      routeEndX (unitWL p i incDWL) (incPlan p i r).csC 2010 := by
  have ht := (incPlan_valid hp hins).timedC
  have e : (incPlan p i r).csC = upCorners p (instrBand i) 0 (incCc p i)
      (hairCont p (incG p i r) (incEc p i r) (incCc p i)) (i + 1) (incTc p i) := rfl
  have e3 : (route (unitWL p i incDWL) (isep2C3 p i r)).2 = (reflect (reflect (reflect
      (unitWL p i incDWL) (isep2U1 p (instrBand i) 0 (incCc p i))).2
      (isep2U2 p (instrBand i) 0 (incCc p i) (hairCont p (incG p i r) (incEc p i r)
        (incCc p i)))).2
      (isep2U3 p (instrBand i) 0 (incCc p i) (hairCont p (incG p i r) (incEc p i r)
        (incCc p i)))).2 := rfl
  have e4 : isep2C4 p i = isep2U4 p (instrBand i) 0 (incCc p i) (i + 1) (incTc p i) := rfl
  rw [e3, e4]
  rw [e, isep2_upCorners_eq] at ht ⊢
  obtain ⟨t1, t2, t3, t4, t5, -⟩ := ht
  change _ ≤ (((meetT (reflect (reflect (reflect (reflect (unitWL p i incDWL)
    (isep2U1 p (instrBand i) 0 (incCc p i))).2
      (isep2U2 p (instrBand i) 0 (incCc p i) (hairCont p (incG p i r) (incEc p i r)
        (incCc p i)))).2
      (isep2U3 p (instrBand i) 0 (incCc p i) (hairCont p (incG p i r) (incEc p i r)
        (incCc p i)))).2
      (isep2U4 p (instrBand i) 0 (incCc p i) (i + 1) (incTc p i))).2
      (isep2U5 p (i + 1) (incTc p i))).toNat + 40 : ℕ) : ℤ)
  omega

/-- The final flight of the continue, in coordinates. -/
theorem isep2_mem_flyC (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {j : ℕ}
    (hj1 : routeEndX (unitWL p i incDWL) (incPlan p i r).csC 2010 ≤ j)
    (hj2 : j + 16 ≤ (incPlan p i r).T0c) {c : Cell}
    (hc : c ∈ (route (unitWL p i incDWL) (incPlan p i r).csC).2.box j) :
    c.1 - c.2 ≤ A p ((i + 1 : ℕ) : ℤ) + 6 + 29 * ((incPlan p i r).tc : ℤ) := by
  have hv := incPlan_valid hp hins
  have hcs := isep2_csC_eq hp hins
  have htim := hv.timedC
  have hfin := hv.finC
  rw [hcs] at htim hfin hj1 hc
  exact (isep2_mem_flyEntry htim hv.δcR hfin hv.T0cE hj1 hj2 hc).2.1

/-- The final flight of the INC link, in coordinates. -/
theorem isep2_mem_flyR (hins : p[i]? = some (.inc r)) (hp : p.WellFormed) {j : ℕ}
    (hj1 : routeEndX (unitWL p i incRWL) (incPlan p i r).csR 2010 ≤ j)
    (hj2 : j + 16 ≤ (incPlan p i r).T0l) {c : Cell}
    (hc : c ∈ (route (unitWL p i incRWL) (incPlan p i r).csR).2.box j) :
    A p ((p.length + r : ℕ) : ℤ) + C0halt + 13 - 61 * ((incPlan p i r).tl : ℤ) ≤ c.1 - c.2 := by
  have hv := incPlan_valid hp hins
  have hcs := isep2_csR_eq hins
  have htim := hv.timedR
  have hfin := hv.finR
  rw [hcs] at htim hfin hj1 hc
  have := (isep2_mem_flyEntry htim hv.δlR hfin hv.T0lE hj1 hj2 hc).1
  rw [unitC0_merge] at this
  exact this

/-- **The continue is in its region until the window of its fourth corner.** -/
theorem isep2_CMov_S (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j : ℕ, ((2010 : ℕ) : ℤ) + j ≤
      meetT (route (unitWL p i incDWL) (isep2C3 p i r)).2 (isep2C4 p i) - 20 →
      isep2CMov (incPlan p i r) j ⊆ isep2S p i r := by
  intro j hj
  have hv := incPlan_valid hp hins
  have hend := isep2_m4_end hp hins
  have hle : 2010 + j ≤ routeEndX (unitWL p i incDWL) (incPlan p i r).csC 2010 := by omega
  have hTc : j ≤ (incPlan p i r).Tc - 2010 := by
    have := hv.endC
    simp only [IncPlan.Tc]
    omega
  unfold isep2CMov linkFootW
  simp only [hTc, hle, ↓reduceIte]
  exact isep2_contS hp hins j hj

/-- **The continue stays in the slabs of the units.** -/
theorem isep2_CMov_U (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j < (incPlan p i r).Tend - 2010, isep2CMov (incPlan p i r) j ⊆
      {x | x.1 - x.2 ≤ A p ((i + 1 : ℕ) : ℤ) + 96 + 29 * ((incPlan p i r).tc : ℤ)} := by
  intro j hj
  have hv := incPlan_valid hp hins
  have htc := incTc_range hp hins
  have htcN : ((incPlan p i r).tc : ℤ) = incTc p i := Int.toNat_of_nonneg htc.1
  have hC1 := unitC0_cases p (i + 1)
  unfold isep2CMov
  split_ifs with h1
  · unfold linkFootW
    split_ifs with h2 h3
    · intro x hx
      have := isep2_contU hp hins j h2 hx
      simp only [Set.mem_ofPred_eq, destU, inCol] at this ⊢
      omega
    · intro x hx
      have := isep2_mem_flyC hp hins (j := 2010 + j) (by omega) (by omega)
        (by push_cast; exact hx)
      simp only [Set.mem_ofPred_eq]
      omega
    · intro x hx
      have := entryFoot_uv p (i + 1) (incPlan p i r).tc hx
      simp only [Set.mem_ofPred_eq]
      omega
  · intro x hx
    have := isep2_mem_outC p (i + 1) (j := j - ((incPlan p i r).Tc - 2010))
      (by have : (incPlan p i r).Tend = (incPlan p i r).Tc + 166 := rfl; omega) hx
    simp only [Set.mem_ofPred_eq]
    omega

/-- **The increment at module `r` stays right of `U_r - 738`**, for every ready register. -/
theorem isep2_evolve_u (p : Program) (r : ℕ) {R : RegS} (hR : R.Ready) (n : ℕ) :
    (conway.evolve n (incStart p r ∪ regAt p r R) : Set Cell) ⊆
      {x | U p r - 738 ≤ x.1 - x.2} := by
  have hm := modD_uv p r
  intro x hx
  rcases lane_incRun_sub p r hR n hx with (hx | hx) | hx
  · obtain ⟨d, hd, rfl⟩ := hx
    have := incRunBox_u hd
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at this ⊢
    omega
  · obtain ⟨g, hg, hxg⟩ := mem_boxesOf.1 hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
    have hs' : s ∈ moduleSpecs p r := by simp [moduleSpecs, hs]
    have hu := (moduleSpecs_uv p r hs').1
    rw [PSpec.piece_box] at hxg
    obtain ⟨x1, x2, x3, x4⟩ := hxg
    unfold BoxT.InUV at hu
    simp only [Set.mem_ofPred_eq]
    omega
  · obtain ⟨d, ⟨d1, d2, d3⟩, rfl⟩ := hx
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
    omega

set_option maxRecDepth 100000 in
/-- **The increment thread is in its region at every generation.** -/
theorem isep2_IMov_J (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {R0 : RegS}
    (hR : R0.Ready) : ∀ j < (incPlan p i r).Tend - 2010,
      isep2IMov (incPlan p i r) R0 j ⊆ isep2J p i r := by
  intro j hj
  have hv := incPlan_valid hp hins
  have hJ := isep2_J_facts hp hins
  have htl := incTl_range hins
  have htlN : ((incPlan p i r).tl : ℤ) = incTl p i r := Int.toNat_of_nonneg htl.1
  have hm := modD_uv p r
  have hgap := unit_module_gap p (a := ((p.length + r : ℕ) : ℤ)) (r := r)
    ⟨by omega, by have := lt_numRegs_of_inc hins; unfold N R; push_cast; omega⟩ (by omega)
  have hRs := slabR_ge_rs p
  have hcb : U p r + modLeft p + 29 ≤ U p r + incChan p :=
    (left_range p (r := r) (idx := 2 * D p) ⟨by have := one_le_D p; omega,
      by have := one_le_D p; omega⟩
      (by have := fixp_bounds (uL - 62 * (2 * D p)) (1 - incPortV % 2)
          unfold incChan leftChan uL at *; omega)).1
  have hright : ∀ x : Cell, U p r - 760 ≤ x.1 - x.2 → x ∈ isep2J p i r := by
    intro x hx
    simp only [isep2J, isep2SetJ, Set.mem_ofPred_eq]
    omega
  have hR1 := le_routeEndX _ _ 2010 hv.timedR
  have hR2 := hv.endR
  have hM1 := le_routeEndX _ _ _ hv.timedM
  have hM2 := hv.endM
  have hT1 : (incPlan p i r).T1 = (incPlan p i r).T0l + (134 + (incPlan p i r).tl * 254) := rfl
  have heM : (incPlan p i r).eM = routeEndX (incPlan p i r).gM (incPlan p i r).csM
    (incPlan p i r).T1 := rfl
  have hstrip : ∀ (R : RegS), R.Inv → ∀ n : ℕ, regStrip p r R (n + R.m) ⊆ isep2J p i r := by
    intro R hRi n x hx
    obtain ⟨d, ⟨d1, d2, d3⟩, rfl⟩ := regStrip_subset hRi p r n hx
    refine hright _ ?_
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  unfold isep2IMov
  split_ifs with h1 h2
  · refine Set.union_subset ?_ (hstrip R0 hR.1 j)
    unfold isep2EMov
    split_ifs with h3 h4 h5
    · unfold linkFootW
      split_ifs with h6 h7
      · exact isep2_incJR hp hins j h6
      · intro x hx
        have := isep2_mem_flyR hins hp (j := 2010 + j) (by omega) (by omega)
          (by push_cast; exact hx)
        simp only [isep2J, isep2SetJ, Set.mem_ofPred_eq, destU, inCol, unitC0_merge] at hJ ⊢
        rw [htlN] at this
        omega
      · intro x hx
        have := entryFoot_uv p (mergeUnit p r) (incPlan p i r).tl hx
        simp only [isep2J, isep2SetJ, Set.mem_ofPred_eq]
        simp only [mergeUnit] at this
        omega
    · exact isep2_incJM hp hins _ (by omega)
    · intro x hx
      have := isep2_mem_flyM hp hins (j := (incPlan p i r).eM +
        (j - ((incPlan p i r).T1 - 2010 + ((incPlan p i r).eM - (incPlan p i r).T1))))
        (by omega) (by omega) (by push_cast; exact hx)
      simp only [isep2J, isep2SetJ, Set.mem_ofPred_eq]
      unfold modLeft at hcb hgap
      omega
    · intro x hx
      have := isep2_mem_gateBox hx
      exact hright x (by omega)
  · refine Set.union_subset ?_ (hstrip (R0.later ((incPlan p i r).Tg - 2010))
      (hR.later ((incPlan p i r).Tg - 2010)).1 (j - ((incPlan p i r).Tg - 2010)))
    intro x hx
    have := lane_modFootW_u (j := j - ((incPlan p i r).Tg - 2010)) hv.TgE h2 x hx
    exact hright x (by omega)
  · intro x hx
    have := isep2_evolve_u p r (R := (R0.later ((incPlan p i r).Tg - 2010)).later 946)
      ((hR.later ((incPlan p i r).Tg - 2010)).later 946)
      (j - ((incPlan p i r).Tg - 2010) - 946) hx
    exact hright x (by simp only [Set.mem_ofPred_eq] at this; omega)

/-- **After the start of the increment, the increment thread is in module `r`.** -/
theorem isep2_IMov_late (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {R0 : RegS}
    (hR : R0.Ready) : ∀ j : ℕ, ((incPlan p i r).Tg : ℤ) + 946 < 2010 + j →
      isep2IMov (incPlan p i r) R0 j ⊆ {x | U p r - 738 ≤ x.1 - x.2} := by
  intro j hj
  have hv := incPlan_valid hp hins
  have hR1 := le_routeEndX _ _ 2010 hv.timedR
  have hR2 := hv.endR
  have hM1 := le_routeEndX _ _ _ hv.timedM
  have hM2 := hv.endM
  have hT1 : (incPlan p i r).T1 = (incPlan p i r).T0l + (134 + (incPlan p i r).tl * 254) := rfl
  have heM : (incPlan p i r).eM = routeEndX (incPlan p i r).gM (incPlan p i r).csM
    (incPlan p i r).T1 := rfl
  have h1 : ¬ j ≤ (incPlan p i r).Tg - 2010 := by omega
  have h2 : ¬ j - ((incPlan p i r).Tg - 2010) ≤ 946 := by omega
  unfold isep2IMov
  simp only [h1, h2, ↓reduceIte]
  exact isep2_evolve_u p r (R := (R0.later ((incPlan p i r).Tg - 2010)).later 946)
    ((hR.later ((incPlan p i r).Tg - 2010)).later 946) (j - ((incPlan p i r).Tg - 2010) - 946)

/-! ### The field `threads` -/

/-- **The moving parts of the two threads are far apart at every generation.** -/
theorem isep2_cross (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {R0 : RegS}
    (hR : R0.Ready) : ∀ j < (incPlan p i r).Tend - 2010,
      FarApart 2 (isep2CMov (incPlan p i r) j) (isep2IMov (incPlan p i r) R0 j) := by
  intro j hj
  by_cases h : ((2010 : ℕ) : ℤ) + j ≤
      meetT (route (unitWL p i incDWL) (isep2C3 p i r)).2 (isep2C4 p i) - 20
  · exact (isep2_SJ hp hins).mono (isep2_CMov_S hp hins j h) (isep2_IMov_J hp hins hR j hj)
  · have hm := isep2_m4C hp hins
    have h1 := isep2_CMov_U hp hins j hj
    have h2 := isep2_IMov_late hp hins hR j (by push_cast at h; omega)
    have hi1 := succ_lt_of_inc hp hins
    have htc := incTc_range hp hins
    have htcN : ((incPlan p i r).tc : ℤ) = incTc p i := Int.toNat_of_nonneg htc.1
    have hD := one_le_D p
    have hgap := entry_module_gap p (a := i + 1) (r := r) (t := (incPlan p i r).tc)
      (by unfold N R; push_cast; have := one_le_R p; omega) (by rw [htcN]; exact htc.2)
    intro x hx y hy ⟨n1, n2, n3, n4⟩
    have := h1 hx
    have := h2 hy
    simp only [Set.mem_ofPred_eq] at *
    push_cast at n1 n2 n3 n4
    omega

/-- **`IncSep.threads`**: the two threads are far apart at every generation. -/
theorem isep2_threads (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {R0 : RegS}
    (hR : R0.Ready) : ∀ j < (incPlan p i r).Tend - 2010,
      FarApart 2 ((incPlan p i r).contFoot j) ((incPlan p i r).incFoot R0 j) := by
  intro j hj
  refine FarApart.mono (A := boxesOf (dd (incPlan p i r).LCraw) ∪ isep2CMov (incPlan p i r) j)
    (B := boxesOf (dd (incPlan p i r).LIraw) ∪ isep2IMov (incPlan p i r) R0 j) ?_
    (isep2_contFoot_eq _ j).le (isep2_incFoot_sub _ R0 j)
  refine FarApart.union_left (FarApart.union_right ?_ ?_)
    (FarApart.union_right ?_ (isep2_cross hp hins hR j hj))
  · refine farApart_boxesOf fun h hh => FarApart.symm' (farApart_boxesOf fun g hg => ?_)
    exact FarApart.symm' (isep2_static hp hins g (mem_dd.1 hg) h (mem_dd.1 hh))
  · refine FarApart.symm' (farApart_boxesOf fun g hg => ?_)
    exact isep2_IMov_far hp hins hR j hj g (isep2_LC_mem hp hins g (mem_dd.1 hg))
      (isep2_LC_not_LI hp hins (mem_dd.1 hg))
  · refine farApart_boxesOf fun h hh => ?_
    exact isep2_CMov_far hp hins j hj h (isep2_LI_mem hp hins h (mem_dd.1 hh))
      (fun hc => isep2_LC_not_LI hp hins hc (mem_dd.1 hh))

end LP

end LeanTheory.Life
