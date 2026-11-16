/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepA4

/-!
# The fields `nQN` and `nQF` of `DecSep`

Research note `N-22`. Before the capture of an NZ activation, the control, the register run and the
answer (`qFootN`) are far from `KNZ` (its reflectors, station `j` and its footprint), and all of
them are far from the pieces of the answer link (the reflectors of the answer and the entry copies
of unit `i + 1`). The proofs compare hulls (`DecSepA3`, `DecSepA4`):

* the control runs in the inner loop of the sub-band of instruction `i` (slot `1`), `KNZ` in the
  outer loop (slot `0`), whose port column is `≥ 186` left of the port column of `C`;
* everything inside the module (`dsepAMHat`) is right of the left zone and above `v = 670` or in the
  lanes, while `KNZ` reaches the module on its port line `v = 1256 + 144 j`, left of the lanes,
  and approaches station `j` in the tight boxes of `dsepA_winN_foot`;
* the reflectors of the answer lie on the tracks of slot `3` (`v ∈ T₀ + [163, 400]`), at its port
  `(cd_A, 1325 + 144 j)` (`cd_A` one channel left of the channel of `KNZ`) or at the unit row.

`dsepA_nQN`, `dsepA_nQF`: the fields, verbatim.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Tools -/

/-- **Far apart from hulls**: two sets whose cells satisfy predicates forcing a gap of `3` in `x` or
in `y`. -/
theorem dsepA_far {A B : Set Cell} {PA PB : Cell → Prop} (hA : ∀ a ∈ A, PA a)
    (hB : ∀ b ∈ B, PB b)
    (h : ∀ a b, PA a → PB b → a.1 + 3 ≤ b.1 ∨ b.1 + 3 ≤ a.1 ∨ a.2 + 3 ≤ b.2 ∨ b.2 + 3 ≤ a.2) :
    FarApart 2 A B := by
  intro a ha b hb ⟨n1, n2, n3, n4⟩
  have := h a b (hA a ha) (hB b hb)
  push_cast at n1 n2 n3 n4
  omega

/-- **The numbers of the NZ answer link.** -/
theorem dsepA_layAN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    U p r + nzAnsChan p (callerIdx p r i) =
      U p r - 918 - 124 * D p - 124 * ((callerIdx p r i : ℕ) : ℤ) ∧
    nzAnsPortV (callerIdx p r i) = 1325 + 144 * ((callerIdx p r i : ℕ) : ℤ) ∧
    trackOut p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i)) =
      VT p + 660 * instrBand i + 187 ∧
    trackBack p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i)) =
      VT p + 660 * instrBand i + 373 ∧
    HI p + 241 ≤ hairReg p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i)) ∧
    hairReg p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i)) ≤ HI p + 270 ∧
    A p i + 364 + 58 * P p ≤ destU p (i + 1) (decTN p i r) ∧
    destV p (decTN p i r) ≤ VU p + 76 ∧ A p ((i + 1 : ℕ) : ℤ) = A p i + 540 + 180 * P p := by
  have hU := U_mod p r
  have ht := decTN_range hp hi
  have hC := unitC0_cases p (i + 1)
  have he : 0 ≤ decEA p i r ∧ decEA p i r ≤ 14 := solveE_bounds _ _ _
  have hf := fixp_bounds (HI p + 90 * 3 - 2 * decEA p i r)
    ((U p r + nzAnsChan p (callerIdx p r i)) % 2)
  have hA1 : A p ((i + 1 : ℕ) : ℤ) = A p i + 540 + 180 * P p := by
    push_cast; rw [A_succ]; unfold PU; ring
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hA1⟩
  · simp only [nzAnsChan, leftChan, fixp, uL, nzAnsPortV]; omega
  · simp only [trackOut, track, nzAnsChan, leftChan, fixp, uL, nzAnsPortV]; omega
  · simp only [trackBack, track, nzAnsChan, leftChan, fixp, uL, nzAnsPortV]; omega
  · unfold hairReg; omega
  · unfold hairReg; omega
  · unfold destU inCol; rw [hA1]; omega
  · simp only [destV, sideV]; omega

/-- The cells of the pieces of the `KNZ` thread: its reflectors and station `j`. -/
theorem dsepA_LNu_cells : ∀ g ∈ decLNu p i r, ∀ x ∈ g.box,
    (dsepACB (A p i + decL) (trackOut p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
      (trackOut p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
      (trackBack p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (U p r + nzTokChan p (callerIdx p r i)) (trackBack p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (U p r + nzTokChan p (callerIdx p r i)) (nzTokPortV (callerIdx p r i)) x) ∨
    ((380 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
      x.1 ≤ 412 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
      829 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
      x.2 ≤ 919 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ)) ∨
    (431 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
      x.1 ≤ 439 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
      891 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
      x.2 ≤ 913 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ)) ∨
    (464 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 ∧
      x.1 ≤ 467 + modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ∧
      820 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.2 ∧
      x.2 ≤ 823 + modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ))) := by
  intro g hg x hx
  simp only [decLNu, mem_dd, List.mem_append] at hg
  rcases hg with hg | hg
  · exact Or.inl (dsepA_LN_cells hg hx)
  · exact Or.inr (dsepA_sjN_cells hg hx)

/-- The cells of the pieces of the NZ answer link: its reflectors and the entry copies of unit
`i + 1`. -/
theorem dsepA_LF0N_cells : ∀ g ∈ decLF0N p i r, ∀ x ∈ g.box,
    (dsepACB (U p r + nzAnsChan p (callerIdx p r i)) (nzAnsPortV (callerIdx p r i)) x ∨
    dsepACB (U p r + nzAnsChan p (callerIdx p r i))
      (trackOut p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))) x ∨
    dsepACB (hairReg p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i)))
      (trackOut p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))) x ∨
    dsepACB (hairReg p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i)))
      (trackBack p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))) x ∨
    dsepACB (destU p (i + 1) (decTN p i r))
      (trackBack p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))) x ∨
    dsepACB (destU p (i + 1) (decTN p i r)) (destV p (decTN p i r)) x) ∨
    (A p ((i + 1 : ℕ) : ℤ) - 32 ≤ x.1 - x.2 ∧ x.1 + x.2 ≤ VU p + 122) := by
  intro g hg x hx
  simp only [decLF0N, mem_dd, List.mem_append] at hg
  rcases hg with hg | hg
  · exact Or.inl (dsepA_LAN_cells hg hx)
  · exact Or.inr (dsepA_E_cells hg hx)

/-! ### Against `KNZ` -/

/-- **The hull of the module is far from `KNZ`**: its pieces and its footprint before the
capture. -/
theorem dsepA_mh_N (hi : p[i]? = some (.decJz r z)) {X : Set Cell}
    (hX : ∀ x ∈ X, dsepAMHat p r x) {t : ℕ} (h0 : 4260 ≤ t) (h1 : t < decCapN p i r) :
    FarApart 2 X (boxesOf (decLNu p i r) ∪ tokFootN p i r t) := by
  obtain ⟨hO0, hB0, -, -, -, -, hcN, -, -, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdL : decL = -155 := rfl
  have hdR : decR = 127 := rfl
  refine dsepT_far_union_r (farApart_boxesOf fun g hg => ?_) ?_
  · refine dsepA_far hX (dsepA_LNu_cells g hg) fun a b ha hb => ?_
    simp only [dsepAMHat, dsepACB] at ha hb hcN hAU
    omega
  · refine dsepA_far hX (dsepA_tokN_hull hi h0 h1) fun a b ha hb => ?_
    simp only [dsepAMHat, dsepADown, Set.mem_ofPred_eq] at ha hb hcN hAU
    omega

/-- **The NZ stations `0 … j - 1` are far from `KNZ`.** -/
theorem dsepA_LSN_N (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (h1 : t < decCapN p i r) :
    FarApart 2 (boxesOf (decLSN p i r)) (boxesOf (decLNu p i r) ∪ tokFootN p i r t) := by
  obtain ⟨hO0, hB0, -, -, -, -, hcN, -, -, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdL : decL = -155 := rfl
  have hdR : decR = 127 := rfl
  refine FarApart.symm' (farApart_boxesOf fun g hg => ?_)
  refine FarApart.symm' (dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_)
  · refine dsepA_far (fun x hx => dsepA_LSN_cells hg hx) (dsepA_LNu_cells h hh) fun a b ha hb => ?_
    obtain ⟨k, hk0, hk1, ha⟩ := ha
    simp only [dsepACB] at hb hcN hAU
    omega
  · refine dsepA_far (fun x hx => dsepA_LSN_cells hg hx) (dsepA_tokN_hull hi h0 h1)
      fun a b ha hb => ?_
    obtain ⟨k, hk0, hk1, ha⟩ := ha
    simp only [dsepADown, Set.mem_ofPred_eq] at hb hcN hAU
    omega

/-- **The pieces of the control thread are far from `KNZ`.** -/
theorem dsepA_LC_N (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (h1 : t < decCapN p i r) :
    FarApart 2 (boxesOf (decLC p i r)) (boxesOf (decLNu p i r) ∪ tokFootN p i r t) := by
  obtain ⟨hO0, hB0, hO1, hB1, -, -, hcN, hcC, hvC, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdL : decL = -155 := rfl
  have hdR : decR = 127 := rfl
  have hm := decM_cast p hi
  refine FarApart.symm' (farApart_boxesOf fun g hg => ?_)
  refine FarApart.symm' (dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_)
  · refine dsepA_far (fun x hx => dsepA_LC_cells hg hx) (dsepA_LNu_cells h hh)
      fun a b ha hb => ?_
    rcases ha with ha | ha | ha | ha | ha | ⟨m, hm0, hm1, ha⟩ <;>
      simp only [dsepACB] at ha hb hcN hcC hAU <;> omega
  · refine dsepA_far (fun x hx => dsepA_LC_cells hg hx) (dsepA_tokN_hull hi h0 h1)
      fun a b ha hb => ?_
    simp only [dsepADown, Set.mem_ofPred_eq] at hb hcN hcC hAU
    rcases ha with ha | ha | ha | ha | ha | ⟨m, hm0, hm1, ha⟩ <;>
      (try simp only [dsepACB] at ha) <;> omega

/-- **The control before the register run is far from `KNZ`.** -/
theorem dsepA_C_N (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t ≤ decTS p i r) (h1 : t < decCapN p i r) :
    FarApart 2 (decFootC p i r t) (boxesOf (decLNu p i r) ∪ tokFootN p i r t) := by
  obtain ⟨hO0, hB0, hO1, hB1, -, -, hcN, hcC, hvC, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdL : decL = -155 := rfl
  have hdR : decR = 127 := rfl
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_
  · refine dsepA_far (dsepA_footC_hull hi h0 ht) (dsepA_LNu_cells h hh) fun a b ha hb => ?_
    simp only [dsepACB, dsepADown, Set.mem_ofPred_eq] at ha hb hcN hcC hAU
    omega
  · refine dsepA_far (dsepA_footC_hull hi h0 ht) (dsepA_tokN_hull hi h0 h1)
      fun a b ha hb => ?_
    simp only [dsepADown, Set.mem_ofPred_eq] at ha hb hcN hcC hAU
    omega

/-- **The NZ answer after the cut**: on its line `u = U_r - 391` below station `0`, then in the
footprints of the stations `0 … j - 1` it passes. -/
theorem dsepA_ansN_hull (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h1 : decCutN p i r ≤ t) :
    ∀ x ∈ decAnsFootN p i r t,
    (104 + modDX p r ≤ x.1 ∧ x.1 ≤ 397 + modDX p r ∧ 495 + modDY p r ≤ x.2 ∧
      x.2 ≤ 788 + modDY p r ∧ -398 ≤ x.1 - modDX p r - (x.2 - modDY p r) ∧
      x.1 - modDX p r - (x.2 - modDY p r) ≤ -384) ∨
    ∃ k : ℤ, 0 ≤ k ∧ k < ((callerIdx p r i : ℕ) : ℤ) ∧
      ((380 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 412 + modDX p r + 72 * k ∧
        829 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 919 + modDY p r + 72 * k) ∨
      (431 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 439 + modDX p r + 72 * k ∧
        891 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 913 + modDY p r + 72 * k) ∨
      (464 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 467 + modDX p r + 72 * k ∧
        820 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 823 + modDY p r + 72 * k) ∨
      (393 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 467 + modDX p r + 72 * k ∧
        784 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 859 + modDY p r + 72 * k ∧
        -394 ≤ x.1 - modDX p r - (x.2 - modDY p r) ∧ x.1 - modDX p r - (x.2 - modDY p r) ≤ -389))
    := by
  intro x hx
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  unfold decAnsFootN at hx
  split_ifs at hx with h2
  · left
    obtain ⟨x1, x2, x3, x4⟩ := hx
    simp only [decAnsWLN, modWL, ansNZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
    simp only [decCutN, decSt0N] at h1 h2
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

/-- **The NZ answer after the cut is far from `KNZ`.** -/
theorem dsepA_ans_N (hi : p[i]? = some (.decJz r z)) {t : ℕ} (hc : decCutN p i r ≤ t)
    (h1 : t < decCapN p i r) :
    FarApart 2 (decAnsFootN p i r t) (boxesOf (decLNu p i r) ∪ tokFootN p i r t) := by
  obtain ⟨hO0, hB0, -, -, -, -, hcN, -, -, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, -, -, hu1, hu2⟩ := dsepA_lay hi
  have hdL : decL = -155 := rfl
  have hdR : decR = 127 := rfl
  have h0 : 4260 ≤ t := by
    obtain ⟨-, -, h⟩ := decTS_facts p hi; unfold decCutN decTS at hc; omega
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_
  · refine dsepA_far (dsepA_ansN_hull hi hc) (dsepA_LNu_cells h hh) fun a b ha hb => ?_
    simp only [dsepACB] at hb
    rcases ha with ha | ⟨k, hk0, hk1, ha⟩ <;> omega
  · refine dsepA_far (dsepA_ansN_hull hi hc) (dsepA_tokN_hull hi h0 h1) fun a b ha hb => ?_
    simp only [dsepADown, Set.mem_ofPred_eq] at hb
    rcases ha with ha | ⟨k, hk0, hk1, ha⟩ <;> omega

/-- **`DecSep.nQN`**: before the capture, the control, the register run and the answer are far
from the pieces and the footprint of `KNZ`. -/
theorem dsepA_nQN (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decCapN p i r →
      FarApart 2 (qFootN p i r t) (boxesOf (decLNu p i r) ∪ tokFootN p i r t) := by
  intro t h0 h1
  unfold qFootN
  split_ifs with hA hB
  · rw [boxesOf_append]
    exact dsepT_far_union (dsepT_far_union
      (dsepA_mh_N hi (fun x hx => dsepA_grpLanes_mh x (Or.inl hx)) h0 h1) (dsepA_LSN_N hi h0 h1))
      (dsepT_far_union (dsepT_far_union (dsepA_LC_N hi h0 h1) (dsepA_C_N hi h0 hA h1))
        (dsepA_mh_N hi (fun x hx => dsepA_grpLanes_mh x (Or.inr hx)) h0 h1))
  · rw [boxesOf_append]
    exact dsepT_far_union (dsepT_far_union (dsepA_LC_N hi h0 h1) (dsepA_LSN_N hi h0 h1))
      (dsepA_mh_N hi (dsepA_modImg_mh dsepA_runNZ_mh) h0 h1)
  · exact dsepT_far_union (dsepA_LC_N hi h0 h1) (dsepT_far_union
      (dsepA_mh_N hi (dsepA_restN_mh t) h0 h1)
      (dsepT_far_union (dsepA_LSN_N hi h0 h1) (dsepA_ans_N hi (by omega) h1)))

/-! ### Against the answer link -/

/-- **The hull of the module is far from the pieces of the NZ answer link.** -/
theorem dsepA_mh_F (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {X : Set Cell}
    (hX : ∀ x ∈ X, dsepAMHat p r x) : ∀ g ∈ decLF0N p i r, FarApart 2 X g.box := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hcA, hvA, hOA, hBA, hHA1, hHA2, hdU, hdV, hA1⟩ := dsepA_layAN hp hi
  intro g hg
  refine dsepA_far hX (dsepA_LF0N_cells g hg) fun a b ha hb => ?_
  simp only [dsepAMHat, dsepACB] at ha hb
  omega

/-- **The NZ stations `0 … j - 1` are far from the pieces of the NZ answer link.** -/
theorem dsepA_LSN_F (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLF0N p i r, FarApart 2 (boxesOf (decLSN p i r)) g.box := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hcA, hvA, hOA, hBA, hHA1, hHA2, hdU, hdV, hA1⟩ := dsepA_layAN hp hi
  intro g hg
  refine FarApart.symm' (farApart_boxesOf fun h hh => ?_)
  refine dsepA_far (dsepA_LF0N_cells g hg) (fun x hx => dsepA_LSN_cells hh hx)
    fun a b ha hb => ?_
  obtain ⟨k, hk0, hk1, hb⟩ := hb
  simp only [dsepACB] at ha
  omega

/-- **The pieces of the control thread are far from the pieces of the NZ answer link.** -/
theorem dsepA_LC_F (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLF0N p i r, FarApart 2 (boxesOf (decLC p i r)) g.box := by
  obtain ⟨hO0, hB0, hO1, hB1, -, -, hcN, hcC, hvC, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hcA, hvA, hOA, hBA, hHA1, hHA2, hdU, hdV, hA1⟩ := dsepA_layAN hp hi
  have hdR : decR = 127 := rfl
  have hm := decM_cast p hi
  intro g hg
  refine FarApart.symm' (farApart_boxesOf fun h hh => ?_)
  refine dsepA_far (dsepA_LF0N_cells g hg) (fun x hx => dsepA_LC_cells hh hx)
    fun a b ha hb => ?_
  simp only [dsepACB] at ha
  rcases hb with hb | hb | hb | hb | hb | ⟨m, hm0, hm1, hb⟩ <;>
    (try simp only [dsepACB] at hb) <;> omega

/-- **The control before the register run is far from the pieces of the NZ answer link.** -/
theorem dsepA_C_F (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t ≤ decTS p i r) : ∀ g ∈ decLF0N p i r, FarApart 2 (decFootC p i r t) g.box := by
  obtain ⟨hO0, hB0, hO1, hB1, -, -, hcN, hcC, hvC, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD,
    hD1, hA0, hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hcA, hvA, hOA, hBA, hHA1, hHA2, hdU, hdV, hA1⟩ := dsepA_layAN hp hi
  have hdR : decR = 127 := rfl
  intro g hg
  refine dsepA_far (dsepA_footC_hull hi h0 ht) (dsepA_LF0N_cells g hg) fun a b ha hb => ?_
  simp only [dsepACB, dsepADown, Set.mem_ofPred_eq] at ha hb
  omega

/-- **The NZ answer after the cut is far from the pieces of the NZ answer link.** -/
theorem dsepA_ans_F (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (hc : decCutN p i r ≤ t) : ∀ g ∈ decLF0N p i r, FarApart 2 (decAnsFootN p i r t) g.box := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hcA, hvA, hOA, hBA, hHA1, hHA2, hdU, hdV, hA1⟩ := dsepA_layAN hp hi
  intro g hg
  refine dsepA_far (dsepA_ansN_hull hi hc) (dsepA_LF0N_cells g hg) fun a b ha hb => ?_
  simp only [dsepACB] at hb
  rcases ha with ha | ⟨k, hk0, hk1, ha⟩ <;> omega

/-- **The pieces of `KNZ` are far from the pieces of the NZ answer link.** -/
theorem dsepA_LNu_F (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLF0N p i r, FarApart 2 (boxesOf (decLNu p i r)) g.box := by
  obtain ⟨hO0, hB0, -, -, -, -, hcN, -, -, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hcA, hvA, hOA, hBA, hHA1, hHA2, hdU, hdV, hA1⟩ := dsepA_layAN hp hi
  have hdL : decL = -155 := rfl
  have hdR : decR = 127 := rfl
  intro g hg
  refine FarApart.symm' (farApart_boxesOf fun h hh => ?_)
  refine dsepA_far (dsepA_LF0N_cells g hg) (dsepA_LNu_cells h hh) fun a b ha hb => ?_
  simp only [dsepACB] at ha hb
  omega

/-- **`KNZ` before its capture is far from the pieces of the NZ answer link.** -/
theorem dsepA_tok_F (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (h1 : t < decCapN p i r) :
    ∀ g ∈ decLF0N p i r, FarApart 2 (tokFootN p i r t) g.box := by
  obtain ⟨hO0, hB0, -, -, -, -, hcN, -, -, hvN, hHC, hHN, -, -, -, -, -, -, hj0, hjD, hD1, hA0,
    hHI, hP1, hAU, hT0, hT0', hVU, hu1, hu2⟩ := dsepA_lay hi
  obtain ⟨hcA, hvA, hOA, hBA, hHA1, hHA2, hdU, hdV, hA1⟩ := dsepA_layAN hp hi
  have hdL : decL = -155 := rfl
  have hdR : decR = 127 := rfl
  intro g hg
  refine dsepA_far (dsepA_tokN_hull hi h0 h1) (dsepA_LF0N_cells g hg) fun a b ha hb => ?_
  simp only [dsepACB, dsepADown, Set.mem_ofPred_eq] at ha hb
  omega

/-- **`DecSep.nQF`**: before the capture, the control, the register run, the answer and `KNZ`
are far from the pieces of the NZ answer link. -/
theorem dsepA_nQF (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decCapN p i r → ∀ g ∈ decLF0N p i r,
      FarApart 2 (qFootN p i r t ∪ (boxesOf (decLNu p i r) ∪ tokFootN p i r t)) g.box := by
  intro t h0 h1 g hg
  refine dsepT_far_union ?_
    (dsepT_far_union (dsepA_LNu_F hp hi g hg) (dsepA_tok_F hp hi h0 h1 g hg))
  unfold qFootN
  split_ifs with hA hB
  · rw [boxesOf_append]
    exact dsepT_far_union (dsepT_far_union
      (dsepA_mh_F hp hi (fun x hx => dsepA_grpLanes_mh x (Or.inl hx)) g hg)
      (dsepA_LSN_F hp hi g hg))
      (dsepT_far_union (dsepT_far_union (dsepA_LC_F hp hi g hg) (dsepA_C_F hp hi h0 hA g hg))
        (dsepA_mh_F hp hi (fun x hx => dsepA_grpLanes_mh x (Or.inr hx)) g hg))
  · rw [boxesOf_append]
    exact dsepT_far_union (dsepT_far_union (dsepA_LC_F hp hi g hg) (dsepA_LSN_F hp hi g hg))
      (dsepA_mh_F hp hi (dsepA_modImg_mh dsepA_runNZ_mh) g hg)
  · exact dsepT_far_union (dsepA_LC_F hp hi g hg) (dsepT_far_union
      (dsepA_mh_F hp hi (dsepA_restN_mh t) g hg)
      (dsepT_far_union (dsepA_LSN_F hp hi g hg) (dsepA_ans_F hp hi (by omega) g hg)))

end LP

end LeanTheory.Life
