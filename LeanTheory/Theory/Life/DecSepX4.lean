/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepX3

/-!
# The module parts of the main threads, and the NZ answer after its dispatch

Research note `N-22`. For the fields `nThr`, `zThr` and `zGate` of `DecSep`:

* `dsepXH`: a hull of the regions of the register runs (module frame): every component of the
  regions before and after the cut lies in it (`dsepX_runNZ_H`, `dsepX_restNZ_H`, `dsepX_runZ_H`,
  `dsepX_restZ_H`), so their images at module `r` lie in the module parts `dsepXMR`, `dsepXMZ`;
* the lanes, the answers on their lines and at the stations, and the captures lie in the module
  parts;
* `dsepX_restZ_gate`: the rest of the zero test is far from the tight footprint of the INC gate;
* `dsepX_finN_late`: after its dispatch the NZ answer link is left of `u = U_r - 300`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### A hull of the regions of the register runs -/

/-- **A hull of the regions of the register runs** (module frame): `u ∈ [-760, 830]`,
`v ≥ -2420`, and below `v = 730` or right of `u = -113` (the lanes). -/
def dsepXH : Set Cell :=
  {x | -760 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ 830 ∧ -2420 ≤ x.1 + x.2 ∧
    (x.1 + x.2 ≤ 730 ∨ -113 ≤ x.1 - x.2)}

/-- A component of a region in the hull. -/
theorem dsepX_BU_H {a b lo hi U₁ U₂ V₁ V₂ : ℤ} (h1 : -760 ≤ U₁ ∨ -760 ≤ a - hi)
    (h2 : U₂ ≤ 830 ∨ b - lo ≤ 830) (h3 : -2420 ≤ V₁ ∨ -2420 ≤ a + lo)
    (h4 : V₂ ≤ 730 ∨ b + hi ≤ 730) : BU a b lo hi U₁ U₂ V₁ V₂ ⊆ dsepXH := by
  rintro x ⟨⟨x1, x2, x3, x4⟩, x5, x6, x7, x8⟩
  simp only [dsepXH, Set.mem_ofPred_eq]
  omega

/-- The lanes of the register diagonal lie in the hull. -/
theorem dsepX_lanes_H : regLanes ⊆ dsepXH := by
  rintro x ⟨x1, x2, x3⟩
  simp only [dsepXH, Set.mem_ofPred_eq]
  omega

/-- All components of a list in the hull. -/
macro "dsepX_hull" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals first
    | exact dsepX_BU_H (by omega) (by omega) (by omega) (by omega)
    | exact dsepX_lanes_H
    | trivial))

/-- The components of the NZ run regions before the cut lie in the hull. -/
theorem dsepX_runNZ_H : decRunRegNZ ⊆ dsepXH := by
  unfold decRunRegNZ
  refine unionL_subset_dec ?_
  simp only [DecAllSub]
  refine ⟨unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_,
    unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_,
    unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_, trivial⟩ <;>
  simp only [dz2dPreRegL, dz2d1PreRegL, dz2d2PreRegL, dz2d3PreRegL, dz2mk1PreRegL,
    dz2mk2PreRegL, dz2mk3PreRegL, dz2mk4PreRegL, dz2mk5PreRegL, dz2mk6PreRegL, dz2mk7PreRegL,
    DecAllSub] <;>
  dsepX_hull

/-- The components of the NZ rest regions lie in the hull. -/
theorem dsepX_restNZ_H : decRestRegNZ ⊆ dsepXH := by
  unfold decRestRegNZ
  refine unionL_subset_dec ?_
  simp only [DecAllSub]
  refine ⟨unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_,
    unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_,
    unionL_subset_dec ?_, unionL_subset_dec ?_, unionL_subset_dec ?_, trivial⟩ <;>
  simp only [dz2dRestRegL, dz2d1RestRegL, dz2d2RestRegL, dz2d3RestRegL, dz2mk1RestRegL,
    dz2mk2RestRegL, dz2mk3RestRegL, dz2mk4RestRegL, dz2mk5RestRegL, dz2mk6RestRegL,
    dz2mk7RestRegL, DecAllSub] <;>
  dsepX_hull

/-- The components of the Z run region before the cut lie in the hull. -/
theorem dsepX_runZ_H : decRunRegZ ⊆ dsepXH := by
  refine unionL_subset_dec ?_
  simp only [dz2mk0PreRegL, DecAllSub]
  dsepX_hull

/-- The components of the Z rest region lie in the hull. -/
theorem dsepX_restZ_H : dz2mk0RestRegion ⊆ dsepXH := by
  refine unionL_subset_dec ?_
  simp only [dz2mk0RestRegL, DecAllSub]
  dsepX_hull

/-- The hull placed at module `r` lies in the module parts of both threads. -/
theorem dsepX_modImg_H {S : Set Cell} (hS : S ⊆ dsepXH) :
    modImg p r S ⊆ dsepXMR p r ∩ dsepXMZ p r := by
  have hu := modD_uv p r
  rintro _ ⟨c, hc, rfl⟩
  have := hS hc
  simp only [dsepXH, dsepXMR, dsepXMZ, Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.fst_add,
    Prod.snd_add] at this ⊢
  omega

/-- The lanes of register `r` lie in the module parts of both threads. -/
theorem dsepX_lanes_M : modLanes p r ⊆ dsepXMR p r ∩ dsepXMZ p r := by
  have hu := modD_uv p r
  rintro _ ⟨c, ⟨c1, c2, c3⟩, rfl⟩
  simp only [dsepXMR, dsepXMZ, Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
  omega

/-! ### The rest of the zero test beside the INC gate -/

/-- **The rest of the zero test is far from the tight footprint of the INC gate.** -/
theorem dsepX_restZ_gate : FarApart 2 (modImg p r dz2mk0RestRegion) (gateFoot p r) := by
  have h1 : FarApart 2 dz2mk0RestRegion (Box (-1132) (-1042) (-1291) (-1272)) := by
    refine farApart_unionL ?_
    simp only [dz2mk0RestRegL, FarAll]
    dsepT_fa
  have h2 : FarApart 2 dz2mk0RestRegion (Box (-1132) (-1073) (-1291) (-1259)) := by
    refine farApart_unionL ?_
    simp only [dz2mk0RestRegL, FarAll]
    dsepT_fa
  have hu := modD_uv p r
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ hn
  obtain ⟨n1, n2, n3, n4⟩ := hn
  simp only [Prod.fst_add, Prod.snd_add] at n1 n2 n3 n4
  rcases hc with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩
  · refine h1 a ha (c + (-1132, -1291)) ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> omega
  · refine h2 a ha (c + (-1132, -1291)) ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-! ### The answers and the captures in the module parts -/

/-- **The NZ answer on its line and at the stations** lies in the module part of the NZ thread. -/
theorem dsepX_ansN_M (hi : p[i]? = some (.decJz r z)) {t : ℕ} (ht : decCutN p i r ≤ t) :
    decAnsFootN p i r t ⊆ dsepXMR p r := by
  have hu := modD_uv p r
  intro x hx
  unfold decAnsFootN at hx
  split_ifs at hx with h
  · obtain ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩ := dsepT_ansN_sub hi ht hx
    simp only [dsepXMR, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
    omega
  · obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨k, hk, -, c1, c2, c3, c4⟩ := dsepT_chainNZ_hull hc
    simp only [dsepXMR, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
    omega

/-- **The Z answer on its line and at the stations** lies in the module part of the Z thread. -/
theorem dsepX_ansZ_M (hi : p[i]? = some (.decJz r z)) {t : ℕ} (ht : decCutZ p i r ≤ t) :
    decAnsFootZ p i r t ⊆ dsepXMZ p r ∩ {x | 460 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 730} := by
  have hu := modD_uv p r
  intro x hx
  unfold decAnsFootZ at hx
  split_ifs at hx with h
  · obtain ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩ := dsepT_ansZ_sub hi ht hx
    simp only [dsepXMZ, Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
    omega
  · obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨k, hk, -, c1, c2, c3, c4⟩ := dsepT_chainZ_hull hc
    simp only [dsepXMZ, Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
    omega

/-- **The capture at station `j` of the line NZ** lies in the module part of the NZ thread, left of
`u = U_r - 317` and above `v = 1160`. -/
theorem dsepX_capN_M (hi : p[i]? = some (.decJz r z)) {k : ℕ} (hk : k ≤ 692) :
    (conway.evolve k (decCapStartN p i r) : Set Cell) ⊆
      dsepXMR p r ∩ {x | x.1 - x.2 ≤ U p r - 317 ∧ 1160 ≤ x.1 + x.2} := by
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hc := decCap_cast p hi
  intro x hx
  have := dsepM_image_box ((stationNZ_captureE p r (callerIdx p r i) (decShift p i r)
    (decShift_mod p i r) (decCapN p i r) hc.1).subset k (by omega) hx)
  simp only [dsepXMR, Set.mem_inter_iff, Set.mem_ofPred_eq] at this ⊢
  omega

/-- **The capture at station `j` of the line Z** lies in the module part of the Z thread, right of
`u = U_r + 1138`, with `v ∈ [469, 722]`. -/
theorem dsepX_capZ_M (hi : p[i]? = some (.decJz r z)) {k : ℕ} (hk : k ≤ 672) :
    (conway.evolve k (decCapStartZ p i r) : Set Cell) ⊆
      dsepXMZ p r ∩ {x | U p r + 1138 ≤ x.1 - x.2 ∧ 469 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 722} := by
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hc := decCap_cast p hi
  intro x hx
  have := dsepM_image_box ((stationZ_captureE p r (callerIdx p r i) (decShift p i r)
    (decShift_mod p i r) (decCapZ p i r) hc.2).subset k (by omega) hx)
  simp only [dsepXMZ, Set.mem_inter_iff, Set.mem_ofPred_eq] at this ⊢
  omega

/-! ### The NZ answer link after its dispatch -/

/-- **After its dispatch, the NZ answer link is left of `u = U_r - 300`**: its route (corners in
the left zone, the band and unit `i + 1`), its flight to the entry copy, the entry chain and the
flight to the body input of unit `i + 1`. -/
theorem dsepX_finN_late (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decDispN p i r < t) (h2 : t < decEndN p i r) :
    finFootN p i r t ⊆ {x | x.1 - x.2 ≤ U p r - 300} := by
  have hl : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have h1' := succ_lt_of_dec hp hi
  have hR := one_le_R p
  have hgap := unit_module_gap p (a := ((i + 1 : ℕ) : ℤ)) (r := r)
    ⟨by omega, by unfold N; push_cast; omega⟩ (by omega)
  have hs := slabR_ge_rs p
  have hAU := dsepX_AU hi
  have hAn : 0 ≤ A p ((i + 1 : ℕ) : ℤ) := A_nonneg p (by omega)
  obtain ⟨hD, -, hT0, -⟩ := decN_times hp hi
  obtain ⟨hlin, htim, hδ, hfin, -⟩ := decAnsN_plan hp hi _ hD
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  have e := dsep_csN_eq hp hi
  have hu := modD_uv p r
  have hU := U_even p r
  have hj := dsepM_j_lt hi
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  intro x hx
  simp only [Set.mem_ofPred_eq]
  unfold finFootN at hx
  split_ifs at hx with ha hb
  · omega
  · unfold linkFootW at hx
    split_ifs at hx with hc hd
    · -- the route
      have hcl := leftChan_in_extent p (idx := 2 * D p + 2 + 2 * (callerIdx p r i))
        (v := nzAnsPortV (callerIdx p r i)) ⟨by omega, by omega⟩
      have hH := hairReg_le p (s := 3) (e := decEA p i r)
        (c := U p r + nzAnsChan p (callerIdx p r i)) (by norm_num)
        (solveE_bounds _ _ _).1
      have hHI := layout_facts p
      have hC := unitC0_cases p (i + 1)
      obtain ⟨g1, g2, g3⟩ := decGN_dir p i r
      refine (dsepX_route_uhigh (U p r - 300) (decCsN p i r) (decGN p i r) (decDispN p i r)
        ⟨Or.inr g1, Or.inl g2⟩ hlin htim (fun c hc' => ?_) ?_).1 _ hc x hx
      · rw [e] at hc'
        simp only [bandCorners, isep2SlabC, List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hc'
        have hcl2 : nzAnsChan p (callerIdx p r i) ≤ -793 := hcl.2
        rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [destU, inCol, modLeft, hairReg] at * <;> omega
      · simp only [WL.uHi, decGN, modWL, nzAnsWL, WL.shift, WL.px, WL.py, WL.qt, modDX, modDY]
        simp only [decDispN]
        push_cast
        omega
    · -- the flight to the entry copy
      have et : ((decDispN p i r : ℕ) : ℤ) + ((t - decDispN p i r : ℕ) : ℤ) = ((t : ℕ) : ℤ) := by
        omega
      rw [et] at hx
      have htim' : RouteTimedX (decGN p i r) (decCsN p i r) (decDispN p i r) := htim
      have hfin' : (route (decGN p i r) (decCsN p i r)).2 = _ := hfin
      rw [e] at htim' hfin' hx hc
      have := isep2_mem_flyEntry (a := i + 1) (t := decTNn p i r) htim' hδ hfin'
        (T0 := decT0N p i r) (by rw [hT0]; rfl) (j := t) (by omega) (by omega) hx
      have hP := one_le_P p
      omega
    · -- the entry chain
      have := isep2_entryFoot_xy hx
      have hP := one_le_P p
      omega
  · -- the flight to the body input
    unfold outFoot at hx
    have := isep2_mem_outC p (i + 1) (j := t - (decT0N p i r + (134 + decTNn p i r * 254)))
      (by unfold decEndN at h2; omega) hx
    omega

end LP

end LeanTheory.Life
