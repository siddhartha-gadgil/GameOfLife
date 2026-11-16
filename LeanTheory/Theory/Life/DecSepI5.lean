/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepI4

/-!
# The idle fields of `DecSep`: the rest of the run and the end

Research note `N-22`. The footprint of the rest of the register run (`restFootN`, `restFootZ`)
is far from every piece outside the circuit (and the INC gate for the zero test); the footprint
of the end (`finFootN`, `finFootZ`: the capture at station `j`, the answer link with its route,
its flight and the entry chain of the next unit, the flight to the body input) is far from every
piece outside the pieces of the end (`decLFN`, `decLFZ`):

* `dsepI_restFootN_far`, `dsepI_restFootZ_far`;
* `dsepI_flyAN_far`, `dsepI_flyAZ_far`: the flights of the answers into their entry copies, up to
  `16` generations before the arrival (inclusive), far from every piece (`isep2_flyEntry`);
* `dsepI_finFootN_far`, `dsepI_finFootZ_far`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The rest of the run -/

/-- **The lanes of a register are far from every piece of the machine.** -/
theorem dsepI_lanes_far (hp : p.WellFormed) (r : ℕ) : dsepIFar p (modLanes p r) [] :=
  fun g hg _ => ((machPieces_laneClear hp r g hg).farApart).symm'

/-- **The rest of the NZ run** is far from every piece outside the circuit. -/
theorem dsepI_restFootN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) (t : ℕ) :
    dsepIFar p (restFootN p i r t) (modGroup p r) := by
  have hr := lt_numRegs_of_dec hi
  unfold restFootN
  split_ifs
  · exact dsepT_restNZ_far hp hr
  · exact fun g hg hn => dsepT_grpLanes_far hp hr hg hn

/-- **The rest of the Z run** is far from every piece outside the circuit and the INC gate. -/
theorem dsepI_restFootZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) (t : ℕ) :
    dsepIFar p (restFootZ p i r t) (modGroup p r ++ [gateP p r]) := by
  have hr := lt_numRegs_of_dec hi
  unfold restFootZ
  split_ifs
  · exact dsepT_restZ_far hp hr
  · exact fun g hg hn => dsepT_grpLanes_far hp hr hg fun h => hn (List.mem_append_left _ h)

/-! ### The answer links -/

/-- **The flight of the NZ answer into its entry copy**, up to `16` generations before its
arrival, is far from every piece of the machine. -/
theorem dsepI_flyAN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (decGN p i r) (decCsN p i r) (decDispN p i r) ≤ t)
    (h2 : t + 16 ≤ decT0N p i r) : dsepIFar p ((decFinN p i r).box t) [] := by
  intro h hh _
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
  change FarApart 2 ((route (decGN p i r) (decCsN p i r)).2.box t) h.box
  rw [e]
  exact this

/-- **The flight of the Z answer into its entry copy**, up to `16` generations before its
arrival, is far from every piece of the machine. -/
theorem dsepI_flyAZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) ≤ t)
    (h2 : t + 16 ≤ decT0Z p i r z) : dsepIFar p ((decFinZ p i r z).box t) [] := by
  intro h hh _
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
  change FarApart 2 ((route (decGZ p i r) (decCsZ p i r z)).2.box t) h.box
  rw [e]
  exact this

/-- The corners of the NZ answer have images below `8`. -/
theorem dsepI_csN_k : ∀ c ∈ decCsN p i r, c.k < 8 := by
  intro c hc
  simp only [decCsN, decMkN, nzAnsCorners, List.mem_cons] at hc
  rcases hc with rfl | hc
  · simp
  · exact upCornersK_k (by norm_num) c hc

/-- The corners of the Z answer have images below `8`. -/
theorem dsepI_csZ_k : ∀ c ∈ decCsZ p i r z, c.k < 8 := by
  intro c hc
  simp only [decCsZ, decMkZ, zAnsCorners, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · simp
  · simp
  · exact upCornersK_k (by norm_num) c hc

/-- **The NZ answer link** (route, flight, entry chain of unit `i + 1`) is far from every piece
of the machine outside the pieces of the end. -/
theorem dsepI_linkN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) (j : ℕ) :
    dsepIFar p (linkFootW p (i + 1) (decTNn p i r) (decGN p i r) (decCsN p i r)
      (decDispN p i r) (decT0N p i r) j) (decLFN p i r) := by
  obtain ⟨hD, -, -, -⟩ := decN_times hp hi
  obtain ⟨hlin, htim, -⟩ := decAnsN_plan hp hi _ hD
  unfold linkFootW
  split_ifs with h1 h2
  · exact (dsepI_route_far (dsep_sepAN hp hi) htim hlin dsepI_csN_k
      (by simp [decCsN, decMkN, nzAnsCorners]) h1).mono subset_rfl
      fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_append_right _ hx))
  · exact (dsepI_flyAN_far hp hi (by omega) h2).mono subset_rfl (by simp)
  · exact fun g hg hn => dsep_entAN hp hi g hg fun hm =>
      hn (mem_dd.2 (List.mem_append_right _ hm))

/-- **The Z answer link** (route, flight, entry chain of unit `z`) is far from every piece of the
machine outside the pieces of the end. -/
theorem dsepI_linkZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) (j : ℕ) :
    dsepIFar p (linkFootW p z (decTZn p i r z) (decGZ p i r) (decCsZ p i r z)
      (decDispZ p i r) (decT0Z p i r z) j) (decLFZ p i r z) := by
  obtain ⟨hD, -, -, -⟩ := decZ_times hp hi
  obtain ⟨hlin, htim, -⟩ := decAnsZ_plan hp hi _ hD
  unfold linkFootW
  split_ifs with h1 h2
  · exact (dsepI_route_far (dsep_sepAZ hp hi) htim hlin dsepI_csZ_k
      (by simp [decCsZ, decMkZ, zAnsCorners]) h1).mono subset_rfl
      fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_append_right _ hx))
  · exact (dsepI_flyAZ_far hp hi (by omega) h2).mono subset_rfl (by simp)
  · exact fun g hg hn => dsep_entAZ hp hi g hg fun hm =>
      hn (mem_dd.2 (List.mem_append_right _ hm))

/-! ### The end -/

/-- **The moving footprint of the end of an NZ activation** is far from every piece of the
machine outside the pieces of the end. -/
theorem dsepI_finFootN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCapN p i r ≤ t) (h2 : t < decEndN p i r) :
    dsepIFar p (finFootN p i r t) (decLFN p i r) := by
  unfold finFootN
  split_ifs with h3 h4
  · exact (dsepI_capN_far hp hi _ (by unfold decDispN at h3; unfold decCapN at h1 ⊢; omega)).mono
      subset_rfl fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_append_left _ hx))
  · exact dsepI_linkN_far hp hi _
  · intro g hg _
    unfold outFoot
    exact dsep_outAN hp (i := i) _ (by unfold decEndN at h2; omega) g hg

/-- **The moving footprint of the end of a Z activation** is far from every piece of the machine
outside the pieces of the end. -/
theorem dsepI_finFootZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCapZ p i r ≤ t) (h2 : t < decEndZ p i r z) :
    dsepIFar p (finFootZ p i r z t) (decLFZ p i r z) := by
  unfold finFootZ
  split_ifs with h3 h4
  · exact (dsepI_capZ_far hp hi _ (by unfold decDispZ at h3; unfold decCapZ at h1 ⊢; omega)).mono
      subset_rfl fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_append_left _ hx))
  · exact dsepI_linkZ_far hp hi _
  · intro g hg _
    unfold outFoot
    exact dsep_outAZ hp (z := z) _ (by unfold decEndZ at h2; omega) g hg

end LP

end LeanTheory.Life
