/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepI8

/-!
# The lanes of the other registers: the end of the activation

Research note `N-22`. The footprint of the end of a `decJz` activation (`finFootN`, `finFootZ`)
is clear of the lanes of every register `r' ≠ r`: the capture in the zone of module `r`; the
route of the answer by `RouteLane` (`lane_instrRoute`, the answer leaving its station beside the
lanes of `r'`, `dsepI_ansN_start`, `dsepI_ansZ_start`); the flight into the entry copy, the entry
chain and the flight to the body input low.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- **The NZ answer leaves its station beside the lanes of every other register.** -/
theorem dsepI_ansN_start (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) :
    ∀ c ∈ (decCsN p i r).head?, LaneStart p r' (decGN p i r) ((decDispN p i r : ℕ) : ℤ) c := by
  intro c hc
  obtain ⟨hD, -, -, -⟩ := decN_times hp hi
  have hj := dsepM_j_lt hi
  have hD1 := one_le_D p
  have hU := U_even p r
  simp only [decCsN, decMkN, nzAnsCorners, List.head?_cons, Option.mem_def,
    Option.some.injEq] at hc
  subst hc
  have hcl := fixp_bounds (uL - 62 * (2 * D p + 2 + 2 * (callerIdx p r i : ℤ)))
    (1 - nzAnsPortV (callerIdx p r i) % 2)
  unfold LaneStart
  simp only [WL.cu, WL.cv, decGN, modWL, nzAnsWL, WL.shift, WL.px, WL.py, WL.qt, nzAnsChan,
    leftChan, nzAnsPortV, uL, modDX, modDY] at hcl ⊢
  rcases lt_or_gt_of_ne hr with h | h
  · have := lane_U_gap p h
    right; right
    constructor <;> omega
  · have := lane_U_gap p h
    right; left
    constructor <;> omega

/-- **The Z answer leaves its station beside the lanes of every other register.** -/
theorem dsepI_ansZ_start (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) :
    ∀ c ∈ (decCsZ p i r z).head?, LaneStart p r' (decGZ p i r) ((decDispZ p i r : ℕ) : ℤ) c := by
  intro c hc
  obtain ⟨hD, -, -, -⟩ := decZ_times hp hi
  have hj := dsepM_j_lt hi
  have hD1 := one_le_D p
  have hU := U_even p r
  simp only [decCsZ, decMkZ, zAnsCorners, List.head?_cons, Option.mem_def,
    Option.some.injEq] at hc
  subst hc
  unfold LaneStart
  simp only [WL.cu, WL.cv, decGZ, modWL, zAnsWL, WL.shift, WL.px, WL.py, WL.qt, zAnsStation,
    modDX, modDY]
  rcases lt_or_gt_of_ne hr with h | h
  · have := lane_U_gap p h
    right; right
    constructor <;> omega
  · have := lane_U_gap p h
    right; left
    constructor <;> omega


/-- **The flight of the NZ answer into its entry copy is low.** -/
theorem dsepI_flyAN_low (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (decGN p i r) (decCsN p i r) (decDispN p i r) ≤ t)
    (h2 : t + 16 ≤ decT0N p i r) : ∀ x ∈ (decFinN p i r).box t, x.1 + x.2 ≤ VU p + 82 := by
  intro x hx
  obtain ⟨hD, -, hT0, -⟩ := decN_times hp hi
  obtain ⟨-, htim, hδ, hfin, -⟩ := decAnsN_plan hp hi _ hD
  have e := dsep_csN_eq hp hi
  change RouteTimedX (decGN p i r) (decCsN p i r) _ at htim
  change (route (decGN p i r) (decCsN p i r)).2 = _ at hfin
  change x ∈ (route (decGN p i r) (decCsN p i r)).2.box t at hx
  rw [e] at htim hfin h1 hx
  have := isep2_mem_flyEntry htim hδ hfin (T0 := decT0N p i r) (by rw [hT0]; rfl) h1 h2 hx
  omega

/-- **The flight of the Z answer into its entry copy is low.** -/
theorem dsepI_flyAZ_low (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) ≤ t)
    (h2 : t + 16 ≤ decT0Z p i r z) : ∀ x ∈ (decFinZ p i r z).box t, x.1 + x.2 ≤ VU p + 82 := by
  intro x hx
  obtain ⟨hD, -, hT0, -⟩ := decZ_times hp hi
  obtain ⟨-, htim, hδ, hfin, -⟩ := decAnsZ_plan hp hi _ hD
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  have e := dsep_csZ_eq hp hi
  change RouteTimedX (decGZ p i r) (decCsZ p i r z) _ at htim
  change (route (decGZ p i r) (decCsZ p i r z)).2 = _ at hfin
  change x ∈ (route (decGZ p i r) (decCsZ p i r z)).2.box t at hx
  rw [e] at htim hfin h1 hx
  have hT0' : (decT0Z p i r z : ℤ) = 180 + 30 * decKZ p i r z +
      16 * ((decTZn p i r z : ℕ) : ℤ) % 30 := by
    rw [hT0, htN]
  have := isep2_mem_flyEntry htim hδ hfin (T0 := decT0Z p i r z) (by rw [hT0']; rfl) h1 h2 hx
  omega

/-- **The NZ answer link is clear of the lanes of the other registers.** -/
theorem dsepI_linkN_lane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) (j : ℕ) :
    LaneClear p r' (linkFootW p (i + 1) (decTNn p i r) (decGN p i r) (decCsN p i r)
      (decDispN p i r) (decT0N p i r) j) := by
  have hV := lane_VT_low p
  obtain ⟨hD, -, -, -⟩ := decN_times hp hi
  obtain ⟨hlin, htim, -⟩ := decAnsN_plan hp hi _ hD
  unfold linkFootW
  split_ifs with h1 h2
  · have hRL := lane_instrRoute hp (List.getElem?_eq_some_iff.1 hi).1 (dsepM_specs hi).2.2.2.1
      (g := decGN p i r) ⟨Or.inr rfl, Or.inl rfl⟩ hlin r' (dsepI_ansN_start hp hi hr)
    obtain ⟨c, cs, hcs⟩ : ∃ c cs, decCsN p i r = c :: cs := ⟨_, _, rfl⟩
    change RouteTimedX (decGN p i r) (decCsN p i r) _ at htim
    rw [hcs] at hRL htim h1 ⊢
    exact dsepI_rfoot_lane cs c _ _ hRL htim j h1
  · exact laneClear_of_low fun x hx => by
      have := dsepI_flyAN_low hp hi (by omega) h2 x hx
      omega
  · exact laneClear_of_low fun x hx => by
      have := lane_entryFoot_low p (i + 1) (decTNn p i r) x hx
      omega

/-- **The Z answer link is clear of the lanes of the other registers.** -/
theorem dsepI_linkZ_lane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) (j : ℕ) :
    LaneClear p r' (linkFootW p z (decTZn p i r z) (decGZ p i r) (decCsZ p i r z)
      (decDispZ p i r) (decT0Z p i r z) j) := by
  have hV := lane_VT_low p
  obtain ⟨hD, -, -, -⟩ := decZ_times hp hi
  obtain ⟨hlin, htim, -⟩ := decAnsZ_plan hp hi _ hD
  unfold linkFootW
  split_ifs with h1 h2
  · have hRL := lane_instrRoute hp (List.getElem?_eq_some_iff.1 hi).1
      (dsepM_specs hi).2.2.2.2 (g := decGZ p i r) ⟨Or.inl rfl, Or.inl rfl⟩ hlin r'
      (dsepI_ansZ_start hp hi hr)
    obtain ⟨c, cs, hcs⟩ : ∃ c cs, decCsZ p i r z = c :: cs := ⟨_, _, rfl⟩
    change RouteTimedX (decGZ p i r) (decCsZ p i r z) _ at htim
    rw [hcs] at hRL htim h1 ⊢
    exact dsepI_rfoot_lane cs c _ _ hRL htim j h1
  · exact laneClear_of_low fun x hx => by
      have := dsepI_flyAZ_low hp hi (by omega) h2 x hx
      omega
  · exact laneClear_of_low fun x hx => by
      have := lane_entryFoot_low p z (decTZn p i r z) x hx
      omega

/-- **The end of an NZ activation is clear of the lanes of the other registers.** -/
theorem dsepI_finFootN_lane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) {t : ℕ} (h1 : decCapN p i r ≤ t) (h2 : t < decEndN p i r) :
    LaneClear p r' (finFootN p i r t) := by
  have hV := lane_VT_low p
  unfold finFootN
  split_ifs with h3 h4
  · exact dsepI_capN_lane hi hr _ (by unfold decDispN at h3; unfold decCapN at h1 ⊢; omega)
  · exact dsepI_linkN_lane hp hi hr _
  · exact laneClear_of_low fun x hx => by
      have := lane_chainOut_low p (i + 1) (t := -166 + ((t - (decT0N p i r +
        (134 + decTNn p i r * 254)) : ℕ) : ℤ)) (by unfold decEndN at h2; omega) x hx
      omega

/-- **The end of a Z activation is clear of the lanes of the other registers.** -/
theorem dsepI_finFootZ_lane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {r' : ℕ}
    (hr : r' ≠ r) {t : ℕ} (h1 : decCapZ p i r ≤ t) (h2 : t < decEndZ p i r z) :
    LaneClear p r' (finFootZ p i r z t) := by
  have hV := lane_VT_low p
  unfold finFootZ
  split_ifs with h3 h4
  · exact dsepI_capZ_lane hi hr _ (by unfold decDispZ at h3; unfold decCapZ at h1 ⊢; omega)
  · exact dsepI_linkZ_lane hp hi hr _
  · exact laneClear_of_low fun x hx => by
      have := lane_chainOut_low p z (t := -166 + ((t - (decT0Z p i r z +
        (134 + decTZn p i r z * 254)) : ℕ) : ℤ)) (by unfold decEndZ at h2; omega) x hx
      omega
end LP

end LeanTheory.Life
