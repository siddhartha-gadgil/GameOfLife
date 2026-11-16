/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepI2

/-!
# The idle fields of `DecSep`: the tokens

Research note `N-22`. The moving footprints of the tokens `KNZ` and `KZ` (`tokFootN`, `tokFootZ`)
and of the unpaired tokens (`unpFootN`, `unpFootZ`) are far from every piece of the machine
outside the thread of the token (`decLNu`, `decLZu`):

* `dsepI_flyN_far`: `KNZ` on the port line `v = 1256 + 144 j`, left of station `j`: far from
  the stations (station `j` in `x`, the others in `v`), the corners of the left zone (its own port
  corner by `dsepM_final_far`, the others by their port lines);
* `dsepI_flyZ_far`: `KZ` on the station column `u = U_r + 1230 + 144 j`: far from the stations
  `j' ≠ j` and from the corners of the right zone in `u` (its own station corner by
  `dsepM_final_far`);
* `dsepI_tokFootN_far`, `dsepI_tokFootZ_far`, `dsepI_unpFootN_far`, `dsepI_unpFootZ_far`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The token `KNZ` -/

/-- **The flight of `KNZ` in coordinates**: on its port line, right of the left end of the
module, left of station `j`. -/
theorem dsepI_flyN_mem (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ≤ t)
    (h2 : t ≤ decCapN p i r - 90) {x : Cell} (hx : x ∈ (decTokN p i r).box t) :
    U p r - 811 - 248 * D p ≤ x.1 - x.2 ∧
      x.1 ≤ modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) + 367 ∧
      1252 + 144 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 + x.2 ∧
      x.1 + x.2 ≤ 1262 + 144 * ((callerIdx p r i : ℕ) : ℤ) := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  have hu := modD_uv p r
  have hUe := U_even p r
  have hc := (decCap_cast p hi).1
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have h90 : 90 ≤ decCapN p i r := by unfold decCapN; omega
  have h := routeEndX_snoc _ ⟨4, U p r + nzTokChan p (callerIdx p r i),
    nzTokPortV (callerIdx p r i), .left r (2 * D p + 1 + 2 * (callerIdx p r i))⟩
    (unitWL p i decLWL) 4260 (decKNZ_timedX p hi)
  change (routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 : ℤ) =
    (route (unitWL p i decLWL) (decCornN p i r)).2.tau - _ + _ - _ at h
  rw [decKNZ_target] at h
  have hcl := fixp_bounds (uL - 62 * (2 * D p + 1 + 2 * (callerIdx p r i : ℤ)))
    (1 - nzTokPortV (callerIdx p r i) % 2)
  have ht1 : (routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 : ℤ) ≤ t := by exact_mod_cast h1
  have ht2 : (t : ℤ) + 90 ≤ decCapN p i r := by omega
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [decTokN, tokNZWL, modWL, WL.shift, WL.px, WL.py, WL.qt, rfOut, rfX, rfCU, rfCV,
    nzTokPortV, modDX, modDY, nzTokChan, leftChan, uL] at h hcl x1 x2 x3 x4 hu ⊢
  refine ⟨by omega, by omega, by omega, by omega⟩


/-- **The flight of `KNZ`** from the end of its route to `90` generations before its capture is
far from every piece of the machine. -/
theorem dsepI_flyN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ≤ t)
    (h2 : t ≤ decCapN p i r - 90) :
    dsepIFar p ((decTokN p i r).box t) [] := by
  have hj := dsepM_j_lt hi
  have hu := modD_uv p r
  have hUe := U_even p r
  have hb := base_boxes
  have hf := layout_facts p
  have hS := fun x (hx : x ∈ (decTokN p i r).box t) => dsepI_flyN_mem hi h1 h2 hx
  refine dsepT_far_list hp (L := []) (by simp) (dsepT_mod_far hp (r := r)
    (own := fun B => ∃ x ∈ ([] : List Piece), dsepTB x = B) ?_ ?_ ?_)
  · intro x hx
    have := hS x hx
    unfold modLeft modRight modTop
    omega
  · intro s hs _
    rcases moduleSpecs_cls p r hs with ⟨i', ph, hi'⟩ | ph | ph | ⟨m', ph, hm'⟩ |
      ⟨i', j', ph, hi', hj'⟩ | ⟨i', j', ph, hi', hj'⟩ | ph | ph
    · have := dz2g_facts i' hi'
      simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · have := stNZ_cases i' hi'
      simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · have := stZ_cases i' hi'
      simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      have : (D p : ℤ) = (numCallers p : ℤ) := rfl
      omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
  · intro c hc ht _
    have hv := allCorners_valid hp c hc
    have hcu := corner_uv c
    rcases ht with ⟨idx, ht⟩ | ⟨j', w, ht⟩
    · have hport := dsepT_left_port c hc r idx ht
      by_cases hidx : idx = 2 * D p + 1 + 2 * (callerIdx p r i : ℤ)
      · -- the port corner of `KNZ`: the final glider has left its window
        have hc0 : (⟨4, U p r + nzTokChan p (callerIdx p r i), nzTokPortV (callerIdx p r i),
            .left r (2 * D p + 1 + 2 * (callerIdx p r i))⟩ : Corner) ∈ allCorners p :=
          dsepM_corner_mem hi (dsepM_specs hi).1 _ (by simp [decCornN, downCorners])
        have e := eq_of_tag (allCorners_tags hp) hc hc0 (by rw [ht, hidx])
        subst e
        unfold decTokN
        rw [← decKNZ_target p i r]
        exact dsepM_final_far (bandCorners p (instrBand i) 0 (A p i + decL)
          (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
          (U p r + nzTokChan p (callerIdx p r i)) 3 2) _ _ 4260 (by norm_num)
          (decKNZ_timedX p hi) h1
      · refine dsepT_far_uv hcu fun x hx => ?_
        have := hS x hx
        unfold dsepTPort at hport
        simp only [decPortV, incPortV, nzTokPortV, nzAnsPortV] at hport
        rcases hport with ⟨h1', h2'⟩ | ⟨j'', h1', h2', h3'⟩
        · omega
        · rcases h3' with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> omega
    · refine dsepT_far_uv hcu fun x hx => ?_
      have := hS x hx
      obtain ⟨k, u, v, tag⟩ := c
      simp only at ht hcu ⊢
      subst ht
      simp only [Valid] at hv
      omega

/-- **The moving footprint of `KNZ`** is far from every piece of the machine outside its
thread. -/
theorem dsepI_tokFootN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (h2 : t ≤ decCapN p i r) :
    dsepIFar p (tokFootN p i r t) (decLNu p i r) := by
  unfold tokFootN
  split_ifs with h3
  · refine dsepI_flyFoot_far (dsep_sepN hp hi) (decKNZ_timedX p hi) (decKNZ_lines p i r).1
      downCorners_k (by simp [decCornN, downCorners, bandCorners])
      (fun x hx => mem_dd.2 (List.mem_append_left _ hx))
      (fun t' h1 h2 => ?_) t h0 h3
    rw [decKNZ_target]
    exact (dsepI_flyN_far hp hi (by omega) h2).mono subset_rfl (by simp)
  · exact (dsepI_winN_far hp hi _ (by omega)).mono subset_rfl
      fun x hx => mem_dd.2 (List.mem_append_right _ hx)

/-! ### The token `KZ` -/

/-- **The flight of `KZ` in coordinates**: on the station column `u = U_r + 1230 + 144 j`. -/
theorem dsepI_flyZ_mem (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h2 : t ≤ decCapZ p i r - 90) {x : Cell} (hx : x ∈ (decTokZ p i r).box t) :
    U p r + 1226 + 144 * ((callerIdx p r i : ℕ) : ℤ) ≤ x.1 - x.2 ∧
      x.1 - x.2 ≤ U p r + 1234 + 144 * ((callerIdx p r i : ℕ) : ℤ) ∧ 0 ≤ x.1 + x.2 := by
  have hu := modD_uv p r
  have hUe := U_even p r
  have hc := (decCap_cast p hi).2
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have h90 : 90 ≤ decCapZ p i r := by unfold decCapZ; omega
  have ht2 : (t : ℤ) + 90 ≤ decCapZ p i r := by omega
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [decTokZ, tokZWL, modWL, WL.shift, WL.px, WL.py, WL.qt, modDX, modDY] at hu x1 x2 x3 x4
  refine ⟨by omega, by omega, by omega⟩

/-- **The flight of `KZ`** from the end of its route to `90` generations before its capture is
far from every piece of the machine outside its thread. -/
theorem dsepI_flyZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 ≤ t)
    (h2 : t ≤ decCapZ p i r - 90) :
    dsepIFar p ((decTokZ p i r).box t) (decLZu p i r) := by
  have hj := dsepM_j_lt hi
  have hu := modD_uv p r
  have hUe := U_even p r
  have hb := base_boxes
  have hf := layout_facts p
  have hS := fun x (hx : x ∈ (decTokZ p i r).box t) => dsepI_flyZ_mem hi h2 hx
  refine dsepT_far_list hp (decLZu_mem hi) (dsepT_mod_far hp (r := r)
    (own := fun B => ∃ x ∈ decLZu p i r, dsepTB x = B) ?_ ?_ ?_)
  · intro x hx
    have := hS x hx
    unfold modLeft modRight modTop
    omega
  · intro s hs hn
    rcases moduleSpecs_cls p r hs with ⟨i', ph, hi'⟩ | ph | ph | ⟨m', ph, hm'⟩ |
      ⟨i', j', ph, hi', hj'⟩ | ⟨i', j', ph, hi', hj'⟩ | ph | ph
    · have := dz2g_facts i' hi'
      simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · have := stNZ_cases i' hi'
      simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · by_cases hjj : j' = callerIdx p r i
      · subst hjj
        obtain ⟨x, hx, e⟩ := dsepI_own_stZ p r (callerIdx p r i) hi'
        exact absurd ⟨x, mem_dd.2 (List.mem_append_right _ hx), e⟩ hn
      · have := stZ_cases i' hi'
        have : (j' : ℤ) ≠ (callerIdx p r i : ℤ) := by exact_mod_cast hjj
        simp only [PSpec.bx_mk]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      omega
    · simp only [PSpec.bx_mk]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      have : (D p : ℤ) = (numCallers p : ℤ) := rfl
      omega
  · intro c hc ht _
    have hv := allCorners_valid hp c hc
    have hcu := corner_uv c
    rcases ht with ⟨idx, ht⟩ | ⟨j', w, ht⟩
    · refine dsepT_far_uv hcu fun x hx => ?_
      have := hS x hx
      obtain ⟨k, u, v, tag⟩ := c
      simp only at ht hcu ⊢
      subst ht
      simp only [Valid] at hv
      omega
    · by_cases hw : w = 3 ∧ j' = (callerIdx p r i : ℤ)
      · -- the station corner of `KZ`: the final glider has left its window
        have e0 : decCornZ p i r = (bandCorners p (instrBand i) 2 (A p i + decD)
            (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
            (U p r + zTokChan p (callerIdx p r i)) 3 2 ++
            [⟨3, U p r + zTokChan p (callerIdx p r i), zTokDepth p (callerIdx p r i),
              .right r (callerIdx p r i) 2⟩]) ++
            [⟨0, U p r + zTokStation (callerIdx p r i), zTokDepth p (callerIdx p r i),
              .right r (callerIdx p r i) 3⟩] := by
          simp [decCornZ, ztokCorners]
        have hc0 : (⟨0, U p r + zTokStation (callerIdx p r i), zTokDepth p (callerIdx p r i),
            .right r (callerIdx p r i) 3⟩ : Corner) ∈ allCorners p :=
          dsepM_corner_mem hi (dsepM_specs hi).2.2.1 _ (by rw [e0]; simp)
        obtain ⟨rfl, rfl⟩ := hw
        have e := eq_of_tag (allCorners_tags hp) hc hc0 (by rw [ht])
        subst e
        have htim := decKZ_timedX p hi
        rw [e0] at htim h1
        unfold decTokZ
        rw [← decKZ_target p i r, e0]
        exact dsepM_final_far _ _ _ 4260 (by norm_num) htim h1
      · refine dsepT_far_uv hcu fun x hx => ?_
        have := hS x hx
        obtain ⟨k, u, v, tag⟩ := c
        simp only at ht hcu ⊢
        subst ht
        simp only [Valid] at hv
        omega

/-- **The moving footprint of `KZ`** is far from every piece of the machine outside its
thread. -/
theorem dsepI_tokFootZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (h2 : t ≤ decCapZ p i r) :
    dsepIFar p (tokFootZ p i r t) (decLZu p i r) := by
  unfold tokFootZ
  split_ifs with h3
  · refine dsepI_flyFoot_far (dsep_sepZ hp hi) (decKZ_timedX p hi) (decKZ_lines p i r)
      ztokCorners_k (by simp [decCornZ, ztokCorners, bandCorners])
      (fun x hx => mem_dd.2 (List.mem_append_left _ hx))
      (fun t' h1 h2 => ?_) t h0 h3
    rw [decKZ_target]
    exact dsepI_flyZ_far hp hi (by omega) h2
  · exact (dsepI_winZ_far hp hi _ (by omega)).mono subset_rfl
      fun x hx => mem_dd.2 (List.mem_append_right _ hx)

/-! ### The unpaired tokens -/

/-- **The moving footprint of the unpaired `KZ`** (NZ activation) is far from every piece of the
machine outside its thread. -/
theorem dsepI_unpFootZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) : dsepIFar p (unpFootZ p i r t) (decLZu p i r) := by
  unfold unpFootZ
  split_ifs with h1 h2
  · exact dsepI_tokFootZ_far hp hi h0 h1
  · exact (dsepI_unpZ_far hp hi _ (by omega)).mono subset_rfl
      fun x hx => mem_dd.2 (List.mem_append_right _ hx)
  · exact dsepI_empty _

/-- **The moving footprint of the unpaired `KNZ`** (Z activation) is far from every piece of the
machine outside its thread. -/
theorem dsepI_unpFootN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) : dsepIFar p (unpFootN p i r t) (decLNu p i r) := by
  unfold unpFootN
  split_ifs with h1 h2
  · exact dsepI_tokFootN_far hp hi h0 h1
  · exact (dsepI_unpN_far hp hi _ (by omega)).mono subset_rfl
      fun x hx => mem_dd.2 (List.mem_append_right _ hx)
  · exact dsepI_empty _
end LP

end LeanTheory.Life
