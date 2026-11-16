/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepMov3

/-!
# The token flights of `DecSep`, and the `14` moving fields

Research note `N-22`. For every `decJz` instruction of a well-formed program:

* `dsepM_flyN`: `KNZ` on the port line `v = 1256 + 144 j`, until `90` generations before its
  capture, is far from its reflectors (band corners in `v`, the port corner by
  `dsepM_final_far`) and from station `j` of the line NZ (in `x`);
* `dsepM_flyZ`: `KZ` on the station column `u = U_r + 1230 + 144 j` is far from its reflectors
  (band corners in `v`, the channel corner in `u`, the station corner by `dsepM_final_far`) and
  from station `j` of the line Z (in `y`);
* **`dsepM_fields`**: the `14` fields `flyC`, `sideC`, `chainC`, `cpC`, `flyN`, `flyZ`, `winN`,
  `winZ`, `unpN`, `unpZ`, `ansFlyN`, `ansFlyZ`, `capN`, `capZ` of `DecSepRest`, verbatim.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The stations as pieces -/

/-- The pieces of station `j` of the line NZ, with their boxes. -/
theorem dsepM_mem_stNZOne {j : ℕ} {h : Piece} (hh : h ∈ stNZOne p r j) :
    ∃ i' < 3, h.box = Box ((Base.stNZ i').piece.a + (modDX p r + 72 * (j : ℤ)))
      ((Base.stNZ i').piece.b + (modDX p r + 72 * (j : ℤ)))
      ((Base.stNZ i').piece.lo + (modDY p r + 72 * (j : ℤ)))
      ((Base.stNZ i').piece.hi + (modDY p r + 72 * (j : ℤ))) := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
  obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩

/-- The pieces of station `j` of the line Z, with their boxes. -/
theorem dsepM_mem_stZOne {j : ℕ} {h : Piece} (hh : h ∈ stZOne p r j) :
    ∃ i' < 3, h.box = Box ((Base.stZ i').piece.a + (modDX p r + 72 * (j : ℤ)))
      ((Base.stZ i').piece.b + (modDX p r + 72 * (j : ℤ)))
      ((Base.stZ i').piece.lo + (modDY p r - 72 * (j : ℤ)))
      ((Base.stZ i').piece.hi + (modDY p r - 72 * (j : ℤ))) := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
  obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩

/-! ### The token flights -/

/-- **`DecSep.flyN`**: `KNZ` from the end of its route to `90` generations before its capture is
far from its reflectors and from station `j` of the line NZ. -/
theorem dsepM_flyN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ≤ t →
      t < decCapN p i r - 90 → ∀ h ∈ decLNu p i r,
        FarApart 2 ((decTokN p i r).box t) h.box := by
  intro t h1 h2 h hh
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hc := (decCap_cast p hi).1
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have h90 : 90 ≤ decCapN p i r := by unfold decCapN; omega
  have hS : ∀ x ∈ (decTokN p i r).box t,
      x.1 + 3 ≤ modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ) + 369 ∧ 0 ≤ x.1 + x.2 := by
    intro x hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    simp only [decTokN, modWL, tokNZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
    have : (t : ℤ) + 91 ≤ decCapN p i r := by omega
    omega
  simp only [decLNu, mem_dd, List.mem_append] at hh
  rcases hh with hh | hh
  · obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem hh
    rw [hb]
    have hcm := dsepM_corner_mem hi (dsepM_specs hi).1 c hc
    rcases dsepM_down_cases hc with ht | rfl
    · refine dsepM_band_far hp (fun x hx => ?_) hcm (Or.inl ht)
      have := hS x hx
      have := one_le_D p
      omega
    · unfold decTokN
      rw [← decKNZ_target p i r]
      exact dsepM_final_far (bandCorners p (instrBand i) 0 (A p i + decL)
        (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
        (U p r + nzTokChan p (callerIdx p r i)) 3 2) _ _ 4260 (by norm_num)
        (decKNZ_timedX p hi) h1
  · obtain ⟨i', hi', hb⟩ := dsepM_mem_stNZOne hh
    have := stNZ_cases i' hi'
    rw [hb]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    omega

/-- **`DecSep.flyZ`**: `KZ` from the end of its route to `90` generations before its capture is
far from its reflectors and from station `j` of the line Z. -/
theorem dsepM_flyZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 ≤ t →
      t < decCapZ p i r - 90 → ∀ h ∈ decLZu p i r,
        FarApart 2 ((decTokZ p i r).box t) h.box := by
  intro t h1 h2 h hh
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hc := (decCap_cast p hi).2
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have h90 : 90 ≤ decCapZ p i r := by unfold decCapZ; omega
  have hS : ∀ x ∈ (decTokZ p i r).box t,
      modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ) - 290 ≤ x.2 ∧
      x.1 - x.2 ≤ U p r + 1234 + 144 * ((callerIdx p r i : ℕ) : ℤ) ∧ 0 ≤ x.1 + x.2 := by
    intro x hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    simp only [decTokZ, modWL, tokZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
    have : (t : ℤ) + 91 ≤ decCapZ p i r := by omega
    omega
  simp only [decLZu, mem_dd, List.mem_append] at hh
  rcases hh with hh | hh
  · obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem hh
    rw [hb]
    have hcm := dsepM_corner_mem hi (dsepM_specs hi).2.2.1 c hc
    have e : decCornZ p i r = bandCorners p (instrBand i) 2 (A p i + decD)
        (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
        (U p r + zTokChan p (callerIdx p r i)) 3 2 ++
        [⟨3, U p r + zTokChan p (callerIdx p r i), zTokDepth p (callerIdx p r i),
          .right r (callerIdx p r i) 2⟩] ++
        [⟨0, U p r + zTokStation (callerIdx p r i), zTokDepth p (callerIdx p r i),
          .right r (callerIdx p r i) 3⟩] := by
      simp [decCornZ, ztokCorners]
    have hc' := hc
    rw [e] at hc'
    simp only [bandCorners, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with ((ht | ht | ht | ht) | ht) | ht
    · refine dsepM_band_far hp (fun x hx => ?_) hcm (Or.inl ⟨_, _, _, by rw [ht]⟩)
      have := hS x hx; have := one_le_D p; omega
    · refine dsepM_band_far hp (fun x hx => ?_) hcm (Or.inl ⟨_, _, _, by rw [ht]⟩)
      have := hS x hx; have := one_le_D p; omega
    · refine dsepM_band_far hp (fun x hx => ?_) hcm (Or.inl ⟨_, _, _, by rw [ht]⟩)
      have := hS x hx; have := one_le_D p; omega
    · refine dsepM_band_far hp (fun x hx => ?_) hcm (Or.inl ⟨_, _, _, by rw [ht]⟩)
      have := hS x hx; have := one_le_D p; omega
    · -- the channel corner: far right of the station column
      have hv := allCorners_valid hp c hcm
      have hcu := corner_uv c
      subst ht
      simp only [Valid] at hv
      unfold BoxT.InUV at hcu
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      have := one_le_D p
      simp only at hcu hv
      omega
    · -- the station corner: the final glider has left its window
      subst ht
      have htim := decKZ_timedX p hi
      rw [e] at htim h1
      unfold decTokZ
      rw [← decKZ_target p i r, e]
      exact dsepM_final_far _ _ _ 4260 (by norm_num) htim h1
  · obtain ⟨i', hi', hb⟩ := dsepM_mem_stZOne hh
    have := stZ_cases i' hi'
    rw [hb]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    omega

/-! ### The `14` moving fields -/

/-- **The `14` moving fields of `DecSepRest`** (`flyC`, `sideC`, `chainC`, `cpC`, `flyN`, `flyZ`,
`winN`, `winZ`, `unpN`, `unpZ`, `ansFlyN`, `ansFlyZ`, `capN`, `capZ`), verbatim, for every
`decJz` instruction of a well-formed program. -/
theorem dsepM_fields (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    (∀ t : ℕ, routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ≤ t →
      t < decTA p i r - 20 → ∀ h ∈ decLC p i r, FarApart 2 ((decGC p i r).box t) h.box) ∧
    (∀ h ∈ decLC p i r, h ≠ decCopyM p i r → FarApart 2 (decSideBoxC p i r) h.box) ∧
    (∀ h ∈ decLC p i r, h ∉ decChainP p i r → FarApart 2 (decChainFoot p i r) h.box) ∧
    (∀ t : ℕ, decTB p i r ≤ t → t < decTS p i r → ∀ h ∈ decLC p i r,
      FarApart 2 (decCpFoot p i r t) h.box) ∧
    (∀ t : ℕ, routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ≤ t →
      t < decCapN p i r - 90 → ∀ h ∈ decLNu p i r, FarApart 2 ((decTokN p i r).box t) h.box) ∧
    (∀ t : ℕ, routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 ≤ t →
      t < decCapZ p i r - 90 → ∀ h ∈ decLZu p i r, FarApart 2 ((decTokZ p i r).box t) h.box) ∧
    (∀ k < 90, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decTokWStartN p i r) : Set Cell) h.box) ∧
    (∀ k < 90, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decTokWStartZ p i r) : Set Cell) h.box) ∧
    (∀ k < 292, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decUnpStartN p i r) : Set Cell) h.box) ∧
    (∀ k < 272, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decUnpStartZ p i r) : Set Cell) h.box) ∧
    (∀ t : ℕ, decCutN p i r ≤ t → t < decSt0N p i r → ∀ h ∈ decLSN p i r,
      FarApart 2 ((decAnsWLN p i r).box t) h.box) ∧
    (∀ t : ℕ, decCutZ p i r ≤ t → t < decSt0Z p i r → ∀ h ∈ decLSZ p i r,
      FarApart 2 ((decAnsWLZ p i r).box t) h.box) ∧
    (∀ k < 692, ∀ h ∈ decLFN p i r, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decCapStartN p i r) : Set Cell) h.box) ∧
    (∀ k < 672, ∀ h ∈ decLFZ p i r z, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decCapStartZ p i r) : Set Cell) h.box) :=
  ⟨dsepM_flyC hp hi, dsepM_sideC hp hi, dsepM_chainC hp hi, dsepM_cpC hp hi, dsepM_flyN hp hi,
    dsepM_flyZ hp hi, dsepM_winN hp hi, dsepM_winZ hp hi, dsepM_unpN hp hi, dsepM_unpZ hp hi,
    dsepM_ansFlyN, dsepM_ansFlyZ, dsepM_capN hp hi, dsepM_capZ hp hi⟩

end LP

end LeanTheory.Life
