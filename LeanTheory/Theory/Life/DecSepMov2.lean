/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepMov

/-!
# The station windows, the absorptions, the captures and the answers of `DecSep`

Research note `N-22`. Fields of `DecSepRest` (`DecSepMain`) proved for every `decJz` instruction
of a well-formed program:

* `dsepM_winN`, `dsepM_winZ`: the joint approach of a token and its station (`stTokWNZ`,
  `stTokWZ`) is far from the reflectors of the token;
* `dsepM_unpN`, `dsepM_unpZ`: the absorption of the unpaired token (`stationNZ_unpaired`,
  `stationZ_unpaired`) is far from the reflectors of the token;
* `dsepM_capN`, `dsepM_capZ`: the extended capture (`stationNZ_captureE`, `stationZ_captureE`) is
  far from the reflectors of the answer and from the entry chain of the next unit;
* `dsepM_ansFlyN`, `dsepM_ansFlyZ`: the answer on its line is far from every station, in `u`
  (NZ, the line `u = U_r - 391`) or in `v` (Z, the line `v = 537`).

The station footprints lie in the `u`-band of the module, so the reflectors are handled by
`dsepM_reflP_far`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Boxes in coordinates -/

/-- A cell of a translated set inside a box, in coordinates. -/
theorem dsepM_translate_box {v : Cell} {S : Finset Cell} {a b lo hi : ℤ}
    (hS : (S : Set Cell) ⊆ Box a b lo hi) {c : Cell} (hc : c ∈ (translate v S : Set Cell)) :
    a + v.1 ≤ c.1 ∧ c.1 ≤ b + v.1 ∧ lo + v.2 ≤ c.2 ∧ c.2 ≤ hi + v.2 := by
  rw [mem_coe, mem_translate] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hS (mem_coe.2 hc)
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  omega

/-- A cell of an image of a box, in coordinates. -/
theorem dsepM_image_box {v : Cell} {a b lo hi : ℤ} {c : Cell}
    (hc : c ∈ (fun d => v + d) '' Box a b lo hi) :
    a + v.1 ≤ c.1 ∧ c.1 ≤ b + v.1 ∧ lo + v.2 ≤ c.2 ∧ c.2 ≤ hi + v.2 := by
  obtain ⟨d, ⟨h1, h2, h3, h4⟩, rfl⟩ := hc
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- The caller index is below `D`. -/
theorem dsepM_j_lt (hi : p[i]? = some (.decJz r z)) : ((callerIdx p r i : ℕ) : ℤ) < D p := by
  have := callerIdx_lt_D p hi
  unfold D
  omega

/-- The routes of a `decJz` instruction, as members of its specs. -/
theorem dsepM_specs (hi : p[i]? = some (.decJz r z)) :
    (unitWL p i decLWL, decCornN p i r) ∈ instrSpecs p i ∧
      (unitWL p i decRWL, decCornC p i r) ∈ instrSpecs p i ∧
      (unitWL p i decDWL, decCornZ p i r) ∈ instrSpecs p i ∧
      (decGN p i r, decCsN p i r) ∈ instrSpecs p i ∧
      (decGZ p i r, decCsZ p i r z) ∈ instrSpecs p i := by
  rw [dsep_instrSpecs hi]
  simp [decCsN, decCsZ]

/-- A copy of an entry chain of a unit is far from a set above the bands. -/
theorem dsepM_chain_far {S : Set Cell} (hS : ∀ x ∈ S, -4100 - 198 * D p ≤ x.1 + x.2)
    {a t : ℕ} {h : Piece} (hh : h ∈ chainPieces p a t) : FarApart 2 S h.box := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  obtain ⟨t', ht', rfl⟩ := mem_chainSpecs hs
  have hd := unitD_uv p a
  have hf := lane_VT_low p
  rw [isep2_chain_box]
  refine isep2_far_box fun x hx => ?_
  have := hS x hx
  omega

/-! ### The tokens at their stations -/

/-- **`DecSep.winN`**: the joint approach of `KNZ` and its station is far from the reflectors of
`KNZ`. -/
theorem dsepM_winN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k < 90, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decTokWStartN p i r) : Set Cell) h.box := by
  intro k hk h hh hn
  simp only [decLNu, mem_dd, List.mem_append] at hh
  rcases hh with hh | hh
  · have hu := modD_uv p r
    have hj := dsepM_j_lt hi
    refine dsepM_reflP_far hp hi r (fun x hx => ?_) (dsepM_specs hi).1 hh
    rw [decTokWStartN_eq hi, Rule.evolve_translate] at hx
    have := dsepM_translate_box (stTokWNZ.subset k (by omega)) hx
    simp only at this
    omega
  · exact absurd hh hn

/-- **`DecSep.winZ`**: the joint approach of `KZ` and its station is far from the reflectors of
`KZ`. -/
theorem dsepM_winZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k < 90, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decTokWStartZ p i r) : Set Cell) h.box := by
  intro k hk h hh hn
  simp only [decLZu, mem_dd, List.mem_append] at hh
  rcases hh with hh | hh
  · have hu := modD_uv p r
    have hj := dsepM_j_lt hi
    refine dsepM_reflP_far hp hi r (fun x hx => ?_) (dsepM_specs hi).2.2.1 hh
    rw [decTokWStartZ_eq hi, Rule.evolve_translate] at hx
    have := dsepM_translate_box (stTokWZ.subset k (by omega)) hx
    simp only at this
    omega
  · exact absurd hh hn

/-- **`DecSep.unpN`**: the absorption of the unpaired `KNZ` is far from its reflectors. -/
theorem dsepM_unpN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k < 292, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decUnpStartN p i r) : Set Cell) h.box := by
  intro k hk h hh hn
  simp only [decLNu, mem_dd, List.mem_append] at hh
  rcases hh with hh | hh
  · have hu := modD_uv p r
    have hj := dsepM_j_lt hi
    have hc := decCap_cast p hi
    refine dsepM_reflP_far hp hi r (fun x hx => ?_) (dsepM_specs hi).1 hh
    have := dsepM_image_box ((stationNZ_unpaired p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapN p i r) hc.1).subset k (by omega) hx)
    simp only at this
    omega
  · exact absurd hh hn

/-- **`DecSep.unpZ`**: the absorption of the unpaired `KZ` is far from its reflectors. -/
theorem dsepM_unpZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k < 272, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decUnpStartZ p i r) : Set Cell) h.box := by
  intro k hk h hh hn
  simp only [decLZu, mem_dd, List.mem_append] at hh
  rcases hh with hh | hh
  · have hu := modD_uv p r
    have hj := dsepM_j_lt hi
    have hc := decCap_cast p hi
    refine dsepM_reflP_far hp hi r (fun x hx => ?_) (dsepM_specs hi).2.2.1 hh
    have := dsepM_image_box ((stationZ_unpaired p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapZ p i r) hc.2).subset k (by omega) hx)
    simp only at this
    omega
  · exact absurd hh hn

/-! ### The captures -/

/-- **`DecSep.capN`**: the extended capture at station `j` of the line NZ is far from the
reflectors of the NZ answer and from the entry chain of unit `i + 1`. -/
theorem dsepM_capN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k < 692, ∀ h ∈ decLFN p i r, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decCapStartN p i r) : Set Cell) h.box := by
  intro k hk h hh hn
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hc := decCap_cast p hi
  have hS : ∀ x ∈ (conway.evolve k (decCapStartN p i r) : Set Cell),
      U p r - 760 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + 1300 + 144 * D p ∧
      -4100 - 198 * D p ≤ x.1 + x.2 ∧ (x.1 - x.2 ≤ U p r + 1170 ∨ x.1 + x.2 ≤ 1450) := by
    intro x hx
    have := dsepM_image_box ((stationNZ_captureE p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapN p i r) hc.1).subset k (by omega) hx)
    simp only at this
    omega
  simp only [decLFN, mem_dd, List.mem_append] at hh
  rcases hh with (hh | hh) | hh
  · exact absurd hh hn
  · exact dsepM_reflP_far hp hi r hS (dsepM_specs hi).2.2.2.1 hh
  · exact dsepM_chain_far (fun x hx => (hS x hx).2.2.1) hh

/-- **`DecSep.capZ`**: the extended capture at station `j` of the line Z is far from the
reflectors of the Z answer and from the entry chain of unit `z`. -/
theorem dsepM_capZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k < 672, ∀ h ∈ decLFZ p i r z, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decCapStartZ p i r) : Set Cell) h.box := by
  intro k hk h hh hn
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  have hc := decCap_cast p hi
  have hS : ∀ x ∈ (conway.evolve k (decCapStartZ p i r) : Set Cell),
      U p r - 760 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + 1300 + 144 * D p ∧
      -4100 - 198 * D p ≤ x.1 + x.2 ∧ (x.1 - x.2 ≤ U p r + 1170 ∨ x.1 + x.2 ≤ 1450) := by
    intro x hx
    have := dsepM_image_box ((stationZ_captureE p r (callerIdx p r i) (decShift p i r)
      (decShift_mod p i r) (decCapZ p i r) hc.2).subset k (by omega) hx)
    simp only at this
    omega
  simp only [decLFZ, mem_dd, List.mem_append] at hh
  rcases hh with (hh | hh) | hh
  · exact absurd hh hn
  · exact dsepM_reflP_far hp hi r hS (dsepM_specs hi).2.2.2.2 hh
  · exact dsepM_chain_far (fun x hx => (hS x hx).2.2.1) hh

/-! ### The answers on their lines -/

/-- **`DecSep.ansFlyN`**: the NZ answer on its line (`u = U_r - 391`) is far from every NZ
station. -/
theorem dsepM_ansFlyN :
    ∀ t : ℕ, decCutN p i r ≤ t → t < decSt0N p i r → ∀ h ∈ decLSN p i r,
      FarApart 2 ((decAnsWLN p i r).box t) h.box := by
  intro t _ _ h hh
  have hu := modD_uv p r
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hh)
  obtain ⟨j', -, i', hi', rfl⟩ := mem_stationSpecs hs
  have := stNZ_cases i' hi'
  rw [isep2_spec_box]
  refine isep2_far_box fun x hx => ?_
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [decAnsWLN, modWL, ansNZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
  omega

/-- **`DecSep.ansFlyZ`**: the Z answer on its line (`v = 537`) is far from every Z station. -/
theorem dsepM_ansFlyZ :
    ∀ t : ℕ, decCutZ p i r ≤ t → t < decSt0Z p i r → ∀ h ∈ decLSZ p i r,
      FarApart 2 ((decAnsWLZ p i r).box t) h.box := by
  intro t _ _ h hh
  have hu := modD_uv p r
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hh)
  obtain ⟨j', -, i', hi', rfl⟩ := mem_stationZSpecs hs
  have := stZ_cases i' hi'
  rw [isep2_spec_box]
  refine isep2_far_box fun x hx => ?_
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [decAnsWLZ, modWL, ansZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
  omega

end LP

end LeanTheory.Life
