/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepMov2

/-!
# The control and the token flights of `DecSep`

Research note `N-22`. Fields of `DecSepRest` (`DecSepMain`) proved for every `decJz` instruction
of a well-formed program:

* `dsepM_sideC`, `dsepM_chainC`, `dsepM_cpC`: the joint approach of `C` and DEC copy `m`, the DEC
  chain and the flight of `C'` (all in the `u`-band of the module, below the stations) are far
  from the reflectors of `C` and from the other DEC copies;
* `dsepM_flyC`: the flight of `C` on the port line `v = -3351 - 99 m` of DEC copy `m`: far from
  the band corners (`v`), its own last corner (`dsepM_final_far`), the copies `< m` (`v`) and
  copy `m` (`y`, until `21` generations before the side input);
* `dsepM_flyN`, `dsepM_flyZ`: the flights of the tokens to their stations: far from the band
  corners, from the corners of their own route, and from station `j` (in `x` for `KNZ`, in `y`
  for `KZ`) until `90` generations before the capture.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Corners of the routes -/

/-- The corners of a route down to a port of the left zone: band corners and the port corner. -/
theorem dsepM_down_cases {b s c H cd vp : ℤ} {r' : ℕ} {idx : ℤ} {x : Corner}
    (hx : x ∈ downCorners p b s c H cd vp r' idx) :
    (∃ b k h, x.tag = .band b k h) ∨ x = ⟨4, cd, vp, .left r' idx⟩ := by
  simp only [downCorners, bandCorners, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with (rfl | rfl | rfl | rfl) | rfl
  · exact Or.inl ⟨_, _, _, rfl⟩
  · exact Or.inl ⟨_, _, _, rfl⟩
  · exact Or.inl ⟨_, _, _, rfl⟩
  · exact Or.inl ⟨_, _, _, rfl⟩
  · exact Or.inr rfl

/-- The pieces of the control thread: reflectors of `C` or DEC copies `m' ≤ m`. -/
theorem dsepM_mem_decLC {h : Piece} (hh : h ∈ decLC p i r) :
    h ∈ reflP (unitWL p i decRWL) (decCornC p i r) ∨
      ∃ m' < decM p i r + 1, h = (⟨.orGate, modDX p r - 1700 - 35 * (m' : ℤ),
        modDY p r - 1727 - 64 * (m' : ℤ), (15 + 14 * m') % 30⟩ : PSpec).piece := by
  rcases List.mem_append.1 (mem_dd.1 hh) with hh | hh
  · exact Or.inl hh
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
    obtain ⟨m', hm', rfl⟩ := mem_decChainSpecs hs
    exact Or.inr ⟨m', hm', rfl⟩

/-- The box of a DEC copy. -/
theorem dsepM_copy_box (p : Program) (r m' ph : ℕ) :
    (⟨.orGate, modDX p r - 1700 - 35 * (m' : ℤ), modDY p r - 1727 - 64 * (m' : ℤ), ph⟩ :
      PSpec).piece.box = Box (modDX p r - 1700 - 35 * m') (modDX p r - 1700 - 35 * m' + 90)
        (modDY p r - 1727 - 64 * m') (modDY p r - 1727 - 64 * m' + 32) :=
  isep2_chain_box _ _ m' ph

/-! ### The DEC chain -/

/-- **`DecSep.sideC`**: the joint approach of `C` and DEC copy `m` is far from the reflectors of
`C` and from the DEC copies `< m`. -/
theorem dsepM_sideC (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ h ∈ decLC p i r, h ≠ decCopyM p i r → FarApart 2 (decSideBoxC p i r) h.box := by
  intro h hh hne
  have hu := modD_uv p r
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  rcases dsepM_mem_decLC hh with hh | ⟨m', hm', rfl⟩
  · refine dsepM_reflP_far hp hi r (fun x hx => ?_) (dsepM_specs hi).2.1 hh
    obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hm' with hlt | rfl
    · rw [dsepM_copy_box]
      refine isep2_far_box fun x hx => ?_
      obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
      simp only [Prod.fst_add, Prod.snd_add]
      have : (m' : ℤ) + 1 ≤ (decM p i r : ℤ) := by exact_mod_cast hlt
      omega
    · exact absurd rfl hne

/-- **`DecSep.chainC`**: the DEC chain is far from the reflectors of `C`. -/
theorem dsepM_chainC (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ h ∈ decLC p i r, h ∉ decChainP p i r → FarApart 2 (decChainFoot p i r) h.box := by
  intro h hh hn
  have hu := modD_uv p r
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  rcases List.mem_append.1 (mem_dd.1 hh) with hh | hh
  · refine dsepM_reflP_far hp hi r (fun x hx => ?_) (dsepM_specs hi).2.1 hh
    obtain ⟨d, ⟨j', hj', d1, d2, d3, d4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add] at d1 d2 d3 d4 ⊢
    have : (j' : ℤ) ≤ (decM p i r : ℤ) := by omega
    omega
  · exact absurd hh hn

/-- **`DecSep.cpC`**: the flight of `C'` to the register run is far from the reflectors of `C`
and from the DEC copies. -/
theorem dsepM_cpC (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, decTB p i r ≤ t → t < decTS p i r → ∀ h ∈ decLC p i r,
      FarApart 2 (decCpFoot p i r t) h.box := by
  intro t h1 h2 h hh
  have hu := modD_uv p r
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  have e : decTS p i r = decTB p i r + 1771 := rfl
  have hs : ((t - decTB p i r : ℕ) : ℤ) < 1771 := by omega
  have hS : ∀ x ∈ decCpFoot p i r t, modDX p r - 1671 ≤ x.1 ∧ modDY p r - 1671 ≤ x.2 ∧
      x.1 - x.2 = U p r + 41 ∨ (U p r + 37 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + 45 ∧
        modDY p r - 1671 ≤ x.2 ∧ -3303 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ -2000) := by
    intro x hx
    obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    simp only [cp0WL, WL.px, WL.py, WL.qt, Prod.fst_add, Prod.snd_add] at d1 d2 d3 d4 ⊢
    right
    omega
  rcases dsepM_mem_decLC hh with hh | ⟨m', -, rfl⟩
  · refine dsepM_reflP_far hp hi r (fun x hx => ?_) (dsepM_specs hi).2.1 hh
    rcases hS x hx with h | h <;> omega
  · rw [dsepM_copy_box]
    refine isep2_far_box fun x hx => ?_
    rcases hS x hx with h | h <;> omega

/-- **`DecSep.flyC`**: the flight of `C` on the port line of DEC copy `m`, from the end of its
route to `20` generations before its side input, is far from the pieces of the control. -/
theorem dsepM_flyC (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ≤ t →
      t < decTA p i r - 20 → ∀ h ∈ decLC p i r, FarApart 2 ((decGC p i r).box t) h.box := by
  intro t h1 h2 h hh
  have hu := modD_uv p r
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  have hUe := U_even p r
  obtain ⟨-, hA20, hTA⟩ := decTA_facts p hi
  have hs := sigma_cases (qOf p (callerIdx p r i))
  have hS : ∀ x ∈ (decGC p i r).box t, x.1 + x.2 ≤ -3345 - 99 * (decM p i r : ℤ) ∧
      -3353 - 99 * (decM p i r : ℤ) ≤ x.1 + x.2 ∧
      modDY p r - 1727 - 64 * (decM p i r : ℤ) + 36 ≤ x.2 := by
    intro x hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    rw [decC_window] at x1 x2 x3 x4
    simp only [decWin, modWL, WL.shift, WL.px, WL.py, WL.qt, modDX, modDY] at x1 x2 x3 x4 hu ⊢
    omega
  rcases dsepM_mem_decLC hh with hh | ⟨m', hm', rfl⟩
  · obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem hh
    rw [hb]
    have hcm := dsepM_corner_mem hi (dsepM_specs hi).2.1 c hc
    rcases dsepM_down_cases hc with ht | rfl
    · refine dsepM_band_far hp (fun x hx => ?_) hcm (Or.inl ht)
      have := hS x hx
      have := lane_VT_low p
      omega
    · exact dsepM_final_far (bandCorners p (instrBand i) 1 (A p i + decR)
        (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
        (U p r + decChan p (2 * (callerIdx p r i))) 3 2) _ _ 4260 (by norm_num)
        (decC_timedX p hi) h1
  · rw [dsepM_copy_box]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    have : (m' : ℤ) ≤ (decM p i r : ℤ) := by omega
    omega

end LP

end LeanTheory.Life
