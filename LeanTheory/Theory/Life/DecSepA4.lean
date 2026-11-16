/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepAGen

/-!
# Hulls of the pieces and of the module footprints of a `decJz` activation

Research note `N-22`. The cells of the boxes of the pieces of the threads and of the footprints
inside the module, in coordinates:

* `dsepACB`: the `uv`-hull of the reflector of a corner (`corner_uv`); `dsepA_refl_cells`;
* the reflectors of `KNZ` (`dsepA_LN_cells`), of `KZ` (`dsepA_LZ_cells`), of the control and the DEC
  copies (`dsepA_LC_cells`), of the answers (`dsepA_LAN_cells`, `dsepA_LAZ_cells`), the entry
  chains (`dsepA_E_cells`), the stations (`dsepA_sjN_cells`, `dsepA_LSN_cells`, …);
* `dsepAMHat`: the hull of the module (`dsepAMH` placed at module `r`), which contains the circuit,
  the lanes, the run regions and the rest of the runs (`dsepA_rest*_mh`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Reflectors -/

/-- The `uv`-hull of the reflector of a corner at `(cu, cv)`. -/
def dsepACB (cu cv : ℤ) (x : Cell) : Prop :=
  cu - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cu + 25 ∧ cv - 24 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ cv + 27

/-- **The cells of a reflector of a route** lie in the hull of one of its corners. -/
theorem dsepA_refl_cells {g : WL} {cs : List Corner} {h : Piece} (hh : h ∈ reflP g cs) :
    ∃ c ∈ cs, ∀ x ∈ h.box, dsepACB c.u c.v x := by
  obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem hh
  refine ⟨c, hc, fun x hx => ?_⟩
  have h1 := corner_uv c
  rw [hb] at hx
  obtain ⟨x1, x2, x3, x4⟩ := hx
  unfold BoxT.InUV at h1
  simp only [dsepACB]
  omega

/-- The cells of the reflectors of `KNZ`. -/
theorem dsepA_LN_cells {g : Piece} (hg : g ∈ reflP (unitWL p i decLWL) (decCornN p i r))
    {x : Cell} (hx : x ∈ g.box) :
    dsepACB (A p i + decL) (trackOut p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
      (trackOut p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
      (trackBack p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (U p r + nzTokChan p (callerIdx p r i)) (trackBack p (instrBand i) 0 (A p i + decL)) x ∨
    dsepACB (U p r + nzTokChan p (callerIdx p r i)) (nzTokPortV (callerIdx p r i)) x := by
  obtain ⟨c, hc, hcb⟩ := dsepA_refl_cells hg
  simp only [decCornN, downCorners, bandCorners, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl) | rfl
  · exact Or.inl (hcb x hx)
  · exact Or.inr (Or.inl (hcb x hx))
  · exact Or.inr (Or.inr (Or.inl (hcb x hx)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hcb x hx))))

/-- The cells of the reflectors of `KZ`. -/
theorem dsepA_LZ_cells {g : Piece} (hg : g ∈ reflP (unitWL p i decDWL) (decCornZ p i r))
    {x : Cell} (hx : x ∈ g.box) :
    dsepACB (A p i + decD) (trackOut p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
      (trackOut p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
      (trackBack p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (U p r + zTokChan p (callerIdx p r i)) (trackBack p (instrBand i) 2 (A p i + decD)) x ∨
    dsepACB (U p r + zTokChan p (callerIdx p r i)) (zTokDepth p (callerIdx p r i)) x ∨
    dsepACB (U p r + zTokStation (callerIdx p r i)) (zTokDepth p (callerIdx p r i)) x := by
  obtain ⟨c, hc, hcb⟩ := dsepA_refl_cells hg
  simp only [decCornZ, ztokCorners, bandCorners, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (hcb x hx)
  · exact Or.inr (Or.inl (hcb x hx))
  · exact Or.inr (Or.inr (Or.inl (hcb x hx)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hcb x hx)))))

/-- The cells of the pieces of the control thread: the reflectors of `C` or a DEC copy. -/
theorem dsepA_LC_cells {g : Piece} (hg : g ∈ decLC p i r) {x : Cell} (hx : x ∈ g.box) :
    dsepACB (A p i + decR) (trackOut p (instrBand i) 1 (A p i + decR)) x ∨
    dsepACB (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
      (trackOut p (instrBand i) 1 (A p i + decR)) x ∨
    dsepACB (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
      (trackBack p (instrBand i) 1 (A p i + decR)) x ∨
    dsepACB (U p r + decChan p (2 * (callerIdx p r i))) (trackBack p (instrBand i) 1 (A p i + decR))
      x ∨
    dsepACB (U p r + decChan p (2 * (callerIdx p r i))) (decPortV p (2 * (callerIdx p r i))) x ∨
    ∃ m : ℤ, 0 ≤ m ∧ m ≤ (decM p i r : ℤ) ∧ modDX p r - 1700 - 35 * m ≤ x.1 ∧
      x.1 ≤ modDX p r - 1610 - 35 * m ∧ modDY p r - 1727 - 64 * m ≤ x.2 ∧
      x.2 ≤ modDY p r - 1695 - 64 * m := by
  rcases dsepM_mem_decLC hg with hr | ⟨m', hm', rfl⟩
  · obtain ⟨c, hc, hcb⟩ := dsepA_refl_cells hr
    simp only [decCornC, downCorners, bandCorners, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | rfl
    · exact Or.inl (hcb x hx)
    · exact Or.inr (Or.inl (hcb x hx))
    · exact Or.inr (Or.inr (Or.inl (hcb x hx)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx)))))
  · rw [dsepM_copy_box] at hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m', by omega, by omega, by omega, by omega,
      by omega, by omega⟩))))

/-- The cells of the reflectors of the NZ answer. -/
theorem dsepA_LAN_cells {g : Piece} (hg : g ∈ reflP (decGN p i r) (decCsN p i r)) {x : Cell}
    (hx : x ∈ g.box) :
    dsepACB (U p r + nzAnsChan p (callerIdx p r i)) (nzAnsPortV (callerIdx p r i)) x ∨
    dsepACB (U p r + nzAnsChan p (callerIdx p r i))
      (trackOut p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))) x ∨
    dsepACB (hairReg p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i)))
      (trackOut p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))) x ∨
    dsepACB (hairReg p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i)))
      (trackBack p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))) x ∨
    dsepACB (destU p (i + 1) (decTN p i r))
      (trackBack p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))) x ∨
    dsepACB (destU p (i + 1) (decTN p i r)) (destV p (decTN p i r)) x := by
  obtain ⟨c, hc, hcb⟩ := dsepA_refl_cells hg
  simp only [decCsN, decMkN, nzAnsCorners, upCornersK, bandCorners, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (hcb x hx)
  · exact Or.inr (Or.inl (hcb x hx))
  · exact Or.inr (Or.inr (Or.inl (hcb x hx)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hcb x hx)))))

/-- The cells of the reflectors of the Z answer. -/
theorem dsepA_LAZ_cells {g : Piece} (hg : g ∈ reflP (decGZ p i r) (decCsZ p i r z)) {x : Cell}
    (hx : x ∈ g.box) :
    dsepACB (U p r + zAnsStation (callerIdx p r i)) (zAnsDepth p (callerIdx p r i)) x ∨
    dsepACB (U p r + zAnsChan p (callerIdx p r i)) (zAnsDepth p (callerIdx p r i)) x ∨
    dsepACB (U p r + zAnsChan p (callerIdx p r i))
      (trackOut p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))) x ∨
    dsepACB (hairReg p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i)))
      (trackOut p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))) x ∨
    dsepACB (hairReg p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i)))
      (trackBack p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))) x ∨
    dsepACB (destU p z (decTZ p i r z))
      (trackBack p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))) x ∨
    dsepACB (destU p z (decTZ p i r z)) (destV p (decTZ p i r z)) x := by
  obtain ⟨c, hc, hcb⟩ := dsepA_refl_cells hg
  simp only [decCsZ, decMkZ, zAnsCorners, upCornersK, bandCorners, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (hcb x hx)
  · exact Or.inr (Or.inl (hcb x hx))
  · exact Or.inr (Or.inr (Or.inl (hcb x hx)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hcb x hx))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hcb x hx))))))

/-- The cells of the entry copies `0 … t` of unit `a`. -/
theorem dsepA_E_cells {a t : ℕ} {g : Piece} (hg : g ∈ chainPieces p a t) {x : Cell}
    (hx : x ∈ g.box) : A p a - 32 ≤ x.1 - x.2 ∧ x.1 + x.2 ≤ VU p + 122 := by
  have hd := unitD_uv p a
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  obtain ⟨t', -, rfl⟩ := mem_chainSpecs hs
  rw [isep2_chain_box] at hx
  obtain ⟨x1, x2, x3, x4⟩ := hx
  omega

/-- The entry copies are wider than a reflector. -/
theorem dsepA_E_wide {a t : ℕ} {g : Piece} (hg : g ∈ chainPieces p a t) :
    (g.a ≤ g.b ∧ g.lo ≤ g.hi) ∧ g.a + 23 ≤ g.b := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  obtain ⟨t', -, rfl⟩ := mem_chainSpecs hs
  have hb := base_boxes
  simp only [PSpec.piece, Piece.place]
  omega

/-- The DEC copies are wider than a reflector. -/
theorem dsepA_copy_wide (p : Program) (r m' ph : ℕ) :
    let g := (⟨.orGate, modDX p r - 1700 - 35 * (m' : ℤ), modDY p r - 1727 - 64 * (m' : ℤ), ph⟩ :
      PSpec).piece
    (g.a ≤ g.b ∧ g.lo ≤ g.hi) ∧ g.a + 23 ≤ g.b := by
  have hb := base_boxes
  simp only [PSpec.piece, Piece.place]
  omega

/-! ### Stations -/

/-- The cells of station `j` of the line NZ. -/
theorem dsepA_sjN_cells {j : ℕ} {g : Piece} (hg : g ∈ stNZOne p r j) {x : Cell}
    (hx : x ∈ g.box) :
    (380 + modDX p r + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 412 + modDX p r + 72 * (j : ℤ) ∧
      829 + modDY p r + 72 * (j : ℤ) ≤ x.2 ∧ x.2 ≤ 919 + modDY p r + 72 * (j : ℤ)) ∨
    (431 + modDX p r + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 439 + modDX p r + 72 * (j : ℤ) ∧
      891 + modDY p r + 72 * (j : ℤ) ≤ x.2 ∧ x.2 ≤ 913 + modDY p r + 72 * (j : ℤ)) ∨
    (464 + modDX p r + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 467 + modDX p r + 72 * (j : ℤ) ∧
      820 + modDY p r + 72 * (j : ℤ) ≤ x.2 ∧ x.2 ≤ 823 + modDY p r + 72 * (j : ℤ)) := by
  obtain ⟨i', hi', hb⟩ := dsepM_mem_stNZOne hg
  rw [hb] at hx
  obtain ⟨x1, x2, x3, x4⟩ := hx
  rcases stNZ_cases i' hi' with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ <;>
    omega

/-- The cells of station `j` of the line Z. -/
theorem dsepA_sjZ_cells {j : ℕ} {g : Piece} (hg : g ∈ stZOne p r j) {x : Cell}
    (hx : x ∈ g.box) :
    (889 + modDX p r + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 979 + modDX p r + 72 * (j : ℤ) ∧
      -325 + modDY p r - 72 * (j : ℤ) ≤ x.2 ∧ x.2 ≤ -293 + modDY p r - 72 * (j : ℤ)) ∨
    (951 + modDX p r + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 973 + modDX p r + 72 * (j : ℤ) ∧
      -352 + modDY p r - 72 * (j : ℤ) ≤ x.2 ∧ x.2 ≤ -344 + modDY p r - 72 * (j : ℤ)) ∨
    (880 + modDX p r + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 883 + modDX p r + 72 * (j : ℤ) ∧
      -380 + modDY p r - 72 * (j : ℤ) ≤ x.2 ∧ x.2 ≤ -377 + modDY p r - 72 * (j : ℤ)) := by
  obtain ⟨i', hi', hb⟩ := dsepM_mem_stZOne hg
  rw [hb] at hx
  obtain ⟨x1, x2, x3, x4⟩ := hx
  rcases stZ_cases i' hi' with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ <;>
    omega

/-- The cells of the NZ stations `0 … j - 1`. -/
theorem dsepA_LSN_cells {g : Piece} (hg : g ∈ decLSN p i r) {x : Cell} (hx : x ∈ g.box) :
    ∃ k : ℤ, 0 ≤ k ∧ k < ((callerIdx p r i : ℕ) : ℤ) ∧
    ((380 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 412 + modDX p r + 72 * k ∧
      829 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 919 + modDY p r + 72 * k) ∨
    (431 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 439 + modDX p r + 72 * k ∧
      891 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 913 + modDY p r + 72 * k) ∨
    (464 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 467 + modDX p r + 72 * k ∧
      820 + modDY p r + 72 * k ≤ x.2 ∧ x.2 ≤ 823 + modDY p r + 72 * k)) := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hg)
  obtain ⟨j', hj', i', hi', rfl⟩ := mem_stationSpecs hs
  rw [isep2_spec_box] at hx
  obtain ⟨x1, x2, x3, x4⟩ := hx
  refine ⟨j', by omega, by omega, ?_⟩
  rcases stNZ_cases i' hi' with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ <;>
    omega

/-- The cells of the Z stations `0 … j - 1`. -/
theorem dsepA_LSZ_cells {g : Piece} (hg : g ∈ decLSZ p i r) {x : Cell} (hx : x ∈ g.box) :
    ∃ k : ℤ, 0 ≤ k ∧ k < ((callerIdx p r i : ℕ) : ℤ) ∧
    ((889 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 979 + modDX p r + 72 * k ∧
      -325 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -293 + modDY p r - 72 * k) ∨
    (951 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 973 + modDX p r + 72 * k ∧
      -352 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -344 + modDY p r - 72 * k) ∨
    (880 + modDX p r + 72 * k ≤ x.1 ∧ x.1 ≤ 883 + modDX p r + 72 * k ∧
      -380 + modDY p r - 72 * k ≤ x.2 ∧ x.2 ≤ -377 + modDY p r - 72 * k)) := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hg)
  obtain ⟨j', hj', i', hi', rfl⟩ := mem_stationZSpecs hs
  rw [isep2_spec_box] at hx
  obtain ⟨x1, x2, x3, x4⟩ := hx
  refine ⟨j', by omega, by omega, ?_⟩
  rcases stZ_cases i' hi' with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ <;>
    omega

/-! ### The hull of the module -/

/-- The hull of the module placed at module `r`. -/
def dsepAMHat (p : Program) (r : ℕ) (x : Cell) : Prop :=
  (U p r - 738 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + 818 ∧ -2413 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 670) ∨
    (U p r - 113 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r - 69 ∧ 354 ≤ x.1 + x.2)

/-- A set placed at module `r` inside `dsepAMH`. -/
theorem dsepA_modImg_mh {S : Set Cell} (h : S ⊆ dsepAMH) : ∀ x ∈ modImg p r S, dsepAMHat p r x := by
  have hu := modD_uv p r
  rintro _ ⟨c, hc, rfl⟩
  rcases h hc with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3⟩
  · left; simp only [Prod.fst_add, Prod.snd_add]; omega
  · right; simp only [Prod.fst_add, Prod.snd_add]; omega

/-- The groups of the circuit and the lanes of the register lie in the hull of the module. -/
theorem dsepA_grpLanes_mh : ∀ x ∈ boxesOf (modGroup p r) ∪ modLanes p r, dsepAMHat p r x := by
  rintro x (hx | hx)
  · obtain ⟨g, hg, hx⟩ := mem_boxesOf.1 hx
    have := dsepT_grp_cells hg x hx
    simp only [dsepTGrpHull] at this
    left; omega
  · exact dsepA_modImg_mh dsepA_regLanes_mh x hx

/-- **The rest of an NZ run lies in the hull of the module.** -/
theorem dsepA_restN_mh (t : ℕ) : ∀ x ∈ restFootN p i r t, dsepAMHat p r x := by
  unfold restFootN
  split_ifs
  · exact dsepA_modImg_mh dsepA_restNZ_mh
  · exact dsepA_grpLanes_mh

/-- **The rest of the Z run lies in the hull of the module.** -/
theorem dsepA_restZ_mh' (t : ℕ) : ∀ x ∈ restFootZ p i r t, dsepAMHat p r x := by
  unfold restFootZ
  split_ifs
  · exact dsepA_modImg_mh dsepA_restZ_mh
  · exact dsepA_grpLanes_mh

end LP

end LeanTheory.Life
