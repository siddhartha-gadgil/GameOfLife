/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepThr2

/-!
# The thread fields `nQ2` and `zQ2` of `DecSep`

Research note `N-22`. The regions of the register runs before the cut are far from every piece of
the machine outside the circuit (`dsepT_runNZ_far`, `dsepT_runZ_far`, generated in
`DecSepThr2`). The pieces of the control thread (reflectors of `C`, DEC copies) and the stations
are not pieces of the circuit (`dsepT_LC_not_grp`, `dsepT_LSN_not_grp`, `dsepT_LSZ_not_grp`: their
boxes lie outside the `uv`-hull of the circuit, `dsepT_grp_cells`), hence:

* `dsepT_nQ2`: the field `nQ2`;
* `dsepT_zQ2`: the field `zQ2`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- The `uv`-hull of the circuit of module `r`. -/
def dsepTGrpHull (p : Program) (r : ℕ) (c : Cell) : Prop :=
  U p r - 738 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r + 798 ∧ -2324 ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ 670

/-- Every cell of the box of a group of the circuit lies in the hull of the circuit. -/
theorem dsepT_grp_cells {g : Piece} (hg : g ∈ modGroup p r) : ∀ c ∈ g.box, dsepTGrpHull p r c := by
  have hu := modD_uv p r
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  obtain ⟨b, hb, rfl⟩ := mem_groupSpecs hs
  obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hb
  have := dz2g_facts i' (List.mem_range.1 hi')
  rintro c ⟨c1, c2, c3, c4⟩
  simp only [PSpec.piece, Piece.place] at c1 c2 c3 c4
  simp only [dsepTGrpHull]
  omega

/-- A piece of the machine whose box has no cell in the hull of the circuit is not a group of the
circuit. -/
theorem dsepT_not_grp {g : Piece} (hg : g ∈ machPieces p)
    (h : ∀ c ∈ g.box, ¬ dsepTGrpHull p r c) : g ∉ modGroup p r := by
  intro hm
  have hn := dsepT_mach_ne hg
  have hc : (g.a, g.lo) ∈ g.box := ⟨le_rfl, hn.1, le_rfl, hn.2⟩
  exact h _ hc (dsepT_grp_cells hm _ hc)

/-- **The pieces of the control thread are not groups of the circuit.** -/
theorem dsepT_LC_not_grp (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLC p i r, g ∉ modGroup p r := by
  intro g hg
  have hu := modD_uv p r
  have hf := lane_VT_low p
  refine dsepT_not_grp (decLC_mem hi g hg) fun c hc hh => ?_
  simp only [dsepTGrpHull] at hh
  rcases dsepM_mem_decLC hg with hr | ⟨m', hm', rfl⟩
  · obtain ⟨cr, hcr, hb⟩ := dsepM_reflP_mem hr
    have hcm := dsepM_corner_mem hi (dsepM_specs hi).2.1 cr hcr
    have hv := allCorners_valid hp cr hcm
    have hcu := corner_uv cr
    rw [hb] at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    unfold BoxT.InUV at hcu
    rcases dsepM_down_cases hcr with ⟨b, k, h', ht⟩ | rfl
    · obtain ⟨k0, u, v, tag⟩ := cr
      simp only at ht
      subst ht
      simp only [Valid] at hv
      simp only at hcu
      omega
    · simp only [Valid] at hv
      simp only at hcu
      omega
  · rw [dsepM_copy_box] at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    omega

/-- **The NZ stations `0 … j - 1` are not groups of the circuit.** -/
theorem dsepT_LSN_not_grp (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLSN p i r, g ∉ modGroup p r := by
  intro g hg
  have hu := modD_uv p r
  refine dsepT_not_grp (decLSN_mem hi g hg) fun c hc hh => ?_
  simp only [dsepTGrpHull] at hh
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hg)
  obtain ⟨j', -, i', hi', rfl⟩ := mem_stationSpecs hs
  have := stNZ_cases i' hi'
  rw [isep2_spec_box] at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  omega

/-- **The Z stations `0 … j - 1` are not groups of the circuit.** -/
theorem dsepT_LSZ_not_grp (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLSZ p i r, g ∉ modGroup p r := by
  intro g hg
  have hu := modD_uv p r
  refine dsepT_not_grp (decLSZ_mem hi g hg) fun c hc hh => ?_
  simp only [dsepTGrpHull] at hh
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hg)
  obtain ⟨j', -, i', hi', rfl⟩ := mem_stationZSpecs hs
  have := stZ_cases i' hi'
  rw [isep2_spec_box] at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  omega

/-- **`DecSep.nQ2`**: the NZ run region before the cut is far from the pieces of the control
thread and from the NZ stations `0 … j - 1`. -/
theorem dsepT_nQ2 (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLC p i r ++ decLSN p i r, FarApart 2 (modImg p r decRunRegNZ) g.box := by
  have hr := lt_numRegs_of_dec hi
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · exact dsepT_runNZ_far hp hr g (decLC_mem hi g hg) (dsepT_LC_not_grp hp hi g hg)
  · exact dsepT_runNZ_far hp hr g (decLSN_mem hi g hg) (dsepT_LSN_not_grp hi g hg)

/-- **`DecSep.zQ2`**: the Z run region before the cut is far from the pieces of the control
thread and from the Z stations `0 … j - 1`. -/
theorem dsepT_zQ2 (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLC p i r ++ decLSZ p i r, FarApart 2 (modImg p r decRunRegZ) g.box := by
  have hr := lt_numRegs_of_dec hi
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · exact dsepT_runZ_far hp hr g (decLC_mem hi g hg) (dsepT_LC_not_grp hp hi g hg)
  · exact dsepT_runZ_far hp hr g (decLSZ_mem hi g hg) (dsepT_LSZ_not_grp hi g hg)

end LP

end LeanTheory.Life
