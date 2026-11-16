/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepThr3

/-!
# The control thread below the circuit: the fields `nQ1b`, `zQ1b`, `nQ3b`, `zQ3b` of `DecSep`

Research note `N-22`. The pieces of the control thread (reflectors of `C`, DEC copies) lie low
(below the module, `v ≤ modTop - 60`), left of the module (`u ≤ U_r - 768`) or in the DEC chain
(`v ≤ -3305`) (`dsepT_LC_cells`), and the footprint of the control before the register run lies at
`v ≤ -2350` (`dsepT_footC_v`). The circuit, the stations, the lanes, the answers and the rest of
the register runs lie above (`dsepT_LC_far`):

* `dsepT_nQ1b`, `dsepT_zQ1b`: the fields `nQ1b`, `zQ1b`;
* `dsepT_nQ3b`, `dsepT_zQ3b`: the fields `nQ3b`, `zQ3b` (the rest of the run far from the
  pieces outside the circuit, `DecSepThr2`, and the INC gate is not a piece of the control).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- Two sets whose cells are `≥ 5` apart in `u` or in `v` are far apart. -/
theorem dsepT_far_cells {A B : Set Cell}
    (h : ∀ a ∈ A, ∀ b ∈ B, a.1 - a.2 + 5 ≤ b.1 - b.2 ∨ b.1 - b.2 + 5 ≤ a.1 - a.2 ∨
      a.1 + a.2 + 5 ≤ b.1 + b.2 ∨ b.1 + b.2 + 5 ≤ a.1 + a.2) : FarApart 2 A B := by
  intro a ha b hb hn
  have := h a ha b hb
  obtain ⟨n1, n2, n3, n4⟩ := hn
  push_cast at n1 n2 n3 n4
  omega

/-- A union far from a set. -/
theorem dsepT_far_union {A B C : Set Cell} (h1 : FarApart 2 A C) (h2 : FarApart 2 B C) :
    FarApart 2 (A ∪ B) C := fun x hx y hy => hx.elim (h1 x · y hy) (h2 x · y hy)

/-- The cells of the pieces of the control thread: below the module, left of it or in the DEC
chain. -/
def dsepTLow (c : Cell) : Prop := c.1 + c.2 ≤ -3300

/-- **The cells of the pieces of the control thread are low.** -/
theorem dsepT_LC_cells (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLC p i r, ∀ c ∈ g.box, dsepTLow c := by
  intro g hg c hc
  have hu := modD_uv p r
  have hf := lane_VT_low p
  have hf' := layout_facts p
  have hj := dsepM_j_lt hi
  simp only [dsepTLow]
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
      have hpv : decPortV p (2 * ((callerIdx p r i : ℕ) : ℤ)) ≤ -3450 := by
        unfold decPortV; omega
      omega
  · rw [dsepM_copy_box] at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    omega

/-- **A set above `v = -3290` is far from the pieces of the control thread.** -/
theorem dsepT_LC_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {S : Set Cell}
    (hS : ∀ x ∈ S, -3290 ≤ x.1 + x.2) : ∀ g ∈ decLC p i r, FarApart 2 S g.box := by
  intro g hg
  refine dsepT_far_cells fun a ha b hb => ?_
  have h1 := hS a ha
  have h2 := dsepT_LC_cells hp hi g hg b hb
  simp only [dsepTLow] at h2
  omega

/-- The cells of the groups of the circuit are above the control thread. -/
theorem dsepT_grp_up {g : Piece} (hg : g ∈ modGroup p r) :
    ∀ x ∈ g.box, U p r - 760 ≤ x.1 - x.2 ∧ -2324 ≤ x.1 + x.2 := by
  intro x hx
  have := dsepT_grp_cells hg x hx
  simp only [dsepTGrpHull] at this
  omega

/-- The cells of the NZ stations are above the control thread. -/
theorem dsepT_LSN_up {g : Piece} (hg : g ∈ decLSN p i r) :
    ∀ x ∈ g.box, U p r - 760 ≤ x.1 - x.2 ∧ 1177 ≤ x.1 + x.2 := by
  have hu := modD_uv p r
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hg)
  obtain ⟨j', -, i', hi', rfl⟩ := mem_stationSpecs hs
  have := stNZ_cases i' hi'
  rw [isep2_spec_box]
  rintro x ⟨x1, x2, x3, x4⟩
  omega

/-- The cells of the Z stations are above the control thread. -/
theorem dsepT_LSZ_up {g : Piece} (hg : g ∈ decLSZ p i r) :
    ∀ x ∈ g.box, U p r - 760 ≤ x.1 - x.2 ∧ 500 ≤ x.1 + x.2 := by
  have hu := modD_uv p r
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hg)
  obtain ⟨j', -, i', hi', rfl⟩ := mem_stationZSpecs hs
  have := stZ_cases i' hi'
  rw [isep2_spec_box]
  rintro x ⟨x1, x2, x3, x4⟩
  omega

/-- The cells of the lanes of register `r` are above the control thread. -/
theorem dsepT_lanes_up : ∀ x ∈ modLanes p r, U p r - 760 ≤ x.1 - x.2 ∧ 354 ≤ x.1 + x.2 := by
  have hu := modD_uv p r
  rintro _ ⟨c, ⟨c1, c2, c3⟩, rfl⟩
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- The corners of the route of `C` lie at `v ≤ -3281`. -/
theorem dsepT_cornC_v (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ c ∈ decCornC p i r, c.v + 70 ≤ -3281 := by
  intro c hc
  have hcm := dsepM_corner_mem hi (dsepM_specs hi).2.1 c hc
  have hv := allCorners_valid hp c hcm
  have hf := layout_facts p
  have hj := dsepM_j_lt hi
  rcases dsepM_down_cases hc with ⟨b, k, h', ht⟩ | rfl
  · obtain ⟨k0, u, v, tag⟩ := c
    simp only at ht
    subst ht
    simp only [Valid] at hv
    simp only
    omega
  · simp only [decPortV]
    omega

/-- **The footprint of the control before the register run lies at `v ≤ -2350`.** -/
theorem dsepT_footC_v (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t)
    (ht : t < decTS p i r) : ∀ x ∈ decFootC p i r t, x.1 + x.2 ≤ -2350 := by
  have hu := modD_uv p r
  have hui := unitD_uv p i
  have hV := lane_VT_low p
  have hm := decM_cast p hi
  obtain ⟨h1, h2⟩ := lane_route_vlow (-2350) (decCornC p i r) (unitWL p i decRWL) 4260
    ⟨Or.inl rfl, Or.inl rfl⟩ (decC_lines p i r).1 (decC_timedX p hi)
    (fun c hc => by have := dsepT_cornC_v hp hi c hc; omega) (by
      simp only [unitWL, decRWL, WL.shift, WL.vHi, WL.px, WL.py, WL.qt]
      omega)
  intro x hx
  unfold decFootC at hx
  split_ifs at hx with ha hb hc
  · unfold flyFoot at hx
    split_ifs at hx with hd
    · exact h1 (t - 4260) (by omega) x hx
    · refine (WL.le_vHi hx).trans ?_
      have hg := decGC_eq p i r
      have hdx : (route (unitWL p i decRWL) (decCornC p i r)).2.dx = 1 := by
        change (decGC p i r).dx = 1; rw [hg]
      rw [WL.vHi_const (by change (decGC p i r).dx + (decGC p i r).dy = 0; rw [hg]; rfl)
        (Or.inl hdx) _ (routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 : ℤ)]
      exact h2
  · obtain ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · obtain ⟨d, ⟨j, hj, d1, d2, d3, d4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add] at *
    have : (j : ℤ) ≤ (decM p i r : ℤ) := by omega
    nlinarith
  · obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    have e1 : decTS p i r = decTB p i r + 1771 := by unfold decTS decTB; omega
    simp only [cp0WL, WL.px, WL.py, WL.qt, Prod.fst_add, Prod.snd_add] at *
    omega

/-! ### The fields -/

/-- The boxes of a list of pieces above `v = -3290`. -/
theorem dsepT_boxesOf_up {L : List Piece} (h : ∀ g ∈ L, ∀ y ∈ g.box, -3290 ≤ y.1 + y.2) :
    ∀ x ∈ boxesOf L, -3290 ≤ x.1 + x.2 := by
  intro x hx
  obtain ⟨g, hg, hx⟩ := mem_boxesOf.1 hx
  exact h g hg x hx

/-- The cells of the groups of the circuit and of the NZ stations are above `v = -2324`. -/
theorem dsepT_grpLSN_up {g : Piece} (hg : g ∈ modGroup p r ++ decLSN p i r) :
    ∀ x ∈ g.box, -2324 ≤ x.1 + x.2 := by
  intro x hx
  rcases List.mem_append.1 hg with hg | hg
  · exact (dsepT_grp_up hg x hx).2
  · have := (dsepT_LSN_up hg x hx).2; omega

/-- The cells of the groups of the circuit and of the Z stations are above `v = -2324`. -/
theorem dsepT_grpLSZ_up {g : Piece} (hg : g ∈ modGroup p r ++ decLSZ p i r) :
    ∀ x ∈ g.box, -2324 ≤ x.1 + x.2 := by
  intro x hx
  rcases List.mem_append.1 hg with hg | hg
  · exact (dsepT_grp_up hg x hx).2
  · have := (dsepT_LSZ_up hg x hx).2; omega

/-- The control, its pieces and the lanes of its register are far from a piece of the machine
above `v = -2324`. -/
theorem dsepT_Q1b (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t < decTS p i r) {g : Piece} (hgm : g ∈ machPieces p)
    (hup : ∀ x ∈ g.box, -2324 ≤ x.1 + x.2) :
    FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r) g.box := by
  refine dsepT_far_union (dsepT_far_union ?_ ?_) ?_
  · refine (farApart_boxesOf fun h hh => ?_).symm'
    refine dsepT_far_cells fun a ha b hb => ?_
    have := dsepT_LC_cells hp hi h hh b hb
    have := hup a ha
    simp only [dsepTLow] at *
    omega
  · refine dsepT_far_cells fun a ha b hb => ?_
    have := dsepT_footC_v hp hi h0 ht a ha
    have := hup b hb
    omega
  · exact (machBoxes_far hp r).symm'.mono le_rfl
      (fun x hx => mem_boxesOf.2 ⟨g, hgm, hx⟩)

/-- **`DecSep.nQ1b`.** -/
theorem dsepT_nQ1b (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decTS p i r → ∀ g ∈ modGroup p r ++ decLSN p i r,
      FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r) g.box := by
  intro t h0 ht g hg
  have hr := lt_numRegs_of_dec hi
  have hgm : g ∈ machPieces p := by
    rcases List.mem_append.1 hg with h | h
    · exact modGroup_mem hr g h
    · exact decLSN_mem hi g h
  exact dsepT_Q1b hp hi h0 ht hgm (dsepT_grpLSN_up hg)

/-- **`DecSep.zQ1b`.** -/
theorem dsepT_zQ1b (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decTS p i r → ∀ g ∈ modGroup p r ++ decLSZ p i r,
      FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r) g.box := by
  intro t h0 ht g hg
  have hr := lt_numRegs_of_dec hi
  have hgm : g ∈ machPieces p := by
    rcases List.mem_append.1 hg with h | h
    · exact modGroup_mem hr g h
    · exact decLSZ_mem hi g h
  exact dsepT_Q1b hp hi h0 ht hgm (dsepT_grpLSZ_up hg)

/-- The station footprint of the NZ answers lies above `v = 1164`. -/
theorem dsepT_chainNZ_up {j : ℕ} {c : Cell}
    (hc : c ∈ modImg p r (chainFoot stNZRY (72, 72) j)) : 1164 ≤ c.1 + c.2 := by
  have hu := modD_uv p r
  obtain ⟨d, ⟨k, hk, hd⟩, rfl⟩ := hc
  simp only [Prod.fst_add, Prod.snd_add]
  rcases hd with (((⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) | ⟨h1, h2, h3, h4⟩) |
    ⟨m, m0, m1, h1, h2, h3, h4⟩) <;> simp only at h1 h2 h3 h4 <;> omega

/-- The station footprint of the Z answers lies above `v = 400`. -/
theorem dsepT_chainZ_up {j : ℕ} {c : Cell}
    (hc : c ∈ modImg p r (chainFoot stZR (72, -72) j)) : 400 ≤ c.1 + c.2 := by
  have hu := modD_uv p r
  obtain ⟨d, ⟨k, hk, hd⟩, rfl⟩ := hc
  simp only [Prod.fst_add, Prod.snd_add]
  rcases hd with (((⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) | ⟨h1, h2, h3, h4⟩) |
    ⟨m, m0, m1, h1, h2, h3, h4⟩) <;> simp only at h1 h2 h3 h4 <;> omega

/-- A piece of the control thread is not the INC gate. -/
theorem dsepT_LC_not_gate (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLC p i r, g ∉ modGroup p r ++ [gateP p r] := by
  intro g hg hm
  rcases List.mem_append.1 hm with hm | hm
  · exact dsepT_LC_not_grp hp hi g hg hm
  · rw [List.mem_singleton.1 hm] at hg
    have hu := modD_uv p r
    have := dsepT_LC_cells hp hi _ hg (modDX p r - 1132, modDY p r - 1291) (by
      simp only [gateP, incGateSpec, PSpec.piece, Piece.place, Piece.box, Box, Base.piece,
        orGateP, Set.mem_ofPred_eq]
      omega)
    simp only [dsepTLow] at this
    omega

/-- **`DecSep.nQ3b`.** -/
theorem dsepT_nQ3b (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, decCutN p i r ≤ t → t < decCapN p i r → ∀ g ∈ decLC p i r,
      FarApart 2 (restFootN p i r t ∪ (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t))
        g.box := by
  intro t h1 h2 g hg
  have hr := lt_numRegs_of_dec hi
  have hu := modD_uv p r
  have hgm := decLC_mem hi g hg
  refine dsepT_far_union ?_ (dsepT_far_union ?_ ?_)
  · unfold restFootN
    split_ifs
    · exact dsepT_restNZ_far hp hr g hgm (dsepT_LC_not_grp hp hi g hg)
    · refine dsepT_LC_far hp hi (fun x hx => ?_) g hg
      rcases hx with hx | hx
      · exact dsepT_boxesOf_up (fun h hh y hy => by
          have := (dsepT_grp_up hh y hy).2; omega) x hx
      · have := (dsepT_lanes_up (p := p) (r := r) x hx).2; omega
  · exact dsepT_LC_far hp hi (dsepT_boxesOf_up fun h hh y hy => by
      have := (dsepT_LSN_up hh y hy).2; omega) g hg
  · refine dsepT_LC_far hp hi (fun x hx => ?_) g hg
    unfold decAnsFootN at hx
    split_ifs at hx
    · obtain ⟨hTS, -, -⟩ := decTS_facts p hi
      obtain ⟨x1, x2, x3, x4⟩ := hx
      simp only [decAnsWLN, modWL, ansNZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
      simp only [decCutN] at h1
      omega
    · have := dsepT_chainNZ_up hx; omega

/-- **`DecSep.zQ3b`.** -/
theorem dsepT_zQ3b (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, decCutZ p i r ≤ t → t < decCapZ p i r → ∀ g ∈ decLC p i r,
      FarApart 2 (restFootZ p i r t ∪ (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t))
        g.box := by
  intro t h1 h2 g hg
  have hr := lt_numRegs_of_dec hi
  have hu := modD_uv p r
  have hgm := decLC_mem hi g hg
  refine dsepT_far_union ?_ (dsepT_far_union ?_ ?_)
  · unfold restFootZ
    split_ifs
    · exact dsepT_restZ_far hp hr g hgm (dsepT_LC_not_gate hp hi g hg)
    · refine dsepT_LC_far hp hi (fun x hx => ?_) g hg
      rcases hx with hx | hx
      · exact dsepT_boxesOf_up (fun h hh y hy => by
          have := (dsepT_grp_up hh y hy).2; omega) x hx
      · have := (dsepT_lanes_up (p := p) (r := r) x hx).2; omega
  · exact dsepT_LC_far hp hi (dsepT_boxesOf_up fun h hh y hy => by
      have := (dsepT_LSZ_up hh y hy).2; omega) g hg
  · refine dsepT_LC_far hp hi (fun x hx => ?_) g hg
    unfold decAnsFootZ at hx
    split_ifs at hx
    · obtain ⟨x1, x2, x3, x4⟩ := hx
      simp only [decAnsWLZ, modWL, ansZWL, WL.shift, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
      omega
    · have := dsepT_chainZ_up hx; omega

end LP

end LeanTheory.Life
