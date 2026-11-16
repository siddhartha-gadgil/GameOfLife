/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepX7

/-!
# The fields `zThr` and `zGate` of `DecSep`

Research note `N-22`. For every `decJz` instruction of a well-formed program:

* `dsepX_zThr`: the main thread of a Z activation (footprint `footMZ`) against the thread of the
  unpaired `KNZ` (its reflectors, station `j` of the line NZ and its footprint `unpFootN`): the
  pieces are far apart (`dsepX_LMZ_LNu`), the routes far from the pieces of the other thread, the
  loop of `KNZ` contains the loops of `C` and `KZ` (`dsepX_N_C`, `dsepX_N_KZ`), the module part
  of the Z thread is right of the channel of `KNZ` and below its port line (`dsepX_MZ_N`), and
  `KNZ` is absorbed before the capture of the Z answer;
* `dsepX_zGate`: both threads against the tight footprint of the INC gate (the rest of the zero
  test by the component check `dsepX_restZ_gate`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The pieces of the main thread of a Z activation -/

/-- Membership in the main thread of a Z activation. -/
theorem dsepX_mem_LMZ {x : Piece} (h : x ∈ decLC p i r ∨ x ∈ modGroup p r ∨ x ∈ decLSZ p i r ∨
    x ∈ decLZu p i r ∨ x ∈ decLF0Z p i r z) : x ∈ decLMZ p i r z := by
  simp only [decLMZ, List.mem_append]
  rcases h with h | h | h | h | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- The pieces of the main thread of a Z activation are pieces of the machine. -/
theorem dsepX_LMZ_mem (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLMZ p i r z, x ∈ machPieces p := by
  intro x hx
  have hr := lt_numRegs_of_dec hi
  simp only [decLMZ, List.mem_append] at hx
  rcases hx with (((h | h) | h) | h) | h
  · exact decLC_mem hi x h
  · exact modGroup_mem hr x h
  · exact decLSZ_mem hi x h
  · exact decLZu_mem hi x h
  · refine decLFZ_mem hp hi x (mem_dd.2 ?_)
    rcases List.mem_append.1 (mem_dd.1 h) with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h

/-- A piece of the main thread of a Z activation is not a piece of the thread of `KNZ`. -/
theorem dsepX_LMZ_not (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g : Piece}
    (hg : g ∈ decLMZ p i r z) (hn : g ∈ decLNu p i r) : False :=
  dsepX_ne_of_far (dsepX_LMZ_mem hp hi g hg) (dsepX_LMZ_LNu hp hi g hg g hn) rfl

/-- The INC gate is not a piece of the main thread of a Z activation nor of the thread of
`KNZ`. -/
theorem dsepX_gate_not (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z))
    (hg : gateP p r ∈ decLMZ p i r z ++ decLNu p i r) : False :=
  dsepX_ne_of_far (decModule_mem (lt_numRegs_of_dec hi) (mem_moduleSpecs_head
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    (dsepX_gate_far hp hi _ hg) rfl

/-! ### `zThr` -/

/-- A set far from the thread of the unpaired `KNZ` at time `t`. -/
def dsepXOkZ (p : Program) (i r t : ℕ) (X : Set Cell) : Prop :=
  FarApart 2 X (boxesOf (decLNu p i r) ∪ unpFootN p i r t)

/-- Unions of sets far from the thread of `KNZ`. -/
theorem dsepXOkZ.union {t : ℕ} {X Y : Set Cell} (hX : dsepXOkZ p i r t X)
    (hY : dsepXOkZ p i r t Y) : dsepXOkZ p i r t (X ∪ Y) := dsepT_far_union hX hY

/-- **The pieces of the main thread of a Z activation are far from the thread of `KNZ`.** -/
theorem dsepX_okZ_static (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) {L : List Piece} (hL : ∀ x ∈ L, x ∈ decLMZ p i r z) :
    dsepXOkZ p i r t (boxesOf L) := by
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_
  · exact (farApart_boxesOf fun g hg => (dsepX_LMZ_LNu hp hi g (hL g hg) h hh).symm').symm'
  · refine (farApart_boxesOf fun g hg => ?_).symm'
    have hg' := hL g hg
    have hcls := dsepX_LMZ_cls hp hi g hg'
    refine dsepX_split_far (fun x hx => dsepX_unpN_split hi h0 hx) ?_ ?_
    · intro x hx y hy
      exact dsepX_N_route_far hp hi hx.1 (dsepX_LMZ_mem hp hi g hg')
        (fun hz => dsepX_LMZ_not hp hi hg' (mem_dd.2 (List.mem_append_left _ hz))) x hx.2 y hy
    · intro x hx y hy
      have := hcls y hy
      omega

/-- A set in the module part of the Z thread is far from the thread of `KNZ`. -/
theorem dsepX_okZ_MZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) {S : Set Cell} (hS : S ⊆ dsepXMZ p r) : dsepXOkZ p i r t S := by
  have hD := one_le_D p
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_)
    ((dsepX_MZ_N hi).mono hS (dsepX_unpN_sub hi h0))
  have hcls := dsepX_LNu_cls hp hi h hh
  refine dsepT_far_cells fun a ha b hb => ?_
  have := hS ha
  have := hcls b hb
  simp only [dsepXMZ, Set.mem_ofPred_eq] at *
  omega

/-- **The control `C` is far from the thread of `KNZ`.** -/
theorem dsepX_okZ_footC (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (ht : t ≤ decTS p i r) : dsepXOkZ p i r t (decFootC p i r t) := by
  have hD := one_le_D p
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_)
    ((dsepX_N_C hi).symm'.mono (dsepX_footC_sub hi h0 ht) (dsepX_unpN_sub hi h0))
  have hcls := dsepX_LNu_cls hp hi h hh
  have hm : h ∈ machPieces p := decLNu_mem hi h hh
  refine dsepX_split_far (fun x hx => dsepX_footC_split hi h0 ht hx) ?_ ?_
  · intro x hx y hy
    refine dsepX_C_route_far hp hi hx.1 hm (fun hc => ?_) x hx.2 y hy
    exact dsepX_LMZ_not hp hi
      (dsepX_mem_LMZ (Or.inl (mem_dd.2 (List.mem_append_left _ hc)))) hh
  · intro x hx y hy
    have := hcls y hy
    omega

/-- **The token `KZ` is far from the thread of `KNZ`.** -/
theorem dsepX_okZ_tokZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (ht : t ≤ decCapZ p i r) : dsepXOkZ p i r t (tokFootZ p i r t) := by
  have hD := one_le_D p
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_)
    ((dsepX_N_KZ hi).symm'.mono (dsepX_tokZ_sub hi h0 ht) (dsepX_unpN_sub hi h0))
  have hcls := dsepX_LNu_cls hp hi h hh
  have hm : h ∈ machPieces p := decLNu_mem hi h hh
  refine dsepX_split_far (fun x hx => dsepX_tokZ_split hi h0 ht hx) ?_ ?_
  · intro x hx y hy
    refine dsepX_Z_route_far hp hi hx.1 hm (fun hc => ?_) x hx.2 y hy
    exact dsepX_LMZ_not hp hi
      (dsepX_mem_LMZ (Or.inr (Or.inr (Or.inr (Or.inl (mem_dd.2 (List.mem_append_left _ hc)))))))
      hh
  · intro x hx y hy
    have := hcls y hy
    omega

/-- The unpaired `KNZ` is absorbed before the capture of the Z answer. -/
theorem dsepX_unpN_empty {t : ℕ} (ht : decCapZ p i r ≤ t) : unpFootN p i r t = ∅ := by
  unfold unpFootN
  simp only [show ¬ t ≤ decCapN p i r by unfold decCapZ decCapN at *; omega,
    show ¬ t ≤ decCapN p i r + 292 by unfold decCapZ decCapN at *; omega, ↓reduceIte]

/-- **The end of the Z activation is far from the thread of `KNZ`.** -/
theorem dsepX_okZ_fin (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCapZ p i r ≤ t) (h2 : t < decEndZ p i r z) :
    dsepXOkZ p i r t (finFootZ p i r z t) := by
  have hD := one_le_D p
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_
  · have hcls := dsepX_LNu_cls hp hi h hh
    have hm : h ∈ machPieces p := decLNu_mem hi h hh
    refine dsepX_finZ_far hp hi h1 h2 hm (fun hc => ?_) (fun hc => ?_) ?_
    · exact dsepX_LMZ_not hp hi (dsepX_mem_LMZ (Or.inr (Or.inr (Or.inr (Or.inr
        (mem_dd.2 (List.mem_append_left _ hc))))))) hh
    · exact dsepX_LMZ_not hp hi (dsepX_mem_LMZ (Or.inr (Or.inr (Or.inr (Or.inr
        (mem_dd.2 (List.mem_append_right _ hc))))))) hh
    · refine dsepT_far_cells fun a ha b hb => ?_
      have := ha.2
      have := hcls b hb
      simp only [Set.mem_ofPred_eq] at *
      omega
  · rw [dsepX_unpN_empty h1]
    intro _ _ _ hb
    exact hb.elim

/-- The rest of the Z register run is far from the thread of `KNZ`. -/
theorem dsepX_okZ_rest (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) : dsepXOkZ p i r t (restFootZ p i r t) := by
  unfold restFootZ
  split_ifs with h
  · exact dsepX_okZ_MZ hp hi h0 ((dsepX_modImg_H dsepX_restZ_H).trans Set.inter_subset_right)
  · exact (dsepX_okZ_static hp hi h0 fun x hx => dsepX_mem_LMZ (Or.inr (Or.inl hx))).union
      (dsepX_okZ_MZ hp hi h0 (dsepX_lanes_M.trans Set.inter_subset_right))

/-- **`DecSep.zThr`**: the main thread of a Z activation is far from the thread of the unpaired
`KNZ` at every generation. -/
theorem dsepX_zThr (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z →
      FarApart 2 (footMZ p i r z t) (boxesOf (decLNu p i r) ∪ unpFootN p i r t) := by
  intro t h0 h1
  have hLC : ∀ x ∈ decLC p i r, x ∈ decLMZ p i r z := fun x hx => dsepX_mem_LMZ (Or.inl hx)
  have hG : ∀ x ∈ modGroup p r, x ∈ decLMZ p i r z := fun x hx =>
    dsepX_mem_LMZ (Or.inr (Or.inl hx))
  have hSZ : ∀ x ∈ decLSZ p i r, x ∈ decLMZ p i r z := fun x hx =>
    dsepX_mem_LMZ (Or.inr (Or.inr (Or.inl hx)))
  have hZu : ∀ x ∈ decLZu p i r, x ∈ decLMZ p i r z := fun x hx =>
    dsepX_mem_LMZ (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  have hF0 : ∀ x ∈ decLF0Z p i r z, x ∈ decLMZ p i r z := fun x hx =>
    dsepX_mem_LMZ (Or.inr (Or.inr (Or.inr (Or.inr hx))))
  have hLZ : ∀ x ∈ decLZ p i r, x ∈ decLMZ p i r z := fun x hx =>
    hZu x (mem_dd.2 (List.mem_append_left _ (mem_dd.1 hx)))
  have hFZ : ∀ x ∈ decLFZ p i r z, x ∈ decLMZ p i r z := by
    intro x hx
    rcases List.mem_append.1 (mem_dd.1 hx) with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hZu x (mem_dd.2 (List.mem_append_right _ h))
      · exact hF0 x (mem_dd.2 (List.mem_append_left _ h))
    · exact hF0 x (mem_dd.2 (List.mem_append_right _ h))
  have happ : ∀ {A B : List Piece}, (∀ x ∈ A, x ∈ decLMZ p i r z) →
      (∀ x ∈ B, x ∈ decLMZ p i r z) → ∀ x ∈ A ++ B, x ∈ decLMZ p i r z := by
    intro A B hA hB x hx
    rcases List.mem_append.1 hx with h | h
    · exact hA x h
    · exact hB x h
  have hst := fun {L : List Piece} (hL : ∀ x ∈ L, x ∈ decLMZ p i r z) =>
    dsepX_okZ_static hp hi h0 hL
  have hMZ := fun {S : Set Cell} (hS : S ⊆ dsepXMZ p r) => dsepX_okZ_MZ hp hi h0 hS
  change dsepXOkZ p i r t (footMZ p i r z t)
  unfold footMZ
  split_ifs with hc
  · refine (hst hF0).union ((?_ : dsepXOkZ p i r t (qFootZ p i r t)).union
      ((hst hZu).union (dsepX_okZ_tokZ hp hi h0 hc)))
    unfold qFootZ
    split_ifs with ha hb
    · exact (hst (happ hG hSZ)).union (((hst hLC).union (dsepX_okZ_footC hp hi h0 ha)).union
        (hMZ (dsepX_lanes_M.trans Set.inter_subset_right)))
    · exact (hst (happ hLC hSZ)).union
        (hMZ ((dsepX_modImg_H dsepX_runZ_H).trans Set.inter_subset_right))
    · exact (hst hLC).union ((dsepX_okZ_rest hp hi h0).union ((hst hSZ).union
        (hMZ ((dsepX_ansZ_M hi (by omega)).trans Set.inter_subset_left))))
  · exact (hst (happ (happ hLC hSZ) hLZ)).union ((dsepX_okZ_rest hp hi h0).union
      ((hst hFZ).union (dsepX_okZ_fin hp hi (by omega) h1)))

/-! ### `zGate` -/

/-- A set far from the tight footprint of the INC gate. -/
def dsepXOkG (p : Program) (r : ℕ) (X : Set Cell) : Prop := FarApart 2 X (gateFoot p r)

/-- Unions of sets far from the INC gate. -/
theorem dsepXOkG.union {X Y : Set Cell} (hX : dsepXOkG p r X) (hY : dsepXOkG p r Y) :
    dsepXOkG p r (X ∪ Y) := dsepT_far_union hX hY

/-- Far from the box of the INC gate, far from its tight footprint. -/
theorem dsepX_okG_box {X : Set Cell} (h : FarApart 2 X (gateP p r).box) : dsepXOkG p r X :=
  h.mono le_rfl (gateFoot_subset p r)

/-- The cells of the box of the INC gate, in coordinates. -/
theorem dsepX_gate_cells {y : Cell} (hy : y ∈ (gateP p r).box) :
    U p r + 127 ≤ y.1 - y.2 ∧ y.1 - y.2 ≤ U p r + 249 ∧ -2423 ≤ y.1 + y.2 ∧
      y.1 + y.2 ≤ -2301 := by
  have hu := modD_uv p r
  rw [isep2_gateP_box] at hy
  obtain ⟨y1, y2, y3, y4⟩ := hy
  omega

/-- **`DecSep.zGate`**: the main thread of a Z activation and the thread of the unpaired `KNZ`
are far from the tight footprint of the INC gate at every generation. -/
theorem dsepX_zGate (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z →
      FarApart 2 (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪ unpFootN p i r t))
        (gateFoot p r) := by
  intro t h0 h1
  have hr := lt_numRegs_of_dec hi
  have hD := one_le_D p
  have hgm : gateP p r ∈ machPieces p := decModule_mem hr (mem_moduleSpecs_head
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hnot : ∀ {L : List Piece}, (∀ x ∈ L, x ∈ decLMZ p i r z ++ decLNu p i r) →
      gateP p r ∉ L := fun hL hg => dsepX_gate_not hp hi (hL _ hg)
  have hst : ∀ {L : List Piece}, (∀ x ∈ L, x ∈ decLMZ p i r z ++ decLNu p i r) →
      dsepXOkG p r (boxesOf L) := fun hL =>
    dsepX_okG_box (farApart_boxesOf fun g hg => (dsepX_gate_far hp hi g (hL g hg)).symm').symm'
  have hZ : ∀ {L : List Piece}, (∀ x ∈ L, x ∈ decLMZ p i r z) →
      ∀ x ∈ L, x ∈ decLMZ p i r z ++ decLNu p i r :=
    fun hL x hx => List.mem_append_left _ (hL x hx)
  have hLC : ∀ x ∈ decLC p i r, x ∈ decLMZ p i r z := fun x hx => dsepX_mem_LMZ (Or.inl hx)
  have hG : ∀ x ∈ modGroup p r, x ∈ decLMZ p i r z := fun x hx =>
    dsepX_mem_LMZ (Or.inr (Or.inl hx))
  have hSZ : ∀ x ∈ decLSZ p i r, x ∈ decLMZ p i r z := fun x hx =>
    dsepX_mem_LMZ (Or.inr (Or.inr (Or.inl hx)))
  have hZu : ∀ x ∈ decLZu p i r, x ∈ decLMZ p i r z := fun x hx =>
    dsepX_mem_LMZ (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  have hF0 : ∀ x ∈ decLF0Z p i r z, x ∈ decLMZ p i r z := fun x hx =>
    dsepX_mem_LMZ (Or.inr (Or.inr (Or.inr (Or.inr hx))))
  have hLZ : ∀ x ∈ decLZ p i r, x ∈ decLMZ p i r z := fun x hx =>
    hZu x (mem_dd.2 (List.mem_append_left _ (mem_dd.1 hx)))
  have hFZ : ∀ x ∈ decLFZ p i r z, x ∈ decLMZ p i r z := by
    intro x hx
    rcases List.mem_append.1 (mem_dd.1 hx) with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hZu x (mem_dd.2 (List.mem_append_right _ h))
      · exact hF0 x (mem_dd.2 (List.mem_append_left _ h))
    · exact hF0 x (mem_dd.2 (List.mem_append_right _ h))
  have happ : ∀ {A B : List Piece}, (∀ x ∈ A, x ∈ decLMZ p i r z) →
      (∀ x ∈ B, x ∈ decLMZ p i r z) → ∀ x ∈ A ++ B, x ∈ decLMZ p i r z := by
    intro A B hA hB x hx
    rcases List.mem_append.1 hx with h | h
    · exact hA x h
    · exact hB x h
  have hlanes : dsepXOkG p r (modLanes p r) :=
    dsepX_okG_box ((machBoxes_far hp r).symm'.mono le_rfl
      (fun x hx => mem_boxesOf.2 ⟨gateP p r, hgm, hx⟩))
  have hgrp : gateP p r ∉ modGroup p r := hnot fun x hx => hZ hG x hx
  have hrest : dsepXOkG p r (restFootZ p i r t) := by
    unfold restFootZ
    split_ifs
    · exact dsepX_restZ_gate
    · exact (hst (hZ hG)).union hlanes
  have hfoot : dsepXOkG p r (footMZ p i r z t) := by
    unfold footMZ
    split_ifs with hc
    · refine (hst (hZ hF0)).union ((?_ : dsepXOkG p r (qFootZ p i r t)).union
        ((hst (hZ hZu)).union (dsepX_okG_box ?_)))
      · unfold qFootZ
        split_ifs with ha hb
        · refine (hst (hZ (happ hG hSZ))).union (((hst (hZ hLC)).union
            (dsepX_okG_box ?_)).union hlanes)
          refine dsepX_split_far (fun x hx => dsepX_footC_split hi h0 ha hx) ?_ ?_
          · intro x hx y hy
            exact dsepX_C_route_far hp hi hx.1 hgm (fun hc => hnot (hZ hLC) (mem_dd.2
              (List.mem_append_left _ hc))) x hx.2 y hy
          · intro x hx y hy
            have := dsepX_gate_cells hy
            omega
        · exact (hst (hZ (happ hLC hSZ))).union
            (dsepX_okG_box (dsepT_runZ_far hp hr _ hgm hgrp))
        · refine (hst (hZ hLC)).union (hrest.union ((hst (hZ hSZ)).union
            (dsepX_okG_box ?_)))
          refine dsepT_far_cells fun a ha b hb => ?_
          have := (dsepX_ansZ_M hi (by omega) ha).2
          have := dsepX_gate_cells hb
          simp only [Set.mem_ofPred_eq] at *
          omega
      · refine dsepX_split_far (fun x hx => dsepX_tokZ_split hi h0 hc hx) ?_ ?_
        · intro x hx y hy
          exact dsepX_Z_route_far hp hi hx.1 hgm (fun hz => hnot (hZ hZu) (mem_dd.2
            (List.mem_append_left _ hz))) x hx.2 y hy
        · intro x hx y hy
          have := dsepX_gate_cells hy
          omega
    · refine (hst (hZ (happ (happ hLC hSZ) hLZ))).union (hrest.union
        ((hst (hZ hFZ)).union (dsepX_okG_box ?_)))
      refine dsepX_finZ_far hp hi (by omega) h1 hgm
        (fun hc => hnot (hZ hF0) (mem_dd.2 (List.mem_append_left _ hc)))
        (fun hc => hnot (hZ hF0) (mem_dd.2 (List.mem_append_right _ hc))) ?_
      refine dsepT_far_cells fun a ha b hb => ?_
      have := ha.2
      have := dsepX_gate_cells hb
      simp only [Set.mem_ofPred_eq] at *
      omega
  have hunp : dsepXOkG p r (unpFootN p i r t) := by
    refine dsepX_okG_box (dsepX_split_far (fun x hx => dsepX_unpN_split hi h0 hx) ?_ ?_)
    · intro x hx y hy
      exact dsepX_N_route_far hp hi hx.1 hgm (fun hz => hnot (fun x hx =>
        List.mem_append_right _ hx) (mem_dd.2 (List.mem_append_left _ hz))) x hx.2 y hy
    · intro x hx y hy
      have := dsepX_gate_cells hy
      omega
  exact hfoot.union ((hst fun x hx => List.mem_append_right _ hx).union hunp)

end LP

end LeanTheory.Life
