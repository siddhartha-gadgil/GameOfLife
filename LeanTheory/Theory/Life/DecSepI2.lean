/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepI1

/-!
# The idle fields of `DecSep`: the control thread

Research note `N-22`. The moving footprint of the control `decFootC` (the route of `C`, its flight
to DEC copy `m`, their joint approach, the DEC chain and the flight of `C'`) is far from every
piece of the machine outside the control thread and the register circuit (`dsepI_footC_far`):

* `dsepI_route_far`, `dsepI_flyFoot_far`: a route with corner windows separated in the machine
  (`RouteSepX`) is far from every piece but its reflectors (`isep2_rfoot_far`), and so is a route
  followed by a flight far from the pieces outside a list;
* `dsepI_flyC_far`: the flight of `C` (in the band of module `r`, `dsepT_mod_far`; the port
  corner of `C` by `dsepM_final_far`, the other corners of the left zone by their port lines);
* `dsepI_sideC_far`, `dsepI_chainC_far`, `dsepI_cpC_far`: the module-local parts
  (`dsepT_zone_far`, `dsepT_mod_cls`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Routes -/

/-- **A route with corner windows separated in the machine is far from every piece of the
machine but its reflectors.** -/
theorem dsepI_route_far {Z : Set Cell} {g : WL} {cs : List Corner} {T : ℕ}
    (hsep : RouteSepX (machPieces p) Z g cs ((T : ℕ) : ℤ)) (htim : RouteTimedX g cs T)
    (hlin : RouteLines g cs) (hk : ∀ c ∈ cs, c.k < 8) (hne : cs ≠ []) {j : ℕ}
    (hj : T + j ≤ routeEndX g cs T) : dsepIFar p (routeFootX g cs T j) (reflP g cs) := by
  obtain ⟨c, cs', rfl⟩ := List.exists_cons_of_ne_nil hne
  exact fun h hh hn => isep2_rfoot_far cs' c g T hsep htim hlin hk j hj h hh hn

/-- **A route followed by a flight**, far from every piece outside a list containing the
reflectors of the route. -/
theorem dsepI_flyFoot_far {Z : Set Cell} {g : WL} {cs : List Corner} {T T' : ℕ}
    {L : List Piece} (hsep : RouteSepX (machPieces p) Z g cs ((T : ℕ) : ℤ))
    (htim : RouteTimedX g cs T) (hlin : RouteLines g cs) (hk : ∀ c ∈ cs, c.k < 8)
    (hne : cs ≠ []) (hL : ∀ x ∈ reflP g cs, x ∈ L)
    (hfly : ∀ t : ℕ, routeEndX g cs T < t → t ≤ T' → dsepIFar p ((route g cs).2.box t) L) :
    ∀ t : ℕ, T ≤ t → t ≤ T' → dsepIFar p (flyFoot g cs T t) L := by
  intro t h1 h2
  unfold flyFoot
  split_ifs with h
  · exact (dsepI_route_far hsep htim hlin hk hne (j := t - T) (by omega)).mono subset_rfl hL
  · exact hfly t (by omega) h2

/-! ### The flight of `C` -/

/-- **The flight of `C` in coordinates**: on the port line of DEC copy `m`, right of the left
end of the module. -/
theorem dsepI_flyC_mem (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ≤ t) (h2 : t ≤ decTA p i r - 20)
    {x : Cell} (hx : x ∈ (decGC p i r).box t) :
    U p r - 811 - 248 * D p ≤ x.1 - x.2 ∧
      x.1 - x.2 ≤ U p r + 120 + 29 * ((decM p i r : ℕ) : ℤ) ∧
      -3353 - 99 * ((decM p i r : ℕ) : ℤ) ≤ x.1 + x.2 ∧
      x.1 + x.2 ≤ -3345 - 99 * ((decM p i r : ℕ) : ℤ) := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  have hm := decM_cast p hi
  have hu := modD_uv p r
  have hUe := U_even p r
  obtain ⟨-, hA20, hTA⟩ := decTA_facts p hi
  have hs := sigma_cases (qOf p (callerIdx p r i))
  have h := routeEndX_snoc _ ⟨4, U p r + decChan p (2 * (callerIdx p r i)),
    decPortV p (2 * (callerIdx p r i)), .left r (2 * (callerIdx p r i))⟩ (unitWL p i decRWL) 4260
    (decC_timedX p hi)
  change (routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 : ℤ) = (decGC p i r).tau - _ + _ - _
    at h
  have hcl := fixp_bounds (uL - 62 * (2 * (callerIdx p r i : ℤ)))
    (1 - decPortV p (2 * (callerIdx p r i)) % 2)
  obtain ⟨x1, x2, x3, x4⟩ := hx
  rw [decC_window] at x1 x2 x3 x4 h
  have ht1 : (routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 : ℤ) ≤ t := by exact_mod_cast h1
  have ht2 : (t : ℤ) ≤ decTA p i r - 20 := by omega
  simp only [decWin, modWL, WL.shift, WL.px, WL.py, WL.qt, modDX, modDY, rfOut, rfX, rfCU, rfCV,
    decPortV, decChan, leftChan, uL] at x1 x2 x3 x4 hu h hcl ⊢
  refine ⟨by omega, by omega, by omega, by omega⟩


/-- A DEC copy `m' ≤ m` is a piece of the control thread, with its box. -/
theorem dsepI_own_copy {m' : ℕ} (h : m' ≤ decM p i r) (ph : ℕ) :
    ∃ x ∈ decLC p i r, dsepTB x =
      (⟨.orGate, modDX p r - 1700 - 35 * (m' : ℤ), modDY p r - 1727 - 64 * (m' : ℤ), ph⟩ :
        PSpec).bx := by
  refine ⟨(⟨.orGate, modDX p r - 1700 - 35 * (m' : ℤ), modDY p r - 1727 - 64 * (m' : ℤ),
    (15 + 14 * m') % 30⟩ : PSpec).piece, mem_dd.2 (List.mem_append_right _ ?_), rfl⟩
  exact List.mem_map_of_mem (List.mem_map.2 ⟨m', List.mem_range.2 (by omega), rfl⟩)

/-- **The flight of `C`** from the end of its route to `20` generations before its side input is
far from every piece of the machine outside the control thread. -/
theorem dsepI_flyC_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ≤ t) (h2 : t ≤ decTA p i r - 20) :
    dsepIFar p ((decGC p i r).box t) (decLC p i r) := by
  have hr := lt_numRegs_of_dec hi
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  have hu := modD_uv p r
  have hb := base_boxes
  have hf := layout_facts p
  have hS := fun x (hx : x ∈ (decGC p i r).box t) => dsepI_flyC_mem hi h1 h2 hx
  refine dsepT_far_list hp (decLC_mem hi) (dsepT_mod_far hp (r := r)
    (own := fun B => ∃ x ∈ decLC p i r, dsepTB x = B) ?_ ?_ ?_)
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
    · by_cases hmm : m' ≤ decM p i r
      · exact absurd (dsepI_own_copy hmm ph) hn
      · simp only [PSpec.bx_mk]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        have : (decM p i r : ℤ) + 1 ≤ m' := by omega
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
      by_cases hidx : idx = 2 * (callerIdx p r i : ℤ)
      · -- the port corner of `C`: the final glider has left its window
        have hc0 : (⟨4, U p r + decChan p (2 * (callerIdx p r i)),
            decPortV p (2 * (callerIdx p r i)), .left r (2 * (callerIdx p r i))⟩ : Corner) ∈
            allCorners p :=
          dsepM_corner_mem hi (dsepM_specs hi).2.1 _ (by simp [decCornC, downCorners])
        have e := eq_of_tag (allCorners_tags hp) hc hc0 (by rw [ht, hidx])
        subst e
        exact dsepM_final_far (bandCorners p (instrBand i) 1 (A p i + decR)
          (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
          (U p r + decChan p (2 * (callerIdx p r i))) 3 2) _ _ 4260 (by norm_num)
          (decC_timedX p hi) h1
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

/-! ### The module-local parts of the control -/

/-- The pieces of the control thread and of the circuit. -/
theorem dsepI_LCG_mem (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLC p i r ++ modGroup p r, x ∈ machPieces p := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact decLC_mem hi x hx
  · exact modGroup_mem (lt_numRegs_of_dec hi) x hx

/-- A DEC copy `m' ≤ m` (integer index) is a piece of a list containing the control thread. -/
theorem dsepI_own_copyZ {L : List Piece} (hL : ∀ x ∈ decLC p i r, x ∈ L) {m' : ℤ}
    (h0 : 0 ≤ m') (h : m' ≤ decM p i r) :
    ∃ x ∈ L, dsepTB x =
      (dsepTBase .orGate).mv (modDX p r - 1700 - 35 * m') (modDY p r - 1727 - 64 * m') := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨x, hx, e⟩ := dsepI_own_copy (p := p) (i := i) (r := r) (m' := n) (by omega) 0
  exact ⟨x, hL x hx, e⟩

/-- A set of the module frame inside the zone and far from the module classes is far from every
piece outside the control thread and the circuit: the module frame form of `dsepT_zone_far` for
the list `decLC ++ modGroup`, where the groups and the copies `≤ m` are excluded. -/
theorem dsepI_ctrl_local (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {S : Set Cell}
    (hZ : S ⊆ dsepTZone p)
    (hJ : FarApart 2 S ((dsepTBase (.rf 4)).mv (-850) (-1044)).set)
    (hI : FarApart 2 S ((dsepTBase .orGate).mv (-1132) (-1291)).set)
    (hDm : ∀ m : ℤ, decM p i r < m → m < 2 * D p →
      FarApart 2 S ((dsepTBase .orGate).mv (-1700 - 35 * m) (-1727 - 64 * m)).set)
    (hN : ∀ j : ℤ, 0 ≤ j → j < D p → ∀ i' < 3,
      FarApart 2 S ((dsepTBase (.stNZ i')).mv (72 * j) (72 * j)).set)
    (hZs : ∀ j : ℤ, 0 ≤ j → j < D p → ∀ i' < 3,
      FarApart 2 S ((dsepTBase (.stZ i')).mv (72 * j) (-72 * j)).set)
    (hEN : FarApart 2 S ((dsepTBase .eatNZ).mv (72 * (D p - 1)) (72 * (D p - 1))).set)
    (hEZ : FarApart 2 S ((dsepTBase .eatZ).mv (72 * (D p - 1)) (-72 * (D p - 1))).set) :
    dsepIFar p (modImg p r S) (decLC p i r ++ modGroup p r) := by
  refine dsepT_zone_far hp hZ (dsepI_LCG_mem hi) (dsepT_mod_cls
    (own := fun B => ∃ x ∈ decLC p i r ++ modGroup p r, dsepTB x = B) ?_ (fun _ => hJ)
    (fun _ => hI) ?_ (fun j h0 h1 i' hi' _ => hN j h0 h1 i' hi')
    (fun j h0 h1 i' hi' _ => hZs j h0 h1 i' hi') (fun _ => hEN) (fun _ => hEZ))
  · intro i' hi' hn
    exact absurd (dsepT_grp_own r i' hi' fun x hx => List.mem_append_right _ hx) hn
  · intro m h0 h1 hn
    by_cases hm : m ≤ decM p i r
    · exact absurd (dsepI_own_copyZ (fun x hx => List.mem_append_left _ hx) h0 hm) hn
    · exact hDm m (by omega) h1

/-- The joint approach box of `C` and DEC copy `m`, in the module frame. -/
theorem dsepI_side_eq (p : Program) (i r : ℕ) :
    decSideBoxC p i r = modImg p r ((fun c => ((-1700 - 35 * ((decM p i r : ℕ) : ℤ),
      -1727 - 64 * ((decM p i r : ℕ) : ℤ)) : Cell) + c) '' sideWBox) := by
  unfold decSideBoxC modImg
  rw [Set.image_image]
  congr 1
  ext c <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- **The joint approach of `C` and DEC copy `m`** is far from every piece of the machine outside
the control thread and the circuit. -/
theorem dsepI_sideC_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    dsepIFar p (decSideBoxC p i r) (decLC p i r ++ modGroup p r) := by
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  have hb := base_boxes
  have hD := one_le_D p
  have hmem : ∀ x ∈ (fun c => ((-1700 - 35 * ((decM p i r : ℕ) : ℤ),
      -1727 - 64 * ((decM p i r : ℕ) : ℤ)) : Cell) + c) '' sideWBox,
      -1700 - 35 * ((decM p i r : ℕ) : ℤ) ≤ x.1 ∧ x.1 ≤ -1610 - 35 * ((decM p i r : ℕ) : ℤ) ∧
      -1727 - 64 * ((decM p i r : ℕ) : ℤ) ≤ x.2 ∧ x.2 ≤ -1687 - 64 * ((decM p i r : ℕ) : ℤ) := by
    rintro _ ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  rw [dsepI_side_eq]
  refine dsepI_ctrl_local hp hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have := hmem x hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  all_goals first
    | (refine isep2_far_box fun x hx => ?_
       have := hmem x hx
       simp only [dsepTBase, BoxT.mv] at *
       omega)
    | (intro m h1 h2
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       have := hmem x hx
       omega)
    | (intro j h0 h1 i' hi'
       have := stNZ_cases i' hi'
       have := stZ_cases i' hi'
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       have := hmem x hx
       omega)

/-- The DEC chain footprint, in the module frame. -/
theorem dsepI_chain_eq (p : Program) (i r : ℕ) :
    decChainFoot p i r = modImg p r ((fun c => ((-1700 - 35 * ((decM p i r : ℕ) : ℤ),
      -1727 - 64 * ((decM p i r : ℕ) : ℤ)) : Cell) + c) ''
        chainFoot (Box 0 90 (-6) 60) chainV (decM p i r + 1)) := by
  unfold decChainFoot modImg
  rw [Set.image_image]
  congr 1
  ext c <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- **The DEC chain** is far from every piece of the machine outside the control thread and the
circuit. -/
theorem dsepI_chainC_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    dsepIFar p (decChainFoot p i r) (decLC p i r ++ modGroup p r) := by
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  have hb := base_boxes
  have hD := one_le_D p
  have hmem : ∀ x ∈ (fun c => ((-1700 - 35 * ((decM p i r : ℕ) : ℤ),
      -1727 - 64 * ((decM p i r : ℕ) : ℤ)) : Cell) + c) ''
        chainFoot (Box 0 90 (-6) 60) chainV (decM p i r + 1),
      ∃ k : ℤ, 0 ≤ k ∧ k ≤ ((decM p i r : ℕ) : ℤ) ∧
      -1700 - 35 * ((decM p i r : ℕ) : ℤ) + 35 * k ≤ x.1 ∧
      x.1 ≤ -1610 - 35 * ((decM p i r : ℕ) : ℤ) + 35 * k ∧
      -1733 - 64 * ((decM p i r : ℕ) : ℤ) + 64 * k ≤ x.2 ∧
      x.2 ≤ -1667 - 64 * ((decM p i r : ℕ) : ℤ) + 64 * k := by
    rintro _ ⟨d, ⟨k, hk, d1, d2, d3, d4⟩, rfl⟩
    refine ⟨k, by omega, by omega, ?_⟩
    simp only [Prod.fst_add, Prod.snd_add] at d1 d2 d3 d4 ⊢
    omega
  rw [dsepI_chain_eq]
  refine dsepI_ctrl_local hp hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  all_goals first
    | (refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       simp only [dsepTBase, BoxT.mv] at *
       omega)
    | (intro m h1 h2
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)
    | (intro j h0 h1 i' hi'
       have := stNZ_cases i' hi'
       have := stZ_cases i' hi'
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)

/-- The flight of `C'`, in the module frame. -/
theorem dsepI_cp_eq (p : Program) (i r t : ℕ) :
    decCpFoot p i r t = modImg p r (cp0WL.box (-2071 + ((t - decTB p i r : ℕ) : ℤ))) := rfl

/-- **The flight of `C'` to the register run** is far from every piece of the machine outside the
control thread and the circuit. -/
theorem dsepI_cpC_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h2 : t ≤ decTS p i r) :
    dsepIFar p (decCpFoot p i r t) (decLC p i r ++ modGroup p r) := by
  have hm := decM_cast p hi
  have hj := dsepM_j_lt hi
  have hb := base_boxes
  have hD := one_le_D p
  have e : decTS p i r = decTB p i r + 1771 := rfl
  have hs : ((t - decTB p i r : ℕ) : ℤ) ≤ 1771 := by omega
  have hmem : ∀ x ∈ cp0WL.box (-2071 + ((t - decTB p i r : ℕ) : ℤ)),
      ∃ k : ℤ, 0 ≤ k ∧ k ≤ 0 ∧ 37 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ 45 ∧ -3303 ≤ x.1 + x.2 ∧
        x.1 + x.2 ≤ -2000 := by
    rintro x ⟨x1, x2, x3, x4⟩
    refine ⟨0, le_rfl, le_rfl, ?_⟩
    simp only [cp0WL, WL.px, WL.py, WL.qt] at x1 x2 x3 x4
    omega
  rw [dsepI_cp_eq]
  refine dsepI_ctrl_local hp hi ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  all_goals first
    | (refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       simp only [dsepTBase, BoxT.mv] at *
       omega)
    | (intro m h1 h2
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)
    | (intro j h0 h1 i' hi'
       have := stNZ_cases i' hi'
       have := stZ_cases i' hi'
       rw [dsepI_mv_set]
       refine isep2_far_box fun x hx => ?_
       obtain ⟨k, hk0, hk1, x1, x2, x3, x4⟩ := hmem x hx
       omega)

/-- **The moving footprint of the control** is far from every piece of the machine outside the
control thread and the circuit. -/
theorem dsepI_footC_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (h2 : t ≤ decTS p i r) :
    dsepIFar p (decFootC p i r t) (decLC p i r ++ modGroup p r) := by
  unfold decFootC
  split_ifs with h3 h4 h5
  · refine dsepI_flyFoot_far (dsep_sepC hp hi) (decC_timedX p hi) (decC_lines p i r).1
      downCorners_k (by simp [decCornC, downCorners, bandCorners])
      (fun x hx => List.mem_append_left _ (mem_dd.2 (List.mem_append_left _ hx)))
      (fun t' h1 h2 => (dsepI_flyC_far hp hi (by omega) h2).mono subset_rfl
        fun x hx => List.mem_append_left _ hx) t h0 h3
  · exact dsepI_sideC_far hp hi
  · exact dsepI_chainC_far hp hi
  · exact dsepI_cpC_far hp hi h2
end LP

end LeanTheory.Life
