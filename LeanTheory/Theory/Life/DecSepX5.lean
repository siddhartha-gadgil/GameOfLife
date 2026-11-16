/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepX4

/-!
# The pieces of the two threads of a `decJz` activation

Research note `N-22`. For the fields `nThr`, `zThr` and `zGate` of `DecSep`, the pieces of the
main thread and of the thread of the unpaired token, by kind (reflectors of corners, pieces of
module `r`, copies of an entry chain):

* `dsepX_tags_N`, `dsepX_tags_Z`: the corners of the main thread and of the unpaired token are at
  distinct places (distinct tags);
* `dsepX_LMN_LZu`, `dsepX_LMZ_LNu`: every piece of the main thread is far from every piece of the
  thread of the unpaired token; `dsepX_gate_LMZ`, `dsepX_gate_LNu`: the INC gate is far from
  both;
* the classes of the boxes of the pieces in coordinates (`dsepX_LMN_cls`, `dsepX_LZu_cls`,
  `dsepX_LMZ_cls`, `dsepX_LNu_cls`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### The corners of the routes -/

/-- The box of the reflector of a corner. -/
def dsepXCB (c : Corner) : Set Cell :=
  Box (cornerSpec c).bx.a (cornerSpec c).bx.b (cornerSpec c).bx.lo (cornerSpec c).bx.hi

/-- The corners of `C`, listed. -/
theorem dsepX_cornC_eq (p : Program) (i r : ℕ) :
    decCornC p i r = [⟨3, A p i + decR, trackOut p (instrBand i) 1 (A p i + decR),
        .band (instrBand i) 1 false⟩,
      ⟨7, hairC p (qOf p (callerIdx p r i)) (A p i + decR),
        trackOut p (instrBand i) 1 (A p i + decR), .band (instrBand i) 1 true⟩,
      ⟨4, hairC p (qOf p (callerIdx p r i)) (A p i + decR),
        trackBack p (instrBand i) 1 (A p i + decR), .band (instrBand i) 8 true⟩,
      ⟨2, U p r + decChan p (2 * (callerIdx p r i)), trackBack p (instrBand i) 1 (A p i + decR),
        .band (instrBand i) 8 false⟩,
      ⟨4, U p r + decChan p (2 * (callerIdx p r i)), decPortV p (2 * (callerIdx p r i)),
        .left r (2 * (callerIdx p r i))⟩] := rfl

/-- The corners of `KNZ`, listed. -/
theorem dsepX_cornN_eq (p : Program) (i r : ℕ) :
    decCornN p i r = [⟨3, A p i + decL, trackOut p (instrBand i) 0 (A p i + decL),
        .band (instrBand i) 0 false⟩,
      ⟨7, hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL),
        trackOut p (instrBand i) 0 (A p i + decL), .band (instrBand i) 0 true⟩,
      ⟨4, hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL),
        trackBack p (instrBand i) 0 (A p i + decL), .band (instrBand i) 9 true⟩,
      ⟨2, U p r + nzTokChan p (callerIdx p r i), trackBack p (instrBand i) 0 (A p i + decL),
        .band (instrBand i) 9 false⟩,
      ⟨4, U p r + nzTokChan p (callerIdx p r i), nzTokPortV (callerIdx p r i),
        .left r (2 * D p + 1 + 2 * (callerIdx p r i))⟩] := rfl

/-- The corners of `KZ`, listed. -/
theorem dsepX_cornZ_eq (p : Program) (i r : ℕ) :
    decCornZ p i r = [⟨3, A p i + decD, trackOut p (instrBand i) 2 (A p i + decD),
        .band (instrBand i) 2 false⟩,
      ⟨7, hairKZ p (qOf p (callerIdx p r i)) (A p i + decD),
        trackOut p (instrBand i) 2 (A p i + decD), .band (instrBand i) 2 true⟩,
      ⟨4, hairKZ p (qOf p (callerIdx p r i)) (A p i + decD),
        trackBack p (instrBand i) 2 (A p i + decD), .band (instrBand i) 7 true⟩,
      ⟨2, U p r + zTokChan p (callerIdx p r i), trackBack p (instrBand i) 2 (A p i + decD),
        .band (instrBand i) 7 false⟩,
      ⟨3, U p r + zTokChan p (callerIdx p r i), zTokDepth p (callerIdx p r i),
        .right r (callerIdx p r i) 2⟩,
      ⟨0, U p r + zTokStation (callerIdx p r i), zTokDepth p (callerIdx p r i),
        .right r (callerIdx p r i) 3⟩] := rfl

/-- **The corners of the NZ main thread and of `KZ` have distinct tags.** -/
theorem dsepX_tags_N (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ c ∈ decCornC p i r ++ decCornN p i r ++ decCsN p i r, ∀ c' ∈ decCornZ p i r,
      c.tag ≠ c'.tag := by
  intro c hc c' hc'
  rw [dsepX_cornC_eq, dsepX_cornN_eq, dsep_csN_eq hp hi] at hc
  rw [dsepX_cornZ_eq] at hc'
  simp only [bandCorners, isep2SlabC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc hc'
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, CTag.band.injEq, reduceCtorEq, not_false_eq_true, not_and] <;> omega

/-- **The corners of the Z main thread and of `KNZ` have distinct tags.** -/
theorem dsepX_tags_Z (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ c ∈ decCornC p i r ++ decCornZ p i r ++ decCsZ p i r z, ∀ c' ∈ decCornN p i r,
      c.tag ≠ c'.tag := by
  intro c hc c' hc'
  rw [dsepX_cornC_eq, dsepX_cornZ_eq, dsep_csZ_eq hp hi] at hc
  rw [dsepX_cornN_eq] at hc'
  simp only [bandCorners, isep2SlabC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc hc'
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, CTag.band.injEq, CTag.left.injEq, reduceCtorEq, not_false_eq_true,
      not_and] <;> omega

/-! ### Far apart by kind -/

/-- Two corners of the machine with distinct tags have far reflector boxes. -/
theorem dsepX_cc (hp : p.WellFormed) {c c' : Corner} (hc : c ∈ allCorners p)
    (hc' : c' ∈ allCorners p) (ht : c.tag ≠ c'.tag) : FarApart 2 (dsepXCB c) (dsepXCB c') := by
  have := corner_gap61 p (allCorners_valid hp c hc) (allCorners_valid hp c' hc') ht
  exact (corner_far (by omega)).farApart

/-- A corner of the machine is far from a piece of a module. -/
theorem dsepX_cm (hp : p.WellFormed) {c : Corner} (hc : c ∈ allCorners p) {s : PSpec}
    (hs : s ∈ moduleSpecs p r) : FarApart 2 (dsepXCB c) s.piece.box :=
  corner_module_sep p (allCorners_valid hp c hc) hs

/-- A corner of the machine is far from a piece of a unit. -/
theorem dsepX_cu (hp : p.WellFormed) {c : Corner} (hc : c ∈ allCorners p) {a : ℕ} {s : PSpec}
    (hs : s ∈ unitSpecs p a) : FarApart 2 (dsepXCB c) s.piece.box :=
  corner_unit_sep p (allCorners_valid hp c hc) hs

/-- A piece of a module is far from a piece of a unit. -/
theorem dsepX_mu {s s' : PSpec} (hs : s ∈ moduleSpecs p r) {a : ℕ} (hs' : s' ∈ unitSpecs p a)
    (ha : (a : ℤ) ≤ N p + R p - 1) : FarApart 2 s.piece.box s'.piece.box := by
  have hu := (moduleSpecs_uv p r hs).1
  have hu' := unitSpecs_uv p a hs'
  have hgap := unit_module_gap p (a := a) (r := r) ⟨by omega, ha⟩ (by omega)
  have hRs := slabR_ge_rs p
  have hk : -180 ≤ (unitKind p a).uLo := by cases unitKind p a <;> simp [UKind.uLo]
  have hD := one_le_D p
  rw [PSpec.piece_box, PSpec.piece_box]
  refine isep2_far_box fun x ⟨x1, x2, x3, x4⟩ => ?_
  unfold BoxT.InUV at hu hu'
  unfold modLeft at hgap
  omega

/-- A piece whose box is far from a piece of the machine is not that piece. -/
theorem dsepX_ne_of_far {g h : Piece} (hg : g ∈ machPieces p) (hf : FarApart 2 g.box h.box) :
    g ≠ h := by
  rintro rfl
  have hn := dsepT_mach_ne hg
  exact hf (g.a, g.lo) ⟨le_rfl, hn.1, le_rfl, hn.2⟩ (g.a, g.lo) ⟨le_rfl, hn.1, le_rfl, hn.2⟩
    ⟨by simp, by simp, by simp, by simp⟩

/-! ### The pieces of the lists, by kind -/

/-- The pieces of the control thread: reflectors of `C` or DEC copies (`v ≤ -3305`). -/
theorem dsepX_kind_LC (hi : p[i]? = some (.decJz r z)) {g : Piece} (hg : g ∈ decLC p i r) :
    (∃ c ∈ decCornC p i r, g.box = dsepXCB c) ∨
      ∃ s ∈ moduleSpecs p r, g = s.piece ∧ ∀ x ∈ g.box, x.1 + x.2 ≤ -3305 := by
  rcases List.mem_append.1 (mem_dd.1 hg) with h | h
  · exact Or.inl (dsepM_reflP_mem h)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (decChainP_sub hi h)
    refine Or.inr ⟨s, ?_, rfl, ?_⟩
    · unfold moduleSpecs
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ hs)))
    · obtain ⟨m, -, rfl⟩ := mem_decChainSpecs hs
      have hu := modD_uv p r
      rw [dsepM_copy_box]
      rintro x ⟨x1, x2, x3, x4⟩
      omega

/-- The groups of the circuit: pieces of the module in the hull of the circuit. -/
theorem dsepX_kind_grp {g : Piece} (hg : g ∈ modGroup p r) :
    ∃ s ∈ moduleSpecs p r, g = s.piece ∧ ∀ x ∈ g.box, x.1 - x.2 ≤ U p r + 798 ∧
      -2324 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 670 := by
  have hc := dsepT_grp_cells hg
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  refine ⟨s, ?_, rfl, fun x hx => ?_⟩
  · unfold moduleSpecs
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ hs))))
  · have := hc x hx
    simp only [dsepTGrpHull] at this
    omega

/-- The NZ stations `0 … j - 1`: pieces of the module at `u ≤ U_r - 353`, `v ≥ 1200`. -/
theorem dsepX_kind_LSN (hi : p[i]? = some (.decJz r z)) {g : Piece} (hg : g ∈ decLSN p i r) :
    ∃ s ∈ moduleSpecs p r, g = s.piece ∧ ∀ x ∈ g.box, x.1 - x.2 ≤ U p r - 353 ∧
      1200 ≤ x.1 + x.2 := by
  have hj := callerIdx_lt_D p hi
  have hu := modD_uv p r
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hg)
  refine ⟨s, ?_, rfl, ?_⟩
  · unfold moduleSpecs
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    simp only [stationSpecs, List.mem_flatMap, List.mem_range] at hs ⊢
    obtain ⟨k, hk, hs⟩ := hs
    exact ⟨k, by omega, hs⟩
  · obtain ⟨j', -, i', hi', rfl⟩ := mem_stationSpecs hs
    have := stNZ_cases i' hi'
    rw [isep2_spec_box]
    rintro x ⟨x1, x2, x3, x4⟩
    omega

/-- The Z stations `0 … j - 1`: pieces of the module at `u ≥ U_r + 1173`, `v ∈ [500, 686]`. -/
theorem dsepX_kind_LSZ (hi : p[i]? = some (.decJz r z)) {g : Piece} (hg : g ∈ decLSZ p i r) :
    ∃ s ∈ moduleSpecs p r, g = s.piece ∧ ∀ x ∈ g.box, U p r + 1173 ≤ x.1 - x.2 ∧
      500 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 686 := by
  have hj := callerIdx_lt_D p hi
  have hu := modD_uv p r
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hg)
  refine ⟨s, ?_, rfl, ?_⟩
  · unfold moduleSpecs
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    simp only [stationZSpecs, List.mem_flatMap, List.mem_range] at hs ⊢
    obtain ⟨k, hk, hs⟩ := hs
    exact ⟨k, by omega, hs⟩
  · obtain ⟨j', -, i', hi', rfl⟩ := mem_stationZSpecs hs
    have := stZ_cases i' hi'
    rw [isep2_spec_box]
    rintro x ⟨x1, x2, x3, x4⟩
    omega

/-- Station `j` of the line NZ: pieces of the module at `u ≤ U_r - 353`, `v ≥ 1200`. -/
theorem dsepX_kind_stNZ (hi : p[i]? = some (.decJz r z)) {g : Piece}
    (hg : g ∈ stNZOne p r (callerIdx p r i)) :
    ∃ s ∈ moduleSpecs p r, g = s.piece ∧ ∀ x ∈ g.box, x.1 - x.2 ≤ U p r - 353 ∧
      1200 ≤ x.1 + x.2 := by
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (stNZOne_mem p r (callerIdx_lt_D p hi) hg)
  obtain ⟨i', hi', hb⟩ := dsepM_mem_stNZOne hg
  refine ⟨s, hs, rfl, ?_⟩
  rw [hb]
  have := stNZ_cases i' hi'
  rintro x ⟨x1, x2, x3, x4⟩
  omega

/-- Station `j` of the line Z: pieces of the module at `u ≥ U_r + 1173`, `v ∈ [500, 686]`. -/
theorem dsepX_kind_stZ (hi : p[i]? = some (.decJz r z)) {g : Piece}
    (hg : g ∈ stZOne p r (callerIdx p r i)) :
    ∃ s ∈ moduleSpecs p r, g = s.piece ∧ ∀ x ∈ g.box, U p r + 1173 ≤ x.1 - x.2 ∧
      500 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 686 := by
  have hu := modD_uv p r
  have hj := dsepM_j_lt hi
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (stZOne_mem p r (callerIdx_lt_D p hi) hg)
  obtain ⟨i', hi', hb⟩ := dsepM_mem_stZOne hg
  refine ⟨s, hs, rfl, ?_⟩
  rw [hb]
  have := stZ_cases i' hi'
  have : (0 : ℤ) ≤ (callerIdx p r i : ℤ) := by omega
  rintro x ⟨x1, x2, x3, x4⟩
  omega

/-- The copies `0 … t` of the entry chain of a unit are pieces of the unit. -/
theorem dsepX_kind_chain {a t : ℕ} (ht : (t : ℤ) < 2 * P p) {g : Piece}
    (hg : g ∈ chainPieces p a t) : ∃ s ∈ unitSpecs p a, g = s.piece := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  refine ⟨s, List.mem_append_left _ ?_, rfl⟩
  obtain ⟨t', ht', rfl⟩ := mem_chainSpecs hs
  unfold P at ht
  exact List.mem_map.2 ⟨t', List.mem_range.2 (by omega), rfl⟩

/-! ### Far apart by shape -/

/-- The shape of a piece: the reflector of a corner of `cs`, a piece of module `r` whose box
satisfies `P`, or a piece of unit `a`. -/
def dsepXShape (p : Program) (r : ℕ) (cs : List Corner) (a : ℕ) (P : Cell → Prop)
    (g : Piece) : Prop :=
  (∃ c ∈ cs, g.box = dsepXCB c) ∨ (∃ s ∈ moduleSpecs p r, g = s.piece ∧ ∀ x ∈ g.box, P x) ∨
    ∃ s ∈ unitSpecs p a, g = s.piece

/-- The shape of a piece without the units. -/
def dsepXShape2 (p : Program) (r : ℕ) (cs : List Corner) (P : Cell → Prop) (g : Piece) :
    Prop :=
  (∃ c ∈ cs, g.box = dsepXCB c) ∨ ∃ s ∈ moduleSpecs p r, g = s.piece ∧ ∀ x ∈ g.box, P x

/-- **Two pieces of given shapes are far apart**: corners of distinct tags, module pieces in
separated regions; corners, module pieces and unit pieces are always far apart. -/
theorem dsepX_shape_far (hp : p.WellFormed) {cs cs' : List Corner} {a : ℕ} {P P' : Cell → Prop}
    (hcs : ∀ c ∈ cs, c ∈ allCorners p) (hcs' : ∀ c ∈ cs', c ∈ allCorners p)
    (ht : ∀ c ∈ cs, ∀ c' ∈ cs', c.tag ≠ c'.tag)
    (hPP : ∀ x y : Cell, P x → P' y → x.1 - x.2 + 5 ≤ y.1 - y.2 ∨ y.1 - y.2 + 5 ≤ x.1 - x.2 ∨
      x.1 + x.2 + 5 ≤ y.1 + y.2 ∨ y.1 + y.2 + 5 ≤ x.1 + x.2)
    (ha : (a : ℤ) ≤ N p + R p - 1) {g h : Piece} (hg : dsepXShape p r cs a P g)
    (hh : dsepXShape2 p r cs' P' h) : FarApart 2 g.box h.box := by
  rcases hh with ⟨c', hc', hb'⟩ | ⟨s', hs', rfl, hP'⟩ <;>
    rcases hg with ⟨c, hc, hb⟩ | ⟨s, hs, rfl, hP⟩ | ⟨s, hs, rfl⟩
  · rw [hb, hb']; exact dsepX_cc hp (hcs c hc) (hcs' c' hc') (ht c hc c' hc')
  · rw [hb']; exact (dsepX_cm hp (hcs' c' hc') hs).symm'
  · rw [hb']; exact (dsepX_cu hp (hcs' c' hc') hs).symm'
  · rw [hb]; exact dsepX_cm hp (hcs c hc) hs'
  · exact dsepT_far_cells fun x hx y hy => hPP x y (hP x hx) (hP' y hy)
  · exact (dsepX_mu hs' hs ha).symm'

/-- The corners of the main thread of an NZ activation are corners of the machine. -/
theorem dsepX_cornNZ_mem (hi : p[i]? = some (.decJz r z)) :
    ∀ c ∈ decCornC p i r ++ decCornN p i r ++ decCsN p i r, c ∈ allCorners p := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · exact dsepM_corner_mem hi (dsepM_specs hi).2.1 c hc
    · exact dsepM_corner_mem hi (dsepM_specs hi).1 c hc
  · exact dsepM_corner_mem hi (dsepM_specs hi).2.2.2.1 c hc

/-- The corners of the main thread of a Z activation are corners of the machine. -/
theorem dsepX_cornZ_mem (hi : p[i]? = some (.decJz r z)) :
    ∀ c ∈ decCornC p i r ++ decCornZ p i r ++ decCsZ p i r z, c ∈ allCorners p := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · exact dsepM_corner_mem hi (dsepM_specs hi).2.1 c hc
    · exact dsepM_corner_mem hi (dsepM_specs hi).2.2.1 c hc
  · exact dsepM_corner_mem hi (dsepM_specs hi).2.2.2.2 c hc

/-- **The shape of the pieces of the main thread of an NZ activation.** -/
theorem dsepX_LMN_shape (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g : Piece}
    (hg : g ∈ decLMN p i r) :
    dsepXShape p r (decCornC p i r ++ decCornN p i r ++ decCsN p i r) (i + 1)
      (fun x => x.1 - x.2 ≤ U p r + 798 ∨ x.1 + x.2 ≤ -3305) g := by
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  simp only [decLMN, List.mem_append] at hg
  rcases hg with (((hg | hg) | hg) | hg) | hg
  · rcases dsepX_kind_LC hi hg with ⟨c, hc, hb⟩ | ⟨s, hs, e, hP⟩
    · exact Or.inl ⟨c, by simp [hc], hb⟩
    · exact Or.inr (Or.inl ⟨s, hs, e, fun x hx => Or.inr (hP x hx)⟩)
  · obtain ⟨s, hs, e, hP⟩ := dsepX_kind_grp hg
    exact Or.inr (Or.inl ⟨s, hs, e, fun x hx => Or.inl (hP x hx).1⟩)
  · obtain ⟨s, hs, e, hP⟩ := dsepX_kind_LSN hi hg
    exact Or.inr (Or.inl ⟨s, hs, e, fun x hx => Or.inl (by have := hP x hx; omega)⟩)
  · rcases List.mem_append.1 (mem_dd.1 hg) with h | h
    · obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem h
      exact Or.inl ⟨c, by simp [hc], hb⟩
    · obtain ⟨s, hs, e, hP⟩ := dsepX_kind_stNZ hi h
      exact Or.inr (Or.inl ⟨s, hs, e, fun x hx => Or.inl (by have := hP x hx; omega)⟩)
  · rcases List.mem_append.1 (mem_dd.1 hg) with h | h
    · obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem h
      exact Or.inl ⟨c, by simp [hc], hb⟩
    · exact Or.inr (Or.inr (dsepX_kind_chain (by rw [htN]; exact ht.2) h))

/-- **The shape of the pieces of the thread of `KZ`.** -/
theorem dsepX_LZu_shape (hi : p[i]? = some (.decJz r z)) {h : Piece} (hh : h ∈ decLZu p i r) :
    dsepXShape2 p r (decCornZ p i r) (fun x => U p r + 1173 ≤ x.1 - x.2 ∧ 500 ≤ x.1 + x.2 ∧
      x.1 + x.2 ≤ 686) h := by
  rcases List.mem_append.1 (mem_dd.1 hh) with h1 | h1
  · exact Or.inl (dsepM_reflP_mem h1)
  · exact Or.inr (dsepX_kind_stZ hi h1)

/-- **The shape of the pieces of the main thread of a Z activation** (the groups of the circuit
apart). -/
theorem dsepX_LMZ_shape (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g : Piece}
    (hg : g ∈ decLMZ p i r z) : g ∈ modGroup p r ∨
      dsepXShape p r (decCornC p i r ++ decCornZ p i r ++ decCsZ p i r z) z
        (fun x => x.1 + x.2 ≤ -3305 ∨ (500 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 686)) g := by
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  simp only [decLMZ, List.mem_append] at hg
  rcases hg with (((hg | hg) | hg) | hg) | hg
  · rcases dsepX_kind_LC hi hg with ⟨c, hc, hb⟩ | ⟨s, hs, e, hP⟩
    · exact Or.inr (Or.inl ⟨c, by simp [hc], hb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, hs, e, fun x hx => Or.inl (hP x hx)⟩))
  · exact Or.inl hg
  · obtain ⟨s, hs, e, hP⟩ := dsepX_kind_LSZ hi hg
    exact Or.inr (Or.inr (Or.inl ⟨s, hs, e, fun x hx => Or.inr (hP x hx).2⟩))
  · rcases List.mem_append.1 (mem_dd.1 hg) with h | h
    · obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem h
      exact Or.inr (Or.inl ⟨c, by simp [hc], hb⟩)
    · obtain ⟨s, hs, e, hP⟩ := dsepX_kind_stZ hi h
      exact Or.inr (Or.inr (Or.inl ⟨s, hs, e, fun x hx => Or.inr (hP x hx).2⟩))
  · rcases List.mem_append.1 (mem_dd.1 hg) with h | h
    · obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem h
      exact Or.inr (Or.inl ⟨c, by simp [hc], hb⟩)
    · exact Or.inr (Or.inr (Or.inr (dsepX_kind_chain (by rw [htN]; exact ht.2) h)))

/-- **The shape of the pieces of the thread of `KNZ`.** -/
theorem dsepX_LNu_shape (hi : p[i]? = some (.decJz r z)) {h : Piece} (hh : h ∈ decLNu p i r) :
    dsepXShape2 p r (decCornN p i r) (fun x => x.1 - x.2 ≤ U p r - 353 ∧ 1200 ≤ x.1 + x.2) h := by
  rcases List.mem_append.1 (mem_dd.1 hh) with h1 | h1
  · exact Or.inl (dsepM_reflP_mem h1)
  · exact Or.inr (dsepX_kind_stNZ hi h1)

/-! ### The pieces of the two threads are far apart -/

/-- **Every piece of the main thread of an NZ activation is far from every piece of the thread of
the unpaired `KZ`.** -/
theorem dsepX_LMN_LZu (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLMN p i r, ∀ h ∈ decLZu p i r, FarApart 2 g.box h.box := by
  intro g hg h hh
  have h1 := succ_lt_of_dec hp hi
  have hR := one_le_R p
  exact dsepX_shape_far hp (dsepX_cornNZ_mem hi)
    (fun c hc => dsepM_corner_mem hi (dsepM_specs hi).2.2.1 c hc) (dsepX_tags_N hp hi)
    (fun x y hx hy => by omega) (a := i + 1) (by unfold N; push_cast; omega)
    (dsepX_LMN_shape hp hi hg) (dsepX_LZu_shape hi hh)

/-- **Every piece of the main thread of a Z activation is far from every piece of the thread of
the unpaired `KNZ`.** -/
theorem dsepX_LMZ_LNu (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLMZ p i r z, ∀ h ∈ decLNu p i r, FarApart 2 g.box h.box := by
  intro g hg h hh
  have hz := lt_of_dec hp hi
  have hR := one_le_R p
  have hcN := fun c hc => dsepM_corner_mem hi (dsepM_specs hi).1 c hc
  rcases dsepX_LMZ_shape hp hi hg with hgr | hs
  · obtain ⟨s, hs, e, hP⟩ := dsepX_kind_grp hgr
    exact dsepX_shape_far hp (cs := []) (by simp) hcN (by simp)
      (P := fun x => x.1 + x.2 ≤ 670) (fun x y hx hy => by omega) (a := z)
      (by unfold N; omega) (Or.inr (Or.inl ⟨s, hs, e, fun x hx => (hP x hx).2.2⟩))
      (dsepX_LNu_shape hi hh)
  · exact dsepX_shape_far hp (dsepX_cornZ_mem hi) hcN (dsepX_tags_Z hp hi)
      (fun x y hx hy => by omega) (by unfold N; omega) hs (dsepX_LNu_shape hi hh)

/-- The INC gate is a piece of module `r`, in coordinates. -/
theorem dsepX_gate_shape (p : Program) (r : ℕ) :
    dsepXShape2 p r [] (fun x => U p r + 127 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + 249 ∧
      -2423 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ -2301) (gateP p r) := by
  have hu := modD_uv p r
  refine Or.inr ⟨incGateSpec p r, mem_moduleSpecs_head (List.mem_append_right _
    (List.mem_cons_of_mem _ List.mem_cons_self)), rfl, ?_⟩
  rw [isep2_gateP_box]
  rintro x ⟨x1, x2, x3, x4⟩
  omega

/-- **The INC gate is far from every piece of the main thread of a Z activation and of the thread
of the unpaired `KNZ`.** -/
theorem dsepX_gate_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLMZ p i r z ++ decLNu p i r, FarApart 2 g.box (gateP p r).box := by
  intro g hg
  have hz := lt_of_dec hp hi
  have hR := one_le_R p
  have hr := lt_numRegs_of_dec hi
  rcases List.mem_append.1 hg with hg | hg
  · rcases dsepX_LMZ_shape hp hi hg with hgr | hs
    · have hc := dsepT_grp_cells hgr
      have hu := modD_uv p r
      refine dsepT_sep_of_ne hp (modGroup_mem hr g hgr) (decModule_mem hr (mem_moduleSpecs_head
        (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))) ?_
      rintro rfl
      have := hc (modDX p r - 1132, modDY p r - 1291) (by
        rw [isep2_gateP_box]; exact ⟨le_rfl, by omega, le_rfl, by omega⟩)
      simp only [dsepTGrpHull] at this
      omega
    · exact dsepX_shape_far hp (dsepX_cornZ_mem hi) (cs' := []) (by simp) (by simp)
        (fun x y hx hy => by omega) (by unfold N; omega) hs (dsepX_gate_shape p r)
  · rcases dsepX_LNu_shape hi hg with ⟨c, hc, hb⟩ | ⟨s, hs, e, hP⟩
    · exact dsepX_shape_far hp (fun c hc => dsepM_corner_mem hi (dsepM_specs hi).1 c hc)
        (cs' := []) (by simp) (by simp) (P := fun _ => False) (fun x y hx hy => hx.elim)
        (a := 0) (by unfold N; omega) (Or.inl ⟨c, hc, hb⟩) (dsepX_gate_shape p r)
    · exact dsepX_shape_far hp (cs := []) (cs' := []) (by simp) (by simp) (by simp)
        (fun x y hx hy => by omega) (a := 0) (by unfold N; omega)
        (Or.inr (Or.inl ⟨s, hs, e, hP⟩)) (dsepX_gate_shape p r)

/-! ### The boxes of the pieces in coordinates -/

/-- A cell of the reflector box of a corner, in coordinates. -/
theorem dsepX_corner_cell {c : Corner} {x : Cell} (hx : x ∈ dsepXCB c) :
    c.u - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c.u + 25 ∧ c.v - 24 ≤ x.1 + x.2 ∧
      x.1 + x.2 ≤ c.v + 27 := by
  have h := corner_uv c
  unfold BoxT.InUV at h
  obtain ⟨x1, x2, x3, x4⟩ := hx
  omega

/-- The facts of the layout for the corners of a `decJz` activation. -/
theorem dsepX_corner_facts (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    A p i + 358 ≤ U p r - 823 - 248 * D p ∧ 0 ≤ A p i ∧ 1 ≤ D p ∧
      hairC p (qOf p (callerIdx p r i)) (A p i + decR) ≤ 0 ∧
      hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL) ≤ 0 ∧
      hairKZ p (qOf p (callerIdx p r i)) (A p i + decD) ≤ 0 ∧
      hairReg p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i)) ≤ 0 ∧
      hairReg p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i)) ≤ 0 ∧
      decChan p (2 * (callerIdx p r i)) ≤ -793 ∧ nzTokChan p (callerIdx p r i) ≤ -793 ∧
      nzAnsChan p (callerIdx p r i) ≤ -793 ∧
      destU p (i + 1) (decTN p i r) + 800 ≤ U p r ∧ destU p z (decTZ p i r z) + 800 ≤ U p r ∧
      U p r + 1230 ≤ U p r + zTokStation (callerIdx p r i) ∧
      U p r + 1301 ≤ U p r + zAnsStation (callerIdx p r i) ∧
      U p r + 1300 ≤ U p r + zTokChan p (callerIdx p r i) ∧
      U p r + 1300 ≤ U p r + zAnsChan p (callerIdx p r i) ∧
      1500 ≤ zAnsDepth p (callerIdx p r i) ∧ 1561 ≤ zTokDepth p (callerIdx p r i) ∧
      1256 ≤ nzTokPortV (callerIdx p r i) ∧ decPortV p (2 * (callerIdx p r i)) ≤ -3352 ∧
      destV p (decTN p i r) ≤ -3400 ∧ destV p (decTZ p i r z) ≤ -3400 := by
  have hAU := dsepX_AU hi
  have hA := A_nonneg p (a := (i : ℤ)) (by omega)
  have hD := one_le_D p
  have hj := dsepM_j_lt hi
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hHI := layout_facts p
  have hH := hairC_le p hq (A p i + decR)
  have hK := hairKNZ_le p hq (A p i + decR) (A p i + decL)
  have hZ := hairReg_le p (s := 2) (e := eKZ (qOf p (callerIdx p r i))) (c := A p i + decD)
    (by norm_num) (eKZ_spec hq).2.1
  have h3 := hairReg_le p (s := 3) (e := decEA p i r)
    (c := U p r + nzAnsChan p (callerIdx p r i)) (by norm_num) (solveE_bounds _ _ _).1
  have h4 := hairReg_le p (s := 4) (e := decEB p i r z)
    (c := U p r + zAnsChan p (callerIdx p r i)) (by norm_num) (solveE_bounds _ _ _).1
  have c1 := leftChan_in_extent p (idx := 2 * (callerIdx p r i))
    (v := decPortV p (2 * (callerIdx p r i))) ⟨by omega, by omega⟩
  have c2 := leftChan_in_extent p (idx := 2 * D p + 1 + 2 * (callerIdx p r i))
    (v := nzTokPortV (callerIdx p r i)) ⟨by omega, by omega⟩
  have c3 := leftChan_in_extent p (idx := 2 * D p + 2 + 2 * (callerIdx p r i))
    (v := nzAnsPortV (callerIdx p r i)) ⟨by omega, by omega⟩
  have h1 := succ_lt_of_dec hp hi
  have hz := lt_of_dec hp hi
  have hR := one_le_R p
  have g1 := unit_module_gap p (a := ((i + 1 : ℕ) : ℤ)) (r := r)
    ⟨by omega, by unfold N; push_cast; omega⟩ (by omega)
  have g2 := unit_module_gap p (a := (z : ℤ)) (r := r) ⟨by omega, by unfold N; omega⟩ (by omega)
  have hs := slabR_ge_rs p
  have hC1 := unitC0_cases p (i + 1)
  have hC2 := unitC0_cases p z
  have t1 := decTN_range hp hi
  have t2 := decTZ_range hp hi
  have hzd := zAnsDepth_eq p (callerIdx p r i)
  have hzc := fixp_bounds (uR p + 124 * qOf p (callerIdx p r i) + 62)
    (1 - zTokDepth p (callerIdx p r i) % 2)
  have hza := fixp_bounds (uR p + 124 * qOf p (callerIdx p r i))
    (1 - zAnsDepth p (callerIdx p r i) % 2)
  have hV := lane_VT_low p
  have hml : modLeft p = -823 - 248 * D p := rfl
  refine ⟨by omega, hA, hD, by omega, by omega, by unfold hairKZ; omega, by omega, by omega,
    c1.2, c2.2, c3.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [destU, inCol] at *; omega
  · simp only [destU, inCol] at *; omega
  · unfold zTokStation; omega
  · unfold zAnsStation; omega
  · unfold zTokChan; simp only [uR, qOf] at hzc ⊢; omega
  · unfold zAnsChan; simp only [uR, qOf] at hza ⊢; omega
  · omega
  · unfold zTokDepth; omega
  · unfold nzTokPortV; omega
  · unfold decPortV; omega
  · simp only [destV, sideV]; omega
  · simp only [destV, sideV]; omega

/-- The tracks of sub-band `i + 1` are low (`v ≤ -4865 - 198 D`). -/
theorem dsepX_track_low (hi : p[i]? = some (.decJz r z)) (s c : ℤ) (hs : 0 ≤ s ∧ s ≤ 9) :
    trackOut p (instrBand i) s c ≤ -4865 - 198 * D p ∧
      trackBack p (instrBand i) s c ≤ -4865 - 198 * D p := by
  have hV := lane_VT_low p
  have hil : (i : ℤ) < N p := by
    have := (List.getElem?_eq_some_iff.1 hi).1; unfold N; omega
  simp only [trackOut, trackBack, track, instrBand]
  omega

/-- The corner lists, membership simplified. -/
macro "dsepX_corners" : tactic => `(tactic| (
  simp only [bandCorners, isep2SlabC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_append] at *))

/-- **The boxes of the pieces of the main thread of an NZ activation** are left of `U_r + 798`
or below `v = -3305`. -/
theorem dsepX_LMN_cls (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLMN p i r, ∀ x ∈ g.box, x.1 - x.2 ≤ U p r + 798 ∨ x.1 + x.2 ≤ -3305 := by
  intro g hg x hx
  obtain ⟨f1, f2, f3, f4, f5, -, f7, -, f9, f10, f11, f12, -⟩ := dsepX_corner_facts hp hi
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  have hv : decL = -155 ∧ decR = 127 := ⟨rfl, rfl⟩
  rcases dsepX_LMN_shape hp hi hg with ⟨c, hc, hb⟩ | ⟨s, hs, e, hP⟩ | ⟨s, hs, rfl⟩
  · rw [hb] at hx
    have := dsepX_corner_cell hx
    rw [dsepX_cornC_eq, dsepX_cornN_eq, dsep_csN_eq hp hi, htN] at hc
    dsepX_corners
    left
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp only at this <;> omega
  · exact hP x hx
  · have hu := unitSpecs_uv p (i + 1) hs
    have h1 := succ_lt_of_dec hp hi
    have hR := one_le_R p
    have g1 := unit_module_gap p (a := ((i + 1 : ℕ) : ℤ)) (r := r)
      ⟨by omega, by unfold N; push_cast; omega⟩ (by omega)
    have hsl := slabR_ge_rs p
    have hml : modLeft p = -823 - 248 * D p := rfl
    unfold BoxT.InUV at hu
    rw [PSpec.piece_box] at hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    left
    omega

/-- **The boxes of the pieces of the main thread of a Z activation** are below `v = 730` or right
of `U_r + 1170`. -/
theorem dsepX_LMZ_cls (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ decLMZ p i r z, ∀ x ∈ g.box, x.1 + x.2 ≤ 730 ∨ U p r + 1170 ≤ x.1 - x.2 := by
  intro g hg x hx
  obtain ⟨f1, f2, f3, -, -, -, -, -, -, -, -, -, -, f14, f15, f16, f17, f18, f19, -, f21, -,
    f23⟩ := dsepX_corner_facts hp hi
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  have t1 := dsepX_track_low hi 1 (A p i + decR) (by omega)
  have t2 := dsepX_track_low hi 2 (A p i + decD) (by omega)
  have t4 := dsepX_track_low hi 4 (U p r + zAnsChan p (callerIdx p r i)) (by omega)
  rcases dsepX_LMZ_shape hp hi hg with hgr | ⟨c, hc, hb⟩ | ⟨s, hs, e, hP⟩ | ⟨s, hs, rfl⟩
  · obtain ⟨s, -, -, hP⟩ := dsepX_kind_grp hgr
    have := (hP x hx).2.2; left; omega
  · rw [hb] at hx
    have := dsepX_corner_cell hx
    rw [dsepX_cornC_eq, dsepX_cornZ_eq, dsep_csZ_eq hp hi, htN] at hc
    dsepX_corners
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp only at this <;>
      first
      | (right; omega)
      | (left; omega)
  · have := hP x hx; left; omega
  · have hu := unitSpecs_uv p z hs
    have hV := lane_VT_low p
    unfold BoxT.InUV at hu
    rw [PSpec.piece_box] at hx
    obtain ⟨x1, x2, x3, x4⟩ := hx
    left
    omega

/-- **The boxes of the pieces of the thread of `KZ`** are low (the band) or right of
`U_r + 1170` and above `v = 469`. -/
theorem dsepX_LZu_cls (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ h ∈ decLZu p i r, ∀ x ∈ h.box, x.1 + x.2 ≤ -4800 - 198 * D p ∨
      (U p r + 1170 ≤ x.1 - x.2 ∧ 469 ≤ x.1 + x.2) := by
  intro h hh x hx
  obtain ⟨-, -, f3, -, -, -, -, -, -, -, -, -, -, f14, -, f16, -, -, f19, -⟩ :=
    dsepX_corner_facts hp hi
  have t2 := dsepX_track_low hi 2 (A p i + decD) (by omega)
  rcases dsepX_LZu_shape hi hh with ⟨c, hc, hb⟩ | ⟨s, hs, e, hP⟩
  · rw [hb] at hx
    have := dsepX_corner_cell hx
    rw [dsepX_cornZ_eq] at hc
    dsepX_corners
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at this <;>
      first
      | (left; omega)
      | (right; omega)
  · have := hP x hx; right; omega

/-- **The boxes of the pieces of the thread of `KNZ`** are low (the band) or left of
`U_r - 353` and above `v = 1150`. -/
theorem dsepX_LNu_cls (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ h ∈ decLNu p i r, ∀ x ∈ h.box, x.1 + x.2 ≤ -4800 - 198 * D p ∨
      (x.1 - x.2 ≤ U p r - 353 ∧ 1150 ≤ x.1 + x.2) := by
  intro h hh x hx
  obtain ⟨-, -, f3, -, -, -, -, -, -, f10, -, -, -, -, -, -, -, -, -, f20, -⟩ :=
    dsepX_corner_facts hp hi
  have t0 := dsepX_track_low hi 0 (A p i + decL) (by omega)
  rcases dsepX_LNu_shape hi hh with ⟨c, hc, hb⟩ | ⟨s, hs, e, hP⟩
  · rw [hb] at hx
    have := dsepX_corner_cell hx
    rw [dsepX_cornN_eq] at hc
    dsepX_corners
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp only at this <;>
      first
      | (left; omega)
      | (right; omega)
  · have := hP x hx; right; omega

end LP

end LeanTheory.Life
