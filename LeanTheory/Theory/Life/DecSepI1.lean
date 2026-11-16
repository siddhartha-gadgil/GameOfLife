/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepThrMain
public import LeanTheory.Theory.Life.DecSepIGen

/-!
# The idle fields of `DecSep`: the runs at the stations

Research note `N-22`. For the fields `nIdle`, `zIdle` of `DecSepRest` every moving part of an
activation is shown far from every piece of the machine outside a list of its own pieces
(`dsepIFar`). Here the runs at station `j` (the joint approach of a token and its station, the
extended capture, the absorption of an unpaired token):

* `dsepIRN`, `dsepIRZ`: the regions (station frame) of these runs, boxes with holes at the boxes
  of the neighbouring stations (`DecSepIGen`); `dsepI_RN_far`, `dsepI_RZ_far`: placed at station
  `j` of module `r`, far from every piece of the machine except station `j`;
* `dsepI_capStartN_eq`, `dsepI_unpStartN_eq` (and `Z`): the starts of the captures and of the
  absorptions as translates of the starts of the certificates;
* `dsepI_winN_far`, `dsepI_capN_far`, `dsepI_unpN_far` (and `Z`): the runs, far from every
  piece of the machine except station `j`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Far from every piece outside a list -/

/-- **`S` is far from every piece of the machine outside the list `L`.** -/
def dsepIFar (p : Program) (S : Set Cell) (L : List Piece) : Prop :=
  ∀ g ∈ machPieces p, g ∉ L → FarApart 2 S g.box

/-- Far from the pieces outside a list: unions. -/
theorem dsepIFar.union {S T : Set Cell} {L : List Piece} (hS : dsepIFar p S L)
    (hT : dsepIFar p T L) : dsepIFar p (S ∪ T) L :=
  fun g hg hn => FarApart.union_left (hS g hg hn) (hT g hg hn)

/-- Far from the pieces outside a list: a subset, a larger list. -/
theorem dsepIFar.mono {S T : Set Cell} {L L' : List Piece} (h : dsepIFar p S L) (hT : T ⊆ S)
    (hL : ∀ x ∈ L, x ∈ L') : dsepIFar p T L' :=
  fun g hg hn => (h g hg fun hm => hn (hL g hm)).mono hT le_rfl

/-- The boxes of a list of pieces of the machine are far from the pieces outside the list. -/
theorem dsepI_boxesOf (hp : p.WellFormed) {L : List Piece} (hL : ∀ x ∈ L, x ∈ machPieces p) :
    dsepIFar p (boxesOf L) L :=
  fun _ hg hn => isep2_boxesOf_far hp hL hg hn

/-- The empty set is far from everything. -/
theorem dsepI_empty (L : List Piece) : dsepIFar p ∅ L :=
  fun _ _ _ _ hx => hx.elim

/-! ### The regions of the runs at a station -/

/-- **The region of the runs at a station of the line NZ** (station frame): a box without the
boxes, widened by `2`, of piece `0` of the next station and piece `1` of the previous one. -/
def dsepIRN : Set Cell := tightSet 363 467 784 951 [⟨450, 486, 899, 993⟩, ⟨357, 369, 817, 843⟩]

/-- **The region of the runs at a station of the line Z** (station frame). -/
def dsepIRZ : Set Cell :=
  tightSet 849 1011 (-380) (-282) [⟨959, 1053, -399, -363⟩, ⟨877, 903, -282, -270⟩]

/-- A box with holes inside another one. -/
theorem dsepI_tight_mono {a b lo hi a' b' lo' hi' : ℤ} {H H' : List BoxT}
    (h : ∀ c : Cell, c ∈ tightSet a b lo hi H → a' ≤ c.1 ∧ c.1 ≤ b' ∧ lo' ≤ c.2 ∧ c.2 ≤ hi' ∧
      ∀ B ∈ H', c ∉ Box B.a B.b B.lo B.hi) :
    tightSet a b lo hi H ⊆ tightSet a' b' lo' hi' H' := by
  intro c hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := h c hc
  exact ⟨⟨h1, h2, h3, h4⟩, h5⟩

/-- Membership in a box with two holes, in coordinates. -/
theorem dsepI_mem_tight2 {a b lo hi : ℤ} {B₁ B₂ : BoxT} {c : Cell} :
    c ∈ tightSet a b lo hi [B₁, B₂] ↔ (a ≤ c.1 ∧ c.1 ≤ b ∧ lo ≤ c.2 ∧ c.2 ≤ hi) ∧
      ¬ (B₁.a ≤ c.1 ∧ c.1 ≤ B₁.b ∧ B₁.lo ≤ c.2 ∧ c.2 ≤ B₁.hi) ∧
      ¬ (B₂.a ≤ c.1 ∧ c.1 ≤ B₂.b ∧ B₂.lo ≤ c.2 ∧ c.2 ≤ B₂.hi) := by
  simp [tightSet, Box]

/-- Membership in a box with one hole, in coordinates. -/
theorem dsepI_mem_tight1 {a b lo hi : ℤ} {B₁ : BoxT} {c : Cell} :
    c ∈ tightSet a b lo hi [B₁] ↔ (a ≤ c.1 ∧ c.1 ≤ b ∧ lo ≤ c.2 ∧ c.2 ≤ hi) ∧
      ¬ (B₁.a ≤ c.1 ∧ c.1 ≤ B₁.b ∧ B₁.lo ≤ c.2 ∧ c.2 ≤ B₁.hi) := by
  simp [tightSet, Box]

/-- The run regions of the line NZ lie in `dsepIRN`. -/
theorem dsepI_RN_sub :
    tightSet 363 467 820 919 [⟨450, 486, 899, 993⟩, ⟨357, 369, 817, 843⟩] ⊆ dsepIRN ∧
      tightSet 376 467 784 951 [⟨450, 486, 899, 993⟩] ⊆ dsepIRN ∧
      tightSet 380 467 820 919 [⟨450, 486, 899, 993⟩] ⊆ dsepIRN := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · rw [dsepI_mem_tight2] at hc
    rw [dsepIRN, dsepI_mem_tight2]
    dsimp only at hc ⊢
    omega
  · rw [dsepI_mem_tight1] at hc
    rw [dsepIRN, dsepI_mem_tight2]
    dsimp only at hc ⊢
    omega
  · rw [dsepI_mem_tight1] at hc
    rw [dsepIRN, dsepI_mem_tight2]
    dsimp only at hc ⊢
    omega

/-- The run regions of the line Z lie in `dsepIRZ`. -/
theorem dsepI_RZ_sub :
    tightSet 880 979 (-380) (-282) [⟨959, 1053, -399, -363⟩, ⟨877, 903, -282, -270⟩] ⊆
        dsepIRZ ∧
      tightSet 849 1011 (-380) (-289) [⟨959, 1053, -399, -363⟩] ⊆ dsepIRZ ∧
      tightSet 880 979 (-380) (-293) [⟨959, 1053, -399, -363⟩] ⊆ dsepIRZ := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · rw [dsepI_mem_tight2] at hc
    rw [dsepIRZ, dsepI_mem_tight2]
    dsimp only at hc ⊢
    omega
  · rw [dsepI_mem_tight1] at hc
    rw [dsepIRZ, dsepI_mem_tight2]
    dsimp only at hc ⊢
    omega
  · rw [dsepI_mem_tight1] at hc
    rw [dsepIRZ, dsepI_mem_tight2]
    dsimp only at hc ⊢
    omega

/-- A piece of station `j` of the line NZ, with its box. -/
theorem dsepI_own_stNZ (p : Program) (r j : ℕ) {i' : ℕ} (hi : i' < 3) :
    ∃ x ∈ stNZOne p r j, dsepTB x =
      (dsepTBase (.stNZ i')).mv (modDX p r + 72 * (j : ℤ)) (modDY p r + 72 * (j : ℤ)) := by
  refine ⟨(PSpec.mk (.stNZ i') (modDX p r + 72 * (j : ℤ)) (modDY p r + 72 * (j : ℤ))
    (12 * j % 30)).piece, ?_, rfl⟩
  simp only [stNZOne, groupSpecs, List.map_map, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false]
  interval_cases i'
  · exact ⟨.stNZ 0, Or.inl rfl, rfl⟩
  · exact ⟨.stNZ 1, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨.stNZ 2, Or.inr (Or.inr rfl), rfl⟩

/-- A piece of station `j` of the line Z, with its box. -/
theorem dsepI_own_stZ (p : Program) (r j : ℕ) {i' : ℕ} (hi : i' < 3) :
    ∃ x ∈ stZOne p r j, dsepTB x =
      (dsepTBase (.stZ i')).mv (modDX p r + 72 * (j : ℤ)) (modDY p r - 72 * (j : ℤ)) := by
  refine ⟨(PSpec.mk (.stZ i') (modDX p r + 72 * (j : ℤ)) (modDY p r - 72 * (j : ℤ))
    (12 * j % 30)).piece, ?_, rfl⟩
  simp only [stZOne, groupSpecs, List.map_map, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false]
  interval_cases i'
  · exact ⟨.stZ 0, Or.inl rfl, rfl⟩
  · exact ⟨.stZ 1, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨.stZ 2, Or.inr (Or.inr rfl), rfl⟩

/-- The box of a base piece moved, as a set. -/
theorem dsepI_mv_set (b : Base) (x y : ℤ) :
    ((dsepTBase b).mv x y).set = Box (b.piece.a + x) (b.piece.b + x) (b.piece.lo + y)
      (b.piece.hi + y) := rfl

/-- The box of a base piece, as a set. -/
theorem dsepI_base_set (b : Base) :
    (dsepTBase b).set = Box b.piece.a b.piece.b b.piece.lo b.piece.hi := rfl

/-- **The region of the runs at station `j` of the line NZ of module `r` is far from every piece
of the machine except the pieces of station `j`.** -/
theorem dsepI_RN_far (hp : p.WellFormed) (hr : r < numRegs p) {j : ℕ} (hj : j < numCallers p) :
    dsepIFar p (modImg p r ((fun c => ((72 * (j : ℤ), 72 * (j : ℤ)) : Cell) + c) '' dsepIRN))
      (stNZOne p r j) := by
  have hD : D p = (numCallers p : ℤ) := rfl
  have hb := base_boxes
  have hjD : (j : ℤ) < D p := by omega
  have hmem : ∀ {x : Cell}, x ∈ (fun c => ((72 * (j : ℤ), 72 * (j : ℤ)) : Cell) + c) '' dsepIRN →
      (363 + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 467 + 72 * (j : ℤ) ∧ 784 + 72 * (j : ℤ) ≤ x.2 ∧
        x.2 ≤ 951 + 72 * (j : ℤ)) ∧
      ¬ (450 + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 486 + 72 * (j : ℤ) ∧ 899 + 72 * (j : ℤ) ≤ x.2 ∧
        x.2 ≤ 993 + 72 * (j : ℤ)) ∧
      ¬ (357 + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 369 + 72 * (j : ℤ) ∧ 817 + 72 * (j : ℤ) ≤ x.2 ∧
        x.2 ≤ 843 + 72 * (j : ℤ)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [dsepIRN, dsepI_mem_tight2] at hd
    dsimp only at hd
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  refine dsepT_zone_far hp ?_ (fun x hx => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (stNZOne_mem p r hj hx)
      exact decModule_mem hr hs) ?_
  · intro x hx
    have := hmem hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  refine dsepT_mod_cls (own := fun B => ∃ x ∈ stNZOne p r j, dsepTB x = B)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i' hi' _
    have := dz2g_facts i' hi'
    rw [dsepI_base_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro m _ _ _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro j' h0 h1 i' hi' hn
    by_cases hjj : j' = (j : ℤ)
    · subst hjj
      exact absurd (dsepI_own_stNZ p r j hi') hn
    · have := stNZ_cases i' hi'
      rw [dsepI_mv_set]
      refine isep2_far_box fun x hx => ?_
      have := hmem hx
      omega
  · intro j' h0 h1 i' hi' _
    have := stZ_cases i' hi'
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega

/-- **The region of the runs at station `j` of the line Z of module `r` is far from every piece
of the machine except the pieces of station `j`.** -/
theorem dsepI_RZ_far (hp : p.WellFormed) (hr : r < numRegs p) {j : ℕ} (hj : j < numCallers p) :
    dsepIFar p (modImg p r ((fun c => ((72 * (j : ℤ), -72 * (j : ℤ)) : Cell) + c) '' dsepIRZ))
      (stZOne p r j) := by
  have hD : D p = (numCallers p : ℤ) := rfl
  have hb := base_boxes
  have hjD : (j : ℤ) < D p := by omega
  have hmem : ∀ {x : Cell}, x ∈ (fun c => ((72 * (j : ℤ), -72 * (j : ℤ)) : Cell) + c) '' dsepIRZ →
      (849 + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 1011 + 72 * (j : ℤ) ∧ -380 - 72 * (j : ℤ) ≤ x.2 ∧
        x.2 ≤ -282 - 72 * (j : ℤ)) ∧
      ¬ (959 + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 1053 + 72 * (j : ℤ) ∧ -399 - 72 * (j : ℤ) ≤ x.2 ∧
        x.2 ≤ -363 - 72 * (j : ℤ)) ∧
      ¬ (877 + 72 * (j : ℤ) ≤ x.1 ∧ x.1 ≤ 903 + 72 * (j : ℤ) ∧ -282 - 72 * (j : ℤ) ≤ x.2 ∧
        x.2 ≤ -270 - 72 * (j : ℤ)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [dsepIRZ, dsepI_mem_tight2] at hd
    dsimp only at hd
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  refine dsepT_zone_far hp ?_ (fun x hx => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (stZOne_mem p r hj hx)
      exact decModule_mem hr hs) ?_
  · intro x hx
    have := hmem hx
    simp only [dsepTZone, Set.mem_ofPred_eq]
    omega
  refine dsepT_mod_cls (own := fun B => ∃ x ∈ stZOne p r j, dsepTB x = B)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i' hi' _
    have := dz2g_facts i' hi'
    rw [dsepI_base_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro m _ _ _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro j' h0 h1 i' hi' _
    have := stNZ_cases i' hi'
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro j' h0 h1 i' hi' hn
    by_cases hjj : j' = (j : ℤ)
    · subst hjj
      exact absurd (dsepI_own_stZ p r j hi') hn
    · have := stZ_cases i' hi'
      rw [dsepI_mv_set]
      refine isep2_far_box fun x hx => ?_
      have := hmem hx
      omega
  · intro _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega
  · intro _
    rw [dsepI_mv_set]
    refine isep2_far_box fun x hx => ?_
    have := hmem hx
    omega


/-! ### The starts of the captures and of the absorptions -/

/-- The start of the extended capture of the line NZ, as the certificate's start. -/
theorem dsepI_capStartN_eq (hi : p[i]? = some (.decJz r z)) :
    decCapStartN p i r = translate (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ)) (stCaptureNZG ∪ stCaptureNZIn) := by
  have hc := (decCap_cast p hi).1
  have hA : ansNZWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have hK : (tokNZWL 0).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have hsh := decShift_mod p i r
  have e1 : ((decCapN p i r : ℕ) : ℤ) = 10350 + 288 * ((callerIdx p r i : ℕ) : ℤ) +
      decShift p i r := by omega
  unfold decCapStartN decAnsWLN decTokN
  rw [stNZOne, stNZ_one_at, e1, modShift_cells p r ⟨Or.inl rfl, Or.inl rfl⟩,
    modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩, tokNZWL_step,
    ← ansNZWL_step ((callerIdx p r i : ℕ) : ℤ), cells_step hA, cells_step hK,
    translate_translate, translate_translate, ← translate_union, ← stCaptureNZIn_eq,
    show ((modDX p r, modDY p r) + (72 * ((callerIdx p r i : ℕ) : ℤ),
      72 * ((callerIdx p r i : ℕ) : ℤ)) : Cell) = (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ)) from rfl, ← translate_union,
    phase_congr stNZG (a := 12 * callerIdx p r i % 30 + decCapN p i r) (b := 0) (by omega),
    show phase stNZG 0 = stNZG by rw [phase, Nat.zero_mod, Rule.evolve_zero], ← stCaptureNZG_eq]

/-- The start of the extended capture of the line Z, as the certificate's start. -/
theorem dsepI_capStartZ_eq (hi : p[i]? = some (.decJz r z)) :
    decCapStartZ p i r = translate (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) (stCaptureZG ∪ stCaptureZIn) := by
  have hc := (decCap_cast p hi).2
  have hA : ansZWL.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have hK : (tokZWL 0).Dir := ⟨Or.inr rfl, Or.inr rfl⟩
  have hsh := decShift_mod p i r
  have e1 : ((decCapZ p i r : ℕ) : ℤ) = 12390 + 288 * ((callerIdx p r i : ℕ) : ℤ) +
      decShift p i r := by omega
  unfold decCapStartZ decAnsWLZ decTokZ
  rw [stZOne, stZ_one_at, e1, modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩,
    modShift_cells p r ⟨Or.inr rfl, Or.inr rfl⟩, tokZWL_step,
    ← ansZWL_step ((callerIdx p r i : ℕ) : ℤ), cells_step hA, cells_step hK,
    translate_translate, translate_translate, ← translate_union, ← stCaptureZIn_eq,
    show ((modDX p r, modDY p r) + (72 * ((callerIdx p r i : ℕ) : ℤ),
      -72 * ((callerIdx p r i : ℕ) : ℤ)) : Cell) = (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) from Prod.ext rfl (by simp; ring),
    ← translate_union,
    phase_congr stZG (a := 12 * callerIdx p r i % 30 + decCapZ p i r) (b := 0) (by omega),
    show phase stZG 0 = stZG by rw [phase, Nat.zero_mod, Rule.evolve_zero], ← stCaptureZG_eq]

/-- The start of the absorption of the unpaired `KNZ`, as the certificate's start. -/
theorem dsepI_unpStartN_eq (hi : p[i]? = some (.decJz r z)) :
    decUnpStartN p i r = translate (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ))
      (stUnpairedTokenNZG ∪ stUnpairedTokenNZIn) := by
  have hc := (decCap_cast p hi).1
  have hK : (tokNZWL 0).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have hsh := decShift_mod p i r
  have e1 : ((decCapN p i r : ℕ) : ℤ) = 10350 + 288 * ((callerIdx p r i : ℕ) : ℤ) +
      decShift p i r := by omega
  unfold decUnpStartN decTokN
  rw [stNZOne, stNZ_one_at, e1, modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩, tokNZWL_step,
    cells_step hK, translate_translate, ← stUnpairedTokenNZIn_eq,
    show ((modDX p r, modDY p r) + (72 * ((callerIdx p r i : ℕ) : ℤ),
      72 * ((callerIdx p r i : ℕ) : ℤ)) : Cell) = (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ)) from rfl, ← translate_union,
    phase_congr stNZG (a := 12 * callerIdx p r i % 30 + decCapN p i r) (b := 0) (by omega),
    show phase stNZG 0 = stNZG by rw [phase, Nat.zero_mod, Rule.evolve_zero],
    ← stUnpairedTokenNZG_eq]

/-- The start of the absorption of the unpaired `KZ`, as the certificate's start. -/
theorem dsepI_unpStartZ_eq (hi : p[i]? = some (.decJz r z)) :
    decUnpStartZ p i r = translate (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) (stUnpairedTokenZG ∪ stUnpairedTokenZIn) := by
  have hc := (decCap_cast p hi).2
  have hK : (tokZWL 0).Dir := ⟨Or.inr rfl, Or.inr rfl⟩
  have hsh := decShift_mod p i r
  have e1 : ((decCapZ p i r : ℕ) : ℤ) = 12390 + 288 * ((callerIdx p r i : ℕ) : ℤ) +
      decShift p i r := by omega
  unfold decUnpStartZ decTokZ
  rw [stZOne, stZ_one_at, e1, modShift_cells p r ⟨Or.inr rfl, Or.inr rfl⟩, tokZWL_step,
    cells_step hK, translate_translate, ← stUnpairedTokenZIn_eq,
    show ((modDX p r, modDY p r) + (72 * ((callerIdx p r i : ℕ) : ℤ),
      -72 * ((callerIdx p r i : ℕ) : ℤ)) : Cell) = (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) from Prod.ext rfl (by simp; ring),
    ← translate_union,
    phase_congr stZG (a := 12 * callerIdx p r i % 30 + decCapZ p i r) (b := 0) (by omega),
    show phase stZG 0 = stZG by rw [phase, Nat.zero_mod, Rule.evolve_zero],
    ← stUnpairedTokenZG_eq]

/-! ### The runs at the stations, far from the machine -/

/-- A run at station `j` (translated certificate region inside `R`) lies in the region `R` placed
at station `j` of module `r`. -/
theorem dsepI_img_sub (p : Program) (r : ℕ) (x y : ℤ) {T R : Set Cell} (h : T ⊆ R) :
    (fun c => ((modDX p r + x, modDY p r + y) : Cell) + c) '' T ⊆
      modImg p r ((fun c => ((x, y) : Cell) + c) '' R) := by
  rintro _ ⟨d, hd, rfl⟩
  refine ⟨((x, y) : Cell) + d, ⟨d, h hd, rfl⟩, ?_⟩
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- `-72 j` as a subtraction. -/
theorem dsepI_neg72 (a j : ℤ) : a - 72 * j = a + -72 * j := by ring

/-- **The joint approach of `KNZ` and its station** is far from every piece of the machine
except station `j`. -/
theorem dsepI_winN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k ≤ 90, dsepIFar p (conway.evolve k (decTokWStartN p i r) : Set Cell)
      (stNZOne p r (callerIdx p r i)) := by
  intro k hk
  rw [decTokWStartN_eq hi]
  exact (dsepI_RN_far hp (lt_numRegs_of_dec hi) (callerIdx_lt_D p hi)).mono
    (((dsepI_tokWNZ_tight.translate _) k hk).trans
      (dsepI_img_sub p r _ _ dsepI_RN_sub.1)) fun _ h => h

/-- **The extended capture at station `j` of the line NZ** is far from every piece of the machine
except station `j`. -/
theorem dsepI_capN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k ≤ 692, dsepIFar p (conway.evolve k (decCapStartN p i r) : Set Cell)
      (stNZOne p r (callerIdx p r i)) := by
  intro k hk
  rw [dsepI_capStartN_eq hi]
  exact (dsepI_RN_far hp (lt_numRegs_of_dec hi) (callerIdx_lt_D p hi)).mono
    (((dsepI_capNZ_tight.translate _) k hk).trans
      (dsepI_img_sub p r _ _ dsepI_RN_sub.2.1)) fun _ h => h

/-- **The absorption of the unpaired `KNZ`** is far from every piece of the machine except
station `j`. -/
theorem dsepI_unpN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k ≤ 292, dsepIFar p (conway.evolve k (decUnpStartN p i r) : Set Cell)
      (stNZOne p r (callerIdx p r i)) := by
  intro k hk
  rw [dsepI_unpStartN_eq hi]
  exact (dsepI_RN_far hp (lt_numRegs_of_dec hi) (callerIdx_lt_D p hi)).mono
    (((dsepI_unpNZ_tight.translate _) k hk).trans
      (dsepI_img_sub p r _ _ dsepI_RN_sub.2.2)) fun _ h => h

/-- **The joint approach of `KZ` and its station** is far from every piece of the machine
except station `j`. -/
theorem dsepI_winZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k ≤ 90, dsepIFar p (conway.evolve k (decTokWStartZ p i r) : Set Cell)
      (stZOne p r (callerIdx p r i)) := by
  intro k hk
  rw [decTokWStartZ_eq hi, dsepI_neg72]
  exact (dsepI_RZ_far hp (lt_numRegs_of_dec hi) (callerIdx_lt_D p hi)).mono
    (((dsepI_tokWZ_tight.translate _) k hk).trans
      (dsepI_img_sub p r _ _ dsepI_RZ_sub.1)) fun _ h => h

/-- **The extended capture at station `j` of the line Z** is far from every piece of the machine
except station `j`. -/
theorem dsepI_capZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k ≤ 672, dsepIFar p (conway.evolve k (decCapStartZ p i r) : Set Cell)
      (stZOne p r (callerIdx p r i)) := by
  intro k hk
  rw [dsepI_capStartZ_eq hi, dsepI_neg72]
  exact (dsepI_RZ_far hp (lt_numRegs_of_dec hi) (callerIdx_lt_D p hi)).mono
    (((dsepI_capZ_tight.translate _) k hk).trans
      (dsepI_img_sub p r _ _ dsepI_RZ_sub.2.1)) fun _ h => h

/-- **The absorption of the unpaired `KZ`** is far from every piece of the machine except
station `j`. -/
theorem dsepI_unpZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ k ≤ 272, dsepIFar p (conway.evolve k (decUnpStartZ p i r) : Set Cell)
      (stZOne p r (callerIdx p r i)) := by
  intro k hk
  rw [dsepI_unpStartZ_eq hi, dsepI_neg72]
  exact (dsepI_RZ_far hp (lt_numRegs_of_dec hi) (callerIdx_lt_D p hi)).mono
    (((dsepI_unpZ_tight.translate _) k hk).trans
      (dsepI_img_sub p r _ _ dsepI_RZ_sub.2.2)) fun _ h => h

end LP

end LeanTheory.Life
