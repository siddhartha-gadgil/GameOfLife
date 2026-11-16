/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepRoute

/-!
# The entry chains and the body, far from the whole machine

Research note `N-22`. Two footprints of an `inc` activation at the units, far from every piece of
the machine other than their own pieces (for the fields `idle` and `body` of `IncSep`):

* `isep2_entry_far`: the entry footprint `entryFoot` of copies `0 … t` of the chain of a used
  unit is far from every piece of the machine other than those copies (the later copies of the
  chain are `≥ 26` rows above, the body `≥ 80` below in `v`, the input corners of the unit `≥ 9`
  left);
* `isep2_body`: the box of the body of an `inc` unit is far from every piece of the machine
  other than the body (the field `body`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-! ### The corners at the input of a unit -/

/-- The input corner is the only corner of an up-going link at a slab place, of image `1`. -/
theorem isep2_upK_slab (k0 : ℕ) (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) :
    ∀ x ∈ upCornersK k0 p b s c H a t, ∀ a' t' : ℤ, x.tag = .slab a' t' → x.k = 1 := by
  simp [upCornersK, bandCorners]

/-- A down-going link has no corner at a slab place. -/
theorem isep2_down_slab (p : Program) (b s c H cd vp : ℤ) (r : ℕ) (idx : ℤ) :
    ∀ x ∈ downCorners p b s c H cd vp r idx, ∀ a' t' : ℤ, x.tag = .slab a' t' → x.k = 1 := by
  simp [downCorners, bandCorners]

/-- **Every corner of the machine at a slab place is of image `1`.** -/
theorem isep2_slab_k {p : Program} :
    ∀ c ∈ allCorners p, ∀ a t : ℤ, c.tag = .slab a t → c.k = 1 := by
  intro c hc a t ht
  unfold allCorners at hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨i, -, hc⟩ := List.mem_flatMap.1 hc
    unfold instrCorners specCorners instrSpecs at hc
    split at hc
    · simp only [haltCorners, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp at ht
    · obtain ⟨x, hx, hc⟩ := List.mem_flatMap.1 hc
      simp only [incSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact isep2_upK_slab _ _ _ _ _ _ _ _ c hc a t ht
      · exact isep2_upK_slab _ _ _ _ _ _ _ _ c hc a t ht
    · obtain ⟨x, hx, hc⟩ := List.mem_flatMap.1 hc
      simp only [decSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact isep2_down_slab _ _ _ _ _ _ _ _ _ c hc a t ht
      · exact isep2_down_slab _ _ _ _ _ _ _ _ _ c hc a t ht
      · simp only [ztokCorners, bandCorners, List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at ht
      · simp only [nzAnsCorners, List.mem_cons] at hc
        rcases hc with rfl | hc
        · simp at ht
        · exact isep2_upK_slab _ _ _ _ _ _ _ _ c hc a t ht
      · simp only [zAnsCorners, List.mem_cons] at hc
        rcases hc with rfl | rfl | hc
        · simp at ht
        · simp at ht
        · exact isep2_upK_slab _ _ _ _ _ _ _ _ c hc a t ht
    · simp at hc
  · obtain ⟨r, -, hc⟩ := List.mem_flatMap.1 hc
    simp only [specCorners, mergeSpecs, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
    exact isep2_down_slab _ _ _ _ _ _ _ _ _ c hc a t ht

/-! ### The entry footprint -/

/-- **A cell of the entry footprint** of unit `a` from copy `t` lies in the tight footprint of
some copy `m ≤ t`. -/
theorem isep2_mem_entryFoot {a t : ℕ} {c : Cell} (hc : c ∈ entryFoot p a t) :
    ∃ m : ℕ, m ≤ t ∧ (c.1 - (unitDX p a - 35 * m), c.2 - (unitDY p a - 64 * m)) ∈ orFoot := by
  obtain ⟨d, ⟨j, hj, hd⟩, rfl⟩ := hc
  refine ⟨t - j, by omega, ?_⟩
  have hj' : (j : ℤ) ≤ t := by exact_mod_cast Nat.lt_succ_iff.1 hj
  convert hd using 2 <;> simp only [Prod.fst_add, Prod.snd_add] <;> push_cast <;>
    [rw [Nat.cast_sub (by omega)]; rw [Nat.cast_sub (by omega)]] <;> ring

/-- Cells of the entry footprint, in coordinates: below the later copies (`y ≥ y_a - 64 t - 6`)
and inside the rectangle of `entryFoot_uv`. -/
theorem isep2_entryFoot_xy {a t : ℕ} {c : Cell} (hc : c ∈ entryFoot p a t) :
    unitDY p a - 64 * t - 6 ≤ c.2 ∧ A p a - 38 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ A p a + 96 + 29 * t ∧
      VU p - 99 * t - 6 ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ VU p + 133 := by
  have huv := entryFoot_uv p a t hc
  obtain ⟨m, hm, hfoot⟩ := isep2_mem_entryFoot hc
  have hm' : (m : ℤ) ≤ t := by exact_mod_cast hm
  rcases hfoot with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩ <;> simp only at h3 <;> omega

/-- A copy of the chain of a unit, as a piece of `chainPieces`. -/
theorem isep2_chain_mem (p : Program) (a : ℕ) {t t' : ℕ} (h : t' ≤ t) :
    (PSpec.mk .orGate (unitDX p a - 35 * (t' : ℤ)) (unitDY p a - 64 * (t' : ℤ))
      (14 * t' % 30)).piece ∈ chainPieces p a t := by
  unfold chainPieces chainSpecs
  exact List.mem_map_of_mem (List.mem_map_of_mem (f := fun t : ℕ =>
    (⟨.orGate, unitDX p a - 35 * (t : ℤ), unitDY p a - 64 * (t : ℤ), 14 * t % 30⟩ : PSpec))
    (List.mem_range.2 (by omega)))

/-- **The entry footprint of a used unit is far from every piece of the machine other than the
copies `0 … t` of its chain.** -/
theorem isep2_entry_far (hp : p.WellFormed) {a t : ℕ} (ha : (a : ℤ) ≤ N p + R p - 1)
    (ht : (t : ℤ) < 2 * P p) :
    ∀ h ∈ machPieces p, h ∉ chainPieces p a t → FarApart 2 (entryFoot p a t) h.box := by
  intro h hh hn
  have hf := layout_facts p
  have hd := unitD_uv p a
  have hS := fun c (hc : c ∈ entryFoot p a t) => isep2_entryFoot_xy hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  rcases mem_machSpecs hs with ⟨a', ha', hs⟩ | ⟨r', hr', hs⟩ | ⟨c, hc, hb⟩
  · rcases lt_trichotomy a' a with h' | rfl | h'
    · have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := a') (a' := a) (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
    · rcases isep2_unit_cases p a' hs with ⟨t', ht', rfl⟩ | ⟨h1, h2, h3, h4⟩
      · by_cases htt : t' ≤ t
        · exact absurd (isep2_chain_mem p a' htt) hn
        · rw [isep2_chain_box]
          refine isep2_far_box fun x hx => ?_
          have := hS x hx
          omega
      · rw [PSpec.piece_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
    · have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := a) (a' := a') (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
  · exact entryFoot_far_module p ha ht hs
  · have hv := allCorners_valid hp c hc
    have hcu := corner_uv c
    rw [PSpec.piece_box, hb]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hcu
    obtain ⟨k, u, v, tag⟩ := c
    simp only at hcu
    cases tag with
    | band b n h' => simp only [Valid] at hv; omega
    | halt a'' => simp only [Valid] at hv; omega
    | slab a'' t' =>
      simp only [Valid] at hv
      have hC'' := unitC0_cases p a''.toNat
      have hC := unitC0_cases p a
      rcases lt_trichotomy a'' a with h' | rfl | h'
      · have := A_add_le p h'
        omega
      · -- the input corners of the unit: `≥ 9` left (image `1`)
        have hk1 : k = 1 := isep2_slab_k _ hc _ t' rfl
        subst hk1
        simp only [Int.toNat_natCast] at hv
        have hpar : (u + v) % 2 = 1 := by
          have := A_even p a
          have := VU_even p
          omega
        have hsl := slab_uv (u := u) (v := v) (.slab (a : ℤ) t') hpar
        unfold BoxT.InUV at hsl
        omega
      · have := A_add_le p h'
        omega
    | left r' idx => simp only [Valid] at hv; omega
    | right r' j' w => simp only [Valid] at hv; omega

/-! ### The body -/

/-- The body box in coordinates. -/
theorem isep2_mem_bodyBox {c : Cell} (hc : c ∈ bodyBox p i) :
    unitDX p i + 113 ≤ c.1 ∧ c.1 ≤ unitDX p i + 354 ∧ unitDY p i + 61 ≤ c.2 ∧
      c.2 ≤ unitDY p i + 286 := by
  obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hc
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- **`IncSep.body`**: the box of the body of an `inc` unit is far from every piece of the
machine other than the body. -/
theorem isep2_body (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ g ∈ machPieces p, g ∉ bodyGroup p i → FarApart 2 (bodyBox p i) g.box := by
  intro h hh hn
  have hf := layout_facts p
  have hd := unitD_uv p i
  have hS := fun c (hc : c ∈ bodyBox p i) => isep2_mem_bodyBox hc
  have hkind : unitKind p i = .inc := by unfold unitKind; rw [hins]
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  rcases mem_machSpecs hs with ⟨a', ha', hs⟩ | ⟨r', hr', hs⟩ | ⟨c, hc, hb⟩
  · rcases lt_trichotomy a' i with h' | rfl | h'
    · have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := a') (a' := i) (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
    · unfold unitSpecs at hs
      rw [hkind] at hs
      rcases List.mem_append.1 hs with hs | hs
      · obtain ⟨t', ht', rfl⟩ := mem_chainSpecs hs
        rw [isep2_chain_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
      · exact absurd (List.mem_map_of_mem hs) hn
    · have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := i) (a' := a') (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
  · have hu := (moduleSpecs_uv p r' hs).1
    rw [PSpec.piece_box]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hu
    omega
  · have hv := allCorners_valid hp c hc
    have hcu := corner_uv c
    rw [PSpec.piece_box, hb]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hcu
    obtain ⟨k, u, v, tag⟩ := c
    simp only at hcu
    cases tag with
    | band b n h' => simp only [Valid] at hv; omega
    | halt a'' => simp only [Valid] at hv; omega
    | slab a'' t' =>
      simp only [Valid] at hv
      have hC'' := unitC0_cases p a''.toNat
      rcases lt_trichotomy a'' i with h' | h' | h'
      · have := A_add_le p h'
        omega
      · omega
      · have := A_add_le p h'
        omega
    | left r' idx => simp only [Valid] at hv; omega
    | right r' j' w => simp only [Valid] at hv; omega

end LP

end LeanTheory.Life
