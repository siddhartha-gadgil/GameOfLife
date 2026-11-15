/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncRegion
public import LeanTheory.Theory.Life.RouteSep3

/-!
# Separation of the entry chains of an `inc` activation

The fields `IncSep.entC` and `IncSep.entR` (`ActivationIncStep`): the footprint `entryFoot` of the
entry chain of unit `i + 1` (continue) and of the merge unit `N + r` (INC link) is far from every
other piece active in its thread, **for every well-formed program** (`incPlan_entC`,
`incPlan_entR`).

With the crude relay box `Box 0 90 (-6) 60` the field `entR` was false: for the first `inc` on a
register the INC link enters the merge unit (`C0 = -67`) at copy `0`, and the reflector of its
input corner (image `1`, box `x ∈ [-1, 7]`, `y ∈ [54, 76]` in the unit frame) meets the relay box
(`x ∈ [0, 7]`, `y ∈ [54, 60]`). The footprint is now the tight one, `orFoot` (`OrChainTight`).

* `entryFoot_uv`: the entry footprint of unit `a` from copy `t` lies in
  `u ∈ [A_a - 38, A_a + 96 + 29 t]`, `v ∈ [V_U - 99 t - 6, V_U + 133]`;
* `farApart_uv`: a set inside a rectangle of `(u, v)` is far from a box whose `uv`-hull is `≥ 6`
  away;
* `slab_uv`, `entryFoot_far_slab`: the reflector of the input corner of copy `t` (image `1`) lies
  in `u ≤ A_a + C0 - 61 t + 20`, `≥ 9` left of the entry footprint (`C0 ≤ -67`);
  `entryFoot_far_slab'`: the same for the input corner of every copy of the unit;
* `entryFoot_far_band`, `entryFoot_far_module`, `entryFoot_far_left`: band corners (`v` far
  above), module pieces and the INC port corner of a module (`u` far right);
* `incPlan_entC`, `incPlan_entR`: the two fields for the plan `incPlan`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The entry footprint in `(u, v)` -/

/-- **The entry footprint in `(u, v)`**: the copies `0 … t` of the tight relay footprint lie in
`u ∈ [A_a - 38, A_a + 96 + 29 t]`, `v ∈ [V_U - 99 t - 6, V_U + 133]`. -/
theorem entryFoot_uv (p : Program) (a t : ℕ) {c : Cell} (hc : c ∈ entryFoot p a t) :
    A p a - 38 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ A p a + 96 + 29 * t ∧
      VU p - 99 * t - 6 ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ VU p + 133 := by
  obtain ⟨c0, ⟨j, hj, hc0⟩, rfl⟩ := hc
  have hd := unitD_uv p a
  have hj' : (j : ℤ) ≤ t := by exact_mod_cast Nat.lt_succ_iff.1 hj
  simp only [orFoot, Set.mem_union, mem_box] at hc0
  simp only [Prod.fst_add, Prod.snd_add]
  rcases hc0 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega

/-- **A set inside a rectangle of `(u, v)` is far from a box whose `uv`-hull is `≥ 6` away.** -/
theorem farApart_uv {S : Set Cell} {u1 u2 v1 v2 : ℤ}
    (hS : ∀ c ∈ S, u1 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ u2 ∧ v1 ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ v2)
    {B : BoxT} {u1' u2' v1' v2' : ℤ} (hB : B.InUV u1' u2' v1' v2')
    (h : u2 + 6 ≤ u1' ∨ u2' + 6 ≤ u1 ∨ v2 + 6 ≤ v1' ∨ v2' + 6 ≤ v1) :
    FarApart 2 S (Box B.a B.b B.lo B.hi) := by
  intro x hx y hy hn
  have h1 := hS x hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  obtain ⟨n1, n2, n3, n4⟩ := hn
  unfold BoxT.InUV at hB
  push_cast at n1 n2 n3 n4
  omega

/-- The entry footprint is far from a box whose `uv`-hull is `≥ 6` from its rectangle. -/
theorem entryFoot_far (p : Program) (a t : ℕ) {B : BoxT} {u1' u2' v1' v2' : ℤ}
    (hB : B.InUV u1' u2' v1' v2')
    (h : A p a + 96 + 29 * t + 6 ≤ u1' ∨ u2' + 6 ≤ A p a - 38 ∨ VU p + 133 + 6 ≤ v1' ∨
      v2' + 6 ≤ VU p - 99 * t - 6) :
    FarApart 2 (entryFoot p a t) (Box B.a B.b B.lo B.hi) :=
  farApart_uv (fun _ hc => entryFoot_uv p a t hc) hB h

/-! ### The reflector of the input corner of the entry copy -/

/-- **The reflector of an image-`1` corner** (the input corner of an entry copy) at `(u, v)` with
`u + v` odd: its `uv`-hull is `[u - 10, u + 20] × [v - 23, v + 7]`. -/
theorem slab_uv {u v : ℤ} (tag : CTag) (hpar : (u + v) % 2 = 1) :
    (cornerSpec ⟨1, u, v, tag⟩).bx.InUV (u - 10) (u + 20) (v - 23) (v + 7) := by
  simp only [cornerSpec, PSpec.bx_mk, BoxT.InUV, rfX, rfY, Base.piece, rfP, rfCU, rfCV]
  omega

/-- The input corner of entry copy `t` of a unit is on an odd `u + v`. -/
theorem dest_odd (p : Program) (a : ℕ) (t : ℤ) : (destU p a t + destV p t) % 2 = 1 := by
  have := A_even p a
  have := VU_even p
  obtain h | h | h := unitC0_cases p a <;>
    simp only [destU, destV, inCol, sideV, h] <;> omega

/-- **The entry footprint of copy `t` is far from the reflector of the input corner of copy
`t`** (image `1`, `9` columns of `u` to the left; `C0 ≤ -67` for every unit kind). -/
theorem entryFoot_far_slab (p : Program) (a t : ℕ) (tag : CTag) :
    FarApart 2 (entryFoot p a t)
      (cornerSpec ⟨1, destU p a t, destV p t, tag⟩).piece.box := by
  rw [PSpec.piece_box]
  refine entryFoot_far p a t (slab_uv tag (dest_odd p a t)) (Or.inr (Or.inl ?_))
  obtain h | h | h := unitC0_cases p a <;> simp only [destU, inCol, h] <;> omega

/-- **The entry footprint from copy `t` is far from the reflector of the input corner of every
copy `t' ≥ 0` of the same unit** (image `1`; for the idle pieces of the machine). -/
theorem entryFoot_far_slab' (p : Program) (a t : ℕ) {t' : ℤ} (ht' : 0 ≤ t') (tag : CTag) :
    FarApart 2 (entryFoot p a t)
      (cornerSpec ⟨1, destU p a t', destV p t', tag⟩).piece.box := by
  rw [PSpec.piece_box]
  refine entryFoot_far p a t (slab_uv tag (dest_odd p a t')) (Or.inr (Or.inl ?_))
  obtain h | h | h := unitC0_cases p a <;> simp only [destU, inCol, h] <;> omega

/-! ### Band corners, module pieces, INC port corners -/

/-- **A corner of the band** (`v ≥ V_T + 660`) is far from every entry footprint. -/
theorem entryFoot_far_band (p : Program) (a t : ℕ) {c : Corner} (hv : VT p + 660 ≤ c.v) :
    FarApart 2 (entryFoot p a t) (cornerSpec c).piece.box := by
  rw [PSpec.piece_box]
  refine entryFoot_far p a t (corner_uv c) (Or.inr (Or.inr (Or.inl ?_)))
  unfold VU
  omega

/-- The right end of an entry footprint of a used unit is `≥ 139` left of the left end of every
module. -/
theorem entry_module_gap (p : Program) {a r t : ℕ} (ha : (a : ℤ) ≤ N p + R p - 1)
    (ht : (t : ℤ) < 2 * P p) :
    A p a + 96 + 29 * t + 139 + 248 * D p ≤ U p r - 823 := by
  have h := unit_module_gap p (a := a) (r := r) ⟨by omega, ha⟩ (by omega)
  have hR := slabR_ge_rs p
  unfold modLeft at h
  omega

/-- **A piece of a module** is far from the entry footprint of every used unit. -/
theorem entryFoot_far_module (p : Program) {a r t : ℕ} (ha : (a : ℤ) ≤ N p + R p - 1)
    (ht : (t : ℤ) < 2 * P p) {s : PSpec} (hs : s ∈ moduleSpecs p r) :
    FarApart 2 (entryFoot p a t) s.piece.box := by
  rw [PSpec.piece_box]
  refine entryFoot_far p a t (moduleSpecs_uv p r hs).1 (Or.inl ?_)
  have := entry_module_gap p (r := r) ha ht
  have := one_le_D p
  omega

/-- **The INC port corner of a module** (column `U_r + incChan`) is far from the entry footprint
of every used unit. -/
theorem entryFoot_far_left (p : Program) {a r t : ℕ} (ha : (a : ℤ) ≤ N p + R p - 1)
    (ht : (t : ℤ) < 2 * P p) (k : ℕ) (v : ℤ) (tag : CTag) :
    FarApart 2 (entryFoot p a t) (cornerSpec ⟨k, U p r + incChan p, v, tag⟩).piece.box := by
  rw [PSpec.piece_box]
  refine entryFoot_far p a t (corner_uv _) (Or.inl ?_)
  have := entry_module_gap p (r := r) ha ht
  have := fixp_bounds (uL - 62 * (2 * D p)) (1 - incPortV % 2)
  have := one_le_D p
  simp only [incChan, leftChan, uL] at *
  omega

/-! ### The reflectors of a route -/

/-- **The reflectors of a route are the reflectors of its corners** (as boxes). -/
theorem route_piece_box {g : WL} {cs : List Corner} {h : Piece}
    (hh : h ∈ (route g cs).1.map PSpec.piece) : ∃ c ∈ cs, h.box = (cornerSpec c).piece.box := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  have hb : s.bx ∈ cs.map fun c => (cornerSpec c).bx := by
    rw [← route_bx g cs]
    exact List.mem_map_of_mem hs
  obtain ⟨c, hc, he⟩ := List.mem_map.1 hb
  exact ⟨c, hc, by rw [PSpec.piece_box, PSpec.piece_box, he]⟩

/-- **An up-going link** (band corners, then the input corner of copy `t` of unit `a`) is far
from the entry footprint of copy `t`, given its band corners. -/
theorem entryFoot_far_up (p : Program) (b s c H : ℤ) (a t : ℕ) (hb : 1 ≤ b) (hs : 0 ≤ s ∧ s ≤ 9)
    {k0 : ℕ} {g : WL} {h : Piece}
    (hh : h ∈ (route g (upCornersK k0 p b s c H a t)).1.map PSpec.piece) :
    FarApart 2 (entryFoot p a t) h.box := by
  obtain ⟨c', hc, he⟩ := route_piece_box hh
  rw [he]
  simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  have hv : ∀ c0, VT p + 660 * b + 62 * s ≤ trackOut p b s c0 ∧
      VT p + 660 * b + 62 * (9 - s) ≤ trackBack p b s c0 := by
    intro c0; unfold trackOut trackBack track; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact entryFoot_far_band p a t (by have := (hv c).1; simp only; nlinarith)
  · exact entryFoot_far_band p a t (by have := (hv c).1; simp only; nlinarith)
  · exact entryFoot_far_band p a t (by have := (hv c).2; simp only; nlinarith)
  · exact entryFoot_far_band p a t (by have := (hv c).2; simp only; nlinarith)
  · exact entryFoot_far_slab p a t _

/-! ### The two fields of `IncSep` -/

/-- The entry copy of the continue is a natural number `< 2P`. -/
theorem incTc_range {p : Program} {i r : ℕ} (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    0 ≤ incTc p i ∧ incTc p i < 2 * P p := by
  have hi1 := succ_lt_of_inc hp hins
  have h := copyIdx_range p (C0 := unitC0 p (i + 1)) (c := incCc p i)
    (e := predIdx p (i + 1) i 0)
    ⟨predIdx_nonneg _ _ _ _, predIdx_lt_P p hins (by simp [predContrib]) (by omega)⟩
  exact ⟨h.1, h.2.1⟩

/-- The entry copy of the INC link is a natural number `< 2P`. -/
theorem incTl_range {p : Program} {i r : ℕ} (hins : p[i]? = some (.inc r)) :
    0 ≤ incTl p i r ∧ incTl p i r < 2 * P p := by
  have hr := lt_numRegs_of_inc hins
  have h := copyIdx_range p (C0 := C0halt) (c := incCl p i)
    (e := predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0))
    ⟨predIdx_nonneg _ _ _ _, predIdx_lt_P p hins (by simp [predContrib]) (by omega)⟩
  exact ⟨h.1, h.2.1⟩

/-- **`IncSep.entC` for every well-formed program**: the entry footprint of unit `i + 1` is far
from the reflectors of the continue (its band corners and the input corner of its entry copy). -/
theorem incPlan_entC {p : Program} {i r : ℕ} (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ h ∈ (incPlan p i r).LCraw, h ∉ chainPieces p (i + 1) (incPlan p i r).tc →
      FarApart 2 (entryFoot p (i + 1) (incPlan p i r).tc) h.box := by
  intro h hh hn
  simp only [IncPlan.LCraw, List.mem_append] at hh
  rcases hh with hh | hh
  · obtain ⟨t, ht⟩ : ∃ t : ℕ, incTc p i = t :=
      ⟨(incTc p i).toNat, by have := (incTc_range hp hins).1; omega⟩
    change h ∈ (route (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r))).1.map
      PSpec.piece at hh
    simp only [incMkc, upCorners, ht] at hh
    change FarApart 2 (entryFoot p (i + 1) (incTc p i).toNat) h.box
    rw [ht, Int.toNat_natCast]
    exact entryFoot_far_up p _ _ _ _ (i + 1) t (by unfold instrBand; omega) (by norm_num) hh
  · exact absurd hh hn

/-- **`IncSep.entR` for every well-formed program**: the entry footprint of the merge unit
`N + r` is far from the reflectors of the INC link (its band corners and the input corner of its
entry copy, the corner of the former defect), from the reflectors of the merge link (band corners
and the INC port corner of module `r`), and from the INC gate, `RF_J` and the register circuit of
module `r`. -/
theorem incPlan_entR {p : Program} {i r : ℕ} (hins : p[i]? = some (.inc r)) :
    ∀ h ∈ (incPlan p i r).LIraw, h ∉ chainPieces p (mergeUnit p r) (incPlan p i r).tl →
      FarApart 2 (entryFoot p (mergeUnit p r) (incPlan p i r).tl) h.box := by
  intro h hh hn
  have hr := lt_numRegs_of_inc hins
  have hrange := incTl_range hins
  obtain ⟨t, ht⟩ : ∃ t : ℕ, incTl p i r = t := ⟨(incTl p i r).toNat, by omega⟩
  have htl : (incPlan p i r).tl = t := by
    change (incTl p i r).toNat = t
    rw [ht, Int.toNat_natCast]
  rw [htl] at hn ⊢
  rw [ht] at hrange
  have ha : ((mergeUnit p r : ℕ) : ℤ) ≤ N p + R p - 1 := by
    unfold N R mergeUnit; push_cast; omega
  simp only [IncPlan.LIraw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with (((hh | hh) | hh) | hh | hh) | hh
  · change h ∈ (route (unitWL p i incRWL) (incMkl p i r (incEl p i r))).1.map PSpec.piece at hh
    simp only [incMkl, upCorners, ht] at hh
    exact entryFoot_far_up p _ _ _ _ (mergeUnit p r) t (by unfold instrBand; omega)
      (by norm_num) hh
  · rw [htl] at hh
    exact absurd hh hn
  · obtain ⟨c', hc, he⟩ := route_piece_box hh
    rw [he]
    change c' ∈ mergeCorners p r (mergeE p r) at hc
    simp only [mergeCorners, downCorners, bandCorners, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    have hv : ∀ c0, VT p + 660 ≤ trackOut p (mergeBand p r) 0 c0 ∧
        VT p + 660 ≤ trackBack p (mergeBand p r) 0 c0 := by
      intro c0; unfold trackOut trackBack track mergeBand N; omega
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact entryFoot_far_band p _ t (hv _).1
    · exact entryFoot_far_band p _ t (hv _).1
    · exact entryFoot_far_band p _ t (hv _).2
    · exact entryFoot_far_band p _ t (hv _).2
    · exact entryFoot_far_left p ha hrange.2 _ _ _
  · subst hh
    exact entryFoot_far_module p ha hrange.2 (s := incGateSpec p r) (mem_moduleSpecs_head
      (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · subst hh
    exact entryFoot_far_module p ha hrange.2
      (mem_moduleSpecs_head (List.mem_append_right _ List.mem_cons_self))
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
    exact entryFoot_far_module p ha hrange.2 (mem_moduleSpecs_head (List.mem_append_left _ hs))

end LP

end LeanTheory.Life
