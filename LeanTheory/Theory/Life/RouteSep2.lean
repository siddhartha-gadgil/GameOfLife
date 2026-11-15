/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RouteSep

/-!
# Descriptions of the corners of the machine: columns and owners

`R-31` #13: every corner of a route lies at (own column, own track). For the separation of the
column legs of the routes this module describes **every** corner of the machine (`Desc`):

* its valid place (`Valid`, `LayoutPieces`);
* for a corner on a column of the band (tag `band b k false`): its column (`ColDesc`) — a source
  column in the slab of unit `b - 1`, the input column of an entry copy, a channel of the left
  zone or a channel of the right zone of a module — and, for the last three, the owner of the
  place at the end of that column (`Owns`): the sub-band of the link;
* for a port corner of a left zone: its port line (`LeftPort`);
* for a halt corner: its unit is a `halt` instruction.

`owns_unique`: a place at the end of a column has one owner, so two links of distinct sub-bands
never share a destination column. `allCorners_split`: a statement about the corners of the
machine follows from the corners of one instruction (or merge link) and the described corners of
the other sub-bands.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Owners and descriptions -/

/-- The place `τ` is owned by the links of sub-band `b`: by instruction `b - 1` or by the merge
link of register `b - 1 - N`. -/
def Owns (p : Program) (b : ℤ) (τ : CTag) : Prop :=
  (∃ i : ℕ, b = 1 + (i : ℤ) ∧ TagOf p i τ) ∨ (∃ r : ℕ, b = 1 + N p + (r : ℤ) ∧ TagOfM p r τ)

/-- The column `u` of a corner of sub-band `b`: a source column in the slab of unit `b - 1`, the
input column of an entry copy, a left-zone channel or a right-zone channel (of caller `j`),
with the owner of the place at its end. -/
def ColDesc (p : Program) (b u : ℤ) : Prop :=
  (∃ a : ℕ, b = 1 + (a : ℤ) ∧ A p a + unitC0 p a + 81 ≤ u ∧ u ≤ A p a + 188) ∨
  (∃ (a : ℕ) (t : ℤ), (a : ℤ) < N p + R p ∧ 0 ≤ t ∧ t < 2 * P p ∧ u = destU p a t ∧
    Owns p b (.slab a t)) ∨
  (∃ (r : ℕ) (idx : ℤ), (r : ℤ) < R p ∧ 0 ≤ idx ∧ idx ≤ 4 * D p ∧
    U p r - 794 - 62 * idx ≤ u ∧ u ≤ U p r - 793 - 62 * idx ∧ Owns p b (.left r idx)) ∨
  (∃ (r : ℕ) (j : ℤ), (r : ℤ) < R p ∧ 0 ≤ j ∧ j < D p ∧
    U p r + uR p - 1 + 124 * (D p - 1 - j) ≤ u ∧ u ≤ U p r + uR p + 62 + 124 * (D p - 1 - j) ∧
    Owns p b (.right r j 0))

/-- The port line of the left-zone channel `idx`: DEC copy, INC, NZ token, NZ answer. -/
def LeftPort (p : Program) (idx v : ℤ) : Prop :=
  (0 ≤ idx ∧ idx < 2 * D p ∧ v = decPortV p idx) ∨ (idx = 2 * D p ∧ v = incPortV) ∨
  (∃ j : ℤ, 0 ≤ j ∧ j < D p ∧ idx = 2 * D p + 1 + 2 * j ∧ v = nzTokPortV j) ∨
  (∃ j : ℤ, 0 ≤ j ∧ j < D p ∧ idx = 2 * D p + 2 + 2 * j ∧ v = nzAnsPortV j)

/-- **The description of a corner of the machine.** -/
def Desc (p : Program) (c : Corner) : Prop :=
  Valid p c ∧ (∀ b k, c.tag = .band b k false → ColDesc p b c.u) ∧
    (∀ a, c.tag = .halt a → p[a.toNat]? = some .halt) ∧
    (∀ r idx, c.tag = .left r idx → LeftPort p idx c.v)

/-- An instruction owning a slab, left or right place is an instruction of the program. -/
theorem TagOf_lt {p : Program} {i : ℕ} {τ : CTag} (h : TagOf p i τ)
    (hτ : (∀ b k h, τ ≠ .band b k h) ∧ ∀ a, τ ≠ .halt a) : i < p.length := by
  cases τ with
  | band b k hb => exact absurd rfl (hτ.1 b k hb)
  | halt a => exact absurd rfl (hτ.2 a)
  | slab a t =>
    obtain ⟨ins, -, -, -, hi, -⟩ := h
    exact (List.getElem?_eq_some_iff.1 hi).1
  | left r idx =>
    obtain ⟨z, r', -, hi, -⟩ := h
    exact (List.getElem?_eq_some_iff.1 hi).1
  | right r j w =>
    obtain ⟨z, r', -, hi, -⟩ := h
    exact (List.getElem?_eq_some_iff.1 hi).1

/-- **A slab, left or right place has one owning sub-band.** -/
theorem owns_unique {p : Program} {b b' : ℤ} {τ : CTag}
    (hτ : (∀ b k h, τ ≠ .band b k h) ∧ ∀ a, τ ≠ .halt a) (h : Owns p b τ) (h' : Owns p b' τ) :
    b = b' := by
  rcases h with ⟨i, rfl, hi⟩ | ⟨r, rfl, hr⟩ <;> rcases h' with ⟨i', rfl, hi'⟩ | ⟨r', rfl, hr'⟩
  · rw [TagOf_unique p hi hi']
  · exact (TagOf_not_M p (TagOf_lt hi hτ) hi hr').elim
  · exact (TagOf_not_M p (TagOf_lt hi' hτ) hi' hr).elim
  · rw [TagOfM_unique p hr hr']

/-- The owner of a right place does not depend on the corner number `w`. -/
theorem owns_right {p : Program} {b r j : ℤ} {w : ℕ} (h : Owns p b (.right r j w)) (w' : ℕ) :
    Owns p b (.right r j w') := by
  rcases h with ⟨i, hb, hi⟩ | ⟨r', hb, hr⟩
  · exact Or.inl ⟨i, hb, hi⟩
  · exact (hr : False).elim

/-- An instruction owns its places for its sub-band. -/
theorem owns_of_tagOf {p : Program} {i : ℕ} {τ : CTag} (h : TagOf p i τ) :
    Owns p (1 + (i : ℤ)) τ := Or.inl ⟨i, rfl, h⟩

/-- A band tag owned by sub-band `b` is a tag of sub-band `b`. -/
theorem owns_band {p : Program} {b b' k : ℤ} {h : Bool} (ho : Owns p b (.band b' k h)) :
    b' = b := by
  rcases ho with ⟨i, hb, hi⟩ | ⟨r, hb, hr⟩
  · simp only [TagOf] at hi; omega
  · simp only [TagOfM] at hr; omega

/-! ### Descriptions of the corners of the links -/

/-- **The corners of a link up to an entry copy are described**, given the column of its first
corner. -/
theorem upLink_desc {p : Program} {k0 : ℕ} {b s c H t : ℤ} {a : ℕ}
    (hall : ∀ x ∈ upCornersK k0 p b s c H a t, Valid p x ∧ Owns p b x.tag)
    (hsrc : ColDesc p b c) : ∀ x ∈ upCornersK k0 p b s c H a t, Desc p x := by
  have hslab := hall ⟨1, destU p a t, destV p t, .slab a t⟩ (by simp [upCornersK])
  simp only [Valid] at hslab
  obtain ⟨⟨-, hN, ht0, ht1, -, -⟩, hown⟩ := hslab
  intro x hx
  refine ⟨(hall x hx).1, ?_, ?_, ?_⟩
  · intro b' k' h
    simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [CTag.band.injEq] at h
    · rw [← h.1]; exact hsrc
    · simp at h
    · simp at h
    · rw [← h.1]
      exact Or.inr (Or.inl ⟨a, t, hN, ht0, ht1, rfl, hown⟩)
    · simp at h
  · intro a' h
    simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp at h
  · intro r idx h
    simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp at h

/-- Membership in the corners of a down-going link. -/
theorem mem_downCorners {p : Program} {b s c H cd vp : ℤ} {r : ℕ} {idx : ℤ} {x : Corner} :
    x ∈ downCorners p b s c H cd vp r idx ↔
      x = ⟨3, c, trackOut p b s c, .band b s false⟩ ∨ x = ⟨7, H, trackOut p b s c, .band b s true⟩ ∨
      x = ⟨4, H, trackBack p b s c, .band b (9 - s) true⟩ ∨
      x = ⟨2, cd, trackBack p b s c, .band b (9 - s) false⟩ ∨ x = ⟨4, cd, vp, .left r idx⟩ := by
  simp [downCorners, bandCorners]

/-- **The corners of a link down to a left-zone port are described**, given the column of its
first corner and the port line. -/
theorem downLink_desc {p : Program} {b s c H cd vp : ℤ} {r : ℕ} {idx : ℤ}
    (hall : ∀ x ∈ downCorners p b s c H cd vp r idx, Valid p x ∧ Owns p b x.tag)
    (hsrc : ColDesc p b c) (hport : LeftPort p idx vp) :
    ∀ x ∈ downCorners p b s c H cd vp r idx, Desc p x := by
  have hl := hall ⟨4, cd, vp, .left r idx⟩ (mem_downCorners.2 (by simp))
  simp only [Valid] at hl
  obtain ⟨⟨-, hR, hi0, hi1, hu0, hu1, -, -⟩, hown⟩ := hl
  intro x hx
  refine ⟨(hall x hx).1, ?_, ?_, ?_⟩
  · intro b' k' h
    rcases mem_downCorners.1 hx with rfl | rfl | rfl | rfl | rfl <;>
      simp only [CTag.band.injEq, reduceCtorEq] at h
    · rw [← h.1]; exact hsrc
    · simp at h
    · simp at h
    · rw [← h.1]
      exact Or.inr (Or.inr (Or.inl ⟨r, idx, hR, hi0, hi1, hu0, hu1, hown⟩))
  · intro a' h
    rcases mem_downCorners.1 hx with rfl | rfl | rfl | rfl | rfl <;> simp at h
  · intro r' idx' h
    rcases mem_downCorners.1 hx with rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq, CTag.left.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hport

/-- Membership in the corners of the KZ link. -/
theorem mem_ztokCorners {p : Program} {b c H : ℤ} {r : ℕ} {j : ℤ} {x : Corner} :
    x ∈ ztokCorners p b c H r j ↔
      x = ⟨3, c, trackOut p b 2 c, .band b 2 false⟩ ∨ x = ⟨7, H, trackOut p b 2 c, .band b 2 true⟩ ∨
      x = ⟨4, H, trackBack p b 2 c, .band b (9 - 2) true⟩ ∨
      x = ⟨2, U p r + zTokChan p j, trackBack p b 2 c, .band b (9 - 2) false⟩ ∨
      x = ⟨3, U p r + zTokChan p j, zTokDepth p j, .right r j 2⟩ ∨
      x = ⟨0, U p r + zTokStation j, zTokDepth p j, .right r j 3⟩ := by
  simp [ztokCorners, bandCorners]

/-- **The corners of the KZ link are described**, given the column of its first corner. -/
theorem ztok_desc {p : Program} {b c H : ℤ} {r : ℕ} {j : ℤ}
    (hall : ∀ x ∈ ztokCorners p b c H r j, Valid p x ∧ Owns p b x.tag)
    (hsrc : ColDesc p b c) : ∀ x ∈ ztokCorners p b c H r j, Desc p x := by
  have hl := hall ⟨3, U p r + zTokChan p j, zTokDepth p j, .right r j 2⟩
    (mem_ztokCorners.2 (by simp))
  simp only [Valid] at hl
  obtain ⟨⟨-, hR, hj0, hj1, hw⟩, hown⟩ := hl
  have hu : U p r + uR p - 1 + 124 * (D p - 1 - j) ≤ U p r + zTokChan p j ∧
      U p r + zTokChan p j ≤ U p r + uR p + 62 + 124 * (D p - 1 - j) := by
    unfold uR; omega
  intro x hx
  refine ⟨(hall x hx).1, ?_, ?_, ?_⟩
  · intro b' k' h
    rcases mem_ztokCorners.1 hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [CTag.band.injEq, reduceCtorEq] at h
    · rw [← h.1]; exact hsrc
    · simp at h
    · simp at h
    · rw [← h.1]
      exact Or.inr (Or.inr (Or.inr ⟨r, j, hR, hj0, hj1, hu.1, hu.2, owns_right hown 0⟩))
  · intro a' h
    rcases mem_ztokCorners.1 hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h
  · intro r' idx' h
    rcases mem_ztokCorners.1 hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h

/-- **The corners of the NZ answer are described** (its source is the NZ answer channel). -/
theorem nzAns_desc {p : Program} {b : ℤ} {r : ℕ} {j H t : ℤ} {a : ℕ}
    (hall : ∀ x ∈ nzAnsCorners p b r j H a t, Valid p x ∧ Owns p b x.tag)
    (hj : 0 ≤ j ∧ j < D p) : ∀ x ∈ nzAnsCorners p b r j H a t, Desc p x := by
  have hl := hall ⟨0, U p r + nzAnsChan p j, nzAnsPortV j, .left r (2 * D p + 2 + 2 * j)⟩
    (by simp [nzAnsCorners])
  simp only [Valid] at hl
  obtain ⟨⟨-, hR, hi0, hi1, hu0, hu1, -, -⟩, hown⟩ := hl
  have hsrc : ColDesc p b (U p r + nzAnsChan p j) :=
    Or.inr (Or.inr (Or.inl ⟨r, _, hR, hi0, hi1, hu0, hu1, hown⟩))
  have hup := upLink_desc (fun x hx => hall x (List.mem_cons_of_mem _ hx)) hsrc
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · refine ⟨(hall _ List.mem_cons_self).1, ?_, ?_, ?_⟩
    · intro b' k' h; simp at h
    · intro a' h; simp at h
    · intro r' idx' h
      simp only [CTag.left.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr ⟨j, hj.1, hj.2, rfl, rfl⟩))
  · exact hup x hx

/-- **The corners of the Z answer are described** (its source is the Z answer channel). -/
theorem zAns_desc {p : Program} {b : ℤ} {r : ℕ} {j H t : ℤ} {a : ℕ}
    (hall : ∀ x ∈ zAnsCorners p b r j H a t, Valid p x ∧ Owns p b x.tag) :
    ∀ x ∈ zAnsCorners p b r j H a t, Desc p x := by
  have hl := hall ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩ (by simp [zAnsCorners])
  simp only [Valid] at hl
  obtain ⟨⟨-, hR, hj0, hj1, hw⟩, hown⟩ := hl
  have hu : U p r + uR p - 1 + 124 * (D p - 1 - j) ≤ U p r + zAnsChan p j ∧
      U p r + zAnsChan p j ≤ U p r + uR p + 62 + 124 * (D p - 1 - j) := by
    unfold uR; omega
  have hsrc : ColDesc p b (U p r + zAnsChan p j) :=
    Or.inr (Or.inr (Or.inr ⟨r, j, hR, hj0, hj1, hu.1, hu.2, owns_right hown 0⟩))
  have hup := upLink_desc (fun x hx => hall x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
    hsrc
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · refine ⟨(hall _ List.mem_cons_self).1, ?_, ?_, ?_⟩ <;> intros <;> simp_all
  rcases List.mem_cons.1 hx with rfl | hx
  · refine ⟨(hall _ (List.mem_cons_of_mem _ List.mem_cons_self)).1, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all
  · exact hup x hx

/-- `C0` of the unit of an `inc` instruction. -/
theorem unitC0_inc {p : Program} {i r : ℕ} (hi : p[i]? = some (.inc r)) : unitC0 p i = C0inc := by
  simp [unitC0, unitKind, hi, UKind.C0]

/-- `C0` of the unit of a `decJz` instruction. -/
theorem unitC0_dec {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    unitC0 p i = C0dec := by
  simp [unitC0, unitKind, hi, UKind.C0]

/-- A source column of unit `i` in sub-band `1 + i`. -/
theorem colDesc_src (p : Program) (i : ℕ) {w : ℤ} (h1 : unitC0 p i + 81 ≤ w) (h2 : w ≤ 188) :
    ColDesc p (instrBand i) (A p i + w) :=
  Or.inl ⟨i, rfl, by omega, by omega⟩

/-- **Every corner of instruction `i` is described.** -/
theorem instrCorners_desc {p : Program} (hp : p.WellFormed) {i : ℕ} (hi : i < p.length) :
    ∀ c ∈ instrCorners p i, Desc p c := by
  have hv := instrCorners_valid hp hi
  have hall : ∀ c ∈ instrCorners p i, Valid p c ∧ Owns p (instrBand i) c.tag :=
    fun c hc => ⟨(hv c hc).1, owns_of_tagOf (hv c hc).2⟩
  obtain ⟨ins, hins⟩ : ∃ ins, p[i]? = some ins := ⟨_, List.getElem?_eq_getElem hi⟩
  cases ins with
  | halt =>
    intro c hc
    have hc' := hc
    rw [instrCorners_halt hins] at hc'
    simp only [haltCorners, List.mem_cons, List.not_mem_nil, or_false] at hc'
    subst hc'
    refine ⟨(hv _ hc).1, ?_, ?_, ?_⟩
    · intro b k h; simp at h
    · intro a h
      simp only [CTag.halt.injEq] at h
      subst h
      simpa using hins
    · intro r idx h; simp at h
  | inc r =>
    obtain ⟨G, ec, el, -, -, -, -, -, heq⟩ := instrCorners_inc hins
    have hC := unitC0_inc hins
    rw [heq] at hall ⊢
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact upLink_desc (fun x hx => hall x (List.mem_append_left _ hx))
        (colDesc_src p i (by rw [hC]; simp [C0inc, incD]) (by simp [incD])) c hc
    · exact upLink_desc (fun x hx => hall x (List.mem_append_right _ hx))
        (colDesc_src p i (by rw [hC]; simp [C0inc, incR]) (by simp [incR])) c hc
  | decJz r z =>
    obtain ⟨eA, eB, -, -, -, -, heq⟩ := instrCorners_dec hins
    have hC := unitC0_dec hins
    have hj := callerIdx_lt_D p hins
    have hDe : D p = (numCallers p : ℤ) := rfl
    rw [heq] at hall ⊢
    intro c hc
    simp only [List.mem_append] at hc hall
    rcases hc with (((hc | hc) | hc) | hc) | hc
    · refine downLink_desc (fun x hx => hall x (Or.inl (Or.inl (Or.inl (Or.inl hx)))))
        (colDesc_src p i (by rw [hC]; simp [C0dec, decL]) (by simp [decL])) ?_ c hc
      exact Or.inr (Or.inr (Or.inl ⟨_, by omega, by omega, rfl, rfl⟩))
    · refine downLink_desc (fun x hx => hall x (Or.inl (Or.inl (Or.inl (Or.inr hx)))))
        (colDesc_src p i (by rw [hC]; simp [C0dec, decR]) (by simp [decR])) ?_ c hc
      exact Or.inl ⟨by omega, by omega, rfl⟩
    · exact ztok_desc (fun x hx => hall x (Or.inl (Or.inl (Or.inr hx))))
        (colDesc_src p i (by rw [hC]; simp [C0dec, decD]) (by simp [decD])) c hc
    · exact nzAns_desc (fun x hx => hall x (Or.inl (Or.inr hx))) ⟨by omega, by omega⟩ c hc
    · exact zAns_desc (fun x hx => hall x (Or.inr hx)) c hc

/-- **Every corner of the merge link of register `r` is described.** -/
theorem mergeCorners_desc {p : Program} {r : ℕ} (hr : r < numRegs p) :
    ∀ c ∈ specCorners (mergeSpecs p r), Desc p c := by
  have hv := mergeCorners_valid p hr
  have hall : ∀ c ∈ specCorners (mergeSpecs p r), Valid p c ∧ Owns p (mergeBand p r) c.tag :=
    fun c hc => ⟨(hv c hc).1, Or.inr ⟨r, rfl, (hv c hc).2⟩⟩
  have hC := unitC0_merge p r
  simp only [specCorners, mergeSpecs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    mergeCorners] at hall ⊢
  refine downLink_desc hall (Or.inl ⟨p.length + r, ?_, ?_, ?_⟩) (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · unfold mergeBand N; push_cast; ring
  · rw [hC]; push_cast; simp only [C0halt, haltD]; omega
  · push_cast; simp only [haltD]; omega

/-- **A statement about the corners of the machine from the corners of instruction `i`** and the
described corners of the other sub-bands. -/
theorem allCorners_split {p : Program} (hp : p.WellFormed) {i : ℕ} (hi : i < p.length)
    {Q : Corner → Prop} (hown : ∀ c ∈ instrCorners p i, Q c)
    (hfor : ∀ c ∈ allCorners p, Desc p c → (∀ b k h, c.tag = .band b k h → b ≠ 1 + i) → Q c) :
    ∀ c ∈ allCorners p, Q c := by
  intro c hc
  have hc0 := hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨i', hi', hc⟩ := List.mem_flatMap.1 hc
    have hi'' := List.mem_range.1 hi'
    by_cases h : i' = i
    · subst h; exact hown c hc
    · refine hfor c hc0 (instrCorners_desc hp hi'' c hc) fun b k hb htag => ?_
      have := (instrCorners_valid hp hi'' c hc).2
      rw [htag] at this
      simp only [TagOf] at this
      omega
  · obtain ⟨r, hr, hc⟩ := List.mem_flatMap.1 hc
    have hr' := List.mem_range.1 (List.mem_filter.1 hr).1
    refine hfor c hc0 (mergeCorners_desc hr' c hc) fun b k hb htag => ?_
    have := (mergeCorners_valid p hr' c hc).2
    rw [htag] at this
    simp only [TagOfM, N] at this
    omega

/-- **A statement about the corners of the machine from the corners of the merge link of `r`**
and the described corners of the other sub-bands. -/
theorem allCorners_split_merge {p : Program} (hp : p.WellFormed) {r : ℕ}
    {Q : Corner → Prop} (hown : ∀ c ∈ specCorners (mergeSpecs p r), Q c)
    (hfor : ∀ c ∈ allCorners p, Desc p c → (∀ b k h, c.tag = .band b k h → b ≠ mergeBand p r) →
      Q c) :
    ∀ c ∈ allCorners p, Q c := by
  intro c hc
  have hc0 := hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨i', hi', hc⟩ := List.mem_flatMap.1 hc
    have hi'' := List.mem_range.1 hi'
    refine hfor c hc0 (instrCorners_desc hp hi'' c hc) fun b k hb htag => ?_
    have := (instrCorners_valid hp hi'' c hc).2
    rw [htag] at this
    simp only [TagOf] at this
    unfold mergeBand N; omega
  · obtain ⟨r', hr, hc⟩ := List.mem_flatMap.1 hc
    have hr' := List.mem_range.1 (List.mem_filter.1 hr).1
    by_cases h : r' = r
    · subst h; exact hown c hc
    · refine hfor c hc0 (mergeCorners_desc hr' c hc) fun b k hb htag => ?_
      have := (mergeCorners_valid p hr' c hc).2
      rw [htag] at this
      simp only [TagOfM] at this
      unfold mergeBand; omega

end LP

end LeanTheory.Life
