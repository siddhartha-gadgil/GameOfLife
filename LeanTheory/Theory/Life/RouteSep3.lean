/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RouteSep2

/-!
# Separation of the legs of the routes, by the region they cross

Every leg of a route of the layout `LP` is a segment of a column (`u` fixed) or of a track (`v`
fixed) between two corners; its glider boxes lie in a rectangle of `(u, v)` (`legOK_of`). This
module proves, for each kind of leg, that every unit piece, every module piece and the reflector
of every corner **of another sub-band** is far from the rectangle (`R-31` #13 and the checks (C)):

* `track_corner`, `band_unit`, `band_module`: the legs on the tracks of a sub-band (`OUT`, `BACK`);
* `hair_corner`: the hairpin columns;
* `src_corner`, `src_unit_other`, `slab_module`: the source columns of the units, down to the band;
* `dst_corner`, `dst_unit`: the input columns of the entry copies, up from the band;
* `left_corner`, `left_unit`, `left_module`: the channels of the left zones;
* `right_corner`, `right_unit`, `right_module`: the channels of the right zones;
* `rzone_corner`, `rzone_module`: the depth lines of the right zones.

The corners of the own sub-band of the leg are checked for each link from its explicit corner
list (`RouteSep4`, `RouteSep5`). Only the descriptions `Desc` of the corners are used: the owner
of the place at the end of a column (`owns_unique`) rules out a foreign corner on the column of
the leg.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Global inequalities -/

/-- Units are left of every module, with a gap of `120`. -/
theorem unit_module_gap (p : Program) {a r : ℤ} (ha : 0 ≤ a ∧ a ≤ N p + R p - 1) (hr : 0 ≤ r) :
    A p a + slabR p + 120 ≤ U p r + modLeft p := by
  have h6 := (sep06_units_module0 p ha.2).1
  have hU := (U_ge p hr).1
  omega

/-- The right end of a module (its pieces and zones) is `≥ 199` left of the left end of the
next one. -/
theorem module_gap (p : Program) {r r' : ℤ} (h : r < r') :
    U p r + modRight p + 199 ≤ U p r' + modLeft p := by
  have := U_add_le p h
  have := one_le_D p
  unfold PM modRight modLeft at *; omega

/-- `slabR` bounds. -/
theorem slabR_ge_rs (p : Program) : 238 ≤ slabR p ∧ 86 + 58 * P p ≤ slabR p := by
  unfold slabR; omega

/-! ### Tracks of the band -/

/-- **A leg on a track**: the reflector of every corner whose place is not on the track `(b, k)`
is far from the rectangle of the leg (only its two corners are on the track). -/
theorem track_corner {p : Program} {b k V u1 u2 : ℤ} (hb : 1 ≤ b ∧ b ≤ N p + R p)
    (hk : 0 ≤ k ∧ k ≤ 9) (hV : VT p + 660 * b + 62 * k ≤ V ∧ V ≤ VT p + 660 * b + 62 * k + 1)
    {c : Corner} (hv : Valid p c) (h1 : c.tag ≠ .band b k true) (h2 : c.tag ≠ .band b k false) :
    FarRect (cornerSpec c).bx u1 u2 (V - 2) (V + 6) := by
  have hf := layout_facts p
  refine corner_farRect ?_
  obtain ⟨k', u, v, tag⟩ := c
  simp only at h1 h2 ⊢
  cases tag with
  | band b' n h =>
    simp only [Valid] at hv
    simp only [ne_eq, CTag.band.injEq, not_and] at h1 h2
    rcases lt_trichotomy b' b with hb' | rfl | hb'
    · omega
    · rcases lt_trichotomy n k with hn | rfl | hn
      · omega
      · cases h <;> simp at h1 h2
      · omega
    · omega
  | halt a => simp only [Valid] at hv; omega
  | slab a t => simp only [Valid] at hv; omega
  | left r idx => simp only [Valid] at hv; omega
  | right r j w => simp only [Valid] at hv; omega

/-- A rectangle in the band is far from every unit piece. -/
theorem band_unit {p : Program} {u1 u2 v1 v2 : ℤ} (hv1 : VT p + 600 ≤ v1) :
    ∀ a s, a < p.length + numRegs p → s ∈ unitSpecs p a → FarRect s.bx u1 u2 v1 v2 := by
  intro a s _ hs
  have h := unitSpecs_uv p a hs
  have hf := layout_facts p
  exact farRect_of_uv h (Or.inr (Or.inr (Or.inl (by omega))))

/-- A rectangle in the band is far from every module piece. -/
theorem band_module {p : Program} {u1 u2 v1 v2 : ℤ} (hv2 : v2 ≤ VT p + 660 * (N p + R p) + 600) :
    ∀ r s, r < numRegs p → s ∈ moduleSpecs p r → FarRect s.bx u1 u2 v1 v2 := by
  intro r s _ hs
  have h := (moduleSpecs_uv p r hs).1
  have hf := layout_facts p
  exact farRect_of_uv h (Or.inr (Or.inr (Or.inr (by omega))))

/-! ### Hairpin columns -/

/-- **A leg on a hairpin column** of sub-band `b` (any `u`): the reflector of every corner of
another sub-band is far from its rectangle (in `v`). -/
theorem hair_corner {p : Program} {b H v1 v2 : ℤ} (hb : 1 ≤ b ∧ b ≤ N p + R p)
    (hv : VT p + 660 * b ≤ v1 ∧ v2 ≤ VT p + 660 * b + 570) {c : Corner} (hd : Desc p c)
    (hband : ∀ b' k h, c.tag = .band b' k h → b' ≠ b) :
    FarRect (cornerSpec c).bx (H - 4) (H + 4) v1 v2 := by
  have hf := layout_facts p
  refine corner_farRect ?_
  obtain ⟨hv', -, -, -⟩ := hd
  obtain ⟨k', u, v, tag⟩ := c
  simp only at hband ⊢
  cases tag with
  | band b' n h =>
    simp only [Valid] at hv'
    have := hband b' n h rfl
    rcases lt_or_gt_of_ne this with hb' | hb' <;> omega
  | halt a => simp only [Valid] at hv'; omega
  | slab a t => simp only [Valid] at hv'; omega
  | left r idx => simp only [Valid] at hv'; omega
  | right r j w => simp only [Valid] at hv'; omega

/-! ### Source columns of the units -/

/-- **A leg on a source column** of unit `a` (column `A_a + w`, sub-band `b = 1 + a`, down to the
band): the reflector of every corner of another sub-band is far from its rectangle. -/
theorem src_corner {p : Program} {a : ℕ} {b w v1 v2 : ℤ} (hb : b = 1 + (a : ℤ))
    (ha : (a : ℤ) < N p + R p) (hw : unitC0 p a + 81 ≤ w ∧ w ≤ 188)
    (hnh : ∀ x : ℕ, p[x]? = some .halt → x ≠ a) (hv2 : v2 ≤ VT p + 660 * b + 570)
    {c : Corner} (hd : Desc p c) (hband : ∀ b' k h, c.tag = .band b' k h → b' ≠ b) :
    FarRect (cornerSpec c).bx (A p a + w - 4) (A p a + w + 4) v1 v2 := by
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have hc0 := unitC0_cases p a
  refine corner_farRect ?_
  obtain ⟨hv, hcol, hhalt, -⟩ := hd
  obtain ⟨k', u, v, tag⟩ := c
  simp only at hband hcol hhalt ⊢
  cases tag with
  | band b' n h =>
    simp only [Valid] at hv
    obtain ⟨hv1, hv2', hv3, hv4, hv5, hv6, hv7, hv8⟩ := hv
    have hne := hband b' n h rfl
    rcases lt_or_gt_of_ne hne with hb' | hb'
    · cases h
      · rcases hcol b' n rfl with ⟨a', rfl, h1, h2⟩ | ⟨a', t', h0, ht0, ht1, rfl, -⟩ |
          ⟨r, idx, hr, hi0, hi1, hu0, hu1, -⟩ | ⟨r, j, hr, hj0, hj1, hu0, hu1, -⟩
        · have hc0' := unitC0_cases p a'
          rcases lt_trichotomy (a' : ℤ) a with h | h | h
          · have := A_add_le p h; omega
          · omega
          · have := A_add_le p h; omega
        · have hc0' := unitC0_cases p a'
          simp only [destU, inCol] at *
          rcases lt_trichotomy (a' : ℤ) a with h | h | h
          · have := A_add_le p h; omega
          · have h' : a' = a := by omega
            subst h'; omega
          · have := A_add_le p h; omega
        · have := unit_module_gap p (a := a) (r := r) ⟨by omega, by omega⟩ (by omega)
          unfold modLeft at this; omega
        · have := unit_module_gap p (a := a) (r := r) ⟨by omega, by omega⟩ (by omega)
          unfold modLeft uR at *; omega
      · have := A_nonneg p (a := a) (by omega)
        have := hv7 rfl
        omega
    · omega
  | halt a' =>
    simp only [Valid] at hv
    have hne : a'.toNat ≠ a := hnh a'.toNat (hhalt a' rfl)
    rcases lt_or_gt_of_ne hne with h | h
    · have := A_add_le p (a := a') (a' := a) (by omega); omega
    · have := A_add_le p (a := a) (a' := a') (by omega); omega
  | slab a' t =>
    simp only [Valid] at hv
    have hc0' := unitC0_cases p a'.toNat
    rcases lt_trichotomy a' a with h | h | h
    · have := A_add_le p h; omega
    · have h' : a'.toNat = a := by omega
      rw [h'] at hv; subst h; omega
    · have := A_add_le p h; omega
  | left r idx =>
    simp only [Valid] at hv
    have := unit_module_gap p (a := a) (r := r) ⟨by omega, by omega⟩ (by omega)
    unfold modLeft at this; omega
  | right r j w' =>
    simp only [Valid] at hv
    have := unit_module_gap p (a := a) (r := r) ⟨by omega, by omega⟩ (by omega)
    unfold modLeft at this; omega

/-- A rectangle on a column of unit `a` is far from the pieces of every other unit. -/
theorem slab_unit_other {p : Program} {a : ℕ} {u1 u2 v1 v2 : ℤ}
    (hu : A p a + slabL p + 26 ≤ u1 ∧ u2 ≤ A p a + slabR p - 26) :
    ∀ a' s, a' < p.length + numRegs p → a' ≠ a → s ∈ unitSpecs p a' →
      FarRect s.bx u1 u2 v1 v2 := by
  intro a' s _ hne hs
  have h := unitSpecs_uv p a' hs
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
  rcases lt_or_gt_of_ne hne with h' | h'
  · have := A_add_le p (a := a') (a' := a) (by exact_mod_cast h')
    exact farRect_of_uv h (Or.inl (by unfold slabR at *; omega))
  · have := A_add_le p (a := a) (a' := a') (by exact_mod_cast h')
    exact farRect_of_uv h (Or.inr (Or.inl (by unfold slabR at *; omega)))

/-- A rectangle on a column of a unit slab is far from every module piece. -/
theorem slab_module {p : Program} {a : ℕ} (ha : (a : ℤ) < N p + R p) {u1 u2 v1 v2 : ℤ}
    (hu : u2 ≤ A p a + slabR p) :
    ∀ r s, r < numRegs p → s ∈ moduleSpecs p r → FarRect s.bx u1 u2 v1 v2 := by
  intro r s _ hs
  have h := (moduleSpecs_uv p r hs).1
  have hf := layout_facts p
  have := unit_module_gap p (a := a) (r := r) ⟨by omega, by omega⟩ (by omega)
  exact farRect_of_uv h (Or.inr (Or.inl (by unfold modLeft at this; omega)))

/-! ### Input columns of the entry copies -/

/-- **A leg on the input column of entry copy `t` of unit `a`** (owned by sub-band `b`, up from
the band): the reflector of every corner of another sub-band, other than the input corner of
the copy, is far from its rectangle. -/
theorem dst_corner {p : Program} {a : ℕ} {t b v1 v2 : ℤ} (ha : (a : ℤ) < N p + R p)
    (ht : 0 ≤ t ∧ t < 2 * P p) (hown : Owns p b (.slab a t)) (hv2 : v2 ≤ VT p + 660 * b + 570)
    {c : Corner} (hd : Desc p c) (hband : ∀ b' k h, c.tag = .band b' k h → b' ≠ b)
    (hne : c.tag ≠ .slab a t) :
    FarRect (cornerSpec c).bx (destU p a t - 4) (destU p a t + 4) v1 v2 := by
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have hc0 := unitC0_cases p a
  have hA := A_nonneg p (a := a) (by omega)
  refine corner_farRect ?_
  obtain ⟨hv, hcol, hhalt, -⟩ := hd
  obtain ⟨k', u, v, tag⟩ := c
  simp only [destU, inCol] at hband hcol hhalt hne ⊢
  cases tag with
  | band b' n h =>
    simp only [Valid] at hv
    obtain ⟨hv1, hv2', hv3, hv4, hv5, hv6, hv7, hv8⟩ := hv
    have hne' := hband b' n h rfl
    rcases lt_or_gt_of_ne hne' with hb' | hb'
    · cases h
      · rcases hcol b' n rfl with ⟨a', rfl, h1, h2⟩ | ⟨a', t', h0, ht0, ht1, rfl, hown'⟩ |
          ⟨r, idx, hr, hi0, hi1, hu0, hu1, -⟩ | ⟨r, j, hr, hj0, hj1, hu0, hu1, -⟩
        · have hc0' := unitC0_cases p a'
          rcases lt_trichotomy (a' : ℤ) a with h | h | h
          · have := A_add_le p h; omega
          · have h' : a' = a := by omega
            subst h'; omega
          · have := A_add_le p h; omega
        · have hc0' := unitC0_cases p a'
          simp only [destU, inCol] at *
          rcases lt_trichotomy (a' : ℤ) a with h | h | h
          · have := A_add_le p h; omega
          · have h' : a' = a := by omega
            subst h'
            by_cases htt : t' = t
            · subst htt
              have := owns_unique (by simp) hown hown'
              omega
            · omega
          · have := A_add_le p h; omega
        · have := unit_module_gap p (a := a) (r := r) ⟨by omega, by omega⟩ (by omega)
          unfold modLeft at this; omega
        · have := unit_module_gap p (a := a) (r := r) ⟨by omega, by omega⟩ (by omega)
          unfold modLeft uR at *; omega
      · have := hv7 rfl
        omega
    · omega
  | halt a' =>
    simp only [Valid] at hv
    rcases lt_trichotomy a' a with h | h | h
    · have := A_add_le p h; omega
    · subst h; omega
    · have := A_add_le p h; omega
  | slab a' t' =>
    simp only [Valid] at hv
    have hc0' := unitC0_cases p a'.toNat
    rcases lt_trichotomy a' a with h | h | h
    · have := A_add_le p h; omega
    · have h' : a'.toNat = a := by omega
      rw [h'] at hv; subst h
      have : t' ≠ t := fun h'' => hne (by rw [h''])
      omega
    · have := A_add_le p h; omega
  | left r idx =>
    simp only [Valid] at hv
    have := unit_module_gap p (a := a) (r := r) ⟨by omega, by omega⟩ (by omega)
    unfold modLeft at this; omega
  | right r j w' =>
    simp only [Valid] at hv
    have := unit_module_gap p (a := a) (r := r) ⟨by omega, by omega⟩ (by omega)
    unfold modLeft at this; omega

/-- A rectangle on the input column of an entry copy of unit `a` is far from every piece of
unit `a` (the pieces are `≥ 35` right of the input columns). -/
theorem dst_unit_own {p : Program} {a : ℕ} {t v1 v2 : ℤ} (ht : 0 ≤ t) :
    ∀ s ∈ unitSpecs p a, FarRect s.bx (destU p a t - 4) (destU p a t + 4) v1 v2 := by
  intro s hs
  have h := unitSpecs_uv p a hs
  have := unitC0_uLo35 p a
  exact farRect_of_uv h (Or.inr (Or.inl (by unfold destU inCol; omega)))

/-! ### The zones of the modules -/

/-- A rectangle in the zones of a module is far from every unit piece. -/
theorem zone_unit {p : Program} {u1 u2 v1 v2 : ℤ} (hu : U0 p + modLeft p + 20 ≤ u1) :
    ∀ a s, a < p.length + numRegs p → s ∈ unitSpecs p a → FarRect s.bx u1 u2 v1 v2 := by
  intro a s ha hs
  have h := unitSpecs_uv p a hs
  have hR := slabR_ge_rs p
  have h6 := (sep06_units_module0 p (a := a) (by unfold N R; omega)).1
  exact farRect_of_uv h (Or.inl (by omega))

/-- A rectangle in the zones of module `r` is far from the pieces of every other module. -/
theorem zone_module_other {p : Program} {r : ℕ} {u1 u2 v1 v2 : ℤ}
    (hu : U p r + modLeft p + 20 ≤ u1 ∧ u2 ≤ U p r + modRight p - 20) :
    ∀ r' s, r' ≠ r → s ∈ moduleSpecs p r' → FarRect s.bx u1 u2 v1 v2 := by
  intro r' s hne hs
  have h := (moduleSpecs_uv p r' hs).1
  have hD := one_le_D p
  rcases lt_or_gt_of_ne hne with h' | h'
  · have := module_gap p (r := r') (r' := r) (by exact_mod_cast h')
    exact farRect_of_uv h (Or.inl (by unfold modLeft modRight at *; omega))
  · have := module_gap p (r := r) (r' := r') (by exact_mod_cast h')
    exact farRect_of_uv h (Or.inr (Or.inl (by unfold modLeft modRight at *; omega)))

/-- The channel ranges of a left zone lie in the zone. -/
theorem left_range (p : Program) {r idx cd : ℤ} (hidx : 0 ≤ idx ∧ idx ≤ 4 * D p)
    (hcd : U p r - 794 - 62 * idx ≤ cd ∧ cd ≤ U p r - 793 - 62 * idx) :
    U p r + modLeft p + 29 ≤ cd ∧ cd ≤ U p r - 793 := by
  unfold modLeft; omega

/-- **A leg on the channel `idx` of the left zone of module `r`** (owned by sub-band `b`, below
the sub-band): the reflector of every corner of another sub-band, other than the port corner of
the channel, is far from its rectangle. -/
theorem left_corner {p : Program} {r : ℕ} {idx cd b v1 v2 : ℤ} (hr : (r : ℤ) < R p)
    (hidx : 0 ≤ idx ∧ idx ≤ 4 * D p)
    (hcd : U p r - 794 - 62 * idx ≤ cd ∧ cd ≤ U p r - 793 - 62 * idx)
    (hown : Owns p b (.left r idx)) (hb : 1 ≤ b) (hv1 : VT p + 660 * b ≤ v1) {c : Corner}
    (hd : Desc p c) (hband : ∀ b' k h, c.tag = .band b' k h → b' ≠ b)
    (hne : c.tag ≠ .left r idx) : FarRect (cornerSpec c).bx (cd - 4) (cd + 4) v1 v2 := by
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have hl := left_range p hidx hcd
  have h0 := unit_module_gap p (a := 0) (r := r) ⟨le_rfl, by omega⟩ (by omega)
  have hA0 : A p 0 = 0 := by unfold A; ring
  refine corner_farRect ?_
  obtain ⟨hv, hcol, -, -⟩ := hd
  obtain ⟨k', u, v, tag⟩ := c
  simp only at hband hcol hne ⊢
  cases tag with
  | band b' n h =>
    simp only [Valid] at hv
    obtain ⟨hv1', hv2', hv3, hv4, hv5, hv6, hv7, hv8⟩ := hv
    have hne' := hband b' n h rfl
    rcases lt_or_gt_of_ne hne' with hb' | hb'
    · omega
    · cases h
      · rcases hcol b' n rfl with ⟨a', rfl, h1, h2⟩ | ⟨a', t', h0', ht0, ht1, rfl, -⟩ |
          ⟨r', idx', hr', hi0, hi1, hu0, hu1, hown'⟩ | ⟨r', j, hr', hj0, hj1, hu0, hu1, -⟩
        · have := unit_module_gap p (a := a') (r := r) ⟨by omega, by omega⟩ (by omega)
          omega
        · have hc0' := unitC0_cases p a'
          have := unit_module_gap p (a := a') (r := r) ⟨by omega, by omega⟩ (by omega)
          simp only [destU, inCol] at *; omega
        · rcases lt_trichotomy r' r with h | rfl | h
          · have := module_gap p (r := r') (r' := r) (by exact_mod_cast h)
            unfold modLeft modRight at *; omega
          · by_cases hii : idx' = idx
            · subst hii
              have := owns_unique (by simp) hown hown'
              omega
            · omega
          · have := module_gap p (r := r) (r' := r') (by exact_mod_cast h)
            unfold modLeft modRight at *; omega
        · rcases lt_trichotomy r' r with h | rfl | h
          · have := module_gap p (r := r') (r' := r) (by exact_mod_cast h)
            unfold modLeft modRight uR at *; omega
          · unfold uR at *; omega
          · have := module_gap p (r := r) (r' := r') (by exact_mod_cast h)
            unfold modLeft modRight uR at *; omega
      · have := hv7 rfl
        omega
  | halt a' => simp only [Valid] at hv; omega
  | slab a' t => simp only [Valid] at hv; omega
  | left r' idx' =>
    simp only [Valid] at hv
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · have : idx' ≠ idx := fun h' => hne (by rw [h'])
      omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega
  | right r' j w =>
    simp only [Valid] at hv
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega

/-- A rectangle on a left-zone channel of module `r` is far from every piece of module `r`. -/
theorem left_module_own {p : Program} {r : ℕ} {cd v1 v2 : ℤ} (hcd : cd ≤ U p r - 793) :
    ∀ s ∈ moduleSpecs p r, FarRect s.bx (cd - 4) (cd + 4) v1 v2 := by
  intro s hs
  have h := (moduleSpecs_uv p r hs).1
  exact farRect_of_uv h (Or.inr (Or.inl (by omega)))

/-- **A leg on a channel of caller `j` in the right zone of module `r`** (owned by sub-band `b`,
below the sub-band): the Z token channel ending at the Z token corner (`w = 2`) or the Z answer
channel starting at the Z answer corner (`w = 1`); the reflector of every corner of another
sub-band, other than that end corner, is far from its rectangle. -/
theorem right_corner {p : Program} {r : ℕ} {j cd b v1 v2 : ℤ} (hr : (r : ℤ) < R p)
    (hj : 0 ≤ j ∧ j < D p) (hown : Owns p b (.right r j 0)) (hb : 1 ≤ b)
    (hv1 : VT p + 660 * b ≤ v1) {c : Corner} (hd : Desc p c)
    (hband : ∀ b' k h, c.tag = .band b' k h → b' ≠ b)
    (hcd : (U p r + 1471 + 144 * D p + 124 * (D p - 1 - j) ≤ cd ∧
        cd ≤ U p r + 1472 + 144 * D p + 124 * (D p - 1 - j) ∧ c.tag ≠ .right r j 2) ∨
      (U p r + 1409 + 144 * D p + 124 * (D p - 1 - j) ≤ cd ∧
        cd ≤ U p r + 1410 + 144 * D p + 124 * (D p - 1 - j) ∧ c.tag ≠ .right r j 1)) :
    FarRect (cornerSpec c).bx (cd - 4) (cd + 4) v1 v2 := by
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have h0 := unit_module_gap p (a := 0) (r := r) ⟨le_rfl, by omega⟩ (by omega)
  have hA0 : A p 0 = 0 := by unfold A; ring
  refine corner_farRect ?_
  obtain ⟨hv, hcol, -, -⟩ := hd
  obtain ⟨k', u, v, tag⟩ := c
  simp only at hband hcol hcd ⊢
  cases tag with
  | band b' n h =>
    simp only [Valid] at hv
    obtain ⟨hv1', hv2', hv3, hv4, hv5, hv6, hv7, hv8⟩ := hv
    have hne' := hband b' n h rfl
    rcases lt_or_gt_of_ne hne' with hb' | hb'
    · omega
    · cases h
      · rcases hcol b' n rfl with ⟨a', rfl, h1, h2⟩ | ⟨a', t', h0', ht0, ht1, rfl, -⟩ |
          ⟨r', idx', hr', hi0, hi1, hu0, hu1, -⟩ | ⟨r', j', hr', hj0, hj1, hu0, hu1, hown'⟩
        · have := unit_module_gap p (a := a') (r := r) ⟨by omega, by omega⟩ (by omega)
          unfold modLeft at this; omega
        · have hc0' := unitC0_cases p a'
          have := unit_module_gap p (a := a') (r := r) ⟨by omega, by omega⟩ (by omega)
          simp only [destU, inCol] at *; unfold modLeft at this; omega
        · rcases lt_trichotomy r' r with h | rfl | h
          · have := module_gap p (r := r') (r' := r) (by exact_mod_cast h)
            unfold modLeft modRight at *; omega
          · omega
          · have := module_gap p (r := r) (r' := r') (by exact_mod_cast h)
            unfold modLeft modRight at *; omega
        · rcases lt_trichotomy r' r with h | rfl | h
          · have := module_gap p (r := r') (r' := r) (by exact_mod_cast h)
            unfold modLeft modRight uR at *; omega
          · by_cases hjj : j' = j
            · subst hjj
              have := owns_unique (by simp) hown hown'
              omega
            · unfold uR at *; omega
          · have := module_gap p (r := r) (r' := r') (by exact_mod_cast h)
            unfold modLeft modRight uR at *; omega
      · have := hv7 rfl
        unfold modLeft at h0
        omega
  | halt a' => simp only [Valid] at hv; omega
  | slab a' t => simp only [Valid] at hv; omega
  | left r' idx' =>
    simp only [Valid] at hv
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega
  | right r' j' w =>
    simp only [Valid] at hv
    simp only [ne_eq, CTag.right.injEq, not_and] at hcd
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · obtain ⟨-, -, hj0', hj1', hw⟩ := hv
      by_cases hjj : j' = j
      · subst hjj
        rcases hw with ⟨rfl, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _⟩ <;>
          simp at hcd <;> omega
      · rcases hw with ⟨rfl, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _⟩ <;> omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega

/-- A rectangle on a right-zone channel of module `r` is far from every piece of module `r`. -/
theorem right_module_own {p : Program} {r : ℕ} {cd v1 v2 : ℤ}
    (hcd : U p r + 1409 + 144 * D p ≤ cd) :
    ∀ s ∈ moduleSpecs p r, FarRect s.bx (cd - 4) (cd + 4) v1 v2 := by
  intro s hs
  have h := (moduleSpecs_uv p r hs).1
  exact farRect_of_uv h (Or.inl (by omega))

/-- **A leg on a depth line of the right zone of module `r`** (`v_d` of caller `j`, between its
corners `0` and `1`, or `w_d`, between its corners `2` and `3`): the reflector of every corner
other than those two is far from its rectangle. -/
theorem rzone_corner {p : Program} {r : ℕ} {j V u1 u2 : ℤ} (hj : 0 ≤ j ∧ j < D p)
    (hu : U p r + 806 ≤ u1 ∧ u2 ≤ U p r + modRight p) {c : Corner} (hv : Valid p c)
    (hV : (V = 1500 + 180 * (D p - 1 - j) ∧ c.tag ≠ .right r j 0 ∧ c.tag ≠ .right r j 1) ∨
      (V = 1561 + 180 * (D p - 1 - j) ∧ c.tag ≠ .right r j 2 ∧ c.tag ≠ .right r j 3)) :
    FarRect (cornerSpec c).bx u1 u2 (V - 2) (V + 6) := by
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  refine corner_farRect ?_
  obtain ⟨k', u, v, tag⟩ := c
  simp only at hV ⊢
  cases tag with
  | band b' n h =>
    simp only [Valid] at hv
    obtain ⟨hv1', hv2', hv3, hv4, hv5, hv6, hv7, hv8⟩ := hv
    omega
  | halt a' => simp only [Valid] at hv; omega
  | slab a' t => simp only [Valid] at hv; omega
  | left r' idx' =>
    simp only [Valid] at hv
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · unfold modRight at *; omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega
  | right r' j' w =>
    simp only [Valid] at hv
    simp only [ne_eq, CTag.right.injEq, not_and] at hV
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · obtain ⟨-, -, hj0', hj1', hw⟩ := hv
      by_cases hjj : j' = j
      · subst hjj
        rcases hw with ⟨rfl, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _⟩ <;>
          simp at hV <;> omega
      · rcases hw with ⟨rfl, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _⟩ <;> omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega

/-- A rectangle in the right zone of module `r` (right of `U_r + 806`, below `v = 706`) is far
from every piece of module `r`. -/
theorem rzone_module_own {p : Program} {r : ℕ} {u1 u2 v1 v2 : ℤ} (hu : U p r + 806 ≤ u1)
    (hv : 706 ≤ v1) : ∀ s ∈ moduleSpecs p r, FarRect s.bx u1 u2 v1 v2 := by
  intro s hs
  obtain ⟨-, h⟩ := moduleSpecs_uv p r hs
  unfold FarRect
  omega

/-- **The first leg of a Z answer** (down the station column of caller `j` of module `r`, from
`v ≥ 708`): the reflector of every corner other than its first corner is far from its
rectangle. -/
theorem zstation_corner {p : Program} {r : ℕ} {j v1 v2 : ℤ} (hj : 0 ≤ j ∧ j < D p)
    (hv1 : 706 ≤ v1) {c : Corner} (hv : Valid p c) (hne : c.tag ≠ .right r j 0) :
    FarRect (cornerSpec c).bx (U p r + 1297 + 144 * j) (U p r + 1305 + 144 * j) v1 v2 := by
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  refine corner_farRect ?_
  obtain ⟨k', u, v, tag⟩ := c
  simp only at hne ⊢
  cases tag with
  | band b' n h =>
    simp only [Valid] at hv
    obtain ⟨hv1', hv2', hv3, hv4, hv5, hv6, hv7, hv8⟩ := hv
    omega
  | halt a' => simp only [Valid] at hv; omega
  | slab a' t => simp only [Valid] at hv; omega
  | left r' idx' =>
    simp only [Valid] at hv
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega
  | right r' j' w =>
    simp only [Valid] at hv
    simp only [ne_eq, CTag.right.injEq, not_and] at hne
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · obtain ⟨-, -, hj0', hj1', hw⟩ := hv
      by_cases hjj : j' = j
      · subst hjj
        rcases hw with ⟨rfl, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _⟩ <;>
          simp at hne <;> omega
      · rcases hw with ⟨rfl, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ | ⟨rfl, _, _⟩ <;> omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega

end LP

end LeanTheory.Life
