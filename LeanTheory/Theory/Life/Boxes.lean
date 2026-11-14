/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Reactions

/-!
# Rectangular footprints

Rectangles of cells as footprints of reactions (research note `N-08`), so that components can be
separated in both coordinates.

* `Box a b lo hi`: the cells with `a ≤ x ≤ b` and `lo ≤ y ≤ hi`.
* `Box.farApart`: boxes with a gap of more than `r` cells in one coordinate are `FarApart r`.
* `image_add_box`: a translate of a box is a box.
* `boxCheck` and `coe_ofRows_subset_box`: a window lies in a box if a Boolean check on its data
  succeeds; the check is evaluated by `rfl`. Together with `life_eval` this gives the box of
  each generation of a certified evolution.
* `reaction_flight_box`: a pattern that reappears translated by `v` after `p` generations, and
  stays in a box during its first `p` generations, flies inside that box moved by `v` every `p`
  generations. This covers spaceships in every direction.
* `IsStillLife.reaction_box`, `IsOscillator.reaction_box`: resting components.

**Sanity.** `glider_flight_box` (the catalogue glider flying inside a 4 × 4 box that follows it),
`not_farApart_box_fixture` (adjacent boxes are not far apart), `boxCheck_fixture_false` (a window
that sticks out of a box fails the check).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- The rectangle of cells with `a ≤ x ≤ b` and `lo ≤ y ≤ hi`. -/
def Box (a b lo hi : ℤ) : Set Cell := {c | a ≤ c.1 ∧ c.1 ≤ b ∧ lo ≤ c.2 ∧ c.2 ≤ hi}

/-- Membership in a box. -/
theorem mem_box {a b lo hi : ℤ} {c : Cell} :
    c ∈ Box a b lo hi ↔ a ≤ c.1 ∧ c.1 ≤ b ∧ lo ≤ c.2 ∧ c.2 ≤ hi :=
  Iff.rfl

/-- A box grows with its bounds. -/
theorem box_subset_box {a b lo hi a' b' lo' hi' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : Box a b lo hi ⊆ Box a' b' lo' hi' := by
  rintro c ⟨h1, h2, h3, h4⟩
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **Separated boxes**: a gap of more than `r` columns or rows between two boxes puts them at
distance greater than `r`. -/
theorem Box.farApart {r : ℕ} {a b lo hi a' b' lo' hi' : ℤ}
    (h : b + r < a' ∨ b' + r < a ∨ hi + r < lo' ∨ hi' + r < lo) :
    FarApart r (Box a b lo hi) (Box a' b' lo' hi') := by
  rintro s ⟨s1, s2, s3, s4⟩ t ⟨t1, t2, t3, t4⟩ ⟨n1, n2, n3, n4⟩
  omega

/-- A translate of a box is a box. -/
theorem image_add_box (v : Cell) (a b lo hi : ℤ) :
    (fun c => v + c) '' Box a b lo hi = Box (a + v.1) (b + v.1) (lo + v.2) (hi + v.2) := by
  ext c
  constructor
  · rintro ⟨d, ⟨h1, h2, h3, h4⟩, rfl⟩
    exact ⟨by simp only [Prod.fst_add]; omega, by simp only [Prod.fst_add]; omega,
      by simp only [Prod.snd_add]; omega, by simp only [Prod.snd_add]; omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨c - v, ⟨by simp only [Prod.fst_sub]; omega, by simp only [Prod.fst_sub]; omega,
      by simp only [Prod.snd_sub]; omega, by simp only [Prod.snd_sub]; omega⟩, by simp⟩

/-! ### Windows in boxes -/

/-- The cells of a window whose rows are all below `2 ^ w` lie in its first `w` columns. -/
theorem fst_lt_of_mem_ofRows {x y : ℤ} {rows : List ℕ} {w : ℕ} {c : Cell}
    (hw : ∀ r ∈ rows, r < 2 ^ w) (h : c ∈ ofRows x y rows) : c.1 < x + w := by
  have hx := (le_of_mem_ofRows h).1
  have hy := (le_of_mem_ofRows h).2
  have hlen := snd_lt_of_mem_ofRows h
  rw [mem_ofRows, bitAt] at h
  by_contra hc
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c.1 - x by omega)
  obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c.2 - y by omega)
  rw [hj, hi, rowZ_natCast, tb_natCast] at h
  have hi' : i < rows.length := by omega
  have hr := hw (rows.getD i 0) (by rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi')
  have h1 := Nat.ge_two_pow_of_testBit h
  have h2 : 2 ^ w ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Boolean check that the window `(x, y, rows)` lies in the box with bounds `a`, `b`, `lo`,
`hi`: the origin is inside, the last row is inside, and every row fits in the columns up to
`b`. -/
def boxCheck (x y : ℤ) (rows : List ℕ) (a b lo hi : ℤ) : Bool :=
  decide (a ≤ x) && decide (lo ≤ y) && decide (y + rows.length ≤ hi + 1) &&
    rows.all fun r => decide (r < 2 ^ (b + 1 - x).toNat)

/-- **Soundness of `boxCheck`.** -/
theorem coe_ofRows_subset_box {x y : ℤ} {rows : List ℕ} {a b lo hi : ℤ}
    (h : boxCheck x y rows a b lo hi = true) :
    (ofRows x y rows : Set Cell) ⊆ Box a b lo hi := by
  simp only [boxCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  intro c hc
  have hc' := mem_coe.1 hc
  have hx := (le_of_mem_ofRows hc').1
  have hy := (le_of_mem_ofRows hc').2
  have hlen := snd_lt_of_mem_ofRows hc'
  have hw := fst_lt_of_mem_ofRows h4 hc'
  refine ⟨by omega, ?_, by omega, by omega⟩
  by_cases hb : 0 ≤ b + 1 - x
  · rw [Int.toNat_of_nonneg hb] at hw
    omega
  · rw [Int.toNat_eq_zero.2 (by omega)] at hw
    simp only [Nat.cast_zero, add_zero] at hw
    omega

/-! ### Basic reactions with boxes -/

/-- A still life inside a box is a reaction of any duration with that box as footprint. -/
theorem IsStillLife.reaction_box {T : Finset Cell} (h : IsStillLife T) {a b lo hi : ℤ}
    (hT : (T : Set Cell) ⊆ Box a b lo hi) (n : ℕ) :
    Reaction T T n (fun _ => Box a b lo hi) :=
  (h.reaction n).mono fun _ _ => hT

/-- An oscillator that stays inside a box during one period is, over any number of periods, a
reaction with that box as footprint. -/
theorem IsOscillator.reaction_box {S : Finset Cell} {p : ℕ} (h : IsOscillator S p)
    {a b lo hi : ℤ} (hS : ∀ r < p, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi) (k : ℕ) :
    Reaction S S (k * p) (fun _ => Box a b lo hi) := by
  refine ⟨h.evolve_mul k, fun i _ => ?_⟩
  rw [h.evolve_mod i]
  exact hS _ (Nat.mod_lt _ (by have := h.1; omega))

/-- **Flight as a reaction with a moving box.** A pattern that reappears translated by `v` after
`p > 0` generations and stays in a box during its first `p` generations flies, for any number
`q` of periods, inside that box moved by `v` once per period. -/
theorem reaction_flight_box {S : Finset Cell} {p : ℕ} {v : Cell} {a b lo hi : ℤ} (hp : 0 < p)
    (hS : conway.evolve p S = translate v S)
    (hB : ∀ r < p, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi) (q : ℕ) :
    Reaction S (translate (q • v) S) (q * p)
      (fun i => (fun c => (i / p) • v + c) '' Box a b lo hi) := by
  refine ⟨conway.evolve_mul_of_evolve_eq_translate hS q, fun i _ c hc => ?_⟩
  rw [mem_coe, evolve_eq_translate_mod hS, mem_translate] at hc
  exact ⟨c - (i / p) • v, hB _ (Nat.mod_lt _ hp) (mem_coe.2 hc), by simp⟩

/-! ### Sanity -/

/-- **Sanity** (accepted fixture): the catalogue glider flies inside a 4 × 4 box that follows
it. -/
theorem glider_flight_box (q : ℕ) :
    Reaction Pattern.glider (translate (q • ((1, 1) : Cell)) Pattern.glider) (q * 4)
      (fun i => (fun c => (i / 4) • ((1, 1) : Cell) + c) '' Box 0 3 0 3) := by
  refine reaction_flight_box (by norm_num) Pattern.glider_isSpaceship.2.2.2.1 (fun r hr => ?_) q
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- **Sanity** (rejected fixture): adjacent boxes are not far apart. -/
theorem not_farApart_box_fixture : ¬ FarApart 2 (Box 0 1 0 1) (Box 3 4 0 1) := by
  intro h
  exact h (1, 0) ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩ (3, 0)
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Sanity** (rejected fixture): the glider window does not pass the check for a box that is
one column too narrow. -/
theorem boxCheck_fixture_false : boxCheck 0 0 [2, 4, 7] 0 1 0 2 = false := rfl

end LeanTheory.Life
