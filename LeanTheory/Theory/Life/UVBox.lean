/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Network
public import Mathlib.Tactic.Linarith

/-!
# Boxes in diagonal coordinates

Gliders fly along diagonals, so bounds on `u = x - y` and `v = x + y` describe them much more
tightly than boxes in `x` and `y`: the detector of the zero test passes within two cells of the
block at position `0`, but stays five apart from it in `v` (research note `N-20`).

* `UVBox U₁ U₂ V₁ V₂`: the cells with `U₁ ≤ x - y ≤ U₂` and `V₁ ≤ x + y ≤ V₂`;
* `uvCheck`, `coe_ofRows_subset_uv`: a computable check that a window lies in such a box, and its
  soundness;
* `UVBox.farApart_v`, `UVBox.farApart_u`: separated by more than four in `v` or in `u`;
* `flight_reaction_uv`: a glider flight with a moving diagonal box as footprint.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- The cells with `U₁ ≤ x - y ≤ U₂` and `V₁ ≤ x + y ≤ V₂`. -/
def UVBox (U₁ U₂ V₁ V₂ : ℤ) : Set Cell :=
  {c | U₁ ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U₂ ∧ V₁ ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ V₂}

/-- Diagonal boxes separated by more than four in `v` are far apart. -/
theorem UVBox.farApart_v {U₁ U₂ V₁ V₂ U₁' U₂' V₁' V₂' : ℤ} (h : V₂ + 4 < V₁' ∨ V₂' + 4 < V₁) :
    FarApart 2 (UVBox U₁ U₂ V₁ V₂) (UVBox U₁' U₂' V₁' V₂') := by
  rintro a ⟨-, -, a3, a4⟩ b ⟨-, -, b3, b4⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  omega

/-- Diagonal boxes separated by more than four in `u` are far apart. -/
theorem UVBox.farApart_u {U₁ U₂ V₁ V₂ U₁' U₂' V₁' V₂' : ℤ} (h : U₂ + 4 < U₁' ∨ U₂' + 4 < U₁) :
    FarApart 2 (UVBox U₁ U₂ V₁ V₂) (UVBox U₁' U₂' V₁' V₂') := by
  rintro a ⟨a1, a2, -, -⟩ b ⟨b1, b2, -, -⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  omega

/-- A box in `x, y` is far from a diagonal box separated from it by more than four in `v`. -/
theorem farApart_box_uv_v {a b lo hi U₁ U₂ V₁ V₂ : ℤ} (h : b + hi + 4 < V₁ ∨ V₂ + 4 < a + lo) :
    FarApart 2 (Box a b lo hi) (UVBox U₁ U₂ V₁ V₂) := by
  rintro x ⟨x1, x2, x3, x4⟩ y ⟨-, -, y3, y4⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  omega

/-- A box in `x, y` is far from a diagonal box separated from it by more than four in `u`. -/
theorem farApart_box_uv_u {a b lo hi U₁ U₂ V₁ V₂ : ℤ} (h : b - lo + 4 < U₁ ∨ U₂ + 4 < a - hi) :
    FarApart 2 (Box a b lo hi) (UVBox U₁ U₂ V₁ V₂) := by
  rintro x ⟨x1, x2, x3, x4⟩ y ⟨y1, y2, -, -⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  omega

/-- A computable check that the window `ofRows x y rows` lies in a diagonal box: every set bit of
every row (bits up to `log2` of the row) is a cell of the box. -/
def uvCheck (x y : ℤ) (rows : List ℕ) (U₁ U₂ V₁ V₂ : ℤ) : Bool :=
  (List.range rows.length).all fun i => (List.range ((rows.getD i 0).log2 + 1)).all fun j =>
    !((rows.getD i 0).testBit j) ||
      (decide (U₁ ≤ (x + j) - (y + i)) && decide ((x + j) - (y + i) ≤ U₂) &&
        decide (V₁ ≤ (x + j) + (y + i)) && decide ((x + j) + (y + i) ≤ V₂))

/-- **Soundness of `uvCheck`.** -/
theorem coe_ofRows_subset_uv {x y : ℤ} {rows : List ℕ} {U₁ U₂ V₁ V₂ : ℤ}
    (h : uvCheck x y rows U₁ U₂ V₁ V₂ = true) :
    (ofRows x y rows : Set Cell) ⊆ UVBox U₁ U₂ V₁ V₂ := by
  intro c hc
  simp only [mem_coe, ofRows, mem_biUnion, mem_range, mem_image, mem_filter] at hc
  obtain ⟨i, hi, j, ⟨-, hbit⟩, rfl⟩ := hc
  have hj : j < (rows.getD i 0).log2 + 1 := by
    by_contra hj
    have h1 : rows.getD i 0 < 2 ^ j :=
      lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1] at hbit
    exact Bool.false_ne_true hbit
  simp only [uvCheck, List.all_eq_true, List.mem_range] at h
  have := h i hi j hj
  simp only [hbit, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  exact ⟨h1, h2, h3, h4⟩

/-- **Flight with a moving diagonal box**: a pattern moving by `(dx, dy)` every four generations
whose first four generations lie in a diagonal box stays, at generation `i`, in that box moved by
`(i / 4) • (dx, dy)` (in `u` by `(i / 4) (dx - dy)`, in `v` by `(i / 4) (dx + dy)`). -/
theorem flight_reaction_uv {G G' : Finset Cell} {dx dy U₁ U₂ V₁ V₂ : ℤ}
    (h4 : conway.evolve 4 G = translate (dx, dy) G)
    (hB : ∀ r < 4, (conway.evolve r G : Set Cell) ⊆ UVBox U₁ U₂ V₁ V₂) (q r : ℕ)
    (hend : translate ((q : ℤ) * dx, (q : ℤ) * dy) (conway.evolve r G) = G') :
    Reaction G G' (4 * q + r) (fun i => UVBox (U₁ + ((i / 4 : ℕ) : ℤ) * (dx - dy))
      (U₂ + ((i / 4 : ℕ) : ℤ) * (dx - dy)) (V₁ + ((i / 4 : ℕ) : ℤ) * (dx + dy))
      (V₂ + ((i / 4 : ℕ) : ℤ) * (dx + dy))) := by
  refine ⟨?_, fun i _ c hc => ?_⟩
  · rw [← hend, add_comm, Rule.evolve_add, mul_comm, conway.evolve_mul_of_evolve_eq_translate h4,
      Rule.evolve_translate]
    congr 1
  · rw [mem_coe, show i = i % 4 + (i / 4) * 4 by omega, Rule.evolve_add,
      conway.evolve_mul_of_evolve_eq_translate h4, Rule.evolve_translate, mem_translate] at hc
    obtain ⟨h1, h2, h3, h4⟩ := hB (i % 4) (Nat.mod_lt _ (by norm_num)) (mem_coe.2 hc)
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul]
      at h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Flight with both footprints**: the box in `x, y` and the diagonal box, both moving. -/
theorem flight_reaction_xyuv {G G' : Finset Cell} {dx dy a b lo hi U₁ U₂ V₁ V₂ : ℤ}
    (h4 : conway.evolve 4 G = translate (dx, dy) G)
    (hB : ∀ r < 4, (conway.evolve r G : Set Cell) ⊆ Box a b lo hi)
    (hU : ∀ r < 4, (conway.evolve r G : Set Cell) ⊆ UVBox U₁ U₂ V₁ V₂) (q r : ℕ)
    (hend : translate ((q : ℤ) * dx, (q : ℤ) * dy) (conway.evolve r G) = G') :
    Reaction G G' (4 * q + r) (fun i =>
      Box (a + ((i / 4 : ℕ) : ℤ) * dx) (b + ((i / 4 : ℕ) : ℤ) * dx) (lo + ((i / 4 : ℕ) : ℤ) * dy)
        (hi + ((i / 4 : ℕ) : ℤ) * dy) ∩
      UVBox (U₁ + ((i / 4 : ℕ) : ℤ) * (dx - dy)) (U₂ + ((i / 4 : ℕ) : ℤ) * (dx - dy))
        (V₁ + ((i / 4 : ℕ) : ℤ) * (dx + dy)) (V₂ + ((i / 4 : ℕ) : ℤ) * (dx + dy))) :=
  ⟨(flight_reaction h4 hB q r hend).evolve_eq, fun i hi _ hc =>
    ⟨(flight_reaction h4 hB q r hend).subset i hi hc,
      (flight_reaction_uv h4 hU q r hend).subset i hi hc⟩⟩

/-- Far apart from a part of a set: the intersection with another set, on the left. -/
theorem FarApart.inter_left {A A' B : Set Cell} (h : FarApart 2 A B) : FarApart 2 (A ∩ A') B :=
  fun a ha => h a ha.1

/-- Far apart from a part of a set: the intersection with another set, on the right (second). -/
theorem FarApart.inter_left' {A A' B : Set Cell} (h : FarApart 2 A' B) : FarApart 2 (A ∩ A') B :=
  fun a ha => h a ha.2

/-- Far apart from a part of a set: the intersection with another set, on the right. -/
theorem FarApart.inter_right {A B B' : Set Cell} (h : FarApart 2 A B) : FarApart 2 A (B ∩ B') :=
  fun a ha b hb => h a ha b hb.1

/-- Far apart from a part of a set: the intersection with another set, on the right (second). -/
theorem FarApart.inter_right' {A B B' : Set Cell} (h : FarApart 2 A B') :
    FarApart 2 A (B ∩ B') :=
  fun a ha b hb => h a ha b hb.2

end LeanTheory.Life
