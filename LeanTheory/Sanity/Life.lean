/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Life
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Tactic.IntervalCases

/-!
# Sanity checks for the Game of Life kernel

Checks that the definitions of `Kernel/Life` mean what they should. Each group names the risk
it tests.

* **Neighbourhood** (wrong neighbourhood shape): `mem_nbrs_iff_max` (Chebyshev distance one, the
  definition used in the HOL4 formalization), `nbrs_eq` (the eight explicit cells), `card_nbrs`,
  `liveNbrs_le_eight`, `liveNbrs_eq` (the count as a sum of eight indicators).
* **Independent characterization** (the computable step differs from the rule):
  `Rule.coe_step`, the finite step equals the set-level specification `Rule.stepSet`.
* **The specification itself** (totalized cardinality, infinite configurations):
  `liveNbrsSet_le_eight`, `conway_stepSet_univ` (the full plane dies of overcrowding).
* **Necessity of the rule's side condition** (silent truncation of an infinite successor):
  `stepSetCore_birth_zero_empty` and `not_finite_stepSetCore_birth_zero`, a rule with birth at
  zero neighbours turns the empty configuration into the whole plane.
* **Degenerate cases**: `Rule.step_empty`, `Rule.evolve_empty`,
  `conway_step_eq_empty_of_card_lt_three` (fewer than three cells die), `conway_step_singleton`.
* **Concrete instances** (the rule is not vacuous): the block is a still life
  (`conway_step_block`), the blinker has period exactly two (`conway_step_blinkerH`,
  `conway_step_blinkerV`, `blinkerH_ne_blinkerV`, `conway_evolve_two_blinkerH`).
* **Counterexamples to overbroad claims**: the step is not monotone
  (`not_monotone_conway_step`), not injective (`not_injective_conway_step`) and not additive on
  disjoint adjacent patterns (`not_additive_conway_step`).
* **Symmetry**: `Rule.step_map` (any bijection of the grid preserving neighbours commutes with
  the step), with translations, the transposition and a reflection as instances; together these
  generate all symmetries of the grid. `blinkerV_eq_map_blinkerH` checks it on an instance.
* **Speed of light** (finiteness and locality of growth): `Rule.step_subset`,
  `Rule.exists_near_of_mem_step`, `Rule.exists_near_of_mem_evolve`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### The neighbourhood -/

/-- The neighbours are the cells at Chebyshev distance exactly one. -/
theorem mem_nbrs_iff_max {c d : Cell} : d ∈ nbrs c ↔ max |d.1 - c.1| |d.2 - c.2| = 1 := by
  obtain ⟨x, y⟩ := c
  obtain ⟨a, b⟩ := d
  simp only [mem_nbrs, ne_eq, Prod.mk.injEq]
  rcases abs_cases (a - x) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases abs_cases (b - y) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases max_cases |a - x| |b - y| with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> omega

/-- The eight neighbours of `(x, y)`, explicitly. -/
theorem nbrs_eq (x y : ℤ) :
    nbrs (x, y) = {(x - 1, y - 1), (x, y - 1), (x + 1, y - 1), (x - 1, y), (x + 1, y),
      (x - 1, y + 1), (x, y + 1), (x + 1, y + 1)} := by
  ext ⟨a, b⟩
  simp only [mem_nbrs, mem_insert, mem_singleton, Prod.mk.injEq, ne_eq]
  omega

/-- Every cell has exactly eight neighbours. -/
theorem card_nbrs (c : Cell) : (nbrs c).card = 8 := by
  have hmem : c ∈ Finset.Icc (c.1 - 1) (c.1 + 1) ×ˢ Finset.Icc (c.2 - 1) (c.2 + 1) := by
    simp
  rw [nbrs, card_erase_of_mem hmem, card_product, Int.card_Icc, Int.card_Icc]
  have h1 : (c.1 + 1 + 1 - (c.1 - 1)).toNat = 3 := by omega
  have h2 : (c.2 + 1 + 1 - (c.2 - 1)).toNat = 3 := by omega
  rw [h1, h2]

/-- A cell has at most eight live neighbours. -/
theorem liveNbrs_le_eight (S : Finset Cell) (c : Cell) : liveNbrs S c ≤ 8 :=
  (card_filter_le _ _).trans (card_nbrs c).le

/-- The live neighbours of `c` are live cells other than `c`. -/
theorem liveNbrs_le_card_erase (S : Finset Cell) (c : Cell) :
    liveNbrs S c ≤ (S.erase c).card := by
  apply card_le_card
  intro d hd
  rw [mem_filter] at hd
  exact mem_erase.2 ⟨fun h => notMem_nbrs_self c (h ▸ hd.1), hd.2⟩

/-- The live-neighbour count as a sum of eight indicators; this is the form in which the count
of a concrete cell is evaluated by `simp`. -/
theorem liveNbrs_eq (S : Finset Cell) (x y : ℤ) :
    liveNbrs S (x, y) =
      (if (x - 1, y - 1) ∈ S then 1 else 0) + ((if (x, y - 1) ∈ S then 1 else 0) +
      ((if (x + 1, y - 1) ∈ S then 1 else 0) + ((if (x - 1, y) ∈ S then 1 else 0) +
      ((if (x + 1, y) ∈ S then 1 else 0) + ((if (x - 1, y + 1) ∈ S then 1 else 0) +
      ((if (x, y + 1) ∈ S then 1 else 0) + (if (x + 1, y + 1) ∈ S then 1 else 0))))))) := by
  unfold liveNbrs
  rw [card_filter, nbrs_eq]
  repeat rw [sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega)]
  rw [sum_singleton]

/-! ### The computable step equals the specification -/

/-- On a finite configuration the set-level neighbour count is the finite one. -/
theorem liveNbrsSet_coe (S : Finset Cell) (c : Cell) :
    liveNbrsSet (S : Set Cell) c = liveNbrs S c := by
  unfold liveNbrsSet liveNbrs
  rw [← coe_inter, Set.ncard_coe_finset, filter_mem_eq_inter]

/-- **Independent characterization**: the computable step on a finite configuration is the
set-level specification of the rule. -/
theorem Rule.coe_step (R : Rule) (S : Finset Cell) :
    (R.step S : Set Cell) = R.stepSet (S : Set Cell) := by
  ext c
  simp [Rule.stepSet, stepSetCore, Rule.mem_step, liveNbrsSet_coe]

/-- The set-level neighbour count never exceeds eight, for arbitrary (also infinite) sets: the
`ncard` in its definition is always the cardinality of a finite set. -/
theorem liveNbrsSet_le_eight (X : Set Cell) (c : Cell) : liveNbrsSet X c ≤ 8 := by
  unfold liveNbrsSet
  calc ((nbrs c : Set Cell) ∩ X).ncard ≤ (nbrs c : Set Cell).ncard :=
        Set.ncard_le_ncard Set.inter_subset_left (nbrs c).finite_toSet
    _ = 8 := by rw [Set.ncard_coe_finset, card_nbrs]

/-- **The specification on an infinite configuration**: when every cell is alive, every cell
has eight live neighbours and dies of overcrowding under Conway's rule. -/
theorem conway_stepSet_univ : conway.stepSet (Set.univ : Set Cell) = ∅ := by
  ext c
  have h : liveNbrsSet (Set.univ : Set Cell) c = 8 := by
    rw [liveNbrsSet, Set.inter_univ, Set.ncard_coe_finset, card_nbrs]
  simp [Rule.stepSet, stepSetCore, h, conway]

/-- With birth at zero neighbours the specification turns the empty configuration into the
whole plane: the side condition `Rule.zero_notMem_birth` cannot be dropped. -/
theorem stepSetCore_birth_zero_empty : stepSetCore {0} ∅ (∅ : Set Cell) = Set.univ := by
  ext c
  simp [stepSetCore, liveNbrsSet]

/-- The successor of the empty configuration under birth at zero neighbours is infinite, so it
is not a finite configuration. -/
theorem not_finite_stepSetCore_birth_zero : ¬ (stepSetCore {0} ∅ (∅ : Set Cell)).Finite := by
  rw [stepSetCore_birth_zero_empty]
  exact Set.infinite_univ

/-! ### Degenerate cases -/

/-- The empty configuration stays empty under every rule. -/
@[simp] theorem Rule.step_empty (R : Rule) : R.step ∅ = ∅ := by
  simp [Rule.step]

/-- The empty configuration stays empty forever. -/
@[simp] theorem Rule.evolve_empty (R : Rule) (n : ℕ) : R.evolve n ∅ = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Rule.evolve_succ, ih, Rule.step_empty]

/-- Under Conway's rule a configuration with fewer than three live cells dies in one
generation. -/
theorem conway_step_eq_empty_of_card_lt_three {S : Finset Cell} (h : S.card < 3) :
    conway.step S = ∅ := by
  ext c
  simp only [Rule.mem_step, conway, mem_insert, mem_singleton, notMem_empty, iff_false]
  have h1 := liveNbrs_le_card_erase S c
  rintro (⟨hc, h2⟩ | ⟨hc, h2⟩)
  · rw [card_erase_of_mem hc] at h1
    omega
  · rw [erase_eq_of_notMem hc] at h1
    omega

/-- A single live cell dies. -/
theorem conway_step_singleton (c : Cell) : conway.step {c} = ∅ :=
  conway_step_eq_empty_of_card_lt_three (by simp)

/-! ### Speed of light -/

/-- After one generation only live cells and their neighbours can be alive. -/
theorem Rule.step_subset (R : Rule) (S : Finset Cell) : R.step S ⊆ S ∪ S.biUnion nbrs :=
  filter_subset _ _

/-- **Speed of light, one generation**: a cell alive after one generation is within distance
one of a cell alive before. -/
theorem Rule.exists_near_of_mem_step {R : Rule} {S : Finset Cell} {c : Cell}
    (h : c ∈ R.step S) :
    ∃ d ∈ S, d.1 - 1 ≤ c.1 ∧ c.1 ≤ d.1 + 1 ∧ d.2 - 1 ≤ c.2 ∧ c.2 ≤ d.2 + 1 := by
  have h' := R.step_subset S h
  rw [mem_union, mem_biUnion] at h'
  rcases h' with h' | ⟨d, hd, hcd⟩
  · exact ⟨c, h', by omega, by omega, by omega, by omega⟩
  · exact ⟨d, hd, (mem_nbrs.1 hcd).2⟩

/-- **Speed of light**: a cell alive after `n` generations is within distance `n` of a cell
alive at the start. In particular the bounding box grows by at most one cell per generation
in each direction. -/
theorem Rule.exists_near_of_mem_evolve {R : Rule} {n : ℕ} {S : Finset Cell} {c : Cell}
    (h : c ∈ R.evolve n S) :
    ∃ d ∈ S, d.1 - n ≤ c.1 ∧ c.1 ≤ d.1 + n ∧ d.2 - n ≤ c.2 ∧ c.2 ≤ d.2 + n := by
  induction n generalizing c with
  | zero => exact ⟨c, h, by simp⟩
  | succ n ih =>
    rw [Rule.evolve_succ] at h
    obtain ⟨e, he, h1, h2, h3, h4⟩ := Rule.exists_near_of_mem_step h
    obtain ⟨d, hd, h5, h6, h7, h8⟩ := ih he
    refine ⟨d, hd, ?_⟩
    push_cast
    omega

/-! ### Concrete instances -/

/-- The block: a two-by-two square. -/
def block : Finset Cell := {(0, 0), (1, 0), (0, 1), (1, 1)}

/-- The horizontal phase of the blinker. -/
def blinkerH : Finset Cell := {(-1, 0), (0, 0), (1, 0)}

/-- The vertical phase of the blinker. -/
def blinkerV : Finset Cell := {(0, -1), (0, 0), (0, 1)}

/-- **Concrete instance**: the block is a still life. -/
theorem conway_step_block : conway.step block = block := by
  ext ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hd, h1, h2, h3, h4⟩ := Rule.exists_near_of_mem_step h
    have hb : -1 ≤ x ∧ x ≤ 2 ∧ -1 ≤ y ∧ y ≤ 2 := by
      simp only [block, mem_insert, mem_singleton, Prod.mk.injEq] at hd
      dsimp only at h1 h2 h3 h4
      omega
    obtain ⟨hx1, hx2, hy1, hy2⟩ := hb
    interval_cases x <;> interval_cases y <;>
      simp [Rule.mem_step, liveNbrs_eq, block, conway] at h ⊢
  · intro h
    simp only [block, mem_insert, mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [Rule.mem_step, liveNbrs_eq, block, conway]

/-- **Concrete instance**: the horizontal blinker becomes the vertical one. -/
theorem conway_step_blinkerH : conway.step blinkerH = blinkerV := by
  ext ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hd, h1, h2, h3, h4⟩ := Rule.exists_near_of_mem_step h
    have hb : -2 ≤ x ∧ x ≤ 2 ∧ -1 ≤ y ∧ y ≤ 1 := by
      simp only [blinkerH, mem_insert, mem_singleton, Prod.mk.injEq] at hd
      dsimp only at h1 h2 h3 h4
      omega
    obtain ⟨hx1, hx2, hy1, hy2⟩ := hb
    interval_cases x <;> interval_cases y <;>
      simp [Rule.mem_step, liveNbrs_eq, blinkerH, blinkerV, conway] at h ⊢
  · intro h
    simp only [blinkerV, mem_insert, mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [Rule.mem_step, liveNbrs_eq, blinkerH, conway]

/-- **Concrete instance**: the vertical blinker becomes the horizontal one. -/
theorem conway_step_blinkerV : conway.step blinkerV = blinkerH := by
  ext ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hd, h1, h2, h3, h4⟩ := Rule.exists_near_of_mem_step h
    have hb : -1 ≤ x ∧ x ≤ 1 ∧ -2 ≤ y ∧ y ≤ 2 := by
      simp only [blinkerV, mem_insert, mem_singleton, Prod.mk.injEq] at hd
      dsimp only at h1 h2 h3 h4
      omega
    obtain ⟨hx1, hx2, hy1, hy2⟩ := hb
    interval_cases x <;> interval_cases y <;>
      simp [Rule.mem_step, liveNbrs_eq, blinkerH, blinkerV, conway] at h ⊢
  · intro h
    simp only [blinkerH, mem_insert, mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [Rule.mem_step, liveNbrs_eq, blinkerV, conway]

/-- The two phases of the blinker are different, so its period is not one. -/
theorem blinkerH_ne_blinkerV : blinkerH ≠ blinkerV := by
  intro h
  have h1 : ((1, 0) : Cell) ∈ blinkerH := by simp [blinkerH]
  rw [h] at h1
  simp [blinkerV] at h1

/-- The blinker returns to itself after two generations. -/
theorem conway_evolve_two_blinkerH : conway.evolve 2 blinkerH = blinkerH := by
  rw [Rule.evolve_succ, Rule.evolve_one, conway_step_blinkerH, conway_step_blinkerV]

/-! ### Counterexamples to overbroad claims -/

/-- **Counterexample**: the step is not monotone. The block is a still life, but adding two
cells next to it kills the cell `(1, 0)` by overcrowding. -/
theorem not_monotone_conway_step :
    ¬ ∀ S T : Finset Cell, S ⊆ T → conway.step S ⊆ conway.step T := by
  intro h
  have hsub : block ⊆ block ∪ {(2, 0), (2, 1)} := subset_union_left
  have h1 : ((1, 0) : Cell) ∈ conway.step block := by
    rw [conway_step_block]
    simp [block]
  have h2 := h _ _ hsub h1
  simp [Rule.mem_step, liveNbrs_eq, block, conway] at h2

/-- **Counterexample**: the step is not injective. The empty configuration and a single cell
have the same successor. -/
theorem not_injective_conway_step : ¬ Function.Injective conway.step := by
  intro h
  have h1 : conway.step {((0, 0) : Cell)} = conway.step ∅ := by
    rw [conway_step_singleton, Rule.step_empty]
  exact singleton_ne_empty _ (h h1)

/-- **Counterexample**: the step is not additive on disjoint patterns that touch. Two cells and
a third adjacent cell each die when alone, but together they form a blinker. This is why
composition theorems need a separation hypothesis. -/
theorem not_additive_conway_step :
    ∃ S T : Finset Cell, Disjoint S T ∧
      conway.step (S ∪ T) ≠ conway.step S ∪ conway.step T := by
  refine ⟨{(-1, 0), (0, 0)}, {(1, 0)}, by simp, ?_⟩
  have hS : conway.step ({(-1, 0), (0, 0)} : Finset Cell) = ∅ :=
    conway_step_eq_empty_of_card_lt_three (by simp)
  have hU : ({(-1, 0), (0, 0)} ∪ {(1, 0)} : Finset Cell) = blinkerH := by
    ext ⟨x, y⟩
    simp [blinkerH]
  rw [hS, conway_step_singleton, hU, conway_step_blinkerH]
  intro h
  have h1 : ((0, 0) : Cell) ∈ blinkerV := by simp [blinkerV]
  rw [h] at h1
  simp at h1

/-! ### Symmetry -/

/-- A bijection of the grid that preserves the neighbour relation preserves live-neighbour
counts. -/
theorem liveNbrs_map (e : Cell ≃ Cell) (he : ∀ c d, e d ∈ nbrs (e c) ↔ d ∈ nbrs c)
    (S : Finset Cell) (c : Cell) :
    liveNbrs (S.map e.toEmbedding) (e c) = liveNbrs S c := by
  have h : (nbrs (e c)).filter (· ∈ S.map e.toEmbedding) =
      ((nbrs c).filter (· ∈ S)).map e.toEmbedding := by
    ext d
    obtain ⟨d, rfl⟩ := e.surjective d
    simp [he]
  rw [liveNbrs, h, card_map, liveNbrs]

/-- **Symmetry**: every bijection of the grid that preserves the neighbour relation commutes
with the step of every rule. -/
theorem Rule.step_map (R : Rule) (e : Cell ≃ Cell)
    (he : ∀ c d, e d ∈ nbrs (e c) ↔ d ∈ nbrs c) (S : Finset Cell) :
    R.step (S.map e.toEmbedding) = (R.step S).map e.toEmbedding := by
  ext c
  obtain ⟨c, rfl⟩ := e.surjective c
  simp [Rule.mem_step, liveNbrs_map e he]

/-- Translations preserve the neighbour relation. -/
theorem nbrs_addLeft (v c d : Cell) :
    Equiv.addLeft v d ∈ nbrs (Equiv.addLeft v c) ↔ d ∈ nbrs c := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨x, y⟩ := c
  obtain ⟨a, b⟩ := d
  simp only [mem_nbrs, Equiv.coe_addLeft, Prod.mk_add_mk, ne_eq, Prod.mk.injEq]
  omega

/-- The transposition `(x, y) ↦ (y, x)` preserves the neighbour relation. -/
theorem nbrs_prodComm (c d : Cell) :
    Equiv.prodComm ℤ ℤ d ∈ nbrs (Equiv.prodComm ℤ ℤ c) ↔ d ∈ nbrs c := by
  obtain ⟨x, y⟩ := c
  obtain ⟨a, b⟩ := d
  simp only [mem_nbrs, Equiv.prodComm_apply, Prod.swap_prod_mk, ne_eq, Prod.mk.injEq]
  omega

/-- The reflection `(x, y) ↦ (-x, y)`. -/
def reflectX : Cell ≃ Cell := (Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)

/-- The reflection `(x, y) ↦ (-x, y)` preserves the neighbour relation. -/
theorem nbrs_reflectX (c d : Cell) : reflectX d ∈ nbrs (reflectX c) ↔ d ∈ nbrs c := by
  obtain ⟨x, y⟩ := c
  obtain ⟨a, b⟩ := d
  simp only [reflectX, mem_nbrs, Equiv.prodCongr_apply, Prod.map_apply, Equiv.neg_apply,
    Equiv.refl_apply, ne_eq, Prod.mk.injEq]
  omega

/-- **Translation invariance** of every rule. -/
theorem Rule.step_translate (R : Rule) (v : Cell) (S : Finset Cell) :
    R.step (S.map (Equiv.addLeft v).toEmbedding) = (R.step S).map (Equiv.addLeft v).toEmbedding :=
  R.step_map _ (nbrs_addLeft v) S

/-- **Invariance under transposition** of every rule. -/
theorem Rule.step_transpose (R : Rule) (S : Finset Cell) :
    R.step (S.map (Equiv.prodComm ℤ ℤ).toEmbedding) =
      (R.step S).map (Equiv.prodComm ℤ ℤ).toEmbedding :=
  R.step_map _ nbrs_prodComm S

/-- **Invariance under reflection** of every rule. -/
theorem Rule.step_reflectX (R : Rule) (S : Finset Cell) :
    R.step (S.map reflectX.toEmbedding) = (R.step S).map reflectX.toEmbedding :=
  R.step_map _ nbrs_reflectX S

/-- The vertical blinker is the transpose of the horizontal one. -/
theorem blinkerV_eq_map_blinkerH :
    blinkerV = blinkerH.map (Equiv.prodComm ℤ ℤ).toEmbedding := by
  ext ⟨x, y⟩
  simp only [blinkerV, blinkerH, mem_insert, mem_singleton, Prod.mk.injEq, mem_map_equiv,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
  omega

/-- **Symmetry check on an instance**: the second half-period of the blinker follows from the
first by transposition, in agreement with the direct computation `conway_step_blinkerV`. -/
theorem conway_step_blinkerV_of_symmetry : conway.step blinkerV = blinkerH := by
  rw [blinkerV_eq_map_blinkerH, Rule.step_transpose, conway_step_blinkerH,
    blinkerV_eq_map_blinkerH, map_map]
  ext c
  simp

end LeanTheory.Life
