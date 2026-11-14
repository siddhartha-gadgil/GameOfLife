/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.LifeSim
public import Mathlib.Computability.Halting

/-!
# Decision problems about finite configurations

The form in which the undecidability results about the Game of Life are stated (research note
`N-12`), and the reduction between the two forms. Nothing here asserts that the problems are
undecidable: that is the goal `G-7`.

* `WindowData`: a finite configuration as data, namely the origin and the rows of a window;
  `WindowData.cells` is the configuration. The type is `ℤ × ℤ × List ℕ`, so Mathlib's notions
  `Computable` and `ComputablePred` apply to it directly.
* `EverAlive c S`: the cell `c` is alive at some generation of the evolution of `S`.
* `not_computablePred_everAlive_of_family`: if for some *computable* family `f : ℕ → WindowData`
  it is undecidable whether the cell `c` is ever alive in the evolution of `f n`, then it is
  undecidable whether `c` is ever alive in the evolution of a given finite configuration.

The intended use: the family `f n` is the Life pattern of a fixed counter program started on the
input `n`, the cell `c` is a marker reached exactly when the program halts, and the hypothesis
comes from an undecidable halting problem.

**Sanity.** `everAlive_of_mem` and `not_everAlive_empty` (the predicate is neither always false
nor always true); `everAlive_iff_exists_window` (the predicate on data is the predicate on
configurations).
-/

@[expose] public section

namespace LeanTheory.Life

/-- A finite configuration as data: the origin `(x₀, y₀)` and the rows of a window. -/
abbrev WindowData : Type := ℤ × ℤ × List ℕ

/-- The configuration encoded by window data. -/
def WindowData.cells (w : WindowData) : Finset Cell := ofRows w.1 w.2.1 w.2.2

/-- The cell `c` is alive at some generation of the evolution of `S`. -/
def EverAlive (c : Cell) (S : Finset Cell) : Prop := ∃ t, c ∈ conway.evolve t S

/-- **Sanity**: a cell that is alive at the start is ever alive. -/
theorem everAlive_of_mem {c : Cell} {S : Finset Cell} (h : c ∈ S) : EverAlive c S :=
  ⟨0, h⟩

/-- **Sanity**: no cell is ever alive in the evolution of the empty configuration. -/
theorem not_everAlive_empty (c : Cell) : ¬ EverAlive c ∅ := by
  rintro ⟨t, ht⟩
  rw [Rule.evolve_empty] at ht
  exact Finset.notMem_empty c ht

/-- The predicate on window data, unfolded. -/
theorem everAlive_iff_exists_window (c : Cell) (w : WindowData) :
    EverAlive c w.cells ↔ ∃ t, c ∈ conway.evolve t (ofRows w.1 w.2.1 w.2.2) :=
  Iff.rfl

/-- **Reduction.** If, for a computable family of finite configurations, it is undecidable
whether the cell `c` is ever alive, then it is undecidable for finite configurations in
general. -/
theorem not_computablePred_everAlive_of_family (c : Cell) (f : ℕ → WindowData)
    (hf : Computable f) (hn : ¬ ComputablePred fun n : ℕ => EverAlive c (f n).cells) :
    ¬ ComputablePred fun w : WindowData => EverAlive c w.cells := by
  rintro ⟨D, h⟩
  exact hn ⟨fun n => D (f n), h.comp hf⟩

end LeanTheory.Life
