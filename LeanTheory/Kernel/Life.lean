/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Function.Iterate

/-!
# Kernel: Conway's Game of Life on finite configurations

This is a **kernel file**: it fixes the model that every statement about the Game of Life in
this library refers to. The model is a definition, not an empirical law, so there is no law
typeclass; the role of a law is played by the independent set-level specification
`Rule.stepSet`, against which the computable step is checked in `Sanity/Life`.

* `Cell`: a cell of the infinite grid `ℤ × ℤ`. Convention: the first coordinate `x` increases to
  the right (east) and the second coordinate `y` increases **downward** (south), as in the RLE
  pattern format.
* `nbrs c`: the eight Moore neighbours of `c`.
* A **configuration** is a `Finset Cell`, the set of live cells; only finitely many cells are
  alive at any time.
* `Rule`: a Life-like rule, given by the neighbour counts for birth and for survival. A rule
  never gives birth with zero live neighbours (`Rule.zero_notMem_birth`): otherwise a finite
  configuration would have an infinite successor.
* `conway`: Conway's rule B3/S23.
* `Rule.step R S`: one generation; `Rule.evolve R n S`: `n` generations.
* `Rule.stepSet R X`: the specification of one generation on an arbitrary set of live cells.

Scope: definitions and their immediate membership lemmas only. Named patterns, symmetry,
locality and simulation live in other layers.
-/

@[expose] public section

namespace LeanTheory.Life

/-- A cell of the infinite grid. The first coordinate increases to the right, the second
downward (the RLE convention). -/
abbrev Cell : Type := ℤ × ℤ

/-- The eight Moore neighbours of a cell: the cells at Chebyshev distance exactly one. -/
def nbrs (c : Cell) : Finset Cell :=
  (Finset.Icc (c.1 - 1) (c.1 + 1) ×ˢ Finset.Icc (c.2 - 1) (c.2 + 1)).erase c

/-- The number of live neighbours of `c` in the configuration `S`. -/
def liveNbrs (S : Finset Cell) (c : Cell) : ℕ := ((nbrs c).filter (· ∈ S)).card

/-- A Life-like rule: a dead cell with `n` live neighbours is born iff `n ∈ birth`, and a live
cell with `n` live neighbours survives iff `n ∈ survive`. Birth with zero live neighbours is
excluded, so that finite configurations have finite successors. -/
structure Rule where
  /-- The neighbour counts at which a dead cell becomes alive. -/
  birth : Finset ℕ
  /-- The neighbour counts at which a live cell stays alive. -/
  survive : Finset ℕ
  /-- No birth in empty surroundings. -/
  zero_notMem_birth : 0 ∉ birth

/-- Conway's rule B3/S23: birth with exactly three live neighbours, survival with two or
three. -/
def conway : Rule := ⟨{3}, {2, 3}, by simp⟩

/-- One generation of the rule `R` on the finite configuration `S`. Only the live cells and
their neighbours can be alive afterwards, so the result is computed by filtering that finite
set. -/
def Rule.step (R : Rule) (S : Finset Cell) : Finset Cell :=
  (S ∪ S.biUnion nbrs).filter fun c =>
    if c ∈ S then liveNbrs S c ∈ R.survive else liveNbrs S c ∈ R.birth

/-- `n` generations of the rule `R`. -/
def Rule.evolve (R : Rule) (n : ℕ) (S : Finset Cell) : Finset Cell := R.step^[n] S

/-- The number of live neighbours of `c` in an arbitrary set `X` of live cells. -/
noncomputable def liveNbrsSet (X : Set Cell) (c : Cell) : ℕ := ((nbrs c : Set Cell) ∩ X).ncard

/-- **Specification** of one generation on an arbitrary (possibly infinite) set of live cells,
for arbitrary birth and survival counts: the cell-by-cell statement of the rule. -/
def stepSetCore (birth survive : Finset ℕ) (X : Set Cell) : Set Cell :=
  {c | (c ∈ X ∧ liveNbrsSet X c ∈ survive) ∨ (c ∉ X ∧ liveNbrsSet X c ∈ birth)}

/-- **Specification** of one generation of the rule `R` on an arbitrary set of live cells. -/
def Rule.stepSet (R : Rule) (X : Set Cell) : Set Cell := stepSetCore R.birth R.survive X

/-- `d` is a neighbour of `c` iff it differs from `c` and both coordinates differ by at most
one. -/
theorem mem_nbrs {c d : Cell} :
    d ∈ nbrs c ↔ d ≠ c ∧ c.1 - 1 ≤ d.1 ∧ d.1 ≤ c.1 + 1 ∧ c.2 - 1 ≤ d.2 ∧ d.2 ≤ c.2 + 1 := by
  simp [nbrs, and_assoc]

/-- A cell is not its own neighbour. -/
theorem notMem_nbrs_self (c : Cell) : c ∉ nbrs c := by
  simp [nbrs]

/-- Being neighbours is symmetric. -/
theorem mem_nbrs_comm {c d : Cell} : d ∈ nbrs c ↔ c ∈ nbrs d := by
  simp only [mem_nbrs, ne_eq]
  constructor <;> rintro ⟨h, h1, h2, h3, h4⟩ <;> exact ⟨fun e => h e.symm, by omega, by omega,
    by omega, by omega⟩

/-- A cell has a live neighbour iff its live-neighbour count is nonzero. -/
theorem liveNbrs_ne_zero {S : Finset Cell} {c : Cell} :
    liveNbrs S c ≠ 0 ↔ ∃ d ∈ nbrs c, d ∈ S := by
  simp [liveNbrs, Finset.filter_eq_empty_iff]

/-- **The rule, cell by cell**: `c` is alive after one generation iff it was alive with a
surviving neighbour count, or dead with a birth neighbour count. -/
theorem Rule.mem_step {R : Rule} {S : Finset Cell} {c : Cell} :
    c ∈ R.step S ↔
      (c ∈ S ∧ liveNbrs S c ∈ R.survive) ∨ (c ∉ S ∧ liveNbrs S c ∈ R.birth) := by
  unfold Rule.step
  rw [Finset.mem_filter]
  by_cases hc : c ∈ S
  · simp [hc]
  · simp only [hc, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or,
      Finset.mem_union, Finset.mem_biUnion, and_iff_right_iff_imp]
    intro hb
    have hne : liveNbrs S c ≠ 0 := fun h0 => R.zero_notMem_birth (h0 ▸ hb)
    obtain ⟨d, hd, hdS⟩ := liveNbrs_ne_zero.1 hne
    exact ⟨d, hdS, mem_nbrs_comm.1 hd⟩

/-- Zero generations change nothing. -/
@[simp] theorem Rule.evolve_zero (R : Rule) (S : Finset Cell) : R.evolve 0 S = S := rfl

/-- One more generation, applied last. -/
theorem Rule.evolve_succ (R : Rule) (n : ℕ) (S : Finset Cell) :
    R.evolve (n + 1) S = R.step (R.evolve n S) :=
  Function.iterate_succ_apply' _ _ _

/-- One more generation, applied first. -/
theorem Rule.evolve_succ' (R : Rule) (n : ℕ) (S : Finset Cell) :
    R.evolve (n + 1) S = R.evolve n (R.step S) :=
  Function.iterate_succ_apply _ _ _

/-- One generation is `evolve 1`. -/
@[simp] theorem Rule.evolve_one (R : Rule) (S : Finset Cell) : R.evolve 1 S = R.step S := rfl

/-- Evolution composes: `m + n` generations are `n` generations followed by `m`. -/
theorem Rule.evolve_add (R : Rule) (m n : ℕ) (S : Finset Cell) :
    R.evolve (m + n) S = R.evolve m (R.evolve n S) :=
  Function.iterate_add_apply _ _ _ _

end LeanTheory.Life
