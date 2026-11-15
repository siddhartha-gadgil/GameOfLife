/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ContinueDecrement

/-!
# Networks of reactions: many independent processes side by side

A large circuit (research note `N-15`, the zero test `DZ2` of report `R-28`) cannot be certified
as one window. It is cut into time segments; in each segment the circuit is a list of independent
processes (an idle periodic piece, a glider in flight, a local reaction of a piece with a glider),
whose footprints stay pairwise far apart. This module provides the composition step:

* `Proc n`: a reaction of `n` generations packaged with its start, end and footprint;
* `Reaction.parList`: a list of processes with pairwise far apart footprints is a reaction of the
  union of their starts into the union of their ends, with the union of the footprints;
* `reaction_periodic_box`: an idle periodic piece, started at any phase, as a process.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- Nothing is far from the empty set. -/
theorem FarApart.empty_right (r : ℕ) (A : Set Cell) : FarApart r A ∅ :=
  fun _ _ _ h => h.elim

/-- A reaction of `n` generations, packaged with its start, its end and its footprint. -/
structure Proc (n : ℕ) where
  /-- The configuration at the start. -/
  P : Finset Cell
  /-- The configuration after `n` generations. -/
  Q : Finset Cell
  /-- The footprint at every generation. -/
  F : ℕ → Set Cell
  /-- The reaction. -/
  reaction : Reaction P Q n F

namespace Proc

variable {n : ℕ}

/-- The union of the starts of a list of processes. -/
def start (l : List (Proc n)) : Finset Cell := l.foldr (fun p s => p.P ∪ s) ∅

/-- The union of the ends of a list of processes. -/
def stop (l : List (Proc n)) : Finset Cell := l.foldr (fun p s => p.Q ∪ s) ∅

/-- The union of the footprints of a list of processes at generation `i`. -/
def foot (l : List (Proc n)) (i : ℕ) : Set Cell := l.foldr (fun p s => p.F i ∪ s) ∅

@[simp] theorem start_nil : start ([] : List (Proc n)) = ∅ := rfl
@[simp] theorem start_cons (p : Proc n) (l : List (Proc n)) :
    start (p :: l) = p.P ∪ start l := rfl
@[simp] theorem stop_nil : stop ([] : List (Proc n)) = ∅ := rfl
@[simp] theorem stop_cons (p : Proc n) (l : List (Proc n)) :
    stop (p :: l) = p.Q ∪ stop l := rfl
@[simp] theorem foot_nil (i : ℕ) : foot ([] : List (Proc n)) i = ∅ := rfl
@[simp] theorem foot_cons (p : Proc n) (l : List (Proc n)) (i : ℕ) :
    foot (p :: l) i = p.F i ∪ foot l i := rfl

/-- A set far from every footprint of a list is far from their union. -/
theorem farApart_foot {A : Set Cell} {i : ℕ} (l : List (Proc n))
    (h : ∀ p ∈ l, FarApart 2 A (p.F i)) : FarApart 2 A (foot l i) := by
  induction l with
  | nil => exact FarApart.empty_right 2 A
  | cons p l ih =>
    exact FarApart.union_right (h p List.mem_cons_self)
      (ih fun q hq => h q (List.mem_cons_of_mem p hq))

/-- Two processes run independently: their footprints stay far apart. -/
def Indep (p q : Proc n) : Prop := ∀ i < n, FarApart 2 (p.F i) (q.F i)

end Proc

/-- **Many processes side by side**: a list of processes whose footprints stay pairwise far apart
is a reaction of the union of their starts into the union of their ends. -/
theorem Reaction.parList {n : ℕ} (l : List (Proc n)) (h : l.Pairwise Proc.Indep) :
    Reaction (Proc.start l) (Proc.stop l) n (Proc.foot l) := by
  induction l with
  | nil => exact ⟨Rule.evolve_empty _ _, fun _ _ c hc => by simp at hc⟩
  | cons p l ih =>
    rw [List.pairwise_cons] at h
    exact p.reaction.par (ih h.2) fun i hi => Proc.farApart_foot l fun q hq => h.1 q hq i hi

/-- **An idle periodic piece, started at any phase**: a configuration of period `p` that stays in
a box during one period is, from any phase `s` and for any number of generations, a reaction with
that box as footprint. -/
theorem reaction_periodic_box {S : Finset Cell} {p : ℕ} {a b lo hi : ℤ} (hp : 0 < p)
    (h : conway.evolve p S = S) (hB : ∀ r < p, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi)
    (s n : ℕ) :
    Reaction (conway.evolve s S) (conway.evolve (n + s) S) n (fun _ => Box a b lo hi) :=
  ⟨by rw [Rule.evolve_add], fun i _ => by
    rw [← Rule.evolve_add, conway.evolve_mod_of_evolve_eq h]
    exact hB _ (Nat.mod_lt _ hp)⟩

/-- **A salvo acts at every position of the block, with a sharp footprint.** As
`salvo_quad_reaction`, but the footprint follows the salvo: until generation `k * 4` it is the
salvo's box moved along the diagonal together with the block's box, afterwards the box of the
reaction at position `0` moved to position `k`. -/
theorem salvo_track_reaction {S : Finset Cell} {a b lo hi za zb zlo zhi d : ℤ} {n : ℕ}
    (h4 : conway.evolve 4 S = translate (1, 1) S)
    (hB : ∀ r < 4, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi)
    (hz : Reaction (S ∪ counter 0) (counter d) n (fun _ => Box za zb zlo zhi))
    (hhi : hi ≤ 9) (k : ℕ) :
    Reaction (S ∪ counter k) (counter (d + k)) (k * 4 + n)
      (fun i => if i ≤ k * 4 then
        Box (a + ((i / 4 : ℕ) : ℤ)) (b + ((i / 4 : ℕ) : ℤ)) (lo + ((i / 4 : ℕ) : ℤ))
          (hi + ((i / 4 : ℕ) : ℤ)) ∪ Box (7 + k) (8 + k) (11 + k) (12 + k)
      else Box (za + k) (zb + k) (zlo + k) (zhi + k)) := by
  have hfly := (reaction_flight_box' (by norm_num) h4 hB (k * 4)).par
    ((counter_isStillLife k).reaction_box (counter_subset_box k) (k * 4))
    (fun i hi => by
      rw [image_add_box]
      refine Box.farApart ?_
      simp only [Prod.smul_snd, nsmul_eq_mul]
      have : i / 4 < k := by omega
      push_cast
      omega)
  rw [conway.evolve_mul_of_evolve_eq_translate h4, nsmul_one_one] at hfly
  have hz' := hz.translate ((k : ℤ), (k : ℤ))
  rw [translate_union, translate_counter, translate_counter, zero_add] at hz'
  refine (hfly.seq hz').mono fun i _ => ?_
  split_ifs
  · refine Set.union_subset_union ?_ le_rfl
    rw [image_add_box]
    rintro c ⟨h1, h2, h3, h4⟩
    simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul] at h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast at * <;> omega
  · rw [image_add_box]

end LeanTheory.Life
