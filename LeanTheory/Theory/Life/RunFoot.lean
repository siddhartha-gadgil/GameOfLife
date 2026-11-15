/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DiagProc

/-!
# Footprints of the generated runs

Research note `N-22` (item (e) of the `inc` activation). A generated run is a chain of segments,
each a reaction with the union of the footprints of its processes. To place a run in the machine
we need one fixed region containing the whole run: a box, together with the lanes of the register
diagonal for the operations of a register.

* `regLanes`: the lanes of the register diagonal beyond `x + y = 354` (module frame);
* `FootIn B l`: every process of a segment stays in `B`;
* `Reaction.ofFootIn`: a segment as a reaction with the constant footprint `B`;
* `Reaction.seqC`: chaining reactions with a constant footprint through a glue equality;
* `wStrip_subset_regLanes`: the strip of the diagonal lies in the lanes.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- The lanes of the register diagonal (frame of the register circuit) beyond `x + y = 354`. -/
def regLanes : Set Cell :=
  {c | -113 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ -69 ∧ 354 ≤ c.1 + c.2}

/-- The strip of the register diagonal lies in the lanes when its lower bound is `≥ 354`. -/
theorem wStrip_subset_regLanes {Vs Vb : ℤ} {j : ℕ} (h1 : -34 ≤ Vs + 2 * ((j / 4 : ℕ) : ℤ))
    (h2 : -34 ≤ Vb) : wStrip Vs Vb j ⊆ regLanes := by
  rintro c ⟨c1, c2, c3⟩
  refine ⟨c1, c2, ?_⟩
  rcases min_choice (Vs + 2 * ((j / 4 : ℕ) : ℤ)) Vb with hm | hm <;> rw [hm] at c3 <;> omega

/-- Every process of a list stays in `B` at every generation up to `n`. -/
def FootIn {n : ℕ} (B : Set Cell) : List (Proc n) → Prop
  | [] => True
  | p :: l => (∀ i ≤ n, p.F i ⊆ B) ∧ FootIn B l

/-- The union of the footprints lies in `B`. -/
theorem Proc.foot_subset_of_footIn {n : ℕ} {B : Set Cell} :
    ∀ (l : List (Proc n)), FootIn B l → ∀ i ≤ n, Proc.foot l i ⊆ B
  | [], _, _, _ => Set.empty_subset _
  | _ :: l, ⟨h, hl⟩, i, hi => Set.union_subset (h i hi) (Proc.foot_subset_of_footIn l hl i hi)

/-- **A segment with a constant footprint.** -/
theorem Reaction.ofFootIn {n : ℕ} {B : Set Cell} {l : List (Proc n)}
    (h : Reaction (Proc.start l) (Proc.stop l) n (Proc.foot l)) (hB : FootIn B l) :
    Reaction (Proc.start l) (Proc.stop l) n (fun _ => B) :=
  h.mono fun i hi => Proc.foot_subset_of_footIn l hB i hi

/-- **Chaining with a constant footprint** through a glue equality. -/
theorem Reaction.seqC {P Q Q' R : Finset Cell} {n m : ℕ} {B : Set Cell}
    (h : Reaction P Q n (fun _ => B)) (e : Q = Q') (h' : Reaction Q' R m (fun _ => B)) :
    Reaction P R (n + m) (fun _ => B) :=
  (h.seq_eq e h').mono fun i _ => by split_ifs <;> exact subset_rfl

/-- A reaction with the number of generations rewritten. -/
theorem Reaction.castN {P Q : Finset Cell} {n m : ℕ} {F : ℕ → Set Cell}
    (h : Reaction P Q n F) (e : n = m) : Reaction P Q m F :=
  e ▸ h

/-- A reaction with its start and end rewritten. -/
theorem Reaction.congrPQ {P Q P' Q' : Finset Cell} {n : ℕ} {F : ℕ → Set Cell}
    (h : Reaction P Q n F) (e : P = P') (e' : Q = Q') : Reaction P' Q' n F :=
  e ▸ e' ▸ h

/-- Every piece of a list has its box in `B`. -/
def BoxesIn (B : Set Cell) : List Piece → Prop
  | [] => True
  | g :: l => g.box ⊆ B ∧ BoxesIn B l

/-- Membership form of `BoxesIn`. -/
theorem BoxesIn.mem {B : Set Cell} : ∀ {l : List Piece}, BoxesIn B l → ∀ g ∈ l, g.box ⊆ B
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, hl⟩, g, .tail _ hg => BoxesIn.mem hl g hg

/-- The footprint of an idle bundle lies in any set containing every piece's box. -/
theorem Piece.bundle_F_subset {L : List Piece} {hL : L.Pairwise Piece.Sep} {s n s' : ℕ}
    {h : (n + s) % 30 = s'} {B : Set Cell} (hB : BoxesIn B L) (i : ℕ) :
    (Piece.bundle L hL s n s' h).F i ⊆ B := by
  change Proc.foot (L.map fun g => g.idle s n s' h) i ⊆ B
  have hB' := hB.mem
  clear hB hL
  induction L with
  | nil => exact Set.empty_subset _
  | cons g L ih =>
    exact Set.union_subset (hB' g List.mem_cons_self)
      (ih fun g' hg' => hB' g' (List.mem_cons_of_mem g hg'))

/-- A box inside a box, as a part of a union. -/
theorem box_subset_union_left {a b lo hi a' b' lo' hi' : ℤ} {R : Set Cell}
    (h : a' ≤ a ∧ b ≤ b' ∧ lo' ≤ lo ∧ hi ≤ hi') :
    Box a b lo hi ⊆ Box a' b' lo' hi' ∪ R :=
  (box_subset_box h.1 h.2.1 h.2.2.1 h.2.2.2).trans Set.subset_union_left

/-- A box inside a box. -/
theorem box_subset_of {a b lo hi a' b' lo' hi' : ℤ}
    (h : a' ≤ a ∧ b ≤ b' ∧ lo' ≤ lo ∧ hi ≤ hi') : Box a b lo hi ⊆ Box a' b' lo' hi' :=
  box_subset_box h.1 h.2.1 h.2.2.1 h.2.2.2

end LeanTheory.Life
