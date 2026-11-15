/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Chain

/-!
# Placed pieces and parts

Layer 1 of the assembly of the simulator (research note `N-22`).

* `Piece.place g v p`: the piece `g` translated by `v` and started at phase `p`;
* `Piece.ofList L hL B hB`: a list of pieces with pairwise separated boxes, all inside a box `B`,
  as one piece (a *part* of the machine: a unit, a module), with `B` as its box.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- A piece at any phase is periodic with its box. -/
theorem Piece.phase_rest (g : Piece) (p : ℕ) :
    Reaction (phase g.rest p) (phase g.rest p) 30 (fun _ => g.box) := by
  have h := phase_reaction g.rest_reaction p 30
  rwa [show phase g.rest (p + 30) = phase g.rest p by
    rw [phase, phase, show (p + 30) % 30 = p % 30 by omega]] at h

/-- **A placed piece**: the piece `g` translated by `v = (vx, vy)`, at phase `p`. -/
def Piece.place (g : Piece) (vx vy : ℤ) (p : ℕ) : Piece where
  rest := translate (vx, vy) (phase g.rest p)
  a := g.a + vx
  b := g.b + vx
  lo := g.lo + vy
  hi := g.hi + vy
  rest_reaction := by
    have h := (g.phase_rest p).translate (vx, vy)
    refine h.mono fun _ _ => ?_
    rw [Piece.box, image_add_box]

/-- The union of the rests of a list of pieces. -/
def Piece.restOf (L : List Piece) : Finset Cell := L.foldr (fun g s => g.rest ∪ s) ∅

/-- The idle bundle of a list of pieces over one period starts at the union of their rests. -/
theorem Piece.start_idle (L : List Piece) (h : (30 + 0) % 30 = 0) :
    Proc.start (L.map fun g => g.idle 0 30 0 h) = Piece.restOf L := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    simp only [List.map_cons, Proc.start_cons, Piece.restOf, List.foldr_cons, ih]
    rfl

/-- The idle bundle of a list of pieces over one period ends at the union of their rests. -/
theorem Piece.stop_idle (L : List Piece) (h : (30 + 0) % 30 = 0) :
    Proc.stop (L.map fun g => g.idle 0 30 0 h) = Piece.restOf L := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    simp only [List.map_cons, Proc.stop_cons, Piece.restOf, List.foldr_cons, ih]
    rfl

/-- The footprint of the idle bundle lies in any box containing every piece's box. -/
theorem Piece.foot_idle (L : List Piece) (h : (30 + 0) % 30 = 0) {B : Set Cell}
    (hB : ∀ g ∈ L, g.box ⊆ B) (i : ℕ) :
    Proc.foot (L.map fun g => g.idle 0 30 0 h) i ⊆ B := by
  induction L with
  | nil => exact Set.empty_subset _
  | cons g L ih =>
    exact Set.union_subset (hB g List.mem_cons_self)
      (ih fun g' hg' => hB g' (List.mem_cons_of_mem g hg'))

/-- **A part**: a list of pieces with pairwise separated boxes, all inside the box `Box a b lo hi`,
as one piece. -/
def Piece.ofList (L : List Piece) (hL : L.Pairwise Piece.Sep) (a b lo hi : ℤ)
    (hB : ∀ g ∈ L, g.box ⊆ Box a b lo hi) : Piece where
  rest := Piece.restOf L
  a := a
  b := b
  lo := lo
  hi := hi
  rest_reaction := by
    have h := (Piece.bundle L hL 0 30 0 (by norm_num)).reaction
    simp only [Piece.bundle] at h
    rw [Piece.start_idle, Piece.stop_idle] at h
    exact h.mono fun i _ => Piece.foot_idle L _ hB i

end LeanTheory.Life
