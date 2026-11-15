/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RunFoot

/-!
# Regions of the generated runs as unions of components

Research note `N-22`. A single box around a whole run contains other pieces of the machine (the
reflector `RF_J`, the INC gate, stations): the region of a run is instead a union of a short list
of *components*, each a box in `x, y` intersected with a box in the diagonal coordinates (`BU`),
or the lanes of the register diagonal. A piece is far from the run as soon as it is far from every
component, which is a linear check.

* `BU`, `unionL`, `subset_unionL`, `mem_unionL`;
* `FarAll`, `farApart_unionL`: far from every component, hence from the region;
* `BU.farApart_box`, `regLanes_farApart_box`: the checks for one component;
* `box_subset_BU`, `boxUV_subset_BU`, `BU_subset_BU`: footprints inside a component.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- A component: a box in `x, y` intersected with a box in `u = x - y`, `v = x + y`. -/
def BU (a b lo hi U₁ U₂ V₁ V₂ : ℤ) : Set Cell := Box a b lo hi ∩ UVBox U₁ U₂ V₁ V₂

/-- The union of a list of sets. -/
def unionL : List (Set Cell) → Set Cell
  | [] => ∅
  | X :: L => X ∪ unionL L

/-- A member of the list lies in the union. -/
theorem mem_unionL {X : Set Cell} {c : Cell} : ∀ {L : List (Set Cell)}, X ∈ L → c ∈ X →
    c ∈ unionL L
  | _ :: _, .head _, hc => Or.inl hc
  | _ :: _, .tail _ hX, hc => Or.inr (mem_unionL hX hc)

/-- A set inside a member of the list lies in the union. -/
theorem subset_unionL {S X : Set Cell} {L : List (Set Cell)} (hX : X ∈ L) (h : S ⊆ X) :
    S ⊆ unionL L :=
  fun _ hc => mem_unionL hX (h hc)

/-- Every member of the list is far from `B`. -/
def FarAll (B : Set Cell) : List (Set Cell) → Prop
  | [] => True
  | X :: L => FarApart 2 X B ∧ FarAll B L

/-- **Far from every component, far from the region.** -/
theorem farApart_unionL {B : Set Cell} : ∀ {L : List (Set Cell)}, FarAll B L →
    FarApart 2 (unionL L) B
  | [], _ => fun _ h => h.elim
  | _ :: _, ⟨h, hL⟩ => fun c hc => hc.elim (h c) (farApart_unionL hL c)

/-- A component is far from a box separated from it in `x`, `y`, `u` or `v`. -/
theorem BU.farApart_box {a b lo hi U₁ U₂ V₁ V₂ a' b' lo' hi' : ℤ}
    (h : b + 2 < a' ∨ b' + 2 < a ∨ hi + 2 < lo' ∨ hi' + 2 < lo ∨
      U₂ + 4 < a' - hi' ∨ b' - lo' + 4 < U₁ ∨ V₂ + 4 < a' + lo' ∨ b' + hi' + 4 < V₁) :
    FarApart 2 (BU a b lo hi U₁ U₂ V₁ V₂) (Box a' b' lo' hi') := by
  rintro x ⟨⟨x1, x2, x3, x4⟩, x5, x6, x7, x8⟩ y ⟨y1, y2, y3, y4⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  omega

/-- The lanes of the register diagonal are far from a box below them in `v` or beside them in
`u`. -/
theorem regLanes_farApart_box {a b lo hi : ℤ}
    (h : b + hi + 4 < 354 ∨ -69 + 4 < a - hi ∨ b - lo + 4 < -113) :
    FarApart 2 regLanes (Box a b lo hi) := by
  rintro x ⟨x1, x2, x3⟩ y ⟨y1, y2, y3, y4⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  omega

/-- A box inside a component. -/
theorem box_subset_BU {a b lo hi a' b' lo' hi' U₁ U₂ V₁ V₂ : ℤ}
    (h : a' ≤ a ∧ b ≤ b' ∧ lo' ≤ lo ∧ hi ≤ hi' ∧ U₁ ≤ a - hi ∧ b - lo ≤ U₂ ∧ V₁ ≤ a + lo ∧
      b + hi ≤ V₂) :
    Box a b lo hi ⊆ BU a' b' lo' hi' U₁ U₂ V₁ V₂ := by
  rintro c ⟨c1, c2, c3, c4⟩
  exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega, by omega⟩

/-- A box intersected with a diagonal box, inside a component. -/
theorem boxUV_subset_BU {a b lo hi u₁ u₂ v₁ v₂ a' b' lo' hi' U₁ U₂ V₁ V₂ : ℤ}
    (h : a' ≤ a ∧ b ≤ b' ∧ lo' ≤ lo ∧ hi ≤ hi' ∧ U₁ ≤ u₁ ∧ u₂ ≤ U₂ ∧ V₁ ≤ v₁ ∧ v₂ ≤ V₂) :
    Box a b lo hi ∩ UVBox u₁ u₂ v₁ v₂ ⊆ BU a' b' lo' hi' U₁ U₂ V₁ V₂ := by
  rintro c ⟨⟨c1, c2, c3, c4⟩, c5, c6, c7, c8⟩
  exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega, by omega⟩

/-- The idle bundle of pieces whose boxes lie in members of a list lies in their union. -/
theorem Piece.bundle_F_subset_unionL {L : List Piece} {hL : L.Pairwise Piece.Sep} {s n s' : ℕ}
    {h : (n + s) % 30 = s'} {R : List (Set Cell)} (hB : BoxesIn (unionL R) L) (i : ℕ) :
    (Piece.bundle L hL s n s' h).F i ⊆ unionL R :=
  Piece.bundle_F_subset hB i

end LeanTheory.Life
