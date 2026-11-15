/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Route

/-!
# Routes: instances

Concrete stages for `Theory/Life/Route`, so that its hypotheses are not vacuous:

* `rf0Stage`: the reflector `reflector` (queen bee shuttle with block and eater) turning a glider
  flying down and to the left into one flying up and to the left, in `30` generations;
* `flightStage`: a glider flying freely is a stage with an empty piece;
* `rf0_route`: a route of one reflection followed by a flight, by `Stage.route_reaction`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- **Certificate**: the reflector at rest stays in its box. -/
theorem reflector_rest : Reaction reflector reflector 30 (fun _ => Box 0 22 2 10) := by
  rw [reflector]
  life_reaction

/-- **Certificate**: the reflection as a reaction with its box. -/
theorem reflector_relay :
    Reaction (reflector ∪ ofRows 20 0 [1, 5, 3]) (phase reflector 30 ∪ ofRows 11 (-4) [2, 3, 5])
      30 (fun _ => Box 0 22 (-4) 10) := by
  rw [phase, show 30 % 30 = 0 by norm_num, Rule.evolve_zero, reflector_union_in,
    reflector_union_out]
  life_reaction

/-- The reflector as a stage of a route. -/
def rf0Stage : Stage where
  G := reflector
  In := ofRows 20 0 [1, 5, 3]
  Out := ofRows 11 (-4) [2, 3, 5]
  Δ := 30
  B := Box 0 22 2 10
  R := Box 0 22 (-4) 10
  rest := reflector_rest
  relay := reflector_relay
  hBR := fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, by omega, h4⟩

/-- The empty configuration is a piece at rest with an empty box. -/
theorem empty_rest : Reaction (∅ : Finset Cell) ∅ 30 (fun _ => (∅ : Set Cell)) :=
  ⟨Rule.evolve_empty _ _, fun _ _ c hc => by simp at hc⟩

/-- **A flight as a stage**: a pattern `G` reaching `G'` in `n` generations inside a box. -/
def flightStage (G G' : Finset Cell) (n : ℕ) (R : Set Cell)
    (h : Reaction G G' n (fun _ => R)) : Stage where
  G := ∅
  In := G
  Out := G'
  Δ := n
  B := ∅
  R := R
  rest := empty_rest
  relay := by
    rw [phase, Rule.evolve_empty, empty_union, empty_union]
    exact h
  hBR := Set.empty_subset _

/-- The outgoing glider of the reflector flies up and to the left for 40 generations. -/
theorem rf0_out_flight :
    Reaction (ofRows 11 (-4) [2, 3, 5]) (ofRows 1 (-14) [2, 3, 5]) 40
      (fun _ => Box 1 13 (-14) (-2)) := by
  life_reaction

/-- **A route of two stages**: a reflection, then a free flight. -/
theorem rf0_route :
    Reaction (Stage.pieces [rf0Stage, flightStage _ _ _ _ rf0_out_flight] 0 ∪ rf0Stage.In)
      (Stage.pieces [rf0Stage, flightStage _ _ _ _ rf0_out_flight] 70 ∪ ofRows 1 (-14) [2, 3, 5])
      70 (fun _ => Stage.relayFoot [rf0Stage, flightStage _ _ _ _ rf0_out_flight]) :=
  Stage.route_reaction rf0Stage [flightStage _ _ _ _ rf0_out_flight]
    ⟨fun t ht => by
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨FarApart.empty_right 2 _,
        (Box.farApart (Or.inr (Or.inr (Or.inr (by norm_num)))) :
          FarApart 2 (Box 0 22 2 10) (Box 1 13 (-14) (-2))),
        FarApart.empty_right 2 _⟩, ⟨fun _ ht => by simp at ht, trivial⟩⟩
    ⟨rfl, trivial⟩

end LeanTheory.Life
