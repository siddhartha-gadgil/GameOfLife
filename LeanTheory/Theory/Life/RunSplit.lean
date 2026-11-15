/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Reactions

/-!
# Splitting a part off a run

Research note `N-22`. A generated run of the register circuit also carries its answer glider far
out (to the stations of the module and beyond); in the machine the answer must be handed over to
the stations while the circuit finishes its run. If a part `A` of a run evolves on its own inside
a footprint `Fa` that stays far from the footprint `G` of the rest, then the rest `C` evolves on
its own inside `G`, and the run is the union of the two evolutions.

* `Reaction.split`: from the joint reaction and the reaction of the part, the reaction of the
  rest and the decomposition of the end.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- **Splitting a run.** If `C ∪ A` evolves inside `G ∪ Fa`, the part `A` evolves on its own
inside `Fa`, `C` starts inside `G`, and at every generation `G` is far from `Fa` (distance `> 2`)
and from `Fa` one generation later (distance `> 1`), then `C` evolves on its own inside `G` and
the end of the run is the union of the two ends. -/
theorem Reaction.split {C A Q A' : Finset Cell} {n : ℕ} {G Fa : ℕ → Set Cell}
    (h : Reaction (C ∪ A) Q n (fun i => G i ∪ Fa i)) (hA : Reaction A A' n Fa)
    (hC : (C : Set Cell) ⊆ G 0) (hsep : ∀ i < n, FarApart 2 (G i) (Fa i))
    (hsep' : ∀ i < n, FarApart 1 (G i) (Fa (i + 1))) :
    Reaction C (conway.evolve n C) n G ∧ Q = conway.evolve n C ∪ A' := by
  -- the rest stays in `G` up to every generation `≤ n`
  have key : ∀ i ≤ n, ∀ k ≤ i, (conway.evolve k C : Set Cell) ⊆ G k := by
    intro i
    induction i with
    | zero =>
      intro _ k hk
      rw [Nat.le_zero.1 hk]
      simpa using hC
    | succ i ih =>
      intro hi k hk
      rcases Nat.lt_or_ge k (i + 1) with hlt | hge
      · exact ih (by omega) k (by omega)
      have hk1 : k = i + 1 := by omega
      subst hk1
      have hprev := ih (by omega)
      have hunion : conway.evolve (i + 1) (C ∪ A) =
          conway.evolve (i + 1) C ∪ conway.evolve (i + 1) A :=
        conway.evolve_union_of_forall_sep fun k hk =>
          (hsep k (by omega)).sep (hprev k (by omega)) (hA.subset k (by omega))
      intro c hc
      have hc' : c ∈ conway.evolve (i + 1) (C ∪ A) := by
        rw [hunion]
        exact mem_union_left _ hc
      rcases h.subset (i + 1) hi hc' with hG | hF
      · exact hG
      · rw [Rule.evolve_succ] at hc
        obtain ⟨d, hd, hnear⟩ := Rule.exists_mem_near_of_mem_step hc
        exact absurd hnear.symm (hsep' i (by omega) d (hprev i le_rfl hd) c hF)
  have hunion : conway.evolve n (C ∪ A) = conway.evolve n C ∪ conway.evolve n A :=
    conway.evolve_union_of_forall_sep fun k hk =>
      (hsep k hk).sep (key n le_rfl k hk.le) (hA.subset k hk.le)
  refine ⟨⟨rfl, fun i hi => key n le_rfl i hi⟩, ?_⟩
  rw [← h.evolve_eq, hunion, hA.evolve_eq]

end LeanTheory.Life
