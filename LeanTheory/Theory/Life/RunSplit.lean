/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RunRegion

/-!
# Splitting a part off a run

Research note `N-22`. A generated run of the register circuit also carries its answer glider far
out (to the stations of the module and beyond); in the machine the answer must be handed over to
the stations while the circuit finishes its run. If a part `A` of a run evolves on its own inside
a footprint `Fa` that stays far from the footprint `G` of the rest, then the rest `C` evolves on
its own inside `G`, and the run is the union of the two evolutions.

* `Reaction.split`: from the joint reaction and the reaction of the part, the reaction of the
  rest and the decomposition of the end;
* `FootInT`, `Reaction.ofFootInT`, `Reaction.seqT`: segments and chains with a time-dependent
  footprint (the region of the rest together with the moving box of the part);
* `Proc.start_subset_foot`, `FarApart.mono_radius`, `union_cancel_right`: small tools.
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

/-- Every process of a list stays in `T (i + o)` at its generation `i ≤ n`. -/
def FootInT {n : ℕ} (T : ℕ → Set Cell) (o : ℕ) : List (Proc n) → Prop
  | [] => True
  | p :: l => (∀ i ≤ n, p.F i ⊆ T (i + o)) ∧ FootInT T o l

/-- The union of the footprints lies in `T (i + o)`. -/
theorem Proc.foot_subset_of_footInT {n : ℕ} {T : ℕ → Set Cell} {o : ℕ} :
    ∀ (l : List (Proc n)), FootInT T o l → ∀ i ≤ n, Proc.foot l i ⊆ T (i + o)
  | [], _, _, _ => Set.empty_subset _
  | _ :: l, ⟨h, hl⟩, i, hi => Set.union_subset (h i hi) (Proc.foot_subset_of_footInT l hl i hi)

/-- **A segment with a time-dependent footprint**, starting at time `o`. -/
theorem Reaction.ofFootInT {n o : ℕ} {T : ℕ → Set Cell} {l : List (Proc n)}
    (h : Reaction (Proc.start l) (Proc.stop l) n (Proc.foot l)) (hT : FootInT T o l) :
    Reaction (Proc.start l) (Proc.stop l) n (fun i => T (i + o)) :=
  h.mono fun i hi => Proc.foot_subset_of_footInT l hT i hi

/-- **Chaining with a time-dependent footprint**: a reaction from time `o` for `n` generations,
then one from time `o + n`. -/
theorem Reaction.seqT {P Q Q' R : Finset Cell} {n m o : ℕ} {T : ℕ → Set Cell}
    (h : Reaction P Q n (fun i => T (i + o))) (e : Q = Q')
    (h' : Reaction Q' R m (fun i => T (i + (n + o)))) :
    Reaction P R (n + m) (fun i => T (i + o)) :=
  (h.seq_eq e h').mono fun i _ => by
    split_ifs with hi
    · exact subset_rfl
    · rw [show i - n + (n + o) = i + o by omega]

/-- The start of a list of processes lies in their footprint at generation `0`. -/
theorem Proc.start_subset_foot {n : ℕ} :
    ∀ (l : List (Proc n)), (Proc.start l : Set Cell) ⊆ Proc.foot l 0
  | [] => by simp [Proc.start]
  | p :: l => by
    rw [Proc.start_cons, Proc.foot_cons, coe_union]
    exact Set.union_subset_union (by simpa using p.reaction.subset 0 (Nat.zero_le _))
      (Proc.start_subset_foot l)

/-- The end of a list of processes lies in their footprint at generation `n`. -/
theorem Proc.stop_subset_foot {n : ℕ} :
    ∀ (l : List (Proc n)), (Proc.stop l : Set Cell) ⊆ Proc.foot l n
  | [] => by simp [Proc.stop]
  | p :: l => by
    rw [Proc.stop_cons, Proc.foot_cons, coe_union]
    refine Set.union_subset_union ?_ (Proc.stop_subset_foot l)
    rw [← p.reaction.evolve_eq]
    exact p.reaction.subset n le_rfl

/-- Far apart at a radius, far apart at a smaller one. -/
theorem FarApart.mono_radius {r s : ℕ} {A B : Set Cell} (h : FarApart s A B) (hrs : r ≤ s) :
    FarApart r A B :=
  fun a ha b hb hn => h a ha b hb (hn.mono hrs)

/-- Cancelling a common part disjoint from both sides. -/
theorem union_cancel_right {X Y A : Finset Cell} (h : X ∪ A = Y ∪ A) (hX : Disjoint X A)
    (hY : Disjoint Y A) : X = Y := by
  ext c
  constructor
  · intro hc
    have : c ∈ Y ∪ A := h ▸ mem_union_left A hc
    rcases mem_union.1 this with h1 | h1
    · exact h1
    · exact absurd h1 (disjoint_left.1 hX hc)
  · intro hc
    have : c ∈ X ∪ A := h.symm ▸ mem_union_left A hc
    rcases mem_union.1 this with h1 | h1
    · exact h1
    · exact absurd h1 (disjoint_left.1 hY hc)

end LeanTheory.Life
