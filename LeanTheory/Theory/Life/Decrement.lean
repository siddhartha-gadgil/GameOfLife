/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.SalvoGenerator
public import LeanTheory.Theory.Life.Register

/-!
# A decrement component: one glider in, the register one lower

The first complete operation of the machine design D1 (research note `N-15`) on a register of
unbounded content, assembled with the reaction calculus from certified parts.

* `registerBlock k`: the block of the sliding block memory placed for the generator
  `pullGenerator`, at position `k`.
* `decrement_reaction`, `decrement`: for every `k ≥ 1`, the generator at rest, one control
  glider and the block at position `k` evolve, in `1170 + 4 * (k + 8)` generations, into the
  generator (somewhere in its cycle) and the block at position `k - 1`, and nothing else:

  `conway.evolve (1170 + 4 * (k + 8)) (pullGenerator ∪ pullGeneratorControl ∪ registerBlock k) =
     conway.evolve (4 * (k + 8)) pullGenerator ∪ registerBlock (k - 1)`.

  The statement holds for every position `k ≥ 1`, however far away the block is: the certified
  parts are the generator (`pullGenerator_reaction`, 1170 generations, one position) and the
  block reaction (`pull_zero`, 26 generations, one position); the flight of the salvo and the
  independence of the parts are theorems.
* `decrement_reaction` also gives a footprint for all intermediate generations: the box of the
  generator together with the rows `143` to `156 + k`.

Method: `Reaction.par` of the generator's reaction with the resting block (footprints far apart
because the block lies below the generator's box), then `Reaction.par` of the generator at rest
(`reaction_of_periodic`) with the flight and reaction of the salvo (`Op.reaction`, translated),
then `Reaction.seq`.

Not covered: `k = 0` (the block would then be within two rows of the generator's box; and a
register must not be decremented at zero anyway), repeated use, and the return of a signal.

**Sanity.** `decrement_one` (the instance `k = 1`), `registerBlock_injective`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- A pattern of period `p` that stays in a set `B` during one period is, for any number of
generations, a reaction with footprint `B`; it ends in the corresponding phase of its cycle. -/
theorem reaction_of_periodic {S : Finset Cell} {p : ℕ} {B : Set Cell} (hp : 0 < p)
    (h : conway.evolve p S = S) (hB : ∀ r < p, (conway.evolve r S : Set Cell) ⊆ B) (n : ℕ) :
    Reaction S (conway.evolve n S) n (fun _ => B) :=
  ⟨rfl, fun i _ => by
    rw [conway.evolve_mod_of_evolve_eq h i]
    exact hB _ (Nat.mod_lt _ hp)⟩

set_option maxRecDepth 100000 in
/-- At rest the generator stays in the box `-86 ≤ x ≤ 90`, `0 ≤ y ≤ 132`. -/
theorem pullGenerator_subset_box (r : ℕ) (hr : r < 30) :
    (conway.evolve r pullGenerator : Set Cell) ⊆ Box (-86) 90 0 132 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- The block of the register served by `pullGenerator`, at position `k`. -/
def registerBlock (k : ℤ) : Finset Cell := translate (51, 143) (counter k)

/-- The register block is a still life. -/
theorem registerBlock_isStillLife (k : ℤ) : IsStillLife (registerBlock k) :=
  (counter_isStillLife k).translate _

/-- The register block at position `k` lies in the rows `154 + k` and `155 + k`. -/
theorem registerBlock_snd (k : ℤ) :
    ∀ c ∈ registerBlock k, 154 + k ≤ c.2 ∧ c.2 ≤ 155 + k := by
  intro c hc
  rw [registerBlock, mem_translate] at hc
  have h1 := counter_snd k _ hc
  have h2 := counter_snd_le k _ hc
  simp only [Prod.snd_sub] at h1 h2
  omega

/-- **Sanity**: different positions of the register block are different configurations. -/
theorem registerBlock_injective : Function.Injective registerBlock :=
  fun _ _ h => counter_injective (translate_injective _ h)

/-- **The decrement as a reaction.** For every `k ≥ 1`: the generator, one control glider and
the block at position `k` evolve into the generator and the block at position `k - 1`; at every
generation on the way the configuration lies in the box of the generator or in the rows `143`
to `156 + k`. -/
theorem decrement_reaction (k : ℕ) (hk : 1 ≤ k) :
    Reaction (pullGenerator ∪ pullGeneratorControl ∪ registerBlock k)
      (conway.evolve (4 * (k + 8)) pullGenerator ∪ registerBlock (k - 1)) (1170 + 4 * (k + 8))
      (fun _ => Box (-86) 90 (-9) 152 ∪ {c : Cell | 143 ≤ c.2 ∧ c.2 ≤ 156 + (k : ℤ)}) := by
  -- the generator works while the block rests
  have hfarA : ∀ i < 1170, FarApart 2 (Box (-86) 90 (-9) 152)
      (registerBlock k : Set Cell) := by
    intro i _ a ha b hb hn
    have h1 := (registerBlock_snd k b (mem_coe.1 hb)).1
    have h2 : a.2 ≤ 152 := ha.2.2.2
    obtain ⟨-, -, h4, -⟩ := hn
    push_cast at h4
    omega
  have hA := pullGenerator_reaction.par ((registerBlock_isStillLife k).reaction 1170) hfarA
  -- the salvo flies and acts while the generator runs on
  have hop := (Op.reaction Op.dec k 0 k (by simp)).translate (51, 143)
  rw [Prod.mk_zero_zero, translate_zero, translate_union] at hop
  have hR := reaction_of_periodic (by norm_num) pullGenerator_evolve_thirty
    pullGenerator_subset_box (4 * (k + 8))
  have hfarB : ∀ i < 4 * (k + 8), FarApart 2 (Box (-86) 90 0 132)
      ((fun c : Cell => ((51, 143) : Cell) + c) ''
        {c : Cell | (0 : ℤ) ≤ c.2 ∧ 0 + ((i / 4 : ℕ) : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ (k : ℤ) + 13}) := by
    rintro i _ a ha _ ⟨c, hc, rfl⟩ hn
    have h1 : (0 : ℤ) ≤ c.2 := hc.1
    have h2 : a.2 ≤ 132 := ha.2.2.2
    obtain ⟨-, -, h4, -⟩ := hn
    simp only [Prod.snd_add] at h4
    push_cast at h4
    omega
  have hB := hR.par hop hfarB
  have e : pullGenerator ∪ translate (51, 143) pullSalvo ∪ registerBlock k =
      pullGenerator ∪ (translate (51, 143) Op.dec.salvo ∪ translate (51, 143) (counter k)) :=
    union_assoc _ _ _
  rw [e] at hA
  refine (hA.seq hB).mono fun i _ => ?_
  split_ifs
  · refine Set.union_subset Set.subset_union_left fun c hc => Or.inr ?_
    have h := registerBlock_snd k c (mem_coe.1 hc)
    exact ⟨by omega, by omega⟩
  · refine Set.union_subset ?_ ?_
    · exact (box_subset_box le_rfl le_rfl (by norm_num) (by norm_num)).trans
        Set.subset_union_left
    · rintro _ ⟨c, hc, rfl⟩
      refine Or.inr ⟨?_, ?_⟩
      · have h1 : (0 : ℤ) ≤ c.2 := hc.1
        simp only [Prod.snd_add]
        omega
      · have h3 : c.2 ≤ (k : ℤ) + 13 := hc.2.2
        simp only [Prod.snd_add]
        omega

/-- **The decrement.** For every position `k ≥ 1` of the block: one control glider sent into
the generator moves the block from position `k` to position `k - 1`; the generator is left in
its cycle and nothing else remains. -/
theorem decrement (k : ℕ) (hk : 1 ≤ k) :
    conway.evolve (1170 + 4 * (k + 8))
        (pullGenerator ∪ pullGeneratorControl ∪ registerBlock k) =
      conway.evolve (4 * (k + 8)) pullGenerator ∪ registerBlock (k - 1) :=
  (decrement_reaction k hk).evolve_eq

/-- **Sanity** (an instance): from position 1 the block is brought to position 0. -/
theorem decrement_one :
    conway.evolve 1206 (pullGenerator ∪ pullGeneratorControl ∪ registerBlock 1) =
      conway.evolve 36 pullGenerator ∪ registerBlock 0 :=
  decrement 1 le_rfl

end LeanTheory.Life
