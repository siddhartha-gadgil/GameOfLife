/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Increment

/-!
# Decrement with a continue glider

The decrement of `Theory/Life/Decrement` with the fan-out of `Theory/Life/ContinueGlider` in
front: one control glider lowers the register by one, at any position `k ≥ 1`, **and** produces a
continue glider that can trigger the next component of a machine (research note `N-15`).

* `pull_reaction_quad`: the pulling salvo moves the block from every position `k` to `k - 1`
  and, on the way, stays in the quadrant `x ≥ 0`, `y ≥ 4`. The footprint bounds columns as well
  as rows: this is what allows a glider far to the left (the continue glider) to cross the rows
  of the register.
* `continueDecrement`: for every `k ≥ 1`,

  `conway.evolve (840 + 1170 + (k * 4 + 26))
     (pullGenerator ∪ fanOut ∪ cgControl ∪ registerBlock k) =
   conway.evolve (k * 4 + 26) pullGenerator ∪ registerBlock (k - 1) ∪
     (conway.evolve (k * 4 + 26) fanOut ∪ conway.evolve (k * 4 + 26) contEnd)`.

  The generator and the fan-out are in their cycles, the block is one step closer, and
  `contEnd` is the continue glider (`contEnd_evolve_four`: it travels down and to the left).

The proof composes three phases with the reaction calculus: the fan-out works beside the resting
generator and block; the generator works beside the block, the resting fan-out and the continue
glider in flight; the salvo acts on the block beside the resting generator, the resting fan-out
and the continue glider in flight. No new certificate of the large components is needed.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### Tools -/

/-- Being far apart from two sets, on the left. -/
theorem FarApart.union_left {r : ℕ} {A B C : Set Cell} (h₁ : FarApart r A C)
    (h₂ : FarApart r B C) : FarApart r (A ∪ B) C :=
  fun a ha => ha.elim (h₁ a) (h₂ a)

/-- The block at position `k` lies in the box of its four cells. -/
theorem counter_subset_box (k : ℤ) :
    (counter k : Set Cell) ⊆ Box (7 + k) (8 + k) (11 + k) (12 + k) := by
  intro c hc
  have h1 := le_of_mem_ofRows (mem_coe.1 hc)
  have h2 := snd_lt_of_mem_ofRows (mem_coe.1 hc)
  have h3 := fst_lt_of_mem_ofRows (w := 2) (by simp) (mem_coe.1 hc)
  simp only [List.length_cons, List.length_nil] at h2
  push_cast at h2 h3
  exact ⟨h1.1, by omega, h1.2, by omega⟩

/-- The register block at position `k` lies in its box. -/
theorem registerBlock_subset_box (k : ℤ) :
    (registerBlock k : Set Cell) ⊆ Box (58 + k) (59 + k) (154 + k) (155 + k) := by
  intro c hc
  rw [mem_coe, registerBlock, mem_translate] at hc
  obtain ⟨h1, h2, h3, h4⟩ := counter_subset_box k (mem_coe.2 hc)
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- In its first four generations the pulling salvo stays in the box `0 ≤ x ≤ 10`,
`5 ≤ y ≤ 9`. -/
theorem pullSalvo_subset_box (r : ℕ) (hr : r < 4) :
    (conway.evolve r pullSalvo : Set Cell) ⊆ Box 0 10 5 9 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- **Certificate**: the pull at position `0` stays in the box `0 ≤ x ≤ 14`, `4 ≤ y ≤ 12`. -/
theorem pull_zero_box :
    Reaction (pullSalvo ∪ counter 0) (counter (-1)) 26 (fun _ => Box 0 14 4 12) := by
  rw [pullSalvo_union_counter_zero, show counter (-1) = ofRows 6 10 [3, 3] by
    rw [counter]; norm_num]
  life_reaction

/-- **The pull, for every position, in a quadrant**: the salvo launched from its fixed place moves
the block from position `k` to position `k - 1`, leaving nothing else, and stays in the quadrant
`x ≥ 0`, `y ≥ 4`. -/
theorem pull_reaction_quad (k : ℕ) :
    Reaction (pullSalvo ∪ counter k) (counter (k - 1)) (k * 4 + 26)
      (fun _ => {c : Cell | 0 ≤ c.1 ∧ 4 ≤ c.2}) := by
  have hfly := (reaction_flight_box' (by norm_num) pullSalvo_evolve_four pullSalvo_subset_box
    (k * 4)).par ((counter_isStillLife k).reaction_box (counter_subset_box k) (k * 4))
    (fun i hi => by
      rw [image_add_box]
      refine Box.farApart ?_
      simp only [Prod.smul_snd, nsmul_eq_mul]
      have : i / 4 < k := by omega
      push_cast
      omega)
  rw [conway.evolve_mul_of_evolve_eq_translate pullSalvo_evolve_four, nsmul_one_one] at hfly
  have hz := pull_zero_box.translate ((k : ℤ), (k : ℤ))
  rw [translate_union, translate_counter, translate_counter, zero_add] at hz
  have e : (-1 : ℤ) + k = k - 1 := by omega
  rw [e] at hz
  refine (hfly.seq hz).mono fun i _ => ?_
  split_ifs
  · refine Set.union_subset ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      have h1 := hc.1
      have h2 := hc.2.2.1
      change 0 ≤ ((i / 4) • ((1, 1) : Cell) + c).1 ∧ 4 ≤ ((i / 4) • ((1, 1) : Cell) + c).2
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul]
      push_cast
      omega
    · intro c hc
      have h1 := hc.1
      have h2 := hc.2.2.1
      exact ⟨by omega, by omega⟩
  · rintro _ ⟨c, hc, rfl⟩
    have h1 := hc.1
    have h2 := hc.2.2.1
    change 0 ≤ (((k : ℤ), (k : ℤ)) + c).1 ∧ 4 ≤ (((k : ℤ), (k : ℤ)) + c).2
    simp only [Prod.fst_add, Prod.snd_add]
    omega

/-! ### The continue glider after the end of the generator's reaction -/

/-- The continue glider moves one cell down and to the left every four generations. -/
theorem contEnd_evolve_four : conway.evolve 4 contEnd = translate (-1, 1) contEnd := by
  rw [contEnd, translate_ofRows]
  life_cert

/-- In its first four generations the continue glider stays in a 4 × 3 box. -/
theorem contEnd_subset_box (r : ℕ) (hr : r < 4) :
    (conway.evolve r contEnd : Set Cell) ⊆ Box (-480) (-477) 177 179 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- Rearranging a union of four configurations. -/
theorem union_rearrange₀ (A B C D : Finset Cell) : A ∪ B ∪ C ∪ D = B ∪ C ∪ (A ∪ D) := by
  ext c
  simp only [mem_union]
  tauto

/-- Rearranging a union of five configurations. -/
theorem union_rearrange₁ (A B C D E : Finset Cell) :
    A ∪ B ∪ C ∪ (D ∪ E) = D ∪ B ∪ E ∪ (A ∪ C) := by
  ext c
  simp only [mem_union]
  tauto

/-! ### The decrement with a continue glider -/

set_option maxRecDepth 100000 in
/-- **Decrement with a continue glider.** For every position `k ≥ 1` of the register block, one
control glider sent into the assembly `pullGenerator ∪ fanOut` moves the block to position
`k - 1`; the generator and the fan-out are left in their cycles and the continue glider is in
flight; nothing else remains. -/
theorem continueDecrement (k : ℕ) (hk : 1 ≤ k) :
    conway.evolve (840 + 1170 + (k * 4 + 26))
        (pullGenerator ∪ fanOut ∪ cgControl ∪ registerBlock k) =
      conway.evolve (k * 4 + 26) pullGenerator ∪ registerBlock (k - 1) ∪
        (conway.evolve (k * 4 + 26) fanOut ∪ conway.evolve (k * 4 + 26) contEnd) := by
  have hBk : ∀ n, Reaction (registerBlock k) (registerBlock k) n
      (fun _ => Box (58 + k) (59 + k) (154 + k) (155 + k)) :=
    fun n => (registerBlock_isStillLife k).reaction_box (registerBlock_subset_box k) n
  -- phase A: the fan-out works beside the resting generator and block
  have h840 : conway.evolve 840 pullGenerator = pullGenerator :=
    conway.evolve_mul_of_evolve_eq pullGenerator_evolve_thirty 28
  have hA := fanOut_reaction.par ((reaction_of_periodic (by norm_num) pullGenerator_evolve_thirty
    pullGenerator_subset_box 840).par (hBk 840) (fun _ _ => Box.farApart (by omega)))
    (fun _ _ => FarApart.union_right (Box.farApart (by omega)) (Box.farApart (by omega)))
  rw [h840, union_rearrange₁] at hA
  -- phase B: the generator works beside the block, the resting fan-out and the continue glider
  have h1170 : conway.evolve 1170 fanOut = fanOut :=
    conway.evolve_mul_of_evolve_eq fanOut_evolve_thirty 39
  have hcs := reaction_flight_box' (by norm_num) contStart_evolve_four contStart_subset_box 1170
  have hFC := (reaction_of_periodic (by norm_num) fanOut_evolve_thirty fanOut_subset_box 1170).par
    hcs (fun i _ => by
      rw [image_add_box]
      refine Box.farApart ?_
      simp only [Prod.smul_snd, nsmul_eq_mul]
      push_cast
      omega)
  have hB := (pullGenerator_reaction.par (hBk 1170) (fun _ _ => Box.farApart (by omega))).par hFC
    (fun i _ => by
      rw [image_add_box]
      simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul]
      push_cast
      exact FarApart.union_left
        (FarApart.union_right (Box.farApart (by omega)) (Box.farApart (by omega)))
        (FarApart.union_right (Box.farApart (by omega)) (Box.farApart (by omega))))
  rw [h1170, contStart_evolve, union_assoc pullGenerator (translate (51, 143) pullSalvo)] at hB
  -- phase C: the salvo acts on the block beside the resting generator, the resting fan-out and
  -- the continue glider in flight
  have hS := (pull_reaction_quad k).translate (51, 143)
  rw [translate_union] at hS
  change Reaction (translate (51, 143) pullSalvo ∪ registerBlock k) (registerBlock (k - 1)) _ _
    at hS
  have hPS := (reaction_of_periodic (by norm_num) pullGenerator_evolve_thirty
    pullGenerator_subset_box (k * 4 + 26)).par hS (fun _ _ a ha _ ⟨c, hc, hb⟩ hn => by
      subst hb
      have h1 : 4 ≤ c.2 := hc.2
      have h2 : a.2 ≤ 132 := ha.2.2.2
      obtain ⟨-, -, h4, -⟩ := hn
      simp only [Prod.snd_add] at h4
      push_cast at h4
      omega)
  have hce := reaction_flight_box' (by norm_num) contEnd_evolve_four contEnd_subset_box
    (k * 4 + 26)
  have hFE := (reaction_of_periodic (by norm_num) fanOut_evolve_thirty fanOut_subset_box
    (k * 4 + 26)).par hce (fun i _ => by
      rw [image_add_box]
      refine Box.farApart ?_
      simp only [Prod.smul_snd, nsmul_eq_mul]
      push_cast
      omega)
  have hC := hPS.par hFE (fun i _ => by
    rw [image_add_box]
    simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul]
    push_cast
    refine FarApart.union_left
      (FarApart.union_right (Box.farApart (by omega)) (Box.farApart (by omega)))
      (FarApart.union_right ?_ ?_)
    · rintro _ ⟨c, hc, rfl⟩ b hb hn
      have h1 : 4 ≤ c.2 := hc.2
      have h2 : b.2 ≤ -122 := hb.2.2.2
      obtain ⟨-, -, -, h4⟩ := hn
      simp only [Prod.snd_add] at h4
      push_cast at h4
      omega
    · rintro _ ⟨c, hc, rfl⟩ b hb hn
      have h1 : 0 ≤ c.1 := hc.1
      have h2 := hb.2.1
      obtain ⟨-, h4, -, -⟩ := hn
      simp only [Prod.fst_add] at h4
      push_cast at h4 h2
      omega)
  have hAll := (hA.seq hB).seq hC
  rw [union_rearrange₀ pullGenerator fanOut cgControl (registerBlock k)]
  exact hAll.evolve_eq

end LeanTheory.Life
