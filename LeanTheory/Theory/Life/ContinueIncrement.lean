/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.IncrementContinue

/-!
# Increment with a continue glider

The increment of `Theory/Life/Increment` with the fan-out of `Theory/Life/IncrementContinue` in
front: one control glider raises the register by one, at **every** position `k`, and produces a
continue glider that can trigger the next component (research note `N-15`). The push counterpart
of `Theory/Life/ContinueDecrement`.

* `push3_reaction_quad`: the pushing salvo moves the block from every position `k` to `k + 1`
  and stays in the quadrant `x ≥ -4`, `y ≥ -4` (column and row bounds).
* `continueIncrement`: for every `k`,

  `conway.evolve (450 + 450 + 1200 + (k * 4 + 32))
     (pushGenerator ∪ pushFan ∪ pushFanControl ∪ pushRegister k) =
   conway.evolve (k * 4 + 32) pushGenerator ∪ pushRegister (k + 1) ∪
     (conway.evolve (k * 4 + 32) pushFan ∪ conway.evolve (k * 4 + 32) pushContEnd)`.

The proof composes four phases with the reaction calculus, the register block resting beside the
first three: the fan-out emits the generator's control glider; the generator starts while the
fan-out finishes; the generator finishes while the continue glider flies; the salvo acts on the
block. No new certificate of a large component is needed.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- **The push, for every position, in a quadrant**: the salvo launched from its fixed place
moves the block from position `k` to position `k + 1`, leaving nothing else, and stays in the
quadrant `x ≥ -4`, `y ≥ -4`. -/
theorem push3_reaction_quad (k : ℕ) :
    Reaction (pushSalvo3 ∪ counter k) (counter (k + 1)) (k * 4 + 32)
      (fun _ => {c : Cell | -4 ≤ c.1 ∧ -4 ≤ c.2}) := by
  have hfly := (reaction_flight_box' (by norm_num) pushSalvo3_evolve_four pushSalvo3_subset_box
    (k * 4)).par ((counter_isStillLife k).reaction_box (counter_subset_box k) (k * 4))
    (fun i hi => by
      rw [image_add_box]
      refine Box.farApart ?_
      simp only [Prod.smul_snd, nsmul_eq_mul]
      have : i / 4 < k := by omega
      push_cast
      omega)
  rw [conway.evolve_mul_of_evolve_eq_translate pushSalvo3_evolve_four, nsmul_one_one] at hfly
  have hz := push3_zero_reaction.translate ((k : ℤ), (k : ℤ))
  rw [translate_union, translate_counter, translate_counter, zero_add] at hz
  have e : (1 : ℤ) + k = k + 1 := by omega
  rw [e] at hz
  refine (hfly.seq hz).mono fun i _ => ?_
  split_ifs
  · refine Set.union_subset ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      have h1 := hc.1
      have h2 := hc.2.2.1
      change -4 ≤ ((i / 4) • ((1, 1) : Cell) + c).1 ∧ -4 ≤ ((i / 4) • ((1, 1) : Cell) + c).2
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
    change -4 ≤ (((k : ℤ), (k : ℤ)) + c).1 ∧ -4 ≤ (((k : ℤ), (k : ℤ)) + c).2
    simp only [Prod.fst_add, Prod.snd_add]
    omega

/-- The register block of the push generator at position `k` lies in its box. -/
theorem pushRegister_subset_box (k : ℤ) :
    (pushRegister k : Set Cell) ⊆ Box (91 + k) (92 + k) (160 + k) (161 + k) := by
  intro c hc
  rw [mem_coe, pushRegister, mem_translate] at hc
  obtain ⟨h1, h2, h3, h4⟩ := counter_subset_box k (mem_coe.2 hc)
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The continue glider moves one cell down and to the left every four generations. -/
theorem pushContEnd_evolve_four :
    conway.evolve 4 pushContEnd = translate (-1, 1) pushContEnd := by
  rw [pushContEnd, translate_ofRows]
  life_cert

/-- In its first four generations the continue glider stays in a small box. -/
theorem pushContEnd_subset_box (r : ℕ) (hr : r < 4) :
    (conway.evolve r pushContEnd : Set Cell) ⊆ Box (-467) (-465) 176 179 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- Rearranging a union of four configurations. -/
theorem union_rearrange₂ (A B C D : Finset Cell) : A ∪ B ∪ (C ∪ D) = C ∪ B ∪ D ∪ A := by
  ext c
  simp only [mem_union]
  tauto

/-- Rearranging a union of four configurations. -/
theorem union_rearrange₃ (A B C D : Finset Cell) : A ∪ B ∪ C ∪ D = A ∪ (B ∪ C) ∪ D := by
  ext c
  simp only [mem_union]
  tauto

set_option maxRecDepth 100000 in
/-- **Increment with a continue glider.** For every position `k` of the register block, one
control glider sent into the assembly `pushGenerator ∪ pushFan` moves the block to position
`k + 1`; the generator and the fan-out are left in their cycles and the continue glider is in
flight; nothing else remains. -/
theorem continueIncrement (k : ℕ) :
    conway.evolve (450 + 450 + 1200 + (k * 4 + 32))
        (pushGenerator ∪ pushFan ∪ pushFanControl ∪ pushRegister k) =
      conway.evolve (k * 4 + 32) pushGenerator ∪ pushRegister (k + 1) ∪
        (conway.evolve (k * 4 + 32) pushFan ∪ conway.evolve (k * 4 + 32) pushContEnd) := by
  have hBk : ∀ n, Reaction (pushRegister k) (pushRegister k) n
      (fun _ => Box (91 + k) (92 + k) (160 + k) (161 + k)) :=
    fun n => ((counter_isStillLife k).translate _).reaction_box (pushRegister_subset_box k) n
  -- phase 1: the fan-out emits the generator's control glider
  have h450 : conway.evolve 450 pushGenerator = pushGenerator :=
    conway.evolve_mul_of_evolve_eq pushGenerator_evolve_thirty 15
  have h1 := pushFan_phase1.par ((reaction_of_periodic (by norm_num) pushGenerator_evolve_thirty
    pushGenerator_subset_box 450).par (hBk 450) (fun _ _ => Box.farApart (by omega)))
    (fun _ _ => FarApart.union_right (Box.farApart (by omega)) (Box.farApart (by omega)))
  rw [h450, union_rearrange₂ pushFanMid pushGeneratorControl pushGenerator (pushRegister k)] at h1
  -- phase 2: the generator starts, the fan-out finishes, the block rests
  have hfirst :=
    (pushGenerator_part_1.seq_const pushGenerator_part_2).seq_const pushGenerator_part_3
  rw [← pushGenerator_union_control] at hfirst
  have h2 := (hfirst.par (hBk 450) (fun _ _ => Box.farApart (by omega))).par pushFan_phase2
    (fun _ _ => FarApart.union_left
      (fun a ha b hb hn => by
        have h1 := ha.1
        have h2 := ha.2.2.1
        obtain ⟨-, n2, -, n4⟩ := hn
        rcases hb with hb | hb
        · push_cast at n2; omega
        · push_cast at n4; omega)
      (fun a ha b hb hn => by
        have h1 := ha.1
        have h2 := ha.2.2.1
        obtain ⟨-, n2, -, n4⟩ := hn
        rcases hb with hb | hb
        · push_cast at n2; omega
        · push_cast at n4; omega))
  -- phase 3: the generator finishes, the fan-out rests, the continue glider flies
  have h45 := pushGenerator_part_4.seq_const pushGenerator_part_5
  have h67 := pushGenerator_part_6.seq_const pushGenerator_part_7
  have h89 := pushGenerator_part_8.seq_const pushGenerator_part_9
  have h1011 := pushGenerator_part_10.seq_const pushGenerator_part_11
  have hrest := ((h45.seq_const h67).seq_const h89).seq_const h1011
  rw [← pushGenerator_union_salvo] at hrest
  have h1200 : conway.evolve 1200 pushFan = pushFan :=
    conway.evolve_mul_of_evolve_eq pushFan_evolve_thirty 40
  have hc := reaction_flight_box' (by norm_num) pushCont_evolve_four pushCont_subset_box 1200
  have hFC := (reaction_of_periodic (by norm_num) pushFan_evolve_thirty pushFan_subset_box
    1200).par hc (fun i _ => by
      rw [image_add_box]
      refine Box.farApart ?_
      simp only [Prod.smul_fst, nsmul_eq_mul]
      push_cast
      omega)
  have h3 := (hrest.par (hBk 1200) (fun _ _ => Box.farApart (by omega))).par hFC (fun i _ => by
    rw [image_add_box]
    simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul]
    push_cast
    exact FarApart.union_left
      (FarApart.union_right (Box.farApart (by omega)) (Box.farApart (by omega)))
      (FarApart.union_right (Box.farApart (by omega)) (Box.farApart (by omega))))
  rw [h1200, pushCont_evolve, union_assoc pushGenerator (translate (84, 149) pushSalvo3)] at h3
  -- phase 4: the salvo acts on the block; generator and fan-out rest; continue glider flies
  have hS := (push3_reaction_quad k).translate (84, 149)
  rw [translate_union] at hS
  change Reaction (translate (84, 149) pushSalvo3 ∪ pushRegister k) (pushRegister (k + 1)) _ _
    at hS
  have hPS := (reaction_of_periodic (by norm_num) pushGenerator_evolve_thirty
    pushGenerator_subset_box (k * 4 + 32)).par hS (fun _ _ a ha _ ⟨c, hc, hb⟩ hn => by
      subst hb
      have h1 : -4 ≤ c.2 := hc.2
      have h2 : a.2 ≤ 130 := ha.2.2.2
      obtain ⟨-, -, h4, -⟩ := hn
      simp only [Prod.snd_add] at h4
      push_cast at h4
      omega)
  have hce := reaction_flight_box' (by norm_num) pushContEnd_evolve_four pushContEnd_subset_box
    (k * 4 + 32)
  have hFE := (reaction_of_periodic (by norm_num) pushFan_evolve_thirty pushFan_subset_box
    (k * 4 + 32)).par hce (fun i _ => by
      rw [image_add_box]
      refine Box.farApart ?_
      simp only [Prod.smul_snd, nsmul_eq_mul]
      push_cast
      omega)
  have h4 := hPS.par hFE (fun i _ => by
    rw [image_add_box]
    simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul]
    push_cast
    refine FarApart.union_left
      (FarApart.union_right (Box.farApart (by omega)) (Box.farApart (by omega)))
      (FarApart.union_right ?_ ?_)
    · rintro _ ⟨c, hc, rfl⟩ b hb hn
      have h1 : -4 ≤ c.2 := hc.2
      have h2 : b.2 ≤ -143 := hb.2.2.2
      obtain ⟨-, -, -, h4⟩ := hn
      simp only [Prod.snd_add] at h4
      push_cast at h4
      omega
    · rintro _ ⟨c, hc, rfl⟩ b hb hn
      have h1 : -4 ≤ c.1 := hc.1
      have h2 := hb.2.1
      obtain ⟨-, h4, -, -⟩ := hn
      simp only [Prod.fst_add] at h4
      push_cast at h4 h2
      omega)
  have hAll := ((h1.seq h2).seq h3).seq h4
  rw [union_rearrange₀ pushGenerator pushFan pushFanControl (pushRegister k)]
  exact hAll.evolve_eq

end LeanTheory.Life
