/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.SlidingBlock

/-!
# Reactions with footprints

A first calculus for composing verified pieces of a configuration (research note `N-08`). A
**reaction** records what a pattern evolves into and where it is on the way:

* `Reaction P Q n F`: `conway.evolve n P = Q`, and at every generation `i ≤ n` the evolved
  pattern lies in the *footprint* `F i`, a set of cells.

Reactions compose:

* `Reaction.par`: two reactions of the same duration whose footprints stay at distance greater
  than two (`FarApart 2`) run side by side, with the union of the footprints;
* `Reaction.seq`: a reaction followed by a reaction from its result;
* `Reaction.translate`: a reaction can be moved anywhere;
* `Reaction.mono`: footprints can be enlarged.

Basic reactions: `IsStillLife.reaction` (a still life stays, with itself as footprint) and
`reaction_flight` (a pattern moving one cell diagonally every four generations, with a half
plane that follows it as footprint).

## Test of the calculus

`pull_reaction` rebuilds the decrement of the sliding block memory (`pull` of
`Theory/Life/SlidingBlock`) from these rules: the flight of the salvo in parallel with the
resting block, followed by the certified reaction at position `0`, translated. Besides the
result it gives a footprint for the whole operation, and `pull_reaction_snd_le` reads off that
the operation never touches the rows below `12 + k`.

Limitation: the footprints used here bound only the rows (`y`-coordinates). Rectangular
footprints need the column extent of each generation, which the evolution certificates do not
yet deliver.

**Sanity.** `not_farApart_fixture` (touching footprints are not far apart),
`not_reaction_blinker` (a reaction statement can be false: the blinker does not stay put),
`pull_reaction_evolve_eq` (the calculus reproduces `pull`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- Two sets of cells at Chebyshev distance greater than `r` from each other. -/
def FarApart (r : ℕ) (A B : Set Cell) : Prop := ∀ a ∈ A, ∀ b ∈ B, ¬ Near r a b

/-- Configurations inside sets that are far apart are separated. -/
theorem FarApart.sep {r : ℕ} {A B : Set Cell} {S T : Finset Cell} (h : FarApart r A B)
    (hS : (S : Set Cell) ⊆ A) (hT : (T : Set Cell) ⊆ B) : Sep r S T :=
  fun s hs t ht => h s (hS (mem_coe.2 hs)) t (hT (mem_coe.2 ht))

/-- Being far apart passes to subsets. -/
theorem FarApart.mono {r : ℕ} {A A' B B' : Set Cell} (h : FarApart r A B) (hA : A' ⊆ A)
    (hB : B' ⊆ B) : FarApart r A' B' :=
  fun a ha b hb => h a (hA ha) b (hB hb)

/-- A **reaction**: the configuration `P` evolves into `Q` in `n` generations, and at every
generation `i ≤ n` it lies in the footprint `F i`. -/
structure Reaction (P Q : Finset Cell) (n : ℕ) (F : ℕ → Set Cell) : Prop where
  /-- The result after `n` generations. -/
  evolve_eq : conway.evolve n P = Q
  /-- The footprint at every generation up to `n`. -/
  subset : ∀ i ≤ n, (conway.evolve i P : Set Cell) ⊆ F i

/-- Footprints can be enlarged. -/
theorem Reaction.mono {P Q : Finset Cell} {n : ℕ} {F F' : ℕ → Set Cell} (h : Reaction P Q n F)
    (hF : ∀ i ≤ n, F i ⊆ F' i) : Reaction P Q n F' :=
  ⟨h.evolve_eq, fun i hi => (h.subset i hi).trans (hF i hi)⟩

/-- **Parallel composition**: reactions whose footprints stay far apart run side by side. -/
theorem Reaction.par {P Q P' Q' : Finset Cell} {n : ℕ} {F F' : ℕ → Set Cell}
    (h : Reaction P Q n F) (h' : Reaction P' Q' n F')
    (hsep : ∀ i < n, FarApart 2 (F i) (F' i)) :
    Reaction (P ∪ P') (Q ∪ Q') n (fun i => F i ∪ F' i) := by
  have key : ∀ i ≤ n, conway.evolve i (P ∪ P') = conway.evolve i P ∪ conway.evolve i P' :=
    fun i hi => conway.evolve_union_of_forall_sep fun k hk =>
      (hsep k (by omega)).sep (h.subset k (by omega)) (h'.subset k (by omega))
  refine ⟨by rw [key n le_rfl, h.evolve_eq, h'.evolve_eq], fun i hi => ?_⟩
  rw [key i hi, coe_union]
  exact Set.union_subset_union (h.subset i hi) (h'.subset i hi)

/-- **Sequential composition**: a reaction followed by a reaction from its result. -/
theorem Reaction.seq {P Q R : Finset Cell} {n m : ℕ} {F G : ℕ → Set Cell}
    (h : Reaction P Q n F) (h' : Reaction Q R m G) :
    Reaction P R (n + m) (fun i => if i ≤ n then F i else G (i - n)) := by
  refine ⟨by rw [add_comm, Rule.evolve_add, h.evolve_eq, h'.evolve_eq], fun i hi => ?_⟩
  by_cases hin : i ≤ n
  · simp only [hin, ↓reduceIte]
    exact h.subset i hin
  · have e : conway.evolve i P = conway.evolve (i - n) Q := by
      rw [← h.evolve_eq, ← Rule.evolve_add]
      congr 1
      omega
    simp only [hin, ↓reduceIte]
    rw [e]
    exact h'.subset (i - n) (by omega)

/-- **Placement**: a reaction can be translated, with its footprint. -/
theorem Reaction.translate {P Q : Finset Cell} {n : ℕ} {F : ℕ → Set Cell}
    (h : Reaction P Q n F) (v : Cell) :
    Reaction (translate v P) (translate v Q) n (fun i => (fun c => v + c) '' F i) := by
  refine ⟨by rw [Rule.evolve_translate, h.evolve_eq], fun i hi c hc => ?_⟩
  rw [Rule.evolve_translate, mem_coe, mem_translate] at hc
  exact ⟨c - v, h.subset i hi (mem_coe.2 hc), by simp⟩

/-- A still life is a reaction of any duration with itself as footprint. -/
theorem IsStillLife.reaction {T : Finset Cell} (h : IsStillLife T) (n : ℕ) :
    Reaction T T n (fun _ => (T : Set Cell)) :=
  ⟨h.evolve n, fun i _ => by rw [h.evolve i]⟩

/-- **Flight as a reaction**: a pattern that moves one cell diagonally every four generations
and stays in the rows up to `Y` during its first four generations flies `q` cells in `4 * q`
generations, inside a half plane that advances one row every four generations. -/
theorem reaction_flight {S : Finset Cell} {Y : ℤ}
    (hS : conway.evolve 4 S = translate (1, 1) S)
    (hY : ∀ r < 4, ∀ c ∈ conway.evolve r S, c.2 ≤ Y) (q : ℕ) :
    Reaction S (translate ((q : ℤ), (q : ℤ)) S) (4 * q)
      (fun i => {c : Cell | c.2 ≤ Y + ((i / 4 : ℕ) : ℤ)}) := by
  refine ⟨?_, fun i _ c hc => ?_⟩
  · rw [evolve_eq_translate_mod hS (4 * q)]
    simp
  · rw [mem_coe, evolve_eq_translate_mod hS, mem_translate] at hc
    have h := hY (i % 4) (Nat.mod_lt _ (by norm_num)) _ hc
    simp only [Prod.snd_sub, Prod.smul_snd, nsmul_eq_mul, mul_one] at h
    change c.2 ≤ Y + ((i / 4 : ℕ) : ℤ)
    omega

/-! ### Test: the decrement of the sliding block memory -/

/-- The pulling salvo with the block at position `0`, as one window. -/
theorem pullSalvo_union_counter_zero :
    pullSalvo ∪ counter 0 = ofRows 0 5 [2, 4, 647, 768, 256, 0, 384, 384] := by
  have hc : counter 0 = ofRows 0 5 (padRows 6 7 [3, 3]) := by
    rw [ofRows_padRows, counter]
    norm_num
  rw [hc, pullSalvo, ← ofRows_orRows]
  rfl

/-- **Certificates**: the pull at position `0` as a reaction; throughout its 26 generations the
pattern stays in the rows 4 to 12. -/
theorem pull_zero_reaction :
    Reaction (pullSalvo ∪ counter 0) (counter (-1)) 26
      (fun _ => {c : Cell | 4 ≤ c.2 ∧ c.2 ≤ 12}) := by
  refine ⟨pull_zero, fun i hi => ?_⟩
  rw [pullSalvo_union_counter_zero]
  interval_cases i <;>
    (life_eval
     intro c hc
     have h1 := (le_of_mem_ofRows (mem_coe.1 hc)).2
     have h2 := snd_lt_of_mem_ofRows (mem_coe.1 hc)
     simp only [List.length_cons, List.length_nil] at h2
     change 4 ≤ c.2 ∧ c.2 ≤ 12
     omega)

/-- The footprint of the decrement at position `k`: during the flight of the salvo, a half plane
that follows the salvo together with the block; afterwards the rows `4 + k` to `12 + k`. -/
def pullFootprint (k : ℕ) (i : ℕ) : Set Cell :=
  if i ≤ 4 * k then {c : Cell | c.2 ≤ 9 + ((i / 4 : ℕ) : ℤ)} ∪ (counter k : Set Cell)
  else {c : Cell | 4 + (k : ℤ) ≤ c.2 ∧ c.2 ≤ 12 + (k : ℤ)}

/-- **The decrement as a composed reaction**: flight of the salvo beside the resting block,
then the certified reaction at position `0`, translated to position `k`. -/
theorem pull_reaction (k : ℕ) :
    Reaction (pullSalvo ∪ counter k) (counter (k - 1)) (4 * k + 26) (pullFootprint k) := by
  have hfar : ∀ i < 4 * k, FarApart 2 {c : Cell | c.2 ≤ 9 + ((i / 4 : ℕ) : ℤ)}
      (counter k : Set Cell) := by
    intro i hi a ha b hb hn
    have h1 : a.2 ≤ 9 + ((i / 4 : ℕ) : ℤ) := ha
    have h2 := counter_snd k b (mem_coe.1 hb)
    obtain ⟨-, -, h3, -⟩ := hn
    omega
  have hflight := (reaction_flight pullSalvo_evolve_four pullSalvo_snd k).par
    ((counter_isStillLife k).reaction (4 * k)) hfar
  have hz := pull_zero_reaction.translate ((k : ℤ), (k : ℤ))
  rw [translate_union, translate_counter, translate_counter, zero_add] at hz
  have he : (-1 : ℤ) + k = k - 1 := by omega
  rw [he] at hz
  refine (hflight.seq hz).mono fun i _ => ?_
  by_cases hik : i ≤ 4 * k
  · simp only [hik, ↓reduceIte, pullFootprint]
    exact subset_rfl
  · simp only [hik, ↓reduceIte, pullFootprint]
    rintro _ ⟨c, ⟨h1, h2⟩, rfl⟩
    change 4 + (k : ℤ) ≤ ((k : ℤ), (k : ℤ)).2 + c.2 ∧ ((k : ℤ), (k : ℤ)).2 + c.2 ≤ 12 + (k : ℤ)
    constructor <;> simp only <;> omega

/-- **Sanity** (the calculus reproduces `pull`). -/
theorem pull_reaction_evolve_eq (k : ℕ) :
    conway.evolve (4 * k + 26) (pullSalvo ∪ counter k) = counter (k - 1) :=
  (pull_reaction k).evolve_eq

/-- During the whole decrement at position `k` no cell below row `12 + k` is ever alive. -/
theorem pull_reaction_snd_le (k : ℕ) (i : ℕ) (hi : i ≤ 4 * k + 26) :
    ∀ c ∈ conway.evolve i (pullSalvo ∪ counter k), c.2 ≤ 12 + (k : ℤ) := by
  intro c hc
  have h := (pull_reaction k).subset i hi (mem_coe.2 hc)
  unfold pullFootprint at h
  split at h
  · rcases h with h | h
    · have h1 : c.2 ≤ 9 + ((i / 4 : ℕ) : ℤ) := h
      omega
    · have h1 := snd_lt_of_mem_ofRows (mem_coe.1 h)
      simp only [List.length_cons, List.length_nil] at h1
      omega
  · exact h.2

/-! ### Sanity -/

/-- **Sanity** (rejected fixture): footprints that touch are not far apart. -/
theorem not_farApart_fixture : ¬ FarApart 2 ({(0, 0)} : Set Cell) {(2, 0)} := by
  intro h
  exact h (0, 0) rfl (2, 0) rfl ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Sanity** (a reaction statement has content): the blinker does not stay as it is for one
generation, whatever the footprint. -/
theorem not_reaction_blinker (F : ℕ → Set Cell) :
    ¬ Reaction Pattern.blinker Pattern.blinker 1 F := by
  intro h
  exact Pattern.blinker_isOscillator.2.2 1 (by norm_num) (by norm_num) h.evolve_eq

end LeanTheory.Life
