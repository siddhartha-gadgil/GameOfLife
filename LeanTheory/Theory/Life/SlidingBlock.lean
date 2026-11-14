/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Guns

/-!
# Sliding block memory: the block reactions

A natural number can be stored as the position of a block on a diagonal; salvos of gliders move
the block one cell along the diagonal (research note `N-11`). This module proves the two
reactions for **every** position of the block, with the salvo launched from a fixed place:

* `pull`: the two-glider salvo `pullSalvo` moves the block from position `k` to `k - 1`
  (`conway.evolve (4 * k + 26) (pullSalvo ∪ counter k) = counter (k - 1)`);
* `push`: the three-glider salvo `pushSalvo` moves it from `k` to `k + 1`
  (`conway.evolve (4 * k + 32) (pushSalvo ∪ counter k) = counter (k + 1)`).

Nothing else is left after either reaction. The duration depends on `k`, because the salvo has
to fly to the block.

Each theorem combines one certificate at position `0` (`pull_zero`, `push_zero`) with a general
flight lemma: `evolve_flight` shows that a diagonally moving pattern and a still life below it
evolve independently for as long as a band of empty rows separates them. Translation
equivariance then gives all positions.

Scope: these are the bare reactions. A register of a machine also needs circuitry that produces
the salvos on demand and a test for zero; pulling at position `0` moves the block to position
`-1`, which a register must prevent. None of that is in this module.

Pattern data: the salvos are those of Figure 8.37 (b) and (c) of Johnston and Greene, *Conway's
Game of Life: Mathematics and Construction* (pattern file `synchronized_block_movers`), as
transcribed in `notes/research/reports/R-18-source-report.md` §4.1; (b) is attributed there to
Dean Hickerson (1990) and (c) to Paul Chapman (2004).

**Sanity.** `counter_injective` (different numbers are stored as different configurations),
`counter_isStillLife`, `pull_then_push` (the two operations are inverse to each other),
`pull_misplaced_block_ne` (a block off the diagonal is not pulled along it).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### Flight past a still life -/

/-- A pattern that reappears translated by `v` after `p` generations is, at every time, a
translate of one of its first `p` generations. -/
theorem evolve_eq_translate_mod {S : Finset Cell} {p : ℕ} {v : Cell}
    (h : conway.evolve p S = translate v S) (t : ℕ) :
    conway.evolve t S = translate ((t / p) • v) (conway.evolve (t % p) S) := by
  have ht : t = t % p + t / p * p := (Nat.mod_add_div' t p).symm
  conv_lhs => rw [ht]
  rw [Rule.evolve_add, conway.evolve_mul_of_evolve_eq_translate h, Rule.evolve_translate]

/-- **Flight lemma.** Let `S` move one cell diagonally (to the right and down) every four
generations and stay in the rows up to `Y` during its first four generations, and let `T` be a
still life in the rows from `L` on. As long as `Y + q + 2 ≤ L`, the two evolve independently
for `4 * q` generations: `S` flies `q` cells and `T` stays. -/
theorem evolve_flight {S T : Finset Cell} {Y L : ℤ}
    (hS : conway.evolve 4 S = translate (1, 1) S)
    (hY : ∀ r < 4, ∀ c ∈ conway.evolve r S, c.2 ≤ Y)
    (hT : conway.step T = T) (hL : ∀ c ∈ T, L ≤ c.2) (q : ℕ) (hq : Y + q + 2 ≤ L) :
    conway.evolve (4 * q) (S ∪ T) = translate ((q : ℤ), (q : ℤ)) S ∪ T := by
  have hT' : ∀ i, conway.evolve i T = T := fun i => by
    induction i with
    | zero => rfl
    | succ i ih => rw [Rule.evolve_succ, ih, hT]
  have hsep : ∀ i < 4 * q, Sep 2 (conway.evolve i S) (conway.evolve i T) := by
    intro i hi
    rw [hT']
    refine sep_of_snd_lt (a := Y + q - 1) ?_ ?_
    · intro c hc
      rw [evolve_eq_translate_mod hS, mem_translate] at hc
      have h := hY (i % 4) (Nat.mod_lt _ (by norm_num)) _ hc
      simp only [Prod.snd_sub, Prod.smul_snd, nsmul_eq_mul, mul_one] at h
      omega
    · intro c hc
      have h := hL c hc
      push_cast
      omega
  rw [conway.evolve_union_of_forall_sep hsep, hT', evolve_eq_translate_mod hS (4 * q)]
  simp

/-! ### The counter and the salvos -/

/-- The block storing the number `k`: the block whose upper left cell is `(7 + k, 11 + k)`.
(Integers are allowed so that the result of pulling at `0` can be stated.) -/
def counter (k : ℤ) : Finset Cell := ofRows (7 + k) (11 + k) [3, 3]

/-- The two-glider salvo that pulls the block by one cell.
```
.O........
..O.......
OOO....O.O
........OO
........O.
```
-/
def pullSalvo : Finset Cell := ofRows 0 5 [2, 4, 647, 768, 256]

/-- The three-glider salvo that pushes the block by one cell: the pulling salvo and one more
glider behind it.
```
..O.......
...O......
.OOO......
..........
..........
.O........
..O.......
OOO....O.O
........OO
........O.
```
-/
def pushSalvo : Finset Cell := ofRows 0 0 [4, 8, 14, 0, 0, 2, 4, 647, 768, 256]

/-- Moving a counter along the diagonal changes the stored number. -/
theorem translate_counter (a k : ℤ) : translate (a, a) (counter k) = counter (k + a) := by
  rw [counter, counter, translate_ofRows]
  congr 1 <;> omega

/-- The counter is a block, hence a still life. -/
theorem counter_isStillLife (k : ℤ) : IsStillLife (counter k) := by
  have h : counter k = translate (7 + k, 11 + k) Pattern.block := by
    rw [Pattern.block, translate_ofRows, counter, zero_add, zero_add]
  rw [h]
  exact Pattern.block_isStillLife.translate _

/-- The counter storing `k` lies in the rows from `11 + k` on. -/
theorem counter_snd (k : ℤ) : ∀ c ∈ counter k, 11 + k ≤ c.2 :=
  fun _ hc => (le_of_mem_ofRows hc).2

/-- **Sanity**: different numbers are stored as different configurations. -/
theorem counter_injective : Function.Injective counter := by
  intro j k h
  have h1 := (ofRows_inj (rows := [3, 3]) (rows' := [3, 3]) rfl rfl h).1
  omega

/-- The pulling salvo moves one cell diagonally every four generations. -/
theorem pullSalvo_evolve_four : conway.evolve 4 pullSalvo = translate (1, 1) pullSalvo := by
  rw [pullSalvo, translate_ofRows]
  life_cert

/-- The pushing salvo moves one cell diagonally every four generations. -/
theorem pushSalvo_evolve_four : conway.evolve 4 pushSalvo = translate (1, 1) pushSalvo := by
  rw [pushSalvo, translate_ofRows]
  life_cert

/-- In its first four generations the pulling salvo stays in the rows up to 9. -/
theorem pullSalvo_snd (r : ℕ) (hr : r < 4) : ∀ c ∈ conway.evolve r pullSalvo, c.2 ≤ 9 := by
  interval_cases r <;>
    (life_eval
     intro c hc
     have h2 := snd_lt_of_mem_ofRows hc
     simp only [List.length_cons, List.length_nil] at h2
     omega)

/-- In its first four generations the pushing salvo stays in the rows up to 9. -/
theorem pushSalvo_snd (r : ℕ) (hr : r < 4) : ∀ c ∈ conway.evolve r pushSalvo, c.2 ≤ 9 := by
  interval_cases r <;>
    (life_eval
     intro c hc
     have h2 := snd_lt_of_mem_ofRows hc
     simp only [List.length_cons, List.length_nil] at h2
     omega)

/-! ### The reactions -/

/-- **Certificate**: the pull at position `0`, 26 generations. -/
theorem pull_zero : conway.evolve 26 (pullSalvo ∪ counter 0) = counter (-1) := by
  have hc : counter 0 = ofRows 0 5 (padRows 6 7 [3, 3]) := by
    rw [ofRows_padRows, counter]
    norm_num
  have hU : pullSalvo ∪ counter 0 = ofRows 0 5 [2, 4, 647, 768, 256, 0, 384, 384] := by
    rw [hc, pullSalvo, ← ofRows_orRows]
    rfl
  rw [hU]
  life_cert

/-- **Certificate**: the push at position `0`, 32 generations. -/
theorem push_zero : conway.evolve 32 (pushSalvo ∪ counter 0) = counter 1 := by
  have hc : counter 0 = ofRows 0 0 (padRows 11 7 [3, 3]) := by
    rw [ofRows_padRows, counter]
    norm_num
  have hU : pushSalvo ∪ counter 0 =
      ofRows 0 0 [4, 8, 14, 0, 0, 2, 4, 647, 768, 256, 0, 384, 384] := by
    rw [hc, pushSalvo, ← ofRows_orRows]
    rfl
  rw [hU]
  life_cert

/-- **Decrement, for every position**: the pulling salvo, launched from its fixed place, moves
the block from position `k` to position `k - 1` and nothing else remains. -/
theorem pull (k : ℕ) :
    conway.evolve (4 * k + 26) (pullSalvo ∪ counter k) = counter (k - 1) := by
  rw [add_comm, Rule.evolve_add,
    evolve_flight pullSalvo_evolve_four pullSalvo_snd (counter_isStillLife k).2 (counter_snd k) k
      (by omega)]
  have h := translate_counter k 0
  rw [zero_add] at h
  rw [← h, ← translate_union, Rule.evolve_translate, pull_zero, translate_counter]
  exact congrArg counter (by omega)

/-- **Increment, for every position**: the pushing salvo, launched from its fixed place, moves
the block from position `k` to position `k + 1` and nothing else remains. -/
theorem push (k : ℕ) :
    conway.evolve (4 * k + 32) (pushSalvo ∪ counter k) = counter (k + 1) := by
  rw [add_comm, Rule.evolve_add,
    evolve_flight pushSalvo_evolve_four pushSalvo_snd (counter_isStillLife k).2 (counter_snd k) k
      (by omega)]
  have h := translate_counter k 0
  rw [zero_add] at h
  rw [← h, ← translate_union, Rule.evolve_translate, push_zero, translate_counter]
  exact congrArg counter (by omega)

/-! ### Sanity -/

/-- **Sanity** (the operations are inverse): pushing the block at position `k` and then pulling
it brings it back to position `k`. The second salvo is added when the first reaction is
over. -/
theorem pull_then_push (k : ℕ) :
    conway.evolve (4 * (k + 1) + 26)
        (pullSalvo ∪ conway.evolve (4 * k + 32) (pushSalvo ∪ counter k)) = counter k := by
  have h := pull (k + 1)
  rw [push]
  push_cast at h ⊢
  rw [h]
  exact congrArg counter (by omega)

/-- **Sanity** (rejected fixture): a block one cell to the right of the diagonal is not moved
to the corresponding place by the pulling salvo. -/
theorem pull_misplaced_block_ne :
    conway.evolve 26 (ofRows 0 5 [2, 4, 647, 768, 256, 0, 768, 768]) ≠ ofRows 7 10 [3, 3] := by
  life_eval
  exact ofRows_ne rfl rfl (by simp)

end LeanTheory.Life
