/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Boxes

/-!
# Elementary reactions

The elementary reactions of the machine design D1 (research notes `N-09`, `N-11`, `N-15`),
certified. The geometries were found by the project's own exhaustive search
(`scripts/life_search`, report `notes/research/reports/R-19-elementary-reactions.md`).

* **Absorption** `eater_absorbs_glider`: the eater destroys a glider and is restored (6
  generations).
* **Annihilation** `gliders_annihilate_perp` (two gliders at a right angle, 4 generations) and
  `gliders_annihilate_headOn` (3 generations).
* **Kickback** `glider_kickback`: two gliders at a right angle leave one glider travelling up
  and to the left (10 generations). `glider_turnRound`: a head-on collision leaves one glider
  travelling back on the lane the other came on (6 generations).
* **A shorter push** `shortPush`: a three-glider salvo moving the block by `(1, 1)` in 19
  generations.
* **Zero test.** `zeroTestGlider` travels down and to the left. If the block is at position `0`
  it is consumed and the block is displaced (`zeroTest_hit`, 9 generations); a second glider
  restores the block (`zeroTest_restore`, 20 generations). If the block is at any position
  `k ≥ 1` the test glider passes without interaction, at all times (`zeroTest_pass`). So the
  survival of the test glider tells whether the register is zero.
  `zeroTestSalvo_hit`: a salvo of three gliders that is destroyed by the block at position `0`
  and leaves the block where it is (33 generations) — a test that needs no restoring glider.

Tools: `diagCheck` and `sum_le_of_mem_ofRows` bound `x + y` on a window; `sep_of_sum_lt`
separates configurations lying on different anti-diagonals. These are what a glider travelling
down and to the left needs, since it keeps `x + y`.

**Sanity.** `zeroTest_hit_displaces` (a positive test moves the block, so the restoring glider
or the three-glider test is needed).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### Absorption, annihilation, kickback -/

/-- **Absorption**: the catalogue glider at the origin and the catalogue eater translated by
`(4, 4)`; after 6 generations only the eater is left. -/
theorem eater_absorbs_glider :
    conway.evolve 6 (ofRows 0 0 [2, 4, 7, 0, 48, 80, 64, 192]) = ofRows 4 4 [3, 5, 4, 12] := by
  life_cert

/-- The configuration of `eater_absorbs_glider` is the glider together with the eater. -/
theorem glider_union_eater :
    ofRows 0 0 [2, 4, 7, 0, 48, 80, 64, 192] =
      Pattern.glider ∪ translate (4, 4) Pattern.eater1 := by
  rw [Pattern.glider, Pattern.eater1, translate_ofRows,
    ofRows_eq_padRows (0 + 4) (0 + 4) 4 4 _ (by norm_num) (by norm_num), ← ofRows_orRows]
  rfl

/-- **Annihilation at a right angle**: the glider `ofRows 0 0 [2, 4, 7]` travelling down and to
the right and the glider `ofRows 4 1 [2, 1, 7]` travelling down and to the left destroy each
other in 4 generations. -/
theorem gliders_annihilate_perp : conway.evolve 4 (ofRows 0 0 [2, 36, 23, 112]) = ∅ := by
  life_cert

/-- **Head-on annihilation** in 3 generations. -/
theorem gliders_annihilate_headOn : conway.evolve 3 (ofRows 0 1 [114, 20, 39]) = ∅ := by
  life_cert

/-- **Kickback**: the glider `ofRows 0 0 [2, 4, 7]` and the glider `ofRows 2 5 [5, 3, 2]` at a
right angle leave, after 10 generations, the single glider `ofRows 1 2 [3, 5, 1]`, which travels
up and to the left. -/
theorem glider_kickback :
    conway.evolve 10 (ofRows 0 0 [2, 4, 7, 0, 0, 20, 12, 8]) = ofRows 1 2 [3, 5, 1] := by
  life_cert

/-- The glider left by the kickback travels up and to the left. -/
theorem kickback_glider_evolve_four :
    conway.evolve 4 (ofRows 1 2 [3, 5, 1]) = translate (-1, -1) (ofRows 1 2 [3, 5, 1]) := by
  rw [translate_ofRows]
  life_cert

/-- **Turn-round**: a head-on collision that leaves one glider, travelling back on the lane on
which the other glider came (6 generations). -/
theorem glider_turnRound :
    conway.evolve 6 (ofRows 2 0 [2, 4, 7, 0, 0, 3, 5, 1]) = ofRows 3 0 [2, 3, 5] := by
  life_cert

/-! ### A shorter push -/

/-- **A shorter push**: a three-glider salvo that moves a block (here the block
`ofRows 7 9 [3, 3]`) by `(1, 1)` in 19 generations, leaving nothing else. -/
theorem shortPush :
    conway.evolve 19 (ofRows 0 0 [20, 24, 8, 0, 64, 129, 230, 3, 0, 384, 384]) =
      ofRows 8 10 [3, 3] := by
  life_cert

/-! ### Anti-diagonals -/

/-- Boolean check that every cell of the window `(x, y, rows)` satisfies `x + y ≤ a`: row `i`
must fit in the columns up to `a - y - i`. -/
def diagCheck (x y : ℤ) (rows : List ℕ) (a : ℤ) : Bool :=
  (List.range rows.length).all fun i => decide (rows.getD i 0 < 2 ^ (a + 1 - x - y - i).toNat)

/-- **Soundness of `diagCheck`.** -/
theorem sum_le_of_mem_ofRows {x y a : ℤ} {rows : List ℕ} (h : diagCheck x y rows a = true)
    {c : Cell} (hc : c ∈ ofRows x y rows) : c.1 + c.2 ≤ a := by
  have hx := (le_of_mem_ofRows hc).1
  have hy := (le_of_mem_ofRows hc).2
  have hlen := snd_lt_of_mem_ofRows hc
  rw [mem_ofRows, bitAt] at hc
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c.1 - x by omega)
  obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c.2 - y by omega)
  rw [hj, hi, rowZ_natCast, tb_natCast] at hc
  simp only [diagCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have hr := h i (by omega)
  have h1 := Nat.ge_two_pow_of_testBit hc
  by_contra hcon
  have h2 : 2 ^ (a + 1 - x - y - i).toNat ≤ 2 ^ j :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Configurations on anti-diagonals more than four apart are at distance greater than two. -/
theorem sep_of_sum_lt {S T : Finset Cell} {a : ℤ} (hS : ∀ s ∈ S, s.1 + s.2 ≤ a)
    (hT : ∀ t ∈ T, a + 4 < t.1 + t.2) : Sep 2 S T := by
  intro s hs t ht hn
  have h1 := hS s hs
  have h2 := hT t ht
  obtain ⟨n1, n2, n3, n4⟩ := hn
  push_cast at n1 n2 n3 n4
  omega

/-! ### The zero test -/

/-- The test glider of the zero test; it travels down and to the left. -/
def zeroTestGlider : Finset Cell := ofRows 5 6 [2, 1, 7]

/-- The glider that restores the block after a positive zero test; it travels up and to the
right. -/
def zeroRestoreGlider : Finset Cell := ofRows 6 15 [2, 6, 5]

/-- The test glider moves one cell down and to the left every four generations. -/
theorem zeroTestGlider_evolve_four :
    conway.evolve 4 zeroTestGlider = translate (-1, 1) zeroTestGlider := by
  rw [zeroTestGlider, translate_ofRows]
  life_cert

/-- The test glider with the block at position `0`, as one window. -/
theorem zeroTestGlider_union_counter_zero :
    zeroTestGlider ∪ counter 0 = ofRows 5 6 [2, 1, 7, 0, 0, 12, 12] := by
  have hc : counter 0 = ofRows 5 6 (padRows 5 2 [3, 3]) := by
    rw [ofRows_padRows, counter]
    norm_num
  rw [hc, zeroTestGlider, ← ofRows_orRows]
  rfl

/-- **Zero test, register zero**: the block at position `0` consumes the test glider and is
displaced, in 9 generations. -/
theorem zeroTest_hit : conway.evolve 9 (zeroTestGlider ∪ counter 0) = ofRows 8 9 [3, 3] := by
  rw [zeroTestGlider_union_counter_zero]
  life_cert

/-- **Zero test with restoring glider**: with the restoring glider the block is back at position
`0` after 20 generations and nothing else is left. -/
theorem zeroTest_restore :
    conway.evolve 20 (ofRows 5 6 [2, 1, 7, 0, 0, 12, 12, 0, 0, 4, 12, 10]) = counter 0 := by
  life_cert

/-- The configuration of `zeroTest_restore` is the test glider, the block at position `0` and
the restoring glider. -/
theorem zeroTest_restore_eq_union :
    ofRows 5 6 [2, 1, 7, 0, 0, 12, 12, 0, 0, 4, 12, 10] =
      zeroTestGlider ∪ counter 0 ∪ zeroRestoreGlider := by
  have hr : zeroRestoreGlider = ofRows 5 6 (padRows 9 1 [2, 6, 5]) := by
    rw [ofRows_padRows, zeroRestoreGlider]
    norm_num
  rw [zeroTestGlider_union_counter_zero, hr, ← ofRows_orRows]
  rfl

/-- In its first four generations every cell of the test glider has `x + y ≤ 15`. -/
theorem zeroTestGlider_sum_le (r : ℕ) (hr : r < 4) :
    ∀ c ∈ conway.evolve r zeroTestGlider, c.1 + c.2 ≤ 15 := by
  interval_cases r <;> (life_eval; exact fun c hc => sum_le_of_mem_ofRows rfl hc)

/-- At every time every cell of the test glider has `x + y ≤ 15`: it stays on its
anti-diagonal. -/
theorem zeroTestGlider_evolve_sum_le (t : ℕ) :
    ∀ c ∈ conway.evolve t zeroTestGlider, c.1 + c.2 ≤ 15 := by
  intro c hc
  rw [evolve_eq_translate_mod zeroTestGlider_evolve_four, mem_translate] at hc
  have h := zeroTestGlider_sum_le (t % 4) (Nat.mod_lt _ (by norm_num)) _ hc
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul, mul_neg,
    mul_one] at h
  omega

/-- **Zero test, register not zero**: if the block is at a position `k ≥ 1` the test glider
passes it without any interaction, at all times. -/
theorem zeroTest_pass (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    conway.evolve n (zeroTestGlider ∪ counter k) =
      conway.evolve n zeroTestGlider ∪ counter k := by
  have hT : ∀ i, conway.evolve i (counter k) = counter k := (counter_isStillLife k).evolve
  have hsep : ∀ i < n, Sep 2 (conway.evolve i zeroTestGlider) (conway.evolve i (counter k)) := by
    intro i _
    rw [hT]
    refine sep_of_sum_lt (a := 15) (zeroTestGlider_evolve_sum_le i) fun c hc => ?_
    have h1 := (le_of_mem_ofRows hc).1
    have h2 := (le_of_mem_ofRows hc).2
    omega
  rw [conway.evolve_union_of_forall_sep hsep, hT]

/-- **A zero test without restoring glider**: three gliders that are all destroyed by the block
at position `0`, the block being back in place after 33 generations. -/
theorem zeroTestSalvo_hit :
    conway.evolve 33 (ofRows 5 (-2) [256, 1280, 770, 1, 7, 0, 0, 0, 4, 2, 14, 0, 0, 12, 12]) =
      counter 0 := by
  life_cert

/-! ### Sanity -/

/-- **Sanity** (the test changes the register it finds at zero): after a positive test the
block is not at position `0`, which is why a restoring glider, or the three-glider test, is
needed. -/
theorem zeroTest_hit_displaces : conway.evolve 9 (zeroTestGlider ∪ counter 0) ≠ counter 0 := by
  rw [zeroTest_hit, counter]
  intro h
  have h1 := (ofRows_inj (rows := [3, 3]) (rows' := [3, 3]) rfl rfl h).1
  omega

end LeanTheory.Life
