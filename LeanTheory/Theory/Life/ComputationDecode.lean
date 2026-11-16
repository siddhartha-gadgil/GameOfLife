/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Decision

/-!
# Reading a number off a configuration

Research note `N-23`. The output of a computation of the Life machine is the position of the
block of register `0` along its diagonal. This file defines the decoding and proves it computable.

* **The ray** of a base cell `(x₀, y₀)`: the cells `(x₀ + k, y₀ + k)`, `k : ℕ`.
* **The decoding** `readOut x₀ y₀ S`: the least `k` such that the cell `(x₀ + k, y₀ + k)` is alive
  in `S`, or `0` when no cell of the ray is alive. It reads nothing but the ray.
  `readOut_eq_of_block`: if the live cells of the ray are exactly `k = v` and `k = v + 1` (a block
  at position `v` sits on the ray), the decoding is `v`.
* **Computability.** Finite configurations are given to algorithms as window data
  (`WindowData`, `WindowData.cells`; every finite set of cells is some `w.cells`).
  `DecodeComputable decode` says that some computable `g : WindowData → ℕ` agrees with `decode`
  on the cells of every window. `readOut_computable`: `readOut x₀ y₀` is computable in this sense,
  through the explicit search `readRows` (a bounded search along the ray, testing bits of the
  rows), with `readRows_eq`.
* Primitive recursive facts about `ℤ` (`primrec_int_toNat`, `primrec_int_neg_toNat`), from the
  `Denumerable ℤ` encoding.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### The decoding -/

/-- The positions `k` of the ray of `(x₀, y₀)` whose cell `(x₀ + k, y₀ + k)` is alive in `S`. -/
def rayHits (x₀ y₀ : ℤ) (S : Finset Cell) : Finset ℕ :=
  (S.filter fun c => c.1 - c.2 = x₀ - y₀ ∧ x₀ ≤ c.1).image fun c => (c.1 - x₀).toNat

/-- **The decoding**: the least `k` such that the cell `(x₀ + k, y₀ + k)` is alive in `S`, or `0`
when no cell of the ray is alive. -/
def readOut (x₀ y₀ : ℤ) (S : Finset Cell) : ℕ :=
  if h : (rayHits x₀ y₀ S).Nonempty then (rayHits x₀ y₀ S).min' h else 0

/-- The positions of the ray hit by `S` are those whose cell is alive. -/
theorem mem_rayHits {x₀ y₀ : ℤ} {S : Finset Cell} {k : ℕ} :
    k ∈ rayHits x₀ y₀ S ↔ (x₀ + k, y₀ + k) ∈ S := by
  simp only [rayHits, mem_image, mem_filter]
  constructor
  · rintro ⟨c, ⟨hc, h1, h2⟩, rfl⟩
    have e : c = (x₀ + ((c.1 - x₀).toNat : ℕ), y₀ + ((c.1 - x₀).toNat : ℕ)) := by
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    rwa [← e]
  · intro h
    exact ⟨_, ⟨h, by simp, by simp⟩, by simp⟩

/-- The decoding is the least live position of the ray. -/
theorem readOut_eq_of_least {x₀ y₀ : ℤ} {S : Finset Cell} {k : ℕ} (hk : (x₀ + k, y₀ + k) ∈ S)
    (hmin : ∀ j < k, (x₀ + j, y₀ + j) ∉ S) : readOut x₀ y₀ S = k := by
  have hm : k ∈ rayHits x₀ y₀ S := mem_rayHits.2 hk
  rw [readOut, dite_eq_left ⟨k, hm⟩]
  refine le_antisymm (min'_le _ _ hm) (le_min' _ _ _ fun j hj => ?_)
  by_contra hlt
  exact hmin j (by omega) (mem_rayHits.1 hj)

/-- The decoding is `0` when no cell of the ray is alive. -/
theorem readOut_eq_zero {x₀ y₀ : ℤ} {S : Finset Cell} (h : ∀ k : ℕ, (x₀ + k, y₀ + k) ∉ S) :
    readOut x₀ y₀ S = 0 := by
  rw [readOut, dite_eq_right]
  rintro ⟨k, hk⟩
  exact h k (mem_rayHits.1 hk)

/-- **The decoding of a block on the ray**: if the live cells of the ray are exactly those at
`v` and `v + 1`, the decoding is `v`. -/
theorem readOut_eq_of_block {x₀ y₀ : ℤ} {S : Finset Cell} {v : ℕ}
    (h : ∀ k : ℕ, (x₀ + k, y₀ + k) ∈ S ↔ k = v ∨ k = v + 1) : readOut x₀ y₀ S = v :=
  readOut_eq_of_least ((h v).2 (Or.inl rfl)) fun j hj hm => by
    rcases (h j).1 hm with e | e <;> omega

/-- The block `ofRows (x₀ + v) (y₀ + v) [3, 3]` meets the ray of `(x₀, y₀)` exactly at `v` and
`v + 1`. -/
theorem mem_block_ray (x₀ y₀ : ℤ) (v k : ℕ) :
    (x₀ + k, y₀ + k) ∈ ofRows (x₀ + v) (y₀ + v) [3, 3] ↔ k = v ∨ k = v + 1 := by
  rw [mem_ofRows]
  simp only
  rw [show x₀ + (k : ℤ) - (x₀ + v) = (k : ℤ) - v by omega,
    show y₀ + (k : ℤ) - (y₀ + v) = (k : ℤ) - v by omega]
  simp only [bitAt]
  by_cases h1 : k < v
  · rw [rowZ_of_neg _ (by omega)]
    simp only [tb_zero, Bool.false_eq_true, false_iff]
    omega
  · obtain ⟨d, rfl⟩ : ∃ d, k = v + d := ⟨k - v, by omega⟩
    rw [show ((v + d : ℕ) : ℤ) - v = (d : ℤ) by push_cast; omega, rowZ_natCast, tb_natCast]
    rcases d with _ | _ | d
    · simp
    · simp [Nat.testBit_eq_decide_div_mod_eq]
    · simp only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (show [3, 3].length ≤ d + 2 by simp), Option.getD_none,
        Nat.zero_testBit, Bool.false_eq_true, false_iff]
      omega

/-! ### Primitive recursive facts about `ℤ` -/

/-- The `Denumerable ℤ` decoding is the inverse of `Equiv.intEquivNat`. -/
theorem ofNat_int_eq (n : ℕ) : Denumerable.ofNat ℤ n = Equiv.intEquivNat.symm n := rfl

/-- `Equiv.intEquivNat` sends `k ≥ 0` to `2 k`. -/
theorem intEquivNat_natCast (k : ℕ) : Equiv.intEquivNat (k : ℤ) = 2 * k := rfl

/-- `Equiv.intEquivNat` sends `-(k + 1)` to `2 k + 1`. -/
theorem intEquivNat_negSucc (k : ℕ) : Equiv.intEquivNat (Int.negSucc k) = 2 * k + 1 := by
  simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat]

/-- The `n`-th integer: `n / 2` for even `n`, `-(n / 2 + 1)` for odd `n`. -/
theorem ofNat_int_cases (n : ℕ) :
    (n % 2 = 0 ∧ Denumerable.ofNat ℤ n = ((n / 2 : ℕ) : ℤ)) ∨
      (n % 2 = 1 ∧ Denumerable.ofNat ℤ n = -((n / 2 : ℕ) : ℤ) - 1) := by
  rw [ofNat_int_eq]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · refine Or.inl ⟨by omega, ?_⟩
    rw [(Equiv.symm_apply_eq _).2 (intEquivNat_natCast k).symm]
    congr 1
    omega
  · refine Or.inr ⟨by omega, ?_⟩
    rw [(Equiv.symm_apply_eq _).2 (intEquivNat_negSucc k).symm, Int.negSucc_eq]
    have : (2 * k + 1) / 2 = k := by omega
    rw [this]
    omega

/-- **`Int.toNat` is primitive recursive.** -/
theorem primrec_int_toNat : Primrec fun z : ℤ => z.toNat := by
  refine Primrec.ofNat_iff.2 ((Primrec.ite
    (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0))
    (Primrec.nat_div.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)).of_eq fun n => ?_)
  rcases ofNat_int_cases n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [id, h1, h2] <;> simp <;> omega

/-- **`z ↦ (-z).toNat` is primitive recursive.** -/
theorem primrec_int_neg_toNat : Primrec fun z : ℤ => (-z).toNat := by
  refine Primrec.ofNat_iff.2 ((Primrec.ite
    (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0))
    (Primrec.const 0) (Primrec.succ.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))))
    |>.of_eq fun n => ?_)
  rcases ofNat_int_cases n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [id, h1, h2] <;> simp <;> omega

/-! ### The decoding on window data -/

/-- **The test of the search**: whether the cell `(x₀ + k, y₀ + k)` is alive in the window `w`,
computed on natural numbers (the offsets of the cell from the window origin, then a bit of a row).
-/
def rayTest (x₀ y₀ : ℤ) (w : WindowData) (k : ℕ) : Bool :=
  decide ((-x₀).toNat + w.1.toNat ≤ k + (x₀.toNat + (-w.1).toNat)) &&
    decide ((-y₀).toNat + w.2.1.toNat ≤ k + (y₀.toNat + (-w.2.1).toNat)) &&
    (w.2.2.getD (k + (y₀.toNat + (-w.2.1).toNat) - ((-y₀).toNat + w.2.1.toNat)) 0).testBit
      (k + (x₀.toNat + (-w.1).toNat) - ((-x₀).toNat + w.1.toNat))

/-- The bound of the search: no cell of the ray beyond it lies in the window. -/
def rayBound (y₀ : ℤ) (w : WindowData) : ℕ := w.2.2.length + ((-y₀).toNat + w.2.1.toNat)

/-- The first position of the ray below the bound whose cell is alive (or the bound). -/
def rayIdx (x₀ y₀ : ℤ) (w : WindowData) : ℕ :=
  (List.range (rayBound y₀ w)).findIdx (rayTest x₀ y₀ w)

/-- **The decoding on window data**: the first live position of the ray, or `0`. -/
def readRows (x₀ y₀ : ℤ) (w : WindowData) : ℕ :=
  if rayIdx x₀ y₀ w < rayBound y₀ w then rayIdx x₀ y₀ w else 0

/-- The test of the search is the membership of the ray cell. -/
theorem rayTest_iff (x₀ y₀ : ℤ) (w : WindowData) (k : ℕ) :
    rayTest x₀ y₀ w k = true ↔ (x₀ + k, y₀ + k) ∈ w.cells := by
  obtain ⟨x, y, rows⟩ := w
  rw [WindowData.cells, mem_ofRows]
  simp only [rayTest, bitAt, tb, rowZ, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hy : 0 ≤ y₀ + (k : ℤ) - y
  · by_cases hx : 0 ≤ x₀ + (k : ℤ) - x
    · rw [ite_eq_left hy, show (y₀ + (k : ℤ) - y).toNat = k + (y₀.toNat + (-y).toNat) -
          ((-y₀).toNat + y.toNat) by omega,
        show (x₀ + (k : ℤ) - x).toNat = k + (x₀.toNat + (-x).toNat) -
          ((-x₀).toNat + x.toNat) by omega]
      simp only [hx, true_and]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · intro h
        exact ⟨⟨by omega, by omega⟩, h⟩
    · simp only [hx, false_and, iff_false, not_and]
      intro h
      omega
  · rw [ite_eq_right hy]
    simp only [Nat.zero_testBit, Bool.false_eq_true, and_false, iff_false, not_and]
    intro _ h
    omega

/-- A live cell of the ray lies below the bound of the search. -/
theorem lt_rayBound {x₀ y₀ : ℤ} {w : WindowData} {k : ℕ} (h : rayTest x₀ y₀ w k = true) :
    k < rayBound y₀ w := by
  simp only [rayTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, h2⟩, h3⟩ := h
  have hne : w.2.2.getD (k + (y₀.toNat + (-w.2.1).toNat) - ((-y₀).toNat + w.2.1.toNat)) 0 ≠ 0 :=
    fun e => by rw [e, Nat.zero_testBit] at h3; cases h3
  have hlt : k + (y₀.toNat + (-w.2.1).toNat) - ((-y₀).toNat + w.2.1.toNat) < w.2.2.length := by
    by_contra hge
    exact hne (List.getD_eq_default _ _ (by omega))
  unfold rayBound
  omega

/-- **The search computes the decoding**: `readRows x₀ y₀ w = readOut x₀ y₀ w.cells`. -/
theorem readRows_eq (x₀ y₀ : ℤ) (w : WindowData) : readRows x₀ y₀ w = readOut x₀ y₀ w.cells := by
  by_cases h : ∃ k : ℕ, (x₀ + k, y₀ + k) ∈ w.cells
  · obtain ⟨k, hk⟩ := h
    have hkB := lt_rayBound ((rayTest_iff x₀ y₀ w k).2 hk)
    have hlt : rayIdx x₀ y₀ w < (List.range (rayBound y₀ w)).length :=
      List.findIdx_lt_length_of_exists ⟨k, List.mem_range.2 hkB, (rayTest_iff x₀ y₀ w k).2 hk⟩
    rw [List.length_range] at hlt
    rw [readRows, ite_eq_left hlt]
    refine (readOut_eq_of_least ?_ fun j hj hm => ?_).symm
    · have := List.findIdx_getElem (w := by rw [List.length_range]; exact hlt)
      rw [List.getElem_range] at this
      exact (rayTest_iff x₀ y₀ w _).1 this
    · have := List.not_of_lt_findIdx (xs := List.range (rayBound y₀ w))
        (p := rayTest x₀ y₀ w) (i := j) hj
      rw [List.getElem_range, (rayTest_iff x₀ y₀ w j).2 hm] at this
      cases this
  · simp only [not_exists] at h
    rw [readOut_eq_zero h, readRows, ite_eq_right]
    intro hlt
    have := List.findIdx_getElem (w := by rw [List.length_range]; exact hlt)
    rw [List.getElem_range] at this
    exact h _ ((rayTest_iff x₀ y₀ w _).1 this)

/-- The test of the search is primitive recursive. -/
theorem primrec_rayTest (x₀ y₀ : ℤ) : Primrec₂ (rayTest x₀ y₀) := by
  have hw1 : Primrec fun p : WindowData × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
  have hw2 : Primrec fun p : WindowData × ℕ => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hw3 : Primrec fun p : WindowData × ℕ => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec fun p : WindowData × ℕ => p.2 := Primrec.snd
  have hax : Primrec fun p : WindowData × ℕ => p.2 + (x₀.toNat + (-p.1.1).toNat) :=
    Primrec.nat_add.comp hk (Primrec.nat_add.comp (Primrec.const _)
      (primrec_int_neg_toNat.comp hw1))
  have hbx : Primrec fun p : WindowData × ℕ => (-x₀).toNat + p.1.1.toNat :=
    Primrec.nat_add.comp (Primrec.const _) (primrec_int_toNat.comp hw1)
  have hay : Primrec fun p : WindowData × ℕ => p.2 + (y₀.toNat + (-p.1.2.1).toNat) :=
    Primrec.nat_add.comp hk (Primrec.nat_add.comp (Primrec.const _)
      (primrec_int_neg_toNat.comp hw2))
  have hby : Primrec fun p : WindowData × ℕ => (-y₀).toNat + p.1.2.1.toNat :=
    Primrec.nat_add.comp (Primrec.const _) (primrec_int_toNat.comp hw2)
  have hrow : Primrec fun p : WindowData × ℕ =>
      p.1.2.2.getD (p.2 + (y₀.toNat + (-p.1.2.1).toNat) - ((-y₀).toNat + p.1.2.1.toNat)) 0 :=
    (Primrec.list_getD 0).comp hw3 (Primrec.nat_sub.comp hay hby)
  have hbit : Primrec fun p : WindowData × ℕ =>
      decide ((p.1.2.2.getD (p.2 + (y₀.toNat + (-p.1.2.1).toNat) -
        ((-y₀).toNat + p.1.2.1.toNat)) 0) / 2 ^ (p.2 + (x₀.toNat + (-p.1.1).toNat) -
          ((-x₀).toNat + p.1.1.toNat)) % 2 = 1) :=
    (PrimrecRel.decide Primrec.eq).comp (Primrec.nat_mod.comp (Primrec.nat_div.comp hrow
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
        (Primrec.nat_sub.comp hax hbx))) (Primrec.const 2)) (Primrec.const 1)
  have h1 := (PrimrecRel.decide Primrec.nat_le).comp hbx hax
  have h2 := (PrimrecRel.decide Primrec.nat_le).comp hby hay
  refine (Primrec.and.comp (Primrec.and.comp h1 h2) hbit).of_eq fun p => ?_
  simp only [rayTest, Nat.testBit_eq_decide_div_mod_eq]

/-- **The search is primitive recursive.** -/
theorem primrec_readRows (x₀ y₀ : ℤ) : Primrec (readRows x₀ y₀) := by
  have hB : Primrec (rayBound y₀) :=
    Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_add.comp (Primrec.const _)
        (primrec_int_toNat.comp (Primrec.fst.comp Primrec.snd)))
  have hI : Primrec (rayIdx x₀ y₀) :=
    Primrec.list_findIdx (Primrec.list_range.comp hB) (primrec_rayTest x₀ y₀)
  exact Primrec.ite (Primrec.nat_lt.comp hI hB) hI (Primrec.const 0)

/-- **Computable decoding**: a decoding `Finset Cell → ℕ` is computable when a computable function
of window data agrees with it on the cells of every window. (Every finite set of cells is the set
of cells of some window, `exists_ofRows`.) -/
def DecodeComputable (decode : Finset Cell → ℕ) : Prop :=
  ∃ g : WindowData → ℕ, Computable g ∧ ∀ w, g w = decode w.cells

/-- **The decoding is computable.** -/
theorem readOut_computable (x₀ y₀ : ℤ) : DecodeComputable (readOut x₀ y₀) :=
  ⟨readRows x₀ y₀, (primrec_readRows x₀ y₀).to_comp, readRows_eq x₀ y₀⟩

/-- Sanity: the decoding of a block at position `5` of the ray of `(0, 0)` is `5`. -/
theorem readOut_block_five : readOut 0 0 (ofRows 5 5 [3, 3]) = 5 := by
  refine readOut_eq_of_block fun k => ?_
  have := mem_block_ray 0 0 5 k
  simpa using this

/-- Sanity: the decoding of the empty configuration is `0`. -/
theorem readOut_empty (x₀ y₀ : ℤ) : readOut x₀ y₀ ∅ = 0 :=
  readOut_eq_zero fun _ => Finset.notMem_empty _

end LeanTheory.Life
