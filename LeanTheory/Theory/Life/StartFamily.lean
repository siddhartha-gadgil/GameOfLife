/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.MachineState
public import LeanTheory.Theory.Life.DiagSmall
public import LeanTheory.Theory.Life.Guns
public import LeanTheory.Theory.Life.Decision

/-!
# The start configurations as a computable family of windows

Research note `N-22` (the `start` data of `not_computablePred_everAlive_of_simulator`): for every
counter program `p`, the start configurations `encM p (startM n)` form a computable family of
window data.

* **Every finite configuration is a window** (`exists_ofRows`): for every finite set of cells `S`
  and every point `(x₀, y₀)` there is a window `ofRows x y rows = S` with `x ≤ x₀`, `y ≤ y₀`.
* **The start configuration splits** (`encM_startM`): `encM p (startM n)` is a fixed part
  `startRest p` (the machine at phase `0`, the control at unit `0`, the empty registers
  `1, 2, …`) and the block of register `0`, the window `ofRows (blockX p + n) (blockY p + n)
  [3, 3]`, moving diagonally with `n`.
* **The family** (`exists_startFamily`): window data `f n = (X, Y, rows n)` with a fixed origin;
  for large `n` the block lies above the rows of the fixed part and `rows n` is an explicit list
  (`rows0 ++ zeros ++ [3 · 2 ^ (b + n), 3 · 2 ^ (b + n)]`), primitive recursive in `n`; the
  finitely many small `n` are read off a table.

**Sanity.** `ofRows_singleton` (a one-cell window is the cell), `orRows_replicate_append`
(the union of rows with rows above them is the concatenation).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

/-! ### Windows of finite sets -/

/-- **Sanity**: the window `[1]` is the single cell at its origin. -/
theorem ofRows_singleton (c : Cell) : ({c} : Finset Cell) = ofRows c.1 c.2 [1] := by
  ext ⟨a, b⟩
  rw [mem_singleton, mem_ofRows, bitAt, rowZ, tb]
  obtain ⟨c1, c2⟩ := c
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, rfl⟩
    simp
  · intro h
    by_cases hb : 0 ≤ b - c2
    · simp only [hb, ↓reduceIte] at h
      obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le hb
      rw [hi] at h
      rcases i with _ | i
      · simp only [Int.toNat_natCast, List.getD_cons_zero, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le h1
        rw [hj] at h2
        rcases j with _ | j
        · omega
        · simp [Nat.testBit_succ] at h2
      · simp at h
    · simp only [hb, ↓reduceIte, Nat.zero_testBit, Bool.and_false] at h
      exact absurd h Bool.false_ne_true

/-- **Every finite configuration is a window**, with its origin below and left of any given
point. -/
theorem exists_ofRows (S : Finset Cell) :
    ∀ x₀ y₀ : ℤ, ∃ (x y : ℤ) (rows : List ℕ), x ≤ x₀ ∧ y ≤ y₀ ∧ S = ofRows x y rows := by
  induction S using Finset.induction_on with
  | empty => exact fun x₀ y₀ => ⟨x₀, y₀, [], le_rfl, le_rfl, (ofRows_nil x₀ y₀).symm⟩
  | @insert c S _ ih =>
    intro x₀ y₀
    obtain ⟨x, y, rows, hx, hy, hS⟩ := ih (min x₀ c.1) (min y₀ c.2)
    refine ⟨x, y, orRows (padRows (c.2 - y).toNat (c.1 - x).toNat [1]) rows,
      le_trans hx (min_le_left _ _), le_trans hy (min_le_left _ _), ?_⟩
    have hx' := min_le_right x₀ c.1
    have hy' := min_le_right y₀ c.2
    rw [ofRows_orRows, ← ofRows_eq_padRows' x y c.1 c.2 _ _ [1] (by omega) (by omega),
      ← ofRows_singleton, ← hS, insert_eq]

/-- **Sanity**: rows followed, above them, by further rows: their union is their
concatenation. -/
theorem orRows_replicate_append (A L : List ℕ) (k : ℕ) (h : A.length ≤ k) :
    orRows A (List.replicate k 0 ++ L) = A ++ List.replicate (k - A.length) 0 ++ L := by
  induction A generalizing k with
  | nil => simp [orRows]
  | cons a A ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at h; omega⟩
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    rw [List.replicate_succ, List.cons_append, orRows, Nat.or_zero, ih k h]
    simp

namespace LP

/-! ### The start configuration -/

/-- The `x` of the block of register `0` holding `0`. -/
def blockX (p : Program) : ℤ := 155 + modDX p 0

/-- The `y` of the block of register `0` holding `0`. -/
def blockY (p : Program) : ℤ := 251 + modDY p 0

/-- The diagonal of register `0` holding `n` is the block moved by `(n, n)`. -/
theorem regAt_zero_ofNat (p : Program) (n : ℕ) :
    regAt p 0 (RegS.ofNat n) = ofRows (blockX p + n) (blockY p + n) [3, 3] := by
  have h : conway.evolve (RegS.ofNat n).m (diagW (RegS.ofNat n).q (RegS.ofNat n).K) =
      reg1Block n := RegS.diagW_block n 0 0
  rw [regAt, h, reg1Block, counter, translate_ofRows, translate_ofRows, blockX, blockY]
  congr 1 <;> ring

/-- The empty diagonals of the registers `1 … k`. -/
def restRegs (p : Program) (k : ℕ) : Finset Cell :=
  ((List.range k).map Nat.succ).foldr (fun r S => regAt p r (RegS.ofNat 0) ∪ S) ∅

/-- **The fixed part of the start configurations**: the machine at phase `0`, the control at the
entrance of unit `0`, and the empty registers other than `0`. -/
def startRest (p : Program) : Finset Cell :=
  machAt p 0 ∪ ctrlAt p 0 ∪ restRegs p (numRegs p - 1)

/-- **The start configuration splits** into the fixed part and the block of register `0`. -/
theorem encM_startM (p : Program) (n : ℕ) :
    encM p (startM n) = startRest p ∪ ofRows (blockX p + n) (blockY p + n) [3, 3] := by
  obtain ⟨k, hk⟩ : ∃ k, numRegs p = k + 1 := ⟨numRegs p - 1, by
    have := le_max_left 1 ((p.map regBound).foldr max 0)
    unfold numRegs
    omega⟩
  have hrest : ((List.range k).map Nat.succ).foldr
      (fun r S => regAt p r ((startM n).reg r) ∪ S) ∅ = restRegs p k := by
    simp only [restRegs, List.foldr_map]
    rfl
  have h0 : (startM n).reg 0 = RegS.ofNat n := by simp [startM]
  rw [encM, regsAt, hk, List.range_succ_eq_map, List.foldr_cons, hrest, h0, regAt_zero_ofNat,
    startRest, hk, Nat.add_sub_cancel]
  change machAt p 0 ∪ ctrlAt p 0 ∪ _ = _
  ac_rfl

/-! ### The family -/

/-- A list of `m` zeros, in the form used for computability. -/
theorem map_range_zero (m : ℕ) : (List.range m).map (fun _ => 0) = List.replicate m 0 := by
  simp

/-- `2 ^ k` is primitive recursive in `k`. -/
theorem primrec_two_pow : Primrec fun k : ℕ => 2 ^ k :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id

/-- **The start configurations form a computable family of windows**: for every program `p`
there is a computable `f : ℕ → WindowData` with `(f n).cells = encM p (startM n)`. -/
theorem exists_startFamily (p : Program) :
    ∃ f : ℕ → WindowData, Computable f ∧ ∀ n, (f n).cells = encM p (startM n) := by
  obtain ⟨X, Y, rows0, hX, hY, hF⟩ := exists_ofRows (startRest p) (blockX p) (blockY p)
  set a := (blockY p - Y).toNat with ha
  set b := (blockX p - X).toNat with hb
  set N := rows0.length with hN
  let rowsAt : ℕ → List ℕ := fun n => orRows rows0 (padRows (a + n) (b + n) [3, 3])
  let tbl : List (List ℕ) := (List.range N).map rowsAt
  let g : ℕ → List ℕ := fun n => rows0 ++ (List.range (a + n - N)).map (fun _ => 0) ++
    [3 * 2 ^ (b + n), 3 * 2 ^ (b + n)]
  let h : ℕ → List ℕ := fun n => if n < N then tbl.getD n [] else g n
  have hh : ∀ n, h n = rowsAt n := by
    intro n
    by_cases hn : n < N
    · simp only [h, hn, ↓reduceIte, tbl, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hn, Option.map_some, Option.getD_some]
    · simp only [h, hn, ↓reduceIte, g, rowsAt, padRows, map_range_zero]
      rw [orRows_replicate_append _ _ _ (by omega)]
      simp [Nat.shiftLeft_eq, hN]
  refine ⟨fun n => (X, Y, h n), ?_, fun n => ?_⟩
  · have hg : Primrec g := by
      have e : Primrec fun n : ℕ => 3 * 2 ^ (b + n) :=
        Primrec.nat_mul.comp (Primrec.const 3)
          (primrec_two_pow.comp (Primrec.nat_add.comp (Primrec.const b) Primrec.id))
      refine Primrec.list_append.comp (Primrec.list_append.comp (Primrec.const rows0)
        (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_sub.comp
          (Primrec.nat_add.comp (Primrec.const a) Primrec.id) (Primrec.const N)))
          (Primrec₂.const 0))) (Primrec.list_cons.comp e (Primrec.list_cons.comp e
            (Primrec.const [])))
    have hh' : Primrec h :=
      Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const N))
        ((Primrec.list_getD []).comp (Primrec.const tbl) Primrec.id) hg
    exact (Primrec.pair (Primrec.const X) (Primrec.pair (Primrec.const Y) hh')).to_comp
  · change ofRows X Y (h n) = _
    rw [hh, ofRows_orRows, ← hF, ofRows_padRows, encM_startM]
    congr 2 <;> omega

end LP

end LeanTheory.Life
