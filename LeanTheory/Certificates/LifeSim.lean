/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Sanity.Life
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.GetD

/-!
# Evolution certificates for the Game of Life

Concrete facts `conway.evolve n P = Q` are closed computations. This module turns them into
explicit proof terms whose leaves are natural-number identities evaluated by the kernel (with
GMP arithmetic); no `decide` of any kind is used.

* **Windows.** `ofRows x₀ y₀ rows` is the configuration whose cell `(x₀ + j, y₀ + i)` is alive
  iff bit `j` of the `i`-th entry of `rows` is set. The **least significant bit is the leftmost
  cell** of a row, and rows are listed from top to bottom (`y` increases downward).
* **Bit-parallel step.** `nextRow u m d` computes one generation of a row from the rows above,
  at and below it by a fixed number of bitwise operations; `stepRows` applies it to a window,
  which grows by one cell on every side. `step_ofRows` proves the refinement
  `conway.step (ofRows x₀ y₀ rows) = ofRows (x₀ - 1) (y₀ - 1) (stepRows rows)` without any side
  condition, because the window is enlarged rather than truncated.
* **Certificates** (the SubsetSum pattern). Inside certificates a row is stored as a *tagged*
  literal `e` with `untag e = e >>> 64` the row and the low 64 bits an arbitrary tag (see the
  section on certificates for the reason). `RowsStep` certifies one generation row by row, with
  one kernel fact `nextRow (untag u) (untag m) (untag d) = untag r` per row. `Padded` certifies
  that a window is a trimmed window surrounded by empty rows and columns, with one kernel fact
  per row. `Evolves` chains generations and trimming steps, and `Tagged` relates tagged and
  plain rows. `Evolves.sound` is the soundness theorem: from `Tagged ts rows`,
  `Evolves n x y ts x' y' ts'` and `Tagged ts' rows'` it gives
  `conway.evolve n (ofRows x y rows) = ofRows x' y' rows'`.

The proof-term builder and the tactic `life_cert` are in `Certificates/LifeCert`.

* **Trimmed windows.** `trimmedB` checks the canonical form of a window; `ofRows_inj` shows that
  a configuration has at most one trimmed window, so that different trimmed windows give
  different configurations (`ofRows_ne`, `ofRows_ne_of_rows_ne`).

**Sanity.** `mem_ofRows_glider` (the window encoding of the glider is the expected set of cells),
`nextRow_zero`, `nextBit_eq_ruleB` (the bit formula is Conway's rule, all 512 cases),
`step_ofRows_blinker` (the refinement reproduces the blinker step of `Sanity/Life`),
`not_rowsStep_fixture` (a wrong row is not certifiable), `untag_fixture` (tags do not matter).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### Windows -/

/-- Bit `x` of `r` at an integer position; `false` at negative positions. -/
def tb (r : ℕ) (x : ℤ) : Bool := decide (0 ≤ x) && r.testBit x.toNat

/-- Row `y` of a list of rows at an integer index; `0` outside the list. -/
def rowZ (rows : List ℕ) (y : ℤ) : ℕ := if 0 ≤ y then rows.getD y.toNat 0 else 0

/-- The state of the cell at offset `(x, y)` from the origin of a window. -/
def bitAt (rows : List ℕ) (x y : ℤ) : Bool := tb (rowZ rows y) x

/-- The configuration encoded by a window: cell `(x₀ + j, y₀ + i)` is alive iff bit `j` of
`rows[i]` is set. The least significant bit is the leftmost cell. -/
def ofRows (x₀ y₀ : ℤ) (rows : List ℕ) : Finset Cell :=
  (range rows.length).biUnion fun i =>
    ((range (rows.getD i 0 + 1)).filter fun j => (rows.getD i 0).testBit j).image
      fun j : ℕ => ((x₀ + (j : ℤ), y₀ + (i : ℤ)) : Cell)

@[simp] theorem tb_zero (x : ℤ) : tb 0 x = false := by simp [tb]

/-- At a natural position `tb` is `testBit`. -/
theorem tb_natCast (r k : ℕ) : tb r (k : ℤ) = r.testBit k := by simp [tb]

theorem tb_of_neg (r : ℕ) {x : ℤ} (h : x < 0) : tb r x = false := by
  simp [tb, not_le.2 h]

/-- Shifting a row left by `t` moves every cell `t` places to the right. -/
theorem tb_shiftLeft (r t : ℕ) (x : ℤ) : tb (r <<< t) x = tb r (x - t) := by
  by_cases hx : 0 ≤ x
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    by_cases hk : t ≤ k
    · have h : ((k : ℤ) - t) = ((k - t : ℕ) : ℤ) := by omega
      rw [h, tb_natCast, tb_natCast, Nat.testBit_shiftLeft]
      simp [hk]
    · rw [tb_natCast, Nat.testBit_shiftLeft, tb_of_neg r (by omega)]
      simp [hk]
  · rw [tb_of_neg _ (by omega), tb_of_neg _ (by omega)]

theorem rowZ_of_neg (rows : List ℕ) {y : ℤ} (h : y < 0) : rowZ rows y = 0 := by
  simp [rowZ, not_le.2 h]

theorem rowZ_natCast (rows : List ℕ) (i : ℕ) : rowZ rows (i : ℤ) = rows.getD i 0 := by
  simp [rowZ]

@[simp] theorem rowZ_nil (y : ℤ) : rowZ [] y = 0 := by
  unfold rowZ
  split <;> simp

/-- Dropping the first row moves the remaining rows up. -/
theorem rowZ_cons_succ (a : ℕ) (rows : List ℕ) {y : ℤ} (h : 0 ≤ y) :
    rowZ (a :: rows) (y + 1) = rowZ rows y := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
  have h1 : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by omega
  rw [h1, rowZ_natCast, rowZ_natCast, List.getD_cons_succ]

/-- An empty first row can be dropped at every index. -/
theorem rowZ_zero_cons (rows : List ℕ) (y : ℤ) : rowZ (0 :: rows) (y + 1) = rowZ rows y := by
  by_cases h : 0 ≤ y
  · exact rowZ_cons_succ 0 rows h
  · rw [rowZ_of_neg rows (by omega)]
    by_cases h1 : y + 1 < 0
    · exact rowZ_of_neg _ h1
    · have h0 : y + 1 = ((0 : ℕ) : ℤ) := by omega
      rw [h0, rowZ_natCast]
      rfl

@[simp] theorem rowZ_cons_zero (a : ℕ) (rows : List ℕ) : rowZ (a :: rows) 0 = a := by
  have h := rowZ_natCast (a :: rows) 0
  simpa using h

/-- **Meaning of a window**: a cell is alive iff its bit is set. -/
theorem mem_ofRows {x₀ y₀ : ℤ} {rows : List ℕ} {c : Cell} :
    c ∈ ofRows x₀ y₀ rows ↔ bitAt rows (c.1 - x₀) (c.2 - y₀) = true := by
  obtain ⟨x, y⟩ := c
  simp only [ofRows, mem_biUnion, mem_range, mem_image, mem_filter, Prod.mk.injEq, bitAt]
  constructor
  · rintro ⟨i, -, j, ⟨-, hj⟩, rfl, rfl⟩
    have h1 : x₀ + (j : ℤ) - x₀ = (j : ℤ) := by omega
    have h2 : y₀ + (i : ℤ) - y₀ = (i : ℤ) := by omega
    rw [h1, h2, rowZ_natCast, tb_natCast]
    exact hj
  · intro h
    have hy : 0 ≤ y - y₀ := by
      by_contra hy
      rw [rowZ_of_neg rows (by omega), tb_zero] at h
      exact Bool.false_ne_true h
    have hx : 0 ≤ x - x₀ := by
      by_contra hx
      rw [tb_of_neg _ (by omega)] at h
      exact Bool.false_ne_true h
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le hy
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hx
    rw [hi, hj, rowZ_natCast, tb_natCast] at h
    have hlen : i < rows.length := by
      by_contra hlen
      rw [List.getD_eq_default _ _ (by omega), Nat.zero_testBit] at h
      exact Bool.false_ne_true h
    have hjr : j < rows.getD i 0 + 1 := by
      have h1 := Nat.ge_two_pow_of_testBit h
      have h2 := @Nat.lt_two_pow_self j
      omega
    exact ⟨i, hlen, j, ⟨hjr, h⟩, by omega, by omega⟩

/-- Membership in a window as a Boolean. -/
theorem decide_mem_ofRows (x₀ y₀ : ℤ) (rows : List ℕ) (c : Cell) :
    decide (c ∈ ofRows x₀ y₀ rows) = bitAt rows (c.1 - x₀) (c.2 - y₀) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, mem_ofRows]

/-- The empty window is the empty configuration. -/
@[simp] theorem ofRows_nil (x₀ y₀ : ℤ) : ofRows x₀ y₀ [] = ∅ := by
  simp [ofRows]

/-! ### Trimmed windows are unique -/

/-- Boolean check that a window is in **trimmed** form: its first and last rows are not empty
and some row has its lowest bit set. A nonempty configuration has exactly one trimmed window
(`ofRows_inj`). -/
def trimmedB (rows : List ℕ) : Bool :=
  (rows.getD 0 0 != 0) && (rows.getD (rows.length - 1) 0 != 0) && rows.any (·.testBit 0)

/-- The cells of a window are to the right of and below its origin. -/
theorem le_of_mem_ofRows {x y : ℤ} {rows : List ℕ} {c : Cell} (h : c ∈ ofRows x y rows) :
    x ≤ c.1 ∧ y ≤ c.2 := by
  rw [mem_ofRows, bitAt] at h
  refine ⟨?_, ?_⟩ <;> by_contra hc
  · rw [tb_of_neg _ (by omega)] at h
    exact Bool.false_ne_true h
  · rw [rowZ_of_neg _ (by omega), tb_zero] at h
    exact Bool.false_ne_true h

/-- A trimmed window has a cell in its first column. -/
theorem exists_mem_ofRows_fst {rows : List ℕ} (h : trimmedB rows = true) (x y : ℤ) :
    ∃ c ∈ ofRows x y rows, c.1 = x := by
  simp only [trimmedB, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨-, r, hr, hbit⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  refine ⟨(x, y + i), ?_, rfl⟩
  rw [mem_ofRows, bitAt]
  have e1 : (x, y + (i : ℤ)).1 - x = ((0 : ℕ) : ℤ) := by simp
  have e2 : (x, y + (i : ℤ)).2 - y = (i : ℤ) := by simp
  rw [e1, e2, rowZ_natCast, tb_natCast, List.getD_eq_getElem _ _ hi]
  exact hbit

/-- A trimmed window has a cell in its first row. -/
theorem exists_mem_ofRows_snd {rows : List ℕ} (h : trimmedB rows = true) (x y : ℤ) :
    ∃ c ∈ ofRows x y rows, c.2 = y := by
  simp only [trimmedB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero h.1.1
  refine ⟨(x + j, y), ?_, rfl⟩
  rw [mem_ofRows, bitAt]
  have e1 : (x + (j : ℤ), y).1 - x = (j : ℤ) := by simp
  have e2 : (x + (j : ℤ), y).2 - y = ((0 : ℕ) : ℤ) := by simp
  rw [e1, e2, rowZ_natCast, tb_natCast]
  exact hj

/-- If two windows at the same origin encode the same configuration and the second is trimmed,
the first has at least as many rows. -/
theorem length_le_of_getD_eq {rows rows' : List ℕ} (h' : trimmedB rows' = true)
    (he : ∀ i : ℕ, rows.getD i 0 = rows'.getD i 0) : rows'.length ≤ rows.length := by
  simp only [trimmedB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h'
  by_contra hlt
  have h0 := he (rows'.length - 1)
  rw [List.getD_eq_default _ _ (by omega)] at h0
  exact h'.1.2 h0.symm

/-- **Uniqueness of the trimmed window**: two trimmed windows encoding the same configuration
have the same origin and the same rows. -/
theorem ofRows_inj {x y x' y' : ℤ} {rows rows' : List ℕ} (h : trimmedB rows = true)
    (h' : trimmedB rows' = true) (he : ofRows x y rows = ofRows x' y' rows') :
    x = x' ∧ y = y' ∧ rows = rows' := by
  have hx : x = x' := by
    obtain ⟨c, hc, hcx⟩ := exists_mem_ofRows_fst h x y
    obtain ⟨c', hc', hcx'⟩ := exists_mem_ofRows_fst h' x' y'
    have h1 := (le_of_mem_ofRows (he ▸ hc)).1
    have h2 := (le_of_mem_ofRows (he ▸ hc')).1
    omega
  have hy : y = y' := by
    obtain ⟨c, hc, hcy⟩ := exists_mem_ofRows_snd h x y
    obtain ⟨c', hc', hcy'⟩ := exists_mem_ofRows_snd h' x' y'
    have h1 := (le_of_mem_ofRows (he ▸ hc)).2
    have h2 := (le_of_mem_ofRows (he ▸ hc')).2
    omega
  subst hx hy
  refine ⟨rfl, rfl, ?_⟩
  have hrow : ∀ i : ℕ, rows.getD i 0 = rows'.getD i 0 := by
    intro i
    apply Nat.eq_of_testBit_eq
    intro j
    have hm : ((x + j, y + i) : Cell) ∈ ofRows x y rows ↔
        ((x + j, y + i) : Cell) ∈ ofRows x y rows' := by rw [he]
    rw [mem_ofRows, mem_ofRows, bitAt, bitAt] at hm
    have e1 : ((x + (j : ℤ), y + (i : ℤ)) : Cell).1 - x = (j : ℤ) := by simp
    have e2 : ((x + (j : ℤ), y + (i : ℤ)) : Cell).2 - y = (i : ℤ) := by simp
    rw [e1, e2, rowZ_natCast, rowZ_natCast, tb_natCast, tb_natCast] at hm
    exact Bool.eq_iff_iff.2 hm
  have hlen : rows.length = rows'.length :=
    le_antisymm (length_le_of_getD_eq h fun i => (hrow i).symm) (length_le_of_getD_eq h' hrow)
  apply List.ext_getElem hlen
  intro i h1 h2
  have := hrow i
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- Trimmed windows with different data encode different configurations. -/
theorem ofRows_ne {x y x' y' : ℤ} {rows rows' : List ℕ} (h : trimmedB rows = true)
    (h' : trimmedB rows' = true) (hne : ¬ (x = x' ∧ y = y' ∧ rows = rows')) :
    ofRows x y rows ≠ ofRows x' y' rows' :=
  fun he => hne (ofRows_inj h h' he)

/-- Trimmed windows with different rows encode configurations that are not translates of each
other. -/
theorem ofRows_ne_of_rows_ne {x y x' y' : ℤ} {rows rows' : List ℕ} (h : trimmedB rows = true)
    (h' : trimmedB rows' = true) (hne : rows ≠ rows') : ofRows x y rows ≠ ofRows x' y' rows' :=
  fun he => hne (ofRows_inj h h' he).2.2

/-- A trimmed window encodes a nonempty configuration. -/
theorem ofRows_nonempty {rows : List ℕ} (h : trimmedB rows = true) (x y : ℤ) :
    (ofRows x y rows).Nonempty :=
  let ⟨c, hc, _⟩ := exists_mem_ofRows_fst h x y
  ⟨c, hc⟩

/-! ### The bit-parallel step -/

/-- Bitwise sum of three words without carry. -/
def xor3 (a b c : ℕ) : ℕ := a ^^^ b ^^^ c

/-- Bitwise carry (majority) of three words. -/
def maj3 (a b c : ℕ) : ℕ := (a &&& b) ||| (a &&& c) ||| (b &&& c)

/-- One generation of the row `m`, given the row `u` above and the row `d` below. The result is
in the enlarged frame: bit `k` of the result is the new state of the cell whose old position in
the row was `k - 1`.

The eight neighbours are added bit-parallel: `ones` is the units bit of the count and the
count is `ones + 2 * t` where `t` is the number of set bits among four carry words. The cell is
alive afterwards iff the count is three, or it is two and the cell was alive: iff `t = 1` and
(`ones` or the cell itself). -/
def nextRow (u m d : ℕ) : ℕ :=
  let su := xor3 (u <<< 2) (u <<< 1) u
  let cu := maj3 (u <<< 2) (u <<< 1) u
  let sd := xor3 (d <<< 2) (d <<< 1) d
  let cd := maj3 (d <<< 2) (d <<< 1) d
  let sm := (m <<< 2) ^^^ m
  let cm := (m <<< 2) &&& m
  let ones := xor3 su sd sm
  let carry := maj3 su sd sm
  let odd := (cu ^^^ cd) ^^^ (cm ^^^ carry)
  let two := (cu &&& cd) ||| (cm &&& carry)
  let exactlyOne := odd ^^^ (odd &&& two)
  exactlyOne &&& (ones ||| (m <<< 1))

/-- The Boolean formula computed by `nextRow` in each bit position. Arguments: the three cells
above (left, middle, right), the three cells of the row itself and the three cells below. -/
def nextBit (u2 u1 u0 m2 m1 m0 d2 d1 d0 : Bool) : Bool :=
  let su := (u2 ^^ u1) ^^ u0
  let cu := ((u2 && u1) || (u2 && u0)) || (u1 && u0)
  let sd := (d2 ^^ d1) ^^ d0
  let cd := ((d2 && d1) || (d2 && d0)) || (d1 && d0)
  let sm := m2 ^^ m0
  let cm := m2 && m0
  let ones := (su ^^ sd) ^^ sm
  let carry := ((su && sd) || (su && sm)) || (sd && sm)
  let odd := (cu ^^ cd) ^^ (cm ^^ carry)
  let two := (cu && cd) || (cm && carry)
  let exactlyOne := odd ^^ (odd && two)
  exactlyOne && (ones || m1)

/-- Conway's rule as a Boolean function of the state of a cell and its live-neighbour count. -/
def ruleB (alive : Bool) (n : ℕ) : Bool := n == 3 || (alive && n == 2)

/-- **The bit formula is Conway's rule**: all 512 cases, each by evaluation. -/
theorem nextBit_eq_ruleB (u2 u1 u0 m2 m1 m0 d2 d1 d0 : Bool) :
    nextBit u2 u1 u0 m2 m1 m0 d2 d1 d0 =
      ruleB m1 (u2.toNat + (u1.toNat + (u0.toNat + (m2.toNat + (m0.toNat +
        (d2.toNat + (d1.toNat + d0.toNat))))))) := by
  cases u2 <;> cases u1 <;> cases u0 <;> cases m2 <;> cases m1 <;> cases m0 <;>
    cases d2 <;> cases d1 <;> cases d0 <;> rfl

/-- Each bit of `nextRow` is `nextBit` of the nine surrounding bits. -/
theorem testBit_nextRow (u m d k : ℕ) :
    (nextRow u m d).testBit k =
      nextBit (tb u ((k : ℤ) - 2)) (tb u ((k : ℤ) - 1)) (tb u k)
        (tb m ((k : ℤ) - 2)) (tb m ((k : ℤ) - 1)) (tb m k)
        (tb d ((k : ℤ) - 2)) (tb d ((k : ℤ) - 1)) (tb d k) := by
  have h2 : ∀ r : ℕ, tb r ((k : ℤ) - 2) = (r <<< 2).testBit k := fun r => by
    rw [← tb_natCast, tb_shiftLeft]
    rfl
  have h1 : ∀ r : ℕ, tb r ((k : ℤ) - 1) = (r <<< 1).testBit k := fun r => by
    rw [← tb_natCast, tb_shiftLeft]
    rfl
  simp only [h2, h1, tb_natCast, nextRow, nextBit, xor3, maj3, Nat.testBit_xor, Nat.testBit_and,
    Nat.testBit_or]

/-- Empty surroundings stay empty. -/
theorem nextRow_zero : nextRow 0 0 0 = 0 := by
  simp [nextRow, xor3, maj3]

/-- The integer-indexed form of `testBit_nextRow`, valid at every position. -/
theorem tb_nextRow (u m d : ℕ) (x : ℤ) :
    tb (nextRow u m d) (x + 1) =
      nextBit (tb u (x - 1)) (tb u x) (tb u (x + 1)) (tb m (x - 1)) (tb m x) (tb m (x + 1))
        (tb d (x - 1)) (tb d x) (tb d (x + 1)) := by
  by_cases hx : 0 ≤ x + 1
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hx
    have e1 : x - 1 = (k : ℤ) - 2 := by omega
    have e2 : x = (k : ℤ) - 1 := by omega
    rw [hk, tb_natCast, testBit_nextRow, e1, ← e2]
  · have n1 : x - 1 < 0 := by omega
    have n2 : x < 0 := by omega
    have n3 : x + 1 < 0 := by omega
    simp only [tb_of_neg _ n1, tb_of_neg _ n2, tb_of_neg _ n3]
    rfl

/-- One generation of a window, row by row: `u` and `m` are the two rows above the remaining
rows. Two rows are added below the window. -/
def stepAux (u m : ℕ) : List ℕ → List ℕ
  | [] => [nextRow u m 0, nextRow m 0 0]
  | d :: ds => nextRow u m d :: stepAux m d ds

/-- One generation of a window. The result has two more rows and its origin is one cell up and
one cell to the left of the origin of the argument. -/
def stepRows (rows : List ℕ) : List ℕ := stepAux 0 0 rows

/-- Row `i` of `stepAux u m ds` is `nextRow` of rows `i`, `i + 1`, `i + 2` of `u :: m :: ds`. -/
theorem getD_stepAux (u m : ℕ) (ds : List ℕ) (i : ℕ) :
    (stepAux u m ds).getD i 0 =
      nextRow ((u :: m :: ds).getD i 0) ((u :: m :: ds).getD (i + 1) 0)
        ((u :: m :: ds).getD (i + 2) 0) := by
  induction ds generalizing u m i with
  | nil =>
    match i with
    | 0 => rfl
    | 1 => rfl
    | i + 2 => simp [stepAux, nextRow_zero]
  | cons d ds ih =>
    match i with
    | 0 => rfl
    | i + 1 => simpa [stepAux] using ih m d i

/-- Row `y + 1` of the stepped window is `nextRow` of the rows `y - 1`, `y`, `y + 1` of the
window. -/
theorem rowZ_stepRows (rows : List ℕ) (y : ℤ) :
    rowZ (stepRows rows) (y + 1) =
      nextRow (rowZ rows (y - 1)) (rowZ rows y) (rowZ rows (y + 1)) := by
  have hz : ∀ z : ℤ, rowZ (0 :: 0 :: rows) (z + 2) = rowZ rows z := fun z => by
    have e : z + 2 = z + 1 + 1 := by omega
    rw [e, rowZ_zero_cons, rowZ_zero_cons]
  by_cases hy : 0 ≤ y + 1
  · obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le hy
    have e1 : (i : ℤ) = (y - 1) + 2 := by omega
    have e2 : ((i + 1 : ℕ) : ℤ) = y + 2 := by omega
    have e3 : ((i + 2 : ℕ) : ℤ) = (y + 1) + 2 := by omega
    calc rowZ (stepRows rows) (y + 1)
        = (stepAux 0 0 rows).getD i 0 := by rw [hi, rowZ_natCast, stepRows]
      _ = nextRow (rowZ (0 :: 0 :: rows) (i : ℤ)) (rowZ (0 :: 0 :: rows) ((i + 1 : ℕ) : ℤ))
            (rowZ (0 :: 0 :: rows) ((i + 2 : ℕ) : ℤ)) := by
          rw [getD_stepAux, rowZ_natCast, rowZ_natCast, rowZ_natCast]
      _ = _ := by rw [e1, e2, e3, hz, hz, hz]
  · rw [rowZ_of_neg _ (by omega), rowZ_of_neg _ (by omega), rowZ_of_neg _ (by omega),
      rowZ_of_neg _ (by omega), nextRow_zero]

/-- The new state of a cell of the stepped window is `nextBit` of the nine old states around
it. -/
theorem bitAt_stepRows (rows : List ℕ) (x y : ℤ) :
    bitAt (stepRows rows) (x + 1) (y + 1) =
      nextBit (bitAt rows (x - 1) (y - 1)) (bitAt rows x (y - 1)) (bitAt rows (x + 1) (y - 1))
        (bitAt rows (x - 1) y) (bitAt rows x y) (bitAt rows (x + 1) y)
        (bitAt rows (x - 1) (y + 1)) (bitAt rows x (y + 1)) (bitAt rows (x + 1) (y + 1)) := by
  simp only [bitAt, rowZ_stepRows, tb_nextRow]

/-- Conway's rule for one cell as a Boolean function of nine memberships. -/
theorem mem_conway_step_iff_ruleB (S : Finset Cell) (x y : ℤ) :
    (x, y) ∈ conway.step S ↔
      ruleB (decide ((x, y) ∈ S))
        ((decide ((x - 1, y - 1) ∈ S)).toNat + ((decide ((x, y - 1) ∈ S)).toNat +
        ((decide ((x + 1, y - 1) ∈ S)).toNat + ((decide ((x - 1, y) ∈ S)).toNat +
        ((decide ((x + 1, y) ∈ S)).toNat + ((decide ((x - 1, y + 1) ∈ S)).toNat +
        ((decide ((x, y + 1) ∈ S)).toNat + (decide ((x + 1, y + 1) ∈ S)).toNat))))))) = true := by
  have hb : ∀ p : Prop, [Decidable p] → (decide p).toNat = if p then 1 else 0 := by
    intro p _
    by_cases hp : p <;> simp [hp]
  simp only [hb, ← liveNbrs_eq, Rule.mem_step, conway, mem_insert, mem_singleton, ruleB]
  by_cases h : (x, y) ∈ S <;> simp [h, or_comm]

/-- **Refinement**: one generation of a window, computed bit-parallel, is one generation of
Conway's rule on the configuration it encodes. There is no side condition: the stepped window
is one cell larger on every side. -/
theorem step_ofRows (x₀ y₀ : ℤ) (rows : List ℕ) :
    conway.step (ofRows x₀ y₀ rows) = ofRows (x₀ - 1) (y₀ - 1) (stepRows rows) := by
  ext ⟨x, y⟩
  have h := bitAt_stepRows rows (x - x₀) (y - y₀)
  have e1 : x - (x₀ - 1) = x - x₀ + 1 := by omega
  have e2 : y - (y₀ - 1) = y - y₀ + 1 := by omega
  have e3 : x - 1 - x₀ = x - x₀ - 1 := by omega
  have e4 : y - 1 - y₀ = y - y₀ - 1 := by omega
  have e5 : x + 1 - x₀ = x - x₀ + 1 := by omega
  have e6 : y + 1 - y₀ = y - y₀ + 1 := by omega
  have hr : (x, y) ∈ ofRows (x₀ - 1) (y₀ - 1) (stepRows rows) ↔
      bitAt (stepRows rows) (x - x₀ + 1) (y - y₀ + 1) = true := by
    rw [mem_ofRows, e1, e2]
  rw [mem_conway_step_iff_ruleB, hr, h, nextBit_eq_ruleB]
  simp only [decide_mem_ofRows, e3, e4, e5, e6]

/-! ### Certificates

Rows are stored in certificates as **tagged** literals: the row itself in the bits from position
64 upwards and an arbitrary tag in the low 64 bits. The reason is practical. Lean hashes a
natural number literal by its low 64 bits, so the rows of a wide sparse window (say, a glider
far to the right of an otherwise empty region) would all have the same hash, and the caches of
the kernel would degrade to linear searches. The tag is chosen by the proof builder so that
different rows get different hashes; it has no mathematical meaning and soundness does not
depend on it. -/

/-- The row stored in a tagged literal: the bits above the 64-bit tag. -/
def untag (e : ℕ) : ℕ := e >>> 64

@[simp] theorem untag_zero : untag 0 = 0 := by simp [untag]

/-- Certificate that the tagged rows `es` store the rows `rs`, one kernel fact `untag e = r`
per row. -/
inductive Tagged : List ℕ → List ℕ → Prop where
  /-- No rows. -/
  | nil : Tagged [] []
  /-- One row. -/
  | cons (e r : ℕ) (es rs : List ℕ) (h : untag e = r) (t : Tagged es rs) :
      Tagged (e :: es) (r :: rs)

/-- Soundness of `Tagged`. -/
theorem Tagged.eq {es rs : List ℕ} (h : Tagged es rs) : es.map untag = rs := by
  induction h with
  | nil => rfl
  | cons e r es rs h t ih => simp [h, ih]

/-- Certificate that one generation of the rows stored in `ds`, below the rows stored in `u` and
`m`, gives the rows stored in `rs`: one kernel fact
`nextRow (untag u) (untag m) (untag d) = untag r` per row. -/
inductive RowsStep : ℕ → ℕ → List ℕ → List ℕ → Prop where
  /-- The two rows below the window. -/
  | nil (u m r₁ r₂ : ℕ) (h₁ : nextRow (untag u) (untag m) 0 = untag r₁)
      (h₂ : nextRow (untag m) 0 0 = untag r₂) : RowsStep u m [] [r₁, r₂]
  /-- One row of the window. -/
  | cons (u m d r : ℕ) (ds rs : List ℕ)
      (h : nextRow (untag u) (untag m) (untag d) = untag r) (t : RowsStep m d ds rs) :
      RowsStep u m (d :: ds) (r :: rs)

/-- Soundness of `RowsStep`. -/
theorem RowsStep.eq {u m : ℕ} {ds rs : List ℕ} (h : RowsStep u m ds rs) :
    stepAux (untag u) (untag m) (ds.map untag) = rs.map untag := by
  induction h with
  | nil u m r₁ r₂ h₁ h₂ => simp [stepAux, h₁, h₂]
  | cons u m d r ds rs h t ih => simp [stepAux, h, ih]

/-- Certificate that the window stored in `full` is the window stored in `rows` shifted `t`
cells to the right, with `pre` empty rows above it and any number of empty rows below it; one
kernel fact `untag r <<< t = untag r'` per row. -/
inductive Padded (t : ℕ) : ℕ → List ℕ → List ℕ → Prop where
  /-- Nothing left. -/
  | nil : Padded t 0 [] []
  /-- An empty row below the trimmed window. -/
  | zero (full : List ℕ) (p : Padded t 0 [] full) : Padded t 0 [] (0 :: full)
  /-- A row of the trimmed window. -/
  | row (r r' : ℕ) (rows full : List ℕ) (h : untag r <<< t = untag r')
      (p : Padded t 0 rows full) : Padded t 0 (r :: rows) (r' :: full)
  /-- An empty row above the trimmed window. -/
  | lead (pre : ℕ) (rows full : List ℕ) (p : Padded t pre rows full) :
      Padded t (pre + 1) rows (0 :: full)

/-- The cell states of a padded window are those of the trimmed window, displaced. -/
theorem Padded.bitAt_eq {t pre : ℕ} {rows full : List ℕ} (h : Padded t pre rows full)
    (x y : ℤ) :
    bitAt (full.map untag) x y = bitAt (rows.map untag) (x - t) (y - pre) := by
  induction h generalizing y with
  | nil => simp [bitAt]
  | zero full p ih =>
    have h1 := rowZ_zero_cons (full.map untag) (y - 1)
    rw [sub_add_cancel] at h1
    have h2 := ih (y - 1)
    simp only [bitAt, List.map_cons, untag_zero, h1, List.map_nil, rowZ_nil, tb_zero] at h2 ⊢
    exact h2
  | row r r' rows full h p ih =>
    simp only [bitAt, Nat.cast_zero, sub_zero, List.map_cons] at ih ⊢
    by_cases hy : 0 ≤ y - 1
    · have h1 := rowZ_cons_succ (untag r') (full.map untag) hy
      have h2 := rowZ_cons_succ (untag r) (rows.map untag) hy
      rw [sub_add_cancel] at h1 h2
      rw [h1, h2]
      exact ih (y - 1)
    · by_cases hy0 : y = 0
      · subst hy0
        rw [rowZ_cons_zero, rowZ_cons_zero, ← h, tb_shiftLeft]
      · rw [rowZ_of_neg _ (by omega), rowZ_of_neg _ (by omega)]
        simp
  | lead pre rows full p ih =>
    have h1 := rowZ_zero_cons (full.map untag) (y - 1)
    rw [sub_add_cancel] at h1
    have h2 := ih (y - 1)
    have e : y - 1 - (pre : ℤ) = y - ((pre + 1 : ℕ) : ℤ) := by push_cast; omega
    simp only [bitAt, List.map_cons, untag_zero, h1] at h2 ⊢
    rw [h2, e]

/-- Soundness of `Padded`: a padded window encodes the same configuration as the trimmed window
at the displaced origin. -/
theorem Padded.ofRows_eq {t pre : ℕ} {rows full : List ℕ} (h : Padded t pre rows full)
    (x y : ℤ) :
    ofRows x y (full.map untag) = ofRows (x + t) (y + pre) (rows.map untag) := by
  ext ⟨a, b⟩
  rw [mem_ofRows, mem_ofRows, h.bitAt_eq]
  have e1 : a - x - (t : ℤ) = a - (x + t) := by omega
  have e2 : b - y - (pre : ℤ) = b - (y + pre) := by omega
  rw [e1, e2]

/-- Certificate that the window stored in `(x, y, rows)` evolves in `n` generations into the
window stored in `(x', y', rows')`. -/
inductive Evolves : ℕ → ℤ → ℤ → List ℕ → ℤ → ℤ → List ℕ → Prop where
  /-- No generation. -/
  | done (x y : ℤ) (rows : List ℕ) : Evolves 0 x y rows x y rows
  /-- One generation, certified row by row. -/
  | step (n : ℕ) (x y : ℤ) (rows rows₁ : List ℕ) (x' y' : ℤ) (rows' : List ℕ)
      (h : RowsStep 0 0 rows rows₁) (e : Evolves n (x - 1) (y - 1) rows₁ x' y' rows') :
      Evolves (n + 1) x y rows x' y' rows'
  /-- Replace a window by its trimmed form. -/
  | trim (n : ℕ) (x y : ℤ) (full : List ℕ) (t pre : ℕ) (rows : List ℕ) (x' y' : ℤ)
      (rows' : List ℕ) (h : Padded t pre rows full)
      (e : Evolves n (x + t) (y + pre) rows x' y' rows') : Evolves n x y full x' y' rows'

/-- Soundness of evolution certificates on the stored windows. -/
theorem Evolves.sound_untag {n : ℕ} {x y : ℤ} {rows : List ℕ} {x' y' : ℤ} {rows' : List ℕ}
    (h : Evolves n x y rows x' y' rows') :
    conway.evolve n (ofRows x y (rows.map untag)) = ofRows x' y' (rows'.map untag) := by
  induction h with
  | done x y rows => rfl
  | step n x y rows rows₁ x' y' rows' h e ih =>
    have h1 := h.eq
    rw [untag_zero] at h1
    rw [Rule.evolve_succ', step_ofRows, stepRows, h1, ih]
  | trim n x y full t pre rows x' y' rows' h e ih => rw [h.ofRows_eq, ih]

/-- **Soundness of evolution certificates.** `ts` and `ts'` are the tagged forms of the rows
`rows` and `rows'`. -/
theorem Evolves.sound {n : ℕ} {x y : ℤ} {ts rows : List ℕ} {x' y' : ℤ} {ts' rows' : List ℕ}
    (h₀ : Tagged ts rows) (h : Evolves n x y ts x' y' ts') (h₁ : Tagged ts' rows') :
    conway.evolve n (ofRows x y rows) = ofRows x' y' rows' := by
  rw [← h₀.eq, ← h₁.eq]
  exact h.sound_untag

/-- Soundness for a configuration that dies out. -/
theorem Evolves.sound_empty {n : ℕ} {x y : ℤ} {ts rows : List ℕ} {x' y' : ℤ}
    (h₀ : Tagged ts rows) (h : Evolves n x y ts x' y' []) :
    conway.evolve n (ofRows x y rows) = ∅ := by
  rw [Evolves.sound h₀ h Tagged.nil, ofRows_nil]

/-! ### Sanity -/

/-- **Sanity** (encoding): the window `[2, 4, 7]` at the origin is the glider
`.O. / ..O / OOO`, with the least significant bit as the leftmost cell. -/
theorem mem_ofRows_glider (c : Cell) :
    c ∈ ofRows 0 0 [2, 4, 7] ↔ c ∈ ({(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)} : Finset Cell) := by
  obtain ⟨x, y⟩ := c
  rw [mem_ofRows]
  simp only [mem_insert, mem_singleton, Prod.mk.injEq, sub_zero]
  constructor
  · intro h
    have hy : 0 ≤ y ∧ y < 3 := by
      refine ⟨?_, ?_⟩ <;> by_contra hc
      · rw [bitAt, rowZ_of_neg _ (by omega), tb_zero] at h
        exact Bool.false_ne_true h
      · obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ y by omega)
        rw [bitAt, hi, rowZ_natCast, List.getD_eq_default _ _ (by simp; omega), tb_zero] at h
        exact Bool.false_ne_true h
    have hx : 0 ≤ x ∧ x < 3 := by
      refine ⟨?_, ?_⟩ <;> by_contra hc
      · rw [bitAt, tb_of_neg _ (by omega)] at h
        exact Bool.false_ne_true h
      · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ x by omega)
        obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le hy.1
        rw [bitAt, hi, hj, rowZ_natCast, tb_natCast] at h
        have h1 := Nat.ge_two_pow_of_testBit h
        have h2 : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
        have h3 : [2, 4, 7].getD i 0 ≤ 7 := by
          have hi3 : i < 3 := by omega
          interval_cases i <;> simp
        omega
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hx1, hx2⟩ := hx
    interval_cases x <;> interval_cases y <;> simp [bitAt, tb, rowZ, Nat.testBit] at h ⊢
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [bitAt, tb, rowZ, Nat.testBit]

/-- **Sanity** (refinement on an instance): stepping the window of the horizontal blinker gives
a window of the vertical blinker, in agreement with `conway_step_blinkerH`. -/
theorem step_ofRows_blinker : conway.step (ofRows (-1) 0 [7]) = ofRows (-2) (-1) [4, 4, 4] := by
  rw [step_ofRows]
  rfl

/-- **Sanity** (rejected fixture): a wrong row cannot be certified. The row below a lone
blinker row `7` is `4`, not `7`. (The literals are the rows shifted past the 64-bit tag.) -/
theorem not_rowsStep_fixture : ¬ RowsStep 0 (7 <<< 64) [] [4 <<< 64, 7 <<< 64] := by
  intro h
  have h1 := h.eq
  simp [untag, stepAux, nextRow, xor3, maj3] at h1

/-- **Sanity** (tags are irrelevant): two literals with the same row and different tags store
the same row. -/
theorem untag_fixture : untag (7 <<< 64 + 5) = untag (7 <<< 64 + 9) := by
  simp [untag, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

end LeanTheory.Life
