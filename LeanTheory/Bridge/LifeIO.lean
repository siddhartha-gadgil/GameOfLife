/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.LifeSim
public import Mathlib.Data.List.TakeWhile
public import Lean.Data.Json
public import Std.Data.TreeMap.Raw.Lemmas
public import Std.Data.TreeMap.Raw.WF
public meta import LeanTheory.Certificates.LifeSim
public meta import Lean.Elab.Term

/-!
# Snapshots, finite evolutions and their serialization

The exchange formats between this library, external simulators and oracle scripts: plaintext,
RLE and JSON, for single configurations and for finite time evolutions of Conway's Game of
Life. Everything here is computable; configurations have finitely many live cells.

**Trust.** Data read from a string or from JSON is untrusted. No theorem may depend on it
except through a checked statement about the resulting value: `Evolution.valid` for evolutions
(sound by `Evolution.cells_getElem_of_valid`), or an evolution certificate (`life_cert`).

## Contents

* `Snapshot`: a window `(x₀, y₀, rows)` in the encoding of `ofRows` (`Certificates/LifeSim`):
  cell `(x₀ + j, y₀ + i)` is alive iff bit `j` of `rows[i]` is set, `y` increases downward.
  `Snapshot.cells` is the configuration. Equality of snapshots is equality of windows, which is
  finer than equality of configurations.
* Cell lists: `Snapshot.toCellList` (sorted by row, then column) and `Snapshot.ofCellList`,
  with `Snapshot.mem_toCellList`, `Snapshot.toFinset_toCellList` and `Snapshot.cells_ofCellList`.
* `Snapshot.trim`: the window of the bounding box (no empty first or last row, some row with
  its lowest bit set; the empty configuration is `⟨0, 0, []⟩`), with `Snapshot.cells_trim`.
* Generations: `Snapshot.stepRaw` (window enlarged by one cell on every side), `Snapshot.step`
  (trimmed) and `Snapshot.evolve`, with `Snapshot.cells_step` and `Snapshot.cells_evolve`: they
  compute `conway.step` and `conway.evolve`.
* `Evolution`: an initial snapshot and the snapshots of the following generations.
  `Evolution.valid` is the Boolean check that each frame is one generation after the previous
  snapshot, with soundness theorem `Evolution.cells_getElem_of_valid`. `Evolution.run s n`
  computes `n` generations; `Evolution.cells_getElem_run` and `Evolution.valid_run` are its
  correctness.
* Plaintext: `Snapshot.toAscii`, `Snapshot.ofAscii?`, and the `Repr` instances of `Snapshot`
  and `Evolution` (origin and plaintext of the bounding box; `O` alive, `.` dead).
* RLE: `Snapshot.toRLE` (run-length body, no header) and `Snapshot.ofRLE?` / `rowsOfRLE?`
  (the body with optional `#` comment lines and `x = …` header line).
* JSON: `ToJson` and `FromJson` instances of `Snapshot` and `Evolution`.
  A snapshot is `{"x": x₀, "y": y₀, "rle": "…", "cells": [[x, y], …]}`, written for the trimmed
  form; on input `"cells"` is used if present, otherwise `"rle"` with `"x"` and `"y"` (default
  `0`). An evolution is `{"generations": n, "frames": [snapshot, …]}` with `n + 1` frames, the
  first being the initial snapshot. Rows are never written as JSON numbers.
* Pattern literals: the term elaborators `rle% "bob$2bo$3o!"` and
  `cells% ".O." "..O" "OOO"` read a pattern at elaboration time and elaborate to the explicit
  list of rows, here `[2, 4, 7] : List ℕ`.

## Round trips: what is proved

1. **Proved, for JSON values** (`Lean.Json` terms, no strings): `Snapshot.fromJson?_toJson`,
   `Snapshot.cells_fromJson?_toJson` (decoding the encoding of `s` succeeds and gives a
   snapshot with the cells of `s`), `Evolution.fromJson?_toJson` and
   `cellsOfJson?_cellsToJson`. The decoded snapshot is `ofCellList s.trim.toCellList`.
2. **Proved on fixtures by `rfl`**: RLE and plaintext reading and printing, cell lists,
   trimming, generations, the validity check and the pattern literals (last section).
3. **Tested only** (`#guard`, executable, not proofs): the string level, through `Json.compress`,
   `Json.pretty` and `Json.parse`; the RLE round trip `ofRLE? ∘ toRLE`; and the facts that the
   frames of `Evolution.run` are fixed by `trim` and by `ofCellList ∘ toCellList`.

**Not proved**: that `Snapshot.trim` is a normal form (`s.trim = t.trim` iff
`s.cells = t.cells`; only "if `s.trim = t.trim` then the cells agree" is proved, which is what
soundness of `Evolution.valid` needs), hence `ofCellList s.trim.toCellList = s.trim` and
completeness of `Evolution.valid`; that `toCellList` is sorted and duplicate-free; and every
statement about JSON or RLE strings.

**Implementation notes.** The JSON code uses only the constructors of `Lean.Json` and
`Std.TreeMap.Raw`, because the functions of `Lean.Data.Json` are not exposed to proofs. The
readers are folds over the characters and the printers build lists of characters, so that they
reduce in proofs by `rfl` and run without deep recursion.
-/

@[expose] public section

namespace LeanTheory.Life

open Lean

/-! ### Snapshots -/

/-- A **snapshot**: a window in the encoding of `ofRows`. Cell `(x₀ + j, y₀ + i)` is alive iff
bit `j` of `rows[i]` is set; the least significant bit is the leftmost cell and rows are listed
from top to bottom. Different snapshots may encode the same configuration; `Snapshot.trim`
computes the window of the bounding box. -/
structure Snapshot where
  /-- The `x`-coordinate of the leftmost column of the window. -/
  x₀ : ℤ
  /-- The `y`-coordinate of the top row of the window (`y` increases downward). -/
  y₀ : ℤ
  /-- The rows of the window, from top to bottom, as bit masks. -/
  rows : List ℕ
deriving DecidableEq, Inhabited

namespace Snapshot

/-- The configuration encoded by a snapshot. -/
def cells (s : Snapshot) : Finset Cell := ofRows s.x₀ s.y₀ s.rows

end Snapshot

/-- A cell is alive in a window iff it is at the position of a set bit of some row. -/
theorem mem_ofRows_iff_exists {x₀ y₀ : ℤ} {rows : List ℕ} {c : Cell} :
    c ∈ ofRows x₀ y₀ rows ↔
      ∃ i j : ℕ, (rows.getD i 0).testBit j = true ∧ c = (x₀ + (j : ℤ), y₀ + (i : ℤ)) := by
  constructor
  · simp only [ofRows, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    rintro ⟨i, -, j, ⟨-, hj⟩, rfl⟩
    exact ⟨i, j, hj, rfl⟩
  · rintro ⟨i, j, h, rfl⟩
    rw [mem_ofRows]
    simpa [bitAt, rowZ_natCast, tb_natCast] using h

/-- The positions of the set bits of `r`, in increasing order. -/
def bitPositions (r : ℕ) : List ℕ := (List.range (r.log2 + 1)).filter r.testBit

/-- `bitPositions r` lists exactly the set bits of `r`. -/
theorem mem_bitPositions {r j : ℕ} : j ∈ bitPositions r ↔ r.testBit j = true := by
  simp only [bitPositions, List.mem_filter, List.mem_range, and_iff_right_iff_imp]
  intro h
  have h1 := Nat.ge_two_pow_of_testBit h
  have h2 : r ≠ 0 := by
    rintro rfl
    simp at h
  have h3 := (Nat.le_log2 h2).2 h1
  omega

namespace Snapshot

/-- The live cells of a snapshot as a list, sorted by row and then by column. -/
def toCellList (s : Snapshot) : List (ℤ × ℤ) :=
  s.rows.zipIdx.flatMap fun p =>
    (bitPositions p.1).map fun j : ℕ => (s.x₀ + (j : ℤ), s.y₀ + (p.2 : ℤ))

/-- The cell list of a snapshot lists exactly its live cells. -/
@[simp] theorem mem_toCellList {s : Snapshot} {c : ℤ × ℤ} : c ∈ s.toCellList ↔ c ∈ s.cells := by
  simp only [toCellList, cells, mem_ofRows_iff_exists, List.mem_flatMap, List.mem_map,
    mem_bitPositions, Prod.exists, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨r, i, hi, j, hj, rfl⟩
    exact ⟨i, j, by simpa [List.getD_eq_getElem?_getD, hi] using hj, rfl⟩
  · rintro ⟨i, j, hj, rfl⟩
    have hlt : i < s.rows.length := by
      by_contra hlt
      rw [List.getD_eq_default _ _ (by omega), Nat.zero_testBit] at hj
      exact Bool.false_ne_true hj
    refine ⟨s.rows[i], i, by simp, j, ?_, rfl⟩
    simpa [List.getD_eq_getElem?_getD, hlt] using hj

/-- The configuration of a snapshot is the set of entries of its cell list. -/
@[simp] theorem toFinset_toCellList (s : Snapshot) : s.toCellList.toFinset = s.cells := by
  ext c
  rw [List.mem_toFinset, mem_toCellList]

end Snapshot

/-- Set the bit of the cell `c` in the array `a` of rows of a window with origin `(x₀, y₀)`.
Cells below the last row are ignored. -/
def setCell (x₀ y₀ : ℤ) (a : Array ℕ) (c : ℤ × ℤ) : Array ℕ :=
  a.modify (c.2 - y₀).toNat (· ||| 1 <<< (c.1 - x₀).toNat)

/-- The effect of `setCell` on the bits of the rows, for a cell inside the window. -/
theorem testBit_setCell {x₀ y₀ : ℤ} {a : Array ℕ} {c : ℤ × ℤ} (hx : x₀ ≤ c.1) (hy : y₀ ≤ c.2)
    (hlt : (c.2 - y₀).toNat < a.size) (i j : ℕ) :
    ((setCell x₀ y₀ a c)[i]?.getD 0).testBit j =
      ((a[i]?.getD 0).testBit j || decide ((x₀ + (j : ℤ), y₀ + (i : ℤ)) = c)) := by
  obtain ⟨cx, cy⟩ := c
  simp only at hx hy hlt
  simp only [setCell, Array.getElem?_modify, Prod.mk.injEq]
  by_cases hi : (cy - y₀).toNat = i
  · subst hi
    have e : (decide (x₀ + (j : ℤ) = cx ∧ y₀ + (((cy - y₀).toNat : ℕ) : ℤ) = cy)) =
        decide ((cx - x₀).toNat = j) := by
      rw [decide_eq_decide]
      omega
    rw [e]
    simp [hlt, Nat.one_shiftLeft, Nat.testBit_two_pow]
  · have e : ¬ (x₀ + (j : ℤ) = cx ∧ y₀ + (i : ℤ) = cy) := by omega
    simp [hi, e]

/-- The bits of the rows after setting a list of cells that lie inside the window. -/
theorem testBit_foldl_setCell {x₀ y₀ : ℤ} (l : List (ℤ × ℤ)) (a : Array ℕ)
    (h : ∀ c ∈ l, x₀ ≤ c.1 ∧ y₀ ≤ c.2 ∧ (c.2 - y₀).toNat < a.size) (i j : ℕ) :
    (((l.foldl (setCell x₀ y₀) a)[i]?.getD 0).testBit j = true ↔
      ((a[i]?.getD 0).testBit j = true ∨ (x₀ + (j : ℤ), y₀ + (i : ℤ)) ∈ l)) := by
  induction l generalizing a with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨hx, hy, hlt⟩ := h c List.mem_cons_self
    have hs : (setCell x₀ y₀ a c).size = a.size := by simp [setCell]
    rw [List.foldl_cons, ih _ (fun d hd => by simpa [hs] using h d (List.mem_cons_of_mem _ hd)),
      testBit_setCell hx hy hlt]
    simp [or_assoc]

/-- A left fold of `min` is a lower bound of the initial value and of the list. -/
theorem foldl_min_le (l : List ℤ) (a : ℤ) :
    l.foldl min a ≤ a ∧ ∀ x ∈ l, l.foldl min a ≤ x := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := ih (min a b)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨by omega, by omega, h2⟩

/-- A left fold of `max` is an upper bound of the initial value and of the list. -/
theorem le_foldl_max (l : List ℤ) (a : ℤ) :
    a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := ih (max a b)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨by omega, by omega, h2⟩

namespace Snapshot

/-- The snapshot of a list of live cells (repetitions allowed, any order). The window is the
bounding box of the cells, as for `Snapshot.trim` (their agreement is tested in the fixtures,
not proved); the empty list gives the empty window at the origin. -/
def ofCellList (l : List (ℤ × ℤ)) : Snapshot :=
  match l with
  | [] => ⟨0, 0, []⟩
  | c :: _ =>
    let x₀ := (l.map Prod.fst).foldl min c.1
    let y₀ := (l.map Prod.snd).foldl min c.2
    let y₁ := (l.map Prod.snd).foldl max c.2
    ⟨x₀, y₀, (l.foldl (setCell x₀ y₀) (Array.replicate (y₁ - y₀ + 1).toNat 0)).toList⟩

/-- The snapshot of a list of cells encodes exactly the cells of the list. -/
@[simp] theorem cells_ofCellList (l : List (ℤ × ℤ)) : (ofCellList l).cells = l.toFinset := by
  cases l with
  | nil => simp [ofCellList, cells]
  | cons c cs =>
    ext d
    simp only [ofCellList, cells, mem_ofRows_iff_exists, List.mem_toFinset,
      List.getD_eq_getElem?_getD, Array.getElem?_toList]
    have key := fun i j => testBit_foldl_setCell
      (x₀ := ((c :: cs).map Prod.fst).foldl min c.1)
      (y₀ := ((c :: cs).map Prod.snd).foldl min c.2) (c :: cs)
      (Array.replicate ((((c :: cs).map Prod.snd).foldl max c.2) -
        (((c :: cs).map Prod.snd).foldl min c.2) + 1).toNat 0)
      (fun e he => by
        have h1 := (foldl_min_le ((c :: cs).map Prod.fst) c.1).2 e.1 (List.mem_map_of_mem he)
        have h2 := (foldl_min_le ((c :: cs).map Prod.snd) c.2).2 e.2 (List.mem_map_of_mem he)
        have h3 := (le_foldl_max ((c :: cs).map Prod.snd) c.2).2 e.2 (List.mem_map_of_mem he)
        refine ⟨h1, h2, ?_⟩
        rw [Array.size_replicate]
        omega) i j
    simp only [key]
    constructor
    · rintro ⟨i, j, h | h, rfl⟩
      · rw [Array.getElem?_replicate] at h
        split at h <;> simp at h
      · exact h
    · intro hd
      have h1 := (foldl_min_le ((c :: cs).map Prod.fst) c.1).2 d.1 (List.mem_map_of_mem hd)
      have h2 := (foldl_min_le ((c :: cs).map Prod.snd) c.2).2 d.2 (List.mem_map_of_mem hd)
      refine ⟨(d.2 - ((c :: cs).map Prod.snd).foldl min c.2).toNat,
        (d.1 - ((c :: cs).map Prod.fst).foldl min c.1).toNat, Or.inr ?_, ?_⟩
      · rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
        simpa using hd
      · rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
        ext <;> simp

end Snapshot

/-! ### Trimming -/

/-- A window with an empty first row is the window of the remaining rows, one row lower. -/
theorem ofRows_zero_cons (x y : ℤ) (rows : List ℕ) :
    ofRows x y (0 :: rows) = ofRows x (y + 1) rows := by
  ext c
  rw [mem_ofRows, mem_ofRows]
  have h := rowZ_zero_cons rows (c.2 - (y + 1))
  have e : c.2 - (y + 1) + 1 = c.2 - y := by omega
  rw [e] at h
  simp only [bitAt, h]

/-- Drop the empty rows at the top of a window whose top row is at height `y`; returns the new
height of the top row and the remaining rows. -/
def dropTop : ℤ → List ℕ → ℤ × List ℕ
  | y, [] => (y, [])
  | y, r :: rows => if r = 0 then dropTop (y + 1) rows else (y, r :: rows)

/-- Dropping the empty rows at the top does not change the configuration. -/
theorem ofRows_dropTop (x y : ℤ) (rows : List ℕ) :
    ofRows x (dropTop y rows).1 (dropTop y rows).2 = ofRows x y rows := by
  induction rows generalizing y with
  | nil => rfl
  | cons r rows ih =>
    by_cases h : r = 0
    · subst h
      rw [ofRows_zero_cons, ← ih]
      rfl
    · simp [dropTop, h]

/-- Drop the empty rows at the bottom of a window. -/
def dropBottom (rows : List ℕ) : List ℕ := (rows.reverse.dropWhile (· == 0)).reverse

/-- Dropping the empty rows at the bottom does not change any row, read with default `0`. -/
theorem getD_dropBottom (rows : List ℕ) (i : ℕ) : (dropBottom rows).getD i 0 = rows.getD i 0 := by
  have h : dropBottom rows ++ (rows.reverse.takeWhile (· == 0)).reverse = rows := by
    rw [dropBottom, ← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]
  have hz : ∀ k, ((rows.reverse.takeWhile (· == 0)).reverse).getD k 0 = 0 := by
    intro k
    rw [List.getD_eq_getElem?_getD]
    cases hk : ((rows.reverse.takeWhile (· == 0)).reverse)[k]? with
    | none => rfl
    | some r =>
      have hm := List.mem_reverse.1 (List.mem_of_getElem? hk)
      simpa using List.mem_takeWhile_imp hm
  by_cases hi : i < (dropBottom rows).length
  · conv_rhs => rw [← h, List.getD_append _ _ _ _ hi]
  · conv_rhs => rw [← h, List.getD_append_right _ _ _ _ (by omega), hz]
    rw [List.getD_eq_default _ _ (by omega)]

/-- Dropping the empty rows at the bottom does not change the configuration. -/
theorem ofRows_dropBottom (x y : ℤ) (rows : List ℕ) :
    ofRows x y (dropBottom rows) = ofRows x y rows := by
  ext c
  simp only [mem_ofRows_iff_exists, getD_dropBottom]

/-- If the lowest `t` bits of every row are zero (every row is restored by shifting right and
then left), the rows can be shifted right by `t` and the origin moved `t` cells to the right. -/
theorem ofRows_shiftRight (x y : ℤ) (rows : List ℕ) (t : ℕ)
    (h : ∀ r ∈ rows, (r >>> t) <<< t = r) :
    ofRows (x + (t : ℤ)) y (rows.map (· >>> t)) = ofRows x y rows := by
  have hg : ∀ i, (rows.map (· >>> t)).getD i 0 = rows.getD i 0 >>> t := by
    intro i
    simp [List.getD_eq_getElem?_getD]
    cases rows[i]? <;> simp
  have hr : ∀ i, (rows.getD i 0 >>> t) <<< t = rows.getD i 0 := by
    intro i
    by_cases hi : i < rows.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp
  ext c
  simp only [mem_ofRows_iff_exists]
  constructor
  · rintro ⟨i, j, hj, rfl⟩
    rw [hg, Nat.testBit_shiftRight] at hj
    exact ⟨i, t + j, hj, by rw [Nat.cast_add, add_assoc]⟩
  · rintro ⟨i, j, hj, rfl⟩
    rw [← hr i, Nat.testBit_shiftLeft] at hj
    simp only [ge_iff_le, Bool.and_eq_true, decide_eq_true_eq] at hj
    refine ⟨i, j - t, by rw [hg]; exact hj.2, ?_⟩
    rw [Nat.cast_sub hj.1]
    ext <;> simp

/-- A candidate for the position of the lowest set bit of `m` (`0` for `m = 0`), by a fixed
number of bitwise operations. Nothing is proved about it: `Snapshot.trim` checks its use. -/
def lowBit (m : ℕ) : ℕ := (m &&& (m ^^^ (m - 1))).log2

namespace Snapshot

/-- The **trimmed form** of a snapshot: the same configuration in its bounding box. Empty rows
at the top and at the bottom are dropped and the rows are shifted so that some row has its
lowest bit set; the empty configuration becomes the empty window at the origin `(0, 0)`.

The column shift `t` is proposed by `lowBit` and applied only if it passes the check that every
row is restored by shifting right and then left by `t`; so `cells_trim` holds whatever `lowBit`
computes. That the result is the bounding box, hence a normal form, is not proved. -/
def trim (s : Snapshot) : Snapshot :=
  let p := dropTop s.y₀ (dropBottom s.rows)
  if p.2 = [] then ⟨0, 0, []⟩
  else
    let t := lowBit (p.2.foldl (· ||| ·) 0)
    if p.2.all (fun r => (r >>> t) <<< t == r) then ⟨s.x₀ + (t : ℤ), p.1, p.2.map (· >>> t)⟩
    else ⟨s.x₀, p.1, p.2⟩

/-- **Trimming does not change the configuration.** -/
@[simp] theorem cells_trim (s : Snapshot) : s.trim.cells = s.cells := by
  have h : ofRows s.x₀ (dropTop s.y₀ (dropBottom s.rows)).1 (dropTop s.y₀ (dropBottom s.rows)).2 =
      s.cells := by
    rw [ofRows_dropTop, ofRows_dropBottom, cells]
  unfold trim
  simp only
  split_ifs with h1 h2
  · rw [← h, h1, cells, ofRows_nil, ofRows_nil]
  · rw [← h, cells]
    exact ofRows_shiftRight _ _ _ _ (by simpa using h2)
  · exact h

/-- Snapshots with the same trimmed form encode the same configuration. -/
theorem cells_eq_of_trim_eq {s t : Snapshot} (h : s.trim = t.trim) : s.cells = t.cells := by
  rw [← cells_trim s, h, cells_trim]

/-! ### Generations -/

/-- One generation without trimming: the window grows by one cell on every side. -/
def stepRaw (s : Snapshot) : Snapshot := ⟨s.x₀ - 1, s.y₀ - 1, stepRows s.rows⟩

/-- `stepRaw` is one generation of Conway's rule. -/
@[simp] theorem cells_stepRaw (s : Snapshot) : s.stepRaw.cells = conway.step s.cells :=
  (step_ofRows s.x₀ s.y₀ s.rows).symm

/-- One generation, in trimmed form. -/
def step (s : Snapshot) : Snapshot := s.stepRaw.trim

/-- **`Snapshot.step` is one generation of Conway's rule.** -/
@[simp] theorem cells_step (s : Snapshot) : s.step.cells = conway.step s.cells := by
  rw [step, cells_trim, cells_stepRaw]

/-- `n` generations, trimming after each. -/
def evolve (n : ℕ) (s : Snapshot) : Snapshot := step^[n] s

/-- **`Snapshot.evolve n` is `n` generations of Conway's rule.** -/
@[simp] theorem cells_evolve (n : ℕ) (s : Snapshot) :
    (s.evolve n).cells = conway.evolve n s.cells := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [evolve, Function.iterate_succ_apply, ← evolve, ih, cells_step, Rule.evolve_succ']

end Snapshot

/-! ### Finite evolutions -/

/-- A **finite evolution**: an initial snapshot and the snapshots of the following generations.
This is plain data: nothing forces the frames to be the generations of `init`. The Boolean
`Evolution.valid` checks it, and `Evolution.run` computes valid evolutions. -/
structure Evolution where
  /-- The snapshot at generation `0`. -/
  init : Snapshot
  /-- The snapshots at generations `1`, `2`, …. -/
  frames : List Snapshot
deriving DecidableEq, Inhabited

namespace Evolution

/-- The number of generations after the initial snapshot. -/
def generations (e : Evolution) : ℕ := e.frames.length

/-- All snapshots of an evolution: entry `i` is the snapshot at generation `i`. -/
def snapshots (e : Evolution) : List Snapshot := e.init :: e.frames

/-- Check that each snapshot of the list is, as a configuration, one generation after the
previous one, starting from `s`. Trimmed forms are compared. -/
def validFrom : Snapshot → List Snapshot → Bool
  | _, [] => true
  | s, t :: ts => (s.step.trim == t.trim) && validFrom t ts

/-- The validity check of an evolution: every frame is, as a configuration, one generation of
Conway's rule after the previous snapshot. -/
def valid (e : Evolution) : Bool := validFrom e.init e.frames

/-- Soundness of `validFrom`. -/
theorem cells_getElem_of_validFrom {s : Snapshot} {l : List Snapshot}
    (h : validFrom s l = true) (i : ℕ) (hi : i < l.length) :
    l[i].cells = conway.evolve (i + 1) s.cells := by
  induction l generalizing s i with
  | nil => simp at hi
  | cons t ts ih =>
    simp only [validFrom, Bool.and_eq_true, beq_iff_eq] at h
    have ht : t.cells = conway.step s.cells := by
      rw [← Snapshot.cells_eq_of_trim_eq h.1, Snapshot.cells_step]
    cases i with
    | zero => simpa using ht
    | succ i =>
      rw [List.getElem_cons_succ, ih h.2, ht, ← Rule.evolve_succ']

/-- **Soundness of the validity check**: in a valid evolution the snapshot at generation `i`
encodes `conway.evolve i` of the initial configuration. -/
theorem cells_getElem_of_valid {e : Evolution} (h : e.valid = true) (i : ℕ)
    (hi : i < e.snapshots.length) :
    e.snapshots[i].cells = conway.evolve i e.init.cells := by
  cases i with
  | zero => rfl
  | succ i => exact cells_getElem_of_validFrom h i (by simpa [snapshots] using hi)

/-- The snapshots of generations `1` to `n` of `s`, each in trimmed form. -/
def runFrames : Snapshot → ℕ → List Snapshot
  | _, 0 => []
  | s, n + 1 => s.step :: runFrames s.step n

/-- Compute `n` generations from the snapshot `s`. -/
def run (s : Snapshot) (n : ℕ) : Evolution := ⟨s, runFrames s n⟩

/-- `runFrames s n` has `n` entries. -/
@[simp] theorem length_runFrames (s : Snapshot) (n : ℕ) : (runFrames s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [runFrames, ih]

/-- A computed evolution has `n` generations. -/
@[simp] theorem generations_run (s : Snapshot) (n : ℕ) : (run s n).generations = n :=
  length_runFrames s n

/-- The frames of a computed evolution are the iterates of `Snapshot.step`. -/
theorem getElem_runFrames (s : Snapshot) (n i : ℕ) (hi : i < (runFrames s n).length) :
    (runFrames s n)[i] = s.evolve (i + 1) := by
  induction n generalizing s i with
  | zero => simp [runFrames] at hi
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [runFrames, List.getElem_cons_succ]
      rw [ih, Snapshot.evolve, Snapshot.evolve, Function.iterate_succ_apply (n := i + 1)]

/-- **Correctness of `Evolution.run`**: the snapshot at generation `i` encodes
`conway.evolve i` of the initial configuration. -/
theorem cells_getElem_run (s : Snapshot) (n i : ℕ) (hi : i < (run s n).snapshots.length) :
    (run s n).snapshots[i].cells = conway.evolve i s.cells := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [run, snapshots, List.getElem_cons_succ]
    rw [getElem_runFrames, Snapshot.cells_evolve]

/-- A computed evolution passes the validity check. -/
theorem valid_run (s : Snapshot) (n : ℕ) : (run s n).valid = true := by
  simp only [valid, run]
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [runFrames, validFrom, ih]

end Evolution

/-! ### Plaintext -/

/-- The width of a window: the least `w` such that every row is below `2 ^ w`. -/
def rowsWidth (rows : List ℕ) : ℕ :=
  rows.foldl (fun w r => max w (if r = 0 then 0 else r.log2 + 1)) 0

/-- One row of width `w` as plaintext characters: `O` for a live cell and `.` for a dead one. -/
def asciiRow (w r : ℕ) : List Char :=
  (List.range w).map fun j => if r.testBit j then 'O' else '.'

/-- The state of the plaintext reader for one row: the current column, the row read so far and
the first invalid character met. -/
structure AsciiState where
  /-- The column of the next character. -/
  col : ℕ := 0
  /-- The bit mask of the live cells read so far. -/
  row : ℕ := 0
  /-- The first invalid character, if any. -/
  bad : Option Char := none

/-- Read one character of a plaintext row: `O` or `*` is a live cell, `.` or a blank is a dead
cell, anything else is invalid. -/
def asciiStep (st : AsciiState) (c : Char) : AsciiState :=
  if c = 'O' || c = '*' then { st with col := st.col + 1, row := st.row ||| 1 <<< st.col }
  else if c = '.' || c = ' ' then { st with col := st.col + 1 }
  else if st.bad.isSome then st
  else { st with bad := some c }

/-- Read plaintext rows (`O` or `*` alive, `.` or blank dead), from top to bottom. -/
def rowsOfAscii? : List String → Except String (List ℕ)
  | [] => .ok []
  | l :: ls =>
    let st := l.toList.foldl asciiStep {}
    match st.bad with
    | some c => .error s!"plaintext: unexpected character {c.quote}"
    | none => (rowsOfAscii? ls).map (st.row :: ·)

namespace Snapshot

/-- The window of a snapshot as plaintext, one line per row, without trimming. -/
def toAscii (s : Snapshot) : String :=
  String.ofList (List.intercalate ['\n'] (s.rows.map (asciiRow (rowsWidth s.rows))))

/-- The snapshot at the origin `(0, 0)` of a pattern given in plaintext rows; not trimmed. -/
def ofAscii? (lines : List String) : Except String Snapshot :=
  (rowsOfAscii? lines).map (⟨0, 0, ·⟩)

/-- A description of a snapshot: the origin and the plaintext of its bounding box. -/
def describe (s : Snapshot) : String :=
  let t := s.trim
  s!"origin ({t.x₀}, {t.y₀})\n" ++ if t.rows = [] then "(empty)" else t.toAscii

end Snapshot

/-- Snapshots are shown as the origin and the plaintext of the bounding box, for instance
`origin (0, 0)`, `.O.`, `..O`, `OOO` on four lines for the glider. -/
instance : Repr Snapshot := ⟨fun s _ => Std.Format.text s.describe⟩

/-- Evolutions are shown generation by generation. -/
instance : Repr Evolution :=
  ⟨fun e _ => Std.Format.text ("\n\n".intercalate
    (e.snapshots.zipIdx.map fun p => s!"generation {p.2}, " ++ p.1.describe))⟩

/-! ### Run-length encoding -/

/-- The decimal digits of `n` in front of `acc`, most significant first. The first argument
bounds the number of digits (`n` itself is enough). `Nat.toDigits` is not used because it does
not reduce in proofs by `rfl`. -/
def decDigits : ℕ → ℕ → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n < 10 then Char.ofNat (48 + n) :: acc
    else decDigits fuel (n / 10) (Char.ofNat (48 + n % 10) :: acc)

/-- A run of `n` copies of the tag `c` in RLE: nothing for `n = 0`, the bare tag for `n = 1`. -/
def rleRun (n : ℕ) (c : Char) : List Char :=
  if n = 0 then [] else if n = 1 then [c] else decDigits n n [c]

/-- The state of the RLE printer inside a row: the state of the current run, its length and the
finished runs in reverse order. -/
structure RLERowState where
  /-- Whether the current run is a run of live cells. -/
  alive : Bool := false
  /-- The length of the current run. -/
  len : ℕ := 0
  /-- The finished runs, last first. -/
  acc : List (List Char) := []

/-- Process bit `j` of the row `r`. -/
def rleRowStep (r : ℕ) (st : RLERowState) (j : ℕ) : RLERowState :=
  if r.testBit j = st.alive then { st with len := st.len + 1 }
  else ⟨r.testBit j, 1, rleRun st.len (if st.alive then 'o' else 'b') :: st.acc⟩

/-- A row in RLE, without the dead cells after its last live cell. -/
def rleRow (r : ℕ) : List Char :=
  if r = 0 then []
  else
    let st := (List.range (r.log2 + 1)).foldl (rleRowStep r) {}
    (rleRun st.len (if st.alive then 'o' else 'b') :: st.acc).reverse.flatten

/-- Process one row in the RLE printer: the state is the number of pending row ends and the
finished pieces in reverse order. -/
def rleBodyStep (st : ℕ × List (List Char)) (r : ℕ) : ℕ × List (List Char) :=
  if r = 0 then (st.1 + 1, st.2) else (1, rleRow r :: rleRun st.1 '$' :: st.2)

/-- The state of the RLE reader. -/
structure RLEState where
  /-- Only blanks have been read on the current line. -/
  lineStart : Bool := true
  /-- The current line is a comment line or the header line. -/
  skip : Bool := false
  /-- The end mark `!` has been read. -/
  done : Bool := false
  /-- The first invalid character, if any. -/
  bad : Option Char := none
  /-- The run count read so far (`0` if there is none). -/
  count : ℕ := 0
  /-- The column of the next cell of the current row. -/
  col : ℕ := 0
  /-- The current row. -/
  row : ℕ := 0
  /-- The finished rows, last first. -/
  acc : List ℕ := []

/-- Read one character of an RLE string. Lines whose first non-blank character is `#` or `x`
are comments and the header; in the body, digits form a run count, `b` is a run of dead cells,
`o` a run of live cells, `$` a run of row ends and `!` the end mark; blanks and line breaks
are ignored and everything after `!` is ignored. -/
def rleStep (st : RLEState) (c : Char) : RLEState :=
  if st.done || st.bad.isSome then st
  else if c = '\n' then { st with lineStart := true, skip := false }
  else if st.skip || c = ' ' || c = '\t' || c = '\r' then st
  else if st.lineStart && (c = '#' || c = 'x') then { st with lineStart := false, skip := true }
  else
    let k := if st.count = 0 then 1 else st.count
    let st := { st with lineStart := false }
    if c.isDigit then { st with count := 10 * st.count + (c.toNat - 48) }
    else if c = 'b' then { st with count := 0, col := st.col + k }
    else if c = 'o' then
      { st with count := 0, col := st.col + k, row := st.row ||| ((1 <<< k - 1) <<< st.col) }
    else if c = '$' then
      { st with
        count := 0, col := 0, row := 0, acc := List.replicate (k - 1) 0 ++ st.row :: st.acc }
    else if c = '!' then { st with done := true }
    else { st with bad := some c }

/-- The rows of a pattern given in RLE (see `rleStep` for the accepted format), from top to
bottom, without the empty rows at the bottom. Bit `j` of row `i` is the cell in column `j` of
line `i` of the pattern. -/
def rowsOfRLE? (s : String) : Except String (List ℕ) :=
  let st := s.toList.foldl rleStep {}
  match st.bad with
  | some c => .error s!"RLE: unexpected character {c.quote}"
  | none => .ok ((st.row :: st.acc).dropWhile (· == 0)).reverse

namespace Snapshot

/-- The window of a snapshot in RLE: the run-length body without a header line (`b` dead, `o`
alive, `$` end of row, `!` end of pattern), on one line. The origin is not recorded, and dead
cells at the end of a row and empty rows at the bottom are omitted. -/
def toRLE (s : Snapshot) : String :=
  String.ofList (['!'] :: (s.rows.foldl rleBodyStep (0, [])).2).reverse.flatten

/-- The snapshot at the origin `(0, 0)` of a pattern given in RLE; not trimmed. -/
def ofRLE? (s : String) : Except String Snapshot := (rowsOfRLE? s).map (⟨0, 0, ·⟩)

end Snapshot

/-! ### JSON

The encoders and decoders below are written with the constructors of `Lean.Json` and the
operations of `Std.TreeMap.Raw` only. The functions of `Lean.Data.Json` (`Json.mkObj`,
`Json.getObjVal?`, `Json.getInt?`, …) are not exposed by the module system, so nothing could be
proved about code that calls them. -/

/-- A JSON object, as a search tree of its fields. -/
abbrev JsonFields : Type := Std.TreeMap.Raw String Json compare

/-- An integer as a JSON number (mantissa `z`, exponent `0`). -/
def intToJson (z : ℤ) : Json := .num ⟨z, 0⟩

/-- Read an integer from a JSON number with exponent `0`. -/
def intOfJson? : Json → Except String ℤ
  | .num ⟨z, 0⟩ => .ok z
  | _ => .error "expected an integer"

/-- A cell as the JSON array `[x, y]`. -/
def cellToJson (c : ℤ × ℤ) : Json := .arr #[intToJson c.1, intToJson c.2]

/-- Read a cell from a JSON array `[x, y]` of two integers. -/
def cellOfJson? : Json → Except String (ℤ × ℤ)
  | .arr #[.num ⟨x, 0⟩, .num ⟨y, 0⟩] => .ok (x, y)
  | _ => .error "expected a cell [x, y] with integer coordinates"

/-- A list of cells as a JSON array of arrays `[x, y]`. -/
def cellsToJson (l : List (ℤ × ℤ)) : Json := .arr (l.map cellToJson).toArray

/-- Read a list of cells from a JSON array of arrays `[x, y]`. -/
def cellsOfJson? : Json → Except String (List (ℤ × ℤ))
  | .arr a => a.toList.mapM cellOfJson?
  | _ => .error "expected an array of cells"

/-- Decoding an encoded cell gives the cell. -/
theorem cellOfJson?_cellToJson (c : ℤ × ℤ) : cellOfJson? (cellToJson c) = .ok c := rfl

/-- Mapping an encoder over a list and then a decoder that inverts it up to `g` gives the list
mapped by `g`. -/
theorem mapM_map_eq_ok {α β γ : Type} (enc : α → β) (dec : β → Except String γ) (g : α → γ)
    (h : ∀ a, dec (enc a) = .ok (g a)) (l : List α) :
    (l.map enc).mapM dec = .ok (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.mapM_cons, h, ih]
    rfl

/-- **Round trip for cell lists** (JSON values): decoding an encoded list gives the list. -/
theorem cellsOfJson?_cellsToJson (l : List (ℤ × ℤ)) : cellsOfJson? (cellsToJson l) = .ok l := by
  have h := mapM_map_eq_ok cellToJson cellOfJson? id cellOfJson?_cellToJson l
  rw [List.map_id] at h
  simpa [cellsOfJson?, cellsToJson] using h

namespace Snapshot

/-- The fields of the JSON object of a snapshot, see `Snapshot.toJson`. -/
def toJsonFields (s : Snapshot) : JsonFields :=
  ((((∅ : JsonFields).insert "x" (intToJson s.trim.x₀)).insert "y" (intToJson s.trim.y₀)).insert
    "rle" (.str s.trim.toRLE)).insert "cells" (cellsToJson s.trim.toCellList)

/-- The JSON object `{"x": x₀, "y": y₀, "rle": "…", "cells": [[x, y], …]}` of the trimmed form
of a snapshot: the origin and the RLE body of the bounding box, and the list of live cells.
The two encodings are redundant. Rows are never written as JSON numbers. -/
protected def toJson (s : Snapshot) : Json := .obj s.toJsonFields

/-- Read a snapshot from the fields of a JSON object, see `Snapshot.fromJson?`. -/
def ofJsonFields? (m : JsonFields) : Except String Snapshot :=
  match m["cells"]? with
  | some c =>
    match cellsOfJson? c with
    | .ok l => .ok (ofCellList l)
    | .error e => .error s!"snapshot, field \"cells\": {e}"
  | none =>
    match m["rle"]? with
    | some (.str r) =>
      match (m["x"]?.getD (intToJson 0) |> intOfJson?), (m["y"]?.getD (intToJson 0) |> intOfJson?),
        rowsOfRLE? r with
      | .ok x, .ok y, .ok rows => .ok ⟨x, y, rows⟩
      | .error e, _, _ => .error s!"snapshot, field \"x\": {e}"
      | _, .error e, _ => .error s!"snapshot, field \"y\": {e}"
      | _, _, .error e => .error s!"snapshot, field \"rle\": {e}"
    | some _ => .error "snapshot: the field \"rle\" must be a string"
    | none => .error "snapshot: expected a field \"cells\" or a field \"rle\""

/-- Read a snapshot from a JSON object. If there is a field `"cells"` (an array of cells
`[x, y]`), the snapshot is built from it by `Snapshot.ofCellList` and the other fields are
ignored. Otherwise there must be a field `"rle"` with an RLE string, placed at the origin given
by the integer fields `"x"` and `"y"` (each `0` if absent). -/
protected def fromJson? : Json → Except String Snapshot
  | .obj m => ofJsonFields? m
  | _ => .error "snapshot: expected a JSON object"

/-- **Round trip for snapshots** (JSON values): decoding the JSON value of a snapshot gives the
snapshot of the cell list of its trimmed form. -/
theorem fromJson?_toJson (s : Snapshot) :
    Snapshot.fromJson? s.toJson = .ok (ofCellList s.trim.toCellList) := by
  have h : s.toJsonFields["cells"]? = some (cellsToJson s.trim.toCellList) := by
    rw [toJsonFields, Std.TreeMap.Raw.getElem?_insert_self]
    exact ((Std.TreeMap.Raw.WF.emptyc.insert).insert).insert
  rw [Snapshot.toJson, Snapshot.fromJson?, ofJsonFields?, h]
  simp only [cellsOfJson?_cellsToJson]

/-- **Round trip for snapshots, in terms of configurations**: decoding the JSON value of a
snapshot succeeds and gives a snapshot of the same configuration. -/
theorem cells_fromJson?_toJson (s : Snapshot) :
    ∃ t, Snapshot.fromJson? s.toJson = .ok t ∧ t.cells = s.cells :=
  ⟨_, fromJson?_toJson s, by rw [cells_ofCellList, toFinset_toCellList, cells_trim]⟩

end Snapshot

/-- Snapshots are written as `{"x": x₀, "y": y₀, "rle": "…", "cells": [[x, y], …]}`. -/
instance : ToJson Snapshot := ⟨Snapshot.toJson⟩

/-- Snapshots are read from `"cells"`, or else from `"rle"` with `"x"` and `"y"`. -/
instance : FromJson Snapshot := ⟨Snapshot.fromJson?⟩

namespace Evolution

/-- The fields of the JSON object of an evolution, see `Evolution.toJson`. -/
def toJsonFields (e : Evolution) : JsonFields :=
  ((∅ : JsonFields).insert "generations" (intToJson e.generations)).insert "frames"
    (.arr (e.snapshots.map Snapshot.toJson).toArray)

/-- The JSON object `{"generations": n, "frames": [snapshot, …]}` of an evolution. The array
has `n + 1` entries: entry `i` is the snapshot at generation `i`, so the first entry is the
initial snapshot. -/
protected def toJson (e : Evolution) : Json := .obj e.toJsonFields

/-- Read an evolution from the fields of a JSON object, see `Evolution.fromJson?`. -/
def ofJsonFields? (m : JsonFields) : Except String Evolution :=
  match m["frames"]? with
  | some (.arr a) =>
    match a.toList.mapM Snapshot.fromJson? with
    | .ok (s :: ss) =>
      match m["generations"]? with
      | none => .ok ⟨s, ss⟩
      | some j =>
        match intOfJson? j with
        | .ok n =>
          if n = ss.length then .ok ⟨s, ss⟩
          else .error "evolution: \"generations\" must be the number of frames minus one"
        | .error e => .error s!"evolution, field \"generations\": {e}"
    | .ok [] => .error "evolution: \"frames\" must not be empty"
    | .error e => .error s!"evolution, field \"frames\": {e}"
  | _ => .error "evolution: expected a field \"frames\" with an array of snapshots"

/-- Read an evolution from a JSON object with a non-empty array `"frames"` of snapshots, the
first of which is the initial snapshot. The field `"generations"` is optional; if present it
must be the number of frames minus one. The result is **untrusted data**: nothing is known
about it until `Evolution.valid` has been checked. -/
protected def fromJson? : Json → Except String Evolution
  | .obj m => ofJsonFields? m
  | _ => .error "evolution: expected a JSON object"

/-- **Round trip for evolutions** (JSON values): decoding the JSON value of an evolution gives
the evolution with every snapshot replaced by the snapshot of the cell list of its trimmed
form. -/
theorem fromJson?_toJson (e : Evolution) :
    Evolution.fromJson? e.toJson =
      .ok ⟨.ofCellList e.init.trim.toCellList,
        e.frames.map fun s => .ofCellList s.trim.toCellList⟩ := by
  have hwf : ((∅ : JsonFields).insert "generations" (intToJson e.generations)).WF :=
    Std.TreeMap.Raw.WF.emptyc.insert
  have h1 : e.toJsonFields["frames"]? =
      some (.arr (e.snapshots.map Snapshot.toJson).toArray) := by
    rw [toJsonFields, Std.TreeMap.Raw.getElem?_insert_self hwf]
  have h2 : e.toJsonFields["generations"]? = some (intToJson e.generations) := by
    rw [toJsonFields, Std.TreeMap.Raw.getElem?_insert hwf,
      Std.TreeMap.Raw.getElem?_insert_self Std.TreeMap.Raw.WF.emptyc]
    simp
  have h3 := mapM_map_eq_ok Snapshot.toJson Snapshot.fromJson? _ Snapshot.fromJson?_toJson
    e.snapshots
  rw [Evolution.toJson, Evolution.fromJson?, ofJsonFields?, h1]
  simp only [snapshots, List.map_cons] at h3
  simp only [snapshots, List.map_cons, h3, h2]
  simp [intOfJson?, intToJson, generations]

end Evolution

/-- Evolutions are written as `{"generations": n, "frames": [snapshot, …]}`. -/
instance : ToJson Evolution := ⟨Evolution.toJson⟩

/-- Evolutions are read from a non-empty array `"frames"` of snapshots. -/
instance : FromJson Evolution := ⟨Evolution.fromJson?⟩

/-! ### Pattern literals

`meta` code cannot call the functions above, so the two readers are repeated as `meta`
definitions; the fixtures at the end of the file compare the two copies. -/

/-- `meta` copy of `rleStep`. -/
meta def rleStepM (st : RLEState) (c : Char) : RLEState :=
  if st.done || st.bad.isSome then st
  else if c = '\n' then { st with lineStart := true, skip := false }
  else if st.skip || c = ' ' || c = '\t' || c = '\r' then st
  else if st.lineStart && (c = '#' || c = 'x') then { st with lineStart := false, skip := true }
  else
    let k := if st.count = 0 then 1 else st.count
    let st := { st with lineStart := false }
    if c.isDigit then { st with count := 10 * st.count + (c.toNat - 48) }
    else if c = 'b' then { st with count := 0, col := st.col + k }
    else if c = 'o' then
      { st with count := 0, col := st.col + k, row := st.row ||| ((1 <<< k - 1) <<< st.col) }
    else if c = '$' then
      { st with
        count := 0, col := 0, row := 0, acc := List.replicate (k - 1) 0 ++ st.row :: st.acc }
    else if c = '!' then { st with done := true }
    else { st with bad := some c }

/-- `meta` copy of `rowsOfRLE?`. -/
meta def rowsOfRLEM (s : String) : Except String (List ℕ) :=
  let st := s.toList.foldl rleStepM {}
  match st.bad with
  | some c => .error s!"unexpected character {c.quote}"
  | none => .ok ((st.row :: st.acc).dropWhile (· == 0)).reverse

/-- `meta` copy of `asciiStep`. -/
meta def asciiStepM (st : AsciiState) (c : Char) : AsciiState :=
  if c = 'O' || c = '*' then { st with col := st.col + 1, row := st.row ||| 1 <<< st.col }
  else if c = '.' || c = ' ' then { st with col := st.col + 1 }
  else if st.bad.isSome then st
  else { st with bad := some c }

/-- `meta` copy of `rowsOfAscii?`. -/
meta def rowsOfAsciiM : List String → Except String (List ℕ)
  | [] => .ok []
  | l :: ls =>
    let st := l.toList.foldl asciiStepM {}
    match st.bad with
    | some c => .error s!"unexpected character {c.quote}"
    | none => (rowsOfAsciiM ls).map (st.row :: ·)

/-- `rle% "bob$2bo$3o!"` is the list of rows of the pattern given in RLE, here `[2, 4, 7]`. The
string is read **when the term is elaborated** and the term is the explicit list literal, of
type `List ℕ`: the row of each line as a bit mask whose least significant bit is the leftmost
cell, in the encoding of `ofRows`. The format is that of `rowsOfRLE?`; a malformed string is an
error. -/
syntax (name := rleTerm) "rle% " str : term

/-- The elaborator of `rle%`. -/
@[term_elab rleTerm] meta def elabRle : Elab.Term.TermElab := fun stx _ => do
  let some s := stx[1].isStrLit? | Elab.throwUnsupportedSyntax
  match rowsOfRLEM s with
  | .ok rows => return toExpr rows
  | .error e => throwErrorAt stx[1] "rle%: {e}"

/-- `cells% ".O." "..O" "OOO"` is the list of rows of the pattern given in plaintext, one string
per row from top to bottom (`O` or `*` alive, `.` or blank dead), here `[2, 4, 7]`. The strings
are read **when the term is elaborated** and the term is the explicit list literal, of type
`List ℕ`, in the encoding of `ofRows`. Any other character is an error. -/
syntax (name := cellsTerm) "cells%" (ppSpace str)+ : term

/-- The elaborator of `cells%`. -/
@[term_elab cellsTerm] meta def elabCells : Elab.Term.TermElab := fun stx _ => do
  let lines ← stx[1].getArgs.toList.mapM fun a =>
    match a.isStrLit? with
    | some s => pure s
    | none => Elab.throwUnsupportedSyntax
  match rowsOfAsciiM lines with
  | .ok rows => return toExpr rows
  | .error e => throwErrorAt stx[1] "cells%: {e}"

/-! ### Sanity and round-trip fixtures

The theorems are proved by `rfl`: both sides are evaluated by the kernel. The `#guard` commands
are executable tests run at compile time; they are **not proofs**. -/

/-- The glider `.O. / ..O / OOO` at the origin, used in the fixtures. -/
def gliderSnapshot : Snapshot := ⟨0, 0, [2, 4, 7]⟩

/-- The R-pentomino, used in the executable fixtures. -/
def rPentominoSnapshot : Snapshot := ⟨0, 0, rle% "b2o$2o$bo!"⟩

/-- **Sanity** (RLE reader): the glider. -/
theorem ofRLE?_glider : Snapshot.ofRLE? "bob$2bo$3o!" = .ok gliderSnapshot := rfl

set_option maxRecDepth 8192 in
/-- **Sanity** (RLE reader): comment lines, the header line, line breaks and text after `!` are
skipped, and a run count applies to row ends. -/
theorem ofRLE?_file :
    Snapshot.ofRLE? "#N Glider\n#C a comment\nx = 3, y = 5, rule = B3/S23\nbob$2bo$\n3o2$o!xyz" =
      .ok ⟨0, 0, [2, 4, 7, 0, 1]⟩ := rfl

/-- **Sanity** (RLE reader, rejected fixture): an unknown tag is an error. -/
theorem ofRLE?_rejects : (Snapshot.ofRLE? "bob$2bq$3o!").toOption = none := rfl

/-- **Sanity** (RLE printer): the glider; dead cells at the end of a row are omitted. -/
theorem toRLE_glider : gliderSnapshot.toRLE = "bo$2bo$3o!" := rfl

/-- **Sanity** (RLE printer): run counts, empty rows inside and below the pattern. -/
theorem toRLE_fixture : (⟨0, 0, [0, 4096, 0, 0, 15, 0]⟩ : Snapshot).toRLE = "$12bo3$4o!" := rfl

/-- **Sanity** (plaintext): the glider. -/
theorem toAscii_glider : gliderSnapshot.toAscii = ".O.\n..O\nOOO" := rfl

/-- **Sanity** (plaintext reader): the glider. -/
theorem ofAscii?_glider : Snapshot.ofAscii? [".O.", "..*", "OOO"] = .ok gliderSnapshot := rfl

/-- **Sanity** (cell lists): the cells of the glider, sorted by row and then by column. -/
theorem toCellList_glider :
    gliderSnapshot.toCellList = [(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)] := rfl

/-- **Sanity** (cell lists): a shuffled list with a repetition, away from the origin. -/
theorem ofCellList_fixture :
    Snapshot.ofCellList [(-3, 9), (-4, 7), (-2, 9), (-4, 9), (-2, 8), (-4, 7)] =
      ⟨-4, 7, [1, 4, 7]⟩ := rfl

/-- **Sanity** (trimming): empty rows and columns around the glider are removed. -/
theorem trim_fixture : Snapshot.trim ⟨0, 0, [0, 8, 16, 28, 0]⟩ = ⟨2, 1, [2, 4, 7]⟩ := rfl

/-- **Sanity** (trimming, degenerate case): an empty window becomes the empty window at the
origin. -/
theorem trim_empty : Snapshot.trim ⟨5, 7, [0, 0]⟩ = ⟨0, 0, []⟩ := rfl

/-- **Sanity** (generations): four generations move the glider by `(1, 1)`, in agreement with
`glider_evolve_four`. -/
theorem evolve_glider : gliderSnapshot.evolve 4 = ⟨1, 1, [2, 4, 7]⟩ := rfl

/-- **Sanity** (validity check, accepted fixture): an untrimmed window of the next generation
of the glider is accepted. -/
theorem valid_fixture : Evolution.valid ⟨gliderSnapshot, [⟨-1, 0, [0, 10, 12, 4]⟩]⟩ = true := rfl

/-- **Sanity** (validity check, rejected fixture): the glider is not its own successor. -/
theorem not_valid_fixture : Evolution.valid ⟨gliderSnapshot, [gliderSnapshot]⟩ = false := rfl

/-- **Sanity** (pattern literals): `rle%` and `cells%` elaborate to the explicit rows. -/
theorem rows_literal_fixture :
    rle% "bob$2bo$3o!" = [2, 4, 7] ∧ cells% ".O." "..O" "OOO" = [2, 4, 7] := ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
/-- **Sanity** (pattern literals): the `meta` reader used by `rle%` agrees with `rowsOfRLE?` on
the Gosper glider gun. -/
theorem rowsOfRLE?_gosperGun :
    rowsOfRLE? "24bo$22bobo$12b2o6b2o12b2o$11bo3bo4b2o12b2o$2o8bo5bo3b2o$2o8bo3bob2o4bobo$\
      10bo5bo7bo$11bo3bo$12b2o!" =
    .ok (rle% "24bo$22bobo$12b2o6b2o12b2o$11bo3bo4b2o12b2o$2o8bo5bo3b2o$2o8bo3bob2o4bobo$\
      10bo5bo7bo$11bo3bo$12b2o!") := rfl

/-- **Sanity** (pattern literals, rejected fixtures): malformed strings are refused. -/
example : True := by
  fail_if_success
    have : rle% "bob$2bq$3o!" = [2, 4, 7] := rfl
  fail_if_success
    have : cells% ".O." "..o" "OOO" = [2, 4, 7] := rfl
  trivial

/-- **Round trip** (JSON value, fixture): the glider is recovered exactly. -/
theorem fromJson?_toJson_glider :
    Snapshot.fromJson? gliderSnapshot.toJson = .ok gliderSnapshot :=
  Snapshot.fromJson?_toJson gliderSnapshot

-- Executable fixtures (not proofs). The `#guard` commands below are deliberate tests, so the
-- linter against `#`-commands is switched off for the rest of this file.
set_option linter.hashCommand false

-- Printed forms.
#guard gliderSnapshot.describe == "origin (0, 0)\n.O.\n..O\nOOO"
#guard (toJson gliderSnapshot).compress ==
  "{\"cells\":[[1,0],[2,1],[0,2],[1,2],[2,2]],\"rle\":\"bo$2bo$3o!\",\"x\":0,\"y\":0}"
-- The JSON value agrees with the one built by `Json.mkObj` and the `ToJson` instances of Lean.
#guard (toJson gliderSnapshot).compress == (Json.mkObj [("x", toJson (0 : ℤ)),
  ("y", toJson (0 : ℤ)), ("rle", toJson "bo$2bo$3o!"),
  ("cells", toJson [[(1 : ℤ), 0], [2, 1], [0, 2], [1, 2], [2, 2]])]).compress
-- String-level round trips through `Json.compress`, `Json.pretty` and `Json.parse`.
#guard (Json.parse (toJson gliderSnapshot).compress >>= fromJson?).toOption == some gliderSnapshot
#guard (Json.parse (toJson gliderSnapshot).pretty >>= fromJson?).toOption == some gliderSnapshot
-- Reading: `"cells"` has priority; otherwise `"rle"` with the origin, which defaults to `(0, 0)`.
#guard (Json.parse "{\"x\": -3, \"y\": 2, \"rle\": \"bob$2bo$3o!\"}" >>= fromJson?).toOption ==
  some (⟨-3, 2, [2, 4, 7]⟩ : Snapshot)
#guard (Json.parse "{\"rle\": \"o!\", \"cells\": [[2, 1], [1, 0], [0, 2], [1, 2], [2, 2]]}" >>=
  fromJson?).toOption == some gliderSnapshot
#guard (Json.parse "{\"rle\": \"bob$2bo$3o!\"}" >>= fromJson?).toOption == some gliderSnapshot
-- Rejected inputs: a non-integer coordinate, a missing pattern, a wrong generation count.
#guard (Json.parse "{\"cells\": [[1, 0.5]]}" >>= fromJson? (α := Snapshot)).toOption == none
#guard (Json.parse "{\"x\": 1, \"y\": 2}" >>= fromJson? (α := Snapshot)).toOption == none
#guard (Json.parse "{\"generations\": 3, \"frames\": [{\"rle\": \"o!\"}]}" >>=
  fromJson? (α := Evolution)).toOption == none
-- A longer evolution: 200 generations of the R-pentomino. It passes the validity check, its
-- frames are in normal form and it survives the string-level JSON round trip unchanged.
#guard (Evolution.run rPentominoSnapshot 200).valid
#guard (Evolution.run rPentominoSnapshot 200).snapshots.all fun s =>
  s.trim == s && Snapshot.ofCellList s.toCellList == s &&
    (Snapshot.ofRLE? s.toRLE).toOption == some ⟨0, 0, s.rows⟩
#guard (Json.parse (toJson (Evolution.run rPentominoSnapshot 200)).compress >>=
  fromJson?).toOption == some (Evolution.run rPentominoSnapshot 200)
-- Row masks beyond 64 bits are not damaged (they never appear as JSON numbers).
#guard (Json.parse (toJson (⟨0, 0, [1 ||| 1 <<< 200, 1 <<< 150]⟩ : Snapshot)).compress >>=
  fromJson?).toOption == some (⟨0, 0, [1 ||| 1 <<< 200, 1 <<< 150]⟩ : Snapshot)

end LeanTheory.Life
