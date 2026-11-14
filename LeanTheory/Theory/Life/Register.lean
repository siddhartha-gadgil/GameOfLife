/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Reactions

/-!
# Pipelining of the sliding block memory

The block memory (`Theory/Life/SlidingBlock`) is operated by salvos launched one behind the
other on the same diagonal lane. A salvo launched later flies behind the earlier ones at the
same speed and has to act on the block after the earlier reactions are over, without being
disturbed by them (research note `N-11`, "Register design after the user decision", item 1).
This module proves that salvos launched at least **13 cells apart** act on the block in order.

## Contents

* `Op` (`inc`, `dec`) with `Op.salvo`, `Op.apply`, `Op.time`; `Op.evolve_salvo_union_counter`
  restates `push` and `pull` uniformly.
* Footprints bounded from both sides: `Op.salvo_snd` (rows of a salvo in its first four
  generations), `reaction_flight_strip` and `Op.salvo_flight` (a flying salvo stays in a strip
  of rows that moves with it), `Op.zero_reaction` (certificates: an operation at position `0`
  stays in the rows 0 to 13, and at generation `i ≤ 32` no cell is above row `i / 4 - 1`),
  `push_zero_reaction`.
* `Op.reaction`: one operation, with the salvo anywhere on its lane, as a reaction of duration
  `4 * (q + 8)` (`q` cells of flight). The pattern stays in the rows `a` to `k + 13`, where `a`
  is the displacement of the salvo and `k` the position of the block, and at generation `i` no
  cell is above the row `a + i / 4 - 1`: the whole operation stays below a line that advances
  at the speed of the salvos.
* `Op.evolve_translate_salvo`: one operation with the salvo anywhere on its lane, exact time.
* Lists of pending operations: `launch` (the salvos), `SpacedLaunch` (the spacing condition),
  `run` (the operations applied in order), `finishTime` (when the last one is complete);
  `launch_flight` (a spaced train of salvos flies as a whole).
* **Pipelining**: `pipeline_translate` (the induction), `pipeline`, `pipeline_nat`.
* **Two operations**: `two_ops`, and `two_ops_of_time` with the time as a hypothesis.

## Method

The head of the train is one operation (`Op.reaction`); the rest of the train is in flight
behind it (`launch_flight`). The footprint of the operation lies below a moving line, that of
the rest above a parallel line, so `Reaction.par` applies for the `4 * (q + 8)` generations
of the operation. Then the rest of the train, displaced by `q + 8` cells, faces the block at
its new position, and the statement for the shorter train applies. The induction therefore
carries a displacement `(a, a)` of the whole train.

## The spacing constant

Rows are `y`-coordinates and the salvos move towards larger `y`. A salvo displaced by `-d`
occupies rows up to `9 - d + i / 4` at generation `i`; the operation ahead of it occupies only
rows from `i / 4 - 1` on. The two are independent as long as two rows between them are empty,
that is for `9 - d + 2 < -1`, which is `13 ≤ d`. These footprints bound rows only. Numerical
observations (not proved here): with footprints that bound only rows the constant cannot be
lowered, since at generation 25 the push reaction at position `0` reaches up to row 5 while a
salvo `d` cells behind reaches down to row `15 - d`; the two-operation statement itself holds
from `d = 11` on after `inc` and from `d = 9` on after `dec` (checked for `k ≤ 3`, `d < 40`).
`two_ops_inc_inc_ten_ne` proves that it fails for `d = 10` after `inc`.

No hypothesis on the sign of the positions is needed: by translation invariance the statements
hold for a block anywhere on the diagonal, provided the first salvo is launched before the
block (launch distance at least `-k`). For natural positions and distances this is automatic
(`pipeline_nat`), also when a decrement at position `0` moves the block to position `-1`.

**Sanity.** `Op.dec_apply_inc_apply`, `Op.inc_apply_dec_apply`, `run_append`, `run_eq_add`
(`Op.apply` and `run` compose as expected), `finishTime_pair` (the time for two operations),
`inc_then_dec` (an increment followed 13 cells behind by a decrement returns the block to its
position, for every position), `pipeline_three` (a concrete train of three operations),
`two_ops_inc_inc_ten_ne` (rejected fixture: at distance 10 the result is not the block at
position 2), `not_spacedLaunch_fixture` (rejected fixture for `SpacedLaunch`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### Operations -/

/-- An operation on the block memory. -/
inductive Op
  /-- Increment: push the block one cell away. -/
  | inc
  /-- Decrement: pull the block one cell closer. -/
  | dec

/-- The salvo performing an operation, at its standard launch position. -/
def Op.salvo : Op → Finset Cell
  | .inc => pushSalvo
  | .dec => pullSalvo

/-- The effect of an operation on the position of the block. -/
def Op.apply : Op → ℤ → ℤ
  | .inc, k => k + 1
  | .dec, k => k - 1

/-- The duration of the reaction of the salvo with the block, without the flight. -/
def Op.time : Op → ℕ
  | .inc => 32
  | .dec => 26

/-- Operations commute with shifts of the position. -/
theorem Op.apply_add (o : Op) (k a : ℤ) : o.apply (k + a) = o.apply k + a := by
  cases o <;> simp only [Op.apply] <;> omega

/-- An operation lowers the position by at most one. -/
theorem Op.sub_one_le_apply (o : Op) (k : ℤ) : k - 1 ≤ o.apply k := by
  cases o <;> simp only [Op.apply] <;> omega

/-- An operation raises the position by at most one. -/
theorem Op.apply_le_add_one (o : Op) (k : ℤ) : o.apply k ≤ k + 1 := by
  cases o <;> simp only [Op.apply] <;> omega

/-- The reaction of an operation takes between 26 and 32 generations. -/
theorem Op.time_bounds (o : Op) : 26 ≤ o.time ∧ o.time ≤ 32 := by
  cases o <;> simp [Op.time]

/-- **`push` and `pull`, uniformly**: the salvo of the operation `o`, launched from its standard
place, moves the block from position `k` to position `o.apply k`. -/
theorem Op.evolve_salvo_union_counter (o : Op) (k : ℕ) :
    conway.evolve (4 * k + o.time) (o.salvo ∪ counter k) = counter (o.apply k) := by
  cases o
  · exact push k
  · exact pull k

/-- Every salvo moves one cell diagonally every four generations. -/
theorem Op.salvo_evolve_four (o : Op) :
    conway.evolve 4 o.salvo = translate (1, 1) o.salvo := by
  cases o
  · exact pushSalvo_evolve_four
  · exact pullSalvo_evolve_four

/-! ### Footprints bounded from both sides -/

/-- In its first four generations a salvo stays in the rows 0 to 9. -/
theorem Op.salvo_snd (o : Op) (r : ℕ) (hr : r < 4) :
    ∀ c ∈ conway.evolve r o.salvo, 0 ≤ c.2 ∧ c.2 ≤ 9 := by
  cases o <;> simp only [Op.salvo] <;> interval_cases r <;>
    (life_eval
     intro c hc
     have h1 := (le_of_mem_ofRows hc).2
     have h2 := snd_lt_of_mem_ofRows hc
     simp only [List.length_cons, List.length_nil] at h2
     omega)

/-- Sets of cells with two empty rows between them are far apart. -/
theorem farApart_of_snd {A B : Set Cell} {u : ℤ} (hA : ∀ c ∈ A, c.2 ≤ u)
    (hB : ∀ c ∈ B, u + 2 < c.2) : FarApart 2 A B := by
  intro a ha b hb hn
  have h1 := hA a ha
  have h2 := hB b hb
  obtain ⟨-, -, h3, -⟩ := hn
  omega

/-- **Flight in a strip**: a pattern that moves one cell diagonally every four generations and
stays in the rows `lo` to `Y` during its first four generations flies `q` cells in `4 * q`
generations, inside a strip of rows that advances one row every four generations. -/
theorem reaction_flight_strip {S : Finset Cell} {lo Y : ℤ}
    (hS : conway.evolve 4 S = translate (1, 1) S)
    (hY : ∀ r < 4, ∀ c ∈ conway.evolve r S, lo ≤ c.2 ∧ c.2 ≤ Y) (q : ℕ) :
    Reaction S (translate ((q : ℤ), (q : ℤ)) S) (4 * q)
      (fun i => {c : Cell | lo + ((i / 4 : ℕ) : ℤ) ≤ c.2 ∧ c.2 ≤ Y + ((i / 4 : ℕ) : ℤ)}) := by
  refine ⟨(reaction_flight hS (fun r hr c hc => (hY r hr c hc).2) q).evolve_eq,
    fun i _ c hc => ?_⟩
  rw [mem_coe, evolve_eq_translate_mod hS, mem_translate] at hc
  have h := hY (i % 4) (Nat.mod_lt _ (by norm_num)) _ hc
  simp only [Prod.snd_sub, Prod.smul_snd, nsmul_eq_mul, mul_one] at h
  change lo + ((i / 4 : ℕ) : ℤ) ≤ c.2 ∧ c.2 ≤ Y + ((i / 4 : ℕ) : ℤ)
  omega

/-- **Flight of a salvo**: the salvo displaced by `(a, a)` flies `q` cells in `4 * q`
generations inside the strip of the rows `a + i / 4` to `a + 9 + i / 4`. -/
theorem Op.salvo_flight (o : Op) (a : ℤ) (q : ℕ) :
    Reaction (translate (a, a) o.salvo) (translate (a + q, a + q) o.salvo) (4 * q)
      (fun i => {c : Cell | a + ((i / 4 : ℕ) : ℤ) ≤ c.2 ∧ c.2 ≤ a + 9 + ((i / 4 : ℕ) : ℤ)}) := by
  have h := (reaction_flight_strip o.salvo_evolve_four o.salvo_snd q).translate (a, a)
  rw [translate_translate, Prod.mk_add_mk] at h
  refine h.mono fun i _ => ?_
  rintro _ ⟨c, ⟨h1, h2⟩, rfl⟩
  change a + ((i / 4 : ℕ) : ℤ) ≤ (a, a).2 + c.2 ∧ (a, a).2 + c.2 ≤ a + 9 + ((i / 4 : ℕ) : ℤ)
  constructor <;> simp only <;> omega

/-- The pushing salvo with the block at position `0`, as one window. -/
theorem pushSalvo_union_counter_zero :
    pushSalvo ∪ counter 0 = ofRows 0 0 [4, 8, 14, 0, 0, 2, 4, 647, 768, 256, 0, 384, 384] := by
  have hc : counter 0 = ofRows 0 0 (padRows 11 7 [3, 3]) := by
    rw [ofRows_padRows, counter]
    norm_num
  rw [hc, pushSalvo, ← ofRows_orRows]
  rfl

/-- **Certificates**: an operation at position `0` as a reaction of 32 generations (the pull is
over after 26 of them). The pattern stays in the rows 0 to 13, and at generation `i` no cell is
above the row `i / 4 - 1`: the reaction keeps below a line that moves at the speed of the
salvos. -/
theorem Op.zero_reaction (o : Op) :
    Reaction (o.salvo ∪ counter 0) (counter (o.apply 0)) 32
      (fun i => {c : Cell | 0 ≤ c.2 ∧ ((i / 4 : ℕ) : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ 13}) := by
  cases o
  · have e : Op.inc.apply 0 = 1 := by simp [Op.apply]
    rw [e]
    refine ⟨push_zero, fun i hi => ?_⟩
    simp only [Op.salvo]
    rw [pushSalvo_union_counter_zero]
    interval_cases i <;>
      (life_eval
       intro c hc
       have h1 := (le_of_mem_ofRows (mem_coe.1 hc)).2
       have h2 := snd_lt_of_mem_ofRows (mem_coe.1 hc)
       simp only [List.length_cons, List.length_nil] at h2
       change 0 ≤ c.2 ∧ ((_ : ℕ) : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ 13
       omega)
  · have e : Op.dec.apply 0 = -1 := by simp [Op.apply]
    rw [e]
    simp only [Op.salvo]
    rw [pullSalvo_union_counter_zero]
    refine ⟨by life_cert, fun i hi => ?_⟩
    interval_cases i <;>
      (life_eval
       intro c hc
       have h1 := (le_of_mem_ofRows (mem_coe.1 hc)).2
       have h2 := snd_lt_of_mem_ofRows (mem_coe.1 hc)
       simp only [List.length_cons, List.length_nil] at h2
       change 0 ≤ c.2 ∧ ((_ : ℕ) : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ 13
       omega)

/-- The push at position `0` as a reaction; throughout its 32 generations the pattern stays in
the rows 0 to 13 (compare `pull_zero_reaction`). -/
theorem push_zero_reaction :
    Reaction (pushSalvo ∪ counter 0) (counter 1) 32 (fun _ => {c : Cell | 0 ≤ c.2 ∧ c.2 ≤ 13}) :=
  Op.inc.zero_reaction.mono fun _ _ _ hc => ⟨hc.1, hc.2.2⟩

/-- The counter storing `k` lies in the rows up to `12 + k`. -/
theorem counter_snd_le (k : ℤ) : ∀ c ∈ counter k, c.2 ≤ 12 + k := by
  intro c hc
  have h := snd_lt_of_mem_ofRows hc
  simp only [List.length_cons, List.length_nil] at h
  omega

/-! ### One operation, with the salvo anywhere on its lane -/

/-- **One operation as a reaction.** The salvo is displaced by `(a, a)` and the block is at
position `k = a + q`, so that the salvo flies `q` cells before it meets the block. After
`4 * (q + 8)` generations the block is at position `o.apply k` and nothing else is left.
Throughout, the pattern stays in the rows `a` to `k + 13`, and at generation `i` no cell is
above the row `a + i / 4 - 1`. -/
theorem Op.reaction (o : Op) (k a : ℤ) (q : ℕ) (hq : k - a = q) :
    Reaction (translate (a, a) o.salvo ∪ counter k) (counter (o.apply k)) (4 * (q + 8))
      (fun i => {c : Cell | a ≤ c.2 ∧ a + ((i / 4 : ℕ) : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ k + 13}) := by
  have hfar : ∀ i < 4 * q, FarApart 2
      {c : Cell | a + ((i / 4 : ℕ) : ℤ) ≤ c.2 ∧ c.2 ≤ a + 9 + ((i / 4 : ℕ) : ℤ)}
      (counter k : Set Cell) := by
    intro i hi
    refine farApart_of_snd (u := a + 9 + ((i / 4 : ℕ) : ℤ)) (fun c hc => hc.2) fun c hc => ?_
    have h := counter_snd k c (mem_coe.1 hc)
    omega
  have hflight := (o.salvo_flight a q).par ((counter_isStillLife k).reaction (4 * q)) hfar
  have hk : a + q = k := by omega
  rw [hk] at hflight
  have hz := o.zero_reaction.translate (k, k)
  rw [translate_union, translate_counter, translate_counter, zero_add, ← Op.apply_add,
    zero_add] at hz
  have hn : 4 * (q + 8) = 4 * q + 32 := by omega
  rw [hn]
  refine (hflight.seq hz).mono fun i _ => ?_
  by_cases hik : i ≤ 4 * q
  · simp only [hik, ↓reduceIte]
    rintro c (⟨h1, h2⟩ | hc)
    · change a ≤ c.2 ∧ a + ((i / 4 : ℕ) : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ k + 13
      omega
    · have h1 := counter_snd k c (mem_coe.1 hc)
      have h2 := counter_snd_le k c (mem_coe.1 hc)
      change a ≤ c.2 ∧ a + ((i / 4 : ℕ) : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ k + 13
      omega
  · simp only [hik, ↓reduceIte]
    rintro _ ⟨c, h1, rfl⟩
    have h2 : 0 ≤ c.2 ∧ (((i - 4 * q) / 4 : ℕ) : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ 13 := h1
    change a ≤ (k, k).2 + c.2 ∧ a + ((i / 4 : ℕ) : ℤ) - 1 ≤ (k, k).2 + c.2 ∧
      (k, k).2 + c.2 ≤ k + 13
    simp only
    omega

/-- **One operation, exact time.** With the salvo displaced by `(a, a)` and the block at
position `k = a + q`, the block is at position `o.apply k` after `4 * q + o.time`
generations. For `a = 0` this is `Op.evolve_salvo_union_counter`. -/
theorem Op.evolve_translate_salvo (o : Op) (k a : ℤ) (q : ℕ) (hq : k - a = q) :
    conway.evolve (4 * q + o.time) (translate (a, a) o.salvo ∪ counter k) =
      counter (o.apply k) := by
  have hk : (q : ℤ) + a = k := by omega
  have h : translate (a, a) (o.salvo ∪ counter q) = translate (a, a) o.salvo ∪ counter k := by
    rw [translate_union, translate_counter, hk]
  rw [← h, Rule.evolve_translate, o.evolve_salvo_union_counter q, translate_counter,
    ← Op.apply_add, hk]

/-! ### Trains of pending operations -/

/-- The salvos of a list of pending operations. A pair `(o, d)` stands for the salvo of the
operation `o` placed `d` cells behind its standard launch position; the head of the list is
the operation that acts first. -/
def launch : List (Op × ℤ) → Finset Cell
  | [] => ∅
  | p :: l => translate (-p.2, -p.2) p.1.salvo ∪ launch l

/-- `SpacedLaunch D b l`: the first launch distance of the list `l` is at least `b`, and every
further one exceeds the one before it by at least `D`. -/
def SpacedLaunch (D : ℤ) : ℤ → List (Op × ℤ) → Prop
  | _, [] => True
  | b, p :: l => b ≤ p.2 ∧ SpacedLaunch D (p.2 + D) l

/-- The position of the block after the operations of the list, applied in order to the
position `k`. -/
def run : List (Op × ℤ) → ℤ → ℤ
  | [], k => k
  | p :: l, k => run l (p.1.apply k)

/-- The generation at which the last operation of the list is complete, for a block that starts
at position `k`: if the last operation `o` is launched at distance `d` and finds the block at
position `k'`, this is `4 * (k' + d) + o.time`. -/
def finishTime : ℤ → List (Op × ℤ) → ℤ
  | _, [] => 0
  | k, [p] => 4 * (k + p.2) + p.1.time
  | k, p :: p' :: l => finishTime (p.1.apply k) (p' :: l)

/-- The bound on the first launch distance can be lowered. -/
theorem SpacedLaunch.mono {D b b' : ℤ} {l : List (Op × ℤ)} (h : SpacedLaunch D b l) (hb : b' ≤ b) :
    SpacedLaunch D b' l := by
  cases l with
  | nil => trivial
  | cons p l => exact ⟨hb.trans h.1, h.2⟩

/-- A displaced train: the first salvo and the displaced rest. -/
theorem translate_launch_cons (a : ℤ) (p : Op × ℤ) (l : List (Op × ℤ)) :
    translate (a, a) (launch (p :: l)) =
      translate (a - p.2, a - p.2) p.1.salvo ∪ translate (a, a) (launch l) := by
  rw [launch, translate_union, translate_translate, Prod.mk_add_mk, ← sub_eq_add_neg]

/-- **Flight of a train**: salvos launched at least 12 cells apart fly as a whole. A train
whose launch distances are at least `b`, displaced by `(a, a)`, stays in the rows up to
`a - b + 9 + i / 4`. -/
theorem launch_flight {D : ℤ} (hD : 12 ≤ D) (l : List (Op × ℤ)) (b a : ℤ) (q : ℕ)
    (hs : SpacedLaunch D b l) :
    Reaction (translate (a, a) (launch l)) (translate (a + q, a + q) (launch l)) (4 * q)
      (fun i => {c : Cell | c.2 ≤ a - b + 9 + ((i / 4 : ℕ) : ℤ)}) := by
  induction l generalizing b with
  | nil =>
    simp only [launch, translate_empty]
    exact ⟨Rule.evolve_empty _ _, fun i _ => by simp⟩
  | cons p l ih =>
    have hhead := p.1.salvo_flight (a - p.2) q
    have htail := ih (p.2 + D) hs.2
    have hfar : ∀ i < 4 * q, FarApart 2
        {c : Cell | c.2 ≤ a - (p.2 + D) + 9 + ((i / 4 : ℕ) : ℤ)}
        {c : Cell | a - p.2 + ((i / 4 : ℕ) : ℤ) ≤ c.2 ∧
          c.2 ≤ a - p.2 + 9 + ((i / 4 : ℕ) : ℤ)} := by
      intro i _
      refine farApart_of_snd (u := a - (p.2 + D) + 9 + ((i / 4 : ℕ) : ℤ)) (fun c hc => hc)
        fun c hc => ?_
      have h := hc.1
      omega
    have h := htail.par hhead hfar
    have e : a + (q : ℤ) - p.2 = a - p.2 + q := by omega
    rw [translate_launch_cons, translate_launch_cons, e, union_comm,
      union_comm (translate (a - p.2 + q, a - p.2 + q) p.1.salvo)]
    refine h.mono fun i _ => ?_
    have hb := hs.1
    rintro c (hc | ⟨-, hc⟩)
    · have h1 : c.2 ≤ a - (p.2 + D) + 9 + ((i / 4 : ℕ) : ℤ) := hc
      change c.2 ≤ a - b + 9 + ((i / 4 : ℕ) : ℤ)
      omega
    · change c.2 ≤ a - b + 9 + ((i / 4 : ℕ) : ℤ)
      omega

/-- The last operation of a spaced train is not complete before the first one could be. -/
theorem le_finishTime {D : ℤ} (hD : 1 ≤ D) :
    ∀ l : List (Op × ℤ), l ≠ [] → ∀ b k : ℤ, SpacedLaunch D b l →
      4 * (b + k) + 26 ≤ finishTime k l
  | [], h, _, _, _ => absurd rfl h
  | [p], _, b, k, hs => by
    have h1 := hs.1
    have h2 := p.1.time_bounds
    simp only [finishTime]
    omega
  | p :: p' :: l, _, b, k, hs => by
    have ih := le_finishTime hD (p' :: l) (List.cons_ne_nil _ _) (p.2 + D) (p.1.apply k) hs.2
    have h1 := hs.1
    have h2 := p.1.sub_one_le_apply k
    simp only [finishTime]
    omega

/-- **Pipelining, displaced form.** A train of salvos launched at least 13 cells apart,
displaced as a whole by `(a, a)`, whose first salvo is still before the block
(`a - k ≤ d` for its launch distance `d`), acts on the block in order: at the time
`finishTime k l - 4 * a` the block is at the position `run l k` and nothing else is left. -/
theorem pipeline_translate {D : ℤ} (hD : 13 ≤ D) :
    ∀ l : List (Op × ℤ), l ≠ [] → ∀ (k a : ℤ) (t : ℕ), SpacedLaunch D (a - k) l →
      (t : ℤ) = finishTime k l - 4 * a →
      conway.evolve t (translate (a, a) (launch l) ∪ counter k) = counter (run l k)
  | [], h, _, _, _, _, _ => absurd rfl h
  | [p], _, k, a, t, hs, ht => by
    have h0 := hs.1
    obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k - (a - p.2) by omega)
    have ht' : t = 4 * q + p.1.time := by
      simp only [finishTime] at ht
      omega
    rw [translate_launch_cons, launch, translate_empty, union_empty, ht']
    exact p.1.evolve_translate_salvo k (a - p.2) q hq
  | p :: p' :: l, _, k, a, t, hs, ht => by
    have h0 := hs.1
    obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k - (a - p.2) by omega)
    -- the first operation, and the rest of the train in flight behind it
    have h1 := p.1.reaction k (a - p.2) q hq
    have h2 := launch_flight (by omega : 12 ≤ D) (p' :: l) (p.2 + D) a (q + 8) hs.2
    have hfar : ∀ i < 4 * (q + 8), FarApart 2
        {c : Cell | c.2 ≤ a - (p.2 + D) + 9 + ((i / 4 : ℕ) : ℤ)}
        {c : Cell | a - p.2 ≤ c.2 ∧ a - p.2 + ((i / 4 : ℕ) : ℤ) - 1 ≤ c.2 ∧ c.2 ≤ k + 13} := by
      intro i _
      refine farApart_of_snd (u := a - (p.2 + D) + 9 + ((i / 4 : ℕ) : ℤ)) (fun c hc => hc)
        fun c hc => ?_
      have h : a - p.2 + ((i / 4 : ℕ) : ℤ) - 1 ≤ c.2 := hc.2.1
      omega
    have hpar := h2.par h1 hfar
    -- the time that remains is not negative
    have hb := le_finishTime (by omega : 1 ≤ D) (p' :: l) (List.cons_ne_nil _ _) (p.2 + D)
      (p.1.apply k) hs.2
    have hk1 := p.1.sub_one_le_apply k
    have hk2 := p.1.apply_le_add_one k
    have hf : finishTime k (p :: p' :: l) = finishTime (p.1.apply k) (p' :: l) := rfl
    rw [hf] at ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 4 * (q + 8) := ⟨t - 4 * (q + 8), by omega⟩
    rw [Rule.evolve_add, translate_launch_cons,
      union_comm (translate (a - p.2, a - p.2) p.1.salvo), union_assoc, hpar.evolve_eq]
    exact pipeline_translate hD (p' :: l) (List.cons_ne_nil _ _) (p.1.apply k) (a + (q + 8 : ℕ))
      t' (hs.2.mono (by push_cast; omega)) (by push_cast at ht ⊢; omega)

/-- **Pipelining.** Let `l` be a nonempty list of pending operations whose salvos are launched
at least 13 cells apart, the first of them before the block (launch distance at least `-k`; for
a block at a natural position every distance `≥ 0` will do). Then the operations act on the
block in order: at the time `finishTime k l` the configuration is the block at the position
`run l k`, and nothing else. -/
theorem pipeline (l : List (Op × ℤ)) (hl : l ≠ []) (k : ℤ) (t : ℕ) (hs : SpacedLaunch 13 (-k) l)
    (ht : (t : ℤ) = finishTime k l) :
    conway.evolve t (launch l ∪ counter k) = counter (run l k) := by
  have h := pipeline_translate le_rfl l hl k 0 t (by rwa [zero_sub]) (by omega)
  rwa [Prod.mk_zero_zero, translate_zero] at h

/-- The last operation of a spaced train whose first salvo is launched before the block is
complete at a time that is not negative. -/
theorem finishTime_nonneg (l : List (Op × ℤ)) (hl : l ≠ []) (k : ℤ)
    (hs : SpacedLaunch 13 (-k) l) : 0 ≤ finishTime k l := by
  have h := le_finishTime (by norm_num : (1 : ℤ) ≤ 13) l hl (-k) k hs
  omega

/-- **Pipelining, natural positions and distances.** Let `l` be a nonempty list of pending
operations with launch distances `≥ 0` that increase by at least 13 from each to the next, and
let the block be at a natural position `k`. Then at the time `finishTime k l` the configuration
is the block at the position `run l k`, and nothing else. -/
theorem pipeline_nat (l : List (Op × ℤ)) (hl : l ≠ []) (k : ℕ) (hs : SpacedLaunch 13 0 l) :
    conway.evolve (finishTime k l).toNat (launch l ∪ counter k) = counter (run l k) := by
  have hs' : SpacedLaunch 13 (-(k : ℤ)) l := hs.mono (by omega)
  have h := finishTime_nonneg l hl k hs'
  exact pipeline l hl k _ hs' (by omega)

/-! ### Two operations -/

/-- A train of two salvos, the first at its standard launch position. -/
theorem launch_pair (o₁ o₂ : Op) (d : ℤ) (T : Finset Cell) :
    launch [(o₁, 0), (o₂, d)] ∪ T = translate (-d, -d) o₂.salvo ∪ (o₁.salvo ∪ T) := by
  simp only [launch, neg_zero, Prod.mk_zero_zero, translate_zero, union_empty]
  rw [union_assoc, union_left_comm]

/-- **Two operations, time as a hypothesis.** The salvo of `o₁` is launched from the standard
place and the salvo of `o₂` at least 13 cells behind it. The block, at the position `k`, is
moved to `o₁.apply k` and then to `o₂.apply (o₁.apply k)`; the second reaction is complete
`4 * (d + o₁.apply k) + o₂.time` generations after the launch. The position `o₁.apply k` may
be `-1`. -/
theorem two_ops_of_time (o₁ o₂ : Op) (k d t : ℕ) (hd : 13 ≤ d)
    (ht : (t : ℤ) = 4 * (d + o₁.apply k) + o₂.time) :
    conway.evolve t (translate (-(d : ℤ), -(d : ℤ)) o₂.salvo ∪ (o₁.salvo ∪ counter k)) =
      counter (o₂.apply (o₁.apply k)) := by
  rw [← launch_pair]
  refine pipeline [(o₁, 0), (o₂, (d : ℤ))] (List.cons_ne_nil _ _) k t ⟨by omega, ?_, trivial⟩ ?_
  · change (0 : ℤ) + 13 ≤ (d : ℤ)
    omega
  · simp only [finishTime]
    omega

/-- **Two operations.** The salvo of `o₁` is launched from the standard place and the salvo of
`o₂` is launched `d ≥ 13` cells behind it. If the first operation leaves the block at the
natural position `k₁`, then `4 * (d + k₁) + o₂.time` generations after the launch the block is
at the position `o₂.apply (o₁.apply k)` and nothing else is left: the second salvo is not
disturbed by the first reaction and acts when it is over. -/
theorem two_ops (o₁ o₂ : Op) (k k₁ d : ℕ) (hk : o₁.apply k = k₁) (hd : 13 ≤ d) :
    conway.evolve (4 * (d + k₁) + o₂.time)
        (translate (-(d : ℤ), -(d : ℤ)) o₂.salvo ∪ (o₁.salvo ∪ counter k)) =
      counter (o₂.apply (o₁.apply k)) :=
  two_ops_of_time o₁ o₂ k d _ hd (by rw [hk]; push_cast; omega)

/-! ### Sanity -/

/-- **Sanity**: decrement undoes increment. -/
theorem Op.dec_apply_inc_apply (k : ℤ) : Op.dec.apply (Op.inc.apply k) = k := by
  simp [Op.apply]

/-- **Sanity**: increment undoes decrement. -/
theorem Op.inc_apply_dec_apply (k : ℤ) : Op.inc.apply (Op.dec.apply k) = k := by
  simp [Op.apply]

/-- **Sanity**: running a concatenation is running the parts in order. -/
theorem run_append (l l' : List (Op × ℤ)) (k : ℤ) : run (l ++ l') k = run l' (run l k) := by
  induction l generalizing k with
  | nil => rfl
  | cons p l ih => exact ih _

/-- **Sanity**: the operations shift the position by an amount that does not depend on it (the
number of increments minus the number of decrements). -/
theorem run_eq_add (l : List (Op × ℤ)) (k : ℤ) : run l k = k + run l 0 := by
  induction l generalizing k with
  | nil => simp [run]
  | cons p l ih =>
    have h := p.1.apply_add 0 k
    rw [zero_add] at h
    rw [run, run, ih, ih (p.1.apply 0), h]
    omega

/-- **Sanity**: the time for two operations is the flight of the second salvo to the block at
its new position, and the second reaction. -/
theorem finishTime_pair (o₁ o₂ : Op) (d₁ d₂ k : ℤ) :
    finishTime k [(o₁, d₁), (o₂, d₂)] = 4 * (o₁.apply k + d₂) + o₂.time :=
  rfl

/-- **Sanity** (concrete instance): an increment followed 13 cells behind by a decrement
returns the block to its position, for every position `k`. -/
theorem inc_then_dec (k : ℕ) :
    conway.evolve (4 * (13 + (k + 1)) + 26)
        (translate (-13, -13) pullSalvo ∪ (pushSalvo ∪ counter k)) = counter k := by
  have h := two_ops Op.inc Op.dec k (k + 1) 13 (by simp [Op.apply]) le_rfl
  rwa [Op.dec_apply_inc_apply] at h

/-- **Sanity** (concrete train): two increments and a decrement, launched 13 cells apart, move
the block from the position `k` to `k + 1`. -/
theorem pipeline_three (k : ℕ) :
    conway.evolve (4 * (k + 28) + 26)
        (launch [(Op.inc, 0), (Op.inc, 13), (Op.dec, 26)] ∪ counter k) = counter (k + 1) := by
  have h := pipeline [(Op.inc, 0), (Op.inc, 13), (Op.dec, 26)] (List.cons_ne_nil _ _) k
    (4 * (k + 28) + 26) ⟨by omega, by norm_num, by norm_num, trivial⟩
    (by simp only [finishTime, Op.apply, Op.time]; push_cast; omega)
  rw [h]
  simp only [run, Op.apply]
  exact congrArg counter (by omega)

/-- **Sanity** (rejected fixture): distances 0 and 12 are not 13 apart. -/
theorem not_spacedLaunch_fixture : ¬ SpacedLaunch 13 0 [(Op.inc, 0), (Op.dec, 12)] := by
  rintro ⟨-, h, -⟩
  norm_num at h

/-- **Sanity** (the spacing matters): with the second pushing salvo only 10 cells behind the
first one, the block at position `0` is not at position `2` at the time given by `two_ops`
(the result is a honey farm, that is four beehives, and a block at another place). -/
theorem two_ops_inc_inc_ten_ne :
    conway.evolve (4 * (10 + 1) + 32)
        (translate (-10, -10) Op.inc.salvo ∪ (Op.inc.salvo ∪ counter 0)) ≠
      counter (Op.inc.apply (Op.inc.apply 0)) := by
  have h1 : translate (-10, -10) pushSalvo =
      ofRows (-10) (-10) [4, 8, 14, 0, 0, 2, 4, 647, 768, 256] := by
    rw [pushSalvo, translate_ofRows]
    norm_num
  have h2 : pushSalvo =
      ofRows (-10) (-10) (padRows 10 10 [4, 8, 14, 0, 0, 2, 4, 647, 768, 256]) := by
    rw [ofRows_padRows, pushSalvo]
    norm_num
  have h3 : counter 0 = ofRows (-10) (-10) (padRows 21 17 [3, 3]) := by
    rw [ofRows_padRows, counter]
    norm_num
  have hU : translate (-10, -10) Op.inc.salvo ∪ (Op.inc.salvo ∪ counter 0) =
      ofRows (-10) (-10) [4, 8, 14, 0, 0, 2, 4, 647, 768, 256, 4096, 8192, 14336, 0, 0, 2048,
        4096, 662528, 786432, 262144, 0, 393216, 393216] := by
    simp only [Op.salvo]
    rw [h1]
    conv_lhs => rw [h2, h3]
    rw [← ofRows_orRows, ← ofRows_orRows]
    rfl
  have e : counter (Op.inc.apply (Op.inc.apply 0)) = ofRows 9 13 [3, 3] := by
    simp only [Op.apply, counter]
    norm_num
  rw [hU, e]
  life_eval
  exact ofRows_ne rfl rfl (by simp)

end LeanTheory.Life
