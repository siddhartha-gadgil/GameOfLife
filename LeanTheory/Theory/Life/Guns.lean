/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Patterns
public import Mathlib.Data.Finset.Max

/-!
# The Gosper glider gun

The Gosper glider gun emits one glider every 30 generations, forever (research note `N-07`).
On finite configurations a gun is not periodic: its population grows without bound. The
theorem is therefore an invariant for every `n`:

* `gosperGun_evolve`: after `30 * n` generations the configuration is the gun together with
  the `n` gliders emitted so far, the `j`-th of them being the emitted glider `gunGlider` evolved
  for `30 * j` generations;
* `gosperGun_isGun`: the same, as an instance of the definition `IsGun`;
* `gunGlider_isSpaceship`, `gunGlider_evolve_one`: the emitted glider is a spaceship of period
  4 and displacement `(1, 1)`, a phase of the catalogue glider;
* `gosperGun_not_bounded`: the evolution of the gun leaves every finite region, in agreement
  with `Rule.eventually_periodic_of_bounded`.

## Method

The proof is the template for statements about components that emit signals forever.

1. *Certificates*: `gosperGun_evolve_thirty` (the gun after 30 generations is the gun plus one
   glider), `gosperGun_evolve_sixty`, and an upper bound for the `y`-coordinates of the gun
   with its newest glider during the 30 generations that follow (`gosperGun_snd_le`, thirty
   certificates).
2. *Signals in flight*: the emitted glider at every age lies in a known band of rows
   (`gunGlider_snd`), so gliders emitted at least 30 generations apart never interact
   (`evolve_train`).
3. *Independence along a run* (`Rule.evolve_union_of_forall_sep`): the gun with its newest glider
   evolves independently of the older gliders, because a band of at least three empty rows
   separates them at every generation.

## Window tools

`orRows`, `padRows` with `ofRows_orRows`, `ofRows_padRows`: a union of windows as one window, used
to split the result of a certificate into its parts; `snd_lt_of_mem_ofRows`.

Pattern data: the gun is the pattern of the LifeWiki page "Gosper glider gun" (36 cells,
36 × 9), RLE
(two lines to be joined)
`24bo11b$22bobo11b$12b2o6b2o12b2o$11bo3bo4b2o12b2o$2o8bo5bo3b2o14b$`
`2o8bo3bob2o4bobo11b$10bo5bo7bo11b$11bo3bo20b$12b2o!`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### Window tools -/

/-- The cells of a window lie above its last row. -/
theorem snd_lt_of_mem_ofRows {x y : ℤ} {rows : List ℕ} {c : Cell} (h : c ∈ ofRows x y rows) :
    c.2 < y + rows.length := by
  have hy := (le_of_mem_ofRows h).2
  rw [mem_ofRows, bitAt] at h
  by_contra hc
  obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c.2 - y by omega)
  rw [hi, rowZ_natCast, List.getD_eq_default _ _ (by omega), tb_zero] at h
  exact Bool.false_ne_true h

/-- Row-by-row union of two lists of rows. -/
def orRows : List ℕ → List ℕ → List ℕ
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a ||| b) :: orRows as bs

/-- Row `i` of `orRows A B`. -/
theorem getD_orRows (A B : List ℕ) (i : ℕ) :
    (orRows A B).getD i 0 = A.getD i 0 ||| B.getD i 0 := by
  induction A generalizing B i with
  | nil => simp [orRows]
  | cons a as ih =>
    cases B with
    | nil => simp [orRows]
    | cons b bs =>
      cases i with
      | zero => simp [orRows]
      | succ i => simpa [orRows] using ih bs i

/-- The window of `orRows A B` is the union of the windows of `A` and `B` at the same origin. -/
theorem ofRows_orRows (x y : ℤ) (A B : List ℕ) :
    ofRows x y (orRows A B) = ofRows x y A ∪ ofRows x y B := by
  ext c
  have hrow : ∀ b : ℤ, rowZ (orRows A B) b = rowZ A b ||| rowZ B b := by
    intro b
    by_cases hb : 0 ≤ b
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hb
      simp only [rowZ_natCast, getD_orRows]
    · simp [rowZ_of_neg _ (not_le.1 hb)]
  rw [mem_union, mem_ofRows, mem_ofRows, mem_ofRows, bitAt, bitAt, bitAt, hrow, tb, tb, tb,
    Nat.testBit_or, Bool.and_or_distrib_left, Bool.or_eq_true]

/-- A list of rows moved `t` cells to the right and `pre` rows down inside a larger window. -/
def padRows (pre t : ℕ) (rows : List ℕ) : List ℕ :=
  List.replicate pre 0 ++ rows.map (· <<< t)

/-- Rows of a list with empty rows in front. -/
theorem rowZ_replicate_append (pre : ℕ) (L : List ℕ) (b : ℤ) :
    rowZ (List.replicate pre 0 ++ L) b = rowZ L (b - pre) := by
  induction pre generalizing b with
  | zero => simp
  | succ pre ih =>
    have h := rowZ_zero_cons (List.replicate pre 0 ++ L) (b - 1)
    rw [sub_add_cancel] at h
    rw [List.replicate_succ, List.cons_append, h, ih]
    congr 1
    push_cast
    omega

/-- Rows of a list shifted to the right. -/
theorem rowZ_map_shiftLeft (rows : List ℕ) (t : ℕ) (b : ℤ) :
    rowZ (rows.map (· <<< t)) b = rowZ rows b <<< t := by
  by_cases hb : 0 ≤ b
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    have h := List.getD_map (f := (· <<< t)) (l := rows) (d := 0) (n := i)
    simp only [Nat.zero_shiftLeft] at h
    rw [rowZ_natCast, rowZ_natCast, h]
  · simp [rowZ_of_neg _ (not_le.1 hb)]

/-- The window of `padRows pre t rows` is the window of `rows` at the displaced origin. -/
theorem ofRows_padRows (x y : ℤ) (pre t : ℕ) (rows : List ℕ) :
    ofRows x y (padRows pre t rows) = ofRows (x + t) (y + pre) rows := by
  ext ⟨a, b⟩
  rw [mem_ofRows, mem_ofRows, bitAt, bitAt, padRows, rowZ_replicate_append, rowZ_map_shiftLeft,
    tb_shiftLeft]
  have e1 : a - x - (t : ℤ) = a - (x + t) := by omega
  have e2 : b - y - (pre : ℤ) = b - (y + pre) := by omega
  rw [e1, e2]

/-- A window as a padded window at the origin. -/
theorem ofRows_eq_padRows (x y : ℤ) (pre t : ℕ) (rows : List ℕ) (hx : x = t) (hy : y = pre) :
    ofRows x y rows = ofRows 0 0 (padRows pre t rows) := by
  rw [ofRows_padRows, zero_add, zero_add, hx, hy]

/-- If every cell of `S` has `y ≤ a` and every cell of `T` has `y > a + r`, then `S` and `T`
are at distance greater than `r`. -/
theorem sep_of_snd_lt {r : ℕ} {S T : Finset Cell} {a : ℤ} (hS : ∀ s ∈ S, s.2 ≤ a)
    (hT : ∀ t ∈ T, a + r < t.2) : Sep r S T := by
  intro s hs t ht hn
  have h1 := hS s hs
  have h2 := hT t ht
  obtain ⟨-, -, h3, -⟩ := hn
  omega

/-- A finite configuration lies above some row. -/
theorem exists_snd_le (B : Finset Cell) : ∃ Y : ℤ, ∀ c ∈ B, c.2 ≤ Y := by
  induction B using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨max Y a.2, fun c hc => ?_⟩
    rcases mem_insert.1 hc with rfl | h
    · exact le_max_right _ _
    · exact (hY c h).trans (le_max_left _ _)

/-! ### The gun and its glider -/

/-- The Gosper glider gun. 36 cells.
```
........................O...........
......................O.O...........
............OO......OO............OO
...........O...O....OO............OO
OO........O.....O...OO..............
OO........O...O.OO....O.O...........
..........O.....O.......O...........
...........O...O....................
............OO......................
```
-/
def gosperGun : Finset Cell :=
  ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816,
    12288]

/-- The glider emitted by `gosperGun`, in the position and phase in which it is first complete
(generation 30).
```
O..
.OO
OO.
```
-/
def gunGlider : Finset Cell := ofRows 23 9 [1, 6, 3]

/-- One generation later the emitted glider is the catalogue glider, translated. -/
theorem gunGlider_evolve_one :
    conway.evolve 1 gunGlider = translate (23, 9) Pattern.glider := by
  rw [Pattern.glider, translate_ofRows]
  life_cert

/-- The emitted glider is a spaceship of period exactly 4 and displacement `(1, 1)`. -/
theorem gunGlider_isSpaceship : IsSpaceship gunGlider 4 (1, 1) := by
  refine ⟨ofRows_nonempty rfl 23 9, by simp, by norm_num, ?_, fun k hk0 hk w => ?_⟩
  · rw [gunGlider, translate_ofRows]
    life_cert
  · obtain ⟨a, b⟩ := w
    rw [gunGlider, translate_ofRows]
    interval_cases k <;> (life_eval; exact ofRows_ne_of_rows_ne rfl rfl (by simp))

/-- In its first four generations the emitted glider stays in rows 9 to 12. -/
theorem gunGlider_phase_snd (r : ℕ) (hr : r < 4) :
    ∀ c ∈ conway.evolve r gunGlider, 9 ≤ c.2 ∧ c.2 ≤ 12 := by
  interval_cases r <;>
    (life_eval
     intro c hc
     have h1 := (le_of_mem_ofRows hc).2
     have h2 := snd_lt_of_mem_ofRows hc
     simp only [List.length_cons, List.length_nil] at h2
     omega)

/-- In its first four generations the emitted glider is not empty. -/
theorem gunGlider_phase_nonempty (r : ℕ) (hr : r < 4) :
    (conway.evolve r gunGlider).Nonempty := by
  interval_cases r <;> (life_eval; exact ofRows_nonempty rfl _ _)

/-- The emitted glider at age `t`, as a translate of one of its first four generations. -/
theorem gunGlider_evolve (t : ℕ) :
    conway.evolve t gunGlider =
      translate ((t / 4) • ((1, 1) : Cell)) (conway.evolve (t % 4) gunGlider) := by
  have ht : t = t % 4 + t / 4 * 4 := by omega
  conv_lhs => rw [ht]
  rw [Rule.evolve_add, conway.evolve_mul_of_evolve_eq_translate gunGlider_isSpaceship.2.2.2.1,
    Rule.evolve_translate]

/-- **Signal in flight**: at age `t` the emitted glider lies in rows `9 + t / 4` to
`12 + t / 4`. -/
theorem gunGlider_snd (t : ℕ) :
    ∀ c ∈ conway.evolve t gunGlider,
      9 + ((t / 4 : ℕ) : ℤ) ≤ c.2 ∧ c.2 ≤ 12 + ((t / 4 : ℕ) : ℤ) := by
  intro c hc
  rw [gunGlider_evolve, mem_translate] at hc
  have h := gunGlider_phase_snd (t % 4) (Nat.mod_lt _ (by norm_num)) _ hc
  simp only [Prod.snd_sub, Prod.smul_snd, nsmul_eq_mul, mul_one] at h
  omega

/-- The emitted glider never dies. -/
theorem gunGlider_evolve_nonempty (t : ℕ) : (conway.evolve t gunGlider).Nonempty := by
  rw [gunGlider_evolve]
  exact translate_nonempty.2 (gunGlider_phase_nonempty _ (Nat.mod_lt _ (by norm_num)))

/-! ### Trains of gliders -/

/-- The gliders of ages `a ∈ I`: the union of the emitted glider evolved for `a` generations. -/
def train (I : Finset ℕ) : Finset Cell := I.biUnion fun a => conway.evolve a gunGlider

/-- Ages at least 30 generations apart. -/
def Spaced (I : Finset ℕ) : Prop := ∀ a ∈ I, ∀ b ∈ I, a < b → a + 30 ≤ b

@[simp] theorem train_empty : train ∅ = ∅ := rfl

/-- A train with one more glider. -/
theorem train_insert (a : ℕ) (I : Finset ℕ) :
    train (insert a I) = conway.evolve a gunGlider ∪ train I := by
  simp [train, biUnion_insert]

/-- Membership in a train. -/
theorem mem_train {I : Finset ℕ} {c : Cell} :
    c ∈ train I ↔ ∃ a ∈ I, c ∈ conway.evolve a gunGlider := by
  simp [train]

/-- **Gliders in flight do not interact**: a train of gliders emitted at least 30 generations
apart evolves glider by glider. -/
theorem evolve_train {I : Finset ℕ} (hI : Spaced I) (k : ℕ) :
    conway.evolve k (train I) = train (I.image (· + k)) := by
  induction I using Finset.induction_on_max generalizing k with
  | empty => simp
  | insert a s hmax ih =>
    have hs : Spaced s := fun x hx y hy hxy =>
      hI x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy
    have hsep : ∀ i < k, Sep 2 (conway.evolve i (conway.evolve a gunGlider))
        (conway.evolve i (train s)) := by
      intro i _
      refine Sep.symm (sep_of_snd_lt (a := 6 + (((i + a) / 4 : ℕ) : ℤ)) ?_ ?_)
      · intro c hc
        rw [ih hs i, mem_train] at hc
        obtain ⟨b', hb', hc⟩ := hc
        obtain ⟨b, hb, rfl⟩ := mem_image.1 hb'
        have h1 := (gunGlider_snd _ c hc).2
        have h2 := hI b (mem_insert_of_mem hb) a (mem_insert_self a s) (hmax b hb)
        omega
      · intro c hc
        rw [← Rule.evolve_add] at hc
        have h1 := (gunGlider_snd _ c hc).1
        push_cast
        omega
    rw [train_insert, conway.evolve_union_of_forall_sep hsep, ih hs k, ← Rule.evolve_add,
      image_insert, train_insert, add_comm k a]

/-! ### The gun for all time -/

/-- **Certificate**: after 30 generations the gun has emitted one glider and is back in its
initial state. -/
theorem gosperGun_evolve_thirty : conway.evolve 30 gosperGun = gosperGun ∪ gunGlider := by
  have h : conway.evolve 30 gosperGun =
      ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776,
        34816, 12288, 8388608, 50331648, 25165824] := by
    life_cert
  rw [h, gosperGun, gunGlider, ofRows_eq_padRows 23 9 9 23 _ rfl rfl, ← ofRows_orRows]
  rfl

/-- **Certificate**: in the next 30 generations the gun emits a second glider and the first one
flies on undisturbed. -/
theorem gosperGun_evolve_sixty :
    conway.evolve 30 (gosperGun ∪ gunGlider) =
      gosperGun ∪ gunGlider ∪ conway.evolve 30 gunGlider := by
  have h : conway.evolve (30 + 30) gosperGun =
      ofRows 0 0 [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776,
        34816, 12288, 8388608, 50331648, 25165824, 0, 0, 0, 0, 0, 5368709120, 6442450944,
        2147483648] := by
    life_cert
  have hg : conway.evolve 30 gunGlider = ofRows 30 17 [5, 6, 2] := by
    life_cert
  rw [← gosperGun_evolve_thirty, ← Rule.evolve_add, h, gosperGun_evolve_thirty, hg, gosperGun,
    gunGlider, ofRows_eq_padRows 23 9 9 23 _ rfl rfl, ofRows_eq_padRows 30 17 17 30 _ rfl rfl,
    ← ofRows_orRows, ← ofRows_orRows]
  rfl

/-- **Certificates**: during the 30 generations after an emission, the gun together with its
newest glider stays in the rows up to `6 + (30 + k) / 4`. -/
theorem gosperGun_snd_le (k : ℕ) (hk : k < 30) :
    ∀ c ∈ conway.evolve (30 + k) gosperGun, c.2 ≤ 6 + (((30 + k) / 4 : ℕ) : ℤ) := by
  interval_cases k <;>
    (life_eval
     intro c hc
     have h2 := snd_lt_of_mem_ofRows hc
     simp only [List.length_cons, List.length_nil] at h2
     omega)

/-- The ages, at generation `30 * (m + 1)`, of the gliders other than the newest one. -/
def gunAges (m : ℕ) : Finset ℕ := (range m).image fun j => 30 * (j + 1)

theorem spaced_gunAges (m : ℕ) : Spaced (gunAges m) := by
  intro a ha b hb hab
  obtain ⟨i, -, rfl⟩ := mem_image.1 ha
  obtain ⟨j, -, rfl⟩ := mem_image.1 hb
  omega

theorem gunAges_succ (m : ℕ) : gunAges (m + 1) = insert 30 ((gunAges m).image (· + 30)) := by
  ext a
  simp only [gunAges, mem_image, mem_range, mem_insert, exists_exists_and_eq_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    cases j with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr ⟨j, by omega, by omega⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨j + 1, by omega, by omega⟩

/-- The gun at generation `30 * (m + 1)`: the gun, its newest glider and the older gliders. -/
theorem gosperGun_evolve_succ (m : ℕ) :
    conway.evolve (30 * (m + 1)) gosperGun = gosperGun ∪ gunGlider ∪ train (gunAges m) := by
  induction m with
  | zero => simp [gunAges, gosperGun_evolve_thirty]
  | succ m ih =>
    have e : 30 * (m + 1 + 1) = 30 + 30 * (m + 1) := by omega
    have hsep : ∀ k < 30, Sep 2 (conway.evolve k (gosperGun ∪ gunGlider))
        (conway.evolve k (train (gunAges m))) := by
      intro k hk
      refine sep_of_snd_lt (a := 6 + (((30 + k) / 4 : ℕ) : ℤ)) ?_ ?_
      · intro c hc
        rw [← gosperGun_evolve_thirty, ← Rule.evolve_add, add_comm k 30] at hc
        exact gosperGun_snd_le k hk c hc
      · intro c hc
        rw [evolve_train (spaced_gunAges m) k, mem_train] at hc
        obtain ⟨b', hb', hc⟩ := hc
        obtain ⟨b, hb, rfl⟩ := mem_image.1 hb'
        obtain ⟨j, -, rfl⟩ := mem_image.1 hb
        have h1 := (gunGlider_snd _ c hc).1
        push_cast
        omega
    rw [e, Rule.evolve_add, ih, conway.evolve_union_of_forall_sep hsep, gosperGun_evolve_sixty,
      evolve_train (spaced_gunAges m) 30, gunAges_succ, train_insert, union_assoc]

/-- **The Gosper glider gun, for all time**: after `30 * n` generations the configuration is the
gun together with `n` gliders, the `j`-th of which is the emitted glider at age `30 * j`. -/
theorem gosperGun_evolve (n : ℕ) :
    conway.evolve (30 * n) gosperGun =
      gosperGun ∪ (range n).biUnion fun j => conway.evolve (30 * j) gunGlider := by
  cases n with
  | zero => simp
  | succ m =>
    have h : ((range (m + 1)).biUnion fun j => conway.evolve (30 * j) gunGlider) =
        gunGlider ∪ train (gunAges m) := by
      ext c
      simp only [mem_biUnion, mem_range, mem_union, mem_train, gunAges, mem_image,
        exists_exists_and_eq_and]
      constructor
      · rintro ⟨j, hj, hc⟩
        cases j with
        | zero => exact Or.inl hc
        | succ j => exact Or.inr ⟨j, by omega, hc⟩
      · rintro (hc | ⟨j, hj, hc⟩)
        · exact ⟨0, by omega, hc⟩
        · exact ⟨j + 1, by omega, hc⟩
    rw [gosperGun_evolve_succ, h, union_assoc]

/-- A gun of period `p`: a configuration `G` that, every `p` generations, is back in its initial
state together with one more copy of the signal `g`, the earlier copies evolving undisturbed.
The signal is required to be a spaceship. -/
def IsGun (G : Finset Cell) (p : ℕ) (g : Finset Cell) : Prop :=
  0 < p ∧ (∃ q v, IsSpaceship g q v) ∧
    ∀ n, conway.evolve (p * n) G = G ∪ (range n).biUnion fun j => conway.evolve (p * j) g

/-- The Gosper glider gun is a gun of period 30 emitting gliders. -/
theorem gosperGun_isGun : IsGun gosperGun 30 gunGlider :=
  ⟨by norm_num, ⟨4, (1, 1), gunGlider_isSpaceship⟩, gosperGun_evolve⟩

/-! ### Sanity -/

/-- **Sanity** (a gun is not confined): the evolution of the gun leaves every finite region. In
particular it is not eventually periodic and its population is not what "period 30" would
suggest. -/
theorem gosperGun_not_bounded (B : Finset Cell) : ∃ n, ¬ conway.evolve n gosperGun ⊆ B := by
  obtain ⟨Y, hB⟩ := exists_snd_le B
  refine ⟨30 * (Y.toNat + 1), fun hsub => ?_⟩
  obtain ⟨c, hc⟩ := gunGlider_evolve_nonempty (30 * Y.toNat)
  have h1 := (gunGlider_snd _ c hc).1
  have h2 : c ∈ conway.evolve (30 * (Y.toNat + 1)) gosperGun := by
    rw [gosperGun_evolve]
    exact mem_union_right _ (mem_biUnion.2 ⟨Y.toNat, mem_range.2 (by omega), hc⟩)
  have h3 := hB c (hsub h2)
  omega

/-- **Sanity** (a still life is not a gun): the block emits nothing, so it is not a gun for the
glider with any period. -/
theorem not_isGun_block (p : ℕ) : ¬ IsGun Pattern.block p gunGlider := by
  rintro ⟨hp, -, h⟩
  have h1 := h 1
  rw [Pattern.block_isStillLife.evolve] at h1
  have h2 : gunGlider ⊆ Pattern.block := by
    intro c hc
    rw [h1]
    exact mem_union_right _ (mem_biUnion.2 ⟨0, by simp, by simpa using hc⟩)
  have h3 : ((23, 9) : Cell) ∈ gunGlider := by
    rw [gunGlider, mem_ofRows]
    rfl
  have h4 := snd_lt_of_mem_ofRows (h2 h3)
  simp at h4

end LeanTheory.Life
