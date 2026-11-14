/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Sanity.Life
public import Mathlib.Data.Finset.Powerset

/-!
# Locality, symmetry and composition of evolutions

General theorems, valid for every Life-like rule `R`, that turn finite simulations into
statements about patterns placed in a larger configuration and about unbounded time
(research note `N-04`). Distances are Chebyshev distances on `ℤ × ℤ`.

## Definitions

* `translate v S`: the configuration `S` moved by the vector `v`.
* `Near r c d`: the cells `c` and `d` are at Chebyshev distance at most `r`.
* `nbhd r A`: the radius-`r` neighbourhood of a set `A` of cells.
* `AgreeOn A S T`: the configurations `S` and `T` have the same live cells in the region `A`.
* `Sep r S T`: every cell of `S` is at Chebyshev distance **greater than** `r` from every cell
  of `T`.

## Main results

* **Locality**: `Rule.mem_step_congr` (one generation depends only on a cell and its eight
  neighbours), `Rule.mem_evolve_congr` and `Rule.agreeOn_evolve` (`n` generations at `c` depend
  only on the cells within distance `n` of `c`).
* **Speed of light**: `Rule.exists_mem_near_of_mem_evolve`, `Rule.coe_evolve_subset_nbhd`.
* **Independence**: `Rule.step_union_of_sep` (`Sep 2 S T`, that is distance at least `3`, that
  is `nbhd 1 S` and `nbhd 1 T` disjoint by `sep_two_mul_iff_disjoint_nbhd`, gives
  `step (S ∪ T) = step S ∪ step T`); `Rule.evolve_union_of_forall_sep` (the same along a run, when
  the evolved parts stay separated); `Rule.evolve_union_of_sep` (`Sep (2 * n) S T`, that is
  distance at least `2 * n + 1` at time zero, suffices for `n` generations);
  `Rule.evolve_union_of_sep_of_step_eq` (next to a still life distance at least `n + 2`
  suffices).
* **Equivariance**: `Rule.evolve_map` for every bijection of the grid preserving the neighbour
  relation, with instances `Rule.evolve_translate`, `Rule.evolve_transpose`,
  `Rule.evolve_reflectX`; such bijections are closed under composition and inverse
  (`nbrs_trans`, `nbrs_symm`).
* **Periodicity algebra**: `Rule.evolve_mul_of_evolve_eq`, `Rule.evolve_mod_of_evolve_eq`
  (oscillators), `Rule.evolve_mul_of_evolve_eq_translate` (spaceships).
* **Bounded implies eventually periodic**: `Rule.exists_evolve_eq_of_bounded` (pigeonhole),
  `Rule.evolve_add_sub_of_evolve_eq`, `Rule.eventually_periodic_of_bounded`.

## Sanity and adversarial checks

* `not_step_union_of_disjoint`: independence fails for patterns that are merely disjoint.
* `not_step_union_of_sep_one`: independence fails at distance exactly two, so the constant in
  `Rule.step_union_of_sep`, and the constant `2 * n` of `Rule.evolve_union_of_sep` at `n = 1`,
  cannot be lowered.
* `conway_evolve_two_mul_blinkerH`, `conway_evolve_two_mul_add_one_blinkerH`: the periodicity
  algebra on the blinker.
* `conway_evolve_block`, `conway_evolve_two_blocks`: two separated blocks stay as they are, by
  independence along a run.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### Translation of configurations -/

/-- The configuration `S` translated by the vector `v`. -/
def translate (v : Cell) (S : Finset Cell) : Finset Cell := S.map (Equiv.addLeft v).toEmbedding

/-- A cell lies in the translate by `v` iff moving it back by `v` gives a cell of `S`. -/
theorem mem_translate {v c : Cell} {S : Finset Cell} : c ∈ translate v S ↔ c - v ∈ S := by
  simp only [translate, mem_map, Equiv.coe_toEmbedding, Equiv.coe_addLeft]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨c - v, h, by simp⟩

/-- The translate of a cell of `S` lies in the translate of `S`, and conversely. -/
@[simp] theorem add_mem_translate {v c : Cell} {S : Finset Cell} :
    v + c ∈ translate v S ↔ c ∈ S := by
  simp [mem_translate]

/-- Translation by zero changes nothing. -/
@[simp] theorem translate_zero (S : Finset Cell) : translate 0 S = S := by
  ext c
  simp [mem_translate]

/-- Translations compose by adding the vectors. -/
theorem translate_translate (v w : Cell) (S : Finset Cell) :
    translate v (translate w S) = translate (v + w) S := by
  ext c
  simp [mem_translate, sub_sub]

/-- Translations compose by adding the vectors. -/
theorem translate_add (v w : Cell) (S : Finset Cell) :
    translate (v + w) S = translate v (translate w S) :=
  (translate_translate v w S).symm

/-- The empty configuration is invariant under translation. -/
@[simp] theorem translate_empty (v : Cell) : translate v ∅ = ∅ := rfl

/-- Translation distributes over unions. -/
theorem translate_union (v : Cell) (S T : Finset Cell) :
    translate v (S ∪ T) = translate v S ∪ translate v T :=
  map_union _ _

/-- Translation preserves the number of live cells. -/
@[simp] theorem card_translate (v : Cell) (S : Finset Cell) : (translate v S).card = S.card :=
  card_map _

/-! ### Chebyshev balls, neighbourhoods and agreement -/

/-- `Near r c d`: the cells `c` and `d` are at Chebyshev distance at most `r`. The two-sided
inequalities are the form produced by the speed-of-light theorems of `Sanity/Life`. -/
def Near (r : ℕ) (c d : Cell) : Prop :=
  d.1 - r ≤ c.1 ∧ c.1 ≤ d.1 + r ∧ d.2 - r ≤ c.2 ∧ c.2 ≤ d.2 + r

/-- `Near` in terms of absolute values of coordinate differences. -/
theorem near_iff_abs {r : ℕ} {c d : Cell} :
    Near r c d ↔ |c.1 - d.1| ≤ r ∧ |c.2 - d.2| ≤ r := by
  simp only [Near, abs_le]
  omega

/-- `Near` is the closed ball of the Chebyshev distance. -/
theorem near_iff_max {r : ℕ} {c d : Cell} : Near r c d ↔ max |c.1 - d.1| |c.2 - d.2| ≤ r := by
  rw [near_iff_abs, max_le_iff]

/-- Every cell is within every distance of itself. -/
theorem Near.refl (r : ℕ) (c : Cell) : Near r c c :=
  ⟨by omega, by omega, by omega, by omega⟩

/-- `Near` is symmetric. -/
theorem Near.symm {r : ℕ} {c d : Cell} (h : Near r c d) : Near r d c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- `Near` is symmetric. -/
theorem near_comm {r : ℕ} {c d : Cell} : Near r c d ↔ Near r d c :=
  ⟨Near.symm, Near.symm⟩

/-- A larger radius is a weaker condition. -/
theorem Near.mono {r s : ℕ} {c d : Cell} (h : Near r c d) (hrs : r ≤ s) : Near s c d := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The triangle inequality for the Chebyshev distance. -/
theorem Near.trans {r s : ℕ} {c d e : Cell} (h : Near r c d) (h' : Near s d e) :
    Near (r + s) c e := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6, h7, h8⟩ := h'
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Distance zero means equality. -/
theorem near_zero {c d : Cell} : Near 0 c d ↔ c = d := by
  obtain ⟨x, y⟩ := c
  obtain ⟨a, b⟩ := d
  simp only [Near, Prod.mk.injEq]
  omega

/-- The cells within distance one of `c` are `c` and its eight neighbours. -/
theorem near_one {c d : Cell} : Near 1 d c ↔ d = c ∨ d ∈ nbrs c := by
  obtain ⟨x, y⟩ := c
  obtain ⟨a, b⟩ := d
  simp only [Near, mem_nbrs, ne_eq, Prod.mk.injEq]
  omega

/-- The radius-`r` neighbourhood of a set of cells: the cells within Chebyshev distance `r` of
some cell of the set. -/
def nbhd (r : ℕ) (A : Set Cell) : Set Cell := {d | ∃ c ∈ A, Near r d c}

/-- Membership in a neighbourhood. -/
theorem mem_nbhd {r : ℕ} {A : Set Cell} {d : Cell} : d ∈ nbhd r A ↔ ∃ c ∈ A, Near r d c :=
  Iff.rfl

/-- A set is contained in each of its neighbourhoods. -/
theorem subset_nbhd (r : ℕ) (A : Set Cell) : A ⊆ nbhd r A :=
  fun c hc => ⟨c, hc, Near.refl r c⟩

/-- The radius-zero neighbourhood is the set itself. -/
@[simp] theorem nbhd_zero (A : Set Cell) : nbhd 0 A = A := by
  ext d
  simp [mem_nbhd, near_zero]

/-- Neighbourhoods grow with the radius and with the set. -/
theorem nbhd_mono {r s : ℕ} {A B : Set Cell} (hrs : r ≤ s) (hAB : A ⊆ B) :
    nbhd r A ⊆ nbhd s B :=
  fun _ ⟨c, hc, h⟩ => ⟨c, hAB hc, h.mono hrs⟩

/-- The neighbourhood of a neighbourhood is the neighbourhood of the sum of the radii: the
Chebyshev distance on the grid is a path metric. -/
theorem nbhd_nbhd (r s : ℕ) (A : Set Cell) : nbhd r (nbhd s A) = nbhd (r + s) A := by
  ext d
  constructor
  · rintro ⟨e, ⟨c, hc, hec⟩, hde⟩
    exact ⟨c, hc, hde.trans hec⟩
  · rintro ⟨c, hc, h1, h2, h3, h4⟩
    refine ⟨(max (c.1 - s) (min (c.1 + s) d.1), max (c.2 - s) (min (c.2 + s) d.2)),
      ⟨c, hc, ?_⟩, ?_⟩ <;> exact ⟨by omega, by omega, by omega, by omega⟩

/-- `AgreeOn A S T`: the configurations `S` and `T` have the same live cells in the region
`A`. -/
def AgreeOn (A : Set Cell) (S T : Finset Cell) : Prop := ∀ c ∈ A, (c ∈ S ↔ c ∈ T)

/-- Every configuration agrees with itself everywhere. -/
theorem AgreeOn.refl (A : Set Cell) (S : Finset Cell) : AgreeOn A S S :=
  fun _ _ => Iff.rfl

/-- Agreement is symmetric. -/
theorem AgreeOn.symm {A : Set Cell} {S T : Finset Cell} (h : AgreeOn A S T) : AgreeOn A T S :=
  fun c hc => (h c hc).symm

/-- Agreement on a region gives agreement on every smaller region. -/
theorem AgreeOn.mono {A B : Set Cell} {S T : Finset Cell} (h : AgreeOn B S T) (hAB : A ⊆ B) :
    AgreeOn A S T :=
  fun c hc => h c (hAB hc)

/-- Agreement on the whole grid is equality. -/
theorem agreeOn_univ {S T : Finset Cell} : AgreeOn Set.univ S T ↔ S = T := by
  simp [AgreeOn, Finset.ext_iff]

/-! ### Locality -/

/-- The live-neighbour count of `c` depends only on the state of the neighbours of `c`. -/
theorem liveNbrs_congr {S T : Finset Cell} {c : Cell} (h : ∀ d ∈ nbrs c, (d ∈ S ↔ d ∈ T)) :
    liveNbrs S c = liveNbrs T c := by
  unfold liveNbrs
  rw [filter_congr h]

/-- **Locality, one generation**: if `S` and `T` agree on `c` and on the neighbours of `c`,
they agree on `c` after one generation. -/
theorem Rule.mem_step_congr (R : Rule) {S T : Finset Cell} {c : Cell} (hc : c ∈ S ↔ c ∈ T)
    (h : ∀ d ∈ nbrs c, (d ∈ S ↔ d ∈ T)) : c ∈ R.step S ↔ c ∈ R.step T := by
  rw [Rule.mem_step, Rule.mem_step, liveNbrs_congr h, hc]

/-- **Locality, one generation**, in the language of distances: if `S` and `T` agree within
distance one of `c`, they agree on `c` after one generation. -/
theorem Rule.mem_step_congr_of_near (R : Rule) {S T : Finset Cell} {c : Cell}
    (h : ∀ d, Near 1 d c → (d ∈ S ↔ d ∈ T)) : c ∈ R.step S ↔ c ∈ R.step T :=
  R.mem_step_congr (h c (Near.refl 1 c)) fun d hd => h d (near_one.2 (Or.inr hd))

/-- **Locality**: if `S` and `T` agree on every cell within Chebyshev distance `n` of `c`,
they agree on `c` after `n` generations. -/
theorem Rule.mem_evolve_congr (R : Rule) {n : ℕ} {S T : Finset Cell} {c : Cell}
    (h : ∀ d, Near n d c → (d ∈ S ↔ d ∈ T)) : c ∈ R.evolve n S ↔ c ∈ R.evolve n T := by
  induction n generalizing c with
  | zero => exact h c (Near.refl 0 c)
  | succ n ih =>
    rw [Rule.evolve_succ R n S, Rule.evolve_succ R n T]
    exact R.mem_step_congr_of_near fun d hd => ih fun e he => h e (he.trans hd)

/-- **Locality for regions**: if `S` and `T` agree on the radius-`n` neighbourhood of a region
`A`, then after `n` generations they agree on `A`. -/
theorem Rule.agreeOn_evolve (R : Rule) {n : ℕ} {A : Set Cell} {S T : Finset Cell}
    (h : AgreeOn (nbhd n A) S T) : AgreeOn A (R.evolve n S) (R.evolve n T) :=
  fun c hc => R.mem_evolve_congr fun d hd => h d ⟨c, hc, hd⟩

/-! ### Speed of light -/

/-- **Speed of light, one generation**: a cell alive after one generation is within distance
one of a cell alive before. -/
theorem Rule.exists_mem_near_of_mem_step {R : Rule} {S : Finset Cell} {c : Cell}
    (h : c ∈ R.step S) : ∃ d ∈ S, Near 1 c d := by
  obtain ⟨d, hd, h1, h2, h3, h4⟩ := Rule.exists_near_of_mem_step h
  exact ⟨d, hd, by omega, by omega, by omega, by omega⟩

/-- **Speed of light**: a cell alive after `n` generations is within distance `n` of a cell
alive at the start. -/
theorem Rule.exists_mem_near_of_mem_evolve {R : Rule} {n : ℕ} {S : Finset Cell} {c : Cell}
    (h : c ∈ R.evolve n S) : ∃ d ∈ S, Near n c d :=
  Rule.exists_near_of_mem_evolve h

/-- **Speed of light**: after `n` generations the configuration lies in the radius-`n`
neighbourhood of the initial one. -/
theorem Rule.coe_evolve_subset_nbhd (R : Rule) (n : ℕ) (S : Finset Cell) :
    (R.evolve n S : Set Cell) ⊆ nbhd n (S : Set Cell) :=
  fun _ hc => Rule.exists_mem_near_of_mem_evolve (mem_coe.1 hc)

/-! ### Separation -/

/-- `Sep r S T`: every cell of `S` is at Chebyshev distance greater than `r` from every cell of
`T`. -/
def Sep (r : ℕ) (S T : Finset Cell) : Prop := ∀ s ∈ S, ∀ t ∈ T, ¬ Near r s t

/-- Separation in terms of the Chebyshev distance: all distances exceed `r`. -/
theorem sep_iff_max {r : ℕ} {S T : Finset Cell} :
    Sep r S T ↔ ∀ s ∈ S, ∀ t ∈ T, (r : ℤ) < max |s.1 - t.1| |s.2 - t.2| := by
  simp only [Sep, near_iff_max, not_le]

/-- Separation is symmetric. -/
theorem Sep.symm {r : ℕ} {S T : Finset Cell} (h : Sep r S T) : Sep r T S :=
  fun t ht s hs hts => h s hs t ht hts.symm

/-- Separation by a larger distance, of larger sets, is a stronger condition. -/
theorem Sep.mono {r r' : ℕ} {S S' T T' : Finset Cell} (h : Sep r' S' T') (hr : r ≤ r')
    (hS : S ⊆ S') (hT : T ⊆ T') : Sep r S T :=
  fun s hs t ht hst => h s (hS hs) t (hT ht) (hst.mono hr)

/-- Separation by a larger distance is a stronger condition. -/
theorem Sep.mono_radius {r r' : ℕ} {S T : Finset Cell} (h : Sep r' S T) (hr : r ≤ r') :
    Sep r S T :=
  h.mono hr (Subset.refl S) (Subset.refl T)

/-- Separation at distance zero is disjointness. -/
theorem sep_zero {S T : Finset Cell} : Sep 0 S T ↔ Disjoint S T := by
  simp only [Sep, near_zero, disjoint_left]
  exact ⟨fun h s hs ht => h s hs s ht rfl, fun h s hs t ht hst => h hs (hst ▸ ht)⟩

/-- Separated configurations are disjoint. -/
theorem Sep.disjoint {r : ℕ} {S T : Finset Cell} (h : Sep r S T) : Disjoint S T :=
  sep_zero.1 (h.mono_radius (Nat.zero_le r))

/-- The empty configuration is separated from everything. -/
@[simp] theorem sep_empty_left (r : ℕ) (T : Finset Cell) : Sep r ∅ T := by
  simp [Sep]

/-- Everything is separated from the empty configuration. -/
@[simp] theorem sep_empty_right (r : ℕ) (S : Finset Cell) : Sep r S ∅ := by
  simp [Sep]

/-- Distance greater than `2 * r` means exactly that the radius-`r` neighbourhoods are disjoint.
For `r = 1` this is the "disjoint influence" hypothesis `N_1 S ∩ N_1 T = ∅`. -/
theorem sep_two_mul_iff_disjoint_nbhd {r : ℕ} {S T : Finset Cell} :
    Sep (2 * r) S T ↔ Disjoint (nbhd r (S : Set Cell)) (nbhd r (T : Set Cell)) := by
  rw [Set.disjoint_left]
  constructor
  · rintro h c ⟨s, hs, hcs⟩ ⟨t, ht, hct⟩
    exact h s hs t ht ((hcs.symm.trans hct).mono (by omega))
  · rintro h s hs t ht ⟨h1, h2, h3, h4⟩
    refine h (a := ((s.1 + t.1) / 2, (s.2 + t.2) / 2)) ⟨s, hs, ?_⟩ ⟨t, ht, ?_⟩ <;>
      exact ⟨by omega, by omega, by omega, by omega⟩

/-- **Separation decays at twice the speed of light**: configurations at distance greater than
`r + j + k` are at distance greater than `r` after `j` and `k` generations respectively. -/
theorem Sep.evolve_evolve {r j k : ℕ} {S T : Finset Cell} (R : Rule) (h : Sep (r + j + k) S T) :
    Sep r (R.evolve j S) (R.evolve k T) := by
  intro s hs t ht hst
  obtain ⟨s', hs', h1⟩ := Rule.exists_mem_near_of_mem_evolve hs
  obtain ⟨t', ht', h2⟩ := Rule.exists_mem_near_of_mem_evolve ht
  exact h s' hs' t' ht' ((h1.symm.trans (hst.trans h2)).mono (by omega))

/-- Configurations at distance greater than `r + 2 * k` are at distance greater than `r` after
`k` generations. -/
theorem Sep.evolve {r k : ℕ} {S T : Finset Cell} (R : Rule) (h : Sep (r + 2 * k) S T) :
    Sep r (R.evolve k S) (R.evolve k T) :=
  Sep.evolve_evolve R (h.mono_radius (by omega))

/-! ### Independence of separated patterns -/

/-- If no cell of `T` is within distance one of `c`, then `T` does not influence `c` in one
generation. -/
theorem Rule.mem_step_union_of_forall_not_near (R : Rule) {S T : Finset Cell} {c : Cell}
    (h : ∀ t ∈ T, ¬ Near 1 c t) : c ∈ R.step (S ∪ T) ↔ c ∈ R.step S := by
  refine R.mem_step_congr_of_near fun d hd => ?_
  have hdT : d ∉ T := fun hdT => h d hdT hd.symm
  simp [hdT]

/-- If no cell of `T` is within distance one of `c`, then `c` is dead in the successor of
`T`. -/
theorem Rule.notMem_step_of_forall_not_near (R : Rule) {T : Finset Cell} {c : Cell}
    (h : ∀ t ∈ T, ¬ Near 1 c t) : c ∉ R.step T := by
  intro hc
  obtain ⟨d, hd, hcd⟩ := Rule.exists_mem_near_of_mem_step hc
  exact h d hd hcd

/-- **Independence, one generation**: if every cell of `S` is at Chebyshev distance at least
three from every cell of `T` (`Sep 2 S T`, equivalently the radius-one neighbourhoods are
disjoint), then the two parts evolve independently for one generation. The constant is sharp:
see `not_step_union_of_sep_one`. -/
theorem Rule.step_union_of_sep (R : Rule) {S T : Finset Cell} (h : Sep 2 S T) :
    R.step (S ∪ T) = R.step S ∪ R.step T := by
  ext c
  rw [mem_union]
  by_cases hc : ∀ t ∈ T, ¬ Near 1 c t
  · rw [R.mem_step_union_of_forall_not_near hc]
    exact (or_iff_left (R.notMem_step_of_forall_not_near hc)).symm
  · have hc' : ∀ s ∈ S, ¬ Near 1 c s := by
      push Not at hc
      obtain ⟨t, ht, hct⟩ := hc
      exact fun s hs hcs => h s hs t ht (hcs.symm.trans hct)
    rw [union_comm, R.mem_step_union_of_forall_not_near hc']
    exact (or_iff_right (R.notMem_step_of_forall_not_near hc')).symm

/-- **Independence along a run**: if at every time `k < n` the evolved parts are at distance at
least three, then the union evolves as the union of the parts for `n` generations. This is the
form needed for a spaceship travelling past a distant pattern. -/
theorem Rule.evolve_union_of_forall_sep (R : Rule) {n : ℕ} {S T : Finset Cell}
    (h : ∀ k < n, Sep 2 (R.evolve k S) (R.evolve k T)) :
    R.evolve n (S ∪ T) = R.evolve n S ∪ R.evolve n T := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Rule.evolve_succ]
    rw [ih fun k hk => h k (Nat.lt_succ_of_lt hk), R.step_union_of_sep (h n (Nat.lt_succ_self n))]

/-- **Independence, `n` generations**: if every cell of `S` is at Chebyshev distance greater than
`2 * n`, that is at least `2 * n + 1`, from every cell of `T`, then the two parts evolve
independently for `n` generations. For `n = 1` this is `Rule.step_union_of_sep` and the constant
is sharp. -/
theorem Rule.evolve_union_of_sep (R : Rule) {n : ℕ} {S T : Finset Cell} (h : Sep (2 * n) S T) :
    R.evolve n (S ∪ T) = R.evolve n S ∪ R.evolve n T :=
  R.evolve_union_of_forall_sep fun _ hk => Sep.evolve R (h.mono_radius (by omega))

/-- **Independence next to a still life**: if `T` is a still life and every cell of `S` is at
Chebyshev distance greater than `n + 1` from every cell of `T`, then for `n` generations `S`
evolves as if alone and `T` stays. -/
theorem Rule.evolve_union_of_sep_of_step_eq (R : Rule) {n : ℕ} {S T : Finset Cell}
    (hT : R.step T = T) (h : Sep (n + 1) S T) : R.evolve n (S ∪ T) = R.evolve n S ∪ T := by
  have hT' : ∀ k, R.evolve k T = T := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [Rule.evolve_succ, ih, hT]
  have h' : ∀ k < n, Sep 2 (R.evolve k S) (R.evolve k T) := fun k hk => by
    have h2 : Sep 2 (R.evolve k S) (R.evolve 0 T) :=
      Sep.evolve_evolve R (h.mono_radius (by omega))
    rw [hT' k]
    exact h2
  rw [R.evolve_union_of_forall_sep h', hT' n]

/-! ### Equivariance -/

/-- Bijections of the grid preserving the neighbour relation are closed under composition. -/
theorem nbrs_trans {e f : Cell ≃ Cell} (he : ∀ c d, e d ∈ nbrs (e c) ↔ d ∈ nbrs c)
    (hf : ∀ c d, f d ∈ nbrs (f c) ↔ d ∈ nbrs c) (c d : Cell) :
    (e.trans f) d ∈ nbrs ((e.trans f) c) ↔ d ∈ nbrs c := by
  rw [Equiv.trans_apply, Equiv.trans_apply, hf, he]

/-- The inverse of a bijection of the grid preserving the neighbour relation preserves it. -/
theorem nbrs_symm {e : Cell ≃ Cell} (he : ∀ c d, e d ∈ nbrs (e c) ↔ d ∈ nbrs c) (c d : Cell) :
    e.symm d ∈ nbrs (e.symm c) ↔ d ∈ nbrs c := by
  rw [← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Equivariance**: every bijection of the grid that preserves the neighbour relation commutes
with `n` generations of every rule. -/
theorem Rule.evolve_map (R : Rule) (e : Cell ≃ Cell)
    (he : ∀ c d, e d ∈ nbrs (e c) ↔ d ∈ nbrs c) (n : ℕ) (S : Finset Cell) :
    R.evolve n (S.map e.toEmbedding) = (R.evolve n S).map e.toEmbedding := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Rule.evolve_succ]
    rw [ih, R.step_map e he]

/-- One generation commutes with translation, in terms of `translate`. -/
theorem Rule.step_translate_eq (R : Rule) (v : Cell) (S : Finset Cell) :
    R.step (translate v S) = translate v (R.step S) :=
  R.step_translate v S

/-- **Translation equivariance**: `n` generations commute with translation. -/
theorem Rule.evolve_translate (R : Rule) (v : Cell) (n : ℕ) (S : Finset Cell) :
    R.evolve n (translate v S) = translate v (R.evolve n S) :=
  R.evolve_map _ (nbrs_addLeft v) n S

/-- **Equivariance under transposition**: `n` generations commute with `(x, y) ↦ (y, x)`. -/
theorem Rule.evolve_transpose (R : Rule) (n : ℕ) (S : Finset Cell) :
    R.evolve n (S.map (Equiv.prodComm ℤ ℤ).toEmbedding) =
      (R.evolve n S).map (Equiv.prodComm ℤ ℤ).toEmbedding :=
  R.evolve_map _ nbrs_prodComm n S

/-- **Equivariance under reflection**: `n` generations commute with `(x, y) ↦ (-x, y)`. -/
theorem Rule.evolve_reflectX (R : Rule) (n : ℕ) (S : Finset Cell) :
    R.evolve n (S.map reflectX.toEmbedding) = (R.evolve n S).map reflectX.toEmbedding :=
  R.evolve_map _ nbrs_reflectX n S

/-! ### Periodicity algebra -/

/-- **Oscillators**: a configuration that returns to itself after `p` generations returns to
itself after every multiple of `p` generations. -/
theorem Rule.evolve_mul_of_evolve_eq (R : Rule) {p : ℕ} {S : Finset Cell}
    (h : R.evolve p S = S) (k : ℕ) : R.evolve (k * p) S = S := by
  induction k with
  | zero => rw [Nat.zero_mul, Rule.evolve_zero]
  | succ k ih => rw [add_one_mul, Rule.evolve_add, h, ih]

/-- An oscillator of period `p`: adding a multiple of `p` generations changes nothing. -/
theorem Rule.evolve_add_mul_of_evolve_eq (R : Rule) {p : ℕ} {S : Finset Cell}
    (h : R.evolve p S = S) (n k : ℕ) : R.evolve (n + k * p) S = R.evolve n S := by
  rw [Rule.evolve_add, R.evolve_mul_of_evolve_eq h]

/-- An oscillator of period `p`: the generation `n` only depends on `n` modulo `p`. -/
theorem Rule.evolve_mod_of_evolve_eq (R : Rule) {p : ℕ} {S : Finset Cell}
    (h : R.evolve p S = S) (n : ℕ) : R.evolve n S = R.evolve (n % p) S := by
  rw [← R.evolve_add_mul_of_evolve_eq h (n % p) (n / p), Nat.mod_add_div']

/-- **Spaceships**: a configuration that becomes its translate by `v` after `p` generations
becomes its translate by `k • v` after `k * p` generations. -/
theorem Rule.evolve_mul_of_evolve_eq_translate (R : Rule) {p : ℕ} {v : Cell} {S : Finset Cell}
    (h : R.evolve p S = translate v S) (k : ℕ) :
    R.evolve (k * p) S = translate (k • v) S := by
  induction k with
  | zero => rw [Nat.zero_mul, Rule.evolve_zero, zero_nsmul, translate_zero]
  | succ k ih =>
    rw [add_one_mul, Rule.evolve_add, h, R.evolve_translate, ih, translate_translate,
      succ_nsmul']

/-! ### Bounded orbits are eventually periodic -/

/-- **Pigeonhole**: if every generation of `S` lies in the finite region `B`, then two different
generations among the first `2 ^ B.card + 1` coincide. -/
theorem Rule.exists_evolve_eq_of_bounded (R : Rule) {S B : Finset Cell}
    (hB : ∀ n, R.evolve n S ⊆ B) :
    ∃ i j, i < j ∧ j ≤ 2 ^ B.card ∧ R.evolve i S = R.evolve j S := by
  have hc : B.powerset.card < (range (2 ^ B.card + 1)).card := by
    rw [card_powerset, card_range]
    exact Nat.lt_succ_self _
  obtain ⟨x, hx, y, hy, hxy, h⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hc
    (f := fun n => R.evolve n S) fun n _ => mem_powerset.2 (hB n)
  rw [mem_range] at hx hy
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
  · exact ⟨x, y, hlt, by omega, h⟩
  · exact ⟨y, x, hlt, by omega, h.symm⟩

/-- If generations `i ≤ j` coincide, the orbit is periodic with period `j - i` from generation
`i` on. -/
theorem Rule.evolve_add_sub_of_evolve_eq (R : Rule) {i j : ℕ} {S : Finset Cell} (hij : i ≤ j)
    (h : R.evolve i S = R.evolve j S) :
    ∀ n ≥ i, R.evolve (n + (j - i)) S = R.evolve n S := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e : m + i + (j - i) = m + j := by omega
  rw [e, Rule.evolve_add, ← h, ← Rule.evolve_add]

/-- **Bounded implies eventually periodic**: if every generation of `S` lies in the finite region
`B`, then from some generation `i` on the orbit is periodic with a period `p > 0`, and
`i + p ≤ 2 ^ B.card`. -/
theorem Rule.eventually_periodic_of_bounded (R : Rule) {S B : Finset Cell}
    (hB : ∀ n, R.evolve n S ⊆ B) :
    ∃ i p, 0 < p ∧ i + p ≤ 2 ^ B.card ∧ ∀ n ≥ i, R.evolve (n + p) S = R.evolve n S := by
  obtain ⟨i, j, hij, hj, h⟩ := R.exists_evolve_eq_of_bounded hB
  exact ⟨i, j - i, by omega, by omega, R.evolve_add_sub_of_evolve_eq hij.le h⟩

/-! ### Sanity and adversarial checks -/

/-- **Counterexample**: independence fails for patterns that are disjoint but touch. -/
theorem not_step_union_of_disjoint :
    ¬ ∀ S T : Finset Cell, Disjoint S T → conway.step (S ∪ T) = conway.step S ∪ conway.step T := by
  intro h
  obtain ⟨S, T, hd, hne⟩ := not_additive_conway_step
  exact hne (h S T hd)

/-- **Sharpness of the separation constant**: independence fails at Chebyshev distance exactly
two. Two cells and a third cell two columns away each die when alone, but together they give
birth to the cell `(1, 0)` between them. -/
theorem not_step_union_of_sep_one :
    ∃ S T : Finset Cell, Sep 1 S T ∧ conway.step (S ∪ T) ≠ conway.step S ∪ conway.step T := by
  refine ⟨{(0, 0), (0, 1)}, {(2, 0)}, ?_, ?_⟩
  · intro s hs t ht ⟨h1, h2, h3, h4⟩
    simp only [mem_insert, mem_singleton] at hs ht
    subst ht
    rcases hs with rfl | rfl <;> simp at h1
  · have hS : conway.step ({(0, 0), (0, 1)} : Finset Cell) = ∅ :=
      conway_step_eq_empty_of_card_lt_three (by simp)
    rw [hS, conway_step_singleton]
    intro h
    have h1 : ((1, 0) : Cell) ∈ conway.step ({(0, 0), (0, 1)} ∪ {(2, 0)}) := by
      simp [Rule.mem_step, liveNbrs_eq, conway]
    rw [h] at h1
    simp at h1

/-- **Periodicity algebra on an instance**: the blinker returns to itself after every even
number of generations. -/
theorem conway_evolve_two_mul_blinkerH (k : ℕ) : conway.evolve (k * 2) blinkerH = blinkerH :=
  conway.evolve_mul_of_evolve_eq conway_evolve_two_blinkerH k

/-- The blinker is in its vertical phase after every odd number of generations. -/
theorem conway_evolve_two_mul_add_one_blinkerH (k : ℕ) :
    conway.evolve (1 + k * 2) blinkerH = blinkerV := by
  rw [conway.evolve_add_mul_of_evolve_eq conway_evolve_two_blinkerH, Rule.evolve_one,
    conway_step_blinkerH]

/-- The block stays a block forever. -/
theorem conway_evolve_block (n : ℕ) : conway.evolve n block = block := by
  simpa using conway.evolve_mul_of_evolve_eq (p := 1) conway_step_block n

/-- **Independence on an instance**: a block and a copy of it four columns to the right are at
distance three, so together they form a still life for ever. -/
theorem conway_evolve_two_blocks (n : ℕ) :
    conway.evolve n (block ∪ translate (4, 0) block) = block ∪ translate (4, 0) block := by
  have hsep : Sep 2 block (translate (4, 0) block) := by
    intro s hs t ht ⟨h1, h2, h3, h4⟩
    rw [mem_translate] at ht
    simp only [block, mem_insert, mem_singleton, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      at hs ht
    omega
  rw [conway.evolve_union_of_forall_sep, conway.evolve_translate, conway_evolve_block]
  intro k _
  rwa [conway.evolve_translate, conway_evolve_block]

end LeanTheory.Life
