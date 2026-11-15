/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ContinueDecrement

/-!
# Networks of reactions: many independent processes side by side

A large circuit (research note `N-15`, the zero test `DZ2` of report `R-28`) cannot be certified
as one window. It is cut into time segments; in each segment the circuit is a list of independent
processes (an idle periodic piece, a glider in flight, a local reaction of a piece with a glider),
whose footprints stay pairwise far apart. This module provides the composition step:

* `Proc n`: a reaction of `n` generations packaged with its start, end and footprint;
* `Reaction.parList`: a list of processes with pairwise far apart footprints is a reaction of the
  union of their starts into the union of their ends, with the union of the footprints;
* `reaction_periodic_box`: an idle periodic piece, started at any phase, as a process.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- Nothing is far from the empty set. -/
theorem FarApart.empty_right (r : ℕ) (A : Set Cell) : FarApart r A ∅ :=
  fun _ _ _ h => h.elim

/-- A reaction of `n` generations, packaged with its start, its end and its footprint. -/
structure Proc (n : ℕ) where
  /-- The configuration at the start. -/
  P : Finset Cell
  /-- The configuration after `n` generations. -/
  Q : Finset Cell
  /-- The footprint at every generation. -/
  F : ℕ → Set Cell
  /-- The reaction. -/
  reaction : Reaction P Q n F

namespace Proc

variable {n : ℕ}

/-- The union of the starts of a list of processes. -/
def start (l : List (Proc n)) : Finset Cell := l.foldr (fun p s => p.P ∪ s) ∅

/-- The union of the ends of a list of processes. -/
def stop (l : List (Proc n)) : Finset Cell := l.foldr (fun p s => p.Q ∪ s) ∅

/-- The union of the footprints of a list of processes at generation `i`. -/
def foot (l : List (Proc n)) (i : ℕ) : Set Cell := l.foldr (fun p s => p.F i ∪ s) ∅

@[simp] theorem start_nil : start ([] : List (Proc n)) = ∅ := rfl
@[simp] theorem start_cons (p : Proc n) (l : List (Proc n)) :
    start (p :: l) = p.P ∪ start l := rfl
@[simp] theorem stop_nil : stop ([] : List (Proc n)) = ∅ := rfl
@[simp] theorem stop_cons (p : Proc n) (l : List (Proc n)) :
    stop (p :: l) = p.Q ∪ stop l := rfl
@[simp] theorem foot_nil (i : ℕ) : foot ([] : List (Proc n)) i = ∅ := rfl
@[simp] theorem foot_cons (p : Proc n) (l : List (Proc n)) (i : ℕ) :
    foot (p :: l) i = p.F i ∪ foot l i := rfl

/-- A set far from every footprint of a list is far from their union. -/
theorem farApart_foot {A : Set Cell} {i : ℕ} (l : List (Proc n))
    (h : ∀ p ∈ l, FarApart 2 A (p.F i)) : FarApart 2 A (foot l i) := by
  induction l with
  | nil => exact FarApart.empty_right 2 A
  | cons p l ih =>
    exact FarApart.union_right (h p List.mem_cons_self)
      (ih fun q hq => h q (List.mem_cons_of_mem p hq))

/-- Two processes run independently: their footprints stay far apart. -/
def Indep (p q : Proc n) : Prop := ∀ i < n, FarApart 2 (p.F i) (q.F i)

end Proc

/-- **Many processes side by side**: a list of processes whose footprints stay pairwise far apart
is a reaction of the union of their starts into the union of their ends. -/
theorem Reaction.parList {n : ℕ} (l : List (Proc n)) (h : l.Pairwise Proc.Indep) :
    Reaction (Proc.start l) (Proc.stop l) n (Proc.foot l) := by
  induction l with
  | nil => exact ⟨Rule.evolve_empty _ _, fun _ _ c hc => by simp at hc⟩
  | cons p l ih =>
    rw [List.pairwise_cons] at h
    exact p.reaction.par (ih h.2) fun i hi => Proc.farApart_foot l fun q hq => h.1 q hq i hi

/-- **An idle periodic piece, started at any phase**: a configuration of period `p` that stays in
a box during one period is, from any phase `s` and for any number of generations, a reaction with
that box as footprint. -/
theorem reaction_periodic_box {S : Finset Cell} {p : ℕ} {a b lo hi : ℤ} (hp : 0 < p)
    (h : conway.evolve p S = S) (hB : ∀ r < p, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi)
    (s n : ℕ) :
    Reaction (conway.evolve s S) (conway.evolve (n + s) S) n (fun _ => Box a b lo hi) :=
  ⟨by rw [Rule.evolve_add], fun i _ => by
    rw [← Rule.evolve_add, conway.evolve_mod_of_evolve_eq h]
    exact hB _ (Nat.mod_lt _ hp)⟩

/-- **A salvo acts at every position of the block, with a sharp footprint.** As
`salvo_quad_reaction`, but the footprint follows the salvo: until generation `k * 4` it is the
salvo's box moved along the diagonal together with the block's box, afterwards the box of the
reaction at position `0` moved to position `k`. -/
theorem salvo_track_reaction {S : Finset Cell} {a b lo hi za zb zlo zhi d : ℤ} {n : ℕ}
    (h4 : conway.evolve 4 S = translate (1, 1) S)
    (hB : ∀ r < 4, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi)
    (hz : Reaction (S ∪ counter 0) (counter d) n (fun _ => Box za zb zlo zhi))
    (hhi : hi ≤ 9) (k : ℕ) :
    Reaction (S ∪ counter k) (counter (d + k)) (k * 4 + n)
      (fun i => if i ≤ k * 4 then
        Box (a + ((i / 4 : ℕ) : ℤ)) (b + ((i / 4 : ℕ) : ℤ)) (lo + ((i / 4 : ℕ) : ℤ))
          (hi + ((i / 4 : ℕ) : ℤ)) ∪ Box (7 + k) (8 + k) (11 + k) (12 + k)
      else Box (za + k) (zb + k) (zlo + k) (zhi + k)) := by
  have hfly := (reaction_flight_box' (by norm_num) h4 hB (k * 4)).par
    ((counter_isStillLife k).reaction_box (counter_subset_box k) (k * 4))
    (fun i hi => by
      rw [image_add_box]
      refine Box.farApart ?_
      simp only [Prod.smul_snd, nsmul_eq_mul]
      have : i / 4 < k := by omega
      push_cast
      omega)
  rw [conway.evolve_mul_of_evolve_eq_translate h4, nsmul_one_one] at hfly
  have hz' := hz.translate ((k : ℤ), (k : ℤ))
  rw [translate_union, translate_counter, translate_counter, zero_add] at hz'
  refine (hfly.seq hz').mono fun i _ => ?_
  split_ifs
  · refine Set.union_subset_union ?_ le_rfl
    rw [image_add_box]
    rintro c ⟨h1, h2, h3, h4⟩
    simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul] at h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast at * <;> omega
  · rw [image_add_box]

/-! ### Checkable lists of conditions -/

/-- `R a b` for every `b` in the list. A recursive conjunction, proved by an anonymous
constructor on a concrete list. -/
def AllR {α : Type*} (R : α → α → Prop) (a : α) : List α → Prop
  | [] => True
  | b :: l => R a b ∧ AllR R a l

/-- `R a b` for every pair of the list, `a` before `b`. A recursive conjunction. -/
def PairR {α : Type*} (R : α → α → Prop) : List α → Prop
  | [] => True
  | a :: l => AllR R a l ∧ PairR R l

/-- The recursive conjunction gives membership. -/
theorem AllR.forall {α : Type*} {R : α → α → Prop} {a : α} :
    ∀ {l : List α}, AllR R a l → ∀ b ∈ l, R a b
  | [], _, _, hb => by simp at hb
  | _ :: _, ⟨h, hl⟩, _, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h
    · exact AllR.forall hl _ hb

/-- The recursive conjunction gives `List.Pairwise`. -/
theorem PairR.pairwise {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, PairR R l → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | _ :: _, ⟨h, hl⟩ => List.Pairwise.cons (AllR.forall h) (PairR.pairwise hl)

/-! ### Periodic pieces and bundles of idle pieces -/

/-- A piece of a circuit: a configuration of period `30` that stays in a box. -/
structure Piece where
  /-- The piece at rest, at the reference time. -/
  rest : Finset Cell
  /-- Left edge of the box. -/
  a : ℤ
  /-- Right edge of the box. -/
  b : ℤ
  /-- Top edge of the box. -/
  lo : ℤ
  /-- Bottom edge of the box. -/
  hi : ℤ
  /-- Period `30`, inside the box. -/
  rest_reaction : Reaction rest rest 30 (fun _ => Box a b lo hi)

/-- The box of a piece. -/
def Piece.box (g : Piece) : Set Cell := Box g.a g.b g.lo g.hi

/-- The piece idle for `n` generations from phase `s`, ending at phase `s' = (n + s) % 30`. -/
def Piece.idle (g : Piece) (s n s' : ℕ) (h : (n + s) % 30 = s') : Proc n where
  P := conway.evolve s g.rest
  Q := conway.evolve s' g.rest
  F := fun _ => g.box
  reaction := by
    have := reaction_periodic_box (by norm_num) g.rest_reaction.evolve_eq
      (fun r hr => g.rest_reaction.subset r hr.le) s n
    rwa [conway.evolve_mod_of_evolve_eq g.rest_reaction.evolve_eq (n + s), h] at this

/-- Two pieces are separated: their boxes are far apart. -/
def Piece.Sep (g h : Piece) : Prop := FarApart 2 g.box h.box

/-- **A bundle of idle pieces** with pairwise separated boxes, as one process. -/
def Piece.bundle (L : List Piece) (hL : L.Pairwise Piece.Sep) (s n s' : ℕ)
    (h : (n + s) % 30 = s') : Proc n where
  P := Proc.start (L.map fun g => g.idle s n s' h)
  Q := Proc.stop (L.map fun g => g.idle s n s' h)
  F := Proc.foot (L.map fun g => g.idle s n s' h)
  reaction := Reaction.parList _ (List.pairwise_map.2 (hL.imp fun hgh _ _ => hgh))

/-- A footprint far from the box of every piece of a list, at every generation before `n`. -/
def FarFromAll (A : ℕ → Set Cell) (n : ℕ) : List Piece → Prop
  | [] => True
  | g :: L => (∀ i < n, FarApart 2 (A i) g.box) ∧ FarFromAll A n L

/-- A process far from every box of a list of pieces is independent of their bundle. -/
theorem Piece.indep_bundle {n : ℕ} (p : Proc n) (L : List Piece) (hL : L.Pairwise Piece.Sep)
    (s s' : ℕ) (h : (n + s) % 30 = s') (hp : FarFromAll p.F n L) :
    Proc.Indep p (Piece.bundle L hL s n s' h) := by
  intro i hi
  change FarApart 2 (p.F i) (Proc.foot (L.map fun g => g.idle s n s' h) i)
  induction L with
  | nil => exact FarApart.empty_right 2 _
  | cons g L ih =>
    exact FarApart.union_right (hp.1 i hi) (ih (List.pairwise_cons.1 hL).2 hp.2)

/-! ### Flight with a box footprint -/

/-- **Flight with a box footprint**: a pattern that moves by `(dx, dy)` every four generations
and stays in a box during its first four generations flies for `n = 4 * q + r` generations, at
every generation `i` inside the box moved by `(i / 4) • (dx, dy)`, and ends at `G'`. -/
theorem flight_reaction {G G' : Finset Cell} {dx dy a b lo hi : ℤ}
    (h4 : conway.evolve 4 G = translate (dx, dy) G)
    (hB : ∀ r < 4, (conway.evolve r G : Set Cell) ⊆ Box a b lo hi) (q r : ℕ)
    (hend : translate ((q : ℤ) * dx, (q : ℤ) * dy) (conway.evolve r G) = G') :
    Reaction G G' (4 * q + r) (fun i => Box (a + ((i / 4 : ℕ) : ℤ) * dx)
      (b + ((i / 4 : ℕ) : ℤ) * dx) (lo + ((i / 4 : ℕ) : ℤ) * dy)
      (hi + ((i / 4 : ℕ) : ℤ) * dy)) := by
  have h := reaction_flight_box' (by norm_num) h4 hB (4 * q + r)
  refine ⟨?_, fun i hi c hc => ?_⟩
  · rw [← hend, add_comm, Rule.evolve_add, mul_comm, conway.evolve_mul_of_evolve_eq_translate h4,
      Rule.evolve_translate]
    congr 1
  · obtain ⟨d, ⟨h1, h2, h3, h4⟩, rfl⟩ := h.subset i hi hc
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, nsmul_eq_mul] <;> omega

/-- Two consecutive segments: a reaction, an equality of configurations, a reaction. -/
theorem Reaction.seq_eq {P Q Q' R : Finset Cell} {n m : ℕ} {F G : ℕ → Set Cell}
    (h : Reaction P Q n F) (e : Q = Q') (h' : Reaction Q' R m G) :
    Reaction P R (n + m) (fun i => if i ≤ n then F i else G (i - n)) :=
  h.seq (e ▸ h')

/-! ### Trajectories: one evolution, cut into time windows -/

/-- **A window of a trajectory**: if every generation of `X` lies in its footprint `G i`, then from
generation `m` on, for `n` generations, `X` is a reaction with the shifted footprint. -/
theorem trajectory_reaction {X : Finset Cell} {G : ℕ → Set Cell}
    (hG : ∀ i, (conway.evolve i X : Set Cell) ⊆ G i) (m n : ℕ) :
    Reaction (conway.evolve m X) (conway.evolve (n + m) X) n (fun i => G (i + m)) :=
  ⟨by rw [Rule.evolve_add], fun i _ => by rw [← Rule.evolve_add]; exact hG (i + m)⟩

/-- **A salvo and the block, for all time**: under the hypotheses of `salvo_track_reaction`, every
generation of the salvo and the block at position `k` lies in the sharp footprint: until
generation `k * 4` the salvo's box moved along the diagonal and the block's box, afterwards the box
of the reaction at position `0` moved to position `k` (the block at its new position stays
there). -/
theorem salvo_track_all {S : Finset Cell} {a b lo hi za zb zlo zhi d : ℤ} {n : ℕ}
    (h4 : conway.evolve 4 S = translate (1, 1) S)
    (hB : ∀ r < 4, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi)
    (hz : Reaction (S ∪ counter 0) (counter d) n (fun _ => Box za zb zlo zhi))
    (hhi : hi ≤ 9) (k : ℕ) (i : ℕ) :
    (conway.evolve i (S ∪ counter k) : Set Cell) ⊆
      if i ≤ k * 4 then
        Box (a + ((i / 4 : ℕ) : ℤ)) (b + ((i / 4 : ℕ) : ℤ)) (lo + ((i / 4 : ℕ) : ℤ))
          (hi + ((i / 4 : ℕ) : ℤ)) ∪ Box (7 + k) (8 + k) (11 + k) (12 + k)
      else if i ≤ k * 4 + n then Box (za + k) (zb + k) (zlo + k) (zhi + k)
      else Box (7 + (d + k)) (8 + (d + k)) (11 + (d + k)) (12 + (d + k)) := by
  have h := salvo_track_reaction h4 hB hz hhi k
  by_cases hi' : i ≤ k * 4 + n
  · have := h.subset i hi'
    by_cases h1 : i ≤ k * 4
    · simpa only [h1, ↓reduceIte] using this
    · simpa only [h1, hi', ↓reduceIte] using this
  · -- after the reaction the block stays where it is
    have e : conway.evolve i (S ∪ counter k) = counter (d + k) := by
      rw [show i = (i - (k * 4 + n)) + (k * 4 + n) by omega, Rule.evolve_add, h.evolve_eq,
        (counter_isStillLife _).evolve]
    simp only [show ¬ (i ≤ k * 4) by omega, hi', ↓reduceIte]
    rw [e]
    exact counter_subset_box _

/-- `salvo_track_all` placed at `(vx, vy)`. -/
theorem salvo_world_all {S : Finset Cell} {a b lo hi za zb zlo zhi d : ℤ} {n : ℕ}
    (h4 : conway.evolve 4 S = translate (1, 1) S)
    (hB : ∀ r < 4, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi)
    (hz : Reaction (S ∪ counter 0) (counter d) n (fun _ => Box za zb zlo zhi))
    (hhi : hi ≤ 9) (vx vy : ℤ) (k : ℕ) (i : ℕ) :
    (conway.evolve i (translate (vx, vy) (S ∪ counter k)) : Set Cell) ⊆
      if i ≤ k * 4 then
        Box (a + vx + ((i / 4 : ℕ) : ℤ)) (b + vx + ((i / 4 : ℕ) : ℤ))
          (lo + vy + ((i / 4 : ℕ) : ℤ)) (hi + vy + ((i / 4 : ℕ) : ℤ)) ∪
          Box (7 + vx + k) (8 + vx + k) (11 + vy + k) (12 + vy + k)
      else if i ≤ k * 4 + n then Box (za + vx + k) (zb + vx + k) (zlo + vy + k) (zhi + vy + k)
      else Box (7 + d + vx + k) (8 + d + vx + k) (11 + d + vy + k) (12 + d + vy + k) := by
  intro c hc
  rw [Rule.evolve_translate, mem_coe, mem_translate] at hc
  have := salvo_track_all h4 hB hz hhi k i (mem_coe.2 hc)
  split_ifs at this ⊢ with hik
  · rcases this with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · left
      simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
      exact ⟨by omega, by omega, by omega, by omega⟩
    · right
      simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
      exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨h1, h2, h3, h4⟩ := this
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
    exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨h1, h2, h3, h4⟩ := this
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- Far apart from a footprint given by cases. -/
theorem farApart_ite_left {c : Prop} [Decidable c] {A B C D : Set Cell}
    (h1 : c → FarApart 2 A D) (h2 : c → FarApart 2 B D) (h3 : ¬ c → FarApart 2 C D) :
    FarApart 2 (if c then A ∪ B else C) D := by
  split_ifs with hc
  · exact FarApart.union_left (h1 hc) (h2 hc)
  · exact h3 hc

/-- A window of a trajectory, with the end time given as a number. -/
theorem trajectory_reaction' {X : Finset Cell} {G : ℕ → Set Cell}
    (hG : ∀ i, (conway.evolve i X : Set Cell) ⊆ G i) (m n m' : ℕ) (h : n + m = m') :
    Reaction (conway.evolve m X) (conway.evolve m' X) n (fun i => G (i + m)) :=
  h ▸ trajectory_reaction hG m n

/-- The block at position `k + c`, placed at `(vx, vy)`, is the block at position `k` placed at
`(vx + c, vy + c)`. -/
theorem translate_counter_shift (vx vy : ℤ) (c k : ℕ) :
    translate (vx, vy) (counter ((k + c : ℕ) : ℤ)) = translate (vx + c, vy + c) (counter k) := by
  rw [counter, counter, translate_ofRows, translate_ofRows]
  congr 1 <;> push_cast <;> omega

/-- Far apart from a footprint given by three cases. -/
theorem farApart_ite3_left {c c' : Prop} [Decidable c] [Decidable c'] {A B C E D : Set Cell}
    (h1 : c → FarApart 2 A D) (h2 : c → FarApart 2 B D) (h3 : ¬ c → c' → FarApart 2 C D)
    (h4 : ¬ c → ¬ c' → FarApart 2 E D) :
    FarApart 2 (if c then A ∪ B else if c' then C else E) D := by
  split_ifs with hc hc'
  · exact FarApart.union_left (h1 hc) (h2 hc)
  · exact h3 hc hc'
  · exact h4 hc hc'

/-- **The end of a pull**: once the salvo has done its work, the block stays at its new position. -/
theorem salvo_world_end {S : Finset Cell} {a b lo hi za zb zlo zhi d : ℤ} {n : ℕ}
    (h4 : conway.evolve 4 S = translate (1, 1) S)
    (hB : ∀ r < 4, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi)
    (hz : Reaction (S ∪ counter 0) (counter d) n (fun _ => Box za zb zlo zhi))
    (hhi : hi ≤ 9) (vx vy : ℤ) (k M : ℕ) (hM : n ≤ M) :
    conway.evolve (k * 4 + M) (translate (vx, vy) (S ∪ counter k)) =
      translate (vx, vy) (counter (d + k)) := by
  have h := salvo_track_reaction h4 hB hz hhi k
  rw [Rule.evolve_translate, show k * 4 + M = (M - n) + (k * 4 + n) by omega, Rule.evolve_add,
    h.evolve_eq, (counter_isStillLife _).evolve]

end LeanTheory.Life
