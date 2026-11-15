/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Network
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The diagonal of a register: salvos in flight

Research note `N-20`. A *salvo* moves one cell down and to the right every four generations and,
placed in front of the block `counter 0`, moves it to `counter d`. Salvos travelling one behind the
other on the diagonal of a register fly independently while they are far apart.

* `Salvo`: a salvo with its boxes and its certificate at position `0`;
* `farApart_of_fst`: sets separated by a vertical line three cells wide are far apart;
* `flights_reaction`: a list of salvos placed one behind the other, each at least `g` cells behind
  the previous one, flies for any number of generations;
* `diag_strip`: **a block with a valid queue of salvos behind it stays, at every generation, in
  the strip of its diagonal** (induction over the queue: the front salvo and the block as one
  process, the others in flight; when the front salvo is done the next one leads).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- Sets separated by a vertical strip of width three are far apart. -/
theorem farApart_of_fst {A B : Set Cell} {X : ℤ} (hA : ∀ c ∈ A, c.1 ≤ X)
    (hB : ∀ c ∈ B, X + 3 ≤ c.1) : FarApart 2 A B := by
  rintro a ha b hb ⟨h1, -, -, -⟩
  have := hA a ha
  have := hB b hb
  push_cast at h1
  omega

/-- A salvo of the register machine, in the frame of `counter`. -/
structure Salvo where
  /-- The salvo, in front of the block at position `0`. -/
  S : Finset Cell
  /-- The move of the block. -/
  d : ℤ
  /-- The duration of the reaction with the block at position `0`. -/
  n : ℕ
  /-- Left edge of the box of the salvo during four generations. -/
  a : ℤ
  /-- Right edge. -/
  b : ℤ
  /-- Top edge. -/
  lo : ℤ
  /-- Bottom edge. -/
  hi : ℤ
  /-- Left edge of the box of the reaction. -/
  za : ℤ
  /-- Right edge. -/
  zb : ℤ
  /-- Top edge. -/
  zlo : ℤ
  /-- Bottom edge. -/
  zhi : ℤ
  /-- The salvo moves by `(1, 1)` every four generations. -/
  four : conway.evolve 4 S = translate (1, 1) S
  /-- Its box during four generations. -/
  box : ∀ r < 4, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi
  /-- The reaction with the block at position `0`. -/
  hz : Reaction (S ∪ counter 0) (counter d) n (fun _ => Box za zb zlo zhi)
  /-- The salvo is above the block. -/
  hhi : hi ≤ 9

/-- A salvo `e` cells behind its position in front of the block `counter 0`. -/
def Salvo.at (σ : Salvo) (e : ℤ) : Finset Cell := translate (-e, -e) σ.S

/-- A salvo flies: after `4 q` generations it is `q` cells further. -/
theorem Salvo.evolve_at (σ : Salvo) (e : ℤ) (q : ℕ) :
    conway.evolve (q * 4) (σ.at e) = σ.at (e - q) := by
  rw [Salvo.at, Rule.evolve_translate, conway.evolve_mul_of_evolve_eq_translate σ.four,
    translate_translate, Salvo.at]
  congr 1
  ext <;> simp <;> ring

/-- Every generation of a salvo in flight lies in its box moved along the diagonal. -/
theorem Salvo.subset_at (σ : Salvo) (e : ℤ) (i : ℕ) :
    (conway.evolve i (σ.at e) : Set Cell) ⊆
      Box (σ.a - e + ((i / 4 : ℕ) : ℤ)) (σ.b - e + ((i / 4 : ℕ) : ℤ))
        (σ.lo - e + ((i / 4 : ℕ) : ℤ)) (σ.hi - e + ((i / 4 : ℕ) : ℤ)) := by
  intro c hc
  rw [Salvo.at, Rule.evolve_translate, mem_coe, mem_translate,
    show i = i % 4 + (i / 4) * 4 by omega, Rule.evolve_add,
    conway.evolve_mul_of_evolve_eq_translate σ.four, Rule.evolve_translate, mem_translate] at hc
  obtain ⟨h1, h2, h3, h4⟩ := σ.box (i % 4) (Nat.mod_lt _ (by norm_num)) (mem_coe.2 hc)
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul] at h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Being far apart is symmetric. -/
theorem FarApart.symm' {r : ℕ} {A B : Set Cell} (h : FarApart r A B) : FarApart r B A :=
  fun b hb a ha hn => h a ha b hb (near_comm.1 hn)

/-- Salvos in flight, one behind the other (the head of the list in front). -/
def flights : List (Salvo × ℤ) → Finset Cell
  | [] => ∅
  | (σ, e) :: q => σ.at e ∪ flights q

/-- The footprint of salvos in flight at generation `i`: their boxes moved along the diagonal. -/
def flightsFoot : List (Salvo × ℤ) → ℕ → Set Cell
  | [], _ => ∅
  | (σ, e) :: q, i => Box (σ.a - e + ((i / 4 : ℕ) : ℤ)) (σ.b - e + ((i / 4 : ℕ) : ℤ))
      (σ.lo - e + ((i / 4 : ℕ) : ℤ)) (σ.hi - e + ((i / 4 : ℕ) : ℤ)) ∪ flightsFoot q i

/-- Salvos whose boxes lie in `A ≤ x ≤ B` (relative to the salvo), the first at least `e₀` cells
behind the block's front, each at least `g` cells behind the previous one. -/
def Behind (A B g : ℤ) : ℤ → List (Salvo × ℤ) → Prop
  | _, [] => True
  | e₀, (σ, e) :: q => A ≤ σ.a ∧ σ.b ≤ B ∧ e₀ ≤ e ∧ Behind A B g (e + g) q

/-- The footprint of salvos in flight lies left of the front of the first one. -/
theorem flightsFoot_le {A B g : ℤ} (hg : 0 ≤ g) :
    ∀ (q : List (Salvo × ℤ)) (e₀ : ℤ), Behind A B g e₀ q →
      ∀ i, ∀ c ∈ flightsFoot q i, c.1 ≤ B - e₀ + ((i / 4 : ℕ) : ℤ)
  | [], _, _, _, _, hc => hc.elim
  | (σ, e) :: q, e₀, ⟨_, hb, he, hq⟩, i, c, hc => by
    rcases hc with ⟨-, h2, -, -⟩ | hc
    · linarith
    · have := flightsFoot_le hg q (e + g) hq i c hc
      linarith

/-- **Salvos in flight fly independently**, for any number of generations, if each is far enough
behind the previous one. -/
theorem flights_reaction {A B g : ℤ} (hg : B - A + 3 ≤ g) (hg0 : 0 ≤ g) :
    ∀ (q : List (Salvo × ℤ)) (e₀ : ℤ), Behind A B g e₀ q →
      ∀ n, Reaction (flights q) (conway.evolve n (flights q)) n (flightsFoot q)
  | [], _, _, n => ⟨rfl, fun i _ c hc => by simp [flights] at hc⟩
  | (σ, e) :: q, e₀, ⟨ha, hb, he, hq⟩, n => by
    have h1 : Reaction (σ.at e) (conway.evolve n (σ.at e)) n (fun i =>
        Box (σ.a - e + ((i / 4 : ℕ) : ℤ)) (σ.b - e + ((i / 4 : ℕ) : ℤ))
          (σ.lo - e + ((i / 4 : ℕ) : ℤ)) (σ.hi - e + ((i / 4 : ℕ) : ℤ))) :=
      ⟨rfl, fun i _ => σ.subset_at e i⟩
    have h := h1.par (flights_reaction hg hg0 q (e + g) hq n) fun i _ =>
      (farApart_of_fst (X := B - (e + g) + ((i / 4 : ℕ) : ℤ))
        (flightsFoot_le hg0 q (e + g) hq i)
        (fun c hc => by obtain ⟨h1, _, _, _⟩ := hc; linarith)).symm'
    exact ⟨rfl, h.subset⟩

/-- Moving every salvo of a list `m` cells forward. -/
def shiftQ (q : List (Salvo × ℤ)) (m : ℤ) : List (Salvo × ℤ) := q.map fun p => (p.1, p.2 - m)

/-- Salvos in flight after `4 m` generations: each `m` cells further. -/
theorem flights_evolve_mul {A B g : ℤ} (hg : B - A + 3 ≤ g) (hg0 : 0 ≤ g) :
    ∀ (q : List (Salvo × ℤ)) (e₀ : ℤ), Behind A B g e₀ q →
      ∀ m : ℕ, conway.evolve (m * 4) (flights q) = flights (shiftQ q m)
  | [], _, _, m => by simp [flights, shiftQ]
  | (σ, e) :: q, e₀, ⟨ha, hb, he, hq⟩, m => by
    have hsep : ∀ k < m * 4, FarApart 2
        (Box (σ.a - e + ((k / 4 : ℕ) : ℤ)) (σ.b - e + ((k / 4 : ℕ) : ℤ))
          (σ.lo - e + ((k / 4 : ℕ) : ℤ)) (σ.hi - e + ((k / 4 : ℕ) : ℤ))) (flightsFoot q k) :=
      fun k _ => (farApart_of_fst (X := B - (e + g) + ((k / 4 : ℕ) : ℤ))
        (flightsFoot_le hg0 q (e + g) hq k)
        (fun c hc => by obtain ⟨h1, _, _, _⟩ := hc; linarith)).symm'
    have h := (show Reaction (σ.at e) (conway.evolve (m * 4) (σ.at e)) (m * 4) (fun i =>
        Box (σ.a - e + ((i / 4 : ℕ) : ℤ)) (σ.b - e + ((i / 4 : ℕ) : ℤ))
          (σ.lo - e + ((i / 4 : ℕ) : ℤ)) (σ.hi - e + ((i / 4 : ℕ) : ℤ))) from
      ⟨rfl, fun i _ => σ.subset_at e i⟩).par (flights_reaction hg hg0 q (e + g) hq (m * 4)) hsep
    rw [flights, h.evolve_eq, σ.evolve_at, flights_evolve_mul hg hg0 q (e + g) hq m]
    rfl

/-- The strip of a register diagonal: lanes `U₁ ≤ x - y ≤ U₂`, and `x + y ≥ V₀`. -/
def diagStrip (U₁ U₂ V₀ : ℤ) : Set Cell := {c | U₁ ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U₂ ∧ V₀ ≤ c.1 + c.2}

/-- The parameters of a register diagonal: boxes of the salvos, the gap between salvos, the
strip. -/
structure DiagParams where
  /-- Left edge of every salvo box (relative). -/
  A : ℤ
  /-- Right edge of every salvo box (relative). -/
  B : ℤ
  /-- Left edge of every reaction box. -/
  ZA : ℤ
  /-- The longest reaction. -/
  N : ℕ
  /-- The minimum gap between salvos. -/
  g : ℤ
  /-- Lower lane of the strip. -/
  U₁ : ℤ
  /-- Upper lane of the strip. -/
  U₂ : ℤ
  /-- Lower bound of `x + y` in the strip. -/
  V₀ : ℤ

/-- The gap is large enough for the salvos and reactions of the parameters. -/
def DiagParams.Good (P : DiagParams) : Prop :=
  P.B - P.A + 3 ≤ P.g ∧ P.B - 4 ≤ P.g ∧ P.B + P.N / 4 + 3 - P.ZA ≤ P.g ∧ (P.N : ℤ) / 4 + 1 ≤ P.g ∧
    P.U₁ ≤ -5 ∧ -3 ≤ P.U₂

/-- Every salvo of a list, at its offset, lies in the strip. -/
def InStrip (P : DiagParams) : List (Salvo × ℤ) → Prop
  | [] => True
  | (τ, f) :: q => P.U₁ ≤ τ.a - τ.hi ∧ τ.b - τ.lo ≤ P.U₂ ∧ P.V₀ ≤ τ.a + τ.lo - 2 * f ∧ InStrip P q

/-- A valid queue: the front salvo is in front of the block (at offset `≥ -K`), fits the
parameters, every box lies in the strip, the rest is far enough behind, and the queue that remains
after the front salvo has moved the block is valid. -/
def DiagValid (P : DiagParams) : ℤ → List (Salvo × ℤ) → Prop
  | K, [] => P.V₀ ≤ 18 + 2 * K
  | K, (σ, e) :: q => 0 ≤ K + e ∧ σ.n % 4 = 0 ∧ P.A ≤ σ.a ∧ σ.b ≤ P.B ∧ P.ZA ≤ σ.za ∧
      σ.n ≤ P.N ∧ (σ.d = 1 ∨ σ.d = -1) ∧
      P.U₁ ≤ σ.a - σ.hi ∧ σ.b - σ.lo ≤ P.U₂ ∧ P.U₁ ≤ σ.za - σ.zhi ∧ σ.zb - σ.zlo ≤ P.U₂ ∧
      P.V₀ ≤ σ.a + σ.lo - 2 * e ∧ P.V₀ ≤ σ.za + σ.zlo + 2 * K ∧ P.V₀ ≤ 18 + 2 * K ∧
      P.V₀ ≤ 18 + 2 * (K + σ.d) ∧
      Behind P.A P.B P.g (e + P.g) q ∧ InStrip P q ∧
      DiagValid P (K + σ.d) (shiftQ q (K + e + σ.n / 4))
  termination_by _ q => q.length
  decreasing_by simp [shiftQ]

/-- The footprint of the front salvo and the block at generation `i` (the block at `K`, the salvo
`e` cells behind; `Kn = K + e`): the salvo's box and the block, then the reaction, then the moved
block. -/
def frontFoot (σ : Salvo) (e K : ℤ) (Kn : ℕ) (i : ℕ) : Set Cell :=
  if i ≤ Kn * 4 then
    Box (σ.a - e + ((i / 4 : ℕ) : ℤ)) (σ.b - e + ((i / 4 : ℕ) : ℤ)) (σ.lo - e + ((i / 4 : ℕ) : ℤ))
      (σ.hi - e + ((i / 4 : ℕ) : ℤ)) ∪ Box (7 + K) (8 + K) (11 + K) (12 + K)
  else if i ≤ Kn * 4 + σ.n then Box (σ.za + K) (σ.zb + K) (σ.zlo + K) (σ.zhi + K)
  else Box (7 + σ.d + K) (8 + σ.d + K) (11 + σ.d + K) (12 + σ.d + K)

/-- The front salvo and the block, as one translated process. -/
theorem Salvo.front_eq (σ : Salvo) {e K : ℤ} {Kn : ℕ} (hK : (Kn : ℤ) = K + e) :
    σ.at e ∪ counter K = translate (-e, -e) (σ.S ∪ counter Kn) := by
  rw [translate_union, translate_counter, Salvo.at]
  congr 2
  omega

/-- Every generation of the front salvo and the block lies in `frontFoot`. -/
theorem Salvo.front_subset (σ : Salvo) {e K : ℤ} {Kn : ℕ} (hK : (Kn : ℤ) = K + e) (i : ℕ) :
    (conway.evolve i (σ.at e ∪ counter K) : Set Cell) ⊆ frontFoot σ e K Kn i := by
  intro c hc
  rw [σ.front_eq hK, Rule.evolve_translate, mem_coe, mem_translate] at hc
  have := salvo_track_all σ.four σ.box σ.hz σ.hhi Kn i (mem_coe.2 hc)
  simp only [frontFoot]
  split_ifs at this ⊢ with h1 h2
  · rcases this with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · left
      simp only [Prod.fst_sub, Prod.snd_sub] at a1 a2 a3 a4
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · right
      simp only [Prod.fst_sub, Prod.snd_sub] at a1 a2 a3 a4
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · obtain ⟨a1, a2, a3, a4⟩ := this
    simp only [Prod.fst_sub, Prod.snd_sub] at a1 a2 a3 a4
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · obtain ⟨a1, a2, a3, a4⟩ := this
    simp only [Prod.fst_sub, Prod.snd_sub] at a1 a2 a3 a4
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The front salvo has moved the block. -/
theorem Salvo.front_end (σ : Salvo) {e K : ℤ} {Kn : ℕ} (hK : (Kn : ℤ) = K + e) :
    conway.evolve (Kn * 4 + σ.n) (σ.at e ∪ counter K) = counter (K + σ.d) := by
  have h := salvo_track_reaction σ.four σ.box σ.hz σ.hhi Kn
  rw [σ.front_eq hK, Rule.evolve_translate, h.evolve_eq, translate_counter]
  congr 1
  omega

/-- Salvos in flight inside the strip stay inside it. -/
theorem flightsFoot_strip (P : DiagParams) : ∀ (q : List (Salvo × ℤ)), InStrip P q →
    ∀ i, flightsFoot q i ⊆ diagStrip P.U₁ P.U₂ P.V₀
  | [], _, _, _, hc => hc.elim
  | (τ, f) :: q, ⟨h1, h2, h3, hq⟩, i, c, hc => by
    rcases hc with ⟨a1, a2, a3, a4⟩ | hc
    · refine ⟨by linarith, by linarith, ?_⟩
      have : (0 : ℤ) ≤ ((i / 4 : ℕ) : ℤ) := by positivity
      linarith
    · exact flightsFoot_strip P q hq i hc

/-- **The diagonal of a register stays in its strip**: a block at `K` with a valid queue of salvos
behind it lies, at every generation, in the strip of the diagonal. -/
theorem diag_strip (P : DiagParams) (hP : P.Good) : ∀ (n : ℕ) (q : List (Salvo × ℤ)) (K : ℤ),
    q.length = n → DiagValid P K q →
      ∀ i, (conway.evolve i (flights q ∪ counter K) : Set Cell) ⊆ diagStrip P.U₁ P.U₂ P.V₀
  | _, [], K, _, hv, i => by
    rw [DiagValid] at hv
    obtain ⟨-, -, -, -, hU₁, hU₂⟩ := hP
    rw [flights, empty_union, (counter_isStillLife K).evolve]
    intro c hc
    obtain ⟨a1, a2, a3, a4⟩ := counter_subset_box K hc
    exact ⟨by linarith, by linarith, by linarith⟩
  | n, (σ, e) :: q, K, hlen, hv, i => by
    rw [DiagValid] at hv
    obtain ⟨hKe, hn4, hA, hB, hZA, hN, hd, hu1, hu2, hz1, hz2, hv1, hv2, hv3, hv4, hbeh, hin,
      hrest⟩ := hv
    obtain ⟨hg1, hg2, hg3, hg4, hU₁, hU₂⟩ := hP
    obtain ⟨Kn, hK⟩ : ∃ Kn : ℕ, (Kn : ℤ) = K + e := ⟨(K + e).toNat, Int.toNat_of_nonneg hKe⟩
    have hg0 : 0 ≤ P.g := by
      have : (0 : ℤ) ≤ (P.N : ℤ) / 4 := by positivity
      linarith
    have hcfg : flights ((σ, e) :: q) ∪ counter K = (σ.at e ∪ counter K) ∪ flights q := by
      rw [flights]; ac_rfl
    have hn4' : ((σ.n / 4 : ℕ) : ℤ) * 4 = σ.n := by omega
    -- the front process and the rest in flight, side by side until the front salvo is done
    have hsep : ∀ k < Kn * 4 + σ.n, FarApart 2 (frontFoot σ e K Kn k) (flightsFoot q k) := by
      intro k hk
      have hfl := flightsFoot_le hg0 q (e + P.g) hbeh k
      have hk4 : ((k / 4 : ℕ) : ℤ) ≤ Kn + σ.n / 4 := by
        have : k / 4 ≤ Kn + σ.n / 4 := by omega
        exact_mod_cast this
      refine (farApart_of_fst (X := P.B - (e + P.g) + ((k / 4 : ℕ) : ℤ)) hfl ?_).symm'
      intro c hc
      simp only [frontFoot] at hc
      split_ifs at hc with h1 h2
      · rcases hc with ⟨a1, -, -, -⟩ | ⟨a1, -, -, -⟩
        · linarith
        · have : ((k / 4 : ℕ) : ℤ) ≤ Kn := by
            have : k / 4 ≤ Kn := by omega
            exact_mod_cast this
          linarith
      · obtain ⟨a1, -, -, -⟩ := hc
        have : ((σ.n : ℤ)) / 4 ≤ (P.N : ℤ) / 4 :=
          Int.ediv_le_ediv (by norm_num) (by exact_mod_cast hN)
        have : ((σ.n / 4 : ℕ) : ℤ) = (σ.n : ℤ) / 4 := by push_cast; ring_nf
        linarith
      · omega
    have hpar := (show Reaction (σ.at e ∪ counter K) (conway.evolve (Kn * 4 + σ.n)
        (σ.at e ∪ counter K)) (Kn * 4 + σ.n) (frontFoot σ e K Kn) from
      ⟨rfl, fun j _ => σ.front_subset hK j⟩).par
      (flights_reaction hg1 hg0 q (e + P.g) hbeh (Kn * 4 + σ.n)) hsep
    by_cases hi : i ≤ Kn * 4 + σ.n
    · rw [hcfg]
      refine (hpar.subset i hi).trans (Set.union_subset ?_ (flightsFoot_strip P q hin i))
      intro c hc
      simp only [frontFoot] at hc
      split_ifs at hc with h1
      · rcases hc with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
        · refine ⟨by linarith, by linarith, ?_⟩
          have : (0 : ℤ) ≤ ((i / 4 : ℕ) : ℤ) := by positivity
          linarith
        · exact ⟨by linarith, by linarith, by linarith⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hc
        exact ⟨by linarith, by linarith, by linarith⟩
    · have hend : conway.evolve (Kn * 4 + σ.n) (flights ((σ, e) :: q) ∪ counter K) =
          flights (shiftQ q (K + e + σ.n / 4)) ∪ counter (K + σ.d) := by
        rw [hcfg, hpar.evolve_eq, σ.front_end hK,
          show Kn * 4 + σ.n = (Kn + σ.n / 4) * 4 by omega,
          flights_evolve_mul hg1 hg0 q (e + P.g) hbeh (Kn + σ.n / 4)]
        rw [union_comm]
        congr 2
        push_cast
        rw [hK]
      rw [show i = (i - (Kn * 4 + σ.n)) + (Kn * 4 + σ.n) by omega, Rule.evolve_add, hend]
      exact diag_strip P ⟨hg1, hg2, hg3, hg4, hU₁, hU₂⟩ (n - 1) _ _
        (by simp [shiftQ] at hlen ⊢; omega) hrest _

end LeanTheory.Life
