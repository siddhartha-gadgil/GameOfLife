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
  process, the others in flight; when the front salvo is done the next one leads);
* `diag_step`, `diag_end`: one salvo after the other moves the block; after `diagTime` generations
  the block is at its start moved by all the salvos (`qMove`), and stays there;
* `diag_add`: a salvo emitted later is a salvo that started at the beginning, further back;
* `diag_near`: when every salvo is far along, near the start of the diagonal there is only the
  block at its final position (the zero test reads the value correctly).
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

/-- The strip of a register diagonal at generation `i`: lanes `U₁ ≤ x - y ≤ U₂`, and `x + y` at
least `Vs + 2 (i / 4)` (the salvos advance) or `Vb` (blocks and reactions). -/
def diagStrip (U₁ U₂ Vs Vb : ℤ) (i : ℕ) : Set Cell :=
  {c | U₁ ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U₂ ∧ min (Vs + 2 * ((i / 4 : ℕ) : ℤ)) Vb ≤ c.1 + c.2}

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

/-- The gap is large enough for the salvos and reactions of the parameters. -/
def DiagParams.Good (P : DiagParams) : Prop :=
  P.B - P.A + 3 ≤ P.g ∧ P.B - 4 ≤ P.g ∧ P.B + P.N / 4 + 3 - P.ZA ≤ P.g ∧ (P.N : ℤ) / 4 + 1 ≤ P.g ∧
    P.U₁ ≤ -5 ∧ -3 ≤ P.U₂

/-- Every salvo of a list, at its offset, lies in the strip (`x + y ≥ Vs` at generation `0`). -/
def InStrip (P : DiagParams) (Vs : ℤ) : List (Salvo × ℤ) → Prop
  | [] => True
  | (τ, f) :: q => P.U₁ ≤ τ.a - τ.hi ∧ τ.b - τ.lo ≤ P.U₂ ∧ Vs ≤ τ.a + τ.lo - 2 * f ∧
      InStrip P Vs q

/-- A valid queue: the front salvo is in front of the block (at offset `≥ -K`), fits the
parameters, every box lies in the strip, the rest is far enough behind, and the queue that remains
after the front salvo has moved the block is valid. -/
def DiagValid (P : DiagParams) : ℤ → ℤ → ℤ → List (Salvo × ℤ) → Prop
  | _, Vb, K, [] => Vb ≤ 18 + 2 * K
  | Vs, Vb, K, (σ, e) :: q => 0 ≤ K + e ∧ σ.n % 4 = 0 ∧ P.A ≤ σ.a ∧ σ.b ≤ P.B ∧ P.ZA ≤ σ.za ∧
      σ.n ≤ P.N ∧ (σ.d = 1 ∨ σ.d = -1) ∧
      P.U₁ ≤ σ.a - σ.hi ∧ σ.b - σ.lo ≤ P.U₂ ∧ P.U₁ ≤ σ.za - σ.zhi ∧ σ.zb - σ.zlo ≤ P.U₂ ∧
      Vs ≤ σ.a + σ.lo - 2 * e ∧ Vb ≤ σ.za + σ.zlo + 2 * K ∧ Vb ≤ 18 + 2 * K ∧
      Vb ≤ 18 + 2 * (K + σ.d) ∧
      Behind P.A P.B P.g (e + P.g) q ∧ InStrip P Vs q ∧
      DiagValid P (Vs + 2 * (K + e + σ.n / 4)) Vb (K + σ.d) (shiftQ q (K + e + σ.n / 4))
  termination_by _ _ _ q => q.length
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
theorem flightsFoot_strip (P : DiagParams) (Vs Vb : ℤ) : ∀ (q : List (Salvo × ℤ)), InStrip P Vs q →
    ∀ i, flightsFoot q i ⊆ diagStrip P.U₁ P.U₂ Vs Vb i
  | [], _, _, _, hc => hc.elim
  | (τ, f) :: q, ⟨h1, h2, h3, hq⟩, i, c, hc => by
    rcases hc with ⟨a1, a2, a3, a4⟩ | hc
    · refine ⟨by linarith, by linarith, ?_⟩
      have := min_le_left (Vs + 2 * ((i / 4 : ℕ) : ℤ)) Vb
      linarith
    · exact flightsFoot_strip P Vs Vb q hq i hc

/-- **The diagonal of a register stays in its strip**: a block at `K` with a valid queue of salvos
behind it lies, at every generation, in the strip of the diagonal. -/
theorem diag_strip (P : DiagParams) (hP : P.Good) :
    ∀ (n : ℕ) (q : List (Salvo × ℤ)) (Vs Vb K : ℤ), q.length = n → DiagValid P Vs Vb K q →
      ∀ i, (conway.evolve i (flights q ∪ counter K) : Set Cell) ⊆ diagStrip P.U₁ P.U₂ Vs Vb i
  | _, [], Vs, Vb, K, _, hv, i => by
    rw [DiagValid] at hv
    obtain ⟨-, -, -, -, hU₁, hU₂⟩ := hP
    rw [flights, empty_union, (counter_isStillLife K).evolve]
    intro c hc
    obtain ⟨a1, a2, a3, a4⟩ := counter_subset_box K hc
    have := min_le_right (Vs + 2 * ((i / 4 : ℕ) : ℤ)) Vb
    exact ⟨by linarith, by linarith, by linarith⟩
  | n, (σ, e) :: q, Vs, Vb, K, hlen, hv, i => by
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
      refine (hpar.subset i hi).trans (Set.union_subset ?_ (flightsFoot_strip P Vs Vb q hin i))
      intro c hc
      have m1 := min_le_left (Vs + 2 * ((i / 4 : ℕ) : ℤ)) Vb
      have m2 := min_le_right (Vs + 2 * ((i / 4 : ℕ) : ℤ)) Vb
      simp only [frontFoot] at hc
      split_ifs at hc with h1
      · rcases hc with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
        · exact ⟨by linarith, by linarith, by linarith⟩
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
      have hsplit : conway.evolve i (flights ((σ, e) :: q) ∪ counter K) =
          conway.evolve (i - (Kn * 4 + σ.n)) (conway.evolve (Kn * 4 + σ.n)
            (flights ((σ, e) :: q) ∪ counter K)) := by
        rw [← Rule.evolve_add, show i - (Kn * 4 + σ.n) + (Kn * 4 + σ.n) = i by omega]
      rw [hsplit, hend]
      have hih := diag_strip P ⟨hg1, hg2, hg3, hg4, hU₁, hU₂⟩ (n - 1) _ _ _ _
        (by simp [shiftQ] at hlen ⊢; omega) hrest (i - (Kn * 4 + σ.n))
      refine hih.trans fun c ⟨c1, c2, c3⟩ => ⟨c1, c2, ?_⟩
      have key : Vs + 2 * (K + e + ↑σ.n / 4) + 2 * (((i - (Kn * 4 + σ.n)) / 4 : ℕ) : ℤ) =
          Vs + 2 * ((i / 4 : ℕ) : ℤ) := by
        have h5 : (i - (Kn * 4 + σ.n)) / 4 = i / 4 - (Kn + σ.n / 4) := by omega
        have h6 : Kn + σ.n / 4 ≤ i / 4 := by omega
        rw [h5]
        push_cast [h6]
        rw [← hK]
        omega
      rwa [key] at c3

/-- The sum of the moves of a queue. -/
def qMove : List (Salvo × ℤ) → ℤ
  | [] => 0
  | (σ, _) :: q => σ.d + qMove q

/-- The time until every salvo of a valid queue has arrived. -/
def diagTime : ℤ → List (Salvo × ℤ) → ℕ
  | _, [] => 0
  | K, (σ, e) :: q => (K + e).toNat * 4 + σ.n + diagTime (K + σ.d) (shiftQ q (K + e + σ.n / 4))
  termination_by _ q => q.length
  decreasing_by simp [shiftQ]

/-- The moves of a shifted queue are those of the queue. -/
theorem qMove_shiftQ : ∀ (q : List (Salvo × ℤ)) (m : ℤ), qMove (shiftQ q m) = qMove q
  | [], _ => rfl
  | (σ, e) :: q, m => by
    simp only [shiftQ, List.map_cons, qMove] at *
    rw [← qMove_shiftQ q m]
    rfl

/-- **One step of the diagonal**: when the front salvo has done its work, the block has moved and
the other salvos have come closer. -/
theorem diag_step (P : DiagParams) (hP : P.Good) (σ : Salvo) (Vs Vb e K : ℤ)
    (q : List (Salvo × ℤ)) (hv : DiagValid P Vs Vb K ((σ, e) :: q)) :
    conway.evolve ((K + e).toNat * 4 + σ.n) (flights ((σ, e) :: q) ∪ counter K) =
      flights (shiftQ q (K + e + σ.n / 4)) ∪ counter (K + σ.d) := by
  rw [DiagValid] at hv
  obtain ⟨hKe, hn4, hA, hB, hZA, hN, hd, -, -, -, -, -, -, -, -, hbeh, -, -⟩ := hv
  obtain ⟨hg1, hg2, hg3, hg4, -, -⟩ := hP
  set Kn := (K + e).toNat with hKn
  have hK : (Kn : ℤ) = K + e := Int.toNat_of_nonneg hKe
  have hg0 : 0 ≤ P.g := by
    have : (0 : ℤ) ≤ (P.N : ℤ) / 4 := by positivity
    linarith
  have hcfg : flights ((σ, e) :: q) ∪ counter K = (σ.at e ∪ counter K) ∪ flights q := by
    rw [flights]; ac_rfl
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
  rw [hcfg, hpar.evolve_eq, σ.front_end hK,
    show Kn * 4 + σ.n = (Kn + σ.n / 4) * 4 by omega,
    flights_evolve_mul hg1 hg0 q (e + P.g) hbeh (Kn + σ.n / 4), union_comm]
  congr 2
  push_cast
  rw [hK]

/-- **The value of a register**: once every salvo of a valid queue has arrived, the block is at its
start moved by all the salvos, and stays there. -/
theorem diag_end (P : DiagParams) (hP : P.Good) :
    ∀ (n : ℕ) (q : List (Salvo × ℤ)) (Vs Vb K : ℤ), q.length = n → DiagValid P Vs Vb K q →
      ∀ j : ℕ, conway.evolve (j + diagTime K q) (flights q ∪ counter K) = counter (K + qMove q)
  | _, [], _, _, K, _, _, j => by
    rw [diagTime, flights, empty_union, (counter_isStillLife K).evolve, qMove, add_zero]
  | n, (σ, e) :: q, Vs, Vb, K, hlen, hv, j => by
    have hstep := diag_step P hP σ Vs Vb e K q hv
    rw [DiagValid] at hv
    have hrest := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [diagTime, show j + ((K + e).toNat * 4 + σ.n + diagTime (K + σ.d)
        (shiftQ q (K + e + σ.n / 4))) = (j + diagTime (K + σ.d) (shiftQ q (K + e + σ.n / 4))) +
        ((K + e).toNat * 4 + σ.n) by ring, Rule.evolve_add, hstep,
      diag_end P hP (n - 1) _ _ _ _ (by simp [shiftQ] at hlen ⊢; omega) hrest j, qMove_shiftQ,
      qMove]
    congr 1
    ring

/-- Sets separated in `x + y` by more than four are far apart. -/
theorem farApart_of_sum {A B : Set Cell} {W : ℤ} (hA : ∀ c ∈ A, c.1 + c.2 ≤ W)
    (hB : ∀ c ∈ B, W + 5 ≤ c.1 + c.2) : FarApart 2 A B := by
  rintro a ha b hb ⟨h1, h2, h3, h4⟩
  have := hA a ha
  have := hB b hb
  push_cast at h1 h2 h3 h4
  omega

/-- Salvos in flight with one more at the back. -/
theorem flights_append (q : List (Salvo × ℤ)) (σ : Salvo) (e : ℤ) :
    flights (q ++ [(σ, e)]) = flights q ∪ σ.at e := by
  induction q with
  | nil => simp [flights]
  | cons p q ih =>
    obtain ⟨τ, f⟩ := p
    simp only [List.cons_append, flights, ih, union_assoc]

/-- **Adding a salvo at the back of a diagonal.** A salvo far enough behind a valid diagonal, in
`x + y`, flies untouched while the diagonal evolves: after `t` generations (a multiple of four)
the diagonal with the salvo is the evolved diagonal and the salvo `t / 4` cells further. -/
theorem diag_add (P : DiagParams) (hP : P.Good) (q : List (Salvo × ℤ)) (Vs Vb K : ℤ)
    (hv : DiagValid P Vs Vb K q) (σ : Salvo) (e : ℤ) (t : ℕ) (ht : t % 4 = 0)
    (h1 : σ.b + σ.hi - 2 * e + 5 ≤ Vs)
    (h2 : σ.b + σ.hi - 2 * e + 2 * ((t / 4 : ℕ) : ℤ) + 5 ≤ Vb) :
    conway.evolve t (flights (q ++ [(σ, e)]) ∪ counter K) =
      conway.evolve t (flights q ∪ counter K) ∪ σ.at (e - (t / 4 : ℕ)) := by
  have hsep : ∀ k < t, Sep 2 (conway.evolve k (flights q ∪ counter K))
      (conway.evolve k (σ.at e)) := by
    intro k hk
    refine (farApart_of_sum (W := σ.b + σ.hi - 2 * e + 2 * ((k / 4 : ℕ) : ℤ)) ?_ ?_).symm'.sep
      (diag_strip P hP _ q Vs Vb K rfl hv k) (σ.subset_at e k)
    · rintro c ⟨-, a2, -, a4⟩
      linarith
    · rintro c ⟨-, -, c3⟩
      have hk4 : ((k / 4 : ℕ) : ℤ) ≤ ((t / 4 : ℕ) : ℤ) := by
        have : k / 4 ≤ t / 4 := Nat.div_le_div_right hk.le
        exact_mod_cast this
      rcases min_choice (Vs + 2 * ((k / 4 : ℕ) : ℤ)) Vb with hm | hm <;> rw [hm] at c3 <;>
        linarith
  rw [flights_append, show flights q ∪ σ.at e ∪ counter K = (flights q ∪ counter K) ∪ σ.at e by
    ac_rfl, conway.evolve_union_of_forall_sep hsep]
  congr 1
  rw [show t = (t / 4) * 4 by omega, σ.evolve_at, show t / 4 * 4 / 4 = t / 4 by omega]

/-- The front phase of a valid queue: the front salvo with the block, and the other salvos in
flight, side by side until the front salvo is done. -/
theorem diag_phaseA (P : DiagParams) (hP : P.Good) (σ : Salvo) (Vs Vb e K : ℤ)
    (q : List (Salvo × ℤ)) (hv : DiagValid P Vs Vb K ((σ, e) :: q)) :
    Reaction ((σ.at e ∪ counter K) ∪ flights q)
      (conway.evolve ((K + e).toNat * 4 + σ.n) ((σ.at e ∪ counter K) ∪ flights q))
      ((K + e).toNat * 4 + σ.n) (fun i => frontFoot σ e K (K + e).toNat i ∪ flightsFoot q i) := by
  rw [DiagValid] at hv
  obtain ⟨hKe, hn4, hA, hB, hZA, hN, hd, -, -, -, -, -, -, -, -, hbeh, -, -⟩ := hv
  obtain ⟨hg1, hg2, hg3, hg4, -, -⟩ := hP
  set Kn := (K + e).toNat with hKn
  have hK : (Kn : ℤ) = K + e := Int.toNat_of_nonneg hKe
  have hg0 : 0 ≤ P.g := by
    have : (0 : ℤ) ≤ (P.N : ℤ) / 4 := by positivity
    linarith
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
  have h := (show Reaction (σ.at e ∪ counter K) (conway.evolve (Kn * 4 + σ.n)
      (σ.at e ∪ counter K)) (Kn * 4 + σ.n) (frontFoot σ e K Kn) from
    ⟨rfl, fun j _ => σ.front_subset hK j⟩).par
    (flights_reaction hg1 hg0 q (e + P.g) hbeh (Kn * 4 + σ.n)) hsep
  exact ⟨rfl, h.subset⟩

/-- Salvos in flight, all at least `L` cells along at generation `i`, lie at `x ≥ A + L`. -/
theorem flightsFoot_ge {A B g : ℤ} (L : ℤ) : ∀ (q : List (Salvo × ℤ)) (e₀ : ℤ),
    Behind A B g e₀ q → ∀ i, (∀ p ∈ q, L ≤ ((i / 4 : ℕ) : ℤ) - p.2) →
      ∀ c ∈ flightsFoot q i, A + L ≤ c.1
  | [], _, _, _, _, _, hc => hc.elim
  | (σ, e) :: q, e₀, ⟨ha, _, _, hq⟩, i, hL, c, hc => by
    rcases hc with ⟨a1, -, -, -⟩ | hc
    · have := hL (σ, e) List.mem_cons_self
      simp only at this
      linarith
    · exact flightsFoot_ge L q (e + g) hq i (fun p hp => hL p (List.mem_cons_of_mem _ hp)) c hc

/-- **Near the start of the diagonal only the final block**: if at generation `t` every salvo of a
valid queue is at least `L` cells along the diagonal (offset `e` with `L ≤ t / 4 - e`), then every
live cell of the diagonal at generation `t` is far along (`x ≥ L - 40`) or belongs to the block at
its final position. -/
theorem diag_near (P : DiagParams) (hP : P.Good) (L : ℤ) (hA : -20 ≤ P.A) (hZ : -20 ≤ P.ZA)
    (hN : P.N ≤ 40) :
    ∀ (n : ℕ) (q : List (Salvo × ℤ)) (Vs Vb K : ℤ) (t : ℕ), q.length = n →
      DiagValid P Vs Vb K q → (∀ p ∈ q, L ≤ ((t / 4 : ℕ) : ℤ) - p.2) →
      ∀ c ∈ conway.evolve t (flights q ∪ counter K), L - 40 ≤ c.1 ∨ c ∈ counter (K + qMove q)
  | _, [], _, _, K, t, _, _, _, c, hc => by
    rw [flights, empty_union, (counter_isStillLife K).evolve] at hc
    right
    simpa [qMove] using hc
  | n, (σ, e) :: q, Vs, Vb, K, t, hlen, hv, hfar, c, hc => by
    have hstep := diag_step P hP σ Vs Vb e K q hv
    have hpar := diag_phaseA P hP σ Vs Vb e K q hv
    have hv' := hv
    rw [DiagValid] at hv'
    obtain ⟨hKe, hn4, hAσ, hB, hZA, hNσ, hd, -, -, -, -, -, -, -, -, hbeh, -, hrest⟩ := hv'
    have he := hfar (σ, e) List.mem_cons_self
    simp only at he
    set Kn := (K + e).toNat with hKn
    have hK : (Kn : ℤ) = K + e := Int.toNat_of_nonneg hKe
    have hcfg : flights ((σ, e) :: q) ∪ counter K = (σ.at e ∪ counter K) ∪ flights q := by
      rw [flights]; ac_rfl
    by_cases ht : t ≤ Kn * 4 + σ.n
    · -- the front salvo has not finished: everything is far along
      left
      rw [hcfg] at hc
      rcases hpar.subset t ht (mem_coe.2 hc) with hc | hc
      · simp only [frontFoot] at hc
        split_ifs at hc with h1
        · rcases hc with ⟨a1, -, -, -⟩ | ⟨a1, -, -, -⟩
          · linarith
          · have : ((t / 4 : ℕ) : ℤ) ≤ Kn := by
              have : t / 4 ≤ Kn := by omega
              exact_mod_cast this
            linarith
        · obtain ⟨a1, -, -, -⟩ := hc
          have h4 : ((t / 4 : ℕ) : ℤ) ≤ Kn + 10 := by
            have : t / 4 ≤ Kn + 10 := by omega
            exact_mod_cast this
          linarith
      · have := flightsFoot_ge L q (e + P.g) hbeh t
          (fun p hp => hfar p (List.mem_cons_of_mem _ hp)) c hc
        linarith
    · have hsplit : conway.evolve t (flights ((σ, e) :: q) ∪ counter K) =
          conway.evolve (t - (Kn * 4 + σ.n)) (conway.evolve (Kn * 4 + σ.n)
            (flights ((σ, e) :: q) ∪ counter K)) := by
        rw [← Rule.evolve_add, show t - (Kn * 4 + σ.n) + (Kn * 4 + σ.n) = t by omega]
      rw [hsplit, hstep] at hc
      have hshift : ∀ p ∈ shiftQ q (K + e + σ.n / 4),
          L ≤ (((t - (Kn * 4 + σ.n)) / 4 : ℕ) : ℤ) - p.2 := by
        intro p hp
        simp only [shiftQ, List.mem_map] at hp
        obtain ⟨p', hp', rfl⟩ := hp
        have := hfar p' (List.mem_cons_of_mem _ hp')
        have h5 : (t - (Kn * 4 + σ.n)) / 4 = t / 4 - (Kn + σ.n / 4) := by omega
        have h6 : Kn + σ.n / 4 ≤ t / 4 := by omega
        rw [h5]
        push_cast [h6]
        omega
      rcases diag_near P hP L hA hZ hN (n - 1) _ _ _ _ _ (by simp [shiftQ] at hlen ⊢; omega) hrest
        hshift c hc with h | h
      · exact Or.inl h
      · right
        rwa [qMove_shiftQ, show K + σ.d + qMove q = K + qMove ((σ, e) :: q) by
          simp only [qMove]; ring] at h

end LeanTheory.Life
