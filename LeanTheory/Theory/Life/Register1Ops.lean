/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Register1Inc
public import LeanTheory.Theory.Life.ContinueIncrement

/-!
# The register `REG1`: decrement and increment of one block, for every position

With the two input reactions of `Theory/Life/Register1` and `Theory/Life/Register1Inc`, this
module proves that `REG1` operates one block (research note `N-15`):

* `reg1_decrement`: for every `k`, the register at rest, the decrement control glider and the
  block at position `k` evolve into the register (in its cycle) and the block at position
  `k - 1` (position `-1` when `k = 0`), and nothing else;
* `reg1_increment`: likewise with the increment control glider and the block at `k + 1`.

Both act on the **same** block `reg1Block k = translate (148, 240) (counter k)`.

The block reactions are instances of the general lemma `salvo_quad_reaction`: a salvo of gliders
flying down and to the right that acts on the block at position `0` acts in the same way at
every position `k`, staying in a quadrant. The salvos are `reg1DecLocal` and `reg1IncLocal` in
the frame of `counter`: the pulling salvo `pullSalvo` and a three-glider push sharing one glider
with it, both from the project's own search (report `R-24`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- **A salvo acts in the same way at every position of the block.** A pattern `S` that moves one
cell down and to the right every four generations, stays in a box with rows `≤ 9` during its first
four generations, and acts on the block at position `0` in `n` generations, turning it into the
block at position `d`, acts on the block at every position `k` in `k * 4 + n` generations, turning
it into the block at position `d + k`, and stays in the quadrant `X ≤ x`, `Y ≤ y`. -/
theorem salvo_quad_reaction {S : Finset Cell} {a b lo hi za zb zlo zhi X Y d : ℤ} {n : ℕ}
    (h4 : conway.evolve 4 S = translate (1, 1) S)
    (hB : ∀ r < 4, (conway.evolve r S : Set Cell) ⊆ Box a b lo hi)
    (hz : Reaction (S ∪ counter 0) (counter d) n (fun _ => Box za zb zlo zhi))
    (hhi : hi ≤ 9) (hX : X ≤ a) (hX' : X ≤ za) (hX'' : X ≤ 7) (hY : Y ≤ lo) (hY' : Y ≤ zlo)
    (hY'' : Y ≤ 11) (k : ℕ) :
    Reaction (S ∪ counter k) (counter (d + k)) (k * 4 + n)
      (fun _ => {c : Cell | X ≤ c.1 ∧ Y ≤ c.2}) := by
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
  · refine Set.union_subset ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      have h1 := hc.1
      have h2 := hc.2.2.1
      change X ≤ ((i / 4) • ((1, 1) : Cell) + c).1 ∧ Y ≤ ((i / 4) • ((1, 1) : Cell) + c).2
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul]
      push_cast
      omega
    · intro c hc
      have h1 := hc.1
      have h2 := hc.2.2.1
      exact ⟨by omega, by omega⟩
  · rintro _ ⟨c, hc, rfl⟩
    have h1 := hc.1
    have h2 := hc.2.2.1
    change X ≤ (((k : ℤ), (k : ℤ)) + c).1 ∧ Y ≤ (((k : ℤ), (k : ℤ)) + c).2
    simp only [Prod.fst_add, Prod.snd_add]
    omega

/-! ### The salvos of `REG1` in the frame of `counter` -/

/-- The pulling salvo of `REG1` in the frame of `counter`, when the decrement reaction is over. -/
def reg1DecLocal : Finset Cell := ofRows (-6) 0 [4, 261, 1542, 768]

/-- The pushing salvo of `REG1` in the frame of `counter`, when the increment reaction is over. -/
def reg1IncLocal : Finset Cell :=
  ofRows (-11) (-13) [128, 256, 448, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 8199, 49152, 24576]

/-- The decrement salvo is the local salvo placed at the register block. -/
theorem reg1DecSalvo_eq : reg1DecSalvo = translate (148, 240) reg1DecLocal := by
  rw [reg1DecSalvo, reg1DecLocal, translate_ofRows]
  norm_num

/-- The increment salvo is the local salvo placed at the register block. -/
theorem reg1IncSalvo_eq : reg1IncSalvo = translate (148, 240) reg1IncLocal := by
  rw [reg1IncSalvo, reg1IncLocal, translate_ofRows]
  norm_num

theorem reg1DecLocal_evolve_four :
    conway.evolve 4 reg1DecLocal = translate (1, 1) reg1DecLocal := by
  rw [reg1DecLocal, translate_ofRows]
  life_cert

theorem reg1IncLocal_evolve_four :
    conway.evolve 4 reg1IncLocal = translate (1, 1) reg1IncLocal := by
  rw [reg1IncLocal, translate_ofRows]
  life_cert

theorem reg1DecLocal_subset_box (r : ℕ) (hr : r < 4) :
    (conway.evolve r reg1DecLocal : Set Cell) ⊆ Box (-6) 4 0 4 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

theorem reg1IncLocal_subset_box (r : ℕ) (hr : r < 4) :
    (conway.evolve r reg1IncLocal : Set Cell) ⊆ Box (-11) 4 (-13) 4 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- **Certificate**: the pulling salvo at position `0`, 48 generations. -/
theorem reg1Dec_zero :
    Reaction (reg1DecLocal ∪ counter 0) (counter (-1)) 48 (fun _ => Box (-6) 14 0 12) := by
  rw [show reg1DecLocal ∪ counter 0 =
      ofRows (-6) 0 [4, 261, 1542, 768, 0, 0, 0, 0, 0, 0, 0, 24576, 24576] by
        rw [reg1DecLocal, counter, ofRows_eq_padRows' (-6) 0 (7 + 0) (11 + 0) 11 13 _
          (by norm_num) (by norm_num), ← ofRows_orRows]
        rfl,
    show counter (-1) = ofRows 6 10 [3, 3] by rw [counter]; norm_num]
  life_reaction

/-- **Certificate**: the pushing salvo at position `0`, 57 generations. -/
theorem reg1Inc_zero :
    Reaction (reg1IncLocal ∪ counter 0) (counter 1) 57 (fun _ => Box (-11) 15 (-13) 15) := by
  rw [show reg1IncLocal ∪ counter 0 =
      ofRows (-11) (-13) [128, 256, 448, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 8199, 49152, 24576, 0,
        0, 0, 0, 0, 0, 0, 786432, 786432] by
        rw [reg1IncLocal, counter, ofRows_eq_padRows' (-11) (-13) (7 + 0) (11 + 0) 24 18 _
          (by norm_num) (by norm_num), ← ofRows_orRows]
        rfl,
    show counter 1 = ofRows 8 12 [3, 3] by rw [counter]; norm_num]
  life_reaction

/-! ### The register block and the operations -/

/-- The block of `REG1` at position `k`. -/
def reg1Block (k : ℤ) : Finset Cell := translate (148, 240) (counter k)

/-- The register block at position `k` lies in its box. -/
theorem reg1Block_subset_box (k : ℤ) :
    (reg1Block k : Set Cell) ⊆ Box (155 + k) (156 + k) (251 + k) (252 + k) := by
  intro c hc
  rw [mem_coe, reg1Block, mem_translate] at hc
  obtain ⟨h1, h2, h3, h4⟩ := counter_subset_box k (mem_coe.2 hc)
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  exact ⟨by omega, by omega, by omega, by omega⟩

set_option maxRecDepth 100000 in
/-- An operation of the register: the input reaction beside the resting block, then the salvo's
reaction on the block beside the resting register (block at any position `k ≥ -1`). -/
theorem reg1_operation {C G L : Finset Cell} {N n : ℕ} {B : Set Cell} {X Y d : ℤ} (k : ℤ)
    (hk : -1 ≤ k) (hin : Reaction (reg1 ∪ C) (reg1 ∪ G) N (fun _ => B))
    (hB : ∀ c ∈ B, c.2 ≤ 243) (hG : G = translate (148, 240) L)
    (hL : Reaction (L ∪ counter k) (counter (d + k)) n
      (fun _ => {c : Cell | X ≤ c.1 ∧ Y ≤ c.2}))
    (hY : -16 ≤ Y) :
    conway.evolve (N + n) (reg1 ∪ C ∪ reg1Block k) =
      conway.evolve n reg1 ∪ reg1Block (d + k) := by
  have hBk : ∀ m, Reaction (reg1Block k) (reg1Block k) m
      (fun _ => Box (155 + k) (156 + k) (251 + k) (252 + k)) :=
    fun m => ((counter_isStillLife k).translate _).reaction_box (reg1Block_subset_box k) m
  have h1 := hin.par (hBk N) (fun _ _ a ha b hb hn => by
    have h1 := hB a ha
    have h2 := hb.2.2.1
    obtain ⟨-, -, h4, -⟩ := hn
    push_cast at h2 h4
    omega)
  rw [hG, union_assoc reg1 (translate (148, 240) L)] at h1
  have hS := hL.translate (148, 240)
  rw [translate_union] at hS
  change Reaction (translate (148, 240) L ∪ reg1Block k) (reg1Block (d + k)) _ _ at hS
  have h2 := (reaction_of_periodic (by norm_num) reg1_evolve_thirty reg1_subset_box n).par hS
    (fun _ _ a ha _ ⟨c, hc, hb⟩ hn => by
      subst hb
      have h1 : Y ≤ c.2 := hc.2
      have h2 : a.2 ≤ 221 := ha.2.2.2
      obtain ⟨-, -, h4, -⟩ := hn
      simp only [Prod.snd_add] at h4
      push_cast at h4
      omega)
  exact (h1.seq h2).evolve_eq

set_option maxRecDepth 100000 in
/-- **Decrement of the register, for every position.** One control glider into the decrement
input of `REG1` moves the block from position `k` to position `k - 1` (to `-1` when `k = 0`); the
register is left in its cycle and nothing else remains. -/
theorem reg1_decrement (k : ℕ) :
    conway.evolve (3120 + (k * 4 + 48)) (reg1 ∪ reg1DecControl ∪ reg1Block k) =
      conway.evolve (k * 4 + 48) reg1 ∪ reg1Block (k - 1) := by
  have h := reg1_operation k (by omega) reg1Dec_reaction (fun c hc => hc.2.2.2) reg1DecSalvo_eq
    (salvo_quad_reaction (X := -6) (Y := 0) reg1DecLocal_evolve_four reg1DecLocal_subset_box
      reg1Dec_zero (by norm_num) le_rfl le_rfl (by norm_num) le_rfl le_rfl (by norm_num) k)
    (by norm_num)
  rwa [show (-1 : ℤ) + k = k - 1 by omega] at h

set_option maxRecDepth 100000 in
/-- **Increment of the register, for every position.** One control glider into the increment
input of `REG1` moves the **same** block from position `k` to position `k + 1`; the register is
left in its cycle and nothing else remains. -/
theorem reg1_increment (k : ℕ) :
    conway.evolve (3570 + (k * 4 + 57)) (reg1 ∪ reg1IncControl ∪ reg1Block k) =
      conway.evolve (k * 4 + 57) reg1 ∪ reg1Block (k + 1) := by
  have h := reg1_operation k (by omega) reg1Inc_reaction (fun c hc => hc.2.2.2) reg1IncSalvo_eq
    (salvo_quad_reaction (X := -11) (Y := -13) reg1IncLocal_evolve_four reg1IncLocal_subset_box
      reg1Inc_zero (by norm_num) le_rfl le_rfl (by norm_num) le_rfl le_rfl (by norm_num) k)
    (by norm_num)
  rwa [show (1 : ℤ) + k = k + 1 by omega] at h

end LeanTheory.Life
