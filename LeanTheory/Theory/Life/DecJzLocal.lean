/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Register1Ops

/-!
# The zero test of `REG1` by decrement from zero: the reactions at the block

The design `DZ2` (research note `N-15`, report `R-27`, the project's own search) tests the
register for zero by decrementing it anyway. The decrement moves the block from position `k` to
position `k - 1`, that is to `-1` when `k = 0`. A detector glider flying down and to the left
then tells the two cases apart, and in case zero the block is put back. This module certifies the
reactions at the block, in the frame of `counter`; they do not depend on how the gliders are
supplied:

* `dz2Detector_zero`: the detector turns the block at position `-1` into the block
  `dz2DetectorBlock`;
* `dz2Detector_pass`: the detector passes the block at every position `j ≥ 0` without touching
  it;
* `dz2Restore_zero`: the restore glider turns `dz2DetectorBlock` back into the block at `-1`;
* `reg1_increment_neg_one`: the increment input of `REG1` moves the block from `-1` to `0`.

Together: in case zero the block returns to position `0`; otherwise the detector flies on.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### The detector glider -/

/-- The detector glider of `DZ2`, flying down and to the left (world line `(SW, 9, 61)` of
`R-27`, at generation `45`).
```
.O.
O..
OOO
```
-/
def dz2Detector : Finset Cell := ofRows 4 5 [2, 1, 7]

/-- The detector moves one cell down and to the left every four generations. -/
theorem dz2Detector_evolve_four :
    conway.evolve 4 dz2Detector = translate (-1, 1) dz2Detector := by
  rw [dz2Detector, translate_ofRows]
  life_cert

/-- During its first four generations the detector stays in a box. -/
theorem dz2Detector_subset_box (r : ℕ) (hr : r < 4) :
    (conway.evolve r dz2Detector : Set Cell) ⊆ Box 3 6 5 8 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- The detector after sixteen generations. -/
def dz2Detector16 : Finset Cell := ofRows 0 9 [2, 1, 7]

/-- After sixteen generations the detector has moved four cells down and to the left. -/
theorem dz2Detector_evolve_sixteen : conway.evolve 16 dz2Detector = dz2Detector16 := by
  rw [show 16 = 4 * 4 by norm_num, conway.evolve_mul_of_evolve_eq_translate
    dz2Detector_evolve_four, dz2Detector, dz2Detector16, translate_ofRows]
  norm_num

/-- The moved detector also moves one cell down and to the left every four generations. -/
theorem dz2Detector16_evolve_four :
    conway.evolve 4 dz2Detector16 = translate (-1, 1) dz2Detector16 := by
  rw [dz2Detector16, translate_ofRows]
  life_cert

/-- During its first four generations the moved detector stays in a box. -/
theorem dz2Detector16_subset_box (r : ℕ) (hr : r < 4) :
    (conway.evolve r dz2Detector16 : Set Cell) ⊆ Box (-1) 2 9 12 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- The block left by the detector at position `-1`. -/
def dz2DetectorBlock : Finset Cell := ofRows 7 8 [3, 3]

/-- **Certificate**: the detector turns the block at position `-1` into `dz2DetectorBlock`, in
nine generations. -/
theorem dz2Detector_zero :
    Reaction (dz2Detector ∪ counter (-1)) dz2DetectorBlock 9 (fun _ => Box 3 8 5 11) := by
  rw [show dz2Detector ∪ counter (-1) = ofRows 4 5 [2, 1, 7, 0, 0, 12, 12] by
      rw [dz2Detector, counter, ofRows_eq_padRows' 4 5 (7 + -1) (11 + -1) 5 2 _
        (by norm_num) (by norm_num), ← ofRows_orRows]
      rfl, dz2DetectorBlock]
  life_reaction

/-- **Certificate**: the detector passes the block at position `0` in sixteen generations. -/
theorem dz2Detector_pass_zero :
    Reaction (dz2Detector ∪ counter 0) (dz2Detector16 ∪ counter 0) 16
      (fun _ => Box (-1) 8 5 12) := by
  rw [show dz2Detector ∪ counter 0 = ofRows 4 5 [2, 1, 7, 0, 0, 0, 24, 24] by
      rw [dz2Detector, counter, ofRows_eq_padRows' 4 5 (7 + 0) (11 + 0) 6 3 _
        (by norm_num) (by norm_num), ← ofRows_orRows]
      rfl,
    show dz2Detector16 ∪ counter 0 = ofRows 0 9 [2, 1, 391, 384] by
      rw [dz2Detector16, counter, ofRows_eq_padRows' 0 9 (7 + 0) (11 + 0) 2 7 _
        (by norm_num) (by norm_num), ← ofRows_orRows]
      rfl]
  life_reaction

/-- **The detector passes the block at every position `j ≥ 0`**: after `n + 16` generations the
detector and the block are the free detector and the untouched block, and the reaction stays in
a box that grows with the detector's flight. -/
theorem dz2Detector_pass (j n : ℕ) :
    Reaction (dz2Detector ∪ counter j) (conway.evolve (n + 16) dz2Detector ∪ counter j)
      (n + 16) (fun i => Box (-1 - ((i / 4 : ℕ) : ℤ)) (8 + j) 5 (16 + j + ((i / 4 : ℕ) : ℤ))) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hfly := (reaction_flight_box' (by norm_num) dz2Detector16_evolve_four
      dz2Detector16_subset_box n).par
      ((counter_isStillLife 0).reaction_box (counter_subset_box 0) n)
      (fun i _ => by
        rw [image_add_box]
        refine Box.farApart ?_
        simp only [Prod.smul_fst, nsmul_eq_mul]
        push_cast
        omega)
    have h := dz2Detector_pass_zero.seq hfly
    rw [Rule.evolve_add, dz2Detector_evolve_sixteen, add_comm 16 n] at *
    refine (Nat.cast_zero (R := ℤ) ▸ h).mono fun i hi => ?_
    split_ifs with hi16
    · rintro c ⟨h1, h2, h3, h4⟩
      exact ⟨by omega, by push_cast; omega, h3, by push_cast; omega⟩
    · refine Set.union_subset ?_ ?_
      · rintro _ ⟨c, ⟨h1, h2, h3, h4⟩, rfl⟩
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul] <;>
          push_cast <;> omega
      · rintro c ⟨h1, h2, h3, h4⟩
        refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> omega
  · have h := (reaction_flight_box' (by norm_num) dz2Detector_evolve_four
      dz2Detector_subset_box (n + 16)).par
      ((counter_isStillLife j).reaction_box (counter_subset_box j) (n + 16))
      (fun i _ => by
        rw [image_add_box]
        refine Box.farApart ?_
        simp only [Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul]
        push_cast
        omega)
    refine h.mono fun i _ => Set.union_subset ?_ ?_
    · rintro _ ⟨c, ⟨h1, h2, h3, h4⟩, rfl⟩
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, nsmul_eq_mul] <;>
        push_cast <;> omega
    · rintro c ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast at * <;> omega

/-! ### The restore glider -/

/-- The restore glider of `DZ2`, flying up and to the right (world line `(NE, -20, 54)` of
`R-27`, at generation `86`).
```
OOO
..O
.O.
```
-/
def dz2Restore : Finset Cell := ofRows 8 12 [7, 4, 2]

/-- The restore glider moves one cell up and to the right every four generations. -/
theorem dz2Restore_evolve_four :
    conway.evolve 4 dz2Restore = translate (1, -1) dz2Restore := by
  rw [dz2Restore, translate_ofRows]
  life_cert

/-- During its first four generations the restore glider stays in a box. -/
theorem dz2Restore_subset_box (r : ℕ) (hr : r < 4) :
    (conway.evolve r dz2Restore : Set Cell) ⊆ Box 8 11 11 14 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- **Certificate**: the restore glider turns `dz2DetectorBlock` back into the block at position
`-1`, in nine generations. -/
theorem dz2Restore_zero :
    Reaction (dz2DetectorBlock ∪ dz2Restore) (counter (-1)) 9 (fun _ => Box 6 11 8 14) := by
  rw [show dz2DetectorBlock ∪ dz2Restore = ofRows 7 8 [3, 3, 0, 0, 14, 8, 4] by
      rw [dz2DetectorBlock, dz2Restore, ofRows_eq_padRows' 7 8 8 12 4 1 _
        (by norm_num) (by norm_num), ← ofRows_orRows]
      rfl,
    show counter (-1) = ofRows 6 10 [3, 3] by rw [counter]; norm_num]
  life_reaction

/-! ### The increment from position `-1` -/

/-- **Certificate**: the pushing salvo of `REG1` at position `-1`, 53 generations. -/
theorem reg1Inc_neg_one :
    Reaction (reg1IncLocal ∪ counter (-1)) (counter (1 + -1)) 53
      (fun _ => Box (-11) 14 (-13) 14) := by
  rw [show reg1IncLocal ∪ counter (-1) =
      ofRows (-11) (-13) [128, 256, 448, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 8199, 49152, 24576, 0,
        0, 0, 0, 0, 0, 393216, 393216] by
        rw [reg1IncLocal, counter, ofRows_eq_padRows' (-11) (-13) (7 + -1) (11 + -1) 23 17 _
          (by norm_num) (by norm_num), ← ofRows_orRows]
        rfl,
    show counter (1 + -1) = ofRows 7 11 [3, 3] by rw [counter]; norm_num]
  life_reaction

set_option maxRecDepth 100000 in
/-- **Increment from position `-1`.** One control glider into the increment input of `REG1`
moves the block from position `-1` to position `0`; the register is left in its cycle and
nothing else remains. This is the last step of the zero case of `DZ2`. -/
theorem reg1_increment_neg_one :
    conway.evolve (3570 + 53) (reg1 ∪ reg1IncControl ∪ reg1Block (-1)) =
      conway.evolve 53 reg1 ∪ reg1Block 0 := by
  have h := reg1_operation (-1) le_rfl reg1Inc_reaction (fun c hc => hc.2.2.2) reg1IncSalvo_eq
    (reg1Inc_neg_one.mono (F' := fun _ => {c : Cell | -11 ≤ c.1 ∧ -13 ≤ c.2})
      fun _ _ c hc => ⟨hc.1, hc.2.2.1⟩) (by norm_num)
  rwa [show (1 : ℤ) + -1 = 0 by norm_num] at h

end LeanTheory.Life
