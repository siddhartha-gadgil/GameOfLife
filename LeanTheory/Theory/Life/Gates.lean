/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Boxes

/-!
# Terminated streams, blocked streams and a gate

The first components of the machine design D1 (research notes `N-10`, `N-15`), built from
Gosper guns, an eater and gliders only. All of them were found by the project's own search
(`scripts/life_gates`, report `notes/research/reports/R-20-gun-gates.md`); here they are
certified.

* `terminatedGun`: the Gosper gun with an eater on its stream. It is an oscillator of period
  exactly 30 (`terminatedGun_isOscillator`): every glider is absorbed and nothing escapes.
* `gunB`: a mirror image of the gun, firing down and to the left. `blockedStream`: the two guns
  with their streams, which cross and annihilate each other. It is reached from the two bare guns
  in 90 generations (`blockedStream_start`), it is an oscillator of period exactly 30
  (`blockedStream_isOscillator`), and it consists of the two guns, three gliders of the first
  stream and three of the second (`blockedStream_eq_union`).
* `gate`: a control glider on the right lane and at the right time removes one glider of the
  second stream; the glider of the first stream that it would have destroyed escapes, and the
  assembly is back in its cycle:
  `conway.evolve 90 (blockedStream ∪ gateControl) = blockedStream ∪ gateOutput`.
  The control glider is a translate of the catalogue glider (`gateControl_eq_translate`) and the
  released glider is the glider of the gun at age 90 (`gateOutput_eq_evolve`), so the output is
  timed by the gun, not by the input.
* `glider_pair_annihilate`: the collision that keeps the streams blocked, in isolation.
* `blockedStream_reaction`, `gate_reaction`: the resting assembly and the gate as reactions with
  rectangular footprints (`Theory/Life/Boxes`), ready for composition with other components.

**Sanity.** `gate_wrong_lane_ne` (a control glider one lane off does not give the output of the
gate), `blockedStream_isOscillator` (without a control glider nothing is released),
`not_isStillLife_terminatedGun`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### A terminated stream -/

/-- The Gosper gun with an eater on its stream: `gosperGun ∪ translate (25, 11) eater1`. -/
def terminatedGun : Finset Cell :=
  ofRows 0 0
    [16777216, 20971520, 51542765568, 51542788096, 3212291, 21185539, 16843776, 34816, 12288, 0,
     0, 100663296, 167772160, 134217728, 402653184]

set_option maxRecDepth 8192 in
/-- The terminated gun is the gun together with a translate of the catalogue eater. -/
theorem terminatedGun_eq_union :
    terminatedGun = gosperGun ∪ translate (25, 11) Pattern.eater1 := by
  rw [Pattern.eater1, translate_ofRows, gosperGun, ofRows_eq_padRows (0 + 25) (0 + 11) 11 25 _
    (by norm_num) (by norm_num), ← ofRows_orRows]
  rfl

/-- **The terminated gun is an oscillator of period exactly 30**: the eater absorbs every
glider, and the configuration does not return earlier. -/
theorem terminatedGun_isOscillator : IsOscillator terminatedGun 30 := by
  refine ⟨by norm_num, by life_cert, fun k hk0 hk => ?_⟩
  interval_cases k <;> (life_eval; exact ofRows_ne rfl rfl (by simp))

/-! ### Two guns blocking each other -/

/-- A mirror image of the Gosper gun, placed to the right of `gosperGun`; it fires gliders
travelling down and to the left. -/
def gunB : Finset Cell :=
  ofRows 55 1 [2048, 10240, 12632067, 17874947, 51573735424, 51576055808, 34080768, 17825792,
    12582912]

/-- The two guns with their streams in the periodic state: three gliders of each stream are in
flight and the leading pair is about to collide. -/
def blockedStream : Finset Cell :=
  ofRows 0 0
    [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
     644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920,
     1227889072522402593802240, 642241841670271749074944, 453347182355485948903424,
     147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120,
     1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944,
     4505248894812160, 3378524354248704, 6755399441055744]

set_option maxRecDepth 8192 in
/-- **Start**: the two bare guns reach the periodic state in 90 generations. -/
theorem blockedStream_start : conway.evolve 90 (gosperGun ∪ gunB) = blockedStream := by
  have h : gosperGun ∪ gunB = ofRows 0 0
      [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
       644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920,
       1227889072522402593802240, 642241841670271749074944, 453347182355485940514816] := by
    rw [gosperGun, gunB, ofRows_eq_padRows 55 1 1 55 _ rfl rfl, ← ofRows_orRows]
    rfl
  rw [h]
  life_cert

/-- **The blocked stream is an oscillator of period exactly 30**: the two streams annihilate
each other completely, forever, and nothing escapes. -/
theorem blockedStream_isOscillator : IsOscillator blockedStream 30 := by
  refine ⟨by norm_num, by life_cert, fun k hk0 hk => ?_⟩
  interval_cases k <;> (life_eval; exact ofRows_ne rfl rfl (by simp))

set_option maxRecDepth 8192 in
/-- The periodic state consists of the two guns, three gliders of the first stream (the glider
of the gun at ages 0, 30 and 60) and three gliders of the second stream. -/
theorem blockedStream_eq_union :
    blockedStream = gosperGun ∪ gunB ∪
      (gunGlider ∪ ofRows 30 17 [5, 6, 2] ∪ ofRows 38 24 [1, 6, 3]) ∪
      (ofRows 65 10 [4, 3, 6] ∪ ofRows 58 18 [5, 3, 2] ∪ ofRows 50 25 [4, 3, 6]) := by
  rw [gosperGun, gunB, gunGlider, ofRows_eq_padRows 55 1 1 55 _ rfl rfl,
    ofRows_eq_padRows 23 9 9 23 _ rfl rfl, ofRows_eq_padRows 30 17 17 30 _ rfl rfl,
    ofRows_eq_padRows 38 24 24 38 _ rfl rfl, ofRows_eq_padRows 65 10 10 65 _ rfl rfl,
    ofRows_eq_padRows 58 18 18 58 _ rfl rfl, ofRows_eq_padRows 50 25 25 50 _ rfl rfl]
  simp only [← ofRows_orRows]
  rfl

/-- **The collision that blocks the streams**: the leading gliders of the two streams, alone,
annihilate each other in 21 generations. -/
theorem glider_pair_annihilate :
    conway.evolve 21 (ofRows 38 24 [1, 6, 3] ∪ ofRows 50 25 [4, 3, 6]) = ∅ := by
  have h : ofRows 38 24 [1, 6, 3] ∪ ofRows 50 25 [4, 3, 6] =
      ofRows 38 24 (orRows [1, 6, 3] (padRows 1 12 [4, 3, 6])) := by
    rw [ofRows_orRows, ofRows_padRows]
    norm_num
  rw [h]
  life_cert

/-! ### The gate -/

/-- The control glider of the gate. -/
def gateControl : Finset Cell := ofRows 47 6 [2, 4, 7]

/-- The glider released by the gate. -/
def gateOutput : Finset Cell := ofRows 45 32 [5, 6, 2]

/-- The control glider is the catalogue glider, translated. -/
theorem gateControl_eq_translate : gateControl = translate (47, 6) Pattern.glider := by
  rw [Pattern.glider, translate_ofRows, gateControl, zero_add, zero_add]

/-- The released glider is the glider of the gun at age 90: its timing is that of the gun. -/
theorem gateOutput_eq_evolve : gateOutput = conway.evolve 90 gunGlider := by
  symm
  rw [gateOutput]
  life_cert

set_option maxRecDepth 8192 in
/-- The blocked stream with the control glider, as one window. -/
theorem blockedStream_union_gateControl :
    blockedStream ∪ gateControl = ofRows 0 0
    [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
     644012837187738926121987, 1858139645101047596242387971, 1858223245745471122902680576,
     1227889073085352547223552, 642241842655434167562240, 453347182355485948903424,
     147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0,
     5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0,
     274877906944, 4505248894812160, 3378524354248704, 6755399441055744] := by
  rw [blockedStream, gateControl, ofRows_eq_padRows 47 6 6 47 _ rfl rfl, ← ofRows_orRows]
  rfl

set_option maxRecDepth 8192 in
/-- **The gate.** A control glider arriving on the right lane at the right time is destroyed
together with one glider of the second stream; the glider of the first stream that would have
been annihilated escapes, and after 90 generations the two guns are back in their cycle. -/
theorem gate :
    conway.evolve 90 (blockedStream ∪ gateControl) = blockedStream ∪ gateOutput := by
  have he : blockedStream ∪ gateOutput = ofRows 0 0
      [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
       644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920,
       1227889072522402593802240, 642241841670271749074944, 453347182355485948903424,
       147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0,
       5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0,
       274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0,
       175921860444160, 211106232532992, 70368744177664] := by
    rw [blockedStream, gateOutput, ofRows_eq_padRows 45 32 32 45 _ rfl rfl, ← ofRows_orRows]
    rfl
  rw [blockedStream_union_gateControl, he]
  life_cert

/-! ### The components as reactions with footprints -/

/-- During its cycle the blocked stream stays in the box `0 ≤ x ≤ 90`, `0 ≤ y ≤ 32`. -/
theorem blockedStream_subset_box (r : ℕ) (hr : r < 30) :
    (conway.evolve r blockedStream : Set Cell) ⊆ Box 0 90 0 32 := by
  interval_cases r <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-- The blocked stream at rest, as a reaction of any number of periods with a box footprint. -/
theorem blockedStream_reaction (k : ℕ) :
    Reaction blockedStream blockedStream (k * 30) (fun _ => Box 0 90 0 32) :=
  blockedStream_isOscillator.reaction_box blockedStream_subset_box k

/-- **The gate as a reaction**: during its 90 generations the gate with its control glider and
the released glider stays in the box `0 ≤ x ≤ 90`, `0 ≤ y ≤ 34`. -/
theorem gate_reaction :
    Reaction (blockedStream ∪ gateControl) (blockedStream ∪ gateOutput) 90
      (fun _ => Box 0 90 0 34) := by
  refine ⟨gate, fun i hi => ?_⟩
  rw [blockedStream_union_gateControl]
  interval_cases i <;> (life_eval; exact coe_ofRows_subset_box rfl)

/-! ### Sanity -/

set_option maxRecDepth 8192 in
/-- **Sanity** (rejected fixture): a control glider one lane to the right does not produce the
output of the gate. -/
theorem gate_wrong_lane_ne :
    conway.evolve 90 (ofRows 0 0 (orRows
        [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
         644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920,
         1227889072522402593802240, 642241841670271749074944, 453347182355485948903424,
         147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0,
         5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0,
         274877906944, 4505248894812160, 3378524354248704, 6755399441055744]
        (padRows 6 48 [2, 4, 7]))) ≠ blockedStream ∪ gateOutput := by
  have he : blockedStream ∪ gateOutput = ofRows 0 0
      [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
       644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920,
       1227889072522402593802240, 642241841670271749074944, 453347182355485948903424,
       147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0,
       5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0,
       274877906944, 4505248894812160, 3378524354248704, 6755399441055744, 0, 0, 0, 0,
       175921860444160, 211106232532992, 70368744177664] := by
    rw [blockedStream, gateOutput, ofRows_eq_padRows 45 32 32 45 _ rfl rfl, ← ofRows_orRows]
    rfl
  rw [he]
  life_eval
  exact ofRows_ne rfl rfl (by simp)

/-- **Sanity**: the terminated gun is not a still life. -/
theorem not_isStillLife_terminatedGun : ¬ IsStillLife terminatedGun := fun h =>
  terminatedGun_isOscillator.2.2 1 (by norm_num) (by norm_num) h.2

end LeanTheory.Life
