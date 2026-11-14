/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ContinueDecrement
public import LeanTheory.Theory.Life.Invariant

/-!
# The decision part of the zero test

The register of the machine design D1 is the block `counter k` (research notes `N-11`, `N-15`).
This module certifies the part of the zero test that turns the position of the block into a
glider on one of two lanes. The design was found by the project's own search
(`scripts/life_machine/z2_zero_logic.py`, report
`notes/research/reports/R-22-push-and-continue.md`, section 4).

* `zeroTestInput`: three test gliders travelling down and to the left (the three-glider test of
  `zeroTestSalvo_hit`) and a detector glider travelling down and to the right, parallel to the
  register.
* `zeroEaters`: two eaters that absorb the test gliders that pass the register.
* `zeroTest_decision`: for **every** position `k` of the block,

  `conway.evolve 196 (zeroTestInput ∪ zeroEaters ∪ counter k) =
     zeroEaters ∪ counter k ∪ (if k = 0 then zOut else nzOut)`.

  If the register is zero the test gliders are destroyed by the block, which is left in place,
  and the detector flies on: it is the output `zOut` (`zOut_eq`: the detector moved by 49 cells
  along its lane). Otherwise the test gliders pass the block, the third one kicks the detector
  back as the glider `nzOut` travelling up and to the left, and the eaters absorb the other two.
  In both cases the block is unchanged.

Proof: certificates for `k = 0` and `k = 1`; for `k ≥ 2` one certificate of the evolution
without a block, together with `zeroTest_far` (certified by `life_invariant`): during these 196
generations every live cell is off the register's lane or above its anti-diagonals, hence at
distance more than two from the block, so the block does not take part.

Not covered: producing the four input gliders from one control glider.

**Sanity.** `zOut_eq`, `nzOut_evolve_four` (the output `NZ` is a glider travelling up and to the
left), `zOut_ne_nzOut` (the two outcomes differ).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- The three test gliders and the detector glider. -/
def zeroTestInput : Finset Cell :=
  ofRows (-27) (-6)
    [5, 6, 2, 0, 1099511627776, 5497558138880, 3307124817920, 4294967296, 30064771072, 0, 0, 0,
     17179869184, 8589934592, 60129542144]

/-- Two eaters absorbing the test gliders that pass the register. -/
def zeroEaters : Finset Cell := ofRows (-46) 51 [12, 8, 7, 1, 0, 0, 0, 12, 8, 7, 1]

/-- The output when the register is zero: the detector glider, flying on. -/
def zOut : Finset Cell := ofRows 22 43 [5, 6, 2]

/-- The output when the register is not zero: the detector glider kicked back. -/
def nzOut : Finset Cell := ofRows (-35) (-14) [2, 3, 5]

/-- The output `Z` is the detector glider after 196 generations. -/
theorem zOut_eq : conway.evolve 196 (ofRows (-27) (-6) [5, 6, 2]) = zOut := by
  rw [zOut]
  life_cert

/-- The output `NZ` is a glider travelling up and to the left. -/
theorem nzOut_evolve_four : conway.evolve 4 nzOut = translate (-1, -1) nzOut := by
  rw [nzOut, translate_ofRows]
  life_cert

/-- The two outcomes differ. -/
theorem zOut_ne_nzOut : zOut ≠ nzOut := ofRows_ne rfl rfl (by simp)

set_option maxRecDepth 100000 in
/-- The input with the eaters, as one window. -/
theorem zeroTestInput_union_eaters :
    zeroTestInput ∪ zeroEaters = ofRows (-46) (-6)
      [2621440, 3145728, 1048576, 0, 576460752303423488, 2882303761517117440,
       1733885856537640960, 2251799813685248, 15762598695796736, 0, 0, 0, 9007199254740992,
       4503599627370496, 31525197391593472, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 8, 7, 1, 0, 0,
       0, 12, 8, 7, 1] := by
  rw [zeroTestInput, zeroEaters, ofRows_eq_padRows' (-46) (-6) (-27) (-6) 0 19 _ (by norm_num)
    (by norm_num), ofRows_eq_padRows' (-46) (-6) (-46) 51 57 0 _ (by norm_num) (by norm_num),
    ← ofRows_orRows]
  rfl

/-- Union of a window with a padded window, as a rewriting rule. -/
theorem ofRows_union_padRows (x y : ℤ) (A : List ℕ) (pre t : ℕ) (B : List ℕ) :
    ofRows x y A ∪ ofRows (x + t) (y + pre) B = ofRows x y (orRows A (padRows pre t B)) := by
  rw [ofRows_orRows, ofRows_padRows]

set_option maxRecDepth 100000 in
/-- **Certificate**: without a block the test gliders pass, the detector is kicked back, and the
eaters absorb the other two test gliders. -/
theorem zeroTest_noBlock :
    conway.evolve 196 (zeroTestInput ∪ zeroEaters) = zeroEaters ∪ nzOut := by
  rw [zeroTestInput_union_eaters, zeroEaters, nzOut,
    show ofRows (-46) 51 [12, 8, 7, 1, 0, 0, 0, 12, 8, 7, 1] =
      ofRows (-46) (-14) (padRows 65 0 [12, 8, 7, 1, 0, 0, 0, 12, 8, 7, 1]) by
        rw [ofRows_padRows]; norm_num,
    show ofRows (-35) (-14) [2, 3, 5] = ofRows (-46) (-14) (padRows 0 11 [2, 3, 5]) by
        rw [ofRows_padRows]; norm_num, ← ofRows_orRows]
  life_cert

set_option maxRecDepth 100000 in
/-- **Certificate**: with the register at zero, the block destroys the test gliders, stays in
place, and the detector flies on. -/
theorem zeroTest_zero :
    conway.evolve 196 (zeroTestInput ∪ zeroEaters ∪ counter 0) =
      zeroEaters ∪ counter 0 ∪ zOut := by
  rw [zeroTestInput_union_eaters, zeroEaters, counter, zOut,
    show ofRows (7 + 0) (11 + 0) [3, 3] = ofRows (-46) (-6) (padRows 17 53 [3, 3]) by
        rw [ofRows_padRows]; norm_num, ← ofRows_orRows,
    show ofRows (-46) 51 [12, 8, 7, 1, 0, 0, 0, 12, 8, 7, 1] =
      ofRows (-46) 11 (padRows 40 0 [12, 8, 7, 1, 0, 0, 0, 12, 8, 7, 1]) by
        rw [ofRows_padRows]; norm_num,
    show ofRows (-46) (-6) (padRows 17 53 [3, 3]) = ofRows (-46) 11 (padRows 0 53 [3, 3]) by
        rw [ofRows_padRows, ofRows_padRows]; norm_num,
    show ofRows 22 43 [5, 6, 2] = ofRows (-46) 11 (padRows 32 68 [5, 6, 2]) by
        rw [ofRows_padRows]; norm_num, ← ofRows_orRows, ← ofRows_orRows]
  life_cert

set_option maxRecDepth 100000 in
/-- **Certificate**: with the register at one, the test gliders pass the block (one of them at
distance two) and the outcome is `NZ`. -/
theorem zeroTest_one :
    conway.evolve 196 (zeroTestInput ∪ zeroEaters ∪ counter 1) =
      zeroEaters ∪ counter 1 ∪ nzOut := by
  rw [zeroTestInput_union_eaters, zeroEaters, counter, nzOut,
    show ofRows (7 + 1) (11 + 1) [3, 3] = ofRows (-46) (-6) (padRows 18 54 [3, 3]) by
        rw [ofRows_padRows]; norm_num, ← ofRows_orRows,
    show ofRows (-46) 51 [12, 8, 7, 1, 0, 0, 0, 12, 8, 7, 1] =
      ofRows (-46) (-14) (padRows 65 0 [12, 8, 7, 1, 0, 0, 0, 12, 8, 7, 1]) by
        rw [ofRows_padRows]; norm_num,
    show ofRows (-46) (-6) (padRows 18 54 [3, 3]) = ofRows (-46) (-14) (padRows 26 54 [3, 3]) by
        rw [ofRows_padRows, ofRows_padRows]; norm_num,
    show ofRows (-35) (-14) [2, 3, 5] = ofRows (-46) (-14) (padRows 0 11 [2, 3, 5]) by
        rw [ofRows_padRows]; norm_num, ← ofRows_orRows, ← ofRows_orRows]
  life_cert

/-- The cells that are far from the register at positions `k ≥ 2`: off its lane, or above its
anti-diagonals. -/
def zeroFar (x y : ℤ) : Bool := decide (x - y ≤ -10) || decide (2 ≤ x - y) || decide (x + y ≤ 17)

set_option maxRecDepth 100000 in
/-- **Certificate**: during the 196 generations of the test without a block, every live cell is
far from the register at positions `k ≥ 2`. -/
theorem zeroTest_far :
    ∀ i ≤ 196, ∀ c ∈ conway.evolve i (zeroTestInput ∪ zeroEaters), zeroFar c.1 c.2 = true := by
  rw [zeroTestInput_union_eaters]
  life_invariant

/-- **Far blocks do not take part**: for `k ≥ 2` the test evolves as without a block. -/
theorem zeroTest_far_block (k : ℕ) (hk : 2 ≤ k) :
    conway.evolve 196 (zeroTestInput ∪ zeroEaters ∪ counter k) =
      zeroEaters ∪ counter k ∪ nzOut := by
  have hT : ∀ i, conway.evolve i (counter k) = counter k := (counter_isStillLife k).evolve
  have hsep : ∀ i < 196, Sep 2 (conway.evolve i (zeroTestInput ∪ zeroEaters))
      (conway.evolve i (counter k)) := by
    intro i hi s hs t ht hn
    rw [hT] at ht
    have hf := zeroTest_far i hi.le s hs
    obtain ⟨t1, t2, t3, t4⟩ := counter_subset_box k (mem_coe.2 ht)
    obtain ⟨n1, n2, n3, n4⟩ := hn
    simp only [zeroFar, Bool.or_eq_true, decide_eq_true_eq] at hf
    push_cast at *
    omega
  rw [conway.evolve_union_of_forall_sep hsep, zeroTest_noBlock, hT]
  ext c
  simp only [mem_union]
  tauto

/-- **The decision part of the zero test.** For every position `k` of the register block, the
four input gliders and the eaters evolve in 196 generations into the eaters, the unchanged
block, and one output glider: `zOut` if the register is zero, `nzOut` otherwise. -/
theorem zeroTest_decision (k : ℕ) :
    conway.evolve 196 (zeroTestInput ∪ zeroEaters ∪ counter k) =
      zeroEaters ∪ counter k ∪ (if k = 0 then zOut else nzOut) := by
  rcases k with _ | _ | k
  · simpa using zeroTest_zero
  · simpa using zeroTest_one
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact zeroTest_far_block (k + 2) (by omega)

end LeanTheory.Life
