/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepThreads

/-!
# The two threads of an `inc` activation are far apart

Research note `N-22`. The field `threads` of `IncSep` (`ActivationIncStep`). The moving parts of
the two threads (`isep2CMov`, `isep2IMov`) are far apart at every generation (`isep2_cross`):

* **until the continue enters the window of its fourth corner** (`meetT - 20`) it is inside the
  region `isep2SetS` (its source column, its `OUT` track, its hairpin column and its `BACK` track
  in sub-band `i + 1`, with the extended relay boxes of its first four corners); the increment
  thread is, at every generation, inside the region `isep2SetJ` (the source column, `OUT` track,
  hairpin column and `BACK` track of the INC link, which run inside the loop of the continue, and
  everything right of the column of its entry copy or below sub-band `i + 1`); the two regions
  are `≥ 5` apart in `u` or `v` (`isep2_SJ_far`);
* **afterwards** (`isep2_m4C`: `≥ 966` generations after the arrival at the INC gate, so after
  the start of the increment) the continue is in the slabs of the units (`u ≤ A_{i+1} + 96 + 29
  t_c`) and the increment thread in module `r` (`u ≥ U_r - 760`).

`isep2_threads`: the field `threads` (the pieces of the threads are separated, `isep2_static`;
each moving part is far from the pieces of the other thread, `isep2_CMov_far`,
`isep2_IMov_far`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-! ### Two regions of the band -/

/-- The region of the continue before its fourth corner: the source column `cc` (above the `OUT`
track `O0`), the `OUT` track, the hairpin column `Hc` and the `BACK` track `B9` up to the column
`dC` of its entry copy. -/
def isep2SetS (cc O0 Hc B9 dC : ℤ) : Set Cell :=
  {x | (cc - 29 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cc + 29 ∧ x.1 + x.2 ≤ O0 + 27) ∨
    (Hc - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cc + 16 ∧ O0 - 18 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ O0 + 31) ∨
    (Hc - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ Hc + 28 ∧ O0 - 14 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B9 + 26) ∨
    (Hc - 17 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ dC + 25 ∧ B9 - 27 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B9 + 26)}

/-- The region of the increment thread: the source column `cl`, the `OUT` track `O1`, the
hairpin column `Hl` and the `BACK` track `B8` of the INC link, everything right of `dI - 20`
(`dI` the column of its entry copy) and everything below `V7`. -/
def isep2SetJ (cl O1 Hl B8 dI V7 : ℤ) : Set Cell :=
  {x | (cl - 29 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cl + 16 ∧ x.1 + x.2 ≤ O1 + 27) ∨
    (Hl - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cl + 16 ∧ O1 - 18 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ O1 + 31) ∨
    (Hl - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ Hl + 28 ∧ O1 - 14 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B8 + 26) ∨
    (Hl - 17 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ dI + 25 ∧ B8 - 27 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B8 + 26) ∨
    dI - 20 ≤ x.1 - x.2 ∨ V7 ≤ x.1 + x.2}

/-- **The two regions are far apart**, under the relations of the layout between their
parameters. -/
theorem isep2_SJ_far {cc O0 Hc B9 dC cl O1 Hl B8 dI V7 : ℤ} (h1 : cl = cc + 89)
    (h2 : O1 = O0 + 61) (h3 : B9 = O0 + 558) (h4 : B8 = O0 + 495) (h5 : Hc + 63 ≤ Hl)
    (h6 : Hc + 33 ≤ cc) (h7 : dC + 50 ≤ dI) (h8 : cc + 54 ≤ dI) (h9 : B9 + 31 ≤ V7) :
    FarApart 2 (isep2SetS cc O0 Hc B9 dC) (isep2SetJ cl O1 Hl B8 dI V7) := by
  rintro x hx y hy ⟨n1, n2, n3, n4⟩
  simp only [isep2SetS, isep2SetJ, Set.mem_ofPred_eq] at hx hy
  push_cast at n1 n2 n3 n4
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy | hy | hy <;> omega

/-! ### Routes inside a set, leg by leg -/

/-- All cells of the `uv`-rectangle `[u1, u2] × [v1, v2]` lie in `Z`. -/
def isep2InR (Z : Set Cell) (u1 u2 v1 v2 : ℤ) : Prop :=
  ∀ x : Cell, u1 ≤ x.1 - x.2 → x.1 - x.2 ≤ u2 → v1 ≤ x.1 + x.2 → x.1 + x.2 ≤ v2 → x ∈ Z

/-- All cells of the `uv`-half-strip `[u1, u2] × (-∞, v2]` lie in `Z`. -/
def isep2InH (Z : Set Cell) (u1 u2 v2 : ℤ) : Prop :=
  ∀ x : Cell, u1 ≤ x.1 - x.2 → x.1 - x.2 ≤ u2 → x.1 + x.2 ≤ v2 → x ∈ Z

/-- The first corner of an up-going or down-going link (image `3`, on the `OUT` track). -/
def isep2U1 (p : Program) (b s c : ℤ) : Corner := ⟨3, c, trackOut p b s c, .band b s false⟩

/-- The second corner (image `7`, hairpin on the `OUT` track). -/
def isep2U2 (p : Program) (b s c H : ℤ) : Corner := ⟨7, H, trackOut p b s c, .band b s true⟩

/-- The third corner (image `4`, hairpin on the `BACK` track). -/
def isep2U3 (p : Program) (b s c H : ℤ) : Corner :=
  ⟨4, H, trackBack p b s c, .band b (9 - s) true⟩

/-- The fourth corner of an up-going link (image `6`, column of the entry copy). -/
def isep2U4 (p : Program) (b s c : ℤ) (a : ℕ) (t : ℤ) : Corner :=
  ⟨6, destU p a t, trackBack p b s c, .band b (9 - s) false⟩

/-- The input corner of entry copy `t` of unit `a` (image `1`). -/
def isep2U5 (p : Program) (a : ℕ) (t : ℤ) : Corner := ⟨1, destU p a t, destV p t, .slab a t⟩

/-- The corners of an up-going link. -/
theorem isep2_upCorners_eq (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) :
    upCorners p b s c H a t = [isep2U1 p b s c, isep2U2 p b s c H, isep2U3 p b s c H,
      isep2U4 p b s c a t, isep2U5 p a t] := rfl

/-- **An up-going link inside a set, up to the window of its fourth corner** (the source column
`c`, the `OUT` track, the hairpin column `H`, the `BACK` track up to the column of the entry
copy, with the extended relay boxes of the first four corners). -/
theorem isep2_up_sub4 (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) {g : WL} {T : ℕ}
    (htim : RouteTimedX g (upCorners p b s c H a t) T)
    (hlin : RouteLines g (upCorners p b s c H a t))
    (hH : (H - c) % 2 = 0) (hd : (destU p a t - c) % 2 = 0) {Z : Set Cell}
    (zs : isep2InH Z (c - 4) (c + 4) (trackOut p b s c - 7))
    (z1 : isep2InR Z (c - 29) (c + 16) (trackOut p b s c - 18) (trackOut p b s c + 27))
    (z12 : isep2InR Z (H + 9) (c - 9) (trackOut p b s c - 2) (trackOut p b s c + 6))
    (z2 : isep2InR Z (H - 25) (H + 20) (trackOut p b s c - 14) (trackOut p b s c + 31))
    (z23 : isep2InR Z (H - 4) (H + 4) (trackOut p b s c + 11) (trackBack p b s c - 7))
    (z3 : isep2InR Z (H - 17) (H + 28) (trackBack p b s c - 19) (trackBack p b s c + 26))
    (z34 : isep2InR Z (H + 9) (destU p a t - 9) (trackBack p b s c - 2)
      (trackBack p b s c + 6))
    (z4 : isep2InR Z (destU p a t - 20) (destU p a t + 25) (trackBack p b s c - 27)
      (trackBack p b s c + 18)) :
    ∀ j : ℕ, (T : ℤ) + j ≤ meetT (route g [isep2U1 p b s c, isep2U2 p b s c H,
        isep2U3 p b s c H]).2 (isep2U4 p b s c a t) - 20 →
      routeFootX g (upCorners p b s c H a t) T j ⊆ Z := by
  intro j hj
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  rw [isep2_upCorners_eq] at htim hlin ⊢
  have hpre := isep2_rfoot_prefix [isep2U1 p b s c, isep2U2 p b s c H, isep2U3 p b s c H]
    (isep2U4 p b s c a t) [isep2U5 p a t] g T j htim hj
  change routeFootX g ([isep2U1 p b s c, isep2U2 p b s c H, isep2U3 p b s c H] ++
    isep2U4 p b s c a t :: [isep2U5 p a t]) T j ⊆ Z
  rw [hpre]
  obtain ⟨t1, t2, t3, t4, -⟩ := htim
  obtain ⟨l1, l2, l3, l4, -⟩ := hlin
  have e3 : (route g [isep2U1 p b s c, isep2U2 p b s c H, isep2U3 p b s c H]).2 =
      (reflect (reflect (reflect g (isep2U1 p b s c)).2 (isep2U2 p b s c H)).2
        (isep2U3 p b s c H)).2 := rfl
  rw [e3] at hj
  refine isep2_rfoot_sub [isep2U2 p b s c H, isep2U3 p b s c H, isep2U4 p b s c a t]
    (isep2U1 p b s c) g T ⟨t1, t2, t3, t4, trivial⟩ ⟨l1, l2, l3, l4, trivial⟩ ?_ ?_ ?_ ?_ j ?_
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;>
      refine ⟨by simp [isep2U1, isep2U2, isep2U3, isep2U4], ?_⟩ <;>
      simp only [CPar, rfCU, rfCV, isep2U1, isep2U2, isep2U3, isep2U4] <;> omega
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl <;> intro x hx
    · have := isep2_rx_uv (by simp [isep2U1])
        (by simp only [CPar, rfCU, rfCV, isep2U1]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U1] at this
      exact z1 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2U2])
        (by simp only [CPar, rfCU, rfCV, isep2U2]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U2] at this
      exact z2 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2U3])
        (by simp only [CPar, rfCU, rfCV, isep2U3]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U3] at this
      exact z3 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2U4])
        (by simp only [CPar, rfCU, rfCV, isep2U4]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U4] at this
      exact z4 x (by omega) (by omega) (by omega) (by omega)
  · refine ⟨fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_,
      fun cu cv r1 r2 x hx => ?_, trivial⟩ <;>
      simp only [Ray, outD, behindIn, isep2U1, isep2U2, isep2U3, isep2U4] at r1 r2 <;>
      obtain ⟨x1, x2, x3, x4⟩ := hx
    · exact z12 x (by omega) (by omega) (by omega) (by omega)
    · exact z23 x (by omega) (by omega) (by omega) (by omega)
    · exact z34 x (by omega) (by omega) (by omega) (by omega)
  · intro t' _ ht'
    refine isep2_start_of_ray l1 (by simp [isep2U1])
      (by simp only [CPar, rfCU, rfCV, isep2U1]; omega) (fun cu cv r x hx => ?_) t' (by omega)
    simp only [Ray, behindIn, isep2U1] at r
    obtain ⟨x1, x2, x3, x4⟩ := hx
    exact zs x (by omega) (by omega) (by omega)
  · change T + j ≤ (meetT (reflect (reflect (reflect g (isep2U1 p b s c)).2
      (isep2U2 p b s c H)).2 (isep2U3 p b s c H)).2 (isep2U4 p b s c a t)).toNat + 40
    omega

/-- **A whole up-going link inside a set** (with the column of the entry copy up to the input
corner and the extended relay boxes of the last two corners). -/
theorem isep2_up_sub5 (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) {g : WL} {T : ℕ}
    (htim : RouteTimedX g (upCorners p b s c H a t) T)
    (hlin : RouteLines g (upCorners p b s c H a t))
    (hH : (H - c) % 2 = 0) (hd : (destU p a t - c) % 2 = 0)
    (hdv : (destU p a t + destV p t) % 2 = 1) {Z : Set Cell}
    (zs : isep2InH Z (c - 4) (c + 4) (trackOut p b s c - 7))
    (z1 : isep2InR Z (c - 29) (c + 16) (trackOut p b s c - 18) (trackOut p b s c + 27))
    (z12 : isep2InR Z (H + 9) (c - 9) (trackOut p b s c - 2) (trackOut p b s c + 6))
    (z2 : isep2InR Z (H - 25) (H + 20) (trackOut p b s c - 14) (trackOut p b s c + 31))
    (z23 : isep2InR Z (H - 4) (H + 4) (trackOut p b s c + 11) (trackBack p b s c - 7))
    (z3 : isep2InR Z (H - 17) (H + 28) (trackBack p b s c - 19) (trackBack p b s c + 26))
    (z34 : isep2InR Z (H + 9) (destU p a t - 9) (trackBack p b s c - 2)
      (trackBack p b s c + 6))
    (z4 : isep2InR Z (destU p a t - 20) (destU p a t + 25) (trackBack p b s c - 27)
      (trackBack p b s c + 18))
    (z45 : isep2InR Z (destU p a t - 4) (destU p a t + 4) (destV p t + 11)
      (trackBack p b s c - 7))
    (z5 : isep2InR Z (destU p a t - 16) (destU p a t + 29) (destV p t - 23) (destV p t + 22)) :
    ∀ j : ℕ, T + j ≤ routeEndX g (upCorners p b s c H a t) T →
      routeFootX g (upCorners p b s c H a t) T j ⊆ Z := by
  intro j hj
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  rw [isep2_upCorners_eq] at htim hlin hj ⊢
  have l1 := hlin.1
  refine isep2_rfoot_sub [isep2U2 p b s c H, isep2U3 p b s c H, isep2U4 p b s c a t,
    isep2U5 p a t] (isep2U1 p b s c) g T htim hlin ?_ ?_ ?_ ?_ j hj
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by simp [isep2U1, isep2U2, isep2U3, isep2U4, isep2U5], ?_⟩ <;>
      simp only [CPar, rfCU, rfCV, isep2U1, isep2U2, isep2U3, isep2U4, isep2U5] <;> omega
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl <;> intro x hx
    · have := isep2_rx_uv (by simp [isep2U1])
        (by simp only [CPar, rfCU, rfCV, isep2U1]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U1] at this
      exact z1 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2U2])
        (by simp only [CPar, rfCU, rfCV, isep2U2]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U2] at this
      exact z2 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2U3])
        (by simp only [CPar, rfCU, rfCV, isep2U3]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U3] at this
      exact z3 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2U4])
        (by simp only [CPar, rfCU, rfCV, isep2U4]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U4] at this
      exact z4 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2U5])
        (by simp only [CPar, rfCU, rfCV, isep2U5]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U5] at this
      exact z5 x (by omega) (by omega) (by omega) (by omega)
  · refine ⟨fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_,
      fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_, trivial⟩ <;>
      simp only [Ray, outD, behindIn, isep2U1, isep2U2, isep2U3, isep2U4, isep2U5] at r1 r2 <;>
      obtain ⟨x1, x2, x3, x4⟩ := hx
    · exact z12 x (by omega) (by omega) (by omega) (by omega)
    · exact z23 x (by omega) (by omega) (by omega) (by omega)
    · exact z34 x (by omega) (by omega) (by omega) (by omega)
    · exact z45 x (by omega) (by omega) (by omega) (by omega)
  · intro t' _ ht'
    refine isep2_start_of_ray l1 (by simp [isep2U1])
      (by simp only [CPar, rfCU, rfCV, isep2U1]; omega) (fun cu cv r x hx => ?_) t' (by omega)
    simp only [Ray, behindIn, isep2U1] at r
    obtain ⟨x1, x2, x3, x4⟩ := hx
    exact zs x (by omega) (by omega) (by omega)

/-- The fourth corner of a down-going link (image `2`, column of the port). -/
def isep2D4 (p : Program) (b s c cd : ℤ) : Corner :=
  ⟨2, cd, trackBack p b s c, .band b (9 - s) false⟩

/-- The port corner of a down-going link (image `4`). -/
def isep2D5 (cd vp : ℤ) (r : ℕ) (idx : ℤ) : Corner := ⟨4, cd, vp, .left r idx⟩

/-- The corners of a down-going link. -/
theorem isep2_downCorners_eq (p : Program) (b s c H cd vp : ℤ) (r : ℕ) (idx : ℤ) :
    downCorners p b s c H cd vp r idx = [isep2U1 p b s c, isep2U2 p b s c H, isep2U3 p b s c H,
      isep2D4 p b s c cd, isep2D5 cd vp r idx] := rfl

/-- **A whole down-going link inside a set** (source column, `OUT` track, hairpin column,
`BACK` track up to the column `cd` of the port, the column down to the port line `vp`). -/
theorem isep2_down_sub (p : Program) (b s c H cd vp : ℤ) (r : ℕ) (idx : ℤ) {g : WL} {T : ℕ}
    (htim : RouteTimedX g (downCorners p b s c H cd vp r idx) T)
    (hlin : RouteLines g (downCorners p b s c H cd vp r idx))
    (hH : (H - c) % 2 = 0) (hd : (cd - c) % 2 = 0) (hdv : (cd + vp) % 2 = 1) {Z : Set Cell}
    (zs : isep2InH Z (c - 4) (c + 4) (trackOut p b s c - 7))
    (z1 : isep2InR Z (c - 29) (c + 16) (trackOut p b s c - 18) (trackOut p b s c + 27))
    (z12 : isep2InR Z (H + 9) (c - 9) (trackOut p b s c - 2) (trackOut p b s c + 6))
    (z2 : isep2InR Z (H - 25) (H + 20) (trackOut p b s c - 14) (trackOut p b s c + 31))
    (z23 : isep2InR Z (H - 4) (H + 4) (trackOut p b s c + 11) (trackBack p b s c - 7))
    (z3 : isep2InR Z (H - 17) (H + 28) (trackBack p b s c - 19) (trackBack p b s c + 26))
    (z34 : isep2InR Z (H + 9) (cd - 9) (trackBack p b s c - 2) (trackBack p b s c + 6))
    (z4 : isep2InR Z (cd - 21) (cd + 24) (trackBack p b s c - 15) (trackBack p b s c + 30))
    (z45 : isep2InR Z (cd - 4) (cd + 4) (trackBack p b s c + 11) (vp - 7))
    (z5 : isep2InR Z (cd - 17) (cd + 28) (vp - 19) (vp + 26)) :
    ∀ j : ℕ, T + j ≤ routeEndX g (downCorners p b s c H cd vp r idx) T →
      routeFootX g (downCorners p b s c H cd vp r idx) T j ⊆ Z := by
  intro j hj
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  rw [isep2_downCorners_eq] at htim hlin hj ⊢
  have l1 := hlin.1
  refine isep2_rfoot_sub [isep2U2 p b s c H, isep2U3 p b s c H, isep2D4 p b s c cd,
    isep2D5 cd vp r idx] (isep2U1 p b s c) g T htim hlin ?_ ?_ ?_ ?_ j hj
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by simp [isep2U1, isep2U2, isep2U3, isep2D4, isep2D5], ?_⟩ <;>
      simp only [CPar, rfCU, rfCV, isep2U1, isep2U2, isep2U3, isep2D4, isep2D5] <;> omega
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl <;> intro x hx
    · have := isep2_rx_uv (by simp [isep2U1])
        (by simp only [CPar, rfCU, rfCV, isep2U1]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U1] at this
      exact z1 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2U2])
        (by simp only [CPar, rfCU, rfCV, isep2U2]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U2] at this
      exact z2 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2U3])
        (by simp only [CPar, rfCU, rfCV, isep2U3]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U3] at this
      exact z3 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2D4])
        (by simp only [CPar, rfCU, rfCV, isep2D4]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2D4] at this
      exact z4 x (by omega) (by omega) (by omega) (by omega)
    · have := isep2_rx_uv (by simp [isep2D5])
        (by simp only [CPar, rfCU, rfCV, isep2D5]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2D5] at this
      exact z5 x (by omega) (by omega) (by omega) (by omega)
  · refine ⟨fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_,
      fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_, trivial⟩ <;>
      simp only [Ray, outD, behindIn, isep2U1, isep2U2, isep2U3, isep2D4, isep2D5] at r1 r2 <;>
      obtain ⟨x1, x2, x3, x4⟩ := hx
    · exact z12 x (by omega) (by omega) (by omega) (by omega)
    · exact z23 x (by omega) (by omega) (by omega) (by omega)
    · exact z34 x (by omega) (by omega) (by omega) (by omega)
    · exact z45 x (by omega) (by omega) (by omega) (by omega)
  · intro t' _ ht'
    refine isep2_start_of_ray l1 (by simp [isep2U1])
      (by simp only [CPar, rfCU, rfCV, isep2U1]; omega) (fun cu cv r x hx => ?_) t' (by omega)
    simp only [Ray, behindIn, isep2U1] at r
    obtain ⟨x1, x2, x3, x4⟩ := hx
    exact zs x (by omega) (by omega) (by omega)

end LP

end LeanTheory.Life
