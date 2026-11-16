/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepThrMain
public import LeanTheory.Theory.Life.DecSepACert

/-!
# The routes of a `decJz` activation inside explicit regions

Research note `N-22`. The footprints of the routes with corner windows (`routeFootX`) of the
control `C`, the token `KNZ` (down-going links) and the token `KZ` (`ztokCorners`) lie in explicit
unions of `uv`-rectangles: the source column, the `OUT` track, the hairpin column, the `BACK`
track, the column of the port or of the channel and the last legs, with the exact hulls of the
extended relay boxes of the corners (`isep2_rx_uv`):

* `dsepADown`, `dsepA_down_sub`: a down-going link (`isep2_down_sub`);
* `dsepAZtok`, `dsepA_ztok_sub`: the `KZ` link, with its two corners in the right zone;
* `dsepA_final_ray`: after the end of a route, the final glider is on the ray out of its last
  corner, at least `13` from the corner point.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### A down-going link -/

/-- **The region of a down-going link**: the source column `c` above the `OUT` track `O`, the
corner window at `(c, O)`, the `OUT` track, the hairpin `H`, the hairpin column, the `BACK` track
`B`, the corner at the port column `cd`, the port column down to the port line `vp` and the port
corner. -/
def dsepADown (c O H B cd vp : ℤ) : Set Cell :=
  {x | (c - 4 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c + 4 ∧ x.1 + x.2 ≤ O - 7) ∨
    (c - 29 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c + 16 ∧ O - 18 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ O + 27) ∨
    (H + 9 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c - 9 ∧ O - 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ O + 6) ∨
    (H - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ H + 20 ∧ O - 14 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ O + 31) ∨
    (H - 4 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ H + 4 ∧ O + 11 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B - 7) ∨
    (H - 17 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ H + 28 ∧ B - 19 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B + 26) ∨
    (H + 9 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cd - 9 ∧ B - 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B + 6) ∨
    (cd - 21 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cd + 24 ∧ B - 15 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B + 30) ∨
    (cd - 4 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cd + 4 ∧ B + 11 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ vp - 7) ∨
    (cd - 17 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cd + 28 ∧ vp - 19 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ vp + 26)}

/-- **A down-going link lies in its region** up to the end of its route. -/
theorem dsepA_down_sub (p : Program) (b s c H cd vp : ℤ) (r : ℕ) (idx : ℤ) {g : WL} {T : ℕ}
    (htim : RouteTimedX g (downCorners p b s c H cd vp r idx) T)
    (hlin : RouteLines g (downCorners p b s c H cd vp r idx))
    (hH : (H - c) % 2 = 0) (hd : (cd - c) % 2 = 0) (hdv : (cd + vp) % 2 = 1) :
    ∀ j : ℕ, T + j ≤ routeEndX g (downCorners p b s c H cd vp r idx) T →
      routeFootX g (downCorners p b s c H cd vp r idx) T j ⊆
        dsepADown c (trackOut p b s c) H (trackBack p b s c) cd vp :=
  isep2_down_sub p b s c H cd vp r idx htim hlin hH hd hdv
    (fun _ h1 h2 h3 => Or.inl ⟨h1, h2, h3⟩)
    (fun _ h1 h2 h3 h4 => Or.inr (Or.inl ⟨h1, h2, h3, h4⟩))
    (fun _ h1 h2 h3 h4 => Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4⟩)))
    (fun _ h1 h2 h3 h4 => Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4⟩))))
    (fun _ h1 h2 h3 h4 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4⟩)))))
    (fun _ h1 h2 h3 h4 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4⟩))))))
    (fun _ h1 h2 h3 h4 =>
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4⟩)))))))
    (fun _ h1 h2 h3 h4 =>
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4⟩))))))))
    (fun _ h1 h2 h3 h4 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨h1, h2, h3, h4⟩)))))))))
    (fun _ h1 h2 h3 h4 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨h1, h2, h3, h4⟩)))))))))

/-! ### The `KZ` link -/

/-- The corner of the `KZ` link at its channel and turn depth (image `3`). -/
def dsepAZ5 (cd wd : ℤ) (r : ℕ) (j : ℤ) : Corner := ⟨3, cd, wd, .right r j 2⟩

/-- The corner of the `KZ` link at its station column and turn depth (image `0`). -/
def dsepAZ6 (st wd : ℤ) (r : ℕ) (j : ℤ) : Corner := ⟨0, st, wd, .right r j 3⟩

/-- The corners of the `KZ` link. -/
theorem dsepA_ztok_eq (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) :
    ztokCorners p b c H r j = [isep2U1 p b 2 c, isep2U2 p b 2 c H, isep2U3 p b 2 c H,
      isep2D4 p b 2 c (U p r + zTokChan p j), dsepAZ5 (U p r + zTokChan p j) (zTokDepth p j) r j,
      dsepAZ6 (U p r + zTokStation j) (zTokDepth p j) r j] := rfl

/-- **The region of the `KZ` link**: as a down-going link up to its channel `cd`, then the
channel down to the turn depth `wd`, the corner there, the leg to the station column `st` and the
station corner. -/
def dsepAZtok (c O H B cd wd st : ℤ) : Set Cell :=
  {x | (c - 4 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c + 4 ∧ x.1 + x.2 ≤ O - 7) ∨
    (c - 29 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c + 16 ∧ O - 18 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ O + 27) ∨
    (H + 9 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c - 9 ∧ O - 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ O + 6) ∨
    (H - 25 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ H + 20 ∧ O - 14 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ O + 31) ∨
    (H - 4 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ H + 4 ∧ O + 11 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B - 7) ∨
    (H - 17 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ H + 28 ∧ B - 19 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B + 26) ∨
    (H + 9 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cd - 9 ∧ B - 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B + 6) ∨
    (cd - 21 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cd + 24 ∧ B - 15 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ B + 30) ∨
    (cd - 4 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cd + 4 ∧ B + 11 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ wd - 7) ∨
    (cd - 29 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cd + 16 ∧ wd - 18 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ wd + 27) ∨
    (st + 9 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cd - 9 ∧ wd - 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ wd + 6) ∨
    (st - 24 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ st + 21 ∧ wd - 26 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ wd + 19)}

/-- **The `KZ` link lies in its region** up to the end of its route. -/
theorem dsepA_ztok_sub (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) {g : WL} {T : ℕ}
    (htim : RouteTimedX g (ztokCorners p b c H r j) T)
    (hlin : RouteLines g (ztokCorners p b c H r j))
    (hH : (H - c) % 2 = 0) (hd : (U p r + zTokChan p j - c) % 2 = 0)
    (hcw : (U p r + zTokChan p j + zTokDepth p j) % 2 = 1)
    (hsw : (U p r + zTokStation j + zTokDepth p j) % 2 = 1) :
    ∀ k : ℕ, T + k ≤ routeEndX g (ztokCorners p b c H r j) T →
      routeFootX g (ztokCorners p b c H r j) T k ⊆
        dsepAZtok c (trackOut p b 2 c) H (trackBack p b 2 c) (U p r + zTokChan p j)
          (zTokDepth p j) (U p r + zTokStation j) := by
  intro k hk
  have ho := trackOut_par p b 2 c
  have hb := trackBack_par p b 2 c
  rw [dsepA_ztok_eq] at htim hlin hk ⊢
  have l1 := hlin.1
  refine isep2_rfoot_sub [isep2U2 p b 2 c H, isep2U3 p b 2 c H,
    isep2D4 p b 2 c (U p r + zTokChan p j), dsepAZ5 (U p r + zTokChan p j) (zTokDepth p j) r j,
    dsepAZ6 (U p r + zTokStation j) (zTokDepth p j) r j] (isep2U1 p b 2 c) g T htim hlin
    ?_ ?_ ?_ ?_ k hk
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by simp [isep2U1, isep2U2, isep2U3, isep2D4, dsepAZ5, dsepAZ6], ?_⟩ <;>
      simp only [CPar, rfCU, rfCV, isep2U1, isep2U2, isep2U3, isep2D4, dsepAZ5, dsepAZ6] <;>
      omega
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;> intro x hx
    · have := isep2_rx_uv (by simp [isep2U1])
        (by simp only [CPar, rfCU, rfCV, isep2U1]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U1] at this
      exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)
    · have := isep2_rx_uv (by simp [isep2U2])
        (by simp only [CPar, rfCU, rfCV, isep2U2]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U2] at this
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))
    · have := isep2_rx_uv (by simp [isep2U3])
        (by simp only [CPar, rfCU, rfCV, isep2U3]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2U3] at this
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega⟩)))))
    · have := isep2_rx_uv (by simp [isep2D4])
        (by simp only [CPar, rfCU, rfCV, isep2D4]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, isep2D4] at this
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega⟩)))))))
    · have := isep2_rx_uv (by simp [dsepAZ5])
        (by simp only [CPar, rfCU, rfCV, dsepAZ5]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, dsepAZ5] at this
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega⟩)))))))))
    · have := isep2_rx_uv (by simp [dsepAZ6])
        (by simp only [CPar, rfCU, rfCV, dsepAZ6]; omega) hx
      simp only [isep2RxU1, isep2RxU2, isep2RxV1, isep2RxV2, dsepAZ6] at this
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨by omega, by omega, by omega, by omega⟩))))))))))
  · refine ⟨fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_,
      fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_, fun cu cv r1 r2 x hx => ?_,
      trivial⟩ <;>
      simp only [Ray, outD, behindIn, isep2U1, isep2U2, isep2U3, isep2D4, dsepAZ5,
        dsepAZ6] at r1 r2 <;>
      obtain ⟨x1, x2, x3, x4⟩ := hx
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))))))))
  · intro t' _ ht'
    refine isep2_start_of_ray l1 (by simp [isep2U1])
      (by simp only [CPar, rfCU, rfCV, isep2U1]; omega) (fun cu cv r x hx => ?_) t' (by omega)
    simp only [Ray, behindIn, isep2U1] at r
    obtain ⟨x1, x2, x3, x4⟩ := hx
    exact Or.inl ⟨by omega, by omega, by omega⟩

/-! ### After the end of a route -/

/-- **After the end of a route, the final glider is on the ray out of its last corner**, at least
`13` from the corner point. -/
theorem dsepA_final_ray (cs : List Corner) (c : Corner) (g : WL) (T : ℕ) (hk : c.k < 8)
    (hp : CPar c) (htim : RouteTimedX g (cs ++ [c]) T) {t : ℕ}
    (ht : routeEndX g (cs ++ [c]) T ≤ t) :
    ∃ cu cv : ℤ, Ray (outD c.k) c.u c.v cu cv 13 ∧
      (route g (cs ++ [c])).2.box t ⊆ isep2CBox cu cv := by
  have he := routeEndX_snoc cs c g T htim
  rw [dsepM_route_snoc, reflect_snd] at he ⊢
  simp only [outWL, WL.shift] at he
  have ht' : (routeEndX g (cs ++ [c]) T : ℤ) ≤ t := by exact_mod_cast ht
  have ho := out_center hk hp (s := delayS (route g cs).2 c) (t := t) (by omega)
  refine ⟨_, _, ho, ?_⟩
  exact isep2_box_cbox _ t

end LP

end LeanTheory.Life
