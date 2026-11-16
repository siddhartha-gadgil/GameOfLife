/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepThrMain

/-!
# Tools for the fields `nThr`, `zThr`, `zGate` of `DecSep`: routes in a half-plane of `u`

Research note `N-22`. Generic facts about the footprint `routeFootX` of a route with corner
windows, in the coordinate `u = x - y` (as `lane_route_vlow` in `v`):

* `WL.uHi`: the largest `u` of the box of a glider (`WL.uLo`, `ActivationIncRegion`: the
  smallest);
* `dsepX_route_uhigh`: a route whose corners lie at `u ≤ M - 70`, from a glider at `u ≤ M`,
  keeps its footprint at `u ≤ M`, and so does the final glider at the end of the route;
* `dsepX_route_ulow`: the same at `u ≥ M`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The `u` of a glider box -/

/-- The largest `u = x - y` of the box of the glider of `w` at time `t`. -/
def WL.uHi (w : WL) (t : ℤ) : ℤ := w.px t - w.py t + 4

/-- Every cell of the glider box has `u` at most `uHi`. -/
theorem WL.le_uHi {w : WL} {t : ℤ} {c : Cell} (h : c ∈ w.box t) : c.1 - c.2 ≤ w.uHi t := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold WL.uHi
  omega

/-- **Between two times, the largest `u` of a glider box is at most the larger end value.** -/
theorem WL.uHi_between {w : WL} (hd : w.Dir) {t₁ t t₂ : ℤ} (h1 : t₁ ≤ t) (h2 : t ≤ t₂) :
    w.uHi t ≤ max (w.uHi t₁) (w.uHi t₂) := by
  obtain ⟨hx, hy⟩ := hd
  have q1 : (t₁ - w.tau) / 4 ≤ (t - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  have q2 : (t - w.tau) / 4 ≤ (t₂ - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  unfold WL.uHi WL.py WL.px WL.qt
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> omega

/-- **A glider flying `NW` or `SE`** keeps its `u`. -/
theorem WL.uLo_const {w : WL} (hd : w.dx = w.dy) (hx : w.dx = 1 ∨ w.dx = -1) (t t' : ℤ) :
    w.uLo t = w.uLo t' := by
  unfold WL.uLo WL.py WL.px WL.qt
  rw [← hd]
  rcases hx with hx | hx <;> rw [hx] <;> ring

/-- **The glider at a corner**: on the input line of the corner, at the meeting time, its box is
within `70` of the corner point in `u`. -/
theorem dsepX_u_meet {g : WL} {c : Corner} (h : OnLine g c) :
    g.uHi (meetT g c) ≤ c.u + 70 ∧ c.u - 70 ≤ g.uLo (meetT g c) := by
  obtain ⟨dx, dy, lane, tau⟩ := g
  obtain ⟨k, u, v, tag⟩ := c
  have hdx := congrArg WL.dx h
  have hdy := congrArg WL.dy h
  have hl := congrArg WL.lane h
  simp only [WL.shift] at hdx hdy hl
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rfIn] at hdx hdy hl <;> subst hdx hdy <;>
    simp only [WL.uHi, WL.uLo, WL.px, WL.py, WL.qt, meetT, delayS, rfIn, rfX, rfY, rfCU,
      rfCV] at hl ⊢ <;> omega

/-- **The glider leaving a corner window**: `40` generations after the meeting time its box is
within `70` of the corner point in `u`. -/
theorem dsepX_u_out40 (g : WL) (c : Corner) :
    (reflect g c).2.uHi (meetT g c + 40) ≤ c.u + 70 ∧
      c.u - 70 ≤ (reflect g c).2.uLo (meetT g c + 40) := by
  obtain ⟨k, u, v, tag⟩ := c
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [reflect, WL.uHi, WL.uLo, WL.px, WL.py, WL.qt, WL.shift, meetT, delayS, rfIn,
      rfOut, rfX, rfY, rfCU, rfCV] <;> omega

/-- **The extended relay box of a corner** is within `70` of the corner point in `u`. -/
theorem dsepX_relay_u {c : Corner} {x : Cell} (hx : x ∈ relayBoxX c) :
    c.u - 70 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c.u + 70 := by
  obtain ⟨k, u, v, tag⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rxB, rxBox, rfX, rfY, rfCU, rfCV] at h1 h2 h3 h4 ⊢ <;> omega

/-- **A route with corners left of `M - 70` keeps its footprint at `u ≤ M`**: from a glider whose
box is at `u ≤ M` at time `T`, through corners met on their input lines, in order, up to the end
of the route, and so does the final glider box at the end. -/
theorem dsepX_route_uhigh (M : ℤ) : ∀ (cs : List Corner) (g : WL) (T : ℕ), g.Dir →
    RouteLines g cs → RouteTimedX g cs T → (∀ c ∈ cs, c.u + 70 ≤ M) → g.uHi T ≤ M →
    (∀ i, T + i ≤ routeEndX g cs T → ∀ x ∈ routeFootX g cs T i, x.1 - x.2 ≤ M) ∧
      (route g cs).2.uHi (routeEndX g cs T) ≤ M
  | [], g, T, _, _, _, _, h0 => by
    refine ⟨fun i hi x hx => ?_, h0⟩
    simp only [routeEndX] at hi
    rw [show i = 0 by omega] at hx
    simp only [routeFootX, Nat.cast_zero, add_zero] at hx
    exact (WL.le_uHi hx).trans h0
  | c :: cs, g, T, hd, ⟨hl, hls⟩, ⟨ht, hts⟩, hcs, h0 => by
    set m := (meetT g c).toNat with hm
    have hmT : ((m : ℕ) : ℤ) = meetT g c := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hc := hcs c List.mem_cons_self
    have h1 := (dsepX_u_meet hl).1
    have h2 := (dsepX_u_out40 g c).1
    have hts' : RouteTimedX (reflect g c).2 cs ((m + 40 : ℕ) : ℤ) := by
      push_cast
      rw [hmT]
      exact hts
    obtain ⟨ih1, ih2⟩ := dsepX_route_uhigh M cs _ (m + 40) (reflect_dir g c) hls hts'
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by push_cast; rw [hmT]; omega)
    refine ⟨fun i hi x hx => ?_, ih2⟩
    simp only [routeEndX, ← hm] at hi
    simp only [routeFootX, ← hm] at hx
    split_ifs at hx with ha hb
    · exact (WL.le_uHi hx).trans ((WL.uHi_between hd (t₁ := T) (t₂ := meetT g c) (by omega)
        (by omega)).trans (max_le (by omega) (by omega)))
    · have := dsepX_relay_u hx
      omega
    · exact ih1 _ (by omega) x hx

/-- **A route with corners right of `M + 70` keeps its footprint at `u ≥ M`** (as
`dsepX_route_uhigh`). -/
theorem dsepX_route_ulow (M : ℤ) : ∀ (cs : List Corner) (g : WL) (T : ℕ), g.Dir →
    RouteLines g cs → RouteTimedX g cs T → (∀ c ∈ cs, M + 70 ≤ c.u) → M ≤ g.uLo T →
    (∀ i, T + i ≤ routeEndX g cs T → ∀ x ∈ routeFootX g cs T i, M ≤ x.1 - x.2) ∧
      M ≤ (route g cs).2.uLo (routeEndX g cs T)
  | [], g, T, _, _, _, _, h0 => by
    refine ⟨fun i hi x hx => ?_, h0⟩
    simp only [routeEndX] at hi
    rw [show i = 0 by omega] at hx
    simp only [routeFootX, Nat.cast_zero, add_zero] at hx
    exact h0.trans (WL.uLo_le hx)
  | c :: cs, g, T, hd, ⟨hl, hls⟩, ⟨ht, hts⟩, hcs, h0 => by
    set m := (meetT g c).toNat with hm
    have hmT : ((m : ℕ) : ℤ) = meetT g c := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hc := hcs c List.mem_cons_self
    have h1 := (dsepX_u_meet hl).2
    have h2 := (dsepX_u_out40 g c).2
    have hts' : RouteTimedX (reflect g c).2 cs ((m + 40 : ℕ) : ℤ) := by
      push_cast
      rw [hmT]
      exact hts
    obtain ⟨ih1, ih2⟩ := dsepX_route_ulow M cs _ (m + 40) (reflect_dir g c) hls hts'
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by push_cast; rw [hmT]; omega)
    refine ⟨fun i hi x hx => ?_, ih2⟩
    simp only [routeEndX, ← hm] at hi
    simp only [routeFootX, ← hm] at hx
    split_ifs at hx with ha hb
    · exact ((le_min (by omega) (by omega)).trans (WL.uLo_between hd (t₁ := T)
        (t₂ := meetT g c) (by omega) (by omega))).trans (WL.uLo_le hx)
    · have := dsepX_relay_u hx
      omega
    · exact ih1 _ (by omega) x hx

/-- **The footprint of a route after a corner window**: past `40` generations after the first
corner is met, the footprint is that of the rest of the route. -/
theorem dsepX_rfoot_drop {g : WL} {c : Corner} {cs : List Corner} {T j : ℕ}
    (h : meetT g c + 40 < (T : ℤ) + j) :
    routeFootX g (c :: cs) T j = routeFootX (reflect g c).2 cs ((meetT g c).toNat + 40)
      (T + j - ((meetT g c).toNat + 40)) := by
  simp only [routeFootX]
  simp only [show ¬ ((T : ℤ) + j ≤ meetT g c - 20) by omega,
    show ¬ ((T : ℤ) + j ≤ meetT g c + 40) by omega, ↓reduceIte]

end LP

end LeanTheory.Life
