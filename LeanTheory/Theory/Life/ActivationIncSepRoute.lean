/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepTime

/-!
# The footprint of a route with corner windows

Research note `N-22`. Generic facts about `routeFootX` (`ActivationIncCompose`), the footprint of
a route run with corner windows (the glider box until `20` generations before each corner, the
extended relay box `relayBoxX` during the window, then the next leg):

* `isep2_box_sub_relay`: the glider box at `meetT - 20` lies in the extended relay box (so the
  footprint at the start of a window is covered by the window);
* `isep2_rfoot_far`: under `RouteSepX`, the footprint is far from every piece of `L` other than
  the reflectors of the route, at every generation up to the end of the route;
* `isep2_rx_uv`: the exact `uv`-hull of the extended relay box of each image;
* `isep2_rfoot_sub`: the footprint lies in a set `Z` that contains the extended relay boxes, the
  first flight and the `uv`-boxes of every glider centre on a leg (`isep2LegsIn`: on the ray out
  of one corner and on the ray into the next one);
* `isep2_rfoot_prefix`: before the window of a corner, the footprint does not depend on the
  corners after it.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Glider boxes and their centres -/

/-- The `uv`-box around a glider centre `(cu, cv)`: `u ∈ [cu - 4, cu + 4]`,
`v ∈ [cv - 2, cv + 6]`. -/
def isep2CBox (cu cv : ℤ) : Set Cell :=
  {x | cu - 4 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ cu + 4 ∧ cv - 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ cv + 6}

/-- The glider box lies in the `uv`-box around its centre. -/
theorem isep2_box_cbox (w : WL) (t : ℤ) : w.box t ⊆ isep2CBox (w.cu t) (w.cv t) := by
  rintro x ⟨h1, h2, h3, h4⟩
  simp only [isep2CBox, WL.cu, WL.cv, Set.mem_ofPred_eq]
  omega

/-- **The glider at the start of the window of a corner lies in its extended relay box.** -/
theorem isep2_box_sub_relay {g : WL} {c : Corner} (hl : OnLine g c) (hk : c.k < 8) :
    g.box (meetT g c - 20) ⊆ relayBoxX c := by
  have h := inWL_of_onLine hl
  unfold meetT
  generalize delayS g c = s at h ⊢
  rw [h]
  obtain ⟨k, u, v, tag⟩ := c
  simp only at hk
  rintro x ⟨x1, x2, x3, x4⟩
  simp only [relayBoxX, rxB, inWL, WL.px, WL.py, WL.qt, WL.shift] at x1 x2 x3 x4 ⊢
  interval_cases k <;>
    simp only [rxBox, rfIn, rfX, rfY, rfCU, rfCV] at x1 x2 x3 x4 ⊢ <;>
    exact ⟨by omega, by omega, by omega, by omega⟩

/-! ### Far from the pieces -/

/-- **The footprint of a route is far from every piece other than its reflectors**, under the
corrected separation condition `RouteSepX`, at every generation up to the end of the route. -/
theorem isep2_rfoot_far {L : List Piece} {Z : Set Cell} :
    ∀ (cs : List Corner) (c : Corner) (g : WL) (T : ℕ), RouteSepX L Z g (c :: cs) T →
      RouteTimedX g (c :: cs) T → RouteLines g (c :: cs) → (∀ c' ∈ c :: cs, c'.k < 8) →
      ∀ j : ℕ, T + j ≤ routeEndX g (c :: cs) T → ∀ h ∈ L,
        h ∉ (route g (c :: cs)).1.map PSpec.piece →
          FarApart 2 (routeFootX g (c :: cs) T j) h.box
  | cs, c, g, T, ⟨_, s2, _, ⟨L', hperm, hfar⟩, s5⟩, ⟨ht, hts⟩, ⟨hl, hls⟩, hk, j, hj, h, hh,
      hn => by
    have hm := meetT_cast_X (Int.natCast_nonneg T) ht
    have hne : h ≠ (reflect g c).1.piece := fun he => hn (by simp [route, he])
    have hL' : h ∈ L' := by
      rcases List.mem_cons.1 (hperm.mem_iff.1 hh) with he | he
      · exact absurd he hne
      · exact he
    have hrel := hfar h hL'
    simp only [routeFootX]
    split_ifs with h1 h2
    · by_cases h3 : (T : ℤ) + j < meetT g c - 20
      · exact s2 _ (by omega) h3 h hh
      · have e : (T : ℤ) + j = meetT g c - 20 := by omega
        rw [e]
        exact hrel.mono (isep2_box_sub_relay hl (hk c List.mem_cons_self)) le_rfl
    · exact hrel
    · cases cs with
      | nil =>
        exfalso
        simp only [routeEndX] at hj
        omega
      | cons c' cs' =>
        refine isep2_rfoot_far cs' c' (reflect g c).2 ((meetT g c).toNat + 40)
          (by rw [hm]; exact s5) (by rw [hm]; exact hts) hls
          (fun c'' hc'' => hk c'' (List.mem_cons_of_mem _ hc''))
          (T + j - ((meetT g c).toNat + 40)) ?_ h hh ?_
        · have hj' : T + j ≤ routeEndX (reflect g c).2 (c' :: cs') ((meetT g c).toNat + 40) := hj
          omega
        · intro hm'
          apply hn
          have e : (route g (c :: c' :: cs')).1 =
              (reflect g c).1 :: (route (reflect g c).2 (c' :: cs')).1 := rfl
          rw [e, List.map_cons, List.mem_cons]
          exact Or.inr hm'

/-! ### The exact hull of the extended relay box -/

/-- Lower `u`-offset of the extended relay box of image `k`. -/
def isep2RxU1 : ℕ → ℤ
  | 0 => -24 | 1 => -16 | 2 => -21 | 3 => -29 | 4 => -17 | 5 => -28 | 6 => -20 | _ => -25

/-- Upper `u`-offset of the extended relay box of image `k`. -/
def isep2RxU2 : ℕ → ℤ
  | 0 => 21 | 1 => 29 | 2 => 24 | 3 => 16 | 4 => 28 | 5 => 17 | 6 => 25 | _ => 20

/-- Lower `v`-offset of the extended relay box of image `k`. -/
def isep2RxV1 : ℕ → ℤ
  | 0 => -26 | 1 => -23 | 2 => -15 | 3 => -18 | 4 => -19 | 5 => -22 | 6 => -27 | _ => -14

/-- Upper `v`-offset of the extended relay box of image `k`. -/
def isep2RxV2 : ℕ → ℤ
  | 0 => 19 | 1 => 22 | 2 => 30 | 3 => 27 | 4 => 26 | 5 => 23 | 6 => 18 | _ => 31

/-- **The exact `uv`-hull of the extended relay box of a corner** (with the parity of its
image). -/
theorem isep2_rx_uv {c : Corner} (hk : c.k < 8) (hp : CPar c) {x : Cell}
    (hx : x ∈ relayBoxX c) :
    c.u + isep2RxU1 c.k ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c.u + isep2RxU2 c.k ∧
      c.v + isep2RxV1 c.k ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ c.v + isep2RxV2 c.k := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only [CPar] at hk hp
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [rxB] at x1 x2 x3 x4
  interval_cases k <;>
    simp only [rxBox, rfX, rfY, rfCU, rfCV, isep2RxU1, isep2RxU2, isep2RxV1,
      isep2RxV2] at hp x1 x2 x3 x4 ⊢ <;> omega

/-! ### Inside a set -/

/-- **The legs of a route lie in `Z`**: for two consecutive corners, the `uv`-box of every glider
centre on the ray out of the first one and on the ray into the second one lies in `Z`. -/
def isep2LegsIn (Z : Set Cell) : List Corner → Prop
  | c :: c' :: cs =>
    (∀ cu cv : ℤ, Ray (outD c.k) c.u c.v cu cv 13 → Ray (behindIn c'.k) c'.u c'.v cu cv 13 →
      isep2CBox cu cv ⊆ Z) ∧ isep2LegsIn Z (c' :: cs)
  | _ => True

/-- **The first flight in `Z` from the ray into the first corner.** -/
theorem isep2_start_of_ray {Z : Set Cell} {g : WL} {c : Corner} (hl : OnLine g c)
    (hk : c.k < 8) (hp : CPar c)
    (hray : ∀ cu cv : ℤ, Ray (behindIn c.k) c.u c.v cu cv 13 → isep2CBox cu cv ⊆ Z) :
    ∀ t : ℤ, t ≤ meetT g c - 16 → g.box t ⊆ Z := by
  intro t ht
  have hw := inWL_of_onLine hl
  have ht' : t ≤ delayS g c - 76 := by unfold meetT at ht; omega
  have hi := in_center hk hp (s := delayS g c) ht'
  change Ray _ _ _ ((inWL c (delayS g c)).cu t) ((inWL c (delayS g c)).cv t) 13 at hi
  rw [← hw] at hi
  exact (isep2_box_cbox g t).trans (hray _ _ hi)

/-- **The footprint of a route lies in `Z`** if `Z` contains the extended relay boxes of its
corners, the first flight up to the window of the first corner, and the legs. -/
theorem isep2_rfoot_sub {Z : Set Cell} :
    ∀ (cs : List Corner) (c : Corner) (g : WL) (T : ℕ), RouteTimedX g (c :: cs) T →
      RouteLines g (c :: cs) → (∀ c' ∈ c :: cs, c'.k < 8 ∧ CPar c') →
      (∀ c' ∈ c :: cs, relayBoxX c' ⊆ Z) → isep2LegsIn Z (c :: cs) →
      (∀ t : ℤ, (T : ℤ) ≤ t → t ≤ meetT g c - 20 → g.box t ⊆ Z) →
      ∀ j : ℕ, T + j ≤ routeEndX g (c :: cs) T → routeFootX g (c :: cs) T j ⊆ Z
  | cs, c, g, T, ⟨ht, hts⟩, ⟨hl, hls⟩, hok, hrel, hlegs, hstart, j, hj => by
    have hm := meetT_cast_X (Int.natCast_nonneg T) ht
    simp only [routeFootX]
    split_ifs with h1 h2
    · exact hstart _ (by omega) h1
    · exact hrel c List.mem_cons_self
    · cases cs with
      | nil =>
        exfalso
        simp only [routeEndX] at hj
        omega
      | cons c' cs' =>
        obtain ⟨hleg, hlegs'⟩ := hlegs
        obtain ⟨hk, hp⟩ := hok c List.mem_cons_self
        obtain ⟨hk', hp'⟩ := hok c' (List.mem_cons_of_mem _ List.mem_cons_self)
        refine isep2_rfoot_sub cs' c' (reflect g c).2 ((meetT g c).toNat + 40)
          (by rw [hm]; exact hts) hls (fun c'' hc'' => hok c'' (List.mem_cons_of_mem _ hc''))
          (fun c'' hc'' => hrel c'' (List.mem_cons_of_mem _ hc'')) hlegs' ?_
          (T + j - ((meetT g c).toNat + 40)) ?_
        · intro t ht1 ht2
          rw [hm] at ht1
          have hw := inWL_of_onLine hls.1
          have ho := out_center hk hp (s := delayS g c) (t := t) (by unfold meetT at ht1; omega)
          have hi := in_center hk' hp' (s := delayS (reflect g c).2 c') (t := t)
            (by unfold meetT at ht2; omega)
          change Ray _ _ _ ((outWL c (delayS g c)).cu t) ((outWL c (delayS g c)).cv t) 13 at ho
          change Ray _ _ _ ((inWL c' (delayS (reflect g c).2 c')).cu t)
            ((inWL c' (delayS (reflect g c).2 c')).cv t) 13 at hi
          rw [← hw] at hi
          rw [← reflect_snd] at ho
          exact (isep2_box_cbox _ t).trans (hleg _ _ ho hi)
        · have hj' : T + j ≤ routeEndX (reflect g c).2 (c' :: cs') ((meetT g c).toNat + 40) := hj
          omega

/-- **Before the window of a corner, the footprint does not depend on the later corners.** -/
theorem isep2_rfoot_prefix : ∀ (pre : List Corner) (c : Corner) (post : List Corner) (g : WL)
    (T j : ℕ), RouteTimedX g (pre ++ c :: post) T →
      (T : ℤ) + j ≤ meetT (route g pre).2 c - 20 →
      routeFootX g (pre ++ c :: post) T j = routeFootX g (pre ++ [c]) T j
  | [], c, post, g, T, j, _, hj => by
    simp only [List.nil_append, routeFootX, route] at hj ⊢
    simp only [hj, ↓reduceIte]
  | c0 :: pre, c, post, g, T, j, ⟨ht, hts⟩, hj => by
    have hm := meetT_cast_X (Int.natCast_nonneg T) ht
    simp only [List.cons_append, routeFootX]
    split_ifs with h1 h2
    · rfl
    · rfl
    · refine isep2_rfoot_prefix pre c post (reflect g c0).2 ((meetT g c0).toNat + 40)
        (T + j - ((meetT g c0).toNat + 40)) (by rw [hm]; exact hts) ?_
      have e : (route g (c0 :: pre)).2 = (route (reflect g c0).2 pre).2 := rfl
      rw [e] at hj
      have hm' : ((meetT g c0).toNat : ℤ) = meetT g c0 := Int.toNat_of_nonneg (by omega)
      push_cast [Nat.cast_sub (show (meetT g c0).toNat + 40 ≤ T + j by omega)]
      omega

end LP

end LeanTheory.Life
