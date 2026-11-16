/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepMain

/-!
# The moving fields of `DecSep`: tools

Research note `N-22`. Tools for the fields of `DecSepRest` (`DecSepMain`) about the control, the
tokens, the answers and the captures of a `decJz` activation:

* `dsepM_reflP_mem`: a reflector of a route has the box of one of its corners;
* `dsepM_corner_far`: a set in the `u`-band of module `r`, above the bands, is far from the
  reflector of every corner of the machine (`allCorners`);
* `dsepM_band_far`: a set above the bands is far from every band corner;
* `dsepM_out_far`: from `40` generations after a corner is met, the outgoing glider is far from
  the reflector of the corner;
* the boxes of the stations, of the DEC copies and of the entry chains, in coordinates.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Reflectors of routes -/

/-- **A reflector of a route has the box of one of its corners.** -/
theorem dsepM_reflP_mem {g : WL} {cs : List Corner} {h : Piece} (hh : h ∈ reflP g cs) :
    ∃ c ∈ cs, h.box = Box (cornerSpec c).bx.a (cornerSpec c).bx.b (cornerSpec c).bx.lo
      (cornerSpec c).bx.hi := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  have hb : s.bx ∈ cs.map fun c => (cornerSpec c).bx := by
    rw [← route_bx g cs]
    exact List.mem_map_of_mem hs
  obtain ⟨c, hc, he⟩ := List.mem_map.1 hb
  exact ⟨c, hc, by rw [PSpec.piece_box, he]⟩

/-- The corners of the routes of a `decJz` instruction are corners of the machine. -/
theorem dsepM_corner_mem (hi : p[i]? = some (.decJz r z)) {g : WL} {cs : List Corner}
    (hx : (g, cs) ∈ instrSpecs p i) : ∀ c ∈ cs, c ∈ allCorners p :=
  instrRoute_corner (List.getElem?_eq_some_iff.1 hi).1 hx

/-! ### Far from the corners -/

/-- **A set above the bands is far from every band, halt or slab corner.** -/
theorem dsepM_band_far (hp : p.WellFormed) {S : Set Cell}
    (hS : ∀ x ∈ S, -4100 - 198 * D p ≤ x.1 + x.2) {c : Corner} (hc : c ∈ allCorners p)
    (ht : (∃ b k h, c.tag = .band b k h) ∨ (∃ a, c.tag = .halt a) ∨ (∃ a t, c.tag = .slab a t)) :
    FarApart 2 S (Box (cornerSpec c).bx.a (cornerSpec c).bx.b (cornerSpec c).bx.lo
      (cornerSpec c).bx.hi) := by
  have hv := allCorners_valid hp c hc
  have hcu := corner_uv c
  have hf := lane_VT_low p
  refine isep2_far_box fun x hx => ?_
  have := hS x hx
  unfold BoxT.InUV at hcu
  obtain ⟨k, u, v, tag⟩ := c
  simp only at hcu ht
  rcases ht with ⟨b, n, h', rfl⟩ | ⟨a, rfl⟩ | ⟨a, t, rfl⟩
  · simp only [Valid] at hv; omega
  · simp only [Valid] at hv; omega
  · simp only [Valid] at hv; omega

/-- **A set in the `u`-band of module `r`, above the bands, is far from the reflector of every
corner of the machine**: right of the left zone of the module (`u ≥ U_r - 760`), and left of the
right zone or below it (`u ≤ U_r + 1170` or `v ≤ 1450`). -/
theorem dsepM_corner_far (hp : p.WellFormed) (r : ℕ) {S : Set Cell}
    (hS : ∀ x ∈ S, U p r - 760 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + 1300 + 144 * D p ∧
      -4100 - 198 * D p ≤ x.1 + x.2 ∧ (x.1 - x.2 ≤ U p r + 1170 ∨ x.1 + x.2 ≤ 1450))
    {c : Corner} (hc : c ∈ allCorners p) :
    FarApart 2 S (Box (cornerSpec c).bx.a (cornerSpec c).bx.b (cornerSpec c).bx.lo
      (cornerSpec c).bx.hi) := by
  have hv := allCorners_valid hp c hc
  have hcu := corner_uv c
  have hf := lane_VT_low p
  refine isep2_far_box fun x hx => ?_
  have := hS x hx
  unfold BoxT.InUV at hcu
  obtain ⟨k, u, v, tag⟩ := c
  simp only at hcu
  cases tag with
  | band b n h' => simp only [Valid] at hv; omega
  | halt a' => simp only [Valid] at hv; omega
  | slab a' t => simp only [Valid] at hv; omega
  | left r' idx =>
    simp only [Valid] at hv
    rcases lt_trichotomy r' r with h' | rfl | h'
    · have := module_gap p (r := r') (r' := r) h'
      unfold modLeft modRight at *; omega
    · omega
    · have := module_gap p (r := r) (r' := r') h'
      unfold modLeft modRight at *; omega
  | right r' j w =>
    simp only [Valid] at hv
    rcases lt_trichotomy r' r with h' | rfl | h'
    · have := module_gap p (r := r') (r' := r) h'
      unfold modLeft modRight at *; omega
    · omega
    · have := module_gap p (r := r) (r' := r') h'
      unfold modLeft modRight at *; omega

/-- **The reflectors of a route of a `decJz` instruction are far from a set in the `u`-band of
module `r`** (as in `dsepM_corner_far`). -/
theorem dsepM_reflP_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) (r' : ℕ)
    {S : Set Cell}
    (hS : ∀ x ∈ S, U p r' - 760 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r' + 1300 + 144 * D p ∧
      -4100 - 198 * D p ≤ x.1 + x.2 ∧ (x.1 - x.2 ≤ U p r' + 1170 ∨ x.1 + x.2 ≤ 1450))
    {g : WL} {cs : List Corner} (hx : (g, cs) ∈ instrSpecs p i) {h : Piece}
    (hh : h ∈ reflP g cs) : FarApart 2 S h.box := by
  obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem hh
  rw [hb]
  exact dsepM_corner_far hp r' hS (dsepM_corner_mem hi hx c hc)

/-! ### The outgoing glider of a corner -/

/-- **From `40` generations after a corner is met, the outgoing glider is far from the reflector
of the corner.** -/
theorem dsepM_out_far {g : WL} {c : Corner} (hk : c.k < 8) {t : ℤ} (ht : meetT g c + 40 ≤ t) :
    FarApart 2 ((reflect g c).2.box t) (Box (cornerSpec c).bx.a (cornerSpec c).bx.b
      (cornerSpec c).bx.lo (cornerSpec c).bx.hi) := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only at hk
  refine isep2_far_box fun x hx => ?_
  obtain ⟨x1, x2, x3, x4⟩ := hx
  simp only [meetT, delayS, reflect, WL.shift, WL.px, WL.py, WL.qt, cornerSpec,
    PSpec.bx_mk, Base.piece] at ht x1 x2 x3 x4 ⊢
  interval_cases k <;>
    simp only [rfIn, rfOut, rfP, rfX, rfY, rfCU, rfCV] at ht x1 x2 x3 x4 ⊢ <;> omega

/-- The final world line of a route with a last corner is the outgoing glider of that corner. -/
theorem dsepM_route_snoc : ∀ (cs : List Corner) (c : Corner) (g : WL),
    (route g (cs ++ [c])).2 = (reflect (route g cs).2 c).2
  | [], _, _ => rfl
  | c' :: cs, c, g => dsepM_route_snoc cs c (reflect g c').2

/-- **After the end of a route with corner windows, the final glider is far from the reflector
of the last corner.** -/
theorem dsepM_final_far (cs : List Corner) (c : Corner) (g : WL) (T : ℕ) (hk : c.k < 8)
    (htim : RouteTimedX g (cs ++ [c]) T) {t : ℕ} (ht : routeEndX g (cs ++ [c]) T ≤ t) :
    FarApart 2 ((route g (cs ++ [c])).2.box t) (Box (cornerSpec c).bx.a (cornerSpec c).bx.b
      (cornerSpec c).bx.lo (cornerSpec c).bx.hi) := by
  have he := routeEndX_snoc cs c g T htim
  rw [dsepM_route_snoc] at he ⊢
  refine dsepM_out_far hk ?_
  have : (routeEndX g (cs ++ [c]) T : ℤ) ≤ t := by exact_mod_cast ht
  simp only [reflect, WL.shift, meetT, delayS] at he ⊢
  omega

end LP

end LeanTheory.Life
