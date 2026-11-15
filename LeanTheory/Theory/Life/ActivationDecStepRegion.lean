/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecStepThread

/-!
# The region of a `decJz` activation: anchors and glider boxes

Research note `N-22`. The region of the machine is `u ≥ uMin p - 300` (`u = x - y`). This module
collects the tools of the region facts of the `decJz` step (as for `inc`, `ActivationIncRegion`):
anchors (a piece of the machine near each footprint bounds `uMin` from above: a module, an entry
chain, a reflector), the least `u` of a glider box (`WL.duLo`) along a flight and at the corners of
a route (`dR_route_region`: a route with corner windows stays in the region), the entry chains and
the lanes of the registers.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program}

/-! ### The least `u` of the machine -/

/-- A fold of `min` from `0` is at most every value of the list. -/
theorem dR_foldr_min_le_of_mem {α : Type*} (f : α → ℤ) : ∀ (l : List α) (s : α), s ∈ l →
    l.foldr (fun s m => min m (f s)) 0 ≤ f s
  | [], _, h => by simp at h
  | x :: l, s, h => by
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (dR_foldr_min_le_of_mem f l s h)

/-- **Every piece of the machine has its least `u` at least `uMin`.** -/
theorem dR_uMin_le_piece {g : Piece} (h : g ∈ machPieces p) : uMin p ≤ g.a - g.hi := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
  exact dR_foldr_min_le_of_mem (fun s : PSpec => s.bx.a - s.bx.hi) _ s hs

/-- Membership in the region of the machine. -/
theorem dR_mem_machRegion {c : Cell} : c ∈ machRegion p ↔ uMin p - 300 ≤ c.1 - c.2 := Iff.rfl

/-- **The pieces of the machine lie in its region.** -/
theorem dR_pieces_region (p : Program) : boxesOf (machPieces p) ⊆ machRegion p := by
  intro c hc
  obtain ⟨g, hg, h1, h2, h3, h4⟩ := mem_boxesOf.1 hc
  have := dR_uMin_le_piece hg
  rw [dR_mem_machRegion]
  omega

/-- A set whose cells have `u` at least `uMin - 300` lies in the region. -/
theorem dR_region_of_u {S : Set Cell} (h : ∀ c ∈ S, uMin p - 300 ≤ c.1 - c.2) :
    S ⊆ machRegion p := h

/-! ### Anchors -/

/-- **Module anchor**: group `17` of the register circuit of module `r` (`u = U_r - 738`). -/
theorem dR_uMin_le_mod {r : ℕ} (hr : r < numRegs p) : uMin p ≤ U p r - 738 := by
  have hm := modGroup_mem hr _ (List.mem_map.2 ⟨⟨.dz2g 17, modDX p r, modDY p r, 0⟩,
    List.mem_map.2 ⟨.dz2g 17, List.mem_map.2 ⟨17, List.mem_range.2 (by norm_num), rfl⟩, rfl⟩,
    rfl⟩)
  have h := dR_uMin_le_piece hm
  change uMin p ≤ (-79 + modDX p r) - (659 + modDY p r) at h
  have := modD_uv p r
  omega

/-- **Unit anchor**: copy `0` of the entry chain of unit `a` (`u = A_a - 32`). -/
theorem dR_uMin_le_chain {a t : ℕ} (h : ∀ x ∈ chainPieces p a t, x ∈ machPieces p) :
    uMin p ≤ A p a - 32 := by
  have hm : (⟨.orGate, unitDX p a - 35 * ((0 : ℕ) : ℤ), unitDY p a - 64 * ((0 : ℕ) : ℤ),
      14 * 0 % 30⟩ : PSpec).piece ∈ chainPieces p a t :=
    List.mem_map.2 ⟨_, List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩, rfl⟩
  have h1 := dR_uMin_le_piece (h _ hm)
  change uMin p ≤ (0 + (unitDX p a - 35 * ((0 : ℕ) : ℤ))) -
    (32 + (unitDY p a - 64 * ((0 : ℕ) : ℤ))) at h1
  have := unitD_uv p a
  omega

/-- **Corner anchor**: the reflector of a corner of a route, if it is a piece of the machine,
gives `uMin ≤ u - 5` for the corner point. -/
theorem dR_uMin_le_corner {g : WL} {c : Corner} (h : (reflect g c).1.piece ∈ machPieces p) :
    uMin p ≤ c.u - 5 := by
  have h1 := dR_uMin_le_piece h
  obtain ⟨k, u, v, tag⟩ := c
  change uMin p ≤ ((rfP k).a + rfX k u v) - ((rfP k).hi + rfY k u v) at h1
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rfP, rfX, rfY, rfCU, rfCV] at h1 ⊢ <;> omega

/-! ### Glider boxes -/

/-- The least `u` of the box of the glider of `w` at time `t`. -/
def WL.duLo (w : WL) (t : ℤ) : ℤ := w.px t - w.py t - 4

/-- Every cell of the glider box has `u` at least `duLo`. -/
theorem WL.duLo_le {w : WL} {t : ℤ} {c : Cell} (h : c ∈ w.box t) : w.duLo t ≤ c.1 - c.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold WL.duLo
  omega

/-- A glider box with `duLo` at least `uMin - 300` lies in the region. -/
theorem WL.dbox_region {w : WL} {t : ℤ} (h : uMin p - 300 ≤ w.duLo t) :
    w.box t ⊆ machRegion p :=
  fun _ hc => le_trans h (WL.duLo_le hc)

/-- **Between two times, the least `u` of a glider box is at least the smaller end value.** -/
theorem WL.duLo_between {w : WL} (hd : w.Dir) {t₁ t t₂ : ℤ} (h1 : t₁ ≤ t) (h2 : t ≤ t₂) :
    min (w.duLo t₁) (w.duLo t₂) ≤ w.duLo t := by
  obtain ⟨hx, hy⟩ := hd
  have q1 : (t₁ - w.tau) / 4 ≤ (t - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  have q2 : (t - w.tau) / 4 ≤ (t₂ - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  unfold WL.duLo WL.py WL.px WL.qt
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> omega

/-- **A glider flying with growing `u`** (`dx = 1`, `dy = -1`): `duLo` grows with time. -/
theorem WL.duLo_mono {w : WL} (hx : w.dx = 1) (hy : w.dy = -1) {t₁ t₂ : ℤ} (h : t₁ ≤ t₂) :
    w.duLo t₁ ≤ w.duLo t₂ := by
  have q : (t₁ - w.tau) / 4 ≤ (t₂ - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  unfold WL.duLo WL.py WL.px WL.qt
  rw [hx, hy]
  omega

/-- A glider flying along `u` constant (`dx = dy = 1`): `uLo = lane - 4`. -/
theorem WL.duLo_se {w : WL} (hx : w.dx = 1) (hy : w.dy = 1) (t : ℤ) :
    w.duLo t = w.lane - 4 := by
  unfold WL.duLo WL.py WL.px
  rw [hx, hy]
  ring

/-! ### Corners -/

/-- **The glider at a corner**: on the input line of the corner, at the meeting time, its box is
at most `60` left of the corner point. -/
theorem dR_uLo_meet {g : WL} {c : Corner} (h : OnLine g c) : c.u - 60 ≤ g.duLo (meetT g c) := by
  obtain ⟨dx, dy, lane, tau⟩ := g
  obtain ⟨k, u, v, tag⟩ := c
  have hdx := congrArg WL.dx h
  have hdy := congrArg WL.dy h
  have hl := congrArg WL.lane h
  simp only [WL.shift] at hdx hdy hl
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rfIn] at hdx hdy hl <;> subst hdx hdy <;>
    simp only [WL.duLo, WL.px, WL.py, WL.qt, meetT, delayS, rfIn, rfX, rfY, rfCU,
      rfCV] at hl ⊢ <;> omega

/-- **The glider leaving a corner**: at the end of the reflection its box is at most `60` left of
the corner point. -/
theorem dR_uLo_out (g : WL) (c : Corner) : c.u - 60 ≤ (reflect g c).2.duLo (meetT g c + 30) := by
  obtain ⟨k, u, v, tag⟩ := c
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [reflect, WL.duLo, WL.px, WL.py, WL.qt, WL.shift, meetT, delayS, rfIn, rfOut,
      rfX, rfY, rfCU, rfCV] <;> omega

/-- **A box in the frame of a corner** (relay box, extended relay box): its cells have
`u ≥ u_corner - cu + (a - hi)`. -/
theorem dR_cornerBox_u {c : Corner} {a b lo hi : ℤ} {x : Cell}
    (hx : x ∈ (fun y => cornerV c + y) '' Box a b lo hi) :
    c.u - rfCU c.k + (a - hi) ≤ x.1 - x.2 := by
  obtain ⟨y, ⟨h1, h2, h3, h4⟩, rfl⟩ := hx
  simp only [cornerV, rfX, rfY, Prod.fst_add, Prod.snd_add]
  omega

/-- **The relay box of a corner** is at most `26` left of the corner point. -/
theorem dR_relayBox_u {c : Corner} {x : Cell} (hx : x ∈ relayBox c) : c.u - 26 ≤ x.1 - x.2 := by
  obtain ⟨k, u, v, tag⟩ := c
  obtain ⟨y, hy, rfl⟩ := hx
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> obtain ⟨h1, h2, h3, h4⟩ := hy <;>
    simp only [cornerV, rfX, rfY, rfCU, rfCV, Prod.fst_add, Prod.snd_add] <;> omega

/-- **The glider leaving a corner window**: `40` generations after the meeting time its box is
at most `70` left of the corner point. -/
theorem dR_uLo_out40 (g : WL) (c : Corner) : c.u - 70 ≤ (reflect g c).2.duLo (meetT g c + 40) := by
  obtain ⟨k, u, v, tag⟩ := c
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [reflect, WL.duLo, WL.px, WL.py, WL.qt, WL.shift, meetT, delayS, rfIn, rfOut,
      rfX, rfY, rfCU, rfCV] <;> omega

/-- **The extended relay box of a corner** (`relayBoxX`) is at most `30` left of the corner
point. -/
theorem dR_relayBoxX_u {c : Corner} {x : Cell} (hx : x ∈ relayBoxX c) : c.u - 30 ≤ x.1 - x.2 := by
  obtain ⟨k, u, v, tag⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rxB, rxBox, rfX, rfY, rfCU, rfCV] at h1 h2 h3 h4 ⊢ <;> omega

/-! ### Routes -/

/-- **A route with corner windows stays in the region** (no separation facts): from a glider in
the region, through corners met on their input lines, in order, whose reflectors are pieces of the
machine, the footprint `routeFootX` lies in the region up to the end of the route, and so does the
box of the final glider at the end. -/
theorem dR_route_region : ∀ (cs : List Corner) (g : WL) (T : ℕ), g.Dir → RouteLines g cs →
    RouteTimedX g cs T → (∀ x ∈ (route g cs).1, x.piece ∈ machPieces p) →
    uMin p - 300 ≤ g.duLo T →
    (∀ i, T + i ≤ routeEndX g cs T → routeFootX g cs T i ⊆ machRegion p) ∧
      uMin p - 300 ≤ (route g cs).2.duLo (routeEndX g cs T)
  | [], g, T, _, _, _, _, h0 => by
    refine ⟨fun i hi => ?_, h0⟩
    simp only [routeEndX] at hi
    rw [show i = 0 by omega]
    simpa [routeFootX] using WL.dbox_region h0
  | c :: cs, g, T, hd, ⟨hl, hls⟩, ⟨ht, hts⟩, hmem, h0 => by
    set m := (meetT g c).toNat with hm
    have hmT : ((m : ℕ) : ℤ) = meetT g c := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hc := dR_uMin_le_corner (g := g) (c := c) (hmem _ (by simp [route]))
    have h1 := dR_uLo_meet hl
    have h2 := dR_uLo_out40 g c
    have hts' : RouteTimedX (reflect g c).2 cs ((m + 40 : ℕ) : ℤ) := by
      push_cast
      rw [hmT]
      exact hts
    obtain ⟨ih1, ih2⟩ := dR_route_region cs _ (m + 40) (reflect_dir g c) hls hts'
      (fun x hx => hmem x (by simp [route, hx])) (by push_cast; rw [hmT]; omega)
    refine ⟨fun i hi => ?_, ih2⟩
    simp only [routeEndX, ← hm] at hi
    simp only [routeFootX, ← hm]
    split_ifs with ha hb
    · exact WL.dbox_region (le_trans (le_min (by omega) (by omega))
        (WL.duLo_between hd (t₁ := T) (t₂ := meetT g c) (by omega) (by omega)))
    · intro x hx
      have := dR_relayBoxX_u hx
      rw [dR_mem_machRegion]
      omega
    · exact ih1 _ (by omega)

/-! ### Units -/

/-- **The entry chain** of unit `a` from any copy lies in the region (`u ≥ A_a - 60`). -/
theorem dR_entryFoot_region {a : ℕ} (t : ℕ) (h : uMin p ≤ A p a - 32) :
    entryFoot p a t ⊆ machRegion p := by
  refine (entryFoot_subset_crude p a t).trans ?_
  rintro _ ⟨c, ⟨j, hj, h1, h2, h3, h4⟩, rfl⟩
  have := unitD_uv p a
  rw [dR_mem_machRegion]
  simp only [Prod.fst_add, Prod.snd_add] at *
  omega

/-- **The flight out of the entry chain** of unit `a` lies in the region (`u ≥ A_a + 10`). -/
theorem dR_chainOut_region {a : ℕ} (h : uMin p ≤ A p a - 32) (t : ℤ) :
    (fun c => (unitDX p a, unitDY p a) + c) '' chainOutWL.box t ⊆ machRegion p := by
  rintro _ ⟨c, hc, rfl⟩
  have h1 := WL.duLo_le hc
  rw [WL.duLo_se (w := chainOutWL) rfl rfl] at h1
  have := unitD_uv p a
  rw [dR_mem_machRegion]
  simp only [Prod.fst_add, Prod.snd_add, chainOutWL] at *
  omega

/-! ### Module -/

/-- **The lanes of register `r`** lie in the region (`u ≥ U_r - 113`). -/
theorem dR_modLanes_region {r : ℕ} (h : uMin p ≤ U p r - 738) : modLanes p r ⊆ machRegion p := by
  rintro _ ⟨c, ⟨c1, c2, c3⟩, rfl⟩
  have := modD_uv p r
  rw [dR_mem_machRegion]
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-! ### Tools for the `decJz` footprints -/

/-- A glider flying `NW` (`dx = dy = -1`): `duLo = -lane - 4`, constant. -/
theorem WL.duLo_nw {w : WL} (hx : w.dx = -1) (hy : w.dy = -1) (t : ℤ) :
    w.duLo t = -w.lane - 4 := by
  unfold WL.duLo WL.py WL.px
  rw [hx, hy]
  ring

/-- **A route followed by a flight stays in the region**, if the least `u` of the final glider
does not decrease after the end of the route. -/
theorem dR_flyFoot_region {g : WL} {cs : List Corner} {T : ℕ} (hd : g.Dir) (hl : RouteLines g cs)
    (ht : RouteTimedX g cs T) (hmem : ∀ x ∈ (route g cs).1, x.piece ∈ machPieces p)
    (h0 : uMin p - 300 ≤ g.duLo T)
    (hmono : ∀ t : ℕ, routeEndX g cs T ≤ t →
      (route g cs).2.duLo (routeEndX g cs T) ≤ (route g cs).2.duLo t) (t : ℕ) :
    flyFoot g cs T t ⊆ machRegion p := by
  obtain ⟨h1, h2⟩ := dR_route_region cs g T hd hl ht hmem h0
  have hT := le_routeEndX cs g T ht
  unfold flyFoot
  split_ifs with h
  · exact h1 _ (by omega)
  · exact WL.dbox_region (h2.trans (hmono t (by omega)))

/-- A set placed by `v` from a set inside a box lies at `u ≥ v.1 - v.2 + a - hi`. -/
theorem dR_translate_u {v : Cell} {S : Finset Cell} {a b lo hi : ℤ}
    (hS : (S : Set Cell) ⊆ Box a b lo hi) {c : Cell} (hc : c ∈ (translate v S : Set Cell)) :
    v.1 - v.2 + (a - hi) ≤ c.1 - c.2 := by
  rw [mem_coe, mem_translate] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hS (mem_coe.2 hc)
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  omega

/-- An image by `v` of a box lies at `u ≥ v.1 - v.2 + a - hi`. -/
theorem dR_image_box_u {v : Cell} {a b lo hi : ℤ} {c : Cell}
    (hc : c ∈ (fun d => v + d) '' Box a b lo hi) : v.1 - v.2 + (a - hi) ≤ c.1 - c.2 := by
  obtain ⟨d, ⟨h1, h2, h3, h4⟩, rfl⟩ := hc
  simp only [Prod.fst_add, Prod.snd_add]
  omega

end LP

end LeanTheory.Life
