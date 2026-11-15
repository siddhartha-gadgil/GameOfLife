/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncPlan

/-!
# The region facts of the `inc` activation

Research note `N-22`, item (h): the hypothesis `IncRegion` of `inc_step` is discharged. Every
footprint of the activation lies in `machRegion p = {c | uMin p - 300 ≤ u}` (`u = x - y`).

The proof rests on **anchors**: pieces of the machine near each footprint, whose `u` bounds
`uMin p` from above (`uMin_le_piece`, by the definition of `uMin` as a fold).

* Pieces: by definition (`pieces_region`).
* Module `r`: the register group `dz2g 17` gives `uMin ≤ U_r - 738` (`uMin_le_mod`). The lanes
  of the register (`u ≥ U_r - 113`), the INC gate, the flights to and from `RF_J`, its relay box
  and the run regions (`incRunBox`, every component at `u ≥ -738` in the module frame,
  `incRunBox_u`) lie above `U_r - 738 - 300`.
* Units: copy `0` of an entry chain gives `uMin ≤ A_a - 32` (`uMin_le_chain`), the body of an
  `inc` unit `uMin ≤ A_a - 36` (`uMin_le_body`); the body box (`u ≥ A_i - 173`), the entry chains
  (`u ≥ A_a - 60`) and the flight out of a chain (`u ≥ A_a + 10`) lie above.
* Routes with corner windows (`route_region`, footprint `routeFootX`), **without separation
  facts**: every corner is a placed reflector, so `uMin ≤ c.u - 5` (`uMin_le_corner`); the glider
  box at the meeting time is at most `60` left of the corner (`uLo_meet`), `40` generations later
  at most `70` (`uLo_out40`), the extended relay box `relayBoxX` at most `30` (`relayBoxX_u`;
  also `uLo_out`, `relayBox_u`, `cornerBox_u`), and between two times the least `u` of a glider
  box is at least the smaller of its values at the ends (`WL.uLo_between`).
  After a route, a glider flying `NE`/`SW` with growing `u` stays in the region (`WL.uLo_mono`).

The register part after the increment (`modRunFoot` beyond `946`) uses the region statement of
`module_run_n`, which needs the separation facts of the module part (fields `gate`, `fl1`, `rf`,
`fl2`, `modLane`, `grpLane`, `inc` of `IncSep`); the route separation fields are not used.

`inc_step'` is `inc_step` with `IncRegion` discharged: only `IncSep` remains.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program}

/-! ### The least `u` of the machine -/

/-- A fold of `min` from `0` is at most every value of the list. -/
theorem foldr_min_le_of_mem {α : Type*} (f : α → ℤ) : ∀ (l : List α) (s : α), s ∈ l →
    l.foldr (fun s m => min m (f s)) 0 ≤ f s
  | [], _, h => by simp at h
  | x :: l, s, h => by
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (foldr_min_le_of_mem f l s h)

/-- **Every piece of the machine has its least `u` at least `uMin`.** -/
theorem uMin_le_piece {g : Piece} (h : g ∈ machPieces p) : uMin p ≤ g.a - g.hi := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
  exact foldr_min_le_of_mem (fun s : PSpec => s.bx.a - s.bx.hi) _ s hs

/-- Membership in the region of the machine. -/
theorem mem_machRegion {c : Cell} : c ∈ machRegion p ↔ uMin p - 300 ≤ c.1 - c.2 := Iff.rfl

/-- **The pieces of the machine lie in its region.** -/
theorem pieces_region (p : Program) : boxesOf (machPieces p) ⊆ machRegion p := by
  intro c hc
  obtain ⟨g, hg, h1, h2, h3, h4⟩ := mem_boxesOf.1 hc
  have := uMin_le_piece hg
  rw [mem_machRegion]
  omega

/-- A set whose cells have `u` at least `uMin - 300` lies in the region. -/
theorem region_of_u {S : Set Cell} (h : ∀ c ∈ S, uMin p - 300 ≤ c.1 - c.2) :
    S ⊆ machRegion p := h

/-! ### Anchors -/

/-- **Module anchor**: group `17` of the register circuit of module `r` (`u = U_r - 738`). -/
theorem uMin_le_mod {r : ℕ} (hr : r < numRegs p) : uMin p ≤ U p r - 738 := by
  have hm := moduleSpecs_mem hr (s := ⟨.dz2g 17, modDX p r, modDY p r, 0⟩)
    (mem_moduleSpecs_head (List.mem_append_left _
      (List.mem_map.2 ⟨.dz2g 17, List.mem_map.2 ⟨17, List.mem_range.2 (by norm_num), rfl⟩,
        rfl⟩)))
  have h := uMin_le_piece hm
  change uMin p ≤ (-79 + modDX p r) - (659 + modDY p r) at h
  have := modD_uv p r
  omega

/-- **Unit anchor**: copy `0` of the entry chain of unit `a` (`u = A_a - 32`). -/
theorem uMin_le_chain {a t : ℕ} (h : ∀ x ∈ chainPieces p a t, x ∈ machPieces p) :
    uMin p ≤ A p a - 32 := by
  have hm : (⟨.orGate, unitDX p a - 35 * ((0 : ℕ) : ℤ), unitDY p a - 64 * ((0 : ℕ) : ℤ),
      14 * 0 % 30⟩ : PSpec).piece ∈ chainPieces p a t :=
    List.mem_map.2 ⟨_, List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩, rfl⟩
  have h1 := uMin_le_piece (h _ hm)
  change uMin p ≤ (0 + (unitDX p a - 35 * ((0 : ℕ) : ℤ))) -
    (32 + (unitDY p a - 64 * ((0 : ℕ) : ℤ))) at h1
  have := unitD_uv p a
  omega

/-- **Body anchor**: group `0` of the body of the `inc` unit `i` (`u = A_i - 36`). -/
theorem uMin_le_body {i : ℕ} (h : ∀ x ∈ bodyGroup p i, x ∈ machPieces p) :
    uMin p ≤ A p i - 36 := by
  have hm : (⟨.bodyInc 0, unitDX p i, unitDY p i, 0⟩ : PSpec).piece ∈ bodyGroup p i :=
    List.mem_map.2 ⟨_, List.mem_map.2 ⟨.bodyInc 0,
      List.mem_map.2 ⟨0, List.mem_range.2 (by norm_num), rfl⟩, rfl⟩, rfl⟩
  have h1 := uMin_le_piece (h _ hm)
  change uMin p ≤ (134 + unitDX p i) - (170 + unitDY p i) at h1
  have := unitD_uv p i
  omega

/-- **Corner anchor**: the reflector of a corner of a route, if it is a piece of the machine,
gives `uMin ≤ u - 5` for the corner point. -/
theorem uMin_le_corner {g : WL} {c : Corner} (h : (reflect g c).1.piece ∈ machPieces p) :
    uMin p ≤ c.u - 5 := by
  have h1 := uMin_le_piece h
  obtain ⟨k, u, v, tag⟩ := c
  change uMin p ≤ ((rfP k).a + rfX k u v) - ((rfP k).hi + rfY k u v) at h1
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rfP, rfX, rfY, rfCU, rfCV] at h1 ⊢ <;> omega

/-! ### Glider boxes -/

/-- The least `u` of the box of the glider of `w` at time `t`. -/
def WL.uLo (w : WL) (t : ℤ) : ℤ := w.px t - w.py t - 4

/-- Every cell of the glider box has `u` at least `uLo`. -/
theorem WL.uLo_le {w : WL} {t : ℤ} {c : Cell} (h : c ∈ w.box t) : w.uLo t ≤ c.1 - c.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold WL.uLo
  omega

/-- A glider box with `uLo` at least `uMin - 300` lies in the region. -/
theorem WL.box_region {w : WL} {t : ℤ} (h : uMin p - 300 ≤ w.uLo t) :
    w.box t ⊆ machRegion p :=
  fun _ hc => le_trans h (WL.uLo_le hc)

/-- **Between two times, the least `u` of a glider box is at least the smaller end value.** -/
theorem WL.uLo_between {w : WL} (hd : w.Dir) {t₁ t t₂ : ℤ} (h1 : t₁ ≤ t) (h2 : t ≤ t₂) :
    min (w.uLo t₁) (w.uLo t₂) ≤ w.uLo t := by
  obtain ⟨hx, hy⟩ := hd
  have q1 : (t₁ - w.tau) / 4 ≤ (t - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  have q2 : (t - w.tau) / 4 ≤ (t₂ - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  unfold WL.uLo WL.py WL.px WL.qt
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> omega

/-- **A glider flying with growing `u`** (`dx = 1`, `dy = -1`): `uLo` grows with time. -/
theorem WL.uLo_mono {w : WL} (hx : w.dx = 1) (hy : w.dy = -1) {t₁ t₂ : ℤ} (h : t₁ ≤ t₂) :
    w.uLo t₁ ≤ w.uLo t₂ := by
  have q : (t₁ - w.tau) / 4 ≤ (t₂ - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  unfold WL.uLo WL.py WL.px WL.qt
  rw [hx, hy]
  omega

/-- A glider flying along `u` constant (`dx = dy = 1`): `uLo = lane - 4`. -/
theorem WL.uLo_se {w : WL} (hx : w.dx = 1) (hy : w.dy = 1) (t : ℤ) :
    w.uLo t = w.lane - 4 := by
  unfold WL.uLo WL.py WL.px
  rw [hx, hy]
  ring

/-! ### Corners -/

/-- **The glider at a corner**: on the input line of the corner, at the meeting time, its box is
at most `60` left of the corner point. -/
theorem uLo_meet {g : WL} {c : Corner} (h : OnLine g c) : c.u - 60 ≤ g.uLo (meetT g c) := by
  obtain ⟨dx, dy, lane, tau⟩ := g
  obtain ⟨k, u, v, tag⟩ := c
  have hdx := congrArg WL.dx h
  have hdy := congrArg WL.dy h
  have hl := congrArg WL.lane h
  simp only [WL.shift] at hdx hdy hl
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rfIn] at hdx hdy hl <;> subst hdx hdy <;>
    simp only [WL.uLo, WL.px, WL.py, WL.qt, meetT, delayS, rfIn, rfX, rfY, rfCU,
      rfCV] at hl ⊢ <;> omega

/-- **The glider leaving a corner**: at the end of the reflection its box is at most `60` left of
the corner point. -/
theorem uLo_out (g : WL) (c : Corner) : c.u - 60 ≤ (reflect g c).2.uLo (meetT g c + 30) := by
  obtain ⟨k, u, v, tag⟩ := c
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [reflect, WL.uLo, WL.px, WL.py, WL.qt, WL.shift, meetT, delayS, rfIn, rfOut,
      rfX, rfY, rfCU, rfCV] <;> omega

/-- **A box in the frame of a corner** (relay box, extended relay box): its cells have
`u ≥ u_corner - cu + (a - hi)`. -/
theorem cornerBox_u {c : Corner} {a b lo hi : ℤ} {x : Cell}
    (hx : x ∈ (fun y => cornerV c + y) '' Box a b lo hi) :
    c.u - rfCU c.k + (a - hi) ≤ x.1 - x.2 := by
  obtain ⟨y, ⟨h1, h2, h3, h4⟩, rfl⟩ := hx
  simp only [cornerV, rfX, rfY, Prod.fst_add, Prod.snd_add]
  omega

/-- **The relay box of a corner** is at most `26` left of the corner point. -/
theorem relayBox_u {c : Corner} {x : Cell} (hx : x ∈ relayBox c) : c.u - 26 ≤ x.1 - x.2 := by
  obtain ⟨k, u, v, tag⟩ := c
  obtain ⟨y, hy, rfl⟩ := hx
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> obtain ⟨h1, h2, h3, h4⟩ := hy <;>
    simp only [cornerV, rfX, rfY, rfCU, rfCV, Prod.fst_add, Prod.snd_add] <;> omega

/-- **The glider leaving a corner window**: `40` generations after the meeting time its box is
at most `70` left of the corner point. -/
theorem uLo_out40 (g : WL) (c : Corner) : c.u - 70 ≤ (reflect g c).2.uLo (meetT g c + 40) := by
  obtain ⟨k, u, v, tag⟩ := c
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [reflect, WL.uLo, WL.px, WL.py, WL.qt, WL.shift, meetT, delayS, rfIn, rfOut,
      rfX, rfY, rfCU, rfCV] <;> omega

/-- **The extended relay box of a corner** (`relayBoxX`) is at most `30` left of the corner
point. -/
theorem relayBoxX_u {c : Corner} {x : Cell} (hx : x ∈ relayBoxX c) : c.u - 30 ≤ x.1 - x.2 := by
  obtain ⟨k, u, v, tag⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rxB, rxBox, rfX, rfY, rfCU, rfCV] at h1 h2 h3 h4 ⊢ <;> omega

/-! ### Routes -/

/-- **A route with corner windows stays in the region** (no separation facts): from a glider in
the region, through corners met on their input lines, in order, whose reflectors are pieces of the
machine, the footprint `routeFootX` lies in the region up to the end of the route, and so does the
box of the final glider at the end. -/
theorem route_region : ∀ (cs : List Corner) (g : WL) (T : ℕ), g.Dir → RouteLines g cs →
    RouteTimedX g cs T → (∀ x ∈ (route g cs).1, x.piece ∈ machPieces p) →
    uMin p - 300 ≤ g.uLo T →
    (∀ i, T + i ≤ routeEndX g cs T → routeFootX g cs T i ⊆ machRegion p) ∧
      uMin p - 300 ≤ (route g cs).2.uLo (routeEndX g cs T)
  | [], g, T, _, _, _, _, h0 => by
    refine ⟨fun i hi => ?_, h0⟩
    simp only [routeEndX] at hi
    rw [show i = 0 by omega]
    simpa [routeFootX] using WL.box_region h0
  | c :: cs, g, T, hd, ⟨hl, hls⟩, ⟨ht, hts⟩, hmem, h0 => by
    set m := (meetT g c).toNat with hm
    have hmT : ((m : ℕ) : ℤ) = meetT g c := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hc := uMin_le_corner (g := g) (c := c) (hmem _ (by simp [route]))
    have h1 := uLo_meet hl
    have h2 := uLo_out40 g c
    have hts' : RouteTimedX (reflect g c).2 cs ((m + 40 : ℕ) : ℤ) := by
      push_cast
      rw [hmT]
      exact hts
    obtain ⟨ih1, ih2⟩ := route_region cs _ (m + 40) (reflect_dir g c) hls hts'
      (fun x hx => hmem x (by simp [route, hx])) (by push_cast; rw [hmT]; omega)
    refine ⟨fun i hi => ?_, ih2⟩
    simp only [routeEndX, ← hm] at hi
    simp only [routeFootX, ← hm]
    split_ifs with ha hb
    · exact WL.box_region (le_trans (le_min (by omega) (by omega))
        (WL.uLo_between hd (t₁ := T) (t₂ := meetT g c) (by omega) (by omega)))
    · intro x hx
      have := relayBoxX_u hx
      rw [mem_machRegion]
      omega
    · exact ih1 _ (by omega)

/-- **A link into an entry chain stays in the region** (`linkFootX`): the route, the flight with
growing `u` after it, and the entry chain (assumed in the region). -/
theorem linkFoot_region {a t : ℕ} {g : WL} {cs : List Corner} {T T0 : ℕ} (hd : g.Dir)
    (hl : RouteLines g cs) (htim : RouteTimedX g cs T)
    (hmem : ∀ x ∈ (route g cs).1, x.piece ∈ machPieces p) (h0 : uMin p - 300 ≤ g.uLo T)
    (hdx : (route g cs).2.dx = 1) (hdy : (route g cs).2.dy = -1)
    (hent : entryFoot p a t ⊆ machRegion p) (j : ℕ) :
    linkFootX p a t g cs T T0 j ⊆ machRegion p := by
  obtain ⟨h1, h2⟩ := route_region cs g T hd hl htim hmem h0
  unfold linkFootX
  split_ifs with ha hb
  · exact h1 j ha
  · exact WL.box_region (h2.trans (WL.uLo_mono hdx hdy (by omega)))
  · exact hent

/-! ### Units -/

/-- **The box of the body** of unit `i` lies in the region (`u ≥ A_i - 173`). -/
theorem bodyBox_region {i : ℕ} (h : uMin p ≤ A p i - 36) : bodyBox p i ⊆ machRegion p := by
  rintro _ ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩
  have := unitD_uv p i
  rw [mem_machRegion]
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- **The entry chain** of unit `a` from any copy lies in the region (`u ≥ A_a - 60`). -/
theorem entryFoot_region {a : ℕ} (t : ℕ) (h : uMin p ≤ A p a - 32) :
    entryFoot p a t ⊆ machRegion p := by
  refine (entryFoot_subset_crude p a t).trans ?_
  rintro _ ⟨c, ⟨j, hj, h1, h2, h3, h4⟩, rfl⟩
  have := unitD_uv p a
  rw [mem_machRegion]
  simp only [Prod.fst_add, Prod.snd_add] at *
  omega

/-- **The flight out of the entry chain** of unit `a` lies in the region (`u ≥ A_a + 10`). -/
theorem chainOut_region {a : ℕ} (h : uMin p ≤ A p a - 32) (t : ℤ) :
    (fun c => (unitDX p a, unitDY p a) + c) '' chainOutWL.box t ⊆ machRegion p := by
  rintro _ ⟨c, hc, rfl⟩
  have h1 := WL.uLo_le hc
  rw [WL.uLo_se (w := chainOutWL) rfl rfl] at h1
  have := unitD_uv p a
  rw [mem_machRegion]
  simp only [Prod.fst_add, Prod.snd_add, chainOutWL] at *
  omega

/-! ### Module -/

/-- **The lanes of register `r`** lie in the region (`u ≥ U_r - 113`). -/
theorem modLanes_region {r : ℕ} (h : uMin p ≤ U p r - 738) : modLanes p r ⊆ machRegion p := by
  rintro _ ⟨c, ⟨c1, c2, c3⟩, rfl⟩
  have := modD_uv p r
  rw [mem_machRegion]
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- Every member of a list of sets lies in `S`. -/
def AllSub (S : Set Cell) : List (Set Cell) → Prop
  | [] => True
  | X :: L => X ⊆ S ∧ AllSub S L

/-- The union of a list of subsets of `S` lies in `S`. -/
theorem unionL_subset_of {S : Set Cell} : ∀ {L : List (Set Cell)}, AllSub S L → unionL L ⊆ S
  | [], _ => fun _ h => h.elim
  | _ :: _, ⟨h, hL⟩ => Set.union_subset h (unionL_subset_of hL)

/-- A component with `a - hi ≥ m` or `U₁ ≥ m` lies at `u ≥ m`. -/
theorem BU_subset_u {m a b lo hi U₁ U₂ V₁ V₂ : ℤ} (h : m ≤ a - hi ∨ m ≤ U₁) :
    BU a b lo hi U₁ U₂ V₁ V₂ ⊆ {c : Cell | m ≤ c.1 - c.2} := by
  rintro c ⟨⟨c1, c2, c3, c4⟩, c5, c6, c7, c8⟩
  change m ≤ c.1 - c.2
  omega

/-- The lanes of the register lie at `u ≥ -113`. -/
theorem regLanes_subset_u {m : ℤ} (h : m ≤ -113) : regLanes ⊆ {c : Cell | m ≤ c.1 - c.2} := by
  rintro c ⟨c1, c2, c3⟩
  change m ≤ c.1 - c.2
  omega

/-- The components of `dz2e` lie at `u ≥ -738`. -/
theorem dz2eRegL_u : AllSub {c : Cell | -738 ≤ c.1 - c.2} dz2eRegL := by
  simp only [dz2eRegL, AllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u (by omega) | exact regLanes_subset_u (by omega) | trivial

/-- The components of `dz2e1` lie at `u ≥ -738`. -/
theorem dz2e1RegL_u : AllSub {c : Cell | -738 ≤ c.1 - c.2} dz2e1RegL := by
  simp only [dz2e1RegL, AllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u (by omega) | exact regLanes_subset_u (by omega) | trivial

/-- The components of `dz2e2` lie at `u ≥ -738`. -/
theorem dz2e2RegL_u : AllSub {c : Cell | -738 ≤ c.1 - c.2} dz2e2RegL := by
  simp only [dz2e2RegL, AllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u (by omega) | exact regLanes_subset_u (by omega) | trivial

/-- The components of `dz2e3` lie at `u ≥ -738`. -/
theorem dz2e3RegL_u : AllSub {c : Cell | -738 ≤ c.1 - c.2} dz2e3RegL := by
  simp only [dz2e3RegL, AllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u (by omega) | exact regLanes_subset_u (by omega) | trivial

/-- The components of `dz2j` lie at `u ≥ -738`. -/
theorem dz2jRegL_u : AllSub {c : Cell | -738 ≤ c.1 - c.2} dz2jRegL := by
  simp only [dz2jRegL, AllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u (by omega) | exact regLanes_subset_u (by omega) | trivial

/-- **The region of the increment runs lies at `u ≥ -738`** (module frame). -/
theorem incRunBox_u : incRunBox ⊆ {c : Cell | -738 ≤ c.1 - c.2} := by
  unfold incRunBox dz2eRegion dz2e1Region dz2e2Region dz2e3Region dz2jRegion
  exact Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
    (unionL_subset_of dz2eRegL_u) (unionL_subset_of dz2e1RegL_u))
    (unionL_subset_of dz2e2RegL_u)) (unionL_subset_of dz2e3RegL_u))
    (unionL_subset_of dz2jRegL_u)

/-- **The increment runs placed at module `r`** lie in the region. -/
theorem incRunBox_region {r : ℕ} (h : uMin p ≤ U p r - 738) :
    (fun c => (modDX p r, modDY p r) + c) '' incRunBox ⊆ machRegion p := by
  rintro _ ⟨c, hc, rfl⟩
  have h1 : -738 ≤ c.1 - c.2 := incRunBox_u hc
  have := modD_uv p r
  rw [mem_machRegion]
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- **The module part before the increment** (gate, flight to `RF_J`, `RF_J`, flight to the
increment) lies in the region. -/
theorem modFoot_region {r : ℕ} (h : uMin p ≤ U p r - 738) {k : ℤ} {Tg : ℕ}
    (hTg : (Tg : ℤ) = 194 + 30 * k) (j : ℕ) : modFoot p r k Tg j ⊆ machRegion p := by
  have hU := modD_uv p r
  have hE := U_even p r
  unfold modFoot
  split_ifs with h1 h2 h3
  · rintro _ ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩
    rw [mem_machRegion]
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · refine WL.box_region ?_
    rw [WL.uLo_se rfl rfl]
    simp only [gateOutWL, modWL, WL.shift]
    omega
  · intro x hx
    have := relayBox_u hx
    simp only [rfJCorner] at this
    rw [mem_machRegion]
    omega
  · refine WL.box_region ?_
    simp only [WL.uLo, WL.px, WL.py, WL.qt, rfJOutWL, modWL, incInWL, WL.shift, modDX,
      modDY] at hU ⊢
    omega

/-! ### The region facts of the activation -/

/-- **The region facts of the `inc` activation**, from the plan facts and the separation facts
of the module part: every footprint lies in the region of the machine. -/
theorem IncPlan.region {i r : ℕ} (hp : p.WellFormed) (P : IncPlan p i r) (hv : P.Valid)
    {R0 : RegS} (hR : R0.Ready) (hs : IncSep P R0) (hr : r < numRegs p) : IncRegion P R0 := by
  have hPc := pieces_region p
  have hU : ∀ r' < numRegs p, uMin p ≤ U p r' - 738 := fun r' h => uMin_le_mod h
  have hAi1 : uMin p ≤ A p ((i + 1 : ℕ) : ℤ) - 32 :=
    uMin_le_chain (t := P.tc) fun x hx => hv.memC x (List.mem_append_right _ hx)
  have hAm : uMin p ≤ A p ((mergeUnit p r : ℕ) : ℤ) - 32 :=
    uMin_le_chain (t := P.tl) fun x hx => hv.memI x (by simp [IncPlan.LIraw, hx])
  have hAi : uMin p ≤ A p i - 36 := uMin_le_body hv.memB
  have hLC : boxesOf (dd P.LCraw) ⊆ machRegion p := by
    rw [boxesOf_dd]
    exact (boxesOf_subset hv.memC).trans hPc
  have hLI : boxesOf (dd P.LIraw) ⊆ machRegion p := by
    rw [boxesOf_dd]
    exact (boxesOf_subset hv.memI).trans hPc
  have hui := unitD_uv p i
  have hum := unitD_uv p (mergeUnit p r)
  refine ⟨hPc, bodyBox_region hAi, fun j hj => Set.union_subset ?_ ?_,
    fun r' h => modLanes_region (hU r' h)⟩
  · -- the continue thread
    unfold IncPlan.contFoot
    split_ifs with h1
    · refine Set.union_subset hLC (linkFoot_region ⟨Or.inl rfl, Or.inl rfl⟩ hv.linesC
        hv.timedC (fun x hx => hv.memC _ (List.mem_append_left _ (List.mem_map_of_mem hx)))
        ?_ ((congrArg WL.dx hv.finC).trans rfl)
          ((congrArg WL.dy hv.finC).trans rfl) (entryFoot_region _ hAi1) j)
      rw [WL.uLo_se rfl rfl]
      simp only [unitWL, incDWL, WL.shift]
      omega
    · exact Set.union_subset hLC (chainOut_region hAi1 _)
  · -- the increment thread
    have hlate := hv.late
    have hT0 := le_routeEndX P.csR (unitWL p i incRWL) 2010 hv.timedR
    have hT1 := le_routeEndX P.csM P.gM P.T1 hv.timedM
    have hendR := hv.endR
    have hendM := hv.endM
    have hTg2 : 2010 ≤ P.Tg := by
      simp only [IncPlan.eM, IncPlan.T1] at hT1 hendM ⊢
      omega
    obtain ⟨hM1, hM2⟩ := route_region P.csM P.gM P.T1 ⟨Or.inl rfl, Or.inl rfl⟩ hv.linesM
      hv.timedM (fun x hx => hv.memI _ (by simp [IncPlan.LIraw, List.mem_map_of_mem hx])) (by
        rw [WL.uLo_se rfl rfl]
        simp only [IncPlan.gM, unitWL, haltDWL, WL.shift]
        omega)
    unfold IncPlan.incFoot
    split_ifs with h1
    · refine Set.union_subset ?_ ((regStrip_subset hR.1 p r j).trans (modLanes_region (hU r hr)))
      unfold IncPlan.earlyFoot
      split_ifs
      · refine Set.union_subset hLI (linkFoot_region ⟨Or.inl rfl, Or.inl rfl⟩ hv.linesR
          hv.timedR (fun x hx => hv.memI _ (by simp [IncPlan.LIraw, List.mem_map_of_mem hx]))
          ?_ ((congrArg WL.dx hv.finR).trans rfl)
          ((congrArg WL.dy hv.finR).trans rfl) (entryFoot_region _ hAm) j)
        rw [WL.uLo_se rfl rfl]
        simp only [unitWL, incRWL, WL.shift]
        omega
      · exact Set.union_subset hLI (hM1 _ (by
          change P.T1 + (j - (P.T1 - 2010)) ≤ P.eM
          omega))
      · refine Set.union_subset hLI (WL.box_region (hM2.trans (WL.uLo_mono ?_ ?_ ?_)))
        · exact (congrArg WL.dx hv.finM).trans rfl
        · exact (congrArg WL.dy hv.finM).trans rfl
        · change ((P.eM : ℕ) : ℤ) ≤ _
          omega
    · have hL := dd_pairwise (machPieces_sep p hp) hv.memI
      have memI : ∀ x ∈ P.LIraw, x ∈ dd P.LIraw := fun x hx => mem_dd.2 hx
      obtain ⟨R', -, -, hsub, -⟩ := module_run_n p r hL (memI _ (by simp [IncPlan.LIraw]))
        (memI _ (by simp [IncPlan.LIraw])) (fun x hx => memI _ (by simp [IncPlan.LIraw, hx]))
        hv.δmR hv.TgE (hR.later (P.Tg - 2010))
        (fun h hh hn => hs.gate h (mem_dd.1 hh) hn)
        (fun j h1 h2 h hh => hs.fl1 j h1 h2 h (mem_dd.1 hh))
        (fun h hh hn => hs.rf h (mem_dd.1 hh) hn)
        (fun j h1 h2 h hh => hs.fl2 j h1 h2 h (mem_dd.1 hh)) hs.modLane hs.grpLane
        (P.Tend - P.Tg - 946) (by omega)
        (fun j hj h hh hn => hs.inc _ ((hR.later _).later 946) j hj h (mem_dd.1 hh) hn)
      unfold modRunFoot
      split_ifs with h2
      · exact Set.union_subset (Set.union_subset hLI (modFoot_region (hU r hr) hv.TgE _))
          ((regStrip_subset (hR.later _).1 p r _).trans (modLanes_region (hU r hr)))
      · refine Set.union_subset hLI ((hsub _ (by omega)).trans (Set.union_subset
          (Set.union_subset (incRunBox_region (hU r hr)) ?_) (modLanes_region (hU r hr))))
        exact (boxesOf_subset fun x hx => hv.memI x (by simp [IncPlan.LIraw, hx])).trans hPc

/-! ### The `inc` step -/

/-- **The `inc` step with the region facts discharged**: for a well-formed program and a state
with the instruction `inc r` at the program counter (register `r` ready), the machine evolves
`encM s` into `encM s'` for the next state `s'` of the counter machine, inside the region of the
machine, in `τ > 0` generations with every other register `τ` generations later — given the
separation facts of the activation plan read off the layout. -/
theorem inc_step' {r : ℕ} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hins : p[s.pc]? = some (.inc r)) (hready : (s.reg r).Ready)
    (hsep : IncSep (incPlan p s.pc r) ((s.reg r).later 930)) :
    ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ (∀ r', r' ≠ r → s'.reg r' = (s.reg r').later τ) ∧
      p.step s.cfg = some s'.cfg ∧ InvM p s' ∧ (s'.reg r).Ready ∧
      conway.evolve τ (encM p s) = encM p s' ∧
      ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p :=
  inc_step hp s hinv hins hready hsep
    ((incPlan p s.pc r).region hp (incPlan_valid hp hins) (hready.later 930) hsep
      (lt_numRegs_of_inc hins))

end LP

end LeanTheory.Life
