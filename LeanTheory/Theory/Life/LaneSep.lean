/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncRegion
public import LeanTheory.Theory.Life.ActivationHalt

/-!
# The register lanes are clear of the machine (`R-31` #14–#17)

Research note `N-22`, report `R-31` §3, rows 14–17: the diagonal of register `r` lives in its
lanes `modLanes p r` (module frame `-113 ≤ u ≤ -69`, `v ≥ 354`, `RunFoot.regLanes`; the strip of
a valid register lies in them, `regStrip_subset`). This module proves, for every program, that
the lanes are far (`FarApart 2`) from the rest of the machine:

* `LaneClear p r S`: every cell of `S` is `≥ 5` beside the lanes of `r` in `u = x - y` or `≥ 5`
  below them in `v = x + y`; `LaneClear.farApart` turns it into `FarApart 2 S (modLanes p r)`.
  `ModNear p r S` (every cell low, or in the `u`-band `[U_r - 750, U_r + 900]` of module `r`)
  gives `LaneClear` for every other register (`ModNear.laneClear`).
* **Lanes of distinct registers** (`modLanes_far`, #16): `U_{r+1} - U_r = P_M ≥ 2940`.
* **Every piece of the machine** (`machPieces_laneClear`, #14, #15, #17): unit pieces and the
  corners of the band, the halt line and the slabs are at `v ≤ -117 + V_T`; left-zone corners are
  `≥ 768` left of their module's lanes, right-zone corners `≥ 1205` right; the pieces of a module
  are inside its `u`-band; the pieces of the module's own register circuit (`lane_dz2g_lane`, the 28
  groups), stations, eaters, `RF_J`, the INC gate and the DEC chain are beside or below the lanes
  (every group of the circuit within `u ∈ [-122, -60]` of the module frame ends at `v ≤ 260`).
* The body box of a unit (`lane_bodyBox_low`), the entry chains (`lane_entryFoot_low`) and the
  flight out of
  a chain (`lane_chainOut_low`) are low.
* **Routes**: `WL.vHi` (the largest `v` of a glider box) is monotone between two times along a
  world line (`WL.vHi_between`), constant on a `NE`/`SW` line (`WL.vHi_const`), at most `70` above
  the corner point at the meeting time (`lane_vHi_meet`) and `40` generations later
  (`lane_vHi_out40`); the extended relay box is at most `70` above it (`lane_relayBoxX_v`). Hence
  `lane_route_vlow`: a route whose
  corners are low has a low footprint `routeFootX`, and `lane_linkFoot_vlow` for `linkFootX`.
* The module part before the increment (`lane_modFoot_u`: `u ∈ [U_r + 99, U_r + 300]`) and the
  run of the increment (`lane_incRun_sub`, `lane_incRunBox_near`: inside the band of the module, or
  in the lanes of
  its own register).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program}

/-! ### Sets clear of the lanes -/

/-- **A set clear of the lanes of register `r`**: every cell is at least `5` left or right (in
`u = x - y`) of the lanes, or at least `5` below them (in `v = x + y`). -/
def LaneClear (p : Program) (r : ℕ) (S : Set Cell) : Prop :=
  ∀ c ∈ S, c.1 - c.2 ≤ U p r - 118 ∨ U p r - 64 ≤ c.1 - c.2 ∨ c.1 + c.2 ≤ 349

/-- **A set clear of the lanes is far from them.** -/
theorem LaneClear.farApart {r : ℕ} {S : Set Cell} (h : LaneClear p r S) :
    FarApart 2 S (modLanes p r) := by
  rintro a ha _ ⟨c, ⟨c1, c2, c3⟩, rfl⟩ ⟨n1, n2, n3, n4⟩
  have hm := modD_uv p r
  have := h a ha
  simp only [Prod.fst_add, Prod.snd_add] at n1 n2 n3 n4
  push_cast at n1 n2 n3 n4
  omega

/-- Clear sets are closed under unions. -/
theorem LaneClear.union {r : ℕ} {S T : Set Cell} (hS : LaneClear p r S) (hT : LaneClear p r T) :
    LaneClear p r (S ∪ T) :=
  fun c hc => hc.elim (hS c) (hT c)

/-- Clear sets are closed under subsets. -/
theorem LaneClear.mono {r : ℕ} {S T : Set Cell} (hS : LaneClear p r S) (h : T ⊆ S) :
    LaneClear p r T :=
  fun c hc => hS c (h hc)

/-- A set at `v ≤ 349` is clear of the lanes of every register. -/
theorem laneClear_of_low {r : ℕ} {S : Set Cell} (h : ∀ c ∈ S, c.1 + c.2 ≤ 349) :
    LaneClear p r S :=
  fun c hc => Or.inr (Or.inr (h c hc))

/-- A box beside or below the lanes of `r` is clear of them. -/
theorem laneClear_box {r : ℕ} {a b lo hi : ℤ}
    (h : b - lo ≤ U p r - 118 ∨ U p r - 64 ≤ a - hi ∨ b + hi ≤ 349) :
    LaneClear p r (Box a b lo hi) := by
  rintro c ⟨c1, c2, c3, c4⟩
  omega

/-- The boxes of a list of pieces, each clear, form a clear set. -/
theorem laneClear_boxesOf {r : ℕ} {L : List Piece} (h : ∀ g ∈ L, LaneClear p r g.box) :
    LaneClear p r (boxesOf L) := by
  intro c hc
  obtain ⟨g, hg, hc⟩ := mem_boxesOf.1 hc
  exact h g hg c hc

/-- **A set near module `r`**: every cell is at `v ≤ 349` or in the `u`-band
`[U_r - 750, U_r + 900]` of the module. -/
def ModNear (p : Program) (r : ℕ) (S : Set Cell) : Prop :=
  ∀ c ∈ S, c.1 + c.2 ≤ 349 ∨ (U p r - 750 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r + 900)

/-- The modules are `P_M = 2400 + 540 D ≥ 2940` apart. -/
theorem lane_U_gap (p : Program) {r r' : ℕ} (h : r < r') :
    U p r + 2400 + 540 * D p ≤ U p r' ∧ 1 ≤ D p := by
  have := U_add_le p (r := r) (r' := r') (by exact_mod_cast h)
  have := one_le_D p
  unfold PM at *
  omega

/-- **A set near module `r` is clear of the lanes of every other register.** -/
theorem ModNear.laneClear {r r' : ℕ} {S : Set Cell} (h : ModNear p r S) (hne : r' ≠ r) :
    LaneClear p r' S := by
  intro c hc
  rcases lt_or_gt_of_ne hne with h' | h'
  · have := lane_U_gap p h'
    rcases h c hc with h1 | h1 <;> omega
  · have := lane_U_gap p h'
    rcases h c hc with h1 | h1 <;> omega

/-- Sets near a module are closed under unions. -/
theorem ModNear.union {r : ℕ} {S T : Set Cell} (hS : ModNear p r S) (hT : ModNear p r T) :
    ModNear p r (S ∪ T) :=
  fun c hc => hc.elim (hS c) (hT c)

/-- Sets near a module are closed under subsets. -/
theorem ModNear.mono {r : ℕ} {S T : Set Cell} (hS : ModNear p r S) (h : T ⊆ S) :
    ModNear p r T :=
  fun c hc => hS c (h hc)

/-! ### The lanes -/

/-- The lanes of register `r` are in the band of module `r`. -/
theorem modLanes_near (p : Program) (r : ℕ) : ModNear p r (modLanes p r) := by
  rintro _ ⟨c, ⟨c1, c2, c3⟩, rfl⟩
  have := modD_uv p r
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- **The lanes of distinct registers are far apart** (`R-31` #16). -/
theorem modLanes_far (p : Program) {r₁ r₂ : ℕ} (h : r₁ ≠ r₂) :
    FarApart 2 (modLanes p r₁) (modLanes p r₂) :=
  ((modLanes_near p r₁).laneClear (Ne.symm h)).farApart

/-- The strip of the diagonal of register `r` (any register state) is in the band of module
`r`. -/
theorem lane_regStrip_near (p : Program) (r : ℕ) (R : RegS) (i : ℕ) :
    ModNear p r (regStrip p r R i) := by
  rintro _ ⟨c, ⟨c1, c2, c3⟩, rfl⟩
  have := modD_uv p r
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-! ### Global facts of the layout -/

/-- The band and the units are low: `V_T + 660 (N + R) ≤ -4764 - 198 D`. -/
theorem lane_VT_low (p : Program) :
    VT p + 660 * (N p + R p) ≤ -4764 - 198 * D p ∧ VU p = VT p - 1644 ∧ 1 ≤ D p ∧ 1 ≤ R p ∧
      0 ≤ N p := by
  have hf := layout_facts p
  omega

/-! ### The pieces of the machine -/

/-- **The groups of the register circuit beside or below the lanes** (module frame): every group
within `u ∈ [-122, -60]` ends at `v ≤ 260` (group `0`). -/
theorem lane_dz2g_lane (i : ℕ) (hi : i < 28) :
    (Base.dz2g i).piece.b - (Base.dz2g i).piece.lo ≤ -118 ∨
      -64 ≤ (Base.dz2g i).piece.a - (Base.dz2g i).piece.hi ∨
      (Base.dz2g i).piece.b + (Base.dz2g i).piece.hi ≤ 349 := by
  interval_cases i <;>
    simp only [Base.piece, dz2gPieces, dz2gG0, dz2gG1, dz2gG2, dz2gG3, dz2gG4, dz2gG5, dz2gG6,
      dz2gG7, dz2gG8, dz2gG9, dz2gG10, dz2gG11, dz2gG12, dz2gG13, dz2gG14, dz2gG15, dz2gG16,
      dz2gG17, dz2gG18, dz2gG19, dz2gG20, dz2gG21, dz2gG22, dz2gG23, dz2gG24, dz2gG25, dz2gG26,
      dz2gG27, List.getD_cons_zero, List.getD_cons_succ] <;> norm_num

/-- The box of a spec beside or below the lanes is clear. -/
theorem spec_laneClear {r : ℕ} {s : PSpec}
    (h : s.bx.b - s.bx.lo ≤ U p r - 118 ∨ U p r - 64 ≤ s.bx.a - s.bx.hi ∨
      s.bx.b + s.bx.hi ≤ 349) : LaneClear p r s.piece.box := by
  rw [PSpec.piece_box]
  exact laneClear_box h

/-- **The pieces of the units are low** (`R-31` #17). -/
theorem unit_laneClear (p : Program) (r a : ℕ) {s : PSpec} (hs : s ∈ unitSpecs p a) :
    LaneClear p r s.piece.box := by
  have h := unitSpecs_uv p a hs
  have hv := lane_VT_low p
  have hP := one_le_P p
  unfold BoxT.InUV at h
  exact spec_laneClear (by omega)

/-- **The pieces of module `r'`** are beside the lanes of every register `r ≠ r'`, and beside or
below the lanes of their own register (`R-31` #14, #15). -/
theorem module_laneClear (p : Program) (r : ℕ) {r' : ℕ} {s : PSpec} (hs : s ∈ moduleSpecs p r') :
    LaneClear p r s.piece.box := by
  have hD := one_le_D p
  by_cases hrr : r = r'
  · subst hrr
    have hb := base_boxes
    have hm := modD_uv p r
    refine spec_laneClear ?_
    rcases moduleSpecs_cls p r hs with ⟨i, ph, hi⟩ | ph | ph | ⟨m, ph, hm'⟩ | ⟨i, j, ph, hi, hj⟩ |
      ⟨i, j, ph, hi, hj⟩ | ph | ph
    · have := lane_dz2g_lane i hi
      simp only [PSpec.bx_mk]; omega
    · simp only [PSpec.bx_mk]; omega
    · simp only [PSpec.bx_mk]; omega
    · simp only [PSpec.bx_mk]; omega
    · have := stNZ_cases i hi
      simp only [PSpec.bx_mk]; omega
    · have := stZ_cases i hi
      simp only [PSpec.bx_mk]; omega
    · simp only [PSpec.bx_mk]; omega
    · simp only [PSpec.bx_mk]; omega
  · have h := (moduleSpecs_uv p r' hs).1
    unfold BoxT.InUV at h
    refine spec_laneClear ?_
    rcases lt_or_gt_of_ne hrr with h' | h'
    · have := lane_U_gap p h'
      omega
    · have := lane_U_gap p h'
      omega

/-- **The reflectors of the corners** are beside or below the lanes of every register: band,
halt and slab corners are low, left-zone corners `≥ 768` left of the lanes of their module,
right-zone corners `≥ 1205` right (`R-31` #14, #15, #17). -/
theorem corner_laneClear (p : Program) (r : ℕ) {c : Corner} (hc : Valid p c) :
    LaneClear p r (cornerSpec c).piece.box := by
  have h1 := corner_uv c
  have hv := lane_VT_low p
  have hf := layout_facts p
  refine spec_laneClear ?_
  obtain ⟨k, u, v, tag⟩ := c
  unfold BoxT.InUV at h1
  simp only at h1 ⊢
  cases tag with
  | band b n h => simp only [Valid] at hc; omega
  | halt a' => simp only [Valid] at hc; omega
  | slab a' t => simp only [Valid] at hc; omega
  | left r' idx =>
    simp only [Valid] at hc
    have hr' : r' = ((r'.toNat : ℕ) : ℤ) := by omega
    rcases lt_trichotomy r'.toNat r with h | h | h
    · have := lane_U_gap p h
      rw [hr'] at hc
      omega
    · subst h
      rw [hr'] at hc
      omega
    · have := lane_U_gap p h
      rw [hr'] at hc
      omega
  | right r' j w =>
    simp only [Valid] at hc
    have hr' : r' = ((r'.toNat : ℕ) : ℤ) := by omega
    rw [hr'] at hc
    obtain ⟨_, _, _, _, hw⟩ := hc
    rcases lt_trichotomy r'.toNat r with h | h | h
    · have := lane_U_gap p h
      rcases hw with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · subst h
      rcases hw with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · have := lane_U_gap p h
      rcases hw with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- **Every piece of the machine of a well-formed program is clear of the lanes of every
register** (`R-31` #14, #15, #17). -/
theorem machPieces_laneClear {p : Program} (hp : p.WellFormed) (r : ℕ) :
    ∀ g ∈ machPieces p, LaneClear p r g.box := by
  intro g hg
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  rcases mem_machSpecs hs with ⟨a, -, hs⟩ | ⟨r', -, hs⟩ | ⟨c, hc, hb⟩
  · exact unit_laneClear p r a hs
  · exact module_laneClear p r hs
  · rw [PSpec.piece_box, hb, ← PSpec.piece_box]
    exact corner_laneClear p r (allCorners_valid hp c hc)

/-- **The boxes of the pieces of the machine are far from the lanes of every register.** -/
theorem machBoxes_far {p : Program} (hp : p.WellFormed) (r : ℕ) :
    FarApart 2 (boxesOf (machPieces p)) (modLanes p r) :=
  (laneClear_boxesOf (machPieces_laneClear hp r)).farApart

/-- **The register circuit of module `r` is far from the lanes of its register.** -/
theorem lane_modGroup_far (p : Program) (r : ℕ) :
    FarApart 2 (boxesOf (modGroup p r)) (modLanes p r) := by
  refine (laneClear_boxesOf fun g hg => ?_).farApart
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  exact module_laneClear p r (s := s) (r' := r) (by simp [moduleSpecs, hs])

/-- The register circuit of module `r` is in the band of module `r`. -/
theorem lane_modGroup_near (p : Program) (r : ℕ) : ModNear p r (boxesOf (modGroup p r)) := by
  intro c hc
  obtain ⟨g, hg, hc⟩ := mem_boxesOf.1 hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  obtain ⟨b, hb, rfl⟩ := mem_groupSpecs hs
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
  have := dz2g_facts i (List.mem_range.1 hi)
  have hm := modD_uv p r
  rw [PSpec.piece_box] at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  simp only [PSpec.bx_mk] at c1 c2 c3 c4
  omega

/-! ### Units -/

/-- **The box of the body of unit `i` is low** (`v ≤ V_U + 640`). -/
theorem lane_bodyBox_low (p : Program) (i : ℕ) : ∀ c ∈ bodyBox p i, c.1 + c.2 ≤ VU p + 640 := by
  rintro _ ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩
  have := unitD_uv p i
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- **The entry chain of unit `a` from copy `t` is low** (`v ≤ V_U + 150`). -/
theorem lane_entryFoot_low (p : Program) (a t : ℕ) :
    ∀ c ∈ entryFoot p a t, c.1 + c.2 ≤ VU p + 150 := by
  intro x hx
  obtain ⟨c, ⟨j, hj, h1, h2, h3, h4⟩, rfl⟩ := entryFoot_subset_crude p a t hx
  have := unitD_uv p a
  simp only [Prod.fst_add, Prod.snd_add] at *
  omega

/-- **The flight out of the entry chain of unit `a` is low** before it reaches the body
(`v ≤ V_U + 216`). -/
theorem lane_chainOut_low (p : Program) (a : ℕ) {t : ℤ} (ht : t ≤ 0) :
    ∀ c ∈ (fun c => (unitDX p a, unitDY p a) + c) '' chainOutWL.box t, c.1 + c.2 ≤ VU p + 216 := by
  rintro _ ⟨c, ⟨h1, h2, h3, h4⟩, rfl⟩
  have := unitD_uv p a
  simp only [Prod.fst_add, Prod.snd_add, chainOutWL, WL.px, WL.py, WL.qt] at *
  omega

/-! ### Routes -/

/-- The largest `v = x + y` of the box of the glider of `w` at time `t`. -/
def WL.vHi (w : WL) (t : ℤ) : ℤ := w.px t + w.py t + 6

/-- Every cell of the glider box has `v` at most `vHi`. -/
theorem WL.le_vHi {w : WL} {t : ℤ} {c : Cell} (h : c ∈ w.box t) : c.1 + c.2 ≤ w.vHi t := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold WL.vHi
  omega

/-- **Between two times, the largest `v` of a glider box is at most the larger end value.** -/
theorem WL.vHi_between {w : WL} (hd : w.Dir) {t₁ t t₂ : ℤ} (h1 : t₁ ≤ t) (h2 : t ≤ t₂) :
    w.vHi t ≤ max (w.vHi t₁) (w.vHi t₂) := by
  obtain ⟨hx, hy⟩ := hd
  have q1 : (t₁ - w.tau) / 4 ≤ (t - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  have q2 : (t - w.tau) / 4 ≤ (t₂ - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  unfold WL.vHi WL.py WL.px WL.qt
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> omega

/-- **A glider flying `NE` or `SW`** keeps its `v`. -/
theorem WL.vHi_const {w : WL} (hd : w.dx + w.dy = 0) (hx : w.dx = 1 ∨ w.dx = -1) (t t' : ℤ) :
    w.vHi t = w.vHi t' := by
  have hy : w.dy = -w.dx := by omega
  unfold WL.vHi WL.py WL.px WL.qt
  rw [hy]
  rcases hx with hx | hx <;> rw [hx] <;> ring

/-- **The glider at a corner**: on the input line of the corner, at the meeting time, its box is
at most `70` above the corner point. -/
theorem lane_vHi_meet {g : WL} {c : Corner} (h : OnLine g c) : g.vHi (meetT g c) ≤ c.v + 70 := by
  obtain ⟨dx, dy, lane, tau⟩ := g
  obtain ⟨k, u, v, tag⟩ := c
  have hdx := congrArg WL.dx h
  have hdy := congrArg WL.dy h
  have hl := congrArg WL.lane h
  simp only [WL.shift] at hdx hdy hl
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rfIn] at hdx hdy hl <;> subst hdx hdy <;>
    simp only [WL.vHi, WL.px, WL.py, WL.qt, meetT, delayS, rfIn, rfX, rfY, rfCU,
      rfCV] at hl ⊢ <;> omega

/-- **The glider leaving a corner window**: `40` generations after the meeting time its box is
at most `70` above the corner point. -/
theorem lane_vHi_out40 (g : WL) (c : Corner) : (reflect g c).2.vHi (meetT g c + 40) ≤ c.v + 70 := by
  obtain ⟨k, u, v, tag⟩ := c
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [reflect, WL.vHi, WL.px, WL.py, WL.qt, WL.shift, meetT, delayS, rfIn, rfOut,
      rfX, rfY, rfCU, rfCV] <;> omega

/-- **The extended relay box of a corner** is at most `70` above the corner point. -/
theorem lane_relayBoxX_v {c : Corner} {x : Cell} (hx : x ∈ relayBoxX c) : x.1 + x.2 ≤ c.v + 70 := by
  obtain ⟨k, u, v, tag⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rxB, rxBox, rfX, rfY, rfCU, rfCV] at h1 h2 h3 h4 ⊢ <;> omega

/-- **A route with low corners has a low footprint**: from a glider whose box is at `v ≤ V` at
time `T`, through corners at `v ≤ V - 70` met on their input lines, in order, the footprint
`routeFootX` stays at `v ≤ V` up to the end of the route, and so does the final glider box at
the end. -/
theorem lane_route_vlow (V : ℤ) : ∀ (cs : List Corner) (g : WL) (T : ℕ), g.Dir → RouteLines g cs →
    RouteTimedX g cs T → (∀ c ∈ cs, c.v + 70 ≤ V) → g.vHi T ≤ V →
    (∀ i, T + i ≤ routeEndX g cs T → ∀ x ∈ routeFootX g cs T i, x.1 + x.2 ≤ V) ∧
      (route g cs).2.vHi (routeEndX g cs T) ≤ V
  | [], g, T, _, _, _, _, h0 => by
    refine ⟨fun i hi x hx => ?_, h0⟩
    simp only [routeEndX] at hi
    rw [show i = 0 by omega] at hx
    simp only [routeFootX, Nat.cast_zero, add_zero] at hx
    exact (WL.le_vHi hx).trans h0
  | c :: cs, g, T, hd, ⟨hl, hls⟩, ⟨ht, hts⟩, hcs, h0 => by
    set m := (meetT g c).toNat with hm
    have hmT : ((m : ℕ) : ℤ) = meetT g c := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hc := hcs c List.mem_cons_self
    have h1 := lane_vHi_meet hl
    have h2 := lane_vHi_out40 g c
    have hts' : RouteTimedX (reflect g c).2 cs ((m + 40 : ℕ) : ℤ) := by
      push_cast
      rw [hmT]
      exact hts
    obtain ⟨ih1, ih2⟩ := lane_route_vlow V cs _ (m + 40) (reflect_dir g c) hls hts'
      (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) (by push_cast; rw [hmT]; omega)
    refine ⟨fun i hi x hx => ?_, ih2⟩
    simp only [routeEndX, ← hm] at hi
    simp only [routeFootX, ← hm] at hx
    split_ifs at hx with ha hb
    · exact (WL.le_vHi hx).trans ((WL.vHi_between hd (t₁ := T) (t₂ := meetT g c) (by omega)
        (by omega)).trans (max_le (by omega) (by omega)))
    · have := lane_relayBoxX_v hx
      omega
    · exact ih1 _ (by omega) x hx

/-- **A low link into an entry chain has a low footprint** (`linkFootX`): the route, the flight
on a `NE`/`SW` line after it, and the entry chain (low). -/
theorem lane_linkFoot_vlow (V : ℤ) {a t : ℕ} {g : WL} {cs : List Corner} {T T0 : ℕ} (hd : g.Dir)
    (hl : RouteLines g cs) (htim : RouteTimedX g cs T) (hcs : ∀ c ∈ cs, c.v + 70 ≤ V)
    (h0 : g.vHi T ≤ V) (hdx : (route g cs).2.dx = 1) (hdy : (route g cs).2.dy = -1)
    (hent : VU p + 150 ≤ V) (j : ℕ) :
    ∀ x ∈ linkFootX p a t g cs T T0 j, x.1 + x.2 ≤ V := by
  obtain ⟨h1, h2⟩ := lane_route_vlow V cs g T hd hl htim hcs h0
  intro x hx
  unfold linkFootX at hx
  split_ifs at hx with ha hb
  · exact h1 j ha x hx
  · refine (WL.le_vHi hx).trans ?_
    rw [WL.vHi_const (by omega) (Or.inl hdx) _ (routeEndX g cs T : ℤ)]
    exact h2
  · exact (lane_entryFoot_low p a t x hx).trans hent

/-- **A low link into an entry chain with a side window has a low footprint** (`linkFootW`): the
route, the flight on a `NE`/`SW` line after it, and the entry chain (low). -/
theorem lane_linkFootW_vlow (V : ℤ) {a t : ℕ} {g : WL} {cs : List Corner} {T T0 : ℕ}
    (hd : g.Dir) (hl : RouteLines g cs) (htim : RouteTimedX g cs T) (hcs : ∀ c ∈ cs, c.v + 70 ≤ V)
    (h0 : g.vHi T ≤ V) (hdx : (route g cs).2.dx = 1) (hdy : (route g cs).2.dy = -1)
    (hent : VU p + 150 ≤ V) (j : ℕ) :
    ∀ x ∈ linkFootW p a t g cs T T0 j, x.1 + x.2 ≤ V := by
  obtain ⟨h1, h2⟩ := lane_route_vlow V cs g T hd hl htim hcs h0
  intro x hx
  unfold linkFootW at hx
  split_ifs at hx with ha hb
  · exact h1 j ha x hx
  · refine (WL.le_vHi hx).trans ?_
    rw [WL.vHi_const (by omega) (Or.inl hdx) _ (routeEndX g cs T : ℤ)]
    exact h2
  · exact (lane_entryFoot_low p a t x hx).trans hent

/-! ### The module part of the `inc` activation -/

/-- **The module part before the increment** (INC gate, flight to `RF_J`, `RF_J`, flight to the
input of the increment) lies at `u ∈ [U_r + 99, U_r + 300]` (up to `946` generations after the
arrival at the gate). -/
theorem lane_modFoot_u {r : ℕ} {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {j : ℕ}
    (hj : j ≤ 946) :
    ∀ c ∈ modFoot p r k Tg j, U p r + 99 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r + 300 := by
  have hU := modD_uv p r
  have hE := U_even p r
  intro x hx
  unfold modFoot at hx
  split_ifs at hx with h1 h2 h3
  · obtain ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · obtain ⟨c1, c2, c3, c4⟩ := hx
    simp only [gateOutWL, modWL, WL.shift, WL.px, WL.py, WL.qt] at c1 c2 c3 c4
    omega
  · obtain ⟨y, ⟨c1, c2, c3, c4⟩, rfl⟩ := hx
    simp only [rfJCorner, cornerV, rfX, rfY, rfCU, rfCV, Prod.fst_add, Prod.snd_add] at *
    omega
  · obtain ⟨c1, c2, c3, c4⟩ := hx
    simp only [rfJOutWL, modWL, incInWL, WL.shift, WL.px, WL.py, WL.qt, modDX,
      modDY] at hU c1 c2 c3 c4
    omega

/-- **The module part before the increment, with the `RF_J` window** (`modFootW`), lies at
`u ∈ [U_r + 99, U_r + 300]` (up to `946` generations after the arrival at the gate). -/
theorem lane_modFootW_u {r : ℕ} {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {j : ℕ}
    (hj : j ≤ 946) :
    ∀ c ∈ modFootW p r k Tg j, U p r + 99 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r + 300 := by
  have hU := modD_uv p r
  have hE := U_even p r
  intro x hx
  unfold modFootW at hx
  split_ifs at hx with h1 h2 h3
  · obtain ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · obtain ⟨c1, c2, c3, c4⟩ := hx
    simp only [gateOutWL, modWL, WL.shift, WL.px, WL.py, WL.qt] at c1 c2 c3 c4
    omega
  · obtain ⟨c1, c2, c3, c4⟩ := hx
    simp only [rxB, rxBox, rfJCorner, rfX, rfY, rfCU, rfCV] at c1 c2 c3 c4
    omega
  · obtain ⟨c1, c2, c3, c4⟩ := hx
    simp only [rfJOutWL, modWL, incInWL, WL.shift, WL.px, WL.py, WL.qt, modDX,
      modDY] at hU c1 c2 c3 c4
    omega

/-- The gate box of module `r` lies at `u ∈ [U_r + 99, U_r + 300]`. -/
theorem lane_gateBox_u (p : Program) (r : ℕ) :
    ∀ c ∈ gateBox p r, U p r + 99 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r + 300 := by
  have hU := modD_uv p r
  rintro _ ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- The module part with the `RF_J` window is clear of the lanes of its register. -/
theorem modFootW_laneClear {r : ℕ} {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {j : ℕ}
    (hj : j ≤ 946) : LaneClear p r (modFootW p r k Tg j) :=
  fun c hc => Or.inr (Or.inl (by have := lane_modFootW_u hTg hj c hc; omega))

/-- The module part with the `RF_J` window is in the band of the module. -/
theorem lane_modFootW_near {r : ℕ} {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {j : ℕ}
    (hj : j ≤ 946) : ModNear p r (modFootW p r k Tg j) :=
  fun c hc => Or.inr (by have := lane_modFootW_u hTg hj c hc; omega)

/-- The gate box of module `r` is in the band of the module. -/
theorem lane_gateBox_near (p : Program) (r : ℕ) : ModNear p r (gateBox p r) :=
  fun c hc => Or.inr (by have := lane_gateBox_u p r c hc; omega)

/-- The gate box of module `r` is clear of the lanes of its register. -/
theorem gateBox_laneClear (p : Program) (r : ℕ) : LaneClear p r (gateBox p r) :=
  fun c hc => Or.inr (Or.inl (by have := lane_gateBox_u p r c hc; omega))

/-- The module part before the increment is clear of the lanes of its register. -/
theorem modFoot_laneClear {r : ℕ} {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {j : ℕ}
    (hj : j ≤ 946) : LaneClear p r (modFoot p r k Tg j) :=
  fun c hc => Or.inr (Or.inl (by have := lane_modFoot_u hTg hj c hc; omega))

/-- The module part before the increment is in the band of the module. -/
theorem lane_modFoot_near {r : ℕ} {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {j : ℕ}
    (hj : j ≤ 946) : ModNear p r (modFoot p r k Tg j) :=
  fun c hc => Or.inr (by have := lane_modFoot_u hTg hj c hc; omega)

/-- A component with `b - lo ≤ m` or `U₂ ≤ m` lies at `u ≤ m`. -/
theorem lane_BU_subset_uHi {m a b lo hi U₁ U₂ V₁ V₂ : ℤ} (h : b - lo ≤ m ∨ U₂ ≤ m) :
    BU a b lo hi U₁ U₂ V₁ V₂ ⊆ {c : Cell | c.1 - c.2 ≤ m} := by
  rintro c ⟨⟨c1, c2, c3, c4⟩, c5, c6, c7, c8⟩
  change c.1 - c.2 ≤ m
  omega

/-- The lanes of the register lie at `u ≤ -69`. -/
theorem lane_regLanes_subset_uHi {m : ℤ} (h : -69 ≤ m) : regLanes ⊆ {c : Cell | c.1 - c.2 ≤ m} := by
  rintro c ⟨c1, c2, c3⟩
  change c.1 - c.2 ≤ m
  omega

set_option maxRecDepth 100000 in
/-- **The runs of the increment lie at `u ≤ 798`** (module frame). -/
theorem lane_incRunBox_uHi : incRunBox ⊆ {c : Cell | c.1 - c.2 ≤ 798} := by
  have key : ∀ L : List (Set Cell), AllSub {c : Cell | c.1 - c.2 ≤ 798} L →
      unionL L ⊆ {c : Cell | c.1 - c.2 ≤ 798} := fun _ h => unionL_subset_of h
  unfold incRunBox dz2eRegion dz2e1Region dz2e2Region dz2e3Region dz2jRegion
  refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
    (key _ ?_) (key _ ?_)) (key _ ?_)) (key _ ?_)) (key _ ?_) <;>
  simp only [dz2eRegL, dz2e1RegL, dz2e2RegL, dz2e3RegL, dz2jRegL, AllSub] <;>
  repeat' apply And.intro
  all_goals first
    | exact lane_BU_subset_uHi (by omega) | exact lane_regLanes_subset_uHi (by omega) | trivial

/-- **The run of the increment placed at module `r`** is in the band of the module. -/
theorem lane_incRunBox_near (p : Program) (r : ℕ) :
    ModNear p r ((fun c => (modDX p r, modDY p r) + c) '' incRunBox) := by
  rintro _ ⟨c, hc, rfl⟩
  have h1 : -738 ≤ c.1 - c.2 := incRunBox_u hc
  have h2 : c.1 - c.2 ≤ 798 := lane_incRunBox_uHi hc
  have := modD_uv p r
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- **The footprint of the increment at module `r`, at every generation**: for a ready
register, inside the run region of the increment, the register circuit, or the lanes of the
register (the circuit idles beside the diagonal after the run, `lane_modGroup_far`). -/
theorem lane_incRun_sub (p : Program) (r : ℕ) {R : RegS} (hR : R.Ready) (i : ℕ) :
    (conway.evolve i (incStart p r ∪ regAt p r R) : Set Cell) ⊆
      ((fun c => (modDX p r, modDY p r) + c) '' incRunBox ∪ boxesOf (modGroup p r)) ∪
        modLanes p r := by
  obtain ⟨d, R', h1, h2, h3, h4, hev, hsub⟩ := regInc_module p r hR
  by_cases hid : i ≤ d
  · exact (hsub i hid).trans (Set.subset_union_left.trans Set.subset_union_left)
  · have hb := (bundleAt (modGroup p r) (modGroup_sep p r) (d - 6990) (i - d)).reaction
    rw [bundleAt_P, bundleAt_Q] at hb
    have hpar := (hb.mono fun j _ => (bundleAt_F _ _ _ _ j).le).par
      (regAt_reaction p r h4.1 (i - d))
      fun j _ => (lane_modGroup_far p r).mono le_rfl (regStrip_subset h4.1 p r j)
    have e2 : piecesAt (modGroup p r) (d - 6990) =
        translate (modDX p r, modDY p r) (conway.evolve (d - 6990) dz2gRest) := by
      rw [modGroup_at, dz2gRest_mod (d - 6990)]
    have e : conway.evolve i (incStart p r ∪ regAt p r R) =
        conway.evolve (i - d) (piecesAt (modGroup p r) (d - 6990) ∪ regAt p r R') := by
      rw [e2, show i = (i - d) + d by omega, Rule.evolve_add, incStart, hev,
        show i - d + d - d = i - d by omega]
    rw [e]
    refine (hpar.subset (i - d) le_rfl).trans (Set.union_subset_union ?_ ?_)
    · exact Set.subset_union_right
    · exact regStrip_subset h4.1 p r _

/-- **The footprint of the increment at module `r` is in the band of the module**, at every
generation, for a ready register. -/
theorem lane_incRun_near (p : Program) (r : ℕ) {R : RegS} (hR : R.Ready) (i : ℕ) :
    ModNear p r (conway.evolve i (incStart p r ∪ regAt p r R) : Set Cell) :=
  (((lane_incRunBox_near p r).union (lane_modGroup_near p r)).union (modLanes_near p r)).mono
    (lane_incRun_sub p r hR i)

end LP

end LeanTheory.Life
