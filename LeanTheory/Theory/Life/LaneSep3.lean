/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.LaneSep2

/-!
# Every route of the machine is clear of the register lanes (`R-31` #14–#17)

Research note `N-22`, report `R-31` §3. `LaneSep2` treats the low routes of the `inc` and halt
activations by their `v`. Here **every** link of the machine is treated, including the `decJz`
links whose legs climb into the zones of a module (`v` up to `1561 + 180 (D - 1)`):

* `RouteLane p r g cs T`: the lane analogue of `RouteSepX` (corner windows): the flight boxes up
  to `20` generations before each corner and the extended relay box `relayBoxX` of every corner
  are clear of the lanes of register `r` (`LaneClear`).
* Tools: the centre of a glider box moves monotonically along a world line
  (`WL.lane_cu_between`, `WL.lane_cv_between`); `20` generations before a corner and `40` after it
  the centre is within `40` of the corner point (`lane_in_near`, `lane_out_near`); a flight between
  two centres both low, both left or both right of the lanes is clear (`lane_flight`).
* `LaneCP p r c₁ c₂`: two corners both at `v ≤ 279`, both `≥ 162` left or both `≥ -20` right of
  the lanes of `r` (in `u`, relative to `U_r`). From the places of the corners (`Valid`):
  every corner is low (band, halt line, slabs: `v ≤ -4000`) or `u`-clear of the lanes of every
  register (left zone: `≥ 768` left of its module's lanes, right zone: `≥ 1250` right;
  `lane_corner_zone`). Hence `LaneCP` for consecutive corners on a common column, on a common
  track of the band, or both in the right zone of one module (`lane_cp_adj`).
* `LaneAdjChain`: the consecutive corners of every corner list of the layout (`upCornersK`,
  `downCorners`, `ztokCorners`, `nzAnsCorners`, `zAnsCorners`, `haltCorners`, `mergeCorners`)
  are adjacent in this sense (`lane_instrSpecs_adj`, `lane_mergeSpecs_adj`).
* **`lane_instrRoute`, `lane_mergeRoute`**: every route of every instruction and every merge link
  of a well-formed program, on its lines, is `RouteLane` for every register, given that its first
  flight starts on the same side of the lanes as its first corner (`LaneStart`; e.g.
  `lane_start_low`
  for the links leaving a unit). `lane_relay_clear`: the extended relay box of every corner of the
  machine is clear of the lanes of every register.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program}

/-! ### Glider centres -/

/-- **Between two times, the `u` of the centre of a glider is between its end values.** -/
theorem WL.lane_cu_between {w : WL} (hd : w.Dir) {t₁ t t₂ : ℤ} (h1 : t₁ ≤ t) (h2 : t ≤ t₂) :
    min (w.cu t₁) (w.cu t₂) ≤ w.cu t ∧ w.cu t ≤ max (w.cu t₁) (w.cu t₂) := by
  obtain ⟨hx, hy⟩ := hd
  have q1 : (t₁ - w.tau) / 4 ≤ (t - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  have q2 : (t - w.tau) / 4 ≤ (t₂ - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  unfold WL.cu WL.py WL.px WL.qt
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> omega

/-- **Between two times, the `v` of the centre of a glider is between its end values.** -/
theorem WL.lane_cv_between {w : WL} (hd : w.Dir) {t₁ t t₂ : ℤ} (h1 : t₁ ≤ t) (h2 : t ≤ t₂) :
    min (w.cv t₁) (w.cv t₂) ≤ w.cv t ∧ w.cv t ≤ max (w.cv t₁) (w.cv t₂) := by
  obtain ⟨hx, hy⟩ := hd
  have q1 : (t₁ - w.tau) / 4 ≤ (t - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  have q2 : (t - w.tau) / 4 ≤ (t₂ - w.tau) / 4 := Int.ediv_le_ediv (by norm_num) (by omega)
  unfold WL.cv WL.py WL.px WL.qt
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> omega

/-- **The glider before a corner**: on the input line, `20` generations before the meeting time,
the centre of the glider is within `40` of the corner point. -/
theorem lane_in_near {g : WL} {c : Corner} (h : OnLine g c) :
    c.u - 40 ≤ g.cu (meetT g c - 20) ∧ g.cu (meetT g c - 20) ≤ c.u + 40 ∧
      c.v - 40 ≤ g.cv (meetT g c - 20) ∧ g.cv (meetT g c - 20) ≤ c.v + 40 := by
  obtain ⟨dx, dy, lane, tau⟩ := g
  obtain ⟨k, u, v, tag⟩ := c
  have hdx := congrArg WL.dx h
  have hdy := congrArg WL.dy h
  have hl := congrArg WL.lane h
  simp only [WL.shift] at hdx hdy hl
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rfIn] at hdx hdy hl <;> subst hdx hdy <;>
    simp only [WL.cu, WL.cv, WL.px, WL.py, WL.qt, meetT, delayS, rfIn, rfX, rfY, rfCU,
      rfCV] at hl ⊢ <;> omega

/-- **The glider after a corner**: `40` generations after the meeting time the centre of the
outgoing glider is within `40` of the corner point. -/
theorem lane_out_near (g : WL) (c : Corner) :
    c.u - 40 ≤ (reflect g c).2.cu (meetT g c + 40) ∧
      (reflect g c).2.cu (meetT g c + 40) ≤ c.u + 40 ∧
      c.v - 40 ≤ (reflect g c).2.cv (meetT g c + 40) ∧
      (reflect g c).2.cv (meetT g c + 40) ≤ c.v + 40 := by
  obtain ⟨k, u, v, tag⟩ := c
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [reflect, WL.cu, WL.cv, WL.px, WL.py, WL.qt, WL.shift, meetT, delayS, rfIn, rfOut,
      rfX, rfY, rfCU, rfCV] <;> omega

/-- The extended relay box of a corner is within `30` of the corner point in `u`. -/
theorem lane_relayBoxX_u {c : Corner} {x : Cell} (hx : x ∈ relayBoxX c) :
    c.u - 30 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ c.u + 30 := by
  obtain ⟨k, u, v, tag⟩ := c
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rxB, rxBox, rfX, rfY, rfCU, rfCV] at h1 h2 h3 h4 ⊢ <;> omega

/-! ### Flights and corners clear of the lanes -/

/-- Two glider centres both low (`v ≤ 343`), both left (`u ≤ U_r - 122`) or both right
(`u ≥ U_r - 60`) of the lanes of `r`. -/
def LanePts (p : Program) (r : ℕ) (u₁ v₁ u₂ v₂ : ℤ) : Prop :=
  (v₁ ≤ 343 ∧ v₂ ≤ 343) ∨ (u₁ ≤ U p r - 122 ∧ u₂ ≤ U p r - 122) ∨
    (U p r - 60 ≤ u₁ ∧ U p r - 60 ≤ u₂)

/-- **A flight between two clear centres on the same side is clear.** -/
theorem lane_flight {r : ℕ} {w : WL} (hd : w.Dir) {t₁ t₂ : ℤ}
    (h : LanePts p r (w.cu t₁) (w.cv t₁) (w.cu t₂) (w.cv t₂)) {t : ℤ} (h1 : t₁ ≤ t) (h2 : t ≤ t₂) :
    LaneClear p r (w.box t) := by
  have hu := WL.lane_cu_between hd h1 h2
  have hv := WL.lane_cv_between hd h1 h2
  rintro x ⟨x1, x2, x3, x4⟩
  simp only [WL.cu, WL.cv] at hu hv
  unfold LanePts at h
  simp only [WL.cu, WL.cv] at h
  omega

/-- Two corners both at `v ≤ 279`, both `≥ 162` left or both at least `-20` right of the lanes
of `r` (relative to `U_r`). -/
def LaneCP (p : Program) (r : ℕ) (c₁ c₂ : Corner) : Prop :=
  (c₁.v ≤ 279 ∧ c₂.v ≤ 279) ∨ (c₁.u ≤ U p r - 162 ∧ c₂.u ≤ U p r - 162) ∨
    (U p r - 20 ≤ c₁.u ∧ U p r - 20 ≤ c₂.u)

/-- **The extended relay box of a clear corner is clear.** -/
theorem lane_relay_of {r : ℕ} {c : Corner} (h : LaneCP p r c c) : LaneClear p r (relayBoxX c) := by
  intro x hx
  have h1 := lane_relayBoxX_u hx
  have h2 := lane_relayBoxX_v hx
  unfold LaneCP at h
  omega

/-- The start of a flight before the corner `c`: its centre at `T` and the corner are both low,
both left or both right of the lanes of `r`. -/
def LaneStart (p : Program) (r : ℕ) (g : WL) (T : ℤ) (c : Corner) : Prop :=
  (g.cv T ≤ 343 ∧ c.v ≤ 279) ∨ (g.cu T ≤ U p r - 122 ∧ c.u ≤ U p r - 162) ∨
    (U p r - 60 ≤ g.cu T ∧ U p r - 20 ≤ c.u)

/-- A flight starting low towards a low corner. -/
theorem lane_start_low {r : ℕ} {g : WL} {T : ℤ} {c : Corner} (h1 : g.cv T ≤ 343)
    (h2 : c.v ≤ 279) : LaneStart p r g T c :=
  Or.inl ⟨h1, h2⟩

/-- **The lane analogue of `RouteSepX`**: the flight boxes up to `20` generations before each
corner and the extended relay box of every corner are clear of the lanes of register `r`. -/
def RouteLane (p : Program) (r : ℕ) : WL → List Corner → ℤ → Prop
  | _, [], _ => True
  | g, c :: cs, T =>
      (∀ t : ℤ, T ≤ t → t ≤ meetT g c - 20 → LaneClear p r (g.box t)) ∧
      LaneClear p r (relayBoxX c) ∧ RouteLane p r (reflect g c).2 cs (meetT g c + 40)

/-- Consecutive corners of a list are pairwise `LaneCP` (the last one with itself). -/
def LaneChain (p : Program) (r : ℕ) : List Corner → Prop
  | [] => True
  | [c] => LaneCP p r c c
  | c₁ :: c₂ :: cs => LaneCP p r c₁ c₂ ∧ LaneChain p r (c₂ :: cs)

/-- The head of a clear chain is clear with itself. -/
theorem LaneChain.head {r : ℕ} {c : Corner} {cs : List Corner} (h : LaneChain p r (c :: cs)) :
    LaneCP p r c c := by
  cases cs with
  | nil => exact h
  | cons c₂ cs =>
    obtain ⟨h1, -⟩ := h
    unfold LaneCP at h1 ⊢
    omega

/-- **A route on its lines with a clear chain of corners and a clear start is clear.** -/
theorem lane_routeLane_of {r : ℕ} : ∀ (cs : List Corner) (g : WL) (T : ℤ), g.Dir →
    RouteLines g cs → LaneChain p r cs → (∀ c ∈ cs.head?, LaneStart p r g T c) →
    RouteLane p r g cs T
  | [], _, _, _, _, _, _ => trivial
  | c :: cs, g, T, hd, ⟨hl, hls⟩, hch, hst => by
    have hs := hst c rfl
    have hn := lane_in_near hl
    refine ⟨fun t h1 h2 => lane_flight hd ?_ h1 h2, lane_relay_of hch.head, ?_⟩
    · unfold LaneStart at hs
      unfold LanePts
      omega
    · cases cs with
      | nil => trivial
      | cons c₂ cs' =>
        obtain ⟨hcp, hch'⟩ := hch
        refine lane_routeLane_of (c₂ :: cs') _ _ (reflect_dir g c) hls hch' ?_
        intro c' hc'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
        subst hc'
        have ho := lane_out_near g c
        unfold LaneCP at hcp
        unfold LaneStart
        omega

/-! ### Corners of the layout -/

/-- **Every corner with a valid place is low, or `u`-clear of the lanes of every register**: band,
halt and slab corners at `v ≤ -4000`; left-zone corners `≥ 768` left of the lanes of their module,
right-zone corners `≥ 1250` right of them (and both far from the other modules). -/
theorem lane_corner_zone {c : Corner} (hc : Valid p c) :
    c.v ≤ -4000 ∨ ∀ r : ℕ, c.u ≤ U p r - 162 ∨ U p r - 20 ≤ c.u := by
  have hv := lane_VT_low p
  have hf := layout_facts p
  obtain ⟨k, u, v, tag⟩ := c
  cases tag with
  | band b n h => simp only [Valid] at hc; left; simp only; omega
  | halt a' => simp only [Valid] at hc; left; simp only; omega
  | slab a' t => simp only [Valid] at hc; left; simp only; omega
  | left r' idx =>
    simp only [Valid] at hc
    right
    intro r
    have hr' : r' = ((r'.toNat : ℕ) : ℤ) := by omega
    rw [hr'] at hc
    simp only
    rcases lt_trichotomy r'.toNat r with h | h | h
    · have := lane_U_gap p h
      omega
    · subst h
      omega
    · have := lane_U_gap p h
      omega
  | right r' j w =>
    simp only [Valid] at hc
    right
    intro r
    have hr' : r' = ((r'.toNat : ℕ) : ℤ) := by omega
    rw [hr'] at hc
    obtain ⟨_, _, _, _, hw⟩ := hc
    simp only
    rcases lt_trichotomy r'.toNat r with h | h | h
    · have := lane_U_gap p h
      rcases hw with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · subst h
      rcases hw with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · have := lane_U_gap p h
      rcases hw with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- **The extended relay box of every corner with a valid place is clear of the lanes of every
register.** -/
theorem lane_relay_clear {c : Corner} (hc : Valid p c) (r : ℕ) : LaneClear p r (relayBoxX c) := by
  refine lane_relay_of ?_
  unfold LaneCP
  rcases lane_corner_zone hc with h | h
  · omega
  · have := h r
    omega

/-- Two consecutive corners of a route: on a common column, or on a common track with one of
them in the band, or both in the right zone of the same module. -/
def LaneAdj (c₁ c₂ : Corner) : Prop :=
  c₁.u = c₂.u ∨ (c₁.v = c₂.v ∧ ((∃ b k h, c₁.tag = .band b k h) ∨
    ∃ (r₀ j j' : ℤ) (w w' : ℕ), c₁.tag = .right r₀ j w ∧ c₂.tag = .right r₀ j' w'))

/-- **Adjacent corners with valid places are `LaneCP` for every register.** -/
theorem lane_cp_adj {c₁ c₂ : Corner} (hc₁ : Valid p c₁) (hc₂ : Valid p c₂) (h : LaneAdj c₁ c₂)
    (r : ℕ) : LaneCP p r c₁ c₂ := by
  unfold LaneCP
  rcases h with hu | ⟨hv, ⟨b, k, hh, hb⟩ | ⟨r₀, j, j', w, w', h1, h2⟩⟩
  · rcases lane_corner_zone hc₁ with h1 | h1
    · rcases lane_corner_zone hc₂ with h2 | h2
      · omega
      · have := h2 r
        omega
    · have := h1 r
      omega
  · have hv := lane_VT_low p
    obtain ⟨k₁, u₁, v₁, tag₁⟩ := c₁
    simp only at hb
    subst hb
    simp only [Valid] at hc₁
    simp only at hv ⊢
    omega
  · obtain ⟨k₁, u₁, v₁, tag₁⟩ := c₁
    obtain ⟨k₂, u₂, v₂, tag₂⟩ := c₂
    simp only at h1 h2
    subst h1 h2
    simp only [Valid] at hc₁ hc₂
    simp only
    have hD := one_le_D p
    have hr' : r₀ = ((r₀.toNat : ℕ) : ℤ) := by omega
    rw [hr'] at hc₁ hc₂
    obtain ⟨_, _, _, _, hw₁⟩ := hc₁
    obtain ⟨_, _, _, _, hw₂⟩ := hc₂
    rcases le_or_gt r r₀.toNat with h | h
    · have hU : U p r ≤ U p r₀.toNat := by
        rcases h.lt_or_eq with h | h
        · have := lane_U_gap p h
          omega
        · rw [h]
      rcases hw₁ with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;>
        rcases hw₂ with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · have := lane_U_gap p h
      rcases hw₁ with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;>
        rcases hw₂ with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega

/-- Consecutive corners of a list are adjacent. -/
def LaneAdjChain : List Corner → Prop
  | [] => True
  | [_] => True
  | c₁ :: c₂ :: cs => LaneAdj c₁ c₂ ∧ LaneAdjChain (c₂ :: cs)

/-- **An adjacent chain of corners with valid places is clear for every register.** -/
theorem lane_chain_of (r : ℕ) : ∀ (cs : List Corner), (∀ c ∈ cs, Valid p c) → LaneAdjChain cs →
    LaneChain p r cs
  | [], _, _ => trivial
  | [c], hv, _ => lane_cp_adj (hv c List.mem_cons_self) (hv c List.mem_cons_self) (Or.inl rfl) r
  | c₁ :: c₂ :: cs, hv, ⟨ha, hs⟩ =>
    ⟨lane_cp_adj (hv c₁ List.mem_cons_self) (hv c₂ (List.mem_cons_of_mem _ List.mem_cons_self))
      ha r, lane_chain_of r (c₂ :: cs) (fun c hc => hv c (List.mem_cons_of_mem _ hc)) hs⟩

/-! ### The corner lists of the layout -/

/-- The band corners followed by a corner on the destination column. -/
theorem lane_bandCorners_adj (p : Program) (b s c H cd : ℤ) (k0 k4 : ℕ) (x : Corner)
    (hx : x.u = cd) : LaneAdjChain (bandCorners p b s c H cd k0 k4 ++ [x]) := by
  simp [bandCorners, LaneAdjChain, LaneAdj, hx]

/-- The corners of a link up to an entry copy are adjacent. -/
theorem lane_upCornersK_adj (k0 : ℕ) (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) :
    LaneAdjChain (upCornersK k0 p b s c H a t) :=
  lane_bandCorners_adj p b s c H _ k0 6 _ rfl

/-- The corners of a link down to a left-zone port are adjacent. -/
theorem lane_downCorners_adj (p : Program) (b s c H cd vp : ℤ) (r : ℕ) (idx : ℤ) :
    LaneAdjChain (downCorners p b s c H cd vp r idx) :=
  lane_bandCorners_adj p b s c H cd 3 2 _ rfl

/-- The corners of the KZ link are adjacent. -/
theorem lane_ztokCorners_adj (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) :
    LaneAdjChain (ztokCorners p b c H r j) := by
  simp [ztokCorners, bandCorners, LaneAdjChain, LaneAdj]

/-- A corner on the source column of an adjacent chain of a link up to an entry copy. -/
theorem lane_cons_upCornersK_adj (k0 : ℕ) (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) (x : Corner)
    (hx : x.u = c) : LaneAdjChain (x :: upCornersK k0 p b s c H a t) := by
  have h := lane_upCornersK_adj k0 p b s c H a t
  simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, LaneAdjChain] at h ⊢
  exact ⟨Or.inl hx, h⟩

/-- The corners of the NZ answer are adjacent. -/
theorem lane_nzAnsCorners_adj (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) :
    LaneAdjChain (nzAnsCorners p b r j H a t) :=
  lane_cons_upCornersK_adj 5 p b 3 _ H a t _ rfl

/-- The corners of the Z answer are adjacent. -/
theorem lane_zAnsCorners_adj (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) :
    LaneAdjChain (zAnsCorners p b r j H a t) := by
  have h := lane_cons_upCornersK_adj 5 p b 4 (U p r + zAnsChan p j) H a t
    ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩ rfl
  unfold zAnsCorners
  exact ⟨Or.inr ⟨rfl, Or.inr ⟨_, _, _, _, _, rfl, rfl⟩⟩, h⟩

/-- **The consecutive corners of every route of an instruction are adjacent.** -/
theorem lane_instrSpecs_adj (p : Program) (i : ℕ) : ∀ x ∈ instrSpecs p i, LaneAdjChain x.2 := by
  intro x hx
  unfold instrSpecs at hx
  split at hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact trivial
  · simp only [incSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact lane_upCornersK_adj _ _ _ _ _ _ _ _
  · simp only [decSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact lane_downCorners_adj _ _ _ _ _ _ _ _ _
    · exact lane_downCorners_adj _ _ _ _ _ _ _ _ _
    · exact lane_ztokCorners_adj _ _ _ _ _ _
    · exact lane_nzAnsCorners_adj _ _ _ _ _ _ _
    · exact lane_zAnsCorners_adj _ _ _ _ _ _ _
  · simp at hx

/-- **The consecutive corners of the merge route of a register are adjacent.** -/
theorem lane_mergeSpecs_adj (p : Program) (r : ℕ) : ∀ x ∈ mergeSpecs p r, LaneAdjChain x.2 := by
  intro x hx
  simp only [mergeSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  exact lane_downCorners_adj _ _ _ _ _ _ _ _ _

/-! ### Every route of the machine -/

/-- **Every route of every instruction of a well-formed program is clear of the lanes of every
register** (flights up to the corner windows and extended relay boxes), for a glider on the
lines of the route whose first flight starts on the side of the lanes of its first corner. -/
theorem lane_instrRoute (hp : p.WellFormed) {i : ℕ} (hi : i < p.length) {x : WL × List Corner}
    (hx : x ∈ instrSpecs p i) {g : WL} (hd : g.Dir) (hl : RouteLines g x.2) (r : ℕ) {T : ℤ}
    (hst : ∀ c ∈ x.2.head?, LaneStart p r g T c) : RouteLane p r g x.2 T :=
  lane_routeLane_of x.2 g T hd hl (lane_chain_of r x.2
    (fun c hc => allCorners_valid hp c (instrRoute_corner hi hx c hc))
    (lane_instrSpecs_adj p i x hx)) hst

/-- **The merge route of every register with an `inc` is clear of the lanes of every
register**, for a glider on its lines whose first flight starts low. -/
theorem lane_mergeRoute (hp : p.WellFormed) {r' : ℕ} (hr : r' < numRegs p)
    (hu : mergeUsed p r' = true) {x : WL × List Corner} (hx : x ∈ mergeSpecs p r') {g : WL}
    (hd : g.Dir) (hl : RouteLines g x.2) (r : ℕ) {T : ℤ}
    (hst : ∀ c ∈ x.2.head?, LaneStart p r g T c) : RouteLane p r g x.2 T :=
  lane_routeLane_of x.2 g T hd hl (lane_chain_of r x.2
    (fun c hc => allCorners_valid hp c (mergeRoute_corner hr hu hx c hc))
    (lane_mergeSpecs_adj p r' x hx)) hst

end LP

end LeanTheory.Life
