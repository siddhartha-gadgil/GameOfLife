/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.LaneSep

/-!
# The lane fields of `IncSep` and `HaltSep`

Research note `N-22`, report `R-31` §3 #14–#17. From the clearance facts of `LaneSep`:

* `IncPlan.LaneLow`: the corners of the three routes of an `inc` plan lie at `v ≤ -2347` (the band,
  the slabs of the units, the INC port of the module); `lane_incPlan_low` proves it for the plan
  `incPlan` of every `inc` instruction of a well-formed program.
* For a valid plan with low corners: the footprints of the continue (`lane_contFoot_clear`, before
  the end of the activation) and of the increment thread before the gate
  (`lane_earlyFoot_clear`) are
  low (routes by `lane_route_vlow`, `lane_linkFoot_vlow`; entry chains and the flight out of a
  chain;
  pieces of the machine), the footprint of the increment thread (`lane_incFoot_clear`, for a ready
  register) is low or in the band of module `r` (`ModNear`), hence clear of the lanes of every
  other register.
* **The lane fields of `IncSep`** (`IncLaneSep`, `incLaneSep`, and `incPlan_laneSep` for the plan
  of every `inc` instruction): `modLane`, `grpLane`, `earlyLane`, `lanes`, `laneBody`, `laneAct`
  (the last one for a ready register at `2010`, the only case used by `inc_step`).
* **The lane fields of `HaltSep`** (`haltLanes`, `haltLaneMach`): the control's flight to the halt
  corner, the relay box and the `SW` flight on `v = V_T + 1` are low.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-! ### Low corners -/

/-- **The corners of the three routes of an `inc` plan are low** (`v ≤ -2347`). -/
def IncPlan.LaneLow (P : IncPlan p i r) : Prop :=
  (∀ c ∈ P.csC, c.v ≤ -2347) ∧ (∀ c ∈ P.csR, c.v ≤ -2347) ∧ ∀ c ∈ P.csM, c.v ≤ -2347

/-- The band corners of a link of sub-band `b ≤ N + R` are low. -/
theorem lane_bandCorners_low {b s c H cd : ℤ} {k0 k4 : ℕ} (hb : b ≤ N p + R p)
    (hs : 0 ≤ s ∧ s ≤ 9) :
    ∀ x ∈ bandCorners p b s c H cd k0 k4, x.v ≤ -2347 := by
  have hc := Int.emod_nonneg c (by norm_num : (2 : ℤ) ≠ 0)
  have hc' := Int.emod_lt_of_pos c (by norm_num : (0 : ℤ) < 2)
  have hv := lane_VT_low p
  intro x hx
  simp only [bandCorners, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp only [trackOut, trackBack, track] <;> omega

/-- The corners of a link up to an entry copy `t ≥ 0` of a unit are low. -/
theorem lane_upCorners_low {b s c H : ℤ} {a : ℕ} {t : ℤ} (hb : b ≤ N p + R p) (hs : 0 ≤ s ∧ s ≤ 9)
    (ht : 0 ≤ t) : ∀ x ∈ upCorners p b s c H a t, x.v ≤ -2347 := by
  intro x hx
  simp only [upCorners, upCornersK, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with hx | rfl
  · exact lane_bandCorners_low hb hs x hx
  · have hv := lane_VT_low p
    simp only [destV, sideV]
    omega

/-- The corners of the merge link of register `r < R` are low. -/
theorem lane_mergeCorners_low {e : ℤ} (hr : r < numRegs p) :
    ∀ x ∈ mergeCorners p r e, x.v ≤ -2347 := by
  intro x hx
  simp only [mergeCorners, downCorners, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with hx | rfl
  · refine lane_bandCorners_low ?_ (by norm_num) x hx
    unfold mergeBand R
    omega
  · simp [incPortV]

/-- A copy index from a predecessor number `≥ 0` is `≥ 0`. -/
theorem lane_copyIdx_nonneg {C0 e c : ℤ} (he : 0 ≤ e) : 0 ≤ copyIdx C0 e c := by
  unfold copyIdx
  have := Int.emod_nonneg (C0 - c) (by norm_num : (2 : ℤ) ≠ 0)
  omega

/-- **The corners of the plan of every `inc` instruction are low.** -/
theorem lane_incPlan_low (hins : p[i]? = some (.inc r)) : (incPlan p i r).LaneLow := by
  have hi : i < p.length := (List.getElem?_eq_some_iff.1 hins).1
  have hr : r < numRegs p := lt_numRegs_of_inc hins
  have hR := one_le_R p
  have hb : instrBand i ≤ N p + R p := by unfold instrBand N; omega
  refine ⟨?_, ?_, ?_⟩
  · exact lane_upCorners_low hb (by norm_num) (lane_copyIdx_nonneg (predIdx_nonneg _ _ _ _))
  · exact lane_upCorners_low hb (by norm_num) (lane_copyIdx_nonneg (predIdx_nonneg _ _ _ _))
  · exact lane_mergeCorners_low hr

/-! ### The footprints of the threads -/

/-- The pieces of a list of pieces of the machine are clear of the lanes of every register. -/
theorem lane_dd_clear (hp : p.WellFormed) {L : List Piece} (hL : ∀ x ∈ L, x ∈ machPieces p)
    (r' : ℕ) :
    LaneClear p r' (boxesOf (dd L)) := by
  rw [boxesOf_dd]
  exact (laneClear_boxesOf (machPieces_laneClear hp r')).mono (boxesOf_subset hL)

/-- A set at `v ≤ -2000` is clear of the lanes of every register. -/
theorem laneClear_of_le {r' : ℕ} {S : Set Cell} (h : ∀ c ∈ S, c.1 + c.2 ≤ -2000) :
    LaneClear p r' S :=
  laneClear_of_low fun c hc => (h c hc).trans (by norm_num)

/-- **The continue thread is low** before the end of the activation. -/
theorem IncPlan.lane_contFoot_clear (hp : p.WellFormed) (P : IncPlan p i r) (hv : P.Valid)
    (hlow : P.LaneLow) (r' : ℕ) {j : ℕ} (hj : j < P.Tend - 2010) :
    LaneClear p r' (P.contFoot j) := by
  have hpc := lane_dd_clear hp hv.memC r'
  have hV := lane_VT_low p
  have hu := unitD_uv p i
  have hu1 := unitD_uv p (i + 1)
  unfold IncPlan.contFoot
  split_ifs with h1
  · refine hpc.union (laneClear_of_le fun x hx => lane_linkFoot_vlow (-2000)
      ⟨Or.inl rfl, Or.inl rfl⟩ hv.linesC hv.timedC (fun c hc => by have := hlow.1 c hc; omega)
      ?_ ((congrArg WL.dx hv.finC).trans rfl) ((congrArg WL.dy hv.finC).trans rfl)
      (by omega) j x hx)
    simp only [unitWL, incDWL, WL.shift, WL.vHi, WL.px, WL.py, WL.qt]
    omega
  · refine hpc.union (laneClear_of_le fun x hx => ?_)
    have := lane_chainOut_low p (i + 1) (t := -166 + ((j - (P.Tc - 2010) : ℕ) : ℤ)) (by
      simp only [IncPlan.Tend] at hj
      omega) x hx
    omega

/-- **The increment thread before the gate is low**. -/
theorem IncPlan.lane_earlyFoot_clear (hp : p.WellFormed) (P : IncPlan p i r) (hv : P.Valid)
    (hlow : P.LaneLow) (r' : ℕ) (j : ℕ) : LaneClear p r' (P.earlyFoot j) := by
  have hpc := lane_dd_clear hp hv.memI r'
  have hV := lane_VT_low p
  have hu := unitD_uv p i
  have hum := unitD_uv p (mergeUnit p r)
  have hT1 := le_routeEndX P.csM P.gM P.T1 hv.timedM
  obtain ⟨hM1, hM2⟩ := lane_route_vlow (-2000) P.csM P.gM P.T1 ⟨Or.inl rfl, Or.inl rfl⟩ hv.linesM
    hv.timedM (fun c hc => by have := hlow.2.2 c hc; omega) (by
      simp only [IncPlan.gM, unitWL, haltDWL, WL.shift, WL.vHi, WL.px, WL.py, WL.qt]
      omega)
  unfold IncPlan.earlyFoot
  split_ifs with h1 h2
  · refine hpc.union (laneClear_of_le fun x hx => lane_linkFoot_vlow (-2000)
      ⟨Or.inl rfl, Or.inl rfl⟩ hv.linesR hv.timedR (fun c hc => by have := hlow.2.1 c hc; omega)
      ?_ ((congrArg WL.dx hv.finR).trans rfl) ((congrArg WL.dy hv.finR).trans rfl)
      (by omega) j x hx)
    simp only [unitWL, incRWL, WL.shift, WL.vHi, WL.px, WL.py, WL.qt]
    omega
  · exact hpc.union (laneClear_of_le fun x hx => hM1 _ (by
      change P.T1 + (j - (P.T1 - 2010)) ≤ P.eM
      omega) x hx)
  · refine hpc.union (laneClear_of_le fun x hx => (WL.le_vHi hx).trans ?_)
    have hdx : (route P.gM P.csM).2.dx = 1 := (congrArg WL.dx hv.finM).trans rfl
    have hdy : (route P.gM P.csM).2.dy = -1 := (congrArg WL.dy hv.finM).trans rfl
    rw [WL.vHi_const (by omega) (Or.inl hdx) _ (P.eM : ℤ)]
    exact hM2

/-- **The increment thread is low or in the band of module `r`** (for a ready register at the
start), hence clear of the lanes of every other register. -/
theorem IncPlan.lane_incFoot_clear (hp : p.WellFormed) (P : IncPlan p i r) (hv : P.Valid)
    (hlow : P.LaneLow) {R0 : RegS} (hR : R0.Ready) {r' : ℕ} (hne : r' ≠ r) (j : ℕ) :
    LaneClear p r' (P.incFoot R0 j) := by
  unfold IncPlan.incFoot
  split_ifs with h1
  · exact (P.lane_earlyFoot_clear hp hv hlow r' j).union
      ((lane_regStrip_near p r R0 _).laneClear hne)
  · unfold modRunFoot
    split_ifs with h2
    · exact ((lane_dd_clear hp hv.memI r').union
        ((lane_modFoot_near hv.TgE h2).laneClear hne)).union
        ((lane_regStrip_near p r _ _).laneClear hne)
    · exact (lane_dd_clear hp hv.memI r').union
        ((lane_incRun_near p r ((hR.later _).later 946) _).laneClear hne)

/-! ### The lane fields of `IncSep` -/

/-- **The lane fields of `IncSep`** (`R-31` #14–#17), with the same statements as the fields
`modLane`, `grpLane`, `earlyLane`, `lanes`, `laneBody`, `laneAct` of `IncSep`. -/
structure IncLaneSep (P : IncPlan p i r) (R0 : RegS) : Prop where
  /-- The module part before the increment and the lanes of the register. -/
  modLane : ∀ j < 946, FarApart 2 (boxesOf (dd P.LIraw) ∪ modFoot p r P.km P.Tg j)
    (modLanes p r)
  /-- The register circuit and the lanes of its register. -/
  grpLane : FarApart 2 (boxesOf (modGroup p r)) (modLanes p r)
  /-- The increment thread before the gate and the lanes of the register. -/
  earlyLane : ∀ j < P.Tg - 2010, FarApart 2 (P.earlyFoot j) (modLanes p r)
  /-- The lanes of distinct registers are far apart. -/
  lanes : ∀ r₁ < numRegs p, ∀ r₂ < numRegs p, r₁ ≠ r₂ → FarApart 2 (modLanes p r₁) (modLanes p r₂)
  /-- The machine and the body are far from the lanes of every register. -/
  laneBody : ∀ r' < numRegs p, FarApart 2 (boxesOf (machPieces p) ∪ bodyBox p i) (modLanes p r')
  /-- The machine and the threads are far from the lanes of every other register. -/
  laneAct : ∀ j < P.Tend - 2010, ∀ r' < numRegs p, r' ≠ r →
    FarApart 2 (boxesOf (machPieces p) ∪ (P.contFoot j ∪ P.incFoot R0 j)) (modLanes p r')

/-- **The lane fields of `IncSep` hold for every valid plan with low corners** of a well-formed
program, for a ready register at the start of the threads. -/
theorem incLaneSep (hp : p.WellFormed) (P : IncPlan p i r) (hv : P.Valid) (hlow : P.LaneLow)
    {R0 : RegS} (hR : R0.Ready) : IncLaneSep P R0 := by
  have hV := lane_VT_low p
  refine ⟨fun j hj => ?_, lane_modGroup_far p r,
    fun j _ => (P.lane_earlyFoot_clear hp hv hlow r j).farApart,
    fun r₁ _ r₂ _ h => modLanes_far p h, fun r' _ => ?_, fun j hj r' _ hne => ?_⟩
  · exact ((lane_dd_clear hp hv.memI r).union (modFoot_laneClear hv.TgE (by omega))).farApart
  · refine ((laneClear_boxesOf (machPieces_laneClear hp r')).union
      (laneClear_of_le fun c hc => ?_)).farApart
    have := lane_bodyBox_low p i c hc
    omega
  · exact ((laneClear_boxesOf (machPieces_laneClear hp r')).union
      ((P.lane_contFoot_clear hp hv hlow r' hj).union
        (P.lane_incFoot_clear hp hv hlow hR hne j))).farApart

/-- **The lane fields of `IncSep` for the plan of every `inc` instruction** of a well-formed
program, for a ready register at `2010`. -/
theorem incPlan_laneSep (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {R0 : RegS}
    (hR : R0.Ready) : IncLaneSep (incPlan p i r) R0 :=
  incLaneSep hp _ (incPlan_valid hp hins) (lane_incPlan_low hins) hR

/-! ### The lane fields of `HaltSep` -/

/-- **The halt glider is low**: the control's flight to the halt corner, the relay box of the
corner and the `SW` flight on `v = V_T + 1` (`v ≤ V_T + 30`). -/
theorem lane_haltFoot_low (p : Program) (a j : ℕ) :
    ∀ c ∈ haltFoot p a j, c.1 + c.2 ≤ VT p + 30 := by
  have hu := unitD_uv p a
  have hV := lane_VT_low p
  intro x hx
  unfold haltFoot at hx
  split_ifs at hx with h1 h2
  · obtain ⟨c1, c2, c3, c4⟩ := hx
    rw [ctrlWL_eq] at c2 c4
    simp only [WL.px, WL.py, WL.qt] at c2 c4
    omega
  · obtain ⟨y, ⟨c1, c2, c3, c4⟩, rfl⟩ := hx
    simp only [haltCorner, cornerV, rfX, rfY, rfCU, rfCV, trackOut, track, Prod.fst_add,
      Prod.snd_add]
    omega
  · obtain ⟨c1, c2, c3, c4⟩ := hx
    rw [haltOutWL_eq] at c2 c4
    simp only [WL.px, WL.py, WL.qt] at c2 c4
    omega

/-- **The field `lanes` of `HaltSep`**: the lanes of distinct registers are far apart. -/
theorem haltLanes (p : Program) :
    ∀ r₁ < numRegs p, ∀ r₂ < numRegs p, r₁ ≠ r₂ → FarApart 2 (modLanes p r₁) (modLanes p r₂) :=
  fun _ _ _ _ h => modLanes_far p h

/-- **The field `laneMach` of `HaltSep`**: the pieces and the halt glider are far from the lanes
of every register, for a well-formed program. -/
theorem haltLaneMach (hp : p.WellFormed) (a : ℕ) :
    ∀ j < haltTime p a, ∀ r < numRegs p,
      FarApart 2 (boxesOf (machPieces p) ∪ haltFoot p a j) (modLanes p r) := by
  intro j _ r _
  have hV := lane_VT_low p
  refine ((laneClear_boxesOf (machPieces_laneClear hp r)).union
    (laneClear_of_low fun c hc => ?_)).farApart
  have := lane_haltFoot_low p a j c hc
  omega

end LP

end LeanTheory.Life
