/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecStepThread
public import LeanTheory.Theory.Life.RouteSep7
public import LeanTheory.Theory.Life.LaneSep
public import LeanTheory.Theory.Life.LaneSep2

/-!
# The true route and lane fields of `DecSep`

Research note `N-22`. `DecSep` (`ActivationDecStepThread`) is unsatisfiable as stated
(`DecSepFalse.dsep_not_decSep`); the fields proved here hold for every `decJz` instruction of a
well-formed program and are unaffected by the defects found there:

* `dsep_sepC`, `dsep_sepN`, `dsep_sepZ`: the routes of `C`, `KNZ`, `KZ` from the end of the body
  (`4260`) are the first three routes of `decSpecs`, undelayed: `decLinks_sep` with `d = 0`;
* `dsep_grpLane`, `dsep_lanes`: the register circuit and the lanes of other registers are far
  from the lanes (`lane_modGroup_far`, `modLanes_far`);
* `dsep_laneBody`: the machine and the region of the `dec` body are far from the lanes of every
  register (the body region lies at `x + y ≤ V_U + 1554`, far below the lanes).

* `dsep_sepAN`, `dsep_sepAZ`: the answer routes from the dispatch (the captures run `692` / `672`
  generations, `stationNZ_captureE`): the answer is then past its station (`u ≤ U_r - 571` for
  NZ, `v ≥ 717` for Z), so `decLinks_sep` applies.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- The routes of a `decJz` instruction are those of `decSpecs`. -/
theorem dsep_instrSpecs (hi : p[i]? = some (.decJz r z)) :
    instrSpecs p i =
      [(unitWL p i decLWL, decCornN p i r), (unitWL p i decRWL, decCornC p i r),
        (unitWL p i decDWL, decCornZ p i r), (decGN p i r, decMkN p i r (decEA p i r)),
        (decGZ p i r, decMkZ p i r z (decEB p i r z))] := by
  rw [← decSpecs_eq]
  simp [instrSpecs, hi]

/-- The first three routes of a `decJz` instruction, from the end of the body. -/
theorem dsep_first3 (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g : WL}
    {cs : List Corner} (hx : (g, cs) ∈ (instrSpecs p i).take 3) :
    RouteSepX (machPieces p) (machRegion p) g cs ((4260 : ℕ) : ℤ) := by
  have h := (decLinks_sep hp hi (d := 0) (by norm_num) (T := ((4260 : ℕ) : ℤ))).1
    (by norm_num) _ hx
  rwa [WL.shift_zero_rs] at h

/-- **`DecSep.sepC`** for every `decJz` instruction of a well-formed program. -/
theorem dsep_sepC (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    RouteSepX (machPieces p) (machRegion p) (unitWL p i decRWL) (decCornC p i r)
      ((4260 : ℕ) : ℤ) :=
  dsep_first3 hp hi (by rw [dsep_instrSpecs hi]; simp)

/-- **`DecSep.sepN`** for every `decJz` instruction of a well-formed program. -/
theorem dsep_sepN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    RouteSepX (machPieces p) (machRegion p) (unitWL p i decLWL) (decCornN p i r)
      ((4260 : ℕ) : ℤ) :=
  dsep_first3 hp hi (by rw [dsep_instrSpecs hi]; simp)

/-- **`DecSep.sepZ`** for every `decJz` instruction of a well-formed program. -/
theorem dsep_sepZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    RouteSepX (machPieces p) (machRegion p) (unitWL p i decDWL) (decCornZ p i r)
      ((4260 : ℕ) : ℤ) :=
  dsep_first3 hp hi (by rw [dsep_instrSpecs hi]; simp)

/-- **`DecSep.sepAN`**: the route of the NZ answer from its dispatch at `decDispN` (the answer is
past its station: `u ≤ U_r - 571` and decreasing), for every `decJz` instruction. -/
theorem dsep_sepAN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    RouteSepX (machPieces p) (machRegion p) (decGN p i r) (decCsN p i r)
      ((decDispN p i r : ℕ) : ℤ) := by
  have h := (decLinks_sep hp hi (d := 0) (by norm_num) (T := ((decDispN p i r : ℕ) : ℤ))).2.1
    (decGN p i r, decMkN p i r (decEA p i r)) (by rw [dsep_instrSpecs hi]; simp)
  rw [WL.shift_zero_rs] at h
  refine h fun t ht => ?_
  have hu := modD_uv p r
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  simp only [decDispN] at ht
  push_cast at ht
  simp only [WL.cu, WL.px, WL.py, WL.qt, decGN, modWL, nzAnsWL, WL.shift]
  omega

/-- **`DecSep.sepAZ`**: the route of the Z answer from its dispatch at `decDispZ` (the answer is
past the Z stations: `v ≥ 717` and increasing), for every `decJz` instruction. -/
theorem dsep_sepAZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    RouteSepX (machPieces p) (machRegion p) (decGZ p i r) (decCsZ p i r z)
      ((decDispZ p i r : ℕ) : ℤ) := by
  have h := (decLinks_sep hp hi (d := 0) (by norm_num) (T := ((decDispZ p i r : ℕ) : ℤ))).2.2
    (decGZ p i r, decMkZ p i r z (decEB p i r z)) (by rw [dsep_instrSpecs hi]; simp)
  rw [WL.shift_zero_rs] at h
  refine h fun t ht => ?_
  have hu := modD_uv p r
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  simp only [decDispZ] at ht
  push_cast at ht
  simp only [WL.cv, WL.px, WL.py, WL.qt, decGZ, modWL, zAnsWL, WL.shift]
  omega

/-- **`DecSep.grpLane`**: the register circuit is far from the lanes of its register. -/
theorem dsep_grpLane (p : Program) (r : ℕ) : FarApart 2 (boxesOf (modGroup p r)) (modLanes p r) :=
  lane_modGroup_far p r

/-- **`DecSep.lanes`**: the lanes of distinct registers are far apart. -/
theorem dsep_lanes (p : Program) :
    ∀ r₁ < numRegs p, ∀ r₂ < numRegs p, r₁ ≠ r₂ → FarApart 2 (modLanes p r₁) (modLanes p r₂) :=
  fun _ _ _ _ h => modLanes_far p h

/-- The components of the body run of a `dec` unit lie at `x + y ≤ 1554` (unit frame). -/
theorem dsep_bodyDecRegL_v : DecAllSub {c : Cell | c.1 + c.2 ≤ 1554} bodyDecRegL := by
  simp only [bodyDecRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact fun c ⟨⟨_, _, _, _⟩, _, _, _, _⟩ => show c.1 + c.2 ≤ 1554 by omega
    | trivial

/-- The region of the body of the `dec` unit `i` is low: `x + y ≤ V_U + 1554`. -/
theorem dsep_bodyDecBox_low (p : Program) (i : ℕ) :
    ∀ c ∈ bodyDecBox p i, c.1 + c.2 ≤ VU p + 1554 := by
  rintro _ ⟨c, hc, rfl⟩
  have h : c.1 + c.2 ≤ 1554 := unionL_subset_dec dsep_bodyDecRegL_v hc
  have := unitD_uv p i
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- **`DecSep.laneBody`**: the machine and the body region are far from the lanes of every
register. -/
theorem dsep_laneBody (hp : p.WellFormed) (i : ℕ) :
    ∀ r' < numRegs p, FarApart 2 (boxesOf (machPieces p) ∪ bodyDecBox p i) (modLanes p r') := by
  intro r' _
  have hV := lane_VT_low p
  refine (LaneClear.union (laneClear_boxesOf (machPieces_laneClear hp r'))
    (laneClear_of_low fun c hc => ?_)).farApart
  have := dsep_bodyDecBox_low p i c hc
  omega

/-! ### The control and the lanes of its register -/

/-- The corners of the route of `C` are low (`v ≤ -2347`). -/
theorem dsep_cornC_low (hi : p[i]? = some (.decJz r z)) :
    ∀ c ∈ decCornC p i r, c.v + 70 ≤ -2000 := by
  have hl : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have hR := one_le_R p
  have hb : instrBand i ≤ N p + R p := by unfold instrBand N; omega
  have hD := one_le_D p
  have hj := callerIdx_lt_D p hi
  intro c hc
  simp only [decCornC, downCorners, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with hc | rfl
  · have := lane_bandCorners_low hb (by norm_num) c hc
    omega
  · simp only [decPortV]
    have : (D p : ℤ) = (numCallers p : ℤ) := rfl
    omega

/-- **The footprint of the control is low** (`v ≤ -2000`) before the register run. -/
theorem dsep_footC_low (hi : p[i]? = some (.decJz r z)) {t : ℕ} (h0 : 4260 ≤ t)
    (ht : t < decTS p i r) :
    ∀ x ∈ decFootC p i r t, x.1 + x.2 ≤ -2000 := by
  have hu := modD_uv p r
  have hui := unitD_uv p i
  have hV := lane_VT_low p
  have hm := decM_cast p hi
  obtain ⟨h1, h2⟩ := lane_route_vlow (-2000) (decCornC p i r) (unitWL p i decRWL) 4260
    ⟨Or.inl rfl, Or.inl rfl⟩ (decC_lines p i r).1 (decC_timedX p hi) (dsep_cornC_low hi) (by
      simp only [unitWL, decRWL, WL.shift, WL.vHi, WL.px, WL.py, WL.qt]
      omega)
  intro x hx
  unfold decFootC at hx
  split_ifs at hx with ha hb hc
  · unfold flyFoot at hx
    split_ifs at hx with hd
    · exact h1 (t - 4260) (by omega) x hx
    · refine (WL.le_vHi hx).trans ?_
      have hg := decGC_eq p i r
      have hdx : (route (unitWL p i decRWL) (decCornC p i r)).2.dx = 1 := by
        change (decGC p i r).dx = 1; rw [hg]
      rw [WL.vHi_const (by change (decGC p i r).dx + (decGC p i r).dy = 0; rw [hg]; rfl)
        (Or.inl hdx) _ (routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 : ℤ)]
      exact h2
  · obtain ⟨c, ⟨c1, c2, c3, c4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · obtain ⟨d, ⟨j, hj, d1, d2, d3, d4⟩, rfl⟩ := hx
    simp only [Prod.fst_add, Prod.snd_add] at *
    have : (j : ℤ) ≤ (decM p i r : ℤ) := by omega
    nlinarith
  · obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hx
    have e1 : decTS p i r = decTB p i r + 1771 := by unfold decTS decTB; omega
    simp only [cp0WL, WL.px, WL.py, WL.qt, Prod.fst_add, Prod.snd_add] at *
    omega

/-- **`DecSep.nQ1a`** (and `zQ1a`): the control and its pieces are far from the lanes of its
register before the register run. -/
theorem dsep_nQ1a (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decTS p i r →
      FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t) (modLanes p r) := by
  intro t h0 ht
  exact (LaneClear.union (laneClear_boxesOf fun g hg =>
    machPieces_laneClear hp r g (decLC_mem hi g hg))
    (laneClear_of_le fun x hx => dsep_footC_low hi h0 ht x hx)).farApart

end LP

end LeanTheory.Life
