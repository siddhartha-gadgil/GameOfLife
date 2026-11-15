/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.MainTheorem
public import LeanTheory.Theory.Life.ActivationIncEntrySep

/-!
# `IncSep` is unsatisfiable: five flight fields fail at the ends of their flights

Research note `N-22`. The separation structure `IncSep` (`ActivationIncStep`) asks, in five of its
fields, a glider box to be far (`FarApart 2`) from a piece **up to the generation before that piece
starts to react with the glider** (or from the generation the glider leaves it). At those
generations the glider box touches (or overlaps) the box of the piece, exactly as the corner
reflectors in the former conditions `RouteSep` / `RouteSepM` (`ActivationHalt.not_far_before_meet`,
`RouteSep.rfIn_near`). For **every** plan (every program, every `inc` instruction, every register
value) the following fail:

* `fl1` at `j = 890` (one generation before `RF_J` is met, `Tg + 891`): the glider box
  `x ∈ [X - 873, X - 869]`, `y ∈ [Y - 1046, Y - 1042]` (`X = modDX`, `Y = modDY`) overlaps the
  box of `RF_J`, `x ∈ [X - 872, X - 850]`, `y ∈ [Y - 1042, Y - 1034]` (`isep_fl1_near`). It needs
  only the arrival time `Tg = 194 + 30 km` (`IncPlan.Valid.TgE`).
* `fl2` at `j = 921` (the first generation of the flight from `RF_J`): the glider box
  `y ∈ [Y - 1048, Y - 1044]` is `2` rows below the box of `RF_J` (`isep_fl2_near`).
* `flyC`, `flyR` at `j = T0 - 1` (the generation before the side reaction of the entry copy `t`):
  the glider box `x ∈ [dx + 42, dx + 46]`, `y ∈ [dy + 32, dy + 36]` (copy frame `dx, dy`)
  overlaps the box `[0, 90] × [0, 32]` of the OR gate of copy `t`, which is a piece of the thread
  (`isep_side_near`); the flight is not empty (`routeEndX + 2 ≤ T0`, `upLink_plan`).
* `flyM` at `j = Tg - 1`: the same at the INC OR gate of module `r` (`isep_gate_near`); the
  flight is not empty (`isep_eM_lt`: `eM < Tg`).

Consequences: `isep_not_incSep` (`¬ IncSep P R0` for every plan with `Tg = 194 + 30 km`, in
particular for `incPlan p i r` of every `inc` instruction of a well-formed program),
`isep_not_machineSteps` (no well-formed program whose first instruction is an `inc` has
`MachineSteps`), and `isep_not_all_machineSteps`: the hypothesis of the final corollary
`exists_not_computablePred_everAlive` is false (the program `[inc 0, halt]`). `IncSep` (and the
hypotheses `hfly` of `link_entryX`, `hfl1`, `hfl2` of `module_pre`) must be reformulated with
windows at the side input of an OR gate and at `RF_J`, as was done for the route corners
(`RouteSepX`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-- A cell is near itself. -/
theorem isep_near_self (c : Cell) : Near 2 c c := by
  simp only [Near]
  omega

/-! ### `RF_J` -/

/-- **The glider to `RF_J` overlaps `RF_J` one generation before the meeting** (`j = 890`). -/
theorem isep_fl1_near (p : Program) (r : ℕ) (k : ℤ) (Tg : ℕ) (hTg : (Tg : ℤ) = 194 + 30 * k) :
    ¬ FarApart 2 ((gateOutWL p r k).box ((Tg : ℤ) + ((890 : ℕ) : ℤ))) (rfJP p r).box := by
  intro h
  have hU := modD_uv p r
  refine h (modDX p r - 870, modDY p r - 1042) ?_ (modDX p r - 870, modDY p r - 1042) ?_
    (isep_near_self _)
  · simp only [WL.box, Box, Set.mem_ofPred_eq, WL.px, WL.py, WL.qt, gateOutWL, modWL, WL.shift]
    omega
  · simp only [rfJP, PSpec.piece, Piece.place, Piece.box, Box, Base.piece, rfP, Set.mem_ofPred_eq]
    omega

/-- **The glider from `RF_J` is `2` rows from `RF_J` when its flight starts** (`j = 921`). -/
theorem isep_fl2_near (p : Program) (r : ℕ) (k : ℤ) (Tg : ℕ) (hTg : (Tg : ℤ) = 194 + 30 * k) :
    ¬ FarApart 2 ((rfJOutWL p r k).box ((Tg : ℤ) + ((921 : ℕ) : ℤ))) (rfJP p r).box := by
  intro h
  have hU := modD_uv p r
  refine h (modDX p r - 860, modDY p r - 1044) ?_ (modDX p r - 860, modDY p r - 1042) ?_ ?_
  · simp only [WL.box, Box, Set.mem_ofPred_eq, WL.px, WL.py, WL.qt, rfJOutWL, modWL, incInWL,
      WL.shift]
    omega
  · simp only [rfJP, PSpec.piece, Piece.place, Piece.box, Box, Base.piece, rfP, Set.mem_ofPred_eq]
    omega
  · simp only [Near]
    omega

/-- `RF_J` is a piece of the increment thread. -/
theorem isep_rfJ_mem (P : IncPlan p i r) : rfJP p r ∈ P.LIraw := by
  simp [IncPlan.LIraw]

/-- The INC OR gate is a piece of the increment thread. -/
theorem isep_gate_mem (P : IncPlan p i r) : gateP p r ∈ P.LIraw := by
  simp [IncPlan.LIraw]

/-- **The field `fl1` of `IncSep` fails for every plan** with the arrival time of `Valid`. -/
theorem isep_not_fl1 (P : IncPlan p i r) (hTg : (P.Tg : ℤ) = 194 + 30 * P.km) :
    ¬ ∀ j : ℕ, 134 ≤ j → j < 891 → ∀ h ∈ P.LIraw,
      FarApart 2 ((gateOutWL p r P.km).box ((P.Tg : ℤ) + j)) h.box :=
  fun hf => isep_fl1_near p r P.km P.Tg hTg (hf 890 (by norm_num) (by norm_num) _ (isep_rfJ_mem P))

/-- **The field `fl2` of `IncSep` fails for every plan** with the arrival time of `Valid`. -/
theorem isep_not_fl2 (P : IncPlan p i r) (hTg : (P.Tg : ℤ) = 194 + 30 * P.km) :
    ¬ ∀ j : ℕ, 921 ≤ j → j < 946 → ∀ h ∈ P.LIraw,
      FarApart 2 ((rfJOutWL p r P.km).box ((P.Tg : ℤ) + j)) h.box :=
  fun hf => isep_fl2_near p r P.km P.Tg hTg (hf 921 (by norm_num) (by norm_num) _ (isep_rfJ_mem P))

/-! ### The side inputs of the OR gates -/

/-- The OR gate of entry copy `t` of unit `a`, as a piece. -/
def isepCopy (p : Program) (a t : ℕ) : Piece :=
  (⟨.orGate, unitDX p a - 35 * (t : ℤ), unitDY p a - 64 * (t : ℤ), 14 * t % 30⟩ : PSpec).piece

/-- The OR gate of copy `t` is one of the copies `0 … t`. -/
theorem isep_copy_mem (p : Program) (a t : ℕ) : isepCopy p a t ∈ chainPieces p a t :=
  List.mem_map.2 ⟨_, List.mem_map.2 ⟨t, List.mem_range.2 (by omega), rfl⟩, rfl⟩

/-- **The glider on the side window of entry copy `t` overlaps the OR gate of the copy one
generation before its arrival time** `T0` (offset `δ ∈ {4, 5}`). -/
theorem isep_side_near (p : Program) (a t : ℕ) {δ k : ℤ} (hδ : δ = 4 ∨ δ = 5) {T0 : ℕ}
    (hT0 : (T0 : ℤ) = 180 + 30 * k + 16 * (t : ℤ) % 30) (h1 : 1 ≤ T0) :
    ¬ FarApart 2 (((destWin p a t).shift 0 0 (δ + 30 * k)).box ((T0 - 1 : ℕ) : ℤ))
      (isepCopy p a t).box := by
  intro h
  have hu := unitD_uv p a
  have hT : ((T0 - 1 : ℕ) : ℤ) = 179 + 30 * k + 16 * (t : ℤ) % 30 := by omega
  refine h (unitDX p a + 44 - 35 * t, unitDY p a + 32 - 64 * t) ?_
    (unitDX p a + 44 - 35 * t, unitDY p a + 32 - 64 * t) ?_ (isep_near_self _)
  · rw [hT]
    simp only [WL.box, Box, Set.mem_ofPred_eq, WL.px, WL.py, WL.qt, destWin, unitWL, sideWL,
      WL.shift]
    rcases hδ with rfl | rfl <;> omega
  · simp only [isepCopy, PSpec.piece, Piece.place, Piece.box, Box, Base.piece, orGateP,
      Set.mem_ofPred_eq]
    omega

/-- **The glider on the INC window of module `r` overlaps the INC OR gate one generation before
its arrival time** `Tg = 194 + 30 k`. -/
theorem isep_gate_near (p : Program) (r : ℕ) {δ k : ℤ} (hδ : δ = 4 ∨ δ = 5) {Tg : ℕ}
    (hTg : (Tg : ℤ) = 194 + 30 * k) :
    ¬ FarApart 2 (((modWL p r incWin).shift 0 0 (δ + 30 * k)).box ((Tg - 1 : ℕ) : ℤ))
      (gateP p r).box := by
  intro h
  have hU := modD_uv p r
  have hT : ((Tg - 1 : ℕ) : ℤ) = 193 + 30 * k := by omega
  refine h (modDX p r - 1088, modDY p r - 1259) ?_ (modDX p r - 1088, modDY p r - 1259) ?_
    (isep_near_self _)
  · rw [hT]
    simp only [WL.box, Box, Set.mem_ofPred_eq, WL.px, WL.py, WL.qt, modWL, incWin, WL.shift]
    rcases hδ with rfl | rfl <;> omega
  · simp only [gateP, incGateSpec, PSpec.piece, Piece.place, Piece.box, Box, Base.piece, orGateP,
      Set.mem_ofPred_eq]
    omega

/-- **The field `flyC` fails** for a valid plan whose continue leaves its last corner window
before `T0c - 1`. -/
theorem isep_not_flyC (P : IncPlan p i r) (hv : P.Valid)
    (he : routeEndX (unitWL p i incDWL) P.csC 2010 + 1 ≤ P.T0c) :
    ¬ ∀ j : ℕ, routeEndX (unitWL p i incDWL) P.csC 2010 ≤ j → j < P.T0c → ∀ h ∈ P.LCraw,
      FarApart 2 ((route (unitWL p i incDWL) P.csC).2.box j) h.box := by
  intro hf
  have h := hf (P.T0c - 1) (by omega) (by omega) (isepCopy p (i + 1) P.tc)
    (List.mem_append_right _ (isep_copy_mem p (i + 1) P.tc))
  rw [hv.finC] at h
  exact isep_side_near p (i + 1) P.tc hv.δcR hv.T0cE (by omega) h

/-- **The field `flyR` fails** for a valid plan whose INC link leaves its last corner window
before `T0l - 1`. -/
theorem isep_not_flyR (P : IncPlan p i r) (hv : P.Valid)
    (he : routeEndX (unitWL p i incRWL) P.csR 2010 + 1 ≤ P.T0l) :
    ¬ ∀ j : ℕ, routeEndX (unitWL p i incRWL) P.csR 2010 ≤ j → j < P.T0l → ∀ h ∈ P.LIraw,
      FarApart 2 ((route (unitWL p i incRWL) P.csR).2.box j) h.box := by
  intro hf
  have hm : isepCopy p (mergeUnit p r) P.tl ∈ P.LIraw := by
    have := isep_copy_mem p (mergeUnit p r) P.tl
    simp only [IncPlan.LIraw, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr this)))
  have h := hf (P.T0l - 1) (by omega) (by omega) _ hm
  rw [hv.finR] at h
  exact isep_side_near p (mergeUnit p r) P.tl hv.δlR hv.T0lE (by omega) h

/-- **The field `flyM` fails** for a valid plan whose merge link leaves its last corner window
before `Tg - 1`. -/
theorem isep_not_flyM (P : IncPlan p i r) (hv : P.Valid) (he : P.eM + 1 ≤ P.Tg) :
    ¬ ∀ j : ℕ, P.eM ≤ j → j < P.Tg → ∀ h ∈ P.LIraw,
      FarApart 2 ((route P.gM P.csM).2.box j) h.box := by
  intro hf
  have h := hf (P.Tg - 1) (by omega) (by omega) _ (isep_gate_mem P)
  rw [hv.finM] at h
  exact isep_gate_near p r hv.δmR hv.TgE h

/-! ### The flights of the plan `incPlan` are not empty -/

/-- **The continue of `incPlan` leaves its last corner window at least `2` generations before
its arrival** (`upLink_plan`). -/
theorem isep_endC_lt (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    routeEndX (unitWL p i incDWL) (incPlan p i r).csC 2010 + 2 ≤ (incPlan p i r).T0c := by
  have hi1 : i + 1 < p.length := succ_lt_of_inc hp hins
  have hbi : 0 ≤ instrBand i := by unfold instrBand; omega
  have hec : 0 ≤ predIdx p (i + 1) i 0 ∧ predIdx p (i + 1) i 0 < P p :=
    ⟨predIdx_nonneg _ _ _ _, predIdx_lt_P p hins (by simp [predContrib]) (by omega)⟩
  have hGe : 0 ≤ incG p i r := G_nonneg _
  have hecB : 0 ≤ incEc p i r ∧ incEc p i r ≤ 14 := solveE_bounds _ _ _
  have hHc := fixp_bounds (HI p - 62 - incG p i r - 2 * incEc p i r) ((A p i + incD) % 2)
  obtain ⟨-, -, -, -, -, eC⟩ := upLink_plan p i (i + 1) incD 605 (instrBand i) 0
    (hairCont p (incG p i r) (incEc p i r) (A p i + incD)) (predIdx p (i + 1) i 0)
    (Or.inl ⟨rfl, rfl⟩) hbi (by norm_num) (hairCont_par _ _ _ _)
    (by unfold hairCont; omega) hec (g := unitWL p i incDWL)
    (t := incTc p i) (cs := incMkc p i (incG p i r) (incEc p i r)) rfl rfl rfl
  have hxc : (route (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r))).2.tau -
      (destWin p (i + 1) (incTc p i)).tau = incXc p i r := rfl
  rw [hxc] at eC
  have h0 := Int.natCast_nonneg
    (routeEndX (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r)) 2010)
  have hT : (((180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30).toNat : ℕ) : ℤ) =
      180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30 := Int.toNat_of_nonneg (by omega)
  change routeEndX (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r)) 2010 + 2 ≤
    (180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30).toNat
  have : ((routeEndX (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r)) 2010 + 2 : ℕ) :
      ℤ) ≤ (((180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30).toNat : ℕ) : ℤ) := by
    rw [hT]; push_cast; omega
  exact_mod_cast this

/-- **The INC link of `incPlan` leaves its last corner window at least `2` generations before
its arrival** (`upLink_plan`). -/
theorem isep_endR_lt (hins : p[i]? = some (.inc r)) :
    routeEndX (unitWL p i incRWL) (incPlan p i r).csR 2010 + 2 ≤ (incPlan p i r).T0l := by
  have hr : r < numRegs p := lt_numRegs_of_inc hins
  have hbi : 0 ≤ instrBand i := by unfold instrBand; omega
  have hel : 0 ≤ predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0) ∧
      predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0) < P p :=
    ⟨predIdx_nonneg _ _ _ _, predIdx_lt_P p hins (by simp [predContrib]) (by omega)⟩
  have helB : 0 ≤ incEl p i r ∧ incEl p i r ≤ 14 := solveE_bounds _ _ _
  obtain ⟨-, -, -, -, -, eR⟩ := upLink_plan p i (p.length + r) incR 1029 (instrBand i) 1
    (hairReg p 1 (incEl p i r) (A p i + incR))
    (predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0))
    (Or.inr ⟨rfl, rfl⟩) hbi (by norm_num) (hairReg_par _ _ _ _)
    (by have := fixp_bounds (HI p + 90 * 1 - 2 * incEl p i r) ((A p i + incR) % 2)
        unfold hairReg; omega) hel (g := unitWL p i incRWL)
    (t := incTl p i r) (cs := incMkl p i r (incEl p i r)) rfl
    (by rw [unitC0_merge]; rfl) rfl
  have hxl : (route (unitWL p i incRWL) (incMkl p i r (incEl p i r))).2.tau -
      (destWin p (p.length + r) (incTl p i r)).tau = incXl p i r := rfl
  rw [hxl] at eR
  have h0 := Int.natCast_nonneg (routeEndX (unitWL p i incRWL) (incMkl p i r (incEl p i r)) 2010)
  have hT : ((incT0l p i r : ℕ) : ℤ) = 180 + 30 * (incXl p i r / 30) + 16 * incTl p i r % 30 :=
    Int.toNat_of_nonneg (by omega)
  change routeEndX (unitWL p i incRWL) (incMkl p i r (incEl p i r)) 2010 + 2 ≤ incT0l p i r
  have : ((routeEndX (unitWL p i incRWL) (incMkl p i r (incEl p i r)) 2010 + 2 : ℕ) : ℤ) ≤
      ((incT0l p i r : ℕ) : ℤ) := by
    rw [hT]; push_cast; omega
  exact_mod_cast this

/-- **The merge link of `incPlan` leaves its last corner window before the arrival at the INC
gate** (the computation of `incPlan_valid`, with the strict inequality). -/
theorem isep_eM_lt (hins : p[i]? = some (.inc r)) :
    (incPlan p i r).eM + 1 ≤ (incPlan p i r).Tg := by
  have hr : r < numRegs p := lt_numRegs_of_inc hins
  have hR : (r : ℤ) < R p := by unfold R; exact_mod_cast hr
  have hel : 0 ≤ predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0) ∧
      predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0) < P p :=
    ⟨predIdx_nonneg _ _ _ _, predIdx_lt_P p hins (by simp [predContrib]) (by omega)⟩
  have tl0 : 0 ≤ incTl p i r := (incTl_range hins).1
  have htlN : (((incTl p i r).toNat : ℕ) : ℤ) = incTl p i r := Int.toNat_of_nonneg tl0
  have hT0l : ((incT0l p i r : ℕ) : ℤ) = 180 + 30 * (incXl p i r / 30) + 16 * incTl p i r % 30 :=
    Int.toNat_of_nonneg (by
      have h2 := isep_endR_lt hins
      change _ + 2 ≤ incT0l p i r at h2
      unfold incT0l at h2
      omega)
  have hT1 : ((incT1 p i r : ℕ) : ℤ) =
      180 + 30 * (incXl p i r / 30) + 16 * incTl p i r % 30 + 134 + incTl p i r * 254 := by
    unfold incT1
    push_cast
    rw [hT0l, htlN]
    ring
  have hD : ((incT1 p i r : ℤ) + 166 - 1080) % 30 = 0 := by rw [hT1]; omega
  have hrd := route_delay _ hD (unitWL p (p.length + r) haltDWL) (mergeCorners p r (mergeE p r))
  have hA := A_even p ((p.length + r : ℕ) : ℤ)
  have hVU := VU_even p
  have hlane0 : (unitWL p (p.length + r) haltDWL).lane = A p ((p.length + r : ℕ) : ℤ) + haltD := by
    simp only [WL.shift, unitWL, haltDWL, unitDX, unitDY, haltD]
    omega
  obtain ⟨-, dx0, dy0, th0⟩ := mergeCorners_lines p r (mergeE p r) rfl rfl hlane0
  have heM : 0 ≤ mergeE p r := (solveE_bounds _ _ _).1
  have tM := mergeLink_timedX p hR (mergeE p r) heM ((incT1 p i r : ℤ) + 166 - 1080)
    (incT1 p i r) (by omega)
  have hxm : (route (unitWL p (p.length + r) haltDWL) (mergeCorners p r (mergeE p r))).2.tau +
      ((incT1 p i r : ℤ) + 166 - 1080) - (modWL p r incWin).tau = incXm p i r := rfl
  have oM : incXm p i r % 30 = 4 ∨ incXm p i r % 30 = 5 := by
    have := mergeLink_offset p r
    rw [← hxm]
    omega
  have hU := U_even p r
  have hwin : (modWL p r incWin).tau = 4543 - 2 * U p r := by
    simp only [modWL, incWin, WL.shift, modDX]
    omega
  have hend : (routeEndX ((unitWL p (p.length + r) haltDWL).shift 0 0
      ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r)) (incT1 p i r) : ℤ) =
      (route ((unitWL p (p.length + r) haltDWL).shift 0 0
        ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r))).2.tau -
        (rfOut 4).tau + 4 * (rfOut 4).dx * rfX 4 (U p r + incChan p) incPortV - 20 :=
    routeEndX_snoc (bandCorners p (mergeBand p r) 0 (A p (p.length + r) + haltD)
      (hairReg p 0 (mergeE p r) (A p (p.length + r) + haltD)) (U p r + incChan p) 3 2)
      ⟨4, U p r + incChan p, incPortV, .left r (2 * D p)⟩ _ _ tM
  have hpar := (incChan_parity p (p.length + r) r).2
  have hch : incChan p ≤ uL := (leftChan_in_extent p (idx := 2 * D p) (v := incPortV)
    ⟨by have := one_le_D p; omega, by have := one_le_D p; omega⟩).2
  have hfin : (route ((unitWL p (p.length + r) haltDWL).shift 0 0
      ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r))).2.tau =
      incXm p i r + (4543 - 2 * U p r) := by
    rw [hrd, ← hxm, hwin]
    simp only [WL.shift]
    ring
  rw [hfin] at hend
  simp only [rfOut, rfX, rfCU, rfCV] at hend
  have hTgN : (((194 + 30 * (incXm p i r / 30)).toNat : ℕ) : ℤ) = 194 + 30 * (incXm p i r / 30) :=
    Int.toNat_of_nonneg (by
      have := Int.natCast_nonneg (routeEndX ((unitWL p (p.length + r) haltDWL).shift 0 0
        ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r)) (incT1 p i r))
      simp only [incPortV, uL] at hend hpar hch
      omega)
  have h : (routeEndX ((unitWL p (p.length + r) haltDWL).shift 0 0
      ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r)) (incT1 p i r) : ℤ) + 1 ≤
      (((194 + 30 * (incXm p i r / 30)).toNat : ℕ) : ℤ) := by
    rw [hTgN]
    simp only [incPortV, uL] at hend hpar hch
    omega
  have e2 : (incPlan p i r).eM = routeEndX ((unitWL p (p.length + r) haltDWL).shift 0 0
      ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r)) (incT1 p i r) := rfl
  have e3 : (incPlan p i r).Tg = (194 + 30 * (incXm p i r / 30)).toNat := rfl
  rw [e2, e3]
  exact_mod_cast h

/-! ### `IncSep` is unsatisfiable -/

/-- **No plan with the arrival time `Tg = 194 + 30 km` has the separation facts `IncSep`** (the
field `fl1` fails at `j = 890`). -/
theorem isep_not_incSep_of_TgE (P : IncPlan p i r) (hTg : (P.Tg : ℤ) = 194 + 30 * P.km)
    (R0 : RegS) : ¬ IncSep P R0 :=
  fun h => isep_not_fl1 P hTg h.fl1

/-- **`IncSep` fails for the plan of every `inc` instruction of a well-formed program**, for
every register. -/
theorem isep_not_incSep (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) (R0 : RegS) :
    ¬ IncSep (incPlan p i r) R0 :=
  isep_not_incSep_of_TgE _ (incPlan_valid hp hins).TgE R0

/-- **The five flight fields of `IncSep` fail separately** for the plan of every `inc`
instruction of a well-formed program: `flyC`, `flyR`, `flyM`, `fl1`, `fl2`. -/
theorem isep_flights_false (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    (¬ ∀ j : ℕ, routeEndX (unitWL p i incDWL) (incPlan p i r).csC 2010 ≤ j →
        j < (incPlan p i r).T0c → ∀ h ∈ (incPlan p i r).LCraw,
        FarApart 2 ((route (unitWL p i incDWL) (incPlan p i r).csC).2.box j) h.box) ∧
      (¬ ∀ j : ℕ, routeEndX (unitWL p i incRWL) (incPlan p i r).csR 2010 ≤ j →
        j < (incPlan p i r).T0l → ∀ h ∈ (incPlan p i r).LIraw,
        FarApart 2 ((route (unitWL p i incRWL) (incPlan p i r).csR).2.box j) h.box) ∧
      (¬ ∀ j : ℕ, (incPlan p i r).eM ≤ j → j < (incPlan p i r).Tg → ∀ h ∈ (incPlan p i r).LIraw,
        FarApart 2 ((route (incPlan p i r).gM (incPlan p i r).csM).2.box j) h.box) ∧
      (¬ ∀ j : ℕ, 134 ≤ j → j < 891 → ∀ h ∈ (incPlan p i r).LIraw,
        FarApart 2 ((gateOutWL p r (incPlan p i r).km).box (((incPlan p i r).Tg : ℤ) + j))
          h.box) ∧
      (¬ ∀ j : ℕ, 921 ≤ j → j < 946 → ∀ h ∈ (incPlan p i r).LIraw,
        FarApart 2 ((rfJOutWL p r (incPlan p i r).km).box (((incPlan p i r).Tg : ℤ) + j))
          h.box) := by
  have hv := incPlan_valid hp hins
  exact ⟨isep_not_flyC _ hv (by have := isep_endC_lt hp hins; omega),
    isep_not_flyR _ hv (by have := isep_endR_lt hins; omega),
    isep_not_flyM _ hv (isep_eM_lt hins), isep_not_fl1 _ hv.TgE, isep_not_fl2 _ hv.TgE⟩

/-- **No well-formed program whose first instruction is an `inc` has `MachineSteps`**: its field
`incSep` would give `IncSep` at the start state. -/
theorem isep_not_machineSteps (hp : p.WellFormed) (h0 : p[0]? = some (.inc r)) :
    ¬ MachineSteps p :=
  fun M => isep_not_incSep hp h0 _ (M.incSep (startM 0) r (startM_minv hp 0) h0)

/-- **The hypothesis of the final corollary `exists_not_computablePred_everAlive` is false**:
the well-formed program `[inc 0, halt]` with a single `halt` has no `MachineSteps`. -/
theorem isep_not_all_machineSteps :
    ¬ ∀ p : Program, p.WellFormed → p.SingleHalt → MachineSteps p := by
  intro h
  have hp : Program.WellFormed [Instr.inc 0, .halt] := ⟨by simp, rfl⟩
  have hs : Program.SingleHalt [Instr.inc 0, .halt] := by
    intro j hj
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simp
  exact isep_not_machineSteps hp (r := 0) rfl (h _ hp hs)

end LP

end LeanTheory.Life
