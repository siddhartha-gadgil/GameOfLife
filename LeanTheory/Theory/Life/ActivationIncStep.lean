/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncModuleRun
public import LeanTheory.Theory.Life.Gen.BodyIncRunR

/-!
# The `inc` step of the simulator

Item (h) of the `inc` activation (research note `N-22`): **one `inc r` instruction of a
well-formed program is simulated by the machine**, from `encM s` to `encM s'`, with every
generation in `machRegion p`.

The activation is described by an **activation plan** (`IncPlan`): the corners of the three links
(continue to unit `i + 1`, INC link to the merge unit `N + r`, merge link to module `r`), the entry
copies, the arrival offsets and the arrival times. `IncPlan.Valid` collects the world-line and time
facts of the plan (lines of the routes, route law, arrival on the windows, order of the arrival
times, membership of the active pieces in the machine): all of them are facts about the layout
arithmetic of `incSpecs` / `mergeSpecs` (several are proved in `ActivationInc*`), not about
separation. `IncSep` collects the **separation facts** (the routes' `RouteSepX`, far-apart facts of
flights, entries, the module part and the lanes of the registers, concurrency of the two threads),
`IncRegion` the facts that the footprints lie in the region of the machine.

**Corner windows** (the separation facts are satisfiable): the routes are run with
`route_window_footX` / `link_entryX` (`ActivationIncCompose`, `ActivationIncThread`). At each
corner the reflector and the glider are run together from `meetT - 20` to `meetT + 40` inside the
extended relay box `relayBoxX` (`RouteSep`); the flight to a corner is required far from the
pieces only until `meetT - 20`, and the next leg starts at `meetT + 40`. So the route fields of
`IncSep` are `RouteSepX` (proved for the links of the layout in `RouteSep5`: `incLinks_sep`,
`mergeLink_sep`), the plan's times are `RouteTimedX`, the ends of the routes are `routeEndX`
(`IncPlan.eM` included), and the footprints `contFoot`, `earlyFoot`, `incFoot` use `linkFootX` and
`routeFootX` (the glider box until `meetT - 20`, then `relayBoxX` of the corner until
`meetT + 40`). The flight fields `flyC`, `flyR`, `flyM` start at `routeEndX`. (The former
conditions `RouteSep` / `RouteSepM` include the corner's own reflector in the flight clause up to
`meetT` and are unsatisfiable: `ActivationHalt.not_far_before_meet`.)

Composition (`inc_step_of_plan`):

1. **Body** (`[1080, 2010]`, world time of the template clock): `bodyIncRun_restR` placed at unit
   `i`, every other piece idle (`window_mem`), every register idle (`regsOn_reaction`).
2. **Two threads** from `2010` to `Tend` (the time the control reaches the entrance of unit
   `i + 1`), side by side (`Reaction.par`), inside the idle machine (`window_mem`):
   * the continue: route, flight, entry chain of unit `i + 1` (`link_entry`), flight to
     `ctrlAt p (i + 1)` (`orOut_flight_unit`);
   * the increment: INC link and entry chain of the merge unit (`link_entry`), merge link
     (`route_window_foot`, starting on the chain output by `mergeStart_eq`), flight to the INC gate,
     then `module_run_n` (gate, `RF_J`, increment for every register value, circuit idle), with
     the diagonal of register `r` beside it.
   The other registers idle beside the threads.
3. The end pattern is `encM s'` with `s'.pc = i + 1`, `s'.T = s.T + (Tend - 1080)`, register `r`
   holding one more (and still ready), the other registers `Tend - 1080` generations later.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The plan of an activation -/

/-- **The plan of the activation of `inc r` at instruction `i`**: corners, entry copies, offsets
and times of the three links. -/
structure IncPlan (p : Program) (i r : ℕ) where
  /-- Corners of the continue. -/
  csC : List Corner
  /-- Entry copy of the continue at unit `i + 1`. -/
  tc : ℕ
  /-- Window offset of the continue. -/
  δc : ℤ
  /-- Window periods of the continue. -/
  kc : ℤ
  /-- Arrival time of the continue at the side input. -/
  T0c : ℕ
  /-- Corners of the INC link. -/
  csR : List Corner
  /-- Entry copy of the INC link at the merge unit. -/
  tl : ℕ
  /-- Window offset of the INC link. -/
  δl : ℤ
  /-- Window periods of the INC link. -/
  kl : ℤ
  /-- Arrival time of the INC link at the side input. -/
  T0l : ℕ
  /-- Corners of the merge link. -/
  csM : List Corner
  /-- Window offset of the merge link at the INC gate. -/
  δm : ℤ
  /-- Window periods of the merge link. -/
  km : ℤ
  /-- Arrival time at the INC gate. -/
  Tg : ℕ

variable {p : Program} {i r : ℕ}

/-- The merge unit of register `r`. -/
abbrev mergeUnit (p : Program) (r : ℕ) : ℕ := p.length + r

/-- The time at which the merge unit's chain releases the INC control. -/
def IncPlan.T1 (P : IncPlan p i r) : ℕ := P.T0l + (134 + P.tl * 254)

/-- The world line of the merge link for this activation. -/
def IncPlan.gM (P : IncPlan p i r) : WL :=
  (unitWL p (mergeUnit p r) haltDWL).shift 0 0 ((P.T1 : ℤ) + 166 - 1080)

/-- The end of the merge route. -/
def IncPlan.eM (P : IncPlan p i r) : ℕ := routeEndX P.gM P.csM P.T1

/-- The time at which the continue's chain releases the control. -/
def IncPlan.Tc (P : IncPlan p i r) : ℕ := P.T0c + (134 + P.tc * 254)

/-- **The end of the activation**: the control at the entrance of unit `i + 1`. -/
def IncPlan.Tend (P : IncPlan p i r) : ℕ := P.Tc + 166

/-- The pieces active in the continue thread. -/
def IncPlan.LCraw (P : IncPlan p i r) : List Piece :=
  (route (unitWL p i incDWL) P.csC).1.map PSpec.piece ++ chainPieces p (i + 1) P.tc

/-- The pieces active in the increment thread. -/
def IncPlan.LIraw (P : IncPlan p i r) : List Piece :=
  (route (unitWL p i incRWL) P.csR).1.map PSpec.piece ++ chainPieces p (mergeUnit p r) P.tl ++
    (route P.gM P.csM).1.map PSpec.piece ++ [gateP p r, rfJP p r] ++ modGroup p r

/-- **The world-line and time facts of a plan** (layout arithmetic, no separation). -/
structure IncPlan.Valid (P : IncPlan p i r) : Prop where
  /-- The continue meets its corners on their input lines. -/
  linesC : RouteLines (unitWL p i incDWL) P.csC
  /-- The continue meets its corners in order from `2010`. -/
  timedC : RouteTimedX (unitWL p i incDWL) P.csC ((2010 : ℕ) : ℤ)
  /-- The continue arrives on the window of its entry copy. -/
  finC : (route (unitWL p i incDWL) P.csC).2 = (destWin p (i + 1) P.tc).shift 0 0 (P.δc + 30 * P.kc)
  /-- Offset of the continue. -/
  δcR : P.δc = 4 ∨ P.δc = 5
  /-- Arrival time of the continue. -/
  T0cE : (P.T0c : ℤ) = 180 + 30 * P.kc + 16 * (P.tc : ℤ) % 30
  /-- The continue leaves its last corner before its arrival. -/
  endC : routeEndX (unitWL p i incDWL) P.csC 2010 ≤ P.T0c
  /-- The INC link meets its corners on their input lines. -/
  linesR : RouteLines (unitWL p i incRWL) P.csR
  /-- The INC link meets its corners in order from `2010`. -/
  timedR : RouteTimedX (unitWL p i incRWL) P.csR ((2010 : ℕ) : ℤ)
  /-- The INC link arrives on the window of its entry copy at the merge unit. -/
  finR : (route (unitWL p i incRWL) P.csR).2 =
    (destWin p (mergeUnit p r) P.tl).shift 0 0 (P.δl + 30 * P.kl)
  /-- Offset of the INC link. -/
  δlR : P.δl = 4 ∨ P.δl = 5
  /-- Arrival time of the INC link. -/
  T0lE : (P.T0l : ℤ) = 180 + 30 * P.kl + 16 * (P.tl : ℤ) % 30
  /-- The INC link leaves its last corner before its arrival. -/
  endR : routeEndX (unitWL p i incRWL) P.csR 2010 ≤ P.T0l
  /-- The merge link meets its corners on their input lines. -/
  linesM : RouteLines P.gM P.csM
  /-- The merge link meets its corners in order from `T1`. -/
  timedM : RouteTimedX P.gM P.csM P.T1
  /-- The merge link arrives on the INC window of module `r`. -/
  finM : (route P.gM P.csM).2 = (modWL p r incWin).shift 0 0 (P.δm + 30 * P.km)
  /-- Offset of the merge link. -/
  δmR : P.δm = 4 ∨ P.δm = 5
  /-- Arrival time at the gate. -/
  TgE : (P.Tg : ℤ) = 194 + 30 * P.km
  /-- The merge link leaves its last corner before the gate. -/
  endM : P.eM ≤ P.Tg
  /-- **The continue waits for the increment** (the delay rule of `incSpecs`). -/
  late : P.Tg + 946 + 7050 ≤ P.Tend
  /-- The pieces of the continue thread are pieces of the machine. -/
  memC : ∀ x ∈ P.LCraw, x ∈ machPieces p
  /-- The pieces of the increment thread are pieces of the machine. -/
  memI : ∀ x ∈ P.LIraw, x ∈ machPieces p
  /-- The body of unit `i` is part of the machine. -/
  memB : ∀ x ∈ bodyGroup p i, x ∈ machPieces p

/-! ### Footprints of the activation -/

/-- The box of the body of unit `i` during the body run. -/
def bodyBox (p : Program) (i : ℕ) : Set Cell :=
  (fun c => (unitDX p i, unitDY p i) + c) '' Box 113 354 61 286

/-- **The footprint of the continue thread**, `j` generations after `2010`. -/
def IncPlan.contFoot (P : IncPlan p i r) (j : ℕ) : Set Cell :=
  if j ≤ P.Tc - 2010 then
    boxesOf (dd P.LCraw) ∪ linkFootX p (i + 1) P.tc (unitWL p i incDWL) P.csC 2010 P.T0c j
  else boxesOf (dd P.LCraw) ∪ (fun c => (unitDX p (i + 1), unitDY p (i + 1)) + c) ''
    chainOutWL.box (-166 + ((j - (P.Tc - 2010) : ℕ) : ℤ))

/-- The footprint of the increment thread before the gate (without the register). -/
def IncPlan.earlyFoot (P : IncPlan p i r) (j : ℕ) : Set Cell :=
  if j ≤ P.T1 - 2010 + (P.eM - P.T1) then
    (if j ≤ P.T1 - 2010 then
      boxesOf (dd P.LIraw) ∪
        linkFootX p (mergeUnit p r) P.tl (unitWL p i incRWL) P.csR 2010 P.T0l j
    else boxesOf (dd P.LIraw) ∪ routeFootX P.gM P.csM P.T1 (j - (P.T1 - 2010)))
  else boxesOf (dd P.LIraw) ∪
    (route P.gM P.csM).2.box ((P.eM : ℤ) + ((j - (P.T1 - 2010 + (P.eM - P.T1)) : ℕ) : ℤ))

/-- **The footprint of the increment thread**, `j` generations after `2010` (`R0`: the register
at `2010`). -/
def IncPlan.incFoot (P : IncPlan p i r) (R0 : RegS) (j : ℕ) : Set Cell :=
  if j ≤ P.Tg - 2010 then P.earlyFoot j ∪ regStrip p r R0 (j + R0.m)
  else modRunFoot p r (dd P.LIraw) P.km P.Tg (R0.later (P.Tg - 2010)) (j - (P.Tg - 2010))

/-- **The separation facts of the activation** (`R0`: register `r` at time `2010`). -/
structure IncSep (P : IncPlan p i r) (R0 : RegS) : Prop where
  /-- Separation of the continue's route with corner windows (whole machine, region as `Z`). -/
  sepC : RouteSepX (machPieces p) (machRegion p) (unitWL p i incDWL) P.csC ((2010 : ℕ) : ℤ)
  /-- Separation of the INC link's route with corner windows. -/
  sepR : RouteSepX (machPieces p) (machRegion p) (unitWL p i incRWL) P.csR ((2010 : ℕ) : ℤ)
  /-- Separation of the merge link's route with corner windows. -/
  sepM : RouteSepX (machPieces p) (machRegion p) P.gM P.csM (P.T1 : ℤ)
  /-- The continue's flight to the side input. -/
  flyC : ∀ j : ℕ, routeEndX (unitWL p i incDWL) P.csC 2010 ≤ j → j < P.T0c → ∀ h ∈ P.LCraw,
    FarApart 2 ((route (unitWL p i incDWL) P.csC).2.box j) h.box
  /-- The entry chain of unit `i + 1`. -/
  entC : ∀ h ∈ P.LCraw, h ∉ chainPieces p (i + 1) P.tc →
    FarApart 2 (entryFoot p (i + 1) P.tc) h.box
  /-- The flight from the chain of unit `i + 1` to its body input. -/
  outC : ∀ j : ℕ, j < 166 → ∀ h ∈ P.LCraw, FarApart 2
    ((fun c => (unitDX p (i + 1), unitDY p (i + 1)) + c) '' chainOutWL.box (-166 + (j : ℤ)))
    h.box
  /-- The INC link's flight to the side input. -/
  flyR : ∀ j : ℕ, routeEndX (unitWL p i incRWL) P.csR 2010 ≤ j → j < P.T0l → ∀ h ∈ P.LIraw,
    FarApart 2 ((route (unitWL p i incRWL) P.csR).2.box j) h.box
  /-- The entry chain of the merge unit. -/
  entR : ∀ h ∈ P.LIraw, h ∉ chainPieces p (mergeUnit p r) P.tl →
    FarApart 2 (entryFoot p (mergeUnit p r) P.tl) h.box
  /-- The merge link's flight to the gate. -/
  flyM : ∀ j : ℕ, P.eM ≤ j → j < P.Tg → ∀ h ∈ P.LIraw,
    FarApart 2 ((route P.gM P.csM).2.box j) h.box
  /-- The INC gate. -/
  gate : ∀ h ∈ P.LIraw, h ≠ gateP p r → FarApart 2 (gateBox p r) h.box
  /-- The flight from the gate to `RF_J`. -/
  fl1 : ∀ j : ℕ, 134 ≤ j → j < 891 → ∀ h ∈ P.LIraw,
    FarApart 2 ((gateOutWL p r P.km).box ((P.Tg : ℤ) + j)) h.box
  /-- `RF_J`. -/
  rf : ∀ h ∈ P.LIraw, h ≠ rfJP p r → FarApart 2 (relayBox (rfJCorner p r)) h.box
  /-- The flight from `RF_J` to the increment. -/
  fl2 : ∀ j : ℕ, 921 ≤ j → j < 946 → ∀ h ∈ P.LIraw,
    FarApart 2 ((rfJOutWL p r P.km).box ((P.Tg : ℤ) + j)) h.box
  /-- The module part before the increment and the lanes of the register. -/
  modLane : ∀ j < 946, FarApart 2 (boxesOf (dd P.LIraw) ∪ modFoot p r P.km P.Tg j)
    (modLanes p r)
  /-- The register circuit and the lanes of its register. -/
  grpLane : FarApart 2 (boxesOf (modGroup p r)) (modLanes p r)
  /-- **The increment, for every ready register, is far from the other pieces of the thread**
  (refined footprints `dz2e*OpG`, `dz2jAllG`). -/
  inc : ∀ R : RegS, R.Ready → ∀ j ≤ P.Tend - P.Tg - 946, ∀ h ∈ P.LIraw, h ∉ modGroup p r →
    FarApart 2 (conway.evolve j (incStart p r ∪ regAt p r R) : Set Cell) h.box
  /-- The increment thread before the gate and the lanes of the register. -/
  earlyLane : ∀ j < P.Tg - 2010, FarApart 2 (P.earlyFoot j) (modLanes p r)
  /-- **The two threads are far apart at every generation.** -/
  threads : ∀ j < P.Tend - 2010, FarApart 2 (P.contFoot j) (P.incFoot R0 j)
  /-- The threads are far from every idle piece of the machine. -/
  idle : ∀ j < P.Tend - 2010, ∀ g ∈ machPieces p, g ∉ P.LCraw ++ P.LIraw →
    FarApart 2 (P.contFoot j ∪ P.incFoot R0 j) g.box
  /-- The body is far from every other piece. -/
  body : ∀ g ∈ machPieces p, g ∉ bodyGroup p i → FarApart 2 (bodyBox p i) g.box
  /-- The lanes of distinct registers are far apart. -/
  lanes : ∀ r₁ < numRegs p, ∀ r₂ < numRegs p, r₁ ≠ r₂ → FarApart 2 (modLanes p r₁) (modLanes p r₂)
  /-- The machine and the body are far from the lanes of every register. -/
  laneBody : ∀ r' < numRegs p, FarApart 2 (boxesOf (machPieces p) ∪ bodyBox p i) (modLanes p r')
  /-- The machine and the threads are far from the lanes of every other register. -/
  laneAct : ∀ j < P.Tend - 2010, ∀ r' < numRegs p, r' ≠ r →
    FarApart 2 (boxesOf (machPieces p) ∪ (P.contFoot j ∪ P.incFoot R0 j)) (modLanes p r')

/-- **The region facts of the activation**: every footprint lies in the region of the machine. -/
structure IncRegion (P : IncPlan p i r) (R0 : RegS) : Prop where
  /-- The pieces of the machine. -/
  pieces : boxesOf (machPieces p) ⊆ machRegion p
  /-- The body. -/
  body : bodyBox p i ⊆ machRegion p
  /-- The two threads. -/
  threads : ∀ j ≤ P.Tend - 2010, P.contFoot j ∪ P.incFoot R0 j ⊆ machRegion p
  /-- The lanes of the registers. -/
  lanes : ∀ r' < numRegs p, modLanes p r' ⊆ machRegion p
/-! ### The two threads -/

/-- **The continue thread**: from the body output at `2010` to the control at the entrance of
unit `i + 1` at `Tend`, the pieces of the thread idle beside it. -/
theorem IncPlan.contThread (hp : p.WellFormed) (P : IncPlan p i r) (hv : P.Valid) {R0 : RegS}
    (hs : IncSep P R0) :
    Reaction (piecesAt (dd P.LCraw) 2010 ∪ (unitWL p i incDWL).cells 2010)
      (piecesAt (dd P.LCraw) P.Tend ∪ ctrlAt p (i + 1)) (P.Tend - 2010) P.contFoot := by
  have hL := dd_pairwise (machPieces_sep p hp) hv.memC
  have hsM := RouteSepX.toXM (L := dd P.LCraw) (fun h hh => hv.memC h (mem_dd.1 hh)) P.csC _ 2010
    hv.timedC (fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_map_of_mem hx))) hs.sepC
  obtain ⟨hle, h1⟩ := link_entryX p hL (i + 1) P.tc (g := unitWL p i incDWL)
    ⟨Or.inl rfl, Or.inl rfl⟩ hv.linesC hv.timedC hsM hv.δcR hv.finC hv.T0cE hv.endC
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx))
    (fun j h1 h2 h hh => hs.flyC j h1 h2 h (mem_dd.1 hh))
    (fun h hh hn => hs.entC h (mem_dd.1 hh) hn)
  have h2 := window hL P.Tc 166 (orOut_flight_unit p (i + 1))
    fun j hj h hh => hs.outC j hj h (mem_dd.1 hh)
  have h12 := h1.seq h2
  refine (h12.castN ?_).mono fun j _ => ?_
  · simp only [IncPlan.Tend, IncPlan.Tc]
    omega
  · exact le_rfl

/-- **The increment thread**: from the body output at `2010` (with the diagonal of register `r`)
to the register holding one more, the pieces of the thread idle beside it. -/
theorem IncPlan.incThread (hp : p.WellFormed) (P : IncPlan p i r) (hv : P.Valid) {R0 : RegS}
    (hR : R0.Ready) (hs : IncSep P R0) :
    ∃ R' : RegS, R'.val = R0.val + 1 ∧ R'.Ready ∧
      Reaction (piecesAt (dd P.LIraw) 2010 ∪ ((unitWL p i incRWL).cells 2010 ∪ regAt p r R0))
        (piecesAt (dd P.LIraw) P.Tend ∪ regAt p r R') (P.Tend - 2010) (P.incFoot R0) := by
  have hL := dd_pairwise (machPieces_sep p hp) hv.memI
  have memI : ∀ x ∈ P.LIraw, x ∈ dd P.LIraw := fun x hx => mem_dd.2 hx
  have hsR := RouteSepX.toXM (L := dd P.LIraw) (fun h hh => hv.memI h (mem_dd.1 hh)) P.csR _ 2010
    hv.timedR (fun x hx => memI _ (by simp [IncPlan.LIraw, List.mem_map_of_mem hx])) hs.sepR
  obtain ⟨hle, h1⟩ := link_entryX p hL (mergeUnit p r) P.tl (g := unitWL p i incRWL)
    ⟨Or.inl rfl, Or.inl rfl⟩ hv.linesR hv.timedR hsR hv.δlR hv.finR hv.T0lE hv.endR
    (fun x hx => memI _ (by simp [IncPlan.LIraw, hx]))
    (fun j h1 h2 h hh => hs.flyR j h1 h2 h (mem_dd.1 hh))
    (fun h hh hn => hs.entR h (mem_dd.1 hh) hn)
  rw [mergeStart_eq p (mergeUnit p r) ((P.T0l + (134 + P.tl * 254) : ℕ) : ℤ)] at h1
  have hsM := RouteSepX.toXM (L := dd P.LIraw) (fun h hh => hv.memI h (mem_dd.1 hh)) P.csM _
    P.T1 hv.timedM (fun x hx => memI _ (by simp [IncPlan.LIraw, List.mem_map_of_mem hx])) hs.sepM
  obtain ⟨hle2, h2⟩ := route_window_footX hL P.csM P.gM P.T1 ⟨Or.inl rfl, Or.inl rfl⟩ hv.linesM
    hv.timedM hsM
  have hd3 : (route P.gM P.csM).2.Dir := by
    rw [hv.finM]
    exact ⟨Or.inl rfl, Or.inr rfl⟩
  have hTg := hv.endM
  have h3 := window hL P.eM (P.Tg - P.eM) (WL.flight hd3 P.eM (P.Tg - P.eM))
    fun j hj h hh => by
      have := hs.flyM (P.eM + j) (by omega) (by omega) h (mem_dd.1 hh)
      push_cast at this
      exact this
  have e3 : (route P.gM P.csM).2.cells ((P.eM : ℤ) + ((P.Tg - P.eM : ℕ) : ℤ)) =
      ((modWL p r incWin).shift 0 0 (P.δm + 30 * P.km)).cells P.Tg := by
    rw [hv.finM]
    congr 1
    push_cast [Nat.cast_sub hTg]
    ring
  rw [e3, show P.eM + (P.Tg - P.eM) = P.Tg by omega] at h3
  have early := ((h1.seq h2).seq h3).castN (m := P.Tg - 2010) (by
    simp only [IncPlan.eM, IncPlan.T1] at hle2 hTg ⊢
    omega)
  have hearly := early.par (regAt_reaction p r hR.1 (P.Tg - 2010)) fun j hj =>
    (hs.earlyLane j hj).mono (fun x hx => by
      simp only [IncPlan.earlyFoot]
      exact hx) (regStrip_subset hR.1 p r j)
  have hlate := hv.late
  have hTg2 : 2010 ≤ P.Tg := by
    have a1 := hle2
    have a2 := hTg
    simp only [IncPlan.eM, IncPlan.T1] at a1 a2 ⊢
    omega
  obtain ⟨R', hval, hrdy, -, hmod⟩ := module_run_n p r hL (memI _ (by simp [IncPlan.LIraw]))
    (memI _ (by simp [IncPlan.LIraw])) (fun x hx => memI _ (by simp [IncPlan.LIraw, hx]))
    hv.δmR hv.TgE (hR.later (P.Tg - 2010))
    (fun h hh hn => hs.gate h (mem_dd.1 hh) hn)
    (fun j h1 h2 h hh => hs.fl1 j h1 h2 h (mem_dd.1 hh))
    (fun h hh hn => hs.rf h (mem_dd.1 hh) hn)
    (fun j h1 h2 h hh => hs.fl2 j h1 h2 h (mem_dd.1 hh)) hs.modLane hs.grpLane
    (P.Tend - P.Tg - 946) (by omega)
    (fun j hj h hh hn => hs.inc _ ((hR.later _).later 946) j hj h (mem_dd.1 hh) hn)
  rw [union_assoc, union_assoc] at hearly
  have w := hearly.seq hmod
  rw [show P.Tg + 946 + (P.Tend - P.Tg - 946) = P.Tend by omega] at w
  refine ⟨R', by simp [hval], hrdy, (w.castN (by omega)).mono fun j _ => ?_⟩
  simp only [IncPlan.incFoot]
  exact le_rfl
/-! ### The step -/

/-- Two delays of a register add up. -/
theorem RegS.later_later (R : RegS) (a b : ℕ) : (R.later a).later b = R.later (a + b) := by
  simp only [RegS.later, add_assoc]

/-- **The body of unit `i`** with the rest of the machine idle. -/
theorem body_window (hp : p.WellFormed) (hmem : ∀ x ∈ bodyGroup p i, x ∈ machPieces p)
    (hfar : ∀ g ∈ machPieces p, g ∉ bodyGroup p i → FarApart 2 (bodyBox p i) g.box) :
    Reaction (piecesAt (machPieces p) 1080 ∪ ctrlAt p i)
      (piecesAt (machPieces p) (1080 + 930) ∪
        ((unitWL p i incDWL).cells 2010 ∪ (unitWL p i incRWL).cells 2010)) 930
      (fun _ => boxesOf (machPieces p) ∪ bodyBox p i) := by
  have h := bodyIncRun_restR.translate (unitDX p i, unitDY p i)
  have hb : Reaction (piecesAt (bodyGroup p i) 1080 ∪ ctrlAt p i)
      (piecesAt (bodyGroup p i) (1080 + 930) ∪
        ((unitWL p i incDWL).cells 2010 ∪ (unitWL p i incRWL).cells 2010)) 930
      (fun _ => bodyBox p i) := by
    rw [bodyGroup_at p i (by norm_num), bodyGroup_at p i (by norm_num), ctrlAt,
      unitWL_cells p i (w := incDWL) ⟨Or.inl rfl, Or.inl rfl⟩,
      unitWL_cells p i (w := incRWL) ⟨Or.inl rfl, Or.inl rfl⟩, ← translate_union,
      ← translate_union, ← translate_union]
    have e1 : incDWL.cells 2010 = ofRows 351 284 [5, 6, 2] := rfl
    have e2 : incRWL.cells 2010 = ofRows 245 89 [5, 6, 2] := rfl
    rw [e1, e2, ← union_assoc]
    exact h
  exact window_mem (machPieces_sep p hp) hmem 1080 930 hb fun _ _ g hg hn => hfar g hg hn

/-- An `inc` instruction is not the last one of a well-formed program. -/
theorem succ_lt_of_inc (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) : i + 1 < p.length := by
  have hi : i < p.length := (List.getElem?_eq_some_iff.1 hins).1
  by_contra hc
  have he : i = p.length - 1 := by omega
  have hlast : p[p.length - 1]? = some .halt := by
    rw [← List.getLast?_eq_getElem?]
    exact hp.2
  rw [← he, hins] at hlast
  cases hlast

/-- The register of an `inc` instruction is a register of the program. -/
theorem lt_numRegs_of_inc (hins : p[i]? = some (.inc r)) : r < numRegs p := by
  have hm : Instr.inc r ∈ p := List.mem_of_getElem? hins
  have := le_foldr_max (List.mem_map_of_mem (f := regBound) hm)
  unfold numRegs
  simp only [regBound] at this
  omega

/-- The new registers after the activation: register `r` replaced, the others later. -/
def incRegs (s : MState) (r : ℕ) (R' : RegS) (n : ℕ) : ℕ → RegS :=
  Function.update (fun r' => (s.reg r').later n) r R'

/-- **The `inc` step, from an activation plan**: for a well-formed program, a state with the
instruction `inc r` at the program counter (register `r` ready), and a valid activation plan with
its separation and region facts, the machine evolves `encM s` into `encM s'` for the next state
`s'` of the counter machine, inside the region of the machine, in `τ > 0` generations, with every
other register `τ` generations later. -/
theorem inc_step_of_plan (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hins : p[s.pc]? = some (.inc r)) (hready : (s.reg r).Ready) (P : IncPlan p s.pc r)
    (hv : P.Valid) (hsep : IncSep P ((s.reg r).later 930))
    (hreg : IncRegion P ((s.reg r).later 930)) :
    ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ (∀ r', r' ≠ r → s'.reg r' = (s.reg r').later τ) ∧
      p.step s.cfg = some s'.cfg ∧ InvM p s' ∧ (s'.reg r).Ready ∧
      conway.evolve τ (encM p s) = encM p s' ∧
      ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p := by
  have hr := lt_numRegs_of_inc hins
  have hLM := machPieces_sep p hp
  have hinvR : ∀ r' ∈ List.range (numRegs p), (s.reg r').Inv :=
    fun r' h => hinv.2.2.1 r' (List.mem_range.1 h)
  have hlate := hv.late
  have hTend : P.Tend % 30 = 0 := by
    have := hv.T0cE
    simp only [IncPlan.Tend, IncPlan.Tc]
    omega
  -- the body, with every register idle
  have S1 := (body_window hp hv.memB hsep.body).par
    (regsOn_reaction p s.reg 930 (List.range (numRegs p)) List.nodup_range hinvR
      fun j _ r₁ h₁ r₂ h₂ hne => (hsep.lanes r₁ (List.mem_range.1 h₁) r₂ (List.mem_range.1 h₂)
        hne).mono (regStrip_subset (hinvR r₁ h₁) p r₁ j) (regStrip_subset (hinvR r₂ h₂) p r₂ j))
    fun j _ a ha b hb => by
      obtain ⟨r', hr', hb⟩ := mem_stripsOn.1 hb
      exact hsep.laneBody r' (List.mem_range.1 hr') a ha b
        (regStrip_subset (hinvR r' hr') p r' j hb)
  -- the two threads inside the idle machine, with the other registers idle
  have hC := P.contThread hp hv hsep
  obtain ⟨R', hval, hrdy, hI⟩ := P.incThread hp hv (hready.later 930) hsep
  have hCI := hC.par hI hsep.threads
  set A := dd P.LCraw ++ dd P.LIraw with hAdef
  have hA : ∀ x ∈ A, x ∈ machPieces p := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hv.memC x (mem_dd.1 h)
    · exact hv.memI x (mem_dd.1 h)
  have hCI' : Reaction (piecesAt A 2010 ∪ ((unitWL p s.pc incDWL).cells 2010 ∪
        ((unitWL p s.pc incRWL).cells 2010 ∪ regAt p r ((s.reg r).later 930))))
      (piecesAt A (2010 + (P.Tend - 2010)) ∪ (ctrlAt p (s.pc + 1) ∪ regAt p r R'))
      (P.Tend - 2010) (fun j => P.contFoot j ∪ P.incFoot ((s.reg r).later 930) j) := by
    refine hCI.congrPQ ?_ ?_
    · rw [hAdef, piecesAt_append]
      ac_rfl
    · rw [hAdef, piecesAt_append, show 2010 + (P.Tend - 2010) = P.Tend by omega]
      ac_rfl
  have W2 := window_mem hLM hA 2010 (P.Tend - 2010) hCI' fun j hj g hg hn =>
    hsep.idle j hj g hg fun h => hn (by
      rcases List.mem_append.1 h with h | h
      · exact List.mem_append_left _ (mem_dd.2 h)
      · exact List.mem_append_right _ (mem_dd.2 h))
  set others := (List.range (numRegs p)).filter (fun r' => r' ≠ r) with hoth
  have hothR : ∀ r' ∈ others, r' < numRegs p ∧ r' ≠ r := fun r' h => by
    simp only [hoth, List.mem_filter, List.mem_range, ne_eq, decide_eq_true_eq] at h
    exact h
  have hinvO : ∀ r' ∈ others, ((s.reg r').later 930).Inv :=
    fun r' h => (hinv.2.2.1 r' (hothR r' h).1).later 930
  have S2 := W2.par (regsOn_reaction p (fun r' => (s.reg r').later 930) (P.Tend - 2010) others
      (List.nodup_range.filter _) hinvO
      fun j _ r₁ h₁ r₂ h₂ hne => (hsep.lanes r₁ (hothR r₁ h₁).1 r₂ (hothR r₂ h₂).1 hne).mono
        (regStrip_subset (hinvO r₁ h₁) p r₁ j) (regStrip_subset (hinvO r₂ h₂) p r₂ j))
    fun j hj a ha b hb => by
      obtain ⟨r', hr', hb⟩ := mem_stripsOn.1 hb
      exact hsep.laneAct j hj r' (hothR r' hr').1 (hothR r' hr').2 a ha b
        (regStrip_subset (hinvO r' hr') p r' j hb)
  have e12 : piecesAt (machPieces p) (1080 + 930) ∪
        ((unitWL p s.pc incDWL).cells 2010 ∪ (unitWL p s.pc incRWL).cells 2010) ∪
        regsOn p (fun r' => (s.reg r').later 930) (List.range (numRegs p)) =
      piecesAt (machPieces p) 2010 ∪ ((unitWL p s.pc incDWL).cells 2010 ∪
        ((unitWL p s.pc incRWL).cells 2010 ∪ regAt p r ((s.reg r).later 930))) ∪
        regsOn p (fun r' => (s.reg r').later 930) others := by
    rw [regsOn_split _ _ hr, show 1080 + 930 = 2010 by norm_num]
    ac_rfl
  have S := S1.seq_eq e12 S2
  set τ := 930 + (P.Tend - 2010) with hτ
  set s' : MState := ⟨s.pc + 1, s.T + τ, incRegs s r R' τ⟩ with hs'
  have estart : encM p s = piecesAt (machPieces p) 1080 ∪ ctrlAt p s.pc ∪
      regsOn p s.reg (List.range (numRegs p)) := by
    rw [encM, machAt, regsAt_eq, piecesAt_mod _ (show s.T % 30 = 1080 % 30 by
      have := hinv.2.1; omega)]
  have eend : encM p s' = piecesAt (machPieces p) (2010 + (P.Tend - 2010)) ∪
      (ctrlAt p (s.pc + 1) ∪ regAt p r R') ∪
        regsOn p (fun r' => ((s.reg r').later 930).later (P.Tend - 2010)) others := by
    rw [encM, machAt, regsAt_eq, regsOn_split _ _ hr]
    have h1 : piecesAt (machPieces p) s'.T = piecesAt (machPieces p) (2010 + (P.Tend - 2010)) :=
      piecesAt_mod _ (by have := hinv.2.1; change (s.T + τ) % 30 = _; omega)
    have h2 : regsOn p s'.reg others =
        regsOn p (fun r' => ((s.reg r').later 930).later (P.Tend - 2010)) others :=
      regsOn_congr fun r' h => by
        change incRegs s r R' τ r' = _
        rw [incRegs, Function.update_of_ne (hothR r' h).2, RegS.later_later, hτ]
    have h3 : s'.reg r = R' := by
      change incRegs s r R' τ r = R'
      rw [incRegs, Function.update_self]
    rw [h1, h2, h3]
    simp only [union_assoc]
    rfl
  refine ⟨τ, s', by omega, fun r' hne => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change incRegs s r R' τ r' = _
    rw [incRegs, Function.update_of_ne hne]
  · -- the counter machine
    rw [Program.step]
    change (p[s.pc]?.bind fun ins => ins.exec s.cfg) = _
    rw [hins, Option.bind_some]
    change some (⟨s.pc + 1, Function.update (fun r' => (s.reg r').val) r ((s.reg r).val + 1)⟩ :
      Cfg) = some ⟨s.pc + 1, fun r' => (incRegs s r R' τ r').val⟩
    refine congrArg some (Cfg.ext rfl (funext fun r' => ?_))
    by_cases he : r' = r
    · subst he
      dsimp only
      rw [Function.update_self, incRegs, Function.update_self, hval, RegS.val_later]
    · dsimp only
      rw [Function.update_of_ne he, incRegs, Function.update_of_ne he, RegS.val_later]
  · -- the invariant
    refine ⟨succ_lt_of_inc hp hins, ?_, fun r' hr' => ?_, fun r' hr' => ?_⟩
    · have := hinv.2.1
      change (s.T + τ) % 30 = 0
      omega
    · change (incRegs s r R' τ r').Inv
      by_cases he : r' = r
      · subst he
        rw [incRegs, Function.update_self]
        exact hrdy.1
      · rw [incRegs, Function.update_of_ne he]
        exact (hinv.2.2.1 r' hr').later τ
    · have he : r' ≠ r := by omega
      change (incRegs s r R' τ r').val = 0
      rw [incRegs, Function.update_of_ne he, RegS.val_later]
      exact hinv.2.2.2 r' hr'
  · change (incRegs s r R' τ r).Ready
    rw [incRegs, Function.update_self]
    exact hrdy
  · rw [estart, eend]
    exact S.evolve_eq
  · intro j hj
    rw [estart]
    refine (S.subset j hj).trans ?_
    have hstrips : ∀ (reg : ℕ → RegS) (l : List ℕ) (k : ℕ), (∀ r' ∈ l, r' < numRegs p) →
        (∀ r' ∈ l, (reg r').Inv) → stripsOn p reg l k ⊆ machRegion p := by
      intro reg l k hl hi x hx
      obtain ⟨r', hr', hx⟩ := mem_stripsOn.1 hx
      exact hreg.lanes r' (hl r' hr') (regStrip_subset (hi r' hr') p r' k hx)
    split_ifs with hj1
    · refine Set.union_subset (Set.union_subset hreg.pieces hreg.body) ?_
      exact hstrips _ _ _ (fun r' h => List.mem_range.1 h) hinvR
    · refine Set.union_subset (Set.union_subset hreg.pieces (hreg.threads _ (by omega))) ?_
      exact hstrips _ _ _ (fun r' h => (hothR r' h).1) hinvO

end LP

end LeanTheory.Life
