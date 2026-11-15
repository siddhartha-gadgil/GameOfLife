/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecStepTimed
public import LeanTheory.Theory.Life.ActivationDecStepRun
public import LeanTheory.Theory.Life.Gen.DecWindow
public import LeanTheory.Theory.Life.OrChainTight
public import LeanTheory.Theory.Life.ActivationIncModuleRun


/-!
# The processes of a `decJz` activation

Research note `N-22`. The processes of the activation of `decJz r z` at instruction `i` (caller
`j`, shift `sh`), each a reaction of its own pieces and gliders with a footprint given at the
**absolute** time `t` (template clock), so that concurrent processes can be run side by side:

* generic tools: `Reaction.splitAt`, `idleR`, `windowW`, `flyFoot` and `routeFly` (a route with
  corner windows followed by a flight);
* **joint approach windows** (the approach of a glider to a piece it is about to enter cannot be
  separated from the piece): `sideWindow` (an OR gate and its side glider, the last `20`
  generations, `Gen/DecWindow`), `dec_side_arrivalE`; `stationNZ_tokW`, `stationZ_tokW` (a token
  and its station, the last `90` generations: the token flies through the station's box);
* the control `C` (`decCProc`): route, flight, the joint approach of DEC copy `m`, the DEC chain,
  the flight of `C'` to the register run (`decFootC`);
* the tokens (`decTokNProc`, `decTokZProc`, footprints `tokFootN`, `tokFootZ`) and the unpaired
  tokens with their absorption (`decUnpNProc`, `decUnpZProc`, exact evolution as footprint);
* the answers from the cut past the stations `0 … j - 1` (`decAnsNProc`, `decAnsZProc`);
* the end (`decFinNProc`, `decFinZProc`): the capture at station `j` (exact evolution), the answer
  link with corner windows and the side window of the entry copy (`link_entryW`), the flight to
  the body input of the next unit;
* the register runs placed in time (`decRunNProc`, `decRunZProc`): the run up to the cut, then the
  rest of the run and the circuit and the register idling (`restFootN`, `restFootZ`).

Every separation hypothesis stops before the interaction it hands over to (`20` generations
before a corner or a side input, `90` before a capture).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Generic tools -/

/-- **A reaction split at generation `k`**: the first `k` generations, then the rest from the
(abstract) intermediate configuration. -/
theorem Reaction.splitAt {P Q : Finset Cell} {n : ℕ} {F : ℕ → Set Cell} (h : Reaction P Q n F)
    (k : ℕ) (hk : k ≤ n) :
    Reaction P (conway.evolve k P) k F ∧
      Reaction (conway.evolve k P) Q (n - k) (fun i => F (i + k)) := by
  refine ⟨⟨rfl, fun i hi => h.subset i (by omega)⟩, ⟨?_, fun i hi => ?_⟩⟩
  · rw [← Rule.evolve_add, Nat.sub_add_cancel hk, h.evolve_eq]
  · rw [← Rule.evolve_add]
    exact h.subset _ (by omega)

/-- **Idle pieces**: a separated list of pieces at phase `T` is, `n` generations later, at phase
`T + n`, inside its boxes. -/
theorem idleR {L : List Piece} (hL : L.Pairwise Piece.Sep) (T n : ℕ) :
    Reaction (piecesAt L T) (piecesAt L (T + n)) n (fun _ => boxesOf L) := by
  have h := (bundleAt L hL T n).reaction
  rw [bundleAt_P, bundleAt_Q] at h
  exact h.mono fun i _ => (bundleAt_F _ _ T n i).le

/-- **A window for any list of pieces whose deduplication is separated**: the pieces of `W` idle
beside a reaction far from each of them. -/
theorem windowW {W : List Piece} (hW : (dd W).Pairwise Piece.Sep) (T n : ℕ) {X Y : Finset Cell}
    {F : ℕ → Set Cell} (h : Reaction X Y n F)
    (hfar : ∀ i < n, ∀ g ∈ W, FarApart 2 (F i) g.box) :
    Reaction (piecesAt W T ∪ X) (piecesAt W (T + n) ∪ Y) n (fun i => boxesOf W ∪ F i) := by
  have w := window hW T n h fun i hi g hg => hfar i hi g (mem_dd.1 hg)
  rw [piecesAt_dd, piecesAt_dd] at w
  exact w.mono fun i _ => by rw [boxesOf_dd]

/-- The footprint of a route with corner windows followed by the flight on its final world line,
at the absolute time `t` (route started at `T`). -/
def flyFoot (g : WL) (cs : List Corner) (T t : ℕ) : Set Cell :=
  if t ≤ routeEndX g cs T then routeFootX g cs T (t - T) else (route g cs).2.box t

/-- **A route followed by a flight**: the glider of `g` at `T` follows the corners `cs` (corner
windows) and flies on its final world line until `T' ≥ routeEndX`, beside the idle pieces of
`L`. -/
theorem routeFly {L : List Piece} (hL : L.Pairwise Piece.Sep) (cs : List Corner) (g : WL)
    (T : ℕ) (hd : g.Dir) (hl : RouteLines g cs) (ht : RouteTimedX g cs T)
    (hs : RouteSepXM L g cs T) (hfd : (route g cs).2.Dir) {T' : ℕ}
    (hT' : routeEndX g cs T ≤ T')
    (hfly : ∀ t : ℕ, routeEndX g cs T ≤ t → t < T' → ∀ h ∈ L,
      FarApart 2 ((route g cs).2.box t) h.box) :
    T ≤ T' ∧ Reaction (piecesAt L T ∪ g.cells T) (piecesAt L T' ∪ (route g cs).2.cells T')
      (T' - T) (fun i => boxesOf L ∪ flyFoot g cs T (T + i)) := by
  obtain ⟨hTe, h1⟩ := route_window_footX hL cs g T hd hl ht hs
  set e := routeEndX g cs T with he
  have h2 := window hL e (T' - e) (WL.flight hfd e (T' - e)) fun j hj h hh => by
    have := hfly (e + j) (by omega) (by omega) h hh
    rw [show ((e : ℤ) + (j : ℤ)) = ((e + j : ℕ) : ℤ) by push_cast; ring]
    exact this
  rw [show e + (T' - e) = T' by omega,
    show (e : ℤ) + ((T' - e : ℕ) : ℤ) = (T' : ℤ) by push_cast [Nat.cast_sub hT']; ring] at h2
  have h12 := h1.seq h2
  refine ⟨by omega, ?_⟩
  rw [show T' - T = e - T + (T' - e) by omega]
  refine h12.mono fun j _ => ?_
  simp only [flyFoot, ← he]
  by_cases ha : j ≤ e - T
  · simp only [ha, show T + j ≤ e by omega, ↓reduceIte, show T + j - T = j by omega]
    exact le_rfl
  · simp only [ha, show ¬ T + j ≤ e by omega, ↓reduceIte]
    rw [show (e : ℤ) + ((j - (e - T) : ℕ) : ℤ) = ((T + j : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hTe, Nat.cast_sub (show e - T ≤ j by omega)]; ring]


/-! ### Joint approach windows -/

/-- The box of the joint approach of a side glider and its OR gate (gate frame). -/
def sideWBox : Set Cell := Box 0 90 0 40

/-- **The joint approach of an OR gate placed at `(dx, dy)`**: the gate (at phase `10` at `T`) and
the side glider `E` become, `20` generations later, the gate at phase `0` and the side input `S`,
inside `sideWBox` placed at the gate. -/
theorem sideWindow (dx dy : ℤ) (ph T : ℕ) (hph : (ph + T) % 30 = 10) {E S : Finset Cell}
    (hw : Reaction (phase orGate 10 ∪ E) (orGate ∪ S) 20 (fun _ => Box 0 90 0 40)) :
    Reaction (piecesAt [(⟨.orGate, dx, dy, ph⟩ : PSpec).piece] T ∪ translate (dx, dy) E)
      (piecesAt [(⟨.orGate, dx, dy, ph⟩ : PSpec).piece] (T + 20) ∪ translate (dx, dy) S) 20
      (fun _ => (fun c => (dx, dy) + c) '' sideWBox) := by
  rw [piecesAt_single, piecesAt_single, orGate_placed_at, orGate_placed_at,
    phase_congr orGate (a := ph + T) (b := 10) (by omega),
    phase_congr orGate (a := ph + (T + 20)) (b := 0) (by omega),
    show phase orGate 0 = orGate by rw [phase, Nat.zero_mod, Rule.evolve_zero],
    ← translate_union, ← translate_union]
  exact hw.translate (dx, dy)

/-- The side glider `20` generations before the side input of the DEC chain. -/
def decSideInE (δ : ℤ) : Finset Cell := if δ = 4 then decSideE6 else decSideE10

/-- The joint approach of the DEC side inputs. -/
theorem decSideInE_window {δ : ℤ} (hδ : δ = 4 ∨ δ = 8) :
    Reaction (phase orGate 10 ∪ decSideInE δ) (orGate ∪ decSideIn δ) 20
      (fun _ => Box 0 90 0 40) := by
  rcases hδ with rfl | rfl
  · exact decSideW6
  · exact decSideW10

/-- **The glider `20` generations before the side input of DEC copy `m`**. -/
theorem dec_side_arrivalE (p : Program) (r : ℕ) (t δ k : ℤ) (hδ : δ = 4 ∨ δ = 8) :
    ((decWin p r t).shift 0 0 (δ + 30 * k)).cells
        (180 + 30 * k + (15 + 16 * (2 * D p - 1 - t)) % 30 - 20) =
      translate (modDX p r - 1700 - 35 * (2 * D p - 1 - t),
        modDY p r - 1727 - 64 * (2 * D p - 1 - t)) (decSideInE δ) := by
  have hd : sideBase.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have hE : decSideInE δ = sideBase.cells (160 - δ) := by
    rcases hδ with rfl | rfl <;> rfl
  rw [decWin_eq, hE]
  rw [WL.shift_cells (show WL.Dir ((sideBase.shift (-1700 - 35 * (2 * D p - 1 - t))
      (-1727 - 64 * (2 * D p - 1 - t)) ((15 + 16 * (2 * D p - 1 - t)) % 30)).shift (modDX p r)
      (modDY p r) 0) from hd),
    WL.shift_cells (show WL.Dir (sideBase.shift (-1700 - 35 * (2 * D p - 1 - t))
      (-1727 - 64 * (2 * D p - 1 - t)) ((15 + 16 * (2 * D p - 1 - t)) % 30)) from hd),
    WL.shift_cells hd, translate_translate, translate_translate]
  congr 1
  · ext <;> simp <;> ring
  · congr 1
    ring

/-! ### The control `C`: route, DEC chain, flight to the register run -/

/-- The reflectors of a route as pieces. -/
def reflP (g : WL) (cs : List Corner) : List Piece := (route g cs).1.map PSpec.piece

/-- The copies `0 … m` of the DEC chain of module `r` used by the activation. -/
def decChainP (p : Program) (i r : ℕ) : List Piece :=
  (decChainSpecs (decM p i r + 1) (modDX p r) (modDY p r)).map PSpec.piece

/-- **The pieces of the control thread**: the reflectors of `C` and the DEC copies `0 … m`. -/
noncomputable def decLC (p : Program) (i r : ℕ) : List Piece :=
  dd (reflP (unitWL p i decRWL) (decCornC p i r) ++ decChainP p i r)

/-- The time at which the DEC chain releases `C'`. -/
def decTB (p : Program) (i r : ℕ) : ℕ := decTA p i r + (134 + decM p i r * 254)

/-- The footprint of the DEC chain during the relay. -/
def decChainFoot (p : Program) (i r : ℕ) : Set Cell :=
  (fun c => (modDX p r - 1700 - 35 * ((decM p i r : ℕ) : ℤ),
    modDY p r - 1727 - 64 * ((decM p i r : ℕ) : ℤ)) + c) ''
    chainFoot (Box 0 90 (-6) 60) chainV (decM p i r + 1)

/-- The box of `C'` flying to the register run, at the absolute time `t`. -/
def decCpFoot (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  (fun c => (modDX p r, modDY p r) + c) '' cp0WL.box (-2071 + ((t - decTB p i r : ℕ) : ℤ))

/-- The DEC copy `m` receiving `C`, as a piece. -/
def decCopyM (p : Program) (i r : ℕ) : Piece :=
  (⟨.orGate, modDX p r - 1700 - 35 * ((decM p i r : ℕ) : ℤ),
    modDY p r - 1727 - 64 * ((decM p i r : ℕ) : ℤ), (15 + 14 * decM p i r) % 30⟩ : PSpec).piece

/-- The box of the joint approach of `C` and DEC copy `m`. -/
def decSideBoxC (p : Program) (i r : ℕ) : Set Cell :=
  (fun c => (modDX p r - 1700 - 35 * ((decM p i r : ℕ) : ℤ),
    modDY p r - 1727 - 64 * ((decM p i r : ℕ) : ℤ)) + c) '' sideWBox

/-- **The moving footprint of the control** at the absolute time `t ∈ [4260, decTS]`: the route
and the flight, the joint approach of DEC copy `m`, the DEC chain, the flight of `C'`. -/
def decFootC (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decTA p i r - 20 then flyFoot (unitWL p i decRWL) (decCornC p i r) 4260 t
  else if t ≤ decTA p i r then decSideBoxC p i r
  else if t ≤ decTB p i r then decChainFoot p i r else decCpFoot p i r t

/-- The DEC copies of the activation are copies of the DEC chain of the module. -/
theorem decChainP_sub {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) {x : Piece}
    (hx : x ∈ decChainP p i r) :
    x ∈ (decChainSpecs (2 * numCallers p) (modDX p r) (modDY p r)).map PSpec.piece := by
  have hj := callerIdx_lt_D p hi
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  exact List.mem_map_of_mem (decChainSpecs_prefix (by unfold decM; omega) _ _ hs)

/-- DEC copy `m` is one of the DEC copies of the activation. -/
theorem decCopyM_mem (p : Program) (i r : ℕ) : decCopyM p i r ∈ decChainP p i r :=
  List.mem_map.2 ⟨_, List.mem_map.2 ⟨decM p i r, List.mem_range.2 (by omega), rfl⟩, rfl⟩

/-- **The control thread**: from the output `R` of the body at `4260`, `C` follows its route and
flies to `20` generations before the side input of DEC copy `m`, approaches it jointly with the
gate, is relayed by the DEC copies `m … 0`, and `C'` flies to the input of the register run,
reached at `decTS`; the pieces of the thread idle beside it. -/
theorem decCProc {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hmem : ∀ x ∈ decLC p i r, x ∈ machPieces p)
    (hsep : RouteSepX (machPieces p) (machRegion p) (unitWL p i decRWL) (decCornC p i r)
      ((4260 : ℕ) : ℤ))
    (hfly : ∀ t : ℕ, routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ≤ t →
      t < decTA p i r - 20 → ∀ h ∈ decLC p i r, FarApart 2 ((decGC p i r).box t) h.box)
    (hside : ∀ h ∈ decLC p i r, h ≠ decCopyM p i r → FarApart 2 (decSideBoxC p i r) h.box)
    (hch : ∀ h ∈ decLC p i r, h ∉ decChainP p i r → FarApart 2 (decChainFoot p i r) h.box)
    (hcp : ∀ t : ℕ, decTB p i r ≤ t → t < decTS p i r → ∀ h ∈ decLC p i r,
      FarApart 2 (decCpFoot p i r t) h.box) :
    Reaction (piecesAt (decLC p i r) 4260 ∪ (unitWL p i decRWL).cells 4260)
      (piecesAt (decLC p i r) (decTS p i r) ∪
        translate (modDX p r, modDY p r) (ofRows (-1186) (-1227) [2, 4, 7]))
      (decTS p i r - 4260) (fun k => boxesOf (decLC p i r) ∪ decFootC p i r (4260 + k)) := by
  have hL : (decLC p i r).Pairwise Piece.Sep :=
    dd_pairwise (machPieces_sep p hp) fun x hx => hmem x (mem_dd.2 hx)
  obtain ⟨hA1, hA2, hA3⟩ := decTA_facts p hi
  obtain ⟨hS1, -, -⟩ := decTS_facts p hi
  have hsM := RouteSepX.toXM (L := decLC p i r) hmem (decCornC p i r) (unitWL p i decRWL) 4260
    (decC_timedX p hi) (fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_map_of_mem hx)))
    hsep
  have hdC : (decGC p i r).Dir := by rw [decC_window]; exact ⟨Or.inl rfl, Or.inr rfl⟩
  obtain ⟨-, h1⟩ := routeFly hL (decCornC p i r) (unitWL p i decRWL) 4260
    ⟨Or.inl rfl, Or.inl rfl⟩ (decC_lines p i r).1 (decC_timedX p hi) hsM hdC
    (T' := decTA p i r - 20) (by omega) hfly
  change Reaction _ (_ ∪ (decGC p i r).cells _) _ _ at h1
  rw [decC_window] at h1
  have hδ : 4 + 2 * sigma (qOf p (callerIdx p r i)) = 4 ∨
      4 + 2 * sigma (qOf p (callerIdx p r i)) = 8 := by
    rcases sigma_cases (qOf p (callerIdx p r i)) with h | h <;> rw [h] <;> norm_num
  have hm := decM_cast p hi
  -- the joint approach of copy `m`
  have hw := sideWindow (modDX p r - 1700 - 35 * ((decM p i r : ℕ) : ℤ))
    (modDY p r - 1727 - 64 * ((decM p i r : ℕ) : ℤ)) ((15 + 14 * decM p i r) % 30)
    (decTA p i r - 20) (by omega) (decSideInE_window hδ)
  have eE := dec_side_arrivalE p r (2 * (callerIdx p r i : ℤ)) _ (decSlot p i r) hδ
  have eS := dec_side_arrival p r (2 * (callerIdx p r i : ℤ)) _ (decSlot p i r) hδ
  rw [← hm] at eE eS
  rw [← eS, ← hA3] at hw
  rw [← hA3, show ((decTA p i r : ℤ) - 20) = ((decTA p i r - 20 : ℕ) : ℤ) by omega] at eE
  rw [← eE] at hw
  have w1 := window_mem hL (A := [decCopyM p i r])
    (fun x hx => by
      rcases List.mem_singleton.1 hx with rfl
      exact mem_dd.2 (List.mem_append_right _ (decCopyM_mem p i r)))
    (decTA p i r - 20) 20 hw fun j _ h hh hn =>
      hside h hh fun he => hn (he ▸ List.mem_singleton_self _)
  rw [show decTA p i r - 20 + 20 = decTA p i r by omega] at w1
  have hch' := decChain_reaction p r (decM p i r) (2 * (callerIdx p r i : ℤ))
    hm hδ (decSlot p i r) (decTA p i r) hA3
  have w2 := window_mem hL (A := decChainP p i r)
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx))
    (decTA p i r) (134 + decM p i r * 254) hch' fun j _ h hh hn => hch h hh hn
  have w3 := window hL (decTA p i r + (134 + decM p i r * 254)) 1771 (cprime_flight p r)
    fun j hj h hh => by
      have := hcp (decTB p i r + j) (by unfold decTB; omega) (by unfold decTB decTS; omega) h hh
      simp only [decCpFoot, show decTB p i r + j - decTB p i r = j by omega] at this
      exact this
  have w := ((h1.seq w1).seq w2).seq w3
  rw [show decTA p i r + (134 + decM p i r * 254) + 1771 = decTS p i r from rfl] at w
  refine (w.castN (by unfold decTS; omega)).mono fun k _ => ?_
  simp only [decFootC, decSideBoxC, decChainFoot, decCpFoot]
  split_ifs <;> first
    | (exfalso; unfold decTB at *; omega)
    | with_reducible exact Set.Subset.rfl
    | (rw [show 4260 + k - decTB p i r =
         k - (decTA p i r - 20 - 4260 + 20 + (134 + decM p i r * 254)) by unfold decTB at *; omega])


/-! ### The tokens approach their stations together with the stations -/

/-- **The NZ token approaches station `j` with the station** (`90` generations before the capture
position, at `T = sh + 10260 + 288 j`): the token flies through the station's box untouched. -/
theorem stationNZ_tokW (p : Program) (r j : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 10260 + 288 * j) :
    conway.evolve 90 (piecesAt (stNZOne p r j) T ∪ ((modWL p r (tokNZWL j)).shift 0 0 sh).cells T) =
      piecesAt (stNZOne p r j) (T + 90) ∪ ((modWL p r (tokNZWL j)).shift 0 0 sh).cells
        ((T + 90 : ℕ) : ℤ) := by
  have hK : (tokNZWL 0).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have e1 : ((T : ℕ) : ℤ) = 10260 + 288 * (j : ℤ) + sh := by omega
  have e2 : ((T + 90 : ℕ) : ℤ) = 10350 + 288 * (j : ℤ) + sh := by push_cast; omega
  have hE : stTokENZ = (tokNZWL 0).cells 10260 := rfl
  rw [stNZOne, stNZ_one_at, stNZ_one_at, e1, e2,
    modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩, modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩,
    tokNZWL_step, cells_step hK, cells_step hK, translate_translate, translate_translate,
    ← hE, ← stUnpairedTokenNZIn_eq,
    show ((modDX p r, modDY p r) + (72 * (j : ℤ), 72 * (j : ℤ)) : Cell) =
      (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ)) from rfl,
    ← translate_union, ← translate_union,
    phase_congr stNZG (a := 12 * j % 30 + T) (b := 0) (by omega),
    phase_congr stNZG (a := 12 * j % 30 + (T + 90)) (b := 0) (by omega),
    show phase stNZG 0 = stNZG by rw [phase, Nat.zero_mod, Rule.evolve_zero],
    Rule.evolve_translate, ← stCaptureNZG_eq, stTokWNZ.evolve_eq]

/-- **The Z token approaches station `j` with the station** (`90` generations before the capture
position, at `T = sh + 12300 + 288 j`). -/
theorem stationZ_tokW (p : Program) (r j : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 12300 + 288 * j) :
    conway.evolve 90 (piecesAt (stZOne p r j) T ∪ ((modWL p r (tokZWL j)).shift 0 0 sh).cells T) =
      piecesAt (stZOne p r j) (T + 90) ∪ ((modWL p r (tokZWL j)).shift 0 0 sh).cells
        ((T + 90 : ℕ) : ℤ) := by
  have hK : (tokZWL 0).Dir := ⟨Or.inr rfl, Or.inr rfl⟩
  have e1 : ((T : ℕ) : ℤ) = 12300 + 288 * (j : ℤ) + sh := by omega
  have e2 : ((T + 90 : ℕ) : ℤ) = 12390 + 288 * (j : ℤ) + sh := by push_cast; omega
  have hE : stTokEZ = (tokZWL 0).cells 12300 := rfl
  rw [stZOne, stZ_one_at, stZ_one_at, e1, e2,
    modShift_cells p r ⟨Or.inr rfl, Or.inr rfl⟩, modShift_cells p r ⟨Or.inr rfl, Or.inr rfl⟩,
    tokZWL_step, cells_step hK, cells_step hK, translate_translate, translate_translate,
    ← hE, ← stUnpairedTokenZIn_eq,
    show ((modDX p r, modDY p r) + (72 * (j : ℤ), -72 * (j : ℤ)) : Cell) =
      (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ)) from Prod.ext rfl (by simp; ring),
    ← translate_union, ← translate_union,
    phase_congr stZG (a := 12 * j % 30 + T) (b := 0) (by omega),
    phase_congr stZG (a := 12 * j % 30 + (T + 90)) (b := 0) (by omega),
    show phase stZG 0 = stZG by rw [phase, Nat.zero_mod, Rule.evolve_zero],
    Rule.evolve_translate, ← stCaptureZG_eq, stTokWZ.evolve_eq]

/-! ### The tokens -/

/-- The capture time of the NZ token at station `j` (`sh + 10350 + 288 j`). -/
def decCapN (p : Program) (i r : ℕ) : ℕ := decTS p i r + 10650 + 288 * callerIdx p r i

/-- The capture time of the Z token at station `j` (`sh + 12390 + 288 j`). -/
def decCapZ (p : Program) (i r : ℕ) : ℕ := decTS p i r + 12690 + 288 * callerIdx p r i

/-- The token `KNZ` on the token line of station `j`. -/
def decTokN (p : Program) (i r : ℕ) : WL :=
  (modWL p r (tokNZWL (callerIdx p r i))).shift 0 0 (decShift p i r)

/-- The token `KZ` on the token line of station `j`. -/
def decTokZ (p : Program) (i r : ℕ) : WL :=
  (modWL p r (tokZWL (callerIdx p r i))).shift 0 0 (decShift p i r)

/-- The reflectors of `KNZ`. -/
noncomputable def decLN (p : Program) (i r : ℕ) : List Piece :=
  dd (reflP (unitWL p i decLWL) (decCornN p i r))

/-- The reflectors of `KZ`. -/
noncomputable def decLZ (p : Program) (i r : ℕ) : List Piece :=
  dd (reflP (unitWL p i decDWL) (decCornZ p i r))

/-- The capture times as integers. -/
theorem decCap_cast (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    (decCapN p i r : ℤ) = decShift p i r + 10350 + 288 * (callerIdx p r i : ℤ) ∧
      (decCapZ p i r : ℤ) = decShift p i r + 12390 + 288 * (callerIdx p r i : ℤ) := by
  obtain ⟨h, -, -⟩ := decTS_facts p hi
  simp only [decCapN, decCapZ]
  push_cast
  omega

/-- The token `KNZ` and station `j` of the line NZ, `90` generations before the capture. -/
def decTokWStartN (p : Program) (i r : ℕ) : Finset Cell :=
  piecesAt (stNZOne p r (callerIdx p r i)) (decCapN p i r - 90) ∪
    (decTokN p i r).cells ((decCapN p i r - 90 : ℕ) : ℤ)

/-- The token `KZ` and station `j` of the line Z, `90` generations before the capture. -/
def decTokWStartZ (p : Program) (i r : ℕ) : Finset Cell :=
  piecesAt (stZOne p r (callerIdx p r i)) (decCapZ p i r - 90) ∪
    (decTokZ p i r).cells ((decCapZ p i r - 90 : ℕ) : ℤ)

/-- **The moving footprint of `KNZ`** at the absolute time `t`: the route and the flight, then
the token and station `j` together (exact evolution) for the last `90` generations. -/
def tokFootN (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decCapN p i r - 90 then flyFoot (unitWL p i decLWL) (decCornN p i r) 4260 t
  else (conway.evolve (t - (decCapN p i r - 90)) (decTokWStartN p i r) : Set Cell)

/-- **The moving footprint of `KZ`** at the absolute time `t`. -/
def tokFootZ (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decCapZ p i r - 90 then flyFoot (unitWL p i decDWL) (decCornZ p i r) 4260 t
  else (conway.evolve (t - (decCapZ p i r - 90)) (decTokWStartZ p i r) : Set Cell)

/-- **The token `KNZ`** follows its route, flies to `90` generations before the capture position
at station `j`, and approaches it together with the station; the pieces of a list `L` containing
its reflectors and station `j` idle beside it. -/
theorem decTokNProc {p : Program} {i r z : ℕ}
    (hi : p[i]? = some (.decJz r z)) {L : List Piece} (hmem : ∀ x ∈ L, x ∈ machPieces p)
    (hnd : L.Pairwise Piece.Sep)
    (hrf : ∀ x ∈ reflP (unitWL p i decLWL) (decCornN p i r), x ∈ L)
    (hst : ∀ x ∈ stNZOne p r (callerIdx p r i), x ∈ L)
    (hsep : RouteSepX (machPieces p) (machRegion p) (unitWL p i decLWL) (decCornN p i r)
      ((4260 : ℕ) : ℤ))
    (hfly : ∀ t : ℕ, routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ≤ t →
      t < decCapN p i r - 90 → ∀ h ∈ L, FarApart 2 ((decTokN p i r).box t) h.box)
    (hwin : ∀ k < 90, ∀ h ∈ L, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decTokWStartN p i r) : Set Cell) h.box) :
    Reaction (piecesAt L 4260 ∪ (unitWL p i decLWL).cells 4260)
      (piecesAt L (decCapN p i r) ∪ (decTokN p i r).cells (decCapN p i r))
      (decCapN p i r - 4260) (fun k => boxesOf L ∪ tokFootN p i r (4260 + k)) := by
  have hsM := RouteSepX.toXM (L := L) hmem _ _ 4260
    (decKNZ_timedX p hi) (fun x hx => hrf _ (List.mem_map_of_mem hx)) hsep
  have he := decKNZ_end p hi
  have hc := (decCap_cast p hi).1
  have ht : (route (unitWL p i decLWL) (decCornN p i r)).2 = decTokN p i r := decKNZ_target p i r
  obtain ⟨-, h⟩ := routeFly hnd _ _ 4260 ⟨Or.inl rfl, Or.inl rfl⟩ (decKNZ_lines p i r).1
    (decKNZ_timedX p hi) hsM (by rw [ht]; exact ⟨Or.inl rfl, Or.inr rfl⟩)
    (T' := decCapN p i r - 90) (by omega)
    (fun t h1 h2 h hh => by rw [ht]; exact hfly t h1 h2 h hh)
  rw [ht] at h
  have hw0 := stationNZ_tokW p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
    (decCapN p i r - 90) (by omega)
  have hw := window_mem hnd hst (decCapN p i r - 90) 90 (Reaction.exact hw0)
    fun k hk h hh hn => hwin k hk h hh hn
  rw [show decCapN p i r - 90 + 90 = decCapN p i r by omega] at hw
  have w := h.seq hw
  have h4 : 4260 + 90 ≤ decCapN p i r := by
    have := (decTS_facts p hi).2.2; unfold decCapN decTS at *; omega
  refine (w.castN (by omega)).mono fun k _ => ?_
  simp only [tokFootN]
  split_ifs <;> first
    | (exfalso; omega)
    | with_reducible exact Set.Subset.rfl
    | (rw [show 4260 + k - (decCapN p i r - 90) = k - (decCapN p i r - 90 - 4260) by omega]
       exact Set.Subset.rfl)

/-- **The token `KZ`** follows its route, flies to `90` generations before the capture position at
station `j`, and approaches it together with the station. -/
theorem decTokZProc {p : Program} {i r z : ℕ}
    (hi : p[i]? = some (.decJz r z)) {L : List Piece} (hmem : ∀ x ∈ L, x ∈ machPieces p)
    (hnd : L.Pairwise Piece.Sep)
    (hrf : ∀ x ∈ reflP (unitWL p i decDWL) (decCornZ p i r), x ∈ L)
    (hst : ∀ x ∈ stZOne p r (callerIdx p r i), x ∈ L)
    (hsep : RouteSepX (machPieces p) (machRegion p) (unitWL p i decDWL) (decCornZ p i r)
      ((4260 : ℕ) : ℤ))
    (hfly : ∀ t : ℕ, routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 ≤ t →
      t < decCapZ p i r - 90 → ∀ h ∈ L, FarApart 2 ((decTokZ p i r).box t) h.box)
    (hwin : ∀ k < 90, ∀ h ∈ L, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decTokWStartZ p i r) : Set Cell) h.box) :
    Reaction (piecesAt L 4260 ∪ (unitWL p i decDWL).cells 4260)
      (piecesAt L (decCapZ p i r) ∪ (decTokZ p i r).cells (decCapZ p i r))
      (decCapZ p i r - 4260) (fun k => boxesOf L ∪ tokFootZ p i r (4260 + k)) := by
  have hsM := RouteSepX.toXM (L := L) hmem _ _ 4260
    (decKZ_timedX p hi) (fun x hx => hrf _ (List.mem_map_of_mem hx)) hsep
  have he := decKZ_end p hi
  have hc := (decCap_cast p hi).2
  have ht : (route (unitWL p i decDWL) (decCornZ p i r)).2 = decTokZ p i r := decKZ_target p i r
  obtain ⟨-, h⟩ := routeFly hnd _ _ 4260 ⟨Or.inl rfl, Or.inl rfl⟩ (decKZ_lines p i r)
    (decKZ_timedX p hi) hsM (by rw [ht]; exact ⟨Or.inr rfl, Or.inr rfl⟩)
    (T' := decCapZ p i r - 90) (by omega)
    (fun t h1 h2 h hh => by rw [ht]; exact hfly t h1 h2 h hh)
  rw [ht] at h
  have hw0 := stationZ_tokW p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
    (decCapZ p i r - 90) (by omega)
  have hw := window_mem hnd hst (decCapZ p i r - 90) 90 (Reaction.exact hw0)
    fun k hk h hh hn => hwin k hk h hh hn
  rw [show decCapZ p i r - 90 + 90 = decCapZ p i r by omega] at hw
  have w := h.seq hw
  have h4 : 4260 + 90 ≤ decCapZ p i r := by
    have := (decTS_facts p hi).2.2; unfold decCapZ decTS at *; omega
  refine (w.castN (by omega)).mono fun k _ => ?_
  simp only [tokFootZ]
  split_ifs <;> first
    | (exfalso; omega)
    | with_reducible exact Set.Subset.rfl
    | (rw [show 4260 + k - (decCapZ p i r - 90) = k - (decCapZ p i r - 90 - 4260) by omega]
       exact Set.Subset.rfl)

/-! ### The unpaired tokens -/

/-- The pieces of the `KZ` thread of an NZ activation: the reflectors of `KZ` and station `j` of
the line Z. -/
noncomputable def decLZu (p : Program) (i r : ℕ) : List Piece :=
  dd (reflP (unitWL p i decDWL) (decCornZ p i r) ++ stZOne p r (callerIdx p r i))

/-- The pieces of the `KNZ` thread of a Z activation: the reflectors of `KNZ` and station `j` of
the line NZ. -/
noncomputable def decLNu (p : Program) (i r : ℕ) : List Piece :=
  dd (reflP (unitWL p i decLWL) (decCornN p i r) ++ stNZOne p r (callerIdx p r i))

/-- The unpaired `KZ` at station `j` (NZ activation), at the capture time. -/
def decUnpStartZ (p : Program) (i r : ℕ) : Finset Cell :=
  piecesAt (stZOne p r (callerIdx p r i)) (decCapZ p i r) ∪ (decTokZ p i r).cells (decCapZ p i r)

/-- The unpaired `KNZ` at station `j` (Z activation), at the capture time. -/
def decUnpStartN (p : Program) (i r : ℕ) : Finset Cell :=
  piecesAt (stNZOne p r (callerIdx p r i)) (decCapN p i r) ∪ (decTokN p i r).cells (decCapN p i r)

/-- **The moving footprint of the unpaired `KZ`** (NZ activation), at the absolute time `t`: the
token, then its absorption by station `j` (exact evolution). -/
def unpFootZ (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decCapZ p i r then tokFootZ p i r t
  else if t ≤ decCapZ p i r + 272 then
    (conway.evolve (t - decCapZ p i r) (decUnpStartZ p i r) : Set Cell)
  else ∅

/-- **The moving footprint of the unpaired `KNZ`** (Z activation), at the absolute time `t`. -/
def unpFootN (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decCapN p i r then tokFootN p i r t
  else if t ≤ decCapN p i r + 292 then
    (conway.evolve (t - decCapN p i r) (decUnpStartN p i r) : Set Cell)
  else ∅

/-- **The thread of the unpaired `KZ`** (NZ activation): the token reaches station `j` of the
line Z, which absorbs it; then its pieces idle until `E`. -/
theorem decUnpZProc {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hmem : ∀ x ∈ decLZu p i r, x ∈ machPieces p)
    (hsep : RouteSepX (machPieces p) (machRegion p) (unitWL p i decDWL) (decCornZ p i r)
      ((4260 : ℕ) : ℤ))
    (hfly : ∀ t : ℕ, routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 ≤ t →
      t < decCapZ p i r - 90 → ∀ h ∈ decLZu p i r, FarApart 2 ((decTokZ p i r).box t) h.box)
    (hwin : ∀ k < 90, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decTokWStartZ p i r) : Set Cell) h.box)
    (hunp : ∀ k < 272, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decUnpStartZ p i r) : Set Cell) h.box)
    (E : ℕ) (hE : decCapZ p i r + 272 ≤ E) :
    Reaction (piecesAt (decLZu p i r) 4260 ∪ (unitWL p i decDWL).cells 4260)
      (piecesAt (decLZu p i r) E) (E - 4260)
      (fun k => boxesOf (decLZu p i r) ∪ unpFootZ p i r (4260 + k)) := by
  have hL : (decLZu p i r).Pairwise Piece.Sep :=
    dd_pairwise (machPieces_sep p hp) fun x hx => hmem x (mem_dd.2 hx)
  have h1 := decTokZProc hi hmem hL (fun x hx => mem_dd.2 (List.mem_append_left _ hx))
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx)) hsep hfly hwin
  have hc := decCap_cast p hi
  have e := (stationZ_unpaired p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
    (decCapZ p i r) hc.2).evolve_eq
  rw [← union_empty (piecesAt (stZOne p r (callerIdx p r i)) (decCapZ p i r + 272))] at e
  have w2 := window_mem hL (A := stZOne p r (callerIdx p r i))
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx)) (decCapZ p i r) 272 (Reaction.exact e)
    fun j hj h hh hn => hunp j hj h hh hn
  have w3 := idleR hL (decCapZ p i r + 272) (E - (decCapZ p i r + 272))
  rw [show decCapZ p i r + 272 + (E - (decCapZ p i r + 272)) = E by omega] at w3
  have hcz : 4260 ≤ decCapZ p i r := by
    have := (decTS_facts p hi).2.2; unfold decCapZ decTS at *; omega
  have w := (h1.seq w2).seq_eq (union_empty _) w3
  refine (w.castN (by omega)).mono fun k _ => ?_
  simp only [unpFootZ]
  split_ifs <;> first
    | (exfalso; omega)
    | with_reducible exact Set.Subset.rfl
    | with_reducible exact Set.subset_union_left
    | (rw [show 4260 + k - decCapZ p i r = k - (decCapZ p i r - 4260) by omega]
       exact Set.Subset.rfl)

/-- **The thread of the unpaired `KNZ`** (Z activation): the token reaches station `j` of the
line NZ, which absorbs it; then its pieces idle until `E`. -/
theorem decUnpNProc {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hmem : ∀ x ∈ decLNu p i r, x ∈ machPieces p)
    (hsep : RouteSepX (machPieces p) (machRegion p) (unitWL p i decLWL) (decCornN p i r)
      ((4260 : ℕ) : ℤ))
    (hfly : ∀ t : ℕ, routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ≤ t →
      t < decCapN p i r - 90 → ∀ h ∈ decLNu p i r, FarApart 2 ((decTokN p i r).box t) h.box)
    (hwin : ∀ k < 90, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decTokWStartN p i r) : Set Cell) h.box)
    (hunp : ∀ k < 292, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decUnpStartN p i r) : Set Cell) h.box)
    (E : ℕ) (hE : decCapN p i r + 292 ≤ E) :
    Reaction (piecesAt (decLNu p i r) 4260 ∪ (unitWL p i decLWL).cells 4260)
      (piecesAt (decLNu p i r) E) (E - 4260)
      (fun k => boxesOf (decLNu p i r) ∪ unpFootN p i r (4260 + k)) := by
  have hL : (decLNu p i r).Pairwise Piece.Sep :=
    dd_pairwise (machPieces_sep p hp) fun x hx => hmem x (mem_dd.2 hx)
  have h1 := decTokNProc hi hmem hL (fun x hx => mem_dd.2 (List.mem_append_left _ hx))
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx)) hsep hfly hwin
  have hc := decCap_cast p hi
  have e := (stationNZ_unpaired p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
    (decCapN p i r) hc.1).evolve_eq
  rw [← union_empty (piecesAt (stNZOne p r (callerIdx p r i)) (decCapN p i r + 292))] at e
  have w2 := window_mem hL (A := stNZOne p r (callerIdx p r i))
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx)) (decCapN p i r) 292 (Reaction.exact e)
    fun j hj h hh hn => hunp j hj h hh hn
  have w3 := idleR hL (decCapN p i r + 292) (E - (decCapN p i r + 292))
  rw [show decCapN p i r + 292 + (E - (decCapN p i r + 292)) = E by omega] at w3
  have hcz : 4260 ≤ decCapN p i r := by
    have := (decTS_facts p hi).2.2; unfold decCapN decTS at *; omega
  have w := (h1.seq w2).seq_eq (union_empty _) w3
  refine (w.castN (by omega)).mono fun k _ => ?_
  simp only [unpFootN]
  split_ifs <;> first
    | (exfalso; omega)
    | with_reducible exact Set.Subset.rfl
    | with_reducible exact Set.subset_union_left
    | (rw [show 4260 + k - decCapN p i r = k - (decCapN p i r - 4260) by omega]
       exact Set.Subset.rfl)

/-! ### The answers on their lines: the cut, the stations before `j` -/

/-- The cut of the NZ runs (`sh + 9203`). -/
def decCutN (p : Program) (i r : ℕ) : ℕ := decTS p i r + 9503

/-- The cut of the Z run (`sh + 11695`). -/
def decCutZ (p : Program) (i r : ℕ) : ℕ := decTS p i r + 11995

/-- The NZ answer at the capture position of station `0` (`sh + 10350`). -/
def decSt0N (p : Program) (i r : ℕ) : ℕ := decTS p i r + 10650

/-- The Z answer at the capture position of station `0` (`sh + 12390`). -/
def decSt0Z (p : Program) (i r : ℕ) : ℕ := decTS p i r + 12690

/-- The NZ stations `0 … j - 1` of module `r`. -/
noncomputable def decLSN (p : Program) (i r : ℕ) : List Piece :=
  dd ((stationSpecs (callerIdx p r i) (modDX p r) (modDY p r)).map PSpec.piece)

/-- The Z stations `0 … j - 1` of module `r`. -/
noncomputable def decLSZ (p : Program) (i r : ℕ) : List Piece :=
  dd ((stationZSpecs (callerIdx p r i) (modDX p r) (modDY p r)).map PSpec.piece)

/-- The world line of the NZ answer of the run (delayed by the shift). -/
def decAnsWLN (p : Program) (i r : ℕ) : WL := (modWL p r ansNZWL).shift 0 0 (decShift p i r)

/-- The world line of the Z answer of the run (delayed by the shift). -/
def decAnsWLZ (p : Program) (i r : ℕ) : WL := (modWL p r ansZWL).shift 0 0 (decShift p i r)

/-- **The moving footprint of the NZ answer** from the cut to the capture at station `j`. -/
def decAnsFootN (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decSt0N p i r then (decAnsWLN p i r).box t
  else modImg p r (chainFoot stNZRY (72, 72) (callerIdx p r i))

/-- **The moving footprint of the Z answer** from the cut to the capture at station `j`. -/
def decAnsFootZ (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decSt0Z p i r then (decAnsWLZ p i r).box t
  else modImg p r (chainFoot stZR (72, -72) (callerIdx p r i))

/-- **The NZ answer from the cut to station `j`**: a free flight to the capture position of
station `0`, then the stations `0 … j - 1` let it pass. -/
theorem decAnsNProc {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hmem : ∀ x ∈ decLSN p i r, x ∈ machPieces p)
    (hfly : ∀ t : ℕ, decCutN p i r ≤ t → t < decSt0N p i r → ∀ h ∈ decLSN p i r,
      FarApart 2 ((decAnsWLN p i r).box t) h.box) :
    Reaction (piecesAt (decLSN p i r) (decCutN p i r) ∪ (decAnsWLN p i r).cells (decCutN p i r))
      (piecesAt (decLSN p i r) (decCapN p i r) ∪ (decAnsWLN p i r).cells (decCapN p i r))
      (decCapN p i r - decCutN p i r)
      (fun k => boxesOf (decLSN p i r) ∪ decAnsFootN p i r (decCutN p i r + k)) := by
  have hL : (decLSN p i r).Pairwise Piece.Sep :=
    dd_pairwise (machPieces_sep p hp) fun x hx => hmem x (mem_dd.2 hx)
  obtain ⟨hS, -, -⟩ := decTS_facts p hi
  have hd : (decAnsWLN p i r).Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have w1 := window hL (decCutN p i r) 1147 (WL.flight hd (decCutN p i r) 1147)
    fun j hj h hh => by
      have := hfly (decCutN p i r + j) (by omega) (by unfold decCutN decSt0N; omega) h hh
      push_cast at this
      exact this
  rw [show decCutN p i r + 1147 = decSt0N p i r by unfold decCutN decSt0N; omega,
    show ((decCutN p i r : ℕ) : ℤ) + ((1147 : ℕ) : ℤ) = ((decSt0N p i r : ℕ) : ℤ) by
      unfold decCutN decSt0N; push_cast; ring] at w1
  rcases hj : callerIdx p r i with _ | L
  · have e : decCapN p i r = decSt0N p i r := by unfold decCapN decSt0N; omega
    rw [e]
    refine (w1.castN (by unfold decCutN decSt0N; omega)).mono fun k hk => ?_
    simp only [decAnsFootN, show decCutN p i r + k ≤ decSt0N p i r by
      unfold decCutN decSt0N at *; omega, ↓reduceIte]
    exact le_rfl
  · have e : decSt0N p i r + (L + 1) * 288 = decCapN p i r := by
      unfold decCapN decSt0N; rw [hj]; ring
    have hpass : Reaction
        (piecesAt (decLSN p i r) (decSt0N p i r) ∪ (decAnsWLN p i r).cells (decSt0N p i r))
        (piecesAt (decLSN p i r) (decCapN p i r) ∪ (decAnsWLN p i r).cells (decCapN p i r))
        ((L + 1) * 288) (fun _ => modImg p r (chainFoot stNZRY (72, 72) (L + 1))) := by
      have h := answerNZ_pass p r L (decShift p i r) (decShift_mod p i r) (decSt0N p i r)
        (by unfold decSt0N; push_cast; omega)
      have e2 : ((decCapN p i r : ℕ) : ℤ) = (decSt0N p i r : ℤ) + ((L : ℤ) + 1) * 288 := by
        rw [← e]; push_cast; ring
      unfold decLSN decAnsWLN modImg
      rw [piecesAt_dd, piecesAt_dd, hj, e2, ← e]
      exact h
    have w := w1.seq hpass
    refine (w.castN (by unfold decCapN decCutN decSt0N at *; rw [hj] at *; omega)).mono
      fun k hk => ?_
    simp only [decAnsFootN]
    split_ifs with h1 h2
    · rw [Nat.cast_add]
    · exfalso; unfold decCutN decSt0N at *; omega
    · exfalso; unfold decCutN decSt0N at *; omega
    · rw [← hj]
      exact Set.subset_union_right

/-- **The Z answer from the cut to station `j`**: a free flight to the capture position of
station `0`, then the stations `0 … j - 1` let it pass. -/
theorem decAnsZProc {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hmem : ∀ x ∈ decLSZ p i r, x ∈ machPieces p)
    (hfly : ∀ t : ℕ, decCutZ p i r ≤ t → t < decSt0Z p i r → ∀ h ∈ decLSZ p i r,
      FarApart 2 ((decAnsWLZ p i r).box t) h.box) :
    Reaction (piecesAt (decLSZ p i r) (decCutZ p i r) ∪ (decAnsWLZ p i r).cells (decCutZ p i r))
      (piecesAt (decLSZ p i r) (decCapZ p i r) ∪ (decAnsWLZ p i r).cells (decCapZ p i r))
      (decCapZ p i r - decCutZ p i r)
      (fun k => boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r (decCutZ p i r + k)) := by
  have hL : (decLSZ p i r).Pairwise Piece.Sep :=
    dd_pairwise (machPieces_sep p hp) fun x hx => hmem x (mem_dd.2 hx)
  obtain ⟨hS, -, -⟩ := decTS_facts p hi
  have hd : (decAnsWLZ p i r).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have w1 := window hL (decCutZ p i r) 695 (WL.flight hd (decCutZ p i r) 695)
    fun j hj h hh => by
      have := hfly (decCutZ p i r + j) (by omega) (by unfold decCutZ decSt0Z; omega) h hh
      push_cast at this
      exact this
  rw [show decCutZ p i r + 695 = decSt0Z p i r by unfold decCutZ decSt0Z; omega,
    show ((decCutZ p i r : ℕ) : ℤ) + ((695 : ℕ) : ℤ) = ((decSt0Z p i r : ℕ) : ℤ) by
      unfold decCutZ decSt0Z; push_cast; ring] at w1
  rcases hj : callerIdx p r i with _ | L
  · have e : decCapZ p i r = decSt0Z p i r := by unfold decCapZ decSt0Z; omega
    rw [e]
    refine (w1.castN (by unfold decCutZ decSt0Z; omega)).mono fun k hk => ?_
    simp only [decAnsFootZ, show decCutZ p i r + k ≤ decSt0Z p i r by
      unfold decCutZ decSt0Z at *; omega, ↓reduceIte]
    exact le_rfl
  · have e : decSt0Z p i r + (L + 1) * 288 = decCapZ p i r := by
      unfold decCapZ decSt0Z; rw [hj]; ring
    have hpass : Reaction
        (piecesAt (decLSZ p i r) (decSt0Z p i r) ∪ (decAnsWLZ p i r).cells (decSt0Z p i r))
        (piecesAt (decLSZ p i r) (decCapZ p i r) ∪ (decAnsWLZ p i r).cells (decCapZ p i r))
        ((L + 1) * 288) (fun _ => modImg p r (chainFoot stZR (72, -72) (L + 1))) := by
      have h := answerZ_pass p r L (decShift p i r) (decShift_mod p i r) (decSt0Z p i r)
        (by unfold decSt0Z; push_cast; omega)
      have e2 : ((decCapZ p i r : ℕ) : ℤ) = (decSt0Z p i r : ℤ) + ((L : ℤ) + 1) * 288 := by
        rw [← e]; push_cast; ring
      unfold decLSZ decAnsWLZ modImg
      rw [piecesAt_dd, piecesAt_dd, hj, e2, ← e]
      exact h
    have w := w1.seq hpass
    refine (w.castN (by unfold decCapZ decCutZ decSt0Z at *; rw [hj] at *; omega)).mono
      fun k hk => ?_
    simp only [decAnsFootZ]
    split_ifs with h1 h2
    · rw [Nat.cast_add]
    · exfalso; unfold decCutZ decSt0Z at *; omega
    · exfalso; unfold decCutZ decSt0Z at *; omega
    · rw [← hj]
      exact Set.subset_union_right

/-! ### Capture, dispatch, the answer link and the entry at the next unit -/

/-- The corners of the NZ answer. -/
def decCsN (p : Program) (i r : ℕ) : List Corner := decMkN p i r (decEA p i r)

/-- The corners of the Z answer. -/
def decCsZ (p : Program) (i r z : ℕ) : List Corner := decMkZ p i r z (decEB p i r z)

/-- **The pieces of the end of an NZ activation**: station `j` of the line NZ, the reflectors of
the NZ answer and the entry copies `0 … t` of unit `i + 1`. -/
noncomputable def decLFN (p : Program) (i r : ℕ) : List Piece :=
  dd (stNZOne p r (callerIdx p r i) ++ reflP (decGN p i r) (decCsN p i r) ++
    chainPieces p (i + 1) (decTNn p i r))

/-- **The pieces of the end of a Z activation**: station `j` of the line Z, the reflectors of
the Z answer and the entry copies `0 … t` of unit `z`. -/
noncomputable def decLFZ (p : Program) (i r z : ℕ) : List Piece :=
  dd (stZOne p r (callerIdx p r i) ++ reflP (decGZ p i r) (decCsZ p i r z) ++
    chainPieces p z (decTZn p i r z))

/-- The flight from copy `0` of the entry chain of unit `a` to its body input (absolute time `t`,
leaving copy `0` at `T`). -/
def outFoot (p : Program) (a T t : ℕ) : Set Cell :=
  (fun c => (unitDX p a, unitDY p a) + c) '' chainOutWL.box (-166 + ((t - T : ℕ) : ℤ))

/-- The capture at station `j` of the line NZ: the station, the answer and the token. -/
def decCapStartN (p : Program) (i r : ℕ) : Finset Cell :=
  piecesAt (stNZOne p r (callerIdx p r i)) (decCapN p i r) ∪
    ((decAnsWLN p i r).cells (decCapN p i r) ∪ (decTokN p i r).cells (decCapN p i r))

/-- The capture at station `j` of the line Z: the station, the answer and the token. -/
def decCapStartZ (p : Program) (i r : ℕ) : Finset Cell :=
  piecesAt (stZOne p r (callerIdx p r i)) (decCapZ p i r) ∪
    ((decAnsWLZ p i r).cells (decCapZ p i r) ∪ (decTokZ p i r).cells (decCapZ p i r))

/-- **The moving footprint of the end of an NZ activation**: the capture, the answer link (route,
flight, entry chain of unit `i + 1`) and the flight to the body input. -/
def finFootN (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decDispN p i r then (conway.evolve (t - decCapN p i r) (decCapStartN p i r) : Set Cell)
  else if t ≤ decT0N p i r + (134 + decTNn p i r * 254) then
    linkFootW p (i + 1) (decTNn p i r) (decGN p i r) (decCsN p i r)
      (decDispN p i r)
      (decT0N p i r) (t - decDispN p i r)
  else outFoot p (i + 1) (decT0N p i r + (134 + decTNn p i r * 254)) t

/-- **The moving footprint of the end of a Z activation**. -/
def finFootZ (p : Program) (i r z : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decDispZ p i r then (conway.evolve (t - decCapZ p i r) (decCapStartZ p i r) : Set Cell)
  else if t ≤ decT0Z p i r z + (134 + decTZn p i r z * 254) then
    linkFootW p z (decTZn p i r z) (decGZ p i r) (decCsZ p i r z) (decDispZ p i r)
      (decT0Z p i r z) (t - decDispZ p i r)
  else outFoot p z (decT0Z p i r z + (134 + decTZn p i r z * 254)) t

/-- **The end of an NZ activation**: at station `j` the answer and the token `KNZ` are captured,
the dispatched answer follows its route to the entry copy of unit `i + 1`, the entry chain relays
it, and the control flies to the body input of unit `i + 1`. -/
theorem decFinNProc {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hmem : ∀ x ∈ decLFN p i r, x ∈ machPieces p)
    (hcap : ∀ k < 692, ∀ h ∈ decLFN p i r, h ∉ stNZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decCapStartN p i r) : Set Cell) h.box)
    (hsep : RouteSepX (machPieces p) (machRegion p) (decGN p i r) (decCsN p i r)
      ((decDispN p i r : ℕ) : ℤ))
    (hfly : ∀ t : ℕ, routeEndX (decGN p i r) (decCsN p i r) (decDispN p i r) ≤ t →
      t + 16 < decT0N p i r → ∀ h ∈ decLFN p i r, FarApart 2 ((decFinN p i r).box t) h.box)
    (hent : ∀ h ∈ decLFN p i r, h ∉ chainPieces p (i + 1) (decTNn p i r) →
      FarApart 2 (entryFoot p (i + 1) (decTNn p i r)) h.box)
    (hout : ∀ t : ℕ, t < 166 → ∀ h ∈ decLFN p i r, FarApart 2
      ((fun c => (unitDX p (i + 1), unitDY p (i + 1)) + c) '' chainOutWL.box (-166 + (t : ℤ)))
      h.box) :
    Reaction (piecesAt (decLFN p i r) (decCapN p i r) ∪
        ((decAnsWLN p i r).cells (decCapN p i r) ∪ (decTokN p i r).cells (decCapN p i r)))
      (piecesAt (decLFN p i r) (decEndN p i r) ∪ ctrlAt p (i + 1)) (decEndN p i r - decCapN p i r)
      (fun k => boxesOf (decLFN p i r) ∪ finFootN p i r (decCapN p i r + k)) := by
  have hL : (decLFN p i r).Pairwise Piece.Sep :=
    dd_pairwise (machPieces_sep p hp) fun x hx => hmem x (mem_dd.2 hx)
  have hc := decCap_cast p hi
  obtain ⟨hD, hle, hT0, -, -, hDT⟩ := decN_times hp hi
  obtain ⟨hl, ht, hδ, hfin, -⟩ := decAnsN_plan hp hi _ hD
  have hcap' := stationNZ_captureE p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
    (decCapN p i r) hc.1
  have w1 := window_mem hL (A := stNZOne p r (callerIdx p r i))
    (fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_append_left _ hx)))
    (decCapN p i r) 692 (Reaction.exact hcap'.evolve_eq) fun j hj h hh hn => hcap j hj h hh hn
  have eD : decCapN p i r + 692 = decDispN p i r := by unfold decCapN decDispN; omega
  have eD' : ((decCapN p i r : ℕ) : ℤ) + 692 = ((decDispN p i r : ℕ) : ℤ) := by
    rw [← eD]; push_cast; ring
  rw [eD, eD'] at w1
  have hsM := RouteSepX.toXM (L := decLFN p i r) hmem (decCsN p i r) (decGN p i r)
    (decDispN p i r) ht
    (fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map_of_mem hx)))) hsep
  obtain ⟨g1, g2, -⟩ := decGN_dir p i r
  obtain ⟨-, w2⟩ := link_entryW p hL (i + 1) (decTNn p i r) (g := decGN p i r)
    (cs := decCsN p i r) (T := decDispN p i r) ⟨Or.inr g1, Or.inl g2⟩ hl ht hsM hδ hfin hT0
    (by unfold decCsN; omega)
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx)) hfly hent
  have w3 := window hL (decT0N p i r + (134 + decTNn p i r * 254)) 166
    (orOut_flight_unit p (i + 1)) fun j hj h hh => hout j hj h hh
  have w := (w1.seq w2).seq w3
  refine (w.castN (by unfold decEndN decCapN decDispN at *; omega)).mono fun k _ => ?_
  simp only [finFootN, outFoot]
  split_ifs <;> first
    | (exfalso; unfold decEndN decCapN decDispN at *; omega)
    | (rw [show decCapN p i r + k - decCapN p i r = k by omega]; exact Set.Subset.rfl)
    | (have e : decCapN p i r + k - decDispN p i r = k - 692 := by
          unfold decCapN decDispN at *; omega
       rw [e])
    | (rw [show decCapN p i r + k - (decT0N p i r + (134 + decTNn p i r * 254)) =
          k - (692 + (decT0N p i r + (134 + decTNn p i r * 254) - decDispN p i r)) by
          unfold decCapN decDispN at *; omega])

/-- **The end of a Z activation**: at station `j` the answer and the token `KZ` are captured,
the dispatched answer follows its route to the entry copy of unit `z`, the entry chain relays
it, and the control flies to the body input of unit `z`. -/
theorem decFinZProc {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hmem : ∀ x ∈ decLFZ p i r z, x ∈ machPieces p)
    (hcap : ∀ k < 672, ∀ h ∈ decLFZ p i r z, h ∉ stZOne p r (callerIdx p r i) →
      FarApart 2 (conway.evolve k (decCapStartZ p i r) : Set Cell) h.box)
    (hsep : RouteSepX (machPieces p) (machRegion p) (decGZ p i r) (decCsZ p i r z)
      ((decDispZ p i r : ℕ) : ℤ))
    (hfly : ∀ t : ℕ, routeEndX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) ≤ t →
      t + 16 < decT0Z p i r z → ∀ h ∈ decLFZ p i r z, FarApart 2 ((decFinZ p i r z).box t) h.box)
    (hent : ∀ h ∈ decLFZ p i r z, h ∉ chainPieces p z (decTZn p i r z) →
      FarApart 2 (entryFoot p z (decTZn p i r z)) h.box)
    (hout : ∀ t : ℕ, t < 166 → ∀ h ∈ decLFZ p i r z, FarApart 2
      ((fun c => (unitDX p z, unitDY p z) + c) '' chainOutWL.box (-166 + (t : ℤ)))
      h.box) :
    Reaction (piecesAt (decLFZ p i r z) (decCapZ p i r) ∪
        ((decAnsWLZ p i r).cells (decCapZ p i r) ∪ (decTokZ p i r).cells (decCapZ p i r)))
      (piecesAt (decLFZ p i r z) (decEndZ p i r z) ∪ ctrlAt p z) (decEndZ p i r z - decCapZ p i r)
      (fun k => boxesOf (decLFZ p i r z) ∪ finFootZ p i r z (decCapZ p i r + k)) := by
  have hL : (decLFZ p i r z).Pairwise Piece.Sep :=
    dd_pairwise (machPieces_sep p hp) fun x hx => hmem x (mem_dd.2 hx)
  have hc := decCap_cast p hi
  obtain ⟨hD, hle, hT0, -, -, hDT⟩ := decZ_times hp hi
  obtain ⟨hl, ht, hδ, hfin, -⟩ := decAnsZ_plan hp hi _ hD
  have hcap' := stationZ_captureE p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
    (decCapZ p i r) hc.2
  have w1 := window_mem hL (A := stZOne p r (callerIdx p r i))
    (fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_append_left _ hx)))
    (decCapZ p i r) 672 (Reaction.exact hcap'.evolve_eq) fun j hj h hh hn => hcap j hj h hh hn
  have eD : decCapZ p i r + 672 = decDispZ p i r := by unfold decCapZ decDispZ; omega
  have eD' : ((decCapZ p i r : ℕ) : ℤ) + 672 = ((decDispZ p i r : ℕ) : ℤ) := by
    rw [← eD]; push_cast; ring
  rw [eD, eD'] at w1
  have hsM := RouteSepX.toXM (L := decLFZ p i r z) hmem (decCsZ p i r z) (decGZ p i r)
    (decDispZ p i r) ht
    (fun x hx => mem_dd.2 (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map_of_mem hx)))) hsep
  obtain ⟨g1, g2, -⟩ := decGZ_dir p i r
  obtain ⟨-, w2⟩ := link_entryW p hL z (decTZn p i r z) (g := decGZ p i r)
    (cs := decCsZ p i r z) (T := decDispZ p i r) ⟨Or.inl g1, Or.inl g2⟩ hl ht hsM hδ hfin hT0
    (by unfold decCsZ; omega)
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx)) hfly hent
  have w3 := window hL (decT0Z p i r z + (134 + decTZn p i r z * 254)) 166
    (orOut_flight_unit p z) fun j hj h hh => hout j hj h hh
  have w := (w1.seq w2).seq w3
  refine (w.castN (by unfold decEndZ decCapZ decDispZ at *; omega)).mono fun k _ => ?_
  simp only [finFootZ, outFoot]
  split_ifs <;> first
    | (exfalso; unfold decEndZ decCapZ decDispZ at *; omega)
    | (rw [show decCapZ p i r + k - decCapZ p i r = k by omega]; exact Set.Subset.rfl)
    | (have e : decCapZ p i r + k - decDispZ p i r = k - 672 := by
          unfold decCapZ decDispZ at *; omega
       rw [e])
    | (rw [show decCapZ p i r + k - (decT0Z p i r z + (134 + decTZn p i r z * 254)) =
          k - (672 + (decT0Z p i r z + (134 + decTZn p i r z * 254) - decDispZ p i r)) by
          unfold decCapZ decDispZ at *; omega])

/-! ### The register runs placed in time -/

/-- The end of the NZ register runs (`sh + 11190`). -/
def decRunEndN (p : Program) (i r : ℕ) : ℕ := decTS p i r + 11490

/-- The end of the Z register run (`sh + 27240`). -/
def decRunEndZ (p : Program) (i r : ℕ) : ℕ := decTS p i r + 27540

/-- **The footprint of the rest of an NZ run**, at the absolute time `t`: the rest region, then the
circuit and the lanes of the register idling. -/
def restFootN (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decRunEndN p i r then modImg p r decRestRegNZ else boxesOf (modGroup p r) ∪ modLanes p r

/-- **The footprint of the rest of the Z run**, at the absolute time `t`. -/
def restFootZ (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decRunEndZ p i r then modImg p r dz2mk0RestRegion
  else boxesOf (modGroup p r) ∪ modLanes p r

/-- Two delays of a register add up. -/
theorem RegS.later_later' (R : RegS) (a b : ℕ) : (R.later a).later b = R.later (a + b) := by
  simp only [RegS.later, add_assoc]

/-- The circuit and the diagonal of register `r` idle (after a run). -/
theorem circuitIdle (p : Program) (r : ℕ) {R : RegS} (hR : R.Inv)
    (hgl : FarApart 2 (boxesOf (modGroup p r)) (modLanes p r)) (T n : ℕ) :
    Reaction (piecesAt (modGroup p r) T ∪ regAt p r R)
      (piecesAt (modGroup p r) (T + n) ∪ regAt p r (R.later n)) n
      (fun _ => boxesOf (modGroup p r) ∪ modLanes p r) :=
  ((idleR (modGroup_sep p r) T n).par (regAt_reaction p r hR n) fun j _ =>
    hgl.mono le_rfl (regStrip_subset hR p r j)).mono fun j _ =>
    Set.union_subset_union le_rfl (regStrip_subset hR p r j)

/-- The circuit of module `r` at a time `≡ 0 (mod 30)`. -/
theorem modGroup_at0 (p : Program) (r : ℕ) {T : ℕ} (hT : T % 30 = 0) :
    piecesAt (modGroup p r) T = translate (modDX p r, modDY p r) dz2gRest := by
  rw [modGroup_at, hT, Rule.evolve_zero]

/-- **The NZ register run of the activation**, from `decTS` (value `≥ 1`): up to the cut, then
the rest and the circuit idling until `E`; the register holds one less. -/
theorem decRunNProc {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) {R : RegS}
    (hR : R.Ready) (hpos : 1 ≤ R.val)
    (hgl : FarApart 2 (boxesOf (modGroup p r)) (modLanes p r)) (E : ℕ)
    (hE : decRunEndN p i r ≤ E) :
    ∃ (X : Finset Cell) (R' : RegS), R'.val + 1 = R.val ∧ R'.Ready ∧
      Reaction (piecesAt (modGroup p r) (decTS p i r) ∪
          (translate (modDX p r, modDY p r) (ofRows (-1186) (-1227) [2, 4, 7]) ∪ regAt p r R))
        (X ∪ (decAnsWLN p i r).cells (decCutN p i r)) 9503 (fun _ => modImg p r decRunRegNZ) ∧
      Reaction X (piecesAt (modGroup p r) E ∪ regAt p r (R'.later (E - decRunEndN p i r)))
        (E - decCutN p i r) (fun k => restFootN p i r (decCutN p i r + k)) := by
  obtain ⟨hS, hS30, -⟩ := decTS_facts p hi
  obtain ⟨X, R', h1, h2, h3, h4⟩ := regNZ_module p r hR hpos
  refine ⟨X, R', h1, h2, ?_, ?_⟩
  · rw [modGroup_at0 p r hS30, ← union_assoc, ← translate_union]
    have e : translate (modDX p r, modDY p r) (ansNZWL.cells 9203) =
        (decAnsWLN p i r).cells (decCutN p i r) := by
      rw [runAnsNZ_placed p r (decShift p i r)]
      congr 1
      unfold decCutN; push_cast; omega
    rw [← e]
    exact h3
  · have hid := circuitIdle p r h2.1 hgl (decRunEndN p i r) (E - decRunEndN p i r)
    rw [modGroup_at0 p r (by unfold decRunEndN; omega),
      show decRunEndN p i r + (E - decRunEndN p i r) = E by omega] at hid
    have w := h4.seq hid
    refine (w.castN (by unfold decRunEndN decCutN at *; omega)).mono fun k _ => ?_
    simp only [restFootN]
    split_ifs <;> first
      | (exfalso; unfold decRunEndN decCutN at *; omega)
      | exact Set.Subset.rfl

/-- **The Z register run of the activation**, from `decTS` (value `0`): up to the cut, then the
rest of the Z restore and the circuit idling until `E`; the register is unchanged. -/
theorem decRunZProc {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) {R : RegS}
    (hR : R.Ready) (h0 : R.val = 0)
    (hgl : FarApart 2 (boxesOf (modGroup p r)) (modLanes p r)) (E : ℕ)
    (hE : decRunEndZ p i r ≤ E) :
    ∃ X : Finset Cell,
      Reaction (piecesAt (modGroup p r) (decTS p i r) ∪
          (translate (modDX p r, modDY p r) (ofRows (-1186) (-1227) [2, 4, 7]) ∪ regAt p r R))
        (X ∪ (decAnsWLZ p i r).cells (decCutZ p i r)) 11995
        (fun _ => modImg p r decRunRegZ) ∧
      Reaction X (piecesAt (modGroup p r) E ∪ regAt p r (R.later (E - decTS p i r)))
        (E - decCutZ p i r) (fun k => restFootZ p i r (decCutZ p i r + k)) := by
  obtain ⟨hS, hS30, -⟩ := decTS_facts p hi
  obtain ⟨X, h3, h4⟩ := regZ_module p r hR h0
  refine ⟨X, ?_, ?_⟩
  · rw [modGroup_at0 p r hS30, ← union_assoc, ← translate_union]
    have e : translate (modDX p r, modDY p r) (ansZWL.cells 11695) =
        (decAnsWLZ p i r).cells (decCutZ p i r) := by
      rw [runAnsZ_placed p r (decShift p i r)]
      congr 1
      unfold decCutZ; push_cast; omega
    rw [← e]
    exact h3
  · have hid := circuitIdle p r (hR.1.later 27540) hgl (decRunEndZ p i r) (E - decRunEndZ p i r)
    rw [modGroup_at0 p r (by unfold decRunEndZ; omega),
      show decRunEndZ p i r + (E - decRunEndZ p i r) = E by omega, RegS.later_later',
      show 27540 + (E - decRunEndZ p i r) = E - decTS p i r by unfold decRunEndZ at *; omega]
      at hid
    have w := h4.seq hid
    refine (w.castN (by unfold decRunEndZ decCutZ at *; omega)).mono fun k _ => ?_
    simp only [restFootZ]
    split_ifs <;> first
      | (exfalso; unfold decRunEndZ decCutZ at *; omega)
      | exact Set.Subset.rfl

end LP

end LeanTheory.Life
