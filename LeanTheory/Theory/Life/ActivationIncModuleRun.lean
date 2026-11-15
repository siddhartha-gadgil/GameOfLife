/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncThread

/-!
# The INC input of a module: gate, `RF_J`, and the increment

Item (h) of the `inc` activation (research note `N-22`): from the merge link arriving on the INC
window of module `r` (offset `δ ∈ {4, 5}`, time `194 + 30 k`) to the register holding one more:

* `piecesAt_group`, `bodyGroup_at`, `modGroup_at`: the groups of a body or a register circuit
  placed by `groupSpecs`, at any phase, are the template's circuit at that phase, translated;
* `modFoot`: the footprint of the module part before the increment (INC OR gate, flight to
  `RF_J`, reflection, flight to the input of the increment);
* `module_run`: the whole module part, with the pieces of a list `L` idle beside it and the
  register diagonal of the module; the increment (`regInc_module`) has its exact evolution as
  footprint;
* **the satisfiable form** (the hypotheses `hfl1`, `hfl2` of `module_pre` are unsatisfiable: the
  glider touches `RF_J` before and after the reflection, `ActivationIncSepFalse`):
  `incGate_approach` (the gate and the arriving glider together from `Tg - 16`, inside the gate
  box; certificates `Gen/SideEarly`), `modFootW`, `module_preW`, `modRunFootW`, `module_runW`,
  `module_run_nW`: `RF_J` is a corner run with `reflect_earlyX` from `Tg + 871` to `Tg + 931`
  inside `relayBoxX (rfJCorner p r)`; the flights are required far only outside that window.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Groups of pieces placed by `groupSpecs` -/

/-- The groups placed by `groupSpecs` at time `T` are the base pieces at time `T`, translated. -/
theorem piecesAt_group (Ls : List Base) (dx dy : ℤ) (T : ℕ) :
    piecesAt ((groupSpecs Ls dx dy).map PSpec.piece) T =
      translate (dx, dy) (piecesAt (Ls.map Base.piece) T) := by
  induction Ls with
  | nil => simp [piecesAt, groupSpecs]
  | cons g Ls ih =>
    simp only [groupSpecs, List.map_cons, piecesAt, List.foldr_cons] at ih ⊢
    rw [ih, translate_union]
    congr 1
    simp only [PSpec.piece, Piece.place, phase, Nat.zero_mod, Rule.evolve_zero,
      Rule.evolve_translate]

/-- The pieces of a separated list at time `n` are those at time `0`, `n` generations later. -/
theorem piecesAt_evolve {L : List Piece} (hL : L.Pairwise Piece.Sep) (n : ℕ) :
    conway.evolve n (piecesAt L 0) = piecesAt L n := by
  have h := (bundleAt L hL 0 n).reaction.evolve_eq
  rw [bundleAt_P, bundleAt_Q, zero_add] at h
  exact h

/-- The groups of the register circuit at time `0` are `dz2gRest`. -/
theorem piecesAt_dz2g : piecesAt dz2gPieces 0 = dz2gRest := by
  simp only [piecesAt, Nat.zero_mod, Rule.evolve_zero, dz2gPieces, List.foldr_cons,
    List.foldr_nil, union_empty]
  rfl

/-- The groups of the `inc` body at time `0` are `bodyIncRest`. -/
theorem piecesAt_bodyInc : piecesAt bodyIncPieces 0 = bodyIncRest := by
  simp only [piecesAt, Nat.zero_mod, Rule.evolve_zero, bodyIncPieces, List.foldr_cons,
    List.foldr_nil, union_empty, bodyIncRest, union_assoc]
  rfl

/-- The register circuit of module `r` as pieces. -/
def modGroup (p : Program) (r : ℕ) : List Piece :=
  (groupSpecs ((List.range 28).map Base.dz2g) (modDX p r) (modDY p r)).map PSpec.piece

/-- The body of unit `a` (an `inc` unit) as pieces. -/
def bodyGroup (p : Program) (a : ℕ) : List Piece :=
  (groupSpecs ((List.range 3).map Base.bodyInc) (unitDX p a) (unitDY p a)).map PSpec.piece

/-- **The register circuit of module `r` at time `T`**: `dz2gRest` at phase `T`, translated. -/
theorem modGroup_at (p : Program) (r : ℕ) (T : ℕ) :
    piecesAt (modGroup p r) T =
      translate (modDX p r, modDY p r) (conway.evolve (T % 30) dz2gRest) := by
  rw [modGroup, piecesAt_group, List.map_map]
  have e : ((List.range 28).map (Base.piece ∘ Base.dz2g)) = dz2gPieces := dz2g_map
  rw [e, piecesAt_mod dz2gPieces (show T % 30 = (T % 30) % 30 by omega),
    ← piecesAt_evolve dz2gPieces_sep, piecesAt_dz2g]

/-- **The body of unit `a` at a time `≡ 0 (mod 30)`**: `bodyIncRest`, translated. -/
theorem bodyGroup_at (p : Program) (a : ℕ) {T : ℕ} (hT : T % 30 = 0) :
    piecesAt (bodyGroup p a) T = translate (unitDX p a, unitDY p a) bodyIncRest := by
  rw [bodyGroup, piecesAt_group, List.map_map]
  have e : ((List.range 3).map (Base.piece ∘ Base.bodyInc)) = bodyIncPieces := bodyInc_map
  rw [e, piecesAt_mod bodyIncPieces (show T % 30 = 0 % 30 by omega), piecesAt_bodyInc]

/-! ### The module part -/

/-- The INC OR gate of module `r` as a piece. -/
def gateP (p : Program) (r : ℕ) : Piece := (incGateSpec p r).piece

/-- `RF_J` of module `r` as a piece. -/
def rfJP (p : Program) (r : ℕ) : Piece :=
  (⟨.rf 4, modDX p r - 850, modDY p r - 1044, 25⟩ : PSpec).piece

/-- The output line of the INC OR gate (module `r`), delayed for the arrival `k`. -/
def gateOutWL (p : Program) (r : ℕ) (k : ℤ) : WL :=
  (modWL p r ⟨1, 1, 173, 3431⟩).shift 0 0 (1140 + 30 * k)

/-- The output line of `RF_J` (module `r`), delayed for the arrival `k`. -/
def rfJOutWL (p : Program) (r : ℕ) (k : ℤ) : WL := (modWL p r incInWL).shift 0 0 (1140 + 30 * k)

/-- The box of the INC OR gate of module `r` during its reaction. -/
def gateBox (p : Program) (r : ℕ) : Set Cell :=
  (fun c => (modDX p r - 1132, modDY p r - 1291) + c) '' Box 0 90 0 60

/-- **The footprint of the module part before the increment**, `j` generations after the arrival
at the gate at time `Tg = 194 + 30 k`. -/
def modFoot (p : Program) (r : ℕ) (k : ℤ) (Tg j : ℕ) : Set Cell :=
  if j ≤ 134 then gateBox p r
  else if j ≤ 891 then (gateOutWL p r k).box ((Tg : ℤ) + j)
  else if j ≤ 921 then relayBox (rfJCorner p r)
  else (rfJOutWL p r k).box ((Tg : ℤ) + j)

/-- The start of the increment at module `r`: the circuit and the input glider, translated. -/
def incStart (p : Program) (r : ℕ) : Finset Cell :=
  translate (modDX p r, modDY p r) (dz2gRest ∪ incInWL.cells 0)

/-- **From the INC gate to the input of the increment**: the glider arriving on the INC window of
module `r` at offset `δ`, time `Tg = 194 + 30 k`, passes the INC OR gate, flies to `RF_J`, is
reflected and flies to the input of the increment, reached at `Tg + 946 = 1140 + 30 k`; the pieces
of `L` (containing the gate and `RF_J`) idle beside it. (The hypotheses `hfl1`, `hfl2` cannot hold
in the layout: the glider touches `RF_J` at `Tg + 881 … 890` and `Tg + 921 … 923`; use
`module_preW`.) -/
theorem module_pre (p : Program) (r : ℕ) {L : List Piece} (hL : L.Pairwise Piece.Sep)
    (hg : gateP p r ∈ L) (hj : rfJP p r ∈ L) {δ k : ℤ} (hδ : δ = 4 ∨ δ = 5) {Tg : ℕ}
    (hTg : (Tg : ℤ) = 194 + 30 * k)
    (hgate : ∀ h ∈ L, h ≠ gateP p r → FarApart 2 (gateBox p r) h.box)
    (hfl1 : ∀ j : ℕ, 134 ≤ j → j < 891 → ∀ h ∈ L,
      FarApart 2 ((gateOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hrf : ∀ h ∈ L, h ≠ rfJP p r → FarApart 2 (relayBox (rfJCorner p r)) h.box)
    (hfl2 : ∀ j : ℕ, 921 ≤ j → j < 946 → ∀ h ∈ L,
      FarApart 2 ((rfJOutWL p r k).box ((Tg : ℤ) + j)) h.box) :
    Reaction (piecesAt L Tg ∪ ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg)
      (piecesAt L (Tg + 946) ∪ translate (modDX p r, modDY p r) (incInWL.cells 0)) 946
      (fun j => boxesOf L ∪ modFoot p r k Tg j) := by
  -- the gate
  have hg1 : Reaction
      (piecesAt [gateP p r] Tg ∪ ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg)
      (piecesAt [gateP p r] (Tg + 134) ∪ (gateOutWL p r k).cells ((Tg + 134 : ℕ) : ℤ)) 134
      (fun _ => gateBox p r) := by
    have h := incGate_reaction p r hδ Tg (by omega)
    rw [piecesAt_single, piecesAt_single, gateP,
      show ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg =
        translate (modDX p r - 1132, modDY p r - 1291) (sideIn δ) by
        rw [show (Tg : ℤ) = 194 + 30 * k from hTg]; exact module_side_arrival p r δ k hδ,
      show (gateOutWL p r k).cells ((Tg + 134 : ℕ) : ℤ) =
        translate (modDX p r - 1132 + 35, modDY p r - 1291 + 64) orIn by
        rw [gateOutWL, incGate_out p r k]; congr 1; push_cast; omega]
    exact h
  have w1 := window_mem hL (A := [gateP p r]) (by simpa using hg) Tg 134 hg1
    fun j _ h hh hne => hgate h hh (by simpa using hne)
  -- the flight to `RF_J`
  have hd1 : (gateOutWL p r k).Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have w2 := window hL (Tg + 134) 757 (WL.flight hd1 ((Tg + 134 : ℕ) : ℤ) 757) fun j hj h hh => by
    have := hfl1 (134 + j) (by omega) (by omega) h hh
    convert this using 2
    push_cast
    ring
  -- `RF_J`
  have hm : ((Tg + 134 + 757 : ℕ) : ℤ) = meetT (gateOutWL p r k) (rfJCorner p r) := by
    rw [gateOutWL, rfJ_meet]; push_cast; omega
  have hr := reflect_reaction_single (rfJ_onLine p r (1140 + 30 * k)) _ hm
  rw [rfJ_reflect p r (1140 + 30 * k) (by omega)] at hr
  have w3 := window_mem hL (A := [rfJP p r]) (by simpa using hj) _ 30 hr
    fun j _ h hh hne => hrf h hh (by simpa using hne)
  -- the flight to the increment
  have hd2 : (rfJOutWL p r k).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have w4 := window hL (Tg + 134 + 757 + 30) 25
      (WL.flight hd2 ((Tg + 134 + 757 + 30 : ℕ) : ℤ) 25) fun j hj h hh => by
    have := hfl2 (921 + j) (by omega) (by omega) h hh
    convert this using 2
    push_cast
    ring
  have e4 : (rfJOutWL p r k).cells (((Tg + 134 + 757 + 30 : ℕ) : ℤ) + ((25 : ℕ) : ℤ)) =
      translate (modDX p r, modDY p r) (incInWL.cells 0) := by
    rw [rfJOutWL, ← rfJ_to_dz2e p r k]
    congr 1
    push_cast
    omega
  rw [e4, show Tg + 134 + 757 + 30 + 25 = Tg + 946 by ring] at w4
  have w := ((w1.seq w2).seq w3).seq w4
  refine (w.castN (by norm_num)).mono fun j _ => ?_
  simp only [modFoot]
  by_cases h1 : j ≤ 134
  · simp only [h1, show j ≤ 134 + 757 by omega, show j ≤ 134 + 757 + 30 by omega, ↓reduceIte]
    exact le_rfl
  by_cases h2 : j ≤ 891
  · simp only [h1, h2, show j ≤ 134 + 757 + 30 by omega, ↓reduceIte]
    rw [show ((Tg + 134 : ℕ) : ℤ) + ((j - 134 : ℕ) : ℤ) = (Tg : ℤ) + j by
      push_cast [Nat.cast_sub (show 134 ≤ j by omega)]; ring]
  by_cases h3 : j ≤ 921
  · simp only [h1, h2, h3, ↓reduceIte]
    exact le_rfl
  · simp only [h1, h2, h3, ↓reduceIte]
    rw [show ((Tg + 134 + 757 + 30 : ℕ) : ℤ) + ((j - (134 + 757 + 30) : ℕ) : ℤ) = (Tg : ℤ) + j by
      push_cast [Nat.cast_sub (show 134 + 757 + 30 ≤ j by omega)]; ring]

/-- The register circuit `dz2gRest` is periodic: its phase depends on the time mod `30`. -/
theorem dz2gRest_mod (n : ℕ) : conway.evolve n dz2gRest = conway.evolve (n % 30) dz2gRest := by
  rw [← piecesAt_dz2g, piecesAt_evolve dz2gPieces_sep, piecesAt_evolve dz2gPieces_sep,
    piecesAt_mod dz2gPieces (show n % 30 = (n % 30) % 30 by omega)]

/-- The footprint of the whole module part: before the increment `modFoot` and the strip of the
register; then the exact evolution of the increment. -/
def modRunFoot (p : Program) (r : ℕ) (L : List Piece) (k : ℤ) (Tg : ℕ) (R : RegS) (j : ℕ) :
    Set Cell :=
  if j ≤ 946 then boxesOf L ∪ modFoot p r k Tg j ∪ regStrip p r R (j + R.m)
  else boxesOf L ∪ (conway.evolve (j - 946) (incStart p r ∪ regAt p r (R.later 946)) : Set Cell)

/-- **The module part of the `inc` activation**: the merge link arriving on the INC window of
module `r` (offset `δ`, time `Tg = 194 + 30 k`), the pieces of `L` (containing the gate, `RF_J`
and the register circuit of the module) and the register diagonal become, `946 + d` generations
later, the pieces and the diagonal of the register holding one more. -/
theorem module_run (p : Program) (r : ℕ) {L : List Piece} (hL : L.Pairwise Piece.Sep)
    (hg : gateP p r ∈ L) (hj : rfJP p r ∈ L) (hgrp : ∀ x ∈ modGroup p r, x ∈ L) {δ k : ℤ}
    (hδ : δ = 4 ∨ δ = 5) {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {R : RegS} (hR : R.Ready)
    (hgate : ∀ h ∈ L, h ≠ gateP p r → FarApart 2 (gateBox p r) h.box)
    (hfl1 : ∀ j : ℕ, 134 ≤ j → j < 891 → ∀ h ∈ L,
      FarApart 2 ((gateOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hrf : ∀ h ∈ L, h ≠ rfJP p r → FarApart 2 (relayBox (rfJCorner p r)) h.box)
    (hfl2 : ∀ j : ℕ, 921 ≤ j → j < 946 → ∀ h ∈ L,
      FarApart 2 ((rfJOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hstrip : ∀ j < 946, FarApart 2 (boxesOf L ∪ modFoot p r k Tg j) (regStrip p r R (j + R.m)))
    (hinc : ∀ i ≤ 7050, ∀ h ∈ L, h ∉ modGroup p r →
      FarApart 2 (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell) h.box) :
    ∃ (d : ℕ) (R' : RegS), 6990 ≤ d ∧ d ≤ 7050 ∧ R'.val = R.val + 1 ∧ R'.Ready ∧
      (∀ i ≤ d, (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell) ⊆
        (fun c => (modDX p r, modDY p r) + c) '' incRunBox) ∧
      Reaction (piecesAt L Tg ∪ (((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
          regAt p r R))
        (piecesAt L (Tg + 946 + d) ∪ regAt p r R') (946 + d) (modRunFoot p r L k Tg R) := by
  have hpre := (module_pre p r hL hg hj hδ hTg hgate hfl1 hrf hfl2).par
    (regAt_reaction p r hR.1 946) hstrip
  obtain ⟨d, R', h1, h2, h3, h4, hev, hsub⟩ := regInc_module p r (hR.later 946)
  have hT1 : (Tg + 946) % 30 = 0 := by omega
  have hinc' : Reaction (piecesAt (modGroup p r) (Tg + 946) ∪
        (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)))
      (piecesAt (modGroup p r) (Tg + 946 + d) ∪ regAt p r R') d
      (fun i => (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell)) := by
    have e1 : piecesAt (modGroup p r) (Tg + 946) ∪
        (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)) =
        incStart p r ∪ regAt p r (R.later 946) := by
      rw [modGroup_at, hT1, Rule.evolve_zero, incStart, translate_union, union_assoc]
    have e2 : piecesAt (modGroup p r) (Tg + 946 + d) =
        translate (modDX p r, modDY p r) (conway.evolve (d - 6990) dz2gRest) := by
      rw [modGroup_at, dz2gRest_mod (d - 6990),
        show (Tg + 946 + d) % 30 = (d - 6990) % 30 by omega]
    rw [e1, e2]
    exact Reaction.exact hev
  have w := window_mem hL hgrp (Tg + 946) d hinc' fun i hi h hh hne => hinc i (by omega) h hh hne
  refine ⟨d, R', h1, h2, h3, h4, hsub, ?_⟩
  have e3 : piecesAt L Tg ∪ ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
      regAt p r R = piecesAt L Tg ∪ (((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
        regAt p r R) := union_assoc _ _ _
  have e4 : piecesAt L (Tg + 946) ∪ translate (modDX p r, modDY p r) (incInWL.cells 0) ∪
      regAt p r (R.later 946) = piecesAt L (Tg + 946) ∪
        (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)) :=
    union_assoc _ _ _
  rw [e3, e4] at hpre
  refine (hpre.seq w).mono fun j _ => ?_
  simp only [modRunFoot]
  split_ifs <;> exact le_rfl
/-- The lanes of the register diagonal of module `r`. -/
def modLanes (p : Program) (r : ℕ) : Set Cell := (fun c => (modDX p r, modDY p r) + c) '' regLanes

/-- **The strip of a valid register lies in the lanes of its module.** -/
theorem regStrip_subset {R : RegS} (hR : R.Inv) (p : Program) (r i : ℕ) :
    regStrip p r R (i + R.m) ⊆ modLanes p r := by
  unfold regStrip modLanes
  apply Set.image_mono
  apply wStrip_subset_regLanes
  · have h1 := hR.2.2.1
    have h2 : R.m / 4 ≤ (i + R.m) / 4 := Nat.div_le_div_right (by omega)
    have h3 : ((R.m / 4 : ℕ) : ℤ) ≤ (((i + R.m) / 4 : ℕ) : ℤ) := by exact_mod_cast h2
    linarith
  · have := hR.2.1
    omega

/-- The register circuit of module `r` is pairwise separated. -/
theorem modGroup_sep (p : Program) (r : ℕ) : (modGroup p r).Pairwise Piece.Sep := by
  unfold modGroup
  rw [List.pairwise_map]
  apply groupSpecs_sep
  rw [List.map_map]
  exact dz2g_map ▸ dz2gPieces_sep

/-- **The module part of the `inc` activation, for any duration `n ≥ 7050` of the increment
window**: as `module_run`, followed by the circuit and the register idling; the footprint is
`modRunFoot` (the exact evolution after the input of the increment). -/
theorem module_run_n (p : Program) (r : ℕ) {L : List Piece} (hL : L.Pairwise Piece.Sep)
    (hg : gateP p r ∈ L) (hj : rfJP p r ∈ L) (hgrp : ∀ x ∈ modGroup p r, x ∈ L) {δ k : ℤ}
    (hδ : δ = 4 ∨ δ = 5) {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {R : RegS} (hR : R.Ready)
    (hgate : ∀ h ∈ L, h ≠ gateP p r → FarApart 2 (gateBox p r) h.box)
    (hfl1 : ∀ j : ℕ, 134 ≤ j → j < 891 → ∀ h ∈ L,
      FarApart 2 ((gateOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hrf : ∀ h ∈ L, h ≠ rfJP p r → FarApart 2 (relayBox (rfJCorner p r)) h.box)
    (hfl2 : ∀ j : ℕ, 921 ≤ j → j < 946 → ∀ h ∈ L,
      FarApart 2 ((rfJOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hstrip : ∀ j < 946, FarApart 2 (boxesOf L ∪ modFoot p r k Tg j) (modLanes p r))
    (hlanes : FarApart 2 (boxesOf (modGroup p r)) (modLanes p r)) (n : ℕ) (hn : 7050 ≤ n)
    (hinc : ∀ i ≤ n, ∀ h ∈ L, h ∉ modGroup p r →
      FarApart 2 (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell) h.box) :
    ∃ R' : RegS, R'.val = R.val + 1 ∧ R'.Ready ∧
      (∀ i ≤ n, (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell) ⊆
        ((fun c => (modDX p r, modDY p r) + c) '' incRunBox ∪ boxesOf (modGroup p r)) ∪
          modLanes p r) ∧
      Reaction (piecesAt L Tg ∪ (((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
          regAt p r R))
        (piecesAt L (Tg + 946 + n) ∪ regAt p r R') (946 + n) (modRunFoot p r L k Tg R) := by
  have hpre := (module_pre p r hL hg hj hδ hTg hgate hfl1 hrf hfl2).par
    (regAt_reaction p r hR.1 946) fun j hj =>
      (hstrip j hj).mono le_rfl (regStrip_subset hR.1 p r j)
  obtain ⟨d, R', h1, h2, h3, h4, hev, hsub⟩ := regInc_module p r (hR.later 946)
  have hT1 : (Tg + 946) % 30 = 0 := by omega
  have hb := (bundleAt (modGroup p r) (modGroup_sep p r) (Tg + 946 + d) (n - d)).reaction
  rw [bundleAt_P, bundleAt_Q] at hb
  have hpar := (hb.mono fun i _ => (bundleAt_F _ _ _ _ i).le).par (regAt_reaction p r h4.1 (n - d))
    fun i _ => hlanes.mono le_rfl (regStrip_subset h4.1 p r i)
  have e1 : piecesAt (modGroup p r) (Tg + 946) ∪
      (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)) =
      incStart p r ∪ regAt p r (R.later 946) := by
    rw [modGroup_at, hT1, Rule.evolve_zero, incStart, translate_union, union_assoc]
  have e2 : piecesAt (modGroup p r) (Tg + 946 + d) =
      translate (modDX p r, modDY p r) (conway.evolve (d - 6990) dz2gRest) := by
    rw [modGroup_at, dz2gRest_mod (d - 6990),
      show (Tg + 946 + d) % 30 = (d - 6990) % 30 by omega]
  have htot : conway.evolve n (incStart p r ∪ regAt p r (R.later 946)) =
      piecesAt (modGroup p r) (Tg + 946 + n) ∪ regAt p r (R'.later (n - d)) := by
    have hsplit : conway.evolve n (incStart p r ∪ regAt p r (R.later 946)) =
        conway.evolve (n - d) (conway.evolve d (incStart p r ∪ regAt p r (R.later 946))) := by
      rw [← Rule.evolve_add]
      congr 1
      omega
    rw [hsplit, incStart, hev, ← e2, hpar.evolve_eq,
      show Tg + 946 + d + (n - d) = Tg + 946 + n by omega]
  have hinc' : Reaction (piecesAt (modGroup p r) (Tg + 946) ∪
        (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)))
      (piecesAt (modGroup p r) (Tg + 946 + n) ∪ regAt p r (R'.later (n - d))) n
      (fun i => (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell)) := by
    rw [e1]
    exact Reaction.exact htot
  have w := window_mem hL hgrp (Tg + 946) n hinc' fun i hi h hh hne => hinc i (by omega) h hh hne
  refine ⟨R'.later (n - d), by simp [h3], h4.later _, fun i hi => ?_, ?_⟩
  · by_cases hid : i ≤ d
    · exact (hsub i hid).trans (Set.subset_union_left.trans Set.subset_union_left)
    · have e : conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) =
          conway.evolve (i - d) (piecesAt (modGroup p r) (Tg + 946 + d) ∪ regAt p r R') := by
        rw [e2, show i = (i - d) + d by omega, Rule.evolve_add, incStart, hev,
          show i - d + d - d = i - d by omega]
      rw [e]
      refine (hpar.subset (i - d) (by omega)).trans (Set.union_subset_union ?_ ?_)
      · exact Set.subset_union_right
      · exact regStrip_subset h4.1 p r _
  · have e3 : piecesAt L Tg ∪ ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
        regAt p r R = piecesAt L Tg ∪ (((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
          regAt p r R) := union_assoc _ _ _
    have e4 : piecesAt L (Tg + 946) ∪ translate (modDX p r, modDY p r) (incInWL.cells 0) ∪
        regAt p r (R.later 946) = piecesAt L (Tg + 946) ∪
          (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)) :=
      union_assoc _ _ _
    rw [e3, e4] at hpre
    refine (hpre.seq w).mono fun j _ => ?_
    simp only [modRunFoot]
    split_ifs <;> exact le_rfl

/-! ### The INC gate with a side window and `RF_J` with a corner window -/

/-- **The early side input of the INC OR gate**: the glider on the INC window of module `r` at
offset `δ ∈ {4, 5}`, at time `178 + 30 k` (`16` generations before `module_side_arrival`). -/
theorem module_side_arrivalE (p : Program) (r : ℕ) (δ k : ℤ) (hδ : δ = 4 ∨ δ = 5) :
    ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells (178 + 30 * k) =
      translate (modDX p r - 1132, modDY p r - 1291) (sideInE δ) := by
  have hd : sideBase.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  rw [incWin_eq, WL.shift_cells (show WL.Dir ((sideBase.shift (-1132) (-1291) 14).shift
      (modDX p r) (modDY p r) 0) from hd),
    WL.shift_cells (show WL.Dir (sideBase.shift (-1132) (-1291) 14) from hd),
    WL.shift_cells hd, sideInE_cells hδ, translate_translate, translate_translate]
  congr 1
  · ext <;> simp <;> ring
  · congr 1
    ring

/-- **The approach of the merge link to the INC OR gate** (`side_approach` placed): from
`Ts = 178 + 30 k`, `16` generations before the arrival time `Tg = Ts + 16`, the gate and the
glider on the INC window run together, inside the gate box. -/
theorem incGate_approach (p : Program) (r : ℕ) {δ k : ℤ} (hδ : δ = 4 ∨ δ = 5) (Ts : ℕ)
    (hTs : (Ts : ℤ) = 178 + 30 * k) :
    Reaction (piecesAt [gateP p r] Ts ∪ ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Ts)
      (piecesAt [gateP p r] (Ts + 16) ∪
        ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells ((Ts + 16 : ℕ) : ℤ)) 16
      (fun _ => gateBox p r) := by
  have h := (side_approach hδ).translate (modDX p r - 1132, modDY p r - 1291)
  rw [piecesAt_single, piecesAt_single, gateP, incGateSpec, orGate_placed_at, orGate_placed_at,
    phase_congr orGate (a := 16 + Ts) (b := 14) (by omega),
    phase_congr orGate (a := 16 + (Ts + 16)) (b := 0) (by omega),
    show (Ts : ℤ) = 178 + 30 * k from hTs, module_side_arrivalE p r δ k hδ,
    show ((Ts + 16 : ℕ) : ℤ) = 194 + 30 * k by push_cast; omega,
    module_side_arrival p r δ k hδ, ← translate_union, ← translate_union]
  rw [show phase orGate 0 = orGate by rw [phase, Nat.zero_mod, Rule.evolve_zero]]
  refine h.mono fun _ _ => Set.image_mono fun c hc => ?_
  exact ⟨hc.1, hc.2.1, hc.2.2.1, by have := hc.2.2.2; omega⟩

/-- **The footprint of the module part before the increment, with the `RF_J` window**, `j`
generations after the arrival at the gate at time `Tg = 194 + 30 k`: the gate, the flight to
`RF_J` until `20` generations before the meeting (`Tg + 891`), the extended relay box of `RF_J`
from `Tg + 871` to `Tg + 931`, then the flight to the increment. -/
def modFootW (p : Program) (r : ℕ) (k : ℤ) (Tg j : ℕ) : Set Cell :=
  if j ≤ 134 then gateBox p r
  else if j ≤ 871 then (gateOutWL p r k).box ((Tg : ℤ) + j)
  else if j ≤ 931 then relayBoxX (rfJCorner p r)
  else (rfJOutWL p r k).box ((Tg : ℤ) + j)

/-- Sanity: during the corner window of `RF_J` the footprint is its extended relay box. -/
theorem modFootW_window (p : Program) (r : ℕ) (k : ℤ) (Tg : ℕ) {j : ℕ} (h1 : 871 < j)
    (h2 : j ≤ 931) : modFootW p r k Tg j = relayBoxX (rfJCorner p r) := by
  simp only [modFootW, show ¬ j ≤ 134 by omega, show ¬ j ≤ 871 by omega, h2, ↓reduceIte]

/-- **From the INC gate to the input of the increment, with the `RF_J` window** (the satisfiable
form of `module_pre`): as `module_pre`, but `RF_J` is run as a corner (`reflect_earlyX`): the
flight from the gate is required far from the pieces only until `Tg + 871`, `RF_J` and the glider
run together from `Tg + 871` to `Tg + 931` inside `relayBoxX (rfJCorner p r)`, and the flight to
the increment starts at `Tg + 931`. -/
theorem module_preW (p : Program) (r : ℕ) {L : List Piece} (hL : L.Pairwise Piece.Sep)
    (hg : gateP p r ∈ L) (hj : rfJP p r ∈ L) {δ k : ℤ} (hδ : δ = 4 ∨ δ = 5) {Tg : ℕ}
    (hTg : (Tg : ℤ) = 194 + 30 * k)
    (hgate : ∀ h ∈ L, h ≠ gateP p r → FarApart 2 (gateBox p r) h.box)
    (hfl1 : ∀ j : ℕ, 134 ≤ j → j < 871 → ∀ h ∈ L,
      FarApart 2 ((gateOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hrf : ∀ h ∈ L, h ≠ rfJP p r → FarApart 2 (relayBoxX (rfJCorner p r)) h.box)
    (hfl2 : ∀ j : ℕ, 931 ≤ j → j < 946 → ∀ h ∈ L,
      FarApart 2 ((rfJOutWL p r k).box ((Tg : ℤ) + j)) h.box) :
    Reaction (piecesAt L Tg ∪ ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg)
      (piecesAt L (Tg + 946) ∪ translate (modDX p r, modDY p r) (incInWL.cells 0)) 946
      (fun j => boxesOf L ∪ modFootW p r k Tg j) := by
  -- the gate
  have hg1 : Reaction
      (piecesAt [gateP p r] Tg ∪ ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg)
      (piecesAt [gateP p r] (Tg + 134) ∪ (gateOutWL p r k).cells ((Tg + 134 : ℕ) : ℤ)) 134
      (fun _ => gateBox p r) := by
    have h := incGate_reaction p r hδ Tg (by omega)
    rw [piecesAt_single, piecesAt_single, gateP,
      show ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg =
        translate (modDX p r - 1132, modDY p r - 1291) (sideIn δ) by
        rw [show (Tg : ℤ) = 194 + 30 * k from hTg]; exact module_side_arrival p r δ k hδ,
      show (gateOutWL p r k).cells ((Tg + 134 : ℕ) : ℤ) =
        translate (modDX p r - 1132 + 35, modDY p r - 1291 + 64) orIn by
        rw [gateOutWL, incGate_out p r k]; congr 1; push_cast; omega]
    exact h
  have w1 := window_mem hL (A := [gateP p r]) (by simpa using hg) Tg 134 hg1
    fun j _ h hh hne => hgate h hh (by simpa using hne)
  -- the flight to `RF_J`, until `20` generations before the meeting
  have hd1 : (gateOutWL p r k).Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have w2 := window hL (Tg + 134) 737 (WL.flight hd1 ((Tg + 134 : ℕ) : ℤ) 737) fun j hj h hh => by
    have := hfl1 (134 + j) (by omega) (by omega) h hh
    convert this using 2
    push_cast
    ring
  -- `RF_J`, with the early reflection
  have hm : ((Tg + 134 + 737 : ℕ) : ℤ) + 20 = meetT (gateOutWL p r k) (rfJCorner p r) := by
    rw [gateOutWL, rfJ_meet]; push_cast; omega
  have hr := reflect_earlyX_single (rfJ_onLine p r (1140 + 30 * k)) _ hm
  rw [rfJ_reflect p r (1140 + 30 * k) (by omega)] at hr
  have w3 := window_mem hL (A := [rfJP p r]) (by simpa using hj) _ 60 hr
    fun j _ h hh hne => hrf h hh (by simpa using hne)
  -- the flight to the increment
  have hd2 : (rfJOutWL p r k).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have w4 := window hL (Tg + 134 + 737 + 60) 15
      (WL.flight hd2 ((Tg + 134 + 737 + 60 : ℕ) : ℤ) 15) fun j hj h hh => by
    have := hfl2 (931 + j) (by omega) (by omega) h hh
    convert this using 2
    push_cast
    ring
  have e4 : (rfJOutWL p r k).cells (((Tg + 134 + 737 + 60 : ℕ) : ℤ) + ((15 : ℕ) : ℤ)) =
      translate (modDX p r, modDY p r) (incInWL.cells 0) := by
    rw [rfJOutWL, ← rfJ_to_dz2e p r k]
    congr 1
    push_cast
    omega
  rw [e4, show Tg + 134 + 737 + 60 + 15 = Tg + 946 by ring] at w4
  have w := ((w1.seq w2).seq w3).seq w4
  refine (w.castN (by norm_num)).mono fun j _ => ?_
  simp only [modFootW]
  by_cases h1 : j ≤ 134
  · simp only [h1, show j ≤ 134 + 737 by omega, show j ≤ 134 + 737 + 60 by omega, ↓reduceIte]
    exact le_rfl
  by_cases h2 : j ≤ 871
  · simp only [h1, h2, show j ≤ 134 + 737 + 60 by omega, ↓reduceIte]
    rw [show ((Tg + 134 : ℕ) : ℤ) + ((j - 134 : ℕ) : ℤ) = (Tg : ℤ) + j by
      push_cast [Nat.cast_sub (show 134 ≤ j by omega)]; ring]
  by_cases h3 : j ≤ 931
  · simp only [h1, h2, h3, ↓reduceIte]
    exact le_rfl
  · simp only [h1, h2, h3, ↓reduceIte]
    rw [show ((Tg + 134 + 737 + 60 : ℕ) : ℤ) + ((j - (134 + 737 + 60) : ℕ) : ℤ) = (Tg : ℤ) + j by
      push_cast [Nat.cast_sub (show 134 + 737 + 60 ≤ j by omega)]; ring]

/-- The footprint of the whole module part, with the `RF_J` window: before the increment
`modFootW` and the strip of the register; then the exact evolution of the increment. -/
def modRunFootW (p : Program) (r : ℕ) (L : List Piece) (k : ℤ) (Tg : ℕ) (R : RegS) (j : ℕ) :
    Set Cell :=
  if j ≤ 946 then boxesOf L ∪ modFootW p r k Tg j ∪ regStrip p r R (j + R.m)
  else boxesOf L ∪ (conway.evolve (j - 946) (incStart p r ∪ regAt p r (R.later 946)) : Set Cell)

/-- **The module part of the `inc` activation, with the `RF_J` window** (`module_run` with
`module_preW`): the merge link arriving on the INC window of
module `r` (offset `δ`, time `Tg = 194 + 30 k`), the pieces of `L` (containing the gate, `RF_J`
and the register circuit of the module) and the register diagonal become, `946 + d` generations
later, the pieces and the diagonal of the register holding one more. -/
theorem module_runW (p : Program) (r : ℕ) {L : List Piece} (hL : L.Pairwise Piece.Sep)
    (hg : gateP p r ∈ L) (hj : rfJP p r ∈ L) (hgrp : ∀ x ∈ modGroup p r, x ∈ L) {δ k : ℤ}
    (hδ : δ = 4 ∨ δ = 5) {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {R : RegS} (hR : R.Ready)
    (hgate : ∀ h ∈ L, h ≠ gateP p r → FarApart 2 (gateBox p r) h.box)
    (hfl1 : ∀ j : ℕ, 134 ≤ j → j < 871 → ∀ h ∈ L,
      FarApart 2 ((gateOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hrf : ∀ h ∈ L, h ≠ rfJP p r → FarApart 2 (relayBoxX (rfJCorner p r)) h.box)
    (hfl2 : ∀ j : ℕ, 931 ≤ j → j < 946 → ∀ h ∈ L,
      FarApart 2 ((rfJOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hstrip : ∀ j < 946, FarApart 2 (boxesOf L ∪ modFootW p r k Tg j) (regStrip p r R (j + R.m)))
    (hinc : ∀ i ≤ 7050, ∀ h ∈ L, h ∉ modGroup p r →
      FarApart 2 (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell) h.box) :
    ∃ (d : ℕ) (R' : RegS), 6990 ≤ d ∧ d ≤ 7050 ∧ R'.val = R.val + 1 ∧ R'.Ready ∧
      (∀ i ≤ d, (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell) ⊆
        (fun c => (modDX p r, modDY p r) + c) '' incRunBox) ∧
      Reaction (piecesAt L Tg ∪ (((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
          regAt p r R))
        (piecesAt L (Tg + 946 + d) ∪ regAt p r R') (946 + d) (modRunFootW p r L k Tg R) := by
  have hpre := (module_preW p r hL hg hj hδ hTg hgate hfl1 hrf hfl2).par
    (regAt_reaction p r hR.1 946) hstrip
  obtain ⟨d, R', h1, h2, h3, h4, hev, hsub⟩ := regInc_module p r (hR.later 946)
  have hT1 : (Tg + 946) % 30 = 0 := by omega
  have hinc' : Reaction (piecesAt (modGroup p r) (Tg + 946) ∪
        (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)))
      (piecesAt (modGroup p r) (Tg + 946 + d) ∪ regAt p r R') d
      (fun i => (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell)) := by
    have e1 : piecesAt (modGroup p r) (Tg + 946) ∪
        (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)) =
        incStart p r ∪ regAt p r (R.later 946) := by
      rw [modGroup_at, hT1, Rule.evolve_zero, incStart, translate_union, union_assoc]
    have e2 : piecesAt (modGroup p r) (Tg + 946 + d) =
        translate (modDX p r, modDY p r) (conway.evolve (d - 6990) dz2gRest) := by
      rw [modGroup_at, dz2gRest_mod (d - 6990),
        show (Tg + 946 + d) % 30 = (d - 6990) % 30 by omega]
    rw [e1, e2]
    exact Reaction.exact hev
  have w := window_mem hL hgrp (Tg + 946) d hinc' fun i hi h hh hne => hinc i (by omega) h hh hne
  refine ⟨d, R', h1, h2, h3, h4, hsub, ?_⟩
  have e3 : piecesAt L Tg ∪ ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
      regAt p r R = piecesAt L Tg ∪ (((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
        regAt p r R) := union_assoc _ _ _
  have e4 : piecesAt L (Tg + 946) ∪ translate (modDX p r, modDY p r) (incInWL.cells 0) ∪
      regAt p r (R.later 946) = piecesAt L (Tg + 946) ∪
        (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)) :=
    union_assoc _ _ _
  rw [e3, e4] at hpre
  refine (hpre.seq w).mono fun j _ => ?_
  simp only [modRunFootW]
  split_ifs <;> exact le_rfl

/-- **The module part of the `inc` activation, with the `RF_J` window, for any duration
`n ≥ 7050` of the increment window**: as `module_runW`, followed by the circuit and the register
idling; the footprint is `modRunFootW` (the exact evolution after the input of the
increment). -/
theorem module_run_nW (p : Program) (r : ℕ) {L : List Piece} (hL : L.Pairwise Piece.Sep)
    (hg : gateP p r ∈ L) (hj : rfJP p r ∈ L) (hgrp : ∀ x ∈ modGroup p r, x ∈ L) {δ k : ℤ}
    (hδ : δ = 4 ∨ δ = 5) {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {R : RegS} (hR : R.Ready)
    (hgate : ∀ h ∈ L, h ≠ gateP p r → FarApart 2 (gateBox p r) h.box)
    (hfl1 : ∀ j : ℕ, 134 ≤ j → j < 871 → ∀ h ∈ L,
      FarApart 2 ((gateOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hrf : ∀ h ∈ L, h ≠ rfJP p r → FarApart 2 (relayBoxX (rfJCorner p r)) h.box)
    (hfl2 : ∀ j : ℕ, 931 ≤ j → j < 946 → ∀ h ∈ L,
      FarApart 2 ((rfJOutWL p r k).box ((Tg : ℤ) + j)) h.box)
    (hstrip : ∀ j < 946, FarApart 2 (boxesOf L ∪ modFootW p r k Tg j) (modLanes p r))
    (hlanes : FarApart 2 (boxesOf (modGroup p r)) (modLanes p r)) (n : ℕ) (hn : 7050 ≤ n)
    (hinc : ∀ i ≤ n, ∀ h ∈ L, h ∉ modGroup p r →
      FarApart 2 (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell) h.box) :
    ∃ R' : RegS, R'.val = R.val + 1 ∧ R'.Ready ∧
      (∀ i ≤ n, (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell) ⊆
        ((fun c => (modDX p r, modDY p r) + c) '' incRunBox ∪ boxesOf (modGroup p r)) ∪
          modLanes p r) ∧
      Reaction (piecesAt L Tg ∪ (((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
          regAt p r R))
        (piecesAt L (Tg + 946 + n) ∪ regAt p r R') (946 + n) (modRunFootW p r L k Tg R) := by
  have hpre := (module_preW p r hL hg hj hδ hTg hgate hfl1 hrf hfl2).par
    (regAt_reaction p r hR.1 946) fun j hj =>
      (hstrip j hj).mono le_rfl (regStrip_subset hR.1 p r j)
  obtain ⟨d, R', h1, h2, h3, h4, hev, hsub⟩ := regInc_module p r (hR.later 946)
  have hT1 : (Tg + 946) % 30 = 0 := by omega
  have hb := (bundleAt (modGroup p r) (modGroup_sep p r) (Tg + 946 + d) (n - d)).reaction
  rw [bundleAt_P, bundleAt_Q] at hb
  have hpar := (hb.mono fun i _ => (bundleAt_F _ _ _ _ i).le).par (regAt_reaction p r h4.1 (n - d))
    fun i _ => hlanes.mono le_rfl (regStrip_subset h4.1 p r i)
  have e1 : piecesAt (modGroup p r) (Tg + 946) ∪
      (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)) =
      incStart p r ∪ regAt p r (R.later 946) := by
    rw [modGroup_at, hT1, Rule.evolve_zero, incStart, translate_union, union_assoc]
  have e2 : piecesAt (modGroup p r) (Tg + 946 + d) =
      translate (modDX p r, modDY p r) (conway.evolve (d - 6990) dz2gRest) := by
    rw [modGroup_at, dz2gRest_mod (d - 6990),
      show (Tg + 946 + d) % 30 = (d - 6990) % 30 by omega]
  have htot : conway.evolve n (incStart p r ∪ regAt p r (R.later 946)) =
      piecesAt (modGroup p r) (Tg + 946 + n) ∪ regAt p r (R'.later (n - d)) := by
    have hsplit : conway.evolve n (incStart p r ∪ regAt p r (R.later 946)) =
        conway.evolve (n - d) (conway.evolve d (incStart p r ∪ regAt p r (R.later 946))) := by
      rw [← Rule.evolve_add]
      congr 1
      omega
    rw [hsplit, incStart, hev, ← e2, hpar.evolve_eq,
      show Tg + 946 + d + (n - d) = Tg + 946 + n by omega]
  have hinc' : Reaction (piecesAt (modGroup p r) (Tg + 946) ∪
        (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)))
      (piecesAt (modGroup p r) (Tg + 946 + n) ∪ regAt p r (R'.later (n - d))) n
      (fun i => (conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) : Set Cell)) := by
    rw [e1]
    exact Reaction.exact htot
  have w := window_mem hL hgrp (Tg + 946) n hinc' fun i hi h hh hne => hinc i (by omega) h hh hne
  refine ⟨R'.later (n - d), by simp [h3], h4.later _, fun i hi => ?_, ?_⟩
  · by_cases hid : i ≤ d
    · exact (hsub i hid).trans (Set.subset_union_left.trans Set.subset_union_left)
    · have e : conway.evolve i (incStart p r ∪ regAt p r (R.later 946)) =
          conway.evolve (i - d) (piecesAt (modGroup p r) (Tg + 946 + d) ∪ regAt p r R') := by
        rw [e2, show i = (i - d) + d by omega, Rule.evolve_add, incStart, hev,
          show i - d + d - d = i - d by omega]
      rw [e]
      refine (hpar.subset (i - d) (by omega)).trans (Set.union_subset_union ?_ ?_)
      · exact Set.subset_union_right
      · exact regStrip_subset h4.1 p r _
  · have e3 : piecesAt L Tg ∪ ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
        regAt p r R = piecesAt L Tg ∪ (((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells Tg ∪
          regAt p r R) := union_assoc _ _ _
    have e4 : piecesAt L (Tg + 946) ∪ translate (modDX p r, modDY p r) (incInWL.cells 0) ∪
        regAt p r (R.later 946) = piecesAt L (Tg + 946) ∪
          (translate (modDX p r, modDY p r) (incInWL.cells 0) ∪ regAt p r (R.later 946)) :=
      union_assoc _ _ _
    rw [e3, e4] at hpre
    refine (hpre.seq w).mono fun j _ => ?_
    simp only [modRunFootW]
    split_ifs <;> exact le_rfl

end LP

end LeanTheory.Life
