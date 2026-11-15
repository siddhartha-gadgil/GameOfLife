/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecStepThread

/-!
# The former `DecSep` was unsatisfiable: the INC gate and the region of the zero-test run

Research note `N-22`. **Documentation of a corrected defect** of the former separation structure
`DecSep` (`ActivationDecStepThread`, before the reformulation of 2026-11-16). For a `Z`
activation (register value `0`) the footprint of the register run before the cut is the region
`dz2mk0Region` of the **whole** run `dz2mk0`
(`Gen/Dz2mk0RunG`), placed at the module. Its component number `111`,

  `BU (-1182) (-965) (-1335) (-1117) (-65) 370 (-2302) (-2297)`

(module frame), is the hull of the boxes of a glider of the zero-test run flying `SW` along
`x + y ∈ [-2302, -2297]` (segments `60` to `64` of `dz2mk0`, generations `18068` to `19460`).
It contains the cell `(-1042, -1260)`, which is also a cell of the box `[-1132, -1042] ×
[-1291, -1259]` of the **INC OR gate** of the module (`incGateSpec`, `gateP`). The same component
is also number `78` of the rest region `dz2mk0RestRegion`, so the defect is not removed by the cut.

The INC gate is an idle piece of the `Z` activation, so the field `zIdle` asks the footprint of
the activation (at `decTS + 1`, inside the run) to be far from the box of the gate: false. If the
gate were one of the active pieces, the fields `zQ2`, `zQZ`, `zQF`, `zThr` would fail in the same
way, and it is not one of the circuit groups (`moduleSpecs_sep`). Hence the former `DecSep` was
false for every well-formed program and every instruction `decJz r z` (the key fact is kept as
`dsep_old_region_gate`).

Physically the glider is harmless: over all `30` phases the cells of the OR gate stay at
Chebyshev distance `≥ 12` from the glider boxes (the gate has no cell with `x ≥ 60` and `y ≥ 20`
in its frame, and the glider passes the corner `(90, 32)` of its box). The repair (now in
`DecSep`): the INC gate runs in the `Z` thread with the tight footprint `gateFoot`
(`Box 0 90 0 19 ∪ Box 0 59 0 32`, gate
frame, `Gen/OrGateTight`), and the run before the cut uses the prefix region `decRunRegZ`.

The numerical check of all fields (probe of the Lean definitions on the test programs
`[decJz 0 1, halt]`, `add`, `share`, `rand` and a program with five callers of one register)
found further false fields. Three are caused by using the region of the whole run before the cut
(it contains the answer's whole flight): `zQZ` (the answer line `x + y ∈ [535, 541]` of `dz2mk0`,
component `182`, against the token `KZ` on its route leg parallel to it), `zLane` (the same
flight against the lanes of the next register, when there is one) and, when `D p = 1`, `nIdle`
(the line-end eater NZ at `(563, 954)` lies on the answer line `x - y ∈ [-393, -390]` of the NZ
run regions, which reach `x + y = 1600`); the prefix regions `Gen/*PreG` repair them. Two more
started too early: `sepAN` and `sepAZ`, whose first flight clause failed at the dispatch time
itself (the answer still overlapped the reflector of its station for `96`, resp. `94`
generations); the captures now run `200` generations longer (`stationNZ_captureE`,
`stationZ_captureE`, `Gen/CapExt`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- The witness cell of the defect, in the module frame. -/
def dsepCell : Cell := (-1042, -1260)

set_option maxRecDepth 100000 in
/-- The component `111` of the region of the whole zero-test run `dz2mk0`. -/
theorem dsep_comp_mem :
    BU (-1182) (-965) (-1335) (-1117) (-65) 370 (-2302) (-2297) ∈ dz2mk0RegL := by
  simp [dz2mk0RegL]

/-- The witness cell lies in the region of the whole zero-test run. -/
theorem dsep_cell_region : dsepCell ∈ dz2mk0Region :=
  mem_unionL dsep_comp_mem (by
    simp only [BU, dsepCell, Box, UVBox, Set.mem_inter_iff, Set.mem_ofPred_eq]
    omega)

/-- The witness cell, placed at module `r`, lies in the placed region of the run. -/
theorem dsep_cell_modImg (p : Program) (r : ℕ) :
    (modDX p r - 1042, modDY p r - 1260) ∈ modImg p r dz2mk0Region :=
  ⟨dsepCell, dsep_cell_region, by simp only [dsepCell, Prod.mk_add_mk]; ext <;> simp <;> ring⟩

/-- The witness cell, placed at module `r`, lies in the box of the INC OR gate. -/
theorem dsep_cell_gate (p : Program) (r : ℕ) :
    (modDX p r - 1042, modDY p r - 1260) ∈ (gateP p r).box := by
  simp only [gateP, incGateSpec, PSpec.piece, Piece.place, Piece.box, Box, Base.piece, orGateP,
    Set.mem_ofPred_eq]
  omega

/-- A set containing the witness cell is not far from the box of the INC gate. -/
theorem dsep_not_far (p : Program) (r : ℕ) {A : Set Cell}
    (hA : (modDX p r - 1042, modDY p r - 1260) ∈ A) : ¬ FarApart 2 A (gateP p r).box :=
  fun h => h _ hA _ (dsep_cell_gate p r) (by simp only [Near]; omega)

/-- Two sets sharing a cell are not far apart. -/
theorem dsep_far_contra {A B : Set Cell} {c : Cell} (h : FarApart 2 A B) (ha : c ∈ A)
    (hb : c ∈ B) : False :=
  h c ha c hb (by simp only [Near]; omega)

/-- The witness cell lies in the boxes of a list containing the INC gate. -/
theorem dsep_cell_boxesOf (p : Program) (r : ℕ) {L : List Piece} (h : gateP p r ∈ L) :
    (modDX p r - 1042, modDY p r - 1260) ∈ boxesOf L :=
  mem_boxesOf.2 ⟨gateP p r, h, dsep_cell_gate p r⟩

/-- A set containing the witness cell is not far from the boxes of a list containing the INC gate
(together with any set `S`). -/
theorem dsep_far_boxes {p : Program} {r : ℕ} {A S : Set Cell} {L : List Piece}
    (h : FarApart 2 A (boxesOf L ∪ S)) (hA : (modDX p r - 1042, modDY p r - 1260) ∈ A)
    (hg : gateP p r ∈ L) : False :=
  dsep_far_contra h hA (Or.inl (dsep_cell_boxesOf p r hg))

/-- The INC gate of a module is a piece of the machine. -/
theorem dsep_gate_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    gateP p r ∈ machPieces p :=
  decModule_mem (lt_numRegs_of_dec hi) (by simp [moduleSpecs, incGateSpec])

/-- The INC gate is not one of the groups of the register circuit. -/
theorem dsep_gate_not_group (p : Program) (r : ℕ) : gateP p r ∉ modGroup p r := by
  intro hg
  obtain ⟨s, hs, hsg⟩ := List.mem_map.1 hg
  have h := moduleSpecs_sep p r
  simp only [moduleSpecs, List.pairwise_append, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at h
  have hsep : Piece.Sep s.piece (incGateSpec p r).piece :=
    h.1.1.1.1.2.2 s hs _ (by simp [incGateSpec])
  rw [hsg] at hsep
  exact dsep_not_far p r (dsep_cell_gate p r) hsep

/-- **The former footprint of the zero-test run meets the box of the INC gate**: the region of the
whole run `dz2mk0` (used before the cut by the former `DecSep`), placed at module `r`, is not far
from the box of the INC OR gate. This made the former field `zIdle` false for every `decJz`
instruction; `DecSep` now uses the prefix region `decRunRegZ` before the cut and runs the gate in
the `Z` thread with its tight footprint `gateFoot` (`zGate`). -/
theorem dsep_old_region_gate (p : Program) (r : ℕ) :
    ¬ FarApart 2 (modImg p r dz2mk0Region) (gateP p r).box :=
  dsep_not_far p r (dsep_cell_modImg p r)

end LP

end LeanTheory.Life
