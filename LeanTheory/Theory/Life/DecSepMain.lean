/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepProof2
public import LeanTheory.Theory.Life.ActivationDecStep
public import LeanTheory.Theory.Life.MainTheorem

/-!
# `DecSep` from its remaining fields, and the `dec` field of `MachineSteps`

Research note `N-22`. Of the `54` fields of `DecSep` (`ActivationDecStepThread`), `17` are proved
for every `decJz` instruction of a well-formed program (`DecSepProof`, `DecSepProof2`):
`sepC`, `sepN`, `sepZ`, `sepAN`, `sepAZ` (routes), `grpLane`, `lanes`, `laneBody`, `nQ1a`, `zQ1a`
(lanes), `flyAN`, `flyAZ`, `entAN`, `entAZ`, `outAN`, `outAZ` (the ends of the answer links) and
`body`. The other `37` are collected in `DecSepRest`; all `54` were checked numerically on `14`
activations of five test programs (`D` up to `5`, callers `j` up to `4`).

* `dsep_decSep_of_rest`: `DecSepRest p i r z → DecSep p i r z`;
* `dsep_machineSteps_dec`: the field `dec` of `MachineSteps` from `DecSepRest` for every
  `decJz` instruction.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- **The fields of `DecSep` not yet proved generically** (the same statements as in
`DecSep`). -/
structure DecSepRest (p : Program) (i r z : ℕ) : Prop where
  /-- The flight of `C` until `20` generations before the side input of DEC copy `m`. -/
  flyC : ∀ t : ℕ, routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ≤ t →
    t < decTA p i r - 20 → ∀ h ∈ decLC p i r, FarApart 2 ((decGC p i r).box t) h.box
  /-- The joint approach of `C` and DEC copy `m`. -/
  sideC : ∀ h ∈ decLC p i r, h ≠ decCopyM p i r → FarApart 2 (decSideBoxC p i r) h.box
  /-- The DEC chain. -/
  chainC : ∀ h ∈ decLC p i r, h ∉ decChainP p i r → FarApart 2 (decChainFoot p i r) h.box
  /-- The flight of `C'` to the register run. -/
  cpC : ∀ t : ℕ, decTB p i r ≤ t → t < decTS p i r → ∀ h ∈ decLC p i r,
    FarApart 2 (decCpFoot p i r t) h.box
  /-- The flight of `KNZ` until `90` generations before the capture position. -/
  flyN : ∀ t : ℕ, routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ≤ t →
    t < decCapN p i r - 90 → ∀ h ∈ decLNu p i r, FarApart 2 ((decTokN p i r).box t) h.box
  /-- The joint approach of `KNZ` and its station. -/
  winN : ∀ k < 90, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decTokWStartN p i r) : Set Cell) h.box
  /-- The flight of `KZ` until `90` generations before the capture position. -/
  flyZ : ∀ t : ℕ, routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 ≤ t →
    t < decCapZ p i r - 90 → ∀ h ∈ decLZu p i r, FarApart 2 ((decTokZ p i r).box t) h.box
  /-- The joint approach of `KZ` and its station. -/
  winZ : ∀ k < 90, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decTokWStartZ p i r) : Set Cell) h.box
  /-- (NZ) The absorption of the unpaired `KZ`. -/
  unpZ : ∀ k < 272, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decUnpStartZ p i r) : Set Cell) h.box
  /-- (NZ) The answer's flight from the cut to station `0`. -/
  ansFlyN : ∀ t : ℕ, decCutN p i r ≤ t → t < decSt0N p i r → ∀ h ∈ decLSN p i r,
    FarApart 2 ((decAnsWLN p i r).box t) h.box
  /-- (NZ) The capture at station `j`. -/
  capN : ∀ k < 692, ∀ h ∈ decLFN p i r, h ∉ stNZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decCapStartN p i r) : Set Cell) h.box
  /-- (NZ) The control and the lanes against the circuit and the stations. -/
  nQ1b : ∀ t : ℕ, 4260 ≤ t → t < decTS p i r → ∀ g ∈ modGroup p r ++ decLSN p i r,
    FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r) g.box
  /-- (NZ) The run against the control's pieces and the stations. -/
  nQ2 : ∀ g ∈ decLC p i r ++ decLSN p i r, FarApart 2 (modImg p r decRunRegNZ) g.box
  /-- (NZ) The rest of the run against the answer. -/
  nQ3a : ∀ t : ℕ, decCutN p i r ≤ t → t < decCapN p i r →
    FarApart 2 (restFootN p i r t) (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t)
  /-- (NZ) The rest of the run and the answer against the control's pieces. -/
  nQ3b : ∀ t : ℕ, decCutN p i r ≤ t → t < decCapN p i r → ∀ g ∈ decLC p i r,
    FarApart 2 (restFootN p i r t ∪ (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t)) g.box
  /-- (NZ) The control, the run and the answer against `KNZ`. -/
  nQN : ∀ t : ℕ, 4260 ≤ t → t < decCapN p i r →
    FarApart 2 (qFootN p i r t) (boxesOf (decLNu p i r) ∪ tokFootN p i r t)
  /-- (NZ) Before the capture, against the pieces of the answer link. -/
  nQF : ∀ t : ℕ, 4260 ≤ t → t < decCapN p i r → ∀ g ∈ decLF0N p i r,
    FarApart 2 (qFootN p i r t ∪ (boxesOf (decLNu p i r) ∪ tokFootN p i r t)) g.box
  /-- (NZ) The rest of the run against the end. -/
  nA2a : ∀ t : ℕ, decCapN p i r ≤ t → t < decEndN p i r →
    FarApart 2 (restFootN p i r t) (boxesOf (decLFN p i r) ∪ finFootN p i r t)
  /-- (NZ) The end against the pieces of the control, the stations and `KNZ`. -/
  nA2b : ∀ t : ℕ, decCapN p i r ≤ t → t < decEndN p i r →
    ∀ g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r,
    FarApart 2 (restFootN p i r t ∪ (boxesOf (decLFN p i r) ∪ finFootN p i r t)) g.box
  /-- (NZ) The main thread against the unpaired `KZ`. -/
  nThr : ∀ t : ℕ, 4260 ≤ t → t < decEndN p i r →
    FarApart 2 (footMN p i r t) (boxesOf (decLZu p i r) ∪ unpFootZ p i r t)
  /-- (NZ) The threads against every idle piece. -/
  nIdle : ∀ t : ℕ, 4260 ≤ t → t < decEndN p i r → ∀ g ∈ machPieces p,
    g ∉ decLMN p i r ++ decLZu p i r →
    FarApart 2 (footMN p i r t ∪ (boxesOf (decLZu p i r) ∪ unpFootZ p i r t)) g.box
  /-- (NZ) The machine and the threads against the lanes of the other registers. -/
  nLane : ∀ t : ℕ, 4260 ≤ t → t < decEndN p i r → ∀ r' < numRegs p, r' ≠ r →
    FarApart 2 (boxesOf (machPieces p) ∪ (footMN p i r t ∪ (boxesOf (decLZu p i r) ∪
      unpFootZ p i r t))) (modLanes p r')
  /-- (Z) The absorption of the unpaired `KNZ`. -/
  unpN : ∀ k < 292, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decUnpStartN p i r) : Set Cell) h.box
  /-- (Z) The answer's flight from the cut to station `0`. -/
  ansFlyZ : ∀ t : ℕ, decCutZ p i r ≤ t → t < decSt0Z p i r → ∀ h ∈ decLSZ p i r,
    FarApart 2 ((decAnsWLZ p i r).box t) h.box
  /-- (Z) The capture at station `j`. -/
  capZ : ∀ k < 672, ∀ h ∈ decLFZ p i r z, h ∉ stZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decCapStartZ p i r) : Set Cell) h.box
  /-- (Z) The control and the lanes against the circuit and the stations. -/
  zQ1b : ∀ t : ℕ, 4260 ≤ t → t < decTS p i r → ∀ g ∈ modGroup p r ++ decLSZ p i r,
    FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r) g.box
  /-- (Z) The run against the control's pieces and the stations. -/
  zQ2 : ∀ g ∈ decLC p i r ++ decLSZ p i r, FarApart 2 (modImg p r decRunRegZ) g.box
  /-- (Z) The rest of the run against the answer. -/
  zQ3a : ∀ t : ℕ, decCutZ p i r ≤ t → t < decCapZ p i r →
    FarApart 2 (restFootZ p i r t) (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t)
  /-- (Z) The rest of the run and the answer against the control's pieces. -/
  zQ3b : ∀ t : ℕ, decCutZ p i r ≤ t → t < decCapZ p i r → ∀ g ∈ decLC p i r,
    FarApart 2 (restFootZ p i r t ∪ (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t)) g.box
  /-- (Z) The control, the run and the answer against `KZ`. -/
  zQZ : ∀ t : ℕ, 4260 ≤ t → t < decCapZ p i r →
    FarApart 2 (qFootZ p i r t) (boxesOf (decLZu p i r) ∪ tokFootZ p i r t)
  /-- (Z) Before the capture, against the pieces of the answer link. -/
  zQF : ∀ t : ℕ, 4260 ≤ t → t < decCapZ p i r → ∀ g ∈ decLF0Z p i r z,
    FarApart 2 (qFootZ p i r t ∪ (boxesOf (decLZu p i r) ∪ tokFootZ p i r t)) g.box
  /-- (Z) The rest of the run against the end. -/
  zA2a : ∀ t : ℕ, decCapZ p i r ≤ t → t < decEndZ p i r z →
    FarApart 2 (restFootZ p i r t) (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t)
  /-- (Z) The end against the pieces of the control, the stations and `KZ`. -/
  zA2b : ∀ t : ℕ, decCapZ p i r ≤ t → t < decEndZ p i r z →
    ∀ g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r,
    FarApart 2 (restFootZ p i r t ∪ (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t)) g.box
  /-- (Z) The main thread against the unpaired `KNZ`. -/
  zThr : ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z →
    FarApart 2 (footMZ p i r z t) (boxesOf (decLNu p i r) ∪ unpFootN p i r t)
  /-- (Z) The threads against the INC gate of the module (with its tight footprint). -/
  zGate : ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z →
    FarApart 2 (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪ unpFootN p i r t)) (gateFoot p r)
  /-- (Z) The threads and the INC gate against every idle piece. -/
  zIdle : ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z → ∀ g ∈ machPieces p,
    g ∉ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] →
    FarApart 2 (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪ unpFootN p i r t) ∪ gateFoot p r)
      g.box
  /-- (Z) The machine and the threads against the lanes of the other registers. -/
  zLane : ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z → ∀ r' < numRegs p, r' ≠ r →
    FarApart 2 (boxesOf (machPieces p) ∪ (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪
      unpFootN p i r t) ∪ gateFoot p r)) (modLanes p r')

variable {p : Program} {i r z : ℕ}

/-- **`DecSep` from its remaining fields** for every `decJz` instruction of a well-formed
program. -/
theorem dsep_decSep_of_rest (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z))
    (hs : DecSepRest p i r z) : DecSep p i r z :=
    { sepC := dsep_sepC hp hi
      flyC := hs.flyC
      sideC := hs.sideC
      chainC := hs.chainC
      cpC := hs.cpC
      sepN := dsep_sepN hp hi
      flyN := hs.flyN
      winN := hs.winN
      sepZ := dsep_sepZ hp hi
      flyZ := hs.flyZ
      winZ := hs.winZ
      grpLane := dsep_grpLane p r
      body := dsep_body hp hi
      lanes := dsep_lanes p
      laneBody := dsep_laneBody hp i
      unpZ := hs.unpZ
      ansFlyN := hs.ansFlyN
      capN := hs.capN
      sepAN := dsep_sepAN hp hi
      flyAN := fun t h1 h2 h hh => dsep_flyAN hp hi t h1 h2 h (decLFN_mem hp hi h hh)
      entAN := fun h hh hn => dsep_entAN hp hi h (decLFN_mem hp hi h hh) hn
      outAN := fun t ht h hh => dsep_outAN hp t ht h (decLFN_mem hp hi h hh)
      nQ1a := dsep_nQ1a hp hi
      nQ1b := hs.nQ1b
      nQ2 := hs.nQ2
      nQ3a := hs.nQ3a
      nQ3b := hs.nQ3b
      nQN := hs.nQN
      nQF := hs.nQF
      nA2a := hs.nA2a
      nA2b := hs.nA2b
      nThr := hs.nThr
      nIdle := hs.nIdle
      nLane := hs.nLane
      unpN := hs.unpN
      ansFlyZ := hs.ansFlyZ
      capZ := hs.capZ
      sepAZ := dsep_sepAZ hp hi
      flyAZ := fun t h1 h2 h hh => dsep_flyAZ hp hi t h1 h2 h (decLFZ_mem hp hi h hh)
      entAZ := fun h hh hn => dsep_entAZ hp hi h (decLFZ_mem hp hi h hh) hn
      outAZ := fun t ht h hh => dsep_outAZ hp t ht h (decLFZ_mem hp hi h hh)
      zQ1a := dsep_nQ1a hp hi
      zQ1b := hs.zQ1b
      zQ2 := hs.zQ2
      zQ3a := hs.zQ3a
      zQ3b := hs.zQ3b
      zQZ := hs.zQZ
      zQF := hs.zQF
      zA2a := hs.zA2a
      zA2b := hs.zA2b
      zThr := hs.zThr
      zGate := hs.zGate
      zIdle := hs.zIdle
      zLane := hs.zLane }

/-- **The field `dec` of `MachineSteps`** from the remaining fields of `DecSep` at every `decJz`
instruction. -/
theorem dsep_machineSteps_dec (hp : p.WellFormed)
    (hrest : ∀ i r z : ℕ, p[i]? = some (.decJz r z) → DecSepRest p i r z) :
    ∀ (s : MState) (r z : ℕ), MInv p s → p[s.pc]? = some (.decJz r z) →
      ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ p.step s.cfg = some s'.cfg ∧ MInv p s' ∧
        conway.evolve τ (encM p s) = encM p s' ∧
        ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p :=
  decJz_step' hp fun _ r z _ hins => dsep_decSep_of_rest hp hins (hrest _ r z hins)

end LP

end LeanTheory.Life
