/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncReg
public import LeanTheory.Theory.Life.ActivationDecRun
public import LeanTheory.Theory.Life.Gen.Dz2dSplit
public import LeanTheory.Theory.Life.Gen.Dz2d1Split
public import LeanTheory.Theory.Life.Gen.Dz2d2Split
public import LeanTheory.Theory.Life.Gen.Dz2d3Split
public import LeanTheory.Theory.Life.Gen.Dz2mk0Split
public import LeanTheory.Theory.Life.Gen.Dz2mk1Split
public import LeanTheory.Theory.Life.Gen.Dz2mk2Split
public import LeanTheory.Theory.Life.Gen.Dz2mk3Split
public import LeanTheory.Theory.Life.Gen.Dz2mk4Split
public import LeanTheory.Theory.Life.Gen.Dz2mk5Split
public import LeanTheory.Theory.Life.Gen.Dz2mk6Split
public import LeanTheory.Theory.Life.Gen.Dz2mk7Split
public import LeanTheory.Theory.Life.Gen.DecPreOps


/-!
# The register runs of a `decJz` activation, for every register value

Research note `N-22`, the register end of the `decJz` activation at module `r`: from the input
`C'` of the run (`ofRows (-1186) (-1227) [2, 4, 7]`, module frame), the register circuit at rest
`dz2gRest` and the register diagonal, the register run releases its answer at the cut and the
circuit finishes alone (`Gen/*Split.lean`).

* **One circuit** (`dz2dRest_eq_g`, …, `dz2mk7Rest_eq_g`): every run acts on `dz2gRest`.
* **Value `≥ 8`** (`RegS.pull_dichotomy`): the pull of the phase `R.m mod 4` (`dz2dOpS` …
  `dz2d3OpS` with `dz2d_join` … `dz2d3_join`), the register afterwards `RegS.pullAt` (ready,
  value one less, `RegS.pullAt_ready`).
* **Value `1 … 7`**: the register is the static block (`diagW_static`), the run is `dz2mk1` …
  `dz2mk7` (`regNZ_static`), the register afterwards `RegS.block (w - 1)`.
* **Value `0`**: the zero test `dz2mk0`; the register is unchanged (`regZ_frame`: the block `0`
  before and after, `R.later 27540`).
* `regNZ_frame`, `regZ_frame`, `regNZ_module`, `regZ_module`: the NZ answer on `ansNZWL` at
  `9203`, the Z answer on `ansZWL` at `11695` (clock of `cp0WL`); footprints `decRunRegNZ`,
  `decRestRegNZ`, `decRunRegZ`, `dz2mk0RestRegion`, all at `u ≥ -738` in the module frame
  (`decRunRegNZ_u`, …).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2d` is `dz2gRest`. -/
theorem dz2dRest_eq_g : dz2dRest = dz2gRest := by
  simp only [dz2dRest, dz2gRest, show dz2dR0 = dz2gR0 from rfl, show dz2dR1 = dz2gR1 from rfl,
    show dz2dR2 = dz2gR2 from rfl, show dz2dR3 = dz2gR3 from rfl, show dz2dR4 = dz2gR4 from rfl,
    show dz2dR5 = dz2gR5 from rfl, show dz2dR6 = dz2gR6 from rfl, show dz2dR7 = dz2gR7 from rfl,
    show dz2dR8 = dz2gR8 from rfl, show dz2dR9 = dz2gR9 from rfl, show dz2dR10 = dz2gR10 from rfl,
    show dz2dR11 = dz2gR11 from rfl, show dz2dR12 = dz2gR12 from rfl,
    show dz2dR13 = dz2gR13 from rfl, show dz2dR14 = dz2gR14 from rfl,
    show dz2dR15 = dz2gR15 from rfl, show dz2dR16 = dz2gR16 from rfl,
    show dz2dR17 = dz2gR17 from rfl, show dz2dR18 = dz2gR18 from rfl,
    show dz2dR19 = dz2gR19 from rfl, show dz2dR20 = dz2gR20 from rfl,
    show dz2dR21 = dz2gR21 from rfl, show dz2dR22 = dz2gR22 from rfl,
    show dz2dR23 = dz2gR23 from rfl, show dz2dR24 = dz2gR24 from rfl,
    show dz2dR25 = dz2gR25 from rfl, show dz2dR26 = dz2gR26 from rfl,
    show dz2dR27 = dz2gR27 from rfl]

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2d1` is `dz2gRest`. -/
theorem dz2d1Rest_eq_g : dz2d1Rest = dz2gRest := by
  simp only [dz2d1Rest, dz2gRest, show dz2d1R0 = dz2gR0 from rfl, show dz2d1R1 = dz2gR1 from rfl,
    show dz2d1R2 = dz2gR2 from rfl, show dz2d1R3 = dz2gR3 from rfl, show dz2d1R4 = dz2gR4 from rfl,
    show dz2d1R5 = dz2gR5 from rfl, show dz2d1R6 = dz2gR6 from rfl, show dz2d1R7 = dz2gR7 from rfl,
    show dz2d1R8 = dz2gR8 from rfl, show dz2d1R9 = dz2gR9 from rfl,
    show dz2d1R10 = dz2gR10 from rfl, show dz2d1R11 = dz2gR11 from rfl,
    show dz2d1R12 = dz2gR12 from rfl, show dz2d1R13 = dz2gR13 from rfl,
    show dz2d1R14 = dz2gR14 from rfl, show dz2d1R15 = dz2gR15 from rfl,
    show dz2d1R16 = dz2gR16 from rfl, show dz2d1R17 = dz2gR17 from rfl,
    show dz2d1R18 = dz2gR18 from rfl, show dz2d1R19 = dz2gR19 from rfl,
    show dz2d1R20 = dz2gR20 from rfl, show dz2d1R21 = dz2gR21 from rfl,
    show dz2d1R22 = dz2gR22 from rfl, show dz2d1R23 = dz2gR23 from rfl,
    show dz2d1R24 = dz2gR24 from rfl, show dz2d1R25 = dz2gR25 from rfl,
    show dz2d1R26 = dz2gR26 from rfl, show dz2d1R27 = dz2gR27 from rfl]

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2d2` is `dz2gRest`. -/
theorem dz2d2Rest_eq_g : dz2d2Rest = dz2gRest := by
  simp only [dz2d2Rest, dz2gRest, show dz2d2R0 = dz2gR0 from rfl, show dz2d2R1 = dz2gR1 from rfl,
    show dz2d2R2 = dz2gR2 from rfl, show dz2d2R3 = dz2gR3 from rfl, show dz2d2R4 = dz2gR4 from rfl,
    show dz2d2R5 = dz2gR5 from rfl, show dz2d2R6 = dz2gR6 from rfl, show dz2d2R7 = dz2gR7 from rfl,
    show dz2d2R8 = dz2gR8 from rfl, show dz2d2R9 = dz2gR9 from rfl,
    show dz2d2R10 = dz2gR10 from rfl, show dz2d2R11 = dz2gR11 from rfl,
    show dz2d2R12 = dz2gR12 from rfl, show dz2d2R13 = dz2gR13 from rfl,
    show dz2d2R14 = dz2gR14 from rfl, show dz2d2R15 = dz2gR15 from rfl,
    show dz2d2R16 = dz2gR16 from rfl, show dz2d2R17 = dz2gR17 from rfl,
    show dz2d2R18 = dz2gR18 from rfl, show dz2d2R19 = dz2gR19 from rfl,
    show dz2d2R20 = dz2gR20 from rfl, show dz2d2R21 = dz2gR21 from rfl,
    show dz2d2R22 = dz2gR22 from rfl, show dz2d2R23 = dz2gR23 from rfl,
    show dz2d2R24 = dz2gR24 from rfl, show dz2d2R25 = dz2gR25 from rfl,
    show dz2d2R26 = dz2gR26 from rfl, show dz2d2R27 = dz2gR27 from rfl]

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2d3` is `dz2gRest`. -/
theorem dz2d3Rest_eq_g : dz2d3Rest = dz2gRest := by
  simp only [dz2d3Rest, dz2gRest, show dz2d3R0 = dz2gR0 from rfl, show dz2d3R1 = dz2gR1 from rfl,
    show dz2d3R2 = dz2gR2 from rfl, show dz2d3R3 = dz2gR3 from rfl, show dz2d3R4 = dz2gR4 from rfl,
    show dz2d3R5 = dz2gR5 from rfl, show dz2d3R6 = dz2gR6 from rfl, show dz2d3R7 = dz2gR7 from rfl,
    show dz2d3R8 = dz2gR8 from rfl, show dz2d3R9 = dz2gR9 from rfl,
    show dz2d3R10 = dz2gR10 from rfl, show dz2d3R11 = dz2gR11 from rfl,
    show dz2d3R12 = dz2gR12 from rfl, show dz2d3R13 = dz2gR13 from rfl,
    show dz2d3R14 = dz2gR14 from rfl, show dz2d3R15 = dz2gR15 from rfl,
    show dz2d3R16 = dz2gR16 from rfl, show dz2d3R17 = dz2gR17 from rfl,
    show dz2d3R18 = dz2gR18 from rfl, show dz2d3R19 = dz2gR19 from rfl,
    show dz2d3R20 = dz2gR20 from rfl, show dz2d3R21 = dz2gR21 from rfl,
    show dz2d3R22 = dz2gR22 from rfl, show dz2d3R23 = dz2gR23 from rfl,
    show dz2d3R24 = dz2gR24 from rfl, show dz2d3R25 = dz2gR25 from rfl,
    show dz2d3R26 = dz2gR26 from rfl, show dz2d3R27 = dz2gR27 from rfl]

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2mk2` is `dz2gRest`. -/
theorem dz2mk2Rest_eq_g : dz2mk2Rest = dz2gRest := by
  simp only [dz2mk2Rest, dz2gRest, show dz2mk2R0 = dz2gR0 from rfl, show dz2mk2R1 = dz2gR1 from rfl,
    show dz2mk2R2 = dz2gR2 from rfl, show dz2mk2R3 = dz2gR3 from rfl,
    show dz2mk2R4 = dz2gR4 from rfl, show dz2mk2R5 = dz2gR5 from rfl,
    show dz2mk2R6 = dz2gR6 from rfl, show dz2mk2R7 = dz2gR7 from rfl,
    show dz2mk2R8 = dz2gR8 from rfl, show dz2mk2R9 = dz2gR9 from rfl,
    show dz2mk2R10 = dz2gR10 from rfl, show dz2mk2R11 = dz2gR11 from rfl,
    show dz2mk2R12 = dz2gR12 from rfl, show dz2mk2R13 = dz2gR13 from rfl,
    show dz2mk2R14 = dz2gR14 from rfl, show dz2mk2R15 = dz2gR15 from rfl,
    show dz2mk2R16 = dz2gR16 from rfl, show dz2mk2R17 = dz2gR17 from rfl,
    show dz2mk2R18 = dz2gR18 from rfl, show dz2mk2R19 = dz2gR19 from rfl,
    show dz2mk2R20 = dz2gR20 from rfl, show dz2mk2R21 = dz2gR21 from rfl,
    show dz2mk2R22 = dz2gR22 from rfl, show dz2mk2R23 = dz2gR23 from rfl,
    show dz2mk2R24 = dz2gR24 from rfl, show dz2mk2R25 = dz2gR25 from rfl,
    show dz2mk2R26 = dz2gR26 from rfl, show dz2mk2R27 = dz2gR27 from rfl]
  ac_rfl

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2mk3` is `dz2gRest`. -/
theorem dz2mk3Rest_eq_g : dz2mk3Rest = dz2gRest := by
  simp only [dz2mk3Rest, dz2gRest, show dz2mk3R0 = dz2gR0 from rfl, show dz2mk3R1 = dz2gR1 from rfl,
    show dz2mk3R2 = dz2gR2 from rfl, show dz2mk3R3 = dz2gR3 from rfl,
    show dz2mk3R4 = dz2gR4 from rfl, show dz2mk3R5 = dz2gR5 from rfl,
    show dz2mk3R6 = dz2gR6 from rfl, show dz2mk3R7 = dz2gR7 from rfl,
    show dz2mk3R8 = dz2gR8 from rfl, show dz2mk3R9 = dz2gR9 from rfl,
    show dz2mk3R10 = dz2gR10 from rfl, show dz2mk3R11 = dz2gR11 from rfl,
    show dz2mk3R12 = dz2gR12 from rfl, show dz2mk3R13 = dz2gR13 from rfl,
    show dz2mk3R14 = dz2gR14 from rfl, show dz2mk3R15 = dz2gR15 from rfl,
    show dz2mk3R16 = dz2gR16 from rfl, show dz2mk3R17 = dz2gR17 from rfl,
    show dz2mk3R18 = dz2gR18 from rfl, show dz2mk3R19 = dz2gR19 from rfl,
    show dz2mk3R20 = dz2gR20 from rfl, show dz2mk3R21 = dz2gR21 from rfl,
    show dz2mk3R22 = dz2gR22 from rfl, show dz2mk3R23 = dz2gR23 from rfl,
    show dz2mk3R24 = dz2gR24 from rfl, show dz2mk3R25 = dz2gR25 from rfl,
    show dz2mk3R26 = dz2gR26 from rfl, show dz2mk3R27 = dz2gR27 from rfl]
  ac_rfl

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2mk4` is `dz2gRest`. -/
theorem dz2mk4Rest_eq_g : dz2mk4Rest = dz2gRest := by
  simp only [dz2mk4Rest, dz2gRest, show dz2mk4R0 = dz2gR0 from rfl, show dz2mk4R1 = dz2gR1 from rfl,
    show dz2mk4R2 = dz2gR2 from rfl, show dz2mk4R3 = dz2gR3 from rfl,
    show dz2mk4R4 = dz2gR4 from rfl, show dz2mk4R5 = dz2gR5 from rfl,
    show dz2mk4R6 = dz2gR6 from rfl, show dz2mk4R7 = dz2gR7 from rfl,
    show dz2mk4R8 = dz2gR8 from rfl, show dz2mk4R9 = dz2gR9 from rfl,
    show dz2mk4R10 = dz2gR10 from rfl, show dz2mk4R11 = dz2gR11 from rfl,
    show dz2mk4R12 = dz2gR12 from rfl, show dz2mk4R13 = dz2gR13 from rfl,
    show dz2mk4R14 = dz2gR14 from rfl, show dz2mk4R15 = dz2gR15 from rfl,
    show dz2mk4R16 = dz2gR16 from rfl, show dz2mk4R17 = dz2gR17 from rfl,
    show dz2mk4R18 = dz2gR18 from rfl, show dz2mk4R19 = dz2gR19 from rfl,
    show dz2mk4R20 = dz2gR20 from rfl, show dz2mk4R21 = dz2gR21 from rfl,
    show dz2mk4R22 = dz2gR22 from rfl, show dz2mk4R23 = dz2gR23 from rfl,
    show dz2mk4R24 = dz2gR24 from rfl, show dz2mk4R25 = dz2gR25 from rfl,
    show dz2mk4R26 = dz2gR26 from rfl, show dz2mk4R27 = dz2gR27 from rfl]
  ac_rfl

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2mk5` is `dz2gRest`. -/
theorem dz2mk5Rest_eq_g : dz2mk5Rest = dz2gRest := by
  simp only [dz2mk5Rest, dz2gRest, show dz2mk5R0 = dz2gR0 from rfl, show dz2mk5R1 = dz2gR1 from rfl,
    show dz2mk5R2 = dz2gR2 from rfl, show dz2mk5R3 = dz2gR3 from rfl,
    show dz2mk5R4 = dz2gR4 from rfl, show dz2mk5R5 = dz2gR5 from rfl,
    show dz2mk5R6 = dz2gR6 from rfl, show dz2mk5R7 = dz2gR7 from rfl,
    show dz2mk5R8 = dz2gR8 from rfl, show dz2mk5R9 = dz2gR9 from rfl,
    show dz2mk5R10 = dz2gR10 from rfl, show dz2mk5R11 = dz2gR11 from rfl,
    show dz2mk5R12 = dz2gR12 from rfl, show dz2mk5R13 = dz2gR13 from rfl,
    show dz2mk5R14 = dz2gR14 from rfl, show dz2mk5R15 = dz2gR15 from rfl,
    show dz2mk5R16 = dz2gR16 from rfl, show dz2mk5R17 = dz2gR17 from rfl,
    show dz2mk5R18 = dz2gR18 from rfl, show dz2mk5R19 = dz2gR19 from rfl,
    show dz2mk5R20 = dz2gR20 from rfl, show dz2mk5R21 = dz2gR21 from rfl,
    show dz2mk5R22 = dz2gR22 from rfl, show dz2mk5R23 = dz2gR23 from rfl,
    show dz2mk5R24 = dz2gR24 from rfl, show dz2mk5R25 = dz2gR25 from rfl,
    show dz2mk5R26 = dz2gR26 from rfl, show dz2mk5R27 = dz2gR27 from rfl]
  ac_rfl

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2mk6` is `dz2gRest`. -/
theorem dz2mk6Rest_eq_g : dz2mk6Rest = dz2gRest := by
  simp only [dz2mk6Rest, dz2gRest, show dz2mk6R0 = dz2gR0 from rfl, show dz2mk6R1 = dz2gR1 from rfl,
    show dz2mk6R2 = dz2gR2 from rfl, show dz2mk6R3 = dz2gR3 from rfl,
    show dz2mk6R4 = dz2gR4 from rfl, show dz2mk6R5 = dz2gR5 from rfl,
    show dz2mk6R6 = dz2gR6 from rfl, show dz2mk6R7 = dz2gR7 from rfl,
    show dz2mk6R8 = dz2gR8 from rfl, show dz2mk6R9 = dz2gR9 from rfl,
    show dz2mk6R10 = dz2gR10 from rfl, show dz2mk6R11 = dz2gR11 from rfl,
    show dz2mk6R12 = dz2gR12 from rfl, show dz2mk6R13 = dz2gR13 from rfl,
    show dz2mk6R14 = dz2gR14 from rfl, show dz2mk6R15 = dz2gR15 from rfl,
    show dz2mk6R16 = dz2gR16 from rfl, show dz2mk6R17 = dz2gR17 from rfl,
    show dz2mk6R18 = dz2gR18 from rfl, show dz2mk6R19 = dz2gR19 from rfl,
    show dz2mk6R20 = dz2gR20 from rfl, show dz2mk6R21 = dz2gR21 from rfl,
    show dz2mk6R22 = dz2gR22 from rfl, show dz2mk6R23 = dz2gR23 from rfl,
    show dz2mk6R24 = dz2gR24 from rfl, show dz2mk6R25 = dz2gR25 from rfl,
    show dz2mk6R26 = dz2gR26 from rfl, show dz2mk6R27 = dz2gR27 from rfl]
  ac_rfl

set_option maxRecDepth 100000 in
/-- The circuit of the run `dz2mk7` is `dz2gRest`. -/
theorem dz2mk7Rest_eq_g : dz2mk7Rest = dz2gRest := by
  simp only [dz2mk7Rest, dz2gRest, show dz2mk7R0 = dz2gR0 from rfl, show dz2mk7R1 = dz2gR1 from rfl,
    show dz2mk7R2 = dz2gR2 from rfl, show dz2mk7R3 = dz2gR3 from rfl,
    show dz2mk7R4 = dz2gR4 from rfl, show dz2mk7R5 = dz2gR5 from rfl,
    show dz2mk7R6 = dz2gR6 from rfl, show dz2mk7R7 = dz2gR7 from rfl,
    show dz2mk7R8 = dz2gR8 from rfl, show dz2mk7R9 = dz2gR9 from rfl,
    show dz2mk7R10 = dz2gR10 from rfl, show dz2mk7R11 = dz2gR11 from rfl,
    show dz2mk7R12 = dz2gR12 from rfl, show dz2mk7R13 = dz2gR13 from rfl,
    show dz2mk7R14 = dz2gR14 from rfl, show dz2mk7R15 = dz2gR15 from rfl,
    show dz2mk7R16 = dz2gR16 from rfl, show dz2mk7R17 = dz2gR17 from rfl,
    show dz2mk7R18 = dz2gR18 from rfl, show dz2mk7R19 = dz2gR19 from rfl,
    show dz2mk7R20 = dz2gR20 from rfl, show dz2mk7R21 = dz2gR21 from rfl,
    show dz2mk7R22 = dz2gR22 from rfl, show dz2mk7R23 = dz2gR23 from rfl,
    show dz2mk7R24 = dz2gR24 from rfl, show dz2mk7R25 = dz2gR25 from rfl,
    show dz2mk7R26 = dz2gR26 from rfl, show dz2mk7R27 = dz2gR27 from rfl]
  ac_rfl

namespace LP

/-- The run region NZ: the regions of the runs up to their cut (`Gen/*PreG`). -/
def decRunRegNZ : Set Cell :=
  unionL [dz2dPreRegion, dz2d1PreRegion, dz2d2PreRegion, dz2d3PreRegion, dz2mk1PreRegion,
    dz2mk2PreRegion, dz2mk3PreRegion, dz2mk4PreRegion, dz2mk5PreRegion, dz2mk6PreRegion,
    dz2mk7PreRegion]

/-- The run region Z: the region of the zero test up to its cut (`Gen/Dz2mk0PreG`). -/
def decRunRegZ : Set Cell := dz2mk0PreRegion

/-- The rest region NZ. -/
def decRestRegNZ : Set Cell :=
  unionL [dz2dRestRegion, dz2d1RestRegion, dz2d2RestRegion, dz2d3RestRegion, dz2mk1RestRegion,
    dz2mk2RestRegion, dz2mk3RestRegion, dz2mk4RestRegion, dz2mk5RestRegion, dz2mk6RestRegion,
    dz2mk7RestRegion]

/-- The register after a pull. -/
def RegS.pullAt (R : RegS) (σ : Salvo) (ph : ℕ) (Vs' : ℤ) : RegS :=
  ⟨R.q ++ [(σ, (16 : ℤ) + (((R.m + 6555 + ph) / 4 : ℕ) : ℤ))], R.K, R.m + 11490, Vs', R.Vb⟩

/-- **The pull keeps the register ready and lowers its value by one** (value `≥ 1`). -/
theorem RegS.pullAt_ready {R : RegS} (hR : R.Ready) {σ : Salvo} (hd : σ.d = -1) {ph : ℕ}
    (hph : ph ≤ 3) {Vs' : ℤ}
    (hv' : DiagValid regParams Vs' R.Vb R.K
      (R.q ++ [(σ, (16 : ℤ) + (((R.m + 6555 + ph) / 4 : ℕ) : ℤ))]))
    (hVs' : -34 ≤ Vs' + 2 * (((R.m + 6555 + ph) / 4 : ℕ) : ℤ)) (hw : 1 ≤ R.K + qMove R.q) :
    (R.pullAt σ ph Vs').Ready ∧ (R.pullAt σ ph Vs').val + 1 = R.val := by
  obtain ⟨⟨-, h2, -, -⟩, hVb, hQ⟩ := hR
  have hm : (R.m + 6555 + ph) / 4 + 1233 ≤ (R.m + 11490) / 4 := by omega
  have hm' : (((R.m + 6555 + ph) / 4 : ℕ) : ℤ) + 1233 ≤ (((R.m + 11490) / 4 : ℕ) : ℤ) := by
    exact_mod_cast hm
  have hq : qMove (R.q ++ [(σ, (16 : ℤ) + (((R.m + 6555 + ph) / 4 : ℕ) : ℤ))]) =
      qMove R.q - 1 := by
    rw [qMove_append, hd]; ring
  refine ⟨⟨⟨hv', h2, ?_, ?_⟩, hVb, QBeforeL.pull (by norm_num) hQ σ ph hph⟩, ?_⟩
  · simp only [RegS.pullAt]; omega
  · simp only [RegS.pullAt]; rw [hq]; omega
  · simp only [RegS.val, RegS.pullAt]; rw [hq]; omega


/-- The block `k` of a register as rows. -/
theorem reg1Block_ofRows (k : ℤ) : reg1Block k = ofRows (155 + k) (251 + k) [3, 3] := by
  rw [reg1Block, counter, translate_ofRows]
  congr 1 <;> ring

/-- The static zero tests `k = 1 … 7` with the answer split off, in the frame of the module. -/
theorem regNZ_static (k : ℤ) (h1 : 1 ≤ k) (h7 : k ≤ 7) :
    ∃ X : Finset Cell,
      Reaction (dz2gRest ∪ ofRows (-1186) (-1227) [2, 4, 7] ∪ reg1Block k)
        (X ∪ ansNZWL.cells 9203) 9503 (fun _ => decRunRegNZ) ∧
      Reaction X (dz2gRest ∪ reg1Block (k - 1)) 1987 (fun _ => decRestRegNZ) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by omega⟩
  have hn1 : 1 ≤ n := by exact_mod_cast h1
  have hn7 : n ≤ 7 := by exact_mod_cast h7
  interval_cases n
  · have h1 := dz2mk1OpP
    have h2 := dz2mk1Run_restS.2
    rw [dz2mk1Rest_eq, runAnsNZ_eq.2.2.2.2.1] at h1
    rw [dz2mk1Rest_eq] at h2
    rw [reg1Block_ofRows, reg1Block_ofRows]
    norm_num
    refine ⟨Proc.start dz2mk1LrestS, (h1.congrPQ (by ac_rfl) rfl).mono ?_, h2.mono ?_⟩ <;>
      exact fun _ _ => subset_unionL (by simp) le_rfl
  · have h1 := dz2mk2OpP
    have h2 := dz2mk2Run_restS.2
    rw [dz2mk2Rest_eq_g, runAnsNZ_eq.2.2.2.2.2.1] at h1
    rw [dz2mk2Rest_eq_g] at h2
    rw [reg1Block_ofRows, reg1Block_ofRows]
    norm_num
    refine ⟨Proc.start dz2mk2LrestS, (h1.congrPQ (by ac_rfl) rfl).mono ?_, h2.mono ?_⟩ <;>
      exact fun _ _ => subset_unionL (by simp) le_rfl
  · have h1 := dz2mk3OpP
    have h2 := dz2mk3Run_restS.2
    rw [dz2mk3Rest_eq_g, runAnsNZ_eq.2.2.2.2.2.2.1] at h1
    rw [dz2mk3Rest_eq_g] at h2
    rw [reg1Block_ofRows, reg1Block_ofRows]
    norm_num
    refine ⟨Proc.start dz2mk3LrestS, (h1.congrPQ (by ac_rfl) rfl).mono ?_, h2.mono ?_⟩ <;>
      exact fun _ _ => subset_unionL (by simp) le_rfl
  · have h1 := dz2mk4OpP
    have h2 := dz2mk4Run_restS.2
    rw [dz2mk4Rest_eq_g, runAnsNZ_eq.2.2.2.2.2.2.2.1] at h1
    rw [dz2mk4Rest_eq_g] at h2
    rw [reg1Block_ofRows, reg1Block_ofRows]
    norm_num
    refine ⟨Proc.start dz2mk4LrestS, (h1.congrPQ (by ac_rfl) rfl).mono ?_, h2.mono ?_⟩ <;>
      exact fun _ _ => subset_unionL (by simp) le_rfl
  · have h1 := dz2mk5OpP
    have h2 := dz2mk5Run_restS.2
    rw [dz2mk5Rest_eq_g, runAnsNZ_eq.2.2.2.2.2.2.2.2.1] at h1
    rw [dz2mk5Rest_eq_g] at h2
    rw [reg1Block_ofRows, reg1Block_ofRows]
    norm_num
    refine ⟨Proc.start dz2mk5LrestS, (h1.congrPQ (by ac_rfl) rfl).mono ?_, h2.mono ?_⟩ <;>
      exact fun _ _ => subset_unionL (by simp) le_rfl
  · have h1 := dz2mk6OpP
    have h2 := dz2mk6Run_restS.2
    rw [dz2mk6Rest_eq_g, runAnsNZ_eq.2.2.2.2.2.2.2.2.2.1] at h1
    rw [dz2mk6Rest_eq_g] at h2
    rw [reg1Block_ofRows, reg1Block_ofRows]
    norm_num
    refine ⟨Proc.start dz2mk6LrestS, (h1.congrPQ (by ac_rfl) rfl).mono ?_, h2.mono ?_⟩ <;>
      exact fun _ _ => subset_unionL (by simp) le_rfl
  · have h1 := dz2mk7OpP
    have h2 := dz2mk7Run_restS.2
    rw [dz2mk7Rest_eq_g, runAnsNZ_eq.2.2.2.2.2.2.2.2.2.2] at h1
    rw [dz2mk7Rest_eq_g] at h2
    rw [reg1Block_ofRows, reg1Block_ofRows]
    norm_num
    refine ⟨Proc.start dz2mk7LrestS, (h1.congrPQ (by ac_rfl) rfl).mono ?_, h2.mono ?_⟩ <;>
      exact fun _ _ => subset_unionL (by simp) le_rfl

/-- The pull `dz2d` (phase `0`) in the frame of the module. -/
theorem regNZ_dz2d {R : RegS} (hR : R.Ready) (hm : (R.m + 6555) % 4 = 0)
    (hz : R.Vb ≤ 3 + 2 * (R.K + qMove R.q)) :
    ∃ (X : Finset Cell) (R' : RegS), R'.val + 1 = R.val ∧ R'.Ready ∧
      Reaction (dz2gRest ∪ ofRows (-1186) (-1227) [2, 4, 7] ∪ conway.evolve R.m (diagW R.q R.K))
        (X ∪ ansNZWL.cells 9203) 9503 (fun _ => decRunRegNZ) ∧
      Reaction X (dz2gRest ∪ conway.evolve R'.m (diagW R'.q R'.K)) 1987
        (fun _ => decRestRegNZ) := by
  obtain ⟨hI, hVb, hQ⟩ := hR
  obtain ⟨hv', hVs'⟩ := dz2d_join hI.1 hI.2.2.2 (hQ.toQBefore (by norm_num)) hI.2.2.1 hz
  have h1 := dz2dOpP R.q R.K R.Vs R.Vb _ R.m hI.1 hv' hm hI.2.1 hI.2.2.1 hVs'
  have h2 := (dz2dOpS R.q R.K R.Vs R.Vb _ R.m hI.1 hv' hm hI.2.1 hI.2.2.1 hVs').2
  rw [dz2dRest_eq_g, runAnsNZ_eq.1] at h1
  rw [dz2dRest_eq_g] at h2
  have hw : 1 ≤ R.K + qMove R.q := by omega
  obtain ⟨hr, hval⟩ := RegS.pullAt_ready ⟨hI, hVb, hQ⟩ (σ := regPull) rfl (ph := 0) (by norm_num)
    (Vs' := joinVs R.Vs regPull ((16 : ℤ) + (((R.m + 6555) / 4 : ℕ) : ℤ))) hv' hVs' hw
  refine ⟨_, _, hval, hr, h1.mono fun _ _ => subset_unionL
    (by simp) le_rfl,
    (h2.congrPQ rfl rfl).mono fun _ _ => subset_unionL
    (by simp) le_rfl⟩

/-- The pull `dz2d1` (phase `1`) in the frame of the module. -/
theorem regNZ_dz2d1 {R : RegS} (hR : R.Ready) (hm : (R.m + 6556) % 4 = 0)
    (hz : R.Vb ≤ 3 + 2 * (R.K + qMove R.q)) :
    ∃ (X : Finset Cell) (R' : RegS), R'.val + 1 = R.val ∧ R'.Ready ∧
      Reaction (dz2gRest ∪ ofRows (-1186) (-1227) [2, 4, 7] ∪ conway.evolve R.m (diagW R.q R.K))
        (X ∪ ansNZWL.cells 9203) 9503 (fun _ => decRunRegNZ) ∧
      Reaction X (dz2gRest ∪ conway.evolve R'.m (diagW R'.q R'.K)) 1987
        (fun _ => decRestRegNZ) := by
  obtain ⟨hI, hVb, hQ⟩ := hR
  obtain ⟨hv', hVs'⟩ := dz2d1_join hI.1 hI.2.2.2 (hQ.toQBefore (by norm_num)) hI.2.2.1 hz
  have h1 := dz2d1OpP R.q R.K R.Vs R.Vb _ R.m hI.1 hv' hm hI.2.1 hI.2.2.1 hVs'
  have h2 := (dz2d1OpS R.q R.K R.Vs R.Vb _ R.m hI.1 hv' hm hI.2.1 hI.2.2.1 hVs').2
  rw [dz2d1Rest_eq_g, runAnsNZ_eq.2.1] at h1
  rw [dz2d1Rest_eq_g] at h2
  have hw : 1 ≤ R.K + qMove R.q := by omega
  obtain ⟨hr, hval⟩ := RegS.pullAt_ready ⟨hI, hVb, hQ⟩ (σ := regPullP1) rfl (ph := 1) (by norm_num)
    (Vs' := joinVs R.Vs regPullP1 ((16 : ℤ) + (((R.m + 6556) / 4 : ℕ) : ℤ))) hv' hVs' hw
  refine ⟨_, _, hval, hr, h1.mono fun _ _ => subset_unionL
    (by simp) le_rfl,
    (h2.congrPQ rfl rfl).mono fun _ _ => subset_unionL
    (by simp) le_rfl⟩

/-- The pull `dz2d2` (phase `2`) in the frame of the module. -/
theorem regNZ_dz2d2 {R : RegS} (hR : R.Ready) (hm : (R.m + 6557) % 4 = 0)
    (hz : R.Vb ≤ 3 + 2 * (R.K + qMove R.q)) :
    ∃ (X : Finset Cell) (R' : RegS), R'.val + 1 = R.val ∧ R'.Ready ∧
      Reaction (dz2gRest ∪ ofRows (-1186) (-1227) [2, 4, 7] ∪ conway.evolve R.m (diagW R.q R.K))
        (X ∪ ansNZWL.cells 9203) 9503 (fun _ => decRunRegNZ) ∧
      Reaction X (dz2gRest ∪ conway.evolve R'.m (diagW R'.q R'.K)) 1987
        (fun _ => decRestRegNZ) := by
  obtain ⟨hI, hVb, hQ⟩ := hR
  obtain ⟨hv', hVs'⟩ := dz2d2_join hI.1 hI.2.2.2 (hQ.toQBefore (by norm_num)) hI.2.2.1 hz
  have h1 := dz2d2OpP R.q R.K R.Vs R.Vb _ R.m hI.1 hv' hm hI.2.1 hI.2.2.1 hVs'
  have h2 := (dz2d2OpS R.q R.K R.Vs R.Vb _ R.m hI.1 hv' hm hI.2.1 hI.2.2.1 hVs').2
  rw [dz2d2Rest_eq_g, runAnsNZ_eq.2.2.1] at h1
  rw [dz2d2Rest_eq_g] at h2
  have hw : 1 ≤ R.K + qMove R.q := by omega
  obtain ⟨hr, hval⟩ := RegS.pullAt_ready ⟨hI, hVb, hQ⟩ (σ := regPullP2) rfl (ph := 2) (by norm_num)
    (Vs' := joinVs R.Vs regPullP2 ((16 : ℤ) + (((R.m + 6557) / 4 : ℕ) : ℤ))) hv' hVs' hw
  refine ⟨_, _, hval, hr, h1.mono fun _ _ => subset_unionL
    (by simp) le_rfl,
    (h2.congrPQ rfl rfl).mono fun _ _ => subset_unionL
    (by simp) le_rfl⟩

/-- The pull `dz2d3` (phase `3`) in the frame of the module. -/
theorem regNZ_dz2d3 {R : RegS} (hR : R.Ready) (hm : (R.m + 6558) % 4 = 0)
    (hz : R.Vb ≤ 3 + 2 * (R.K + qMove R.q)) :
    ∃ (X : Finset Cell) (R' : RegS), R'.val + 1 = R.val ∧ R'.Ready ∧
      Reaction (dz2gRest ∪ ofRows (-1186) (-1227) [2, 4, 7] ∪ conway.evolve R.m (diagW R.q R.K))
        (X ∪ ansNZWL.cells 9203) 9503 (fun _ => decRunRegNZ) ∧
      Reaction X (dz2gRest ∪ conway.evolve R'.m (diagW R'.q R'.K)) 1987
        (fun _ => decRestRegNZ) := by
  obtain ⟨hI, hVb, hQ⟩ := hR
  obtain ⟨hv', hVs'⟩ := dz2d3_join hI.1 hI.2.2.2 (hQ.toQBefore (by norm_num)) hI.2.2.1 hz
  have h1 := dz2d3OpP R.q R.K R.Vs R.Vb _ R.m hI.1 hv' hm hI.2.1 hI.2.2.1 hVs'
  have h2 := (dz2d3OpS R.q R.K R.Vs R.Vb _ R.m hI.1 hv' hm hI.2.1 hI.2.2.1 hVs').2
  rw [dz2d3Rest_eq_g, runAnsNZ_eq.2.2.2.1] at h1
  rw [dz2d3Rest_eq_g] at h2
  have hw : 1 ≤ R.K + qMove R.q := by omega
  obtain ⟨hr, hval⟩ := RegS.pullAt_ready ⟨hI, hVb, hQ⟩ (σ := regPullP3) rfl (ph := 3) (by norm_num)
    (Vs' := joinVs R.Vs regPullP3 ((16 : ℤ) + (((R.m + 6558) / 4 : ℕ) : ℤ))) hv' hVs' hw
  refine ⟨_, _, hval, hr, h1.mono fun _ _ => subset_unionL
    (by simp) le_rfl,
    (h2.congrPQ rfl rfl).mono fun _ _ => subset_unionL
    (by simp) le_rfl⟩

/-- **The NZ register run in the frame of the module**, for every ready register of value
`≥ 1`: up to the cut the run, then the circuit alone, ending with the register holding one
less. -/
theorem regNZ_frame {R : RegS} (hR : R.Ready) (hpos : 1 ≤ R.val) :
    ∃ (X : Finset Cell) (R' : RegS), R'.val + 1 = R.val ∧ R'.Ready ∧
      Reaction (dz2gRest ∪ ofRows (-1186) (-1227) [2, 4, 7] ∪ conway.evolve R.m (diagW R.q R.K))
        (X ∪ ansNZWL.cells 9203) 9503 (fun _ => decRunRegNZ) ∧
      Reaction X (dz2gRest ∪ conway.evolve R'.m (diagW R'.q R'.K)) 1987
        (fun _ => decRestRegNZ) := by
  obtain ⟨hI, hVb, hQ⟩ := hR
  rcases RegS.pull_dichotomy hI hVb hQ with hz | ⟨hw, hs⟩
  · have h4 : (R.m + 6555) % 4 = 0 ∨ (R.m + 6556) % 4 = 0 ∨ (R.m + 6557) % 4 = 0 ∨
        (R.m + 6558) % 4 = 0 := by omega
    rcases h4 with h | h | h | h
    · exact regNZ_dz2d ⟨hI, hVb, hQ⟩ h hz
    · exact regNZ_dz2d1 ⟨hI, hVb, hQ⟩ h hz
    · exact regNZ_dz2d2 ⟨hI, hVb, hQ⟩ h hz
    · exact regNZ_dz2d3 ⟨hI, hVb, hQ⟩ h hz
  · have hv0 := hI.2.2.2
    have h1 : 1 ≤ R.K + qMove R.q := by simp only [RegS.val] at hpos; omega
    obtain ⟨X, hX1, hX2⟩ := regNZ_static _ h1 hw
    refine ⟨X, RegS.block (R.K + qMove R.q - 1).toNat (R.m + 11490), ?_,
      ⟨RegS.inv_block _ _, RegS.Vb_block _ _, RegS.qBeforeL_block _ _ _⟩, ?_, ?_⟩
    · rw [RegS.val_block]; simp only [RegS.val]; omega
    · rw [hs]; exact hX1
    · rw [RegS.diagW_block, show (((R.K + qMove R.q - 1).toNat : ℕ) : ℤ) = R.K + qMove R.q - 1 by
        omega]
      exact hX2

/-- **The Z register run in the frame of the module**: a ready register of value `0` is the
block `0`, and the zero test `dz2mk0` leaves it unchanged. -/
theorem regZ_frame {R : RegS} (hR : R.Ready) (h0 : R.val = 0) :
    ∃ X : Finset Cell,
      Reaction (dz2gRest ∪ ofRows (-1186) (-1227) [2, 4, 7] ∪ conway.evolve R.m (diagW R.q R.K))
        (X ∪ ansZWL.cells 11695) 11995 (fun _ => decRunRegZ) ∧
      Reaction X (dz2gRest ∪ conway.evolve (R.m + 27540) (diagW R.q R.K)) 15545
        (fun _ => dz2mk0RestRegion) := by
  obtain ⟨hI, hVb, hQ⟩ := hR
  have hv0 := hI.2.2.2
  have hw : R.K + qMove R.q = 0 := by simp only [RegS.val] at h0; omega
  have e1 := diagW_static hI.1 hQ (by omega)
  have e2 := diagW_static hI.1 (hQ.mono (show R.m ≤ R.m + 27540 by omega)) (by omega)
  rw [hw, reg1Block_ofRows] at e1 e2
  norm_num at e1 e2
  have h1 := dz2mk0OpP
  have h2 := dz2mk0Run_restS.2
  rw [dz2mk0Rest_eq, runAnsZ_eq] at h1
  rw [dz2mk0Rest_eq] at h2
  rw [e1, e2]
  exact ⟨_, h1.congrPQ (by ac_rfl) rfl, h2⟩

/-! ### Placement at the module -/

/-- A set of the module frame placed at module `r`. -/
def modImg (p : Program) (r : ℕ) (S : Set Cell) : Set Cell :=
  (fun c => (modDX p r, modDY p r) + c) '' S

/-- **The NZ register run at module `r`**, for every ready register of value `≥ 1`. -/
theorem regNZ_module (p : Program) (r : ℕ) {R : RegS} (hR : R.Ready) (hpos : 1 ≤ R.val) :
    ∃ (X : Finset Cell) (R' : RegS), R'.val + 1 = R.val ∧ R'.Ready ∧
      Reaction (translate (modDX p r, modDY p r) (dz2gRest ∪ ofRows (-1186) (-1227) [2, 4, 7]) ∪
          regAt p r R)
        (X ∪ translate (modDX p r, modDY p r) (ansNZWL.cells 9203)) 9503
        (fun _ => modImg p r decRunRegNZ) ∧
      Reaction X (translate (modDX p r, modDY p r) dz2gRest ∪ regAt p r R') 1987
        (fun _ => modImg p r decRestRegNZ) := by
  obtain ⟨X, R', h1, h2, h3, h4⟩ := regNZ_frame hR hpos
  refine ⟨translate (modDX p r, modDY p r) X, R', h1, h2, ?_, ?_⟩
  · have h := h3.translate (modDX p r, modDY p r)
    simp only [translate_union] at h
    rw [regAt, translate_union]
    exact h
  · have h := h4.translate (modDX p r, modDY p r)
    rw [translate_union] at h
    rw [regAt]
    exact h

/-- **The Z register run at module `r`**, for every ready register of value `0`. -/
theorem regZ_module (p : Program) (r : ℕ) {R : RegS} (hR : R.Ready) (h0 : R.val = 0) :
    ∃ X : Finset Cell,
      Reaction (translate (modDX p r, modDY p r) (dz2gRest ∪ ofRows (-1186) (-1227) [2, 4, 7]) ∪
          regAt p r R)
        (X ∪ translate (modDX p r, modDY p r) (ansZWL.cells 11695)) 11995
        (fun _ => modImg p r decRunRegZ) ∧
      Reaction X (translate (modDX p r, modDY p r) dz2gRest ∪ regAt p r (R.later 27540)) 15545
        (fun _ => modImg p r dz2mk0RestRegion) := by
  obtain ⟨X, h3, h4⟩ := regZ_frame hR h0
  refine ⟨translate (modDX p r, modDY p r) X, ?_, ?_⟩
  · have h := h3.translate (modDX p r, modDY p r)
    simp only [translate_union] at h
    rw [regAt, translate_union]
    exact h
  · have h := h4.translate (modDX p r, modDY p r)
    rw [translate_union] at h
    rw [regAt]
    exact h


/-! ### Lower bounds of `u` for unions of components -/

/-- Every member of a list of sets lies in `S`. -/
def DecAllSub (S : Set Cell) : List (Set Cell) → Prop
  | [] => True
  | X :: L => X ⊆ S ∧ DecAllSub S L

/-- The union of a list of subsets of `S` lies in `S`. -/
theorem unionL_subset_dec {S : Set Cell} : ∀ {L : List (Set Cell)}, DecAllSub S L → unionL L ⊆ S
  | [], _ => fun _ h => h.elim
  | _ :: _, ⟨h, hL⟩ => Set.union_subset h (unionL_subset_dec hL)

/-- A component with `a - hi ≥ m` or `U₁ ≥ m` lies at `u ≥ m`. -/
theorem BU_subset_u' {m a b lo hi U₁ U₂ V₁ V₂ : ℤ} (h : m ≤ a - hi ∨ m ≤ U₁) :
    BU a b lo hi U₁ U₂ V₁ V₂ ⊆ {c : Cell | m ≤ c.1 - c.2} := by
  rintro c ⟨⟨c1, c2, c3, c4⟩, c5, c6, c7, c8⟩
  change m ≤ c.1 - c.2
  omega

/-- The lanes of the register lie at `u ≥ -113`. -/
theorem regLanes_subset_u' {m : ℤ} (h : m ≤ -113) : regLanes ⊆ {c : Cell | m ≤ c.1 - c.2} := by
  rintro c ⟨c1, c2, c3⟩
  change m ≤ c.1 - c.2
  omega

/-! ### The regions of the runs lie right of `u = -738` (module frame) -/

/-- The components of `dz2dPreRegL` lie at `u ≥ -738`. -/
theorem dz2dPreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2dPreRegL := by
  simp only [dz2dPreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | exact regLanes_subset_u' (by omega) | trivial

/-- The components of `dz2dRestRegL` lie at `u ≥ -738`. -/
theorem dz2dRestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2dRestRegL := by
  simp only [dz2dRestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | exact regLanes_subset_u' (by omega) | trivial

/-- The components of `dz2d1PreRegL` lie at `u ≥ -738`. -/
theorem dz2d1PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2d1PreRegL := by
  simp only [dz2d1PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | exact regLanes_subset_u' (by omega) | trivial

/-- The components of `dz2d1RestRegL` lie at `u ≥ -738`. -/
theorem dz2d1RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2d1RestRegL := by
  simp only [dz2d1RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | exact regLanes_subset_u' (by omega) | trivial

/-- The components of `dz2d2PreRegL` lie at `u ≥ -738`. -/
theorem dz2d2PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2d2PreRegL := by
  simp only [dz2d2PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | exact regLanes_subset_u' (by omega) | trivial

/-- The components of `dz2d2RestRegL` lie at `u ≥ -738`. -/
theorem dz2d2RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2d2RestRegL := by
  simp only [dz2d2RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | exact regLanes_subset_u' (by omega) | trivial

/-- The components of `dz2d3PreRegL` lie at `u ≥ -738`. -/
theorem dz2d3PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2d3PreRegL := by
  simp only [dz2d3PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | exact regLanes_subset_u' (by omega) | trivial

/-- The components of `dz2d3RestRegL` lie at `u ≥ -738`. -/
theorem dz2d3RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2d3RestRegL := by
  simp only [dz2d3RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | exact regLanes_subset_u' (by omega) | trivial

set_option maxRecDepth 100000 in
/-- The components of `dz2mk0PreRegL` lie at `u ≥ -738`. -/
theorem dz2mk0PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk0PreRegL := by
  simp only [dz2mk0PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

set_option maxRecDepth 100000 in
/-- The components of `dz2mk0RestRegL` lie at `u ≥ -738`. -/
theorem dz2mk0RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk0RestRegL := by
  simp only [dz2mk0RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk1PreRegL` lie at `u ≥ -738`. -/
theorem dz2mk1PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk1PreRegL := by
  simp only [dz2mk1PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk1RestRegL` lie at `u ≥ -738`. -/
theorem dz2mk1RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk1RestRegL := by
  simp only [dz2mk1RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk2PreRegL` lie at `u ≥ -738`. -/
theorem dz2mk2PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk2PreRegL := by
  simp only [dz2mk2PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk2RestRegL` lie at `u ≥ -738`. -/
theorem dz2mk2RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk2RestRegL := by
  simp only [dz2mk2RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk3PreRegL` lie at `u ≥ -738`. -/
theorem dz2mk3PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk3PreRegL := by
  simp only [dz2mk3PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk3RestRegL` lie at `u ≥ -738`. -/
theorem dz2mk3RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk3RestRegL := by
  simp only [dz2mk3RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk4PreRegL` lie at `u ≥ -738`. -/
theorem dz2mk4PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk4PreRegL := by
  simp only [dz2mk4PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk4RestRegL` lie at `u ≥ -738`. -/
theorem dz2mk4RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk4RestRegL := by
  simp only [dz2mk4RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk5PreRegL` lie at `u ≥ -738`. -/
theorem dz2mk5PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk5PreRegL := by
  simp only [dz2mk5PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk5RestRegL` lie at `u ≥ -738`. -/
theorem dz2mk5RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk5RestRegL := by
  simp only [dz2mk5RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk6PreRegL` lie at `u ≥ -738`. -/
theorem dz2mk6PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk6PreRegL := by
  simp only [dz2mk6PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk6RestRegL` lie at `u ≥ -738`. -/
theorem dz2mk6RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk6RestRegL := by
  simp only [dz2mk6RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk7PreRegL` lie at `u ≥ -738`. -/
theorem dz2mk7PreRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk7PreRegL := by
  simp only [dz2mk7PreRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- The components of `dz2mk7RestRegL` lie at `u ≥ -738`. -/
theorem dz2mk7RestRegL_u : DecAllSub {c : Cell | -738 ≤ c.1 - c.2} dz2mk7RestRegL := by
  simp only [dz2mk7RestRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact BU_subset_u' (by omega) | trivial

/-- **The NZ run regions lie at `u ≥ -738`** (module frame). -/
theorem decRunRegNZ_u : decRunRegNZ ⊆ {c : Cell | -738 ≤ c.1 - c.2} :=
  unionL_subset_dec ⟨unionL_subset_dec dz2dPreRegL_u,
    unionL_subset_dec dz2d1PreRegL_u,
    unionL_subset_dec dz2d2PreRegL_u,
    unionL_subset_dec dz2d3PreRegL_u,
    unionL_subset_dec dz2mk1PreRegL_u,
    unionL_subset_dec dz2mk2PreRegL_u,
    unionL_subset_dec dz2mk3PreRegL_u,
    unionL_subset_dec dz2mk4PreRegL_u,
    unionL_subset_dec dz2mk5PreRegL_u,
    unionL_subset_dec dz2mk6PreRegL_u,
    unionL_subset_dec dz2mk7PreRegL_u, trivial⟩

/-- **The NZ rest regions lie at `u ≥ -738`** (module frame). -/
theorem decRestRegNZ_u : decRestRegNZ ⊆ {c : Cell | -738 ≤ c.1 - c.2} :=
  unionL_subset_dec ⟨unionL_subset_dec dz2dRestRegL_u,
    unionL_subset_dec dz2d1RestRegL_u,
    unionL_subset_dec dz2d2RestRegL_u,
    unionL_subset_dec dz2d3RestRegL_u,
    unionL_subset_dec dz2mk1RestRegL_u,
    unionL_subset_dec dz2mk2RestRegL_u,
    unionL_subset_dec dz2mk3RestRegL_u,
    unionL_subset_dec dz2mk4RestRegL_u,
    unionL_subset_dec dz2mk5RestRegL_u,
    unionL_subset_dec dz2mk6RestRegL_u,
    unionL_subset_dec dz2mk7RestRegL_u, trivial⟩

/-- **The Z run region lies at `u ≥ -738`** (module frame). -/
theorem decRunRegZ_u : decRunRegZ ⊆ {c : Cell | -738 ≤ c.1 - c.2} :=
  unionL_subset_dec dz2mk0PreRegL_u

/-- **The Z rest region lies at `u ≥ -738`** (module frame). -/
theorem dz2mk0RestRegion_u : dz2mk0RestRegion ⊆ {c : Cell | -738 ≤ c.1 - c.2} :=
  unionL_subset_dec dz2mk0RestRegL_u

end LP

end LeanTheory.Life
