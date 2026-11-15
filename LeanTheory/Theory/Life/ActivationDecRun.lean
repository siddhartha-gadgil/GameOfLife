/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecModule
public import LeanTheory.Theory.Life.Gen.Dz2dData
public import LeanTheory.Theory.Life.Gen.Dz2d1Data
public import LeanTheory.Theory.Life.Gen.Dz2d2Data
public import LeanTheory.Theory.Life.Gen.Dz2d3Data
public import LeanTheory.Theory.Life.Gen.Dz2mk0Data
public import LeanTheory.Theory.Life.Gen.Dz2mk1Data
public import LeanTheory.Theory.Life.Gen.Dz2mk2Data
public import LeanTheory.Theory.Life.Gen.Dz2mk3Data
public import LeanTheory.Theory.Life.Gen.Dz2mk4Data
public import LeanTheory.Theory.Life.Gen.Dz2mk5Data
public import LeanTheory.Theory.Life.Gen.Dz2mk6Data
public import LeanTheory.Theory.Life.Gen.Dz2mk7Data

/-!
# The answers of the register runs on the module's world lines

Research note `N-22`, layer 3, `decJz` activation. Every split register run (`Gen/*Split.lean`)
starts from the input `ofRows (-1186) (-1227) [2, 4, 7] = cp0WL.cells (-300)` (`runIn_eq`) and
releases its answer glider at the cut. Placed at module `r` with the run started at `sh - 300`
(`dec_run_time`):

* the NZ answer (`dz2dA122`, `dz2d1A124`, `dz2d2A126`, `dz2d3A128`, `dz2mk1A150` …
  `dz2mk7A150`; cut at run time `9503`) is the glider of `ansNZWL` delayed by `sh`, at
  `sh + 9203` (`runAnsNZ_eq`, `runAnsNZ_placed`);
* the Z answer (`dz2mk0A144`; cut at run time `11995`) is the glider of `ansZWL` delayed by `sh`,
  at `sh + 11695` (`runAnsZ_eq`, `runAnsZ_placed`).

From there `ActivationDecStation` carries the answer past the stations `0 … j - 1`
(`answerNZ_pass`, `answerZ_pass`, after a free flight to the capture position of station `0`:
`1147` generations NZ, `695` generations Z) to the capture at station `j`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- **The NZ answers of all the split runs are the same glider**, the glider of `ansNZWL` at
`9203` (the cut, run time `9503`). -/
theorem runAnsNZ_eq :
    dz2dA122 = ansNZWL.cells 9203 ∧ dz2d1A124 = ansNZWL.cells 9203 ∧
      dz2d2A126 = ansNZWL.cells 9203 ∧ dz2d3A128 = ansNZWL.cells 9203 ∧
      dz2mk1A150 = ansNZWL.cells 9203 ∧ dz2mk2A150 = ansNZWL.cells 9203 ∧
      dz2mk3A150 = ansNZWL.cells 9203 ∧ dz2mk4A150 = ansNZWL.cells 9203 ∧
      dz2mk5A150 = ansNZWL.cells 9203 ∧ dz2mk6A150 = ansNZWL.cells 9203 ∧
      dz2mk7A150 = ansNZWL.cells 9203 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The Z answer of the split run `dz2mk0`** is the glider of `ansZWL` at `11695` (the cut, run
time `11995`). -/
theorem runAnsZ_eq : dz2mk0A144 = ansZWL.cells 11695 := rfl

/-- **The NZ answer placed at module `r`**: for a run started at `sh - 300`, the answer at the cut
(`sh + 9203`) is the glider of the module's world line `ansNZWL` delayed by `sh`. -/
theorem runAnsNZ_placed (p : Program) (r : ℕ) (sh : ℤ) :
    translate (modDX p r, modDY p r) (ansNZWL.cells 9203) =
      ((modWL p r ansNZWL).shift 0 0 sh).cells (sh + 9203) := by
  rw [add_comm, modShift_cells p r ⟨Or.inl rfl, Or.inl rfl⟩]

/-- **The Z answer placed at module `r`**: for a run started at `sh - 300`, the answer at the cut
(`sh + 11695`) is the glider of the module's world line `ansZWL` delayed by `sh`. -/
theorem runAnsZ_placed (p : Program) (r : ℕ) (sh : ℤ) :
    translate (modDX p r, modDY p r) (ansZWL.cells 11695) =
      ((modWL p r ansZWL).shift 0 0 sh).cells (sh + 11695) := by
  rw [add_comm, modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩]

/-- **The run input placed at module `r`**: for a run started at `sh - 300`, the input is the
glider of `cp0WL` delayed by `sh` (the reference control `C'` of the module's world lines). -/
theorem runIn_placed (p : Program) (r : ℕ) (sh : ℤ) :
    translate (modDX p r, modDY p r) (ofRows (-1186) (-1227) [2, 4, 7]) =
      ((modWL p r cp0WL).shift 0 0 sh).cells (sh - 300) := by
  rw [runIn_eq, show sh - 300 = -300 + sh by ring, modShift_cells p r ⟨Or.inl rfl, Or.inl rfl⟩]

end LP

end LeanTheory.Life
