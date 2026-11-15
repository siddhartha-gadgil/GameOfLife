/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Gen.Dz2gRun
public import LeanTheory.Theory.Life.Gen.Dz2jRun
public import LeanTheory.Theory.Life.Gen.Dz2mk0Run
public import LeanTheory.Theory.Life.Gen.Dz2mk1Run

/-!
# The register circuit: one definition for all its operations

The generated certificates of the register circuit (reports `R-28`, `R-29`) each carry their own
copy of the circuit at rest: `dz2gRest` (decrement, every `k ≥ 2`), `dz2mk1Rest` (`k = 1`),
`dz2mk0Rest` (`k = 0`), `dz2jRest` (increment). They are the same configuration
(`dz2mk0Rest_eq`, `dz2mk1Rest_eq`, `dz2jRest_eq`), so all four operations act on `dz2gRest`.
-/

set_option linter.style.longLine false

@[expose] public section

namespace LeanTheory.Life

open Finset

set_option maxRecDepth 100000 in
/-- The circuit of the zero test at `k = 0` is `dz2gRest`. -/
theorem dz2mk0Rest_eq : dz2mk0Rest = dz2gRest := by
  simp only [dz2mk0Rest, dz2gRest, show dz2mk0R0 = dz2gR0 from rfl, show dz2mk0R1 = dz2gR1 from rfl, show dz2mk0R2 = dz2gR2 from rfl, show dz2mk0R3 = dz2gR3 from rfl, show dz2mk0R4 = dz2gR4 from rfl, show dz2mk0R5 = dz2gR5 from rfl, show dz2mk0R6 = dz2gR6 from rfl, show dz2mk0R7 = dz2gR7 from rfl, show dz2mk0R8 = dz2gR8 from rfl, show dz2mk0R9 = dz2gR9 from rfl, show dz2mk0R10 = dz2gR10 from rfl, show dz2mk0R11 = dz2gR11 from rfl, show dz2mk0R12 = dz2gR12 from rfl, show dz2mk0R13 = dz2gR13 from rfl, show dz2mk0R14 = dz2gR14 from rfl, show dz2mk0R15 = dz2gR15 from rfl, show dz2mk0R16 = dz2gR16 from rfl, show dz2mk0R17 = dz2gR17 from rfl, show dz2mk0R18 = dz2gR18 from rfl, show dz2mk0R19 = dz2gR19 from rfl, show dz2mk0R20 = dz2gR20 from rfl, show dz2mk0R21 = dz2gR21 from rfl, show dz2mk0R22 = dz2gR22 from rfl, show dz2mk0R23 = dz2gR23 from rfl, show dz2mk0R24 = dz2gR24 from rfl, show dz2mk0R25 = dz2gR25 from rfl, show dz2mk0R26 = dz2gR26 from rfl, show dz2mk0R27 = dz2gR27 from rfl]
  ac_rfl

set_option maxRecDepth 100000 in
/-- The circuit of the zero test at `k = 1` is `dz2gRest`. -/
theorem dz2mk1Rest_eq : dz2mk1Rest = dz2gRest := by
  simp only [dz2mk1Rest, dz2gRest, show dz2mk1R0 = dz2gR0 from rfl, show dz2mk1R1 = dz2gR1 from rfl, show dz2mk1R2 = dz2gR2 from rfl, show dz2mk1R3 = dz2gR3 from rfl, show dz2mk1R4 = dz2gR4 from rfl, show dz2mk1R5 = dz2gR5 from rfl, show dz2mk1R6 = dz2gR6 from rfl, show dz2mk1R7 = dz2gR7 from rfl, show dz2mk1R8 = dz2gR8 from rfl, show dz2mk1R9 = dz2gR9 from rfl, show dz2mk1R10 = dz2gR10 from rfl, show dz2mk1R11 = dz2gR11 from rfl, show dz2mk1R12 = dz2gR12 from rfl, show dz2mk1R13 = dz2gR13 from rfl, show dz2mk1R14 = dz2gR14 from rfl, show dz2mk1R15 = dz2gR15 from rfl, show dz2mk1R16 = dz2gR16 from rfl, show dz2mk1R17 = dz2gR17 from rfl, show dz2mk1R18 = dz2gR18 from rfl, show dz2mk1R19 = dz2gR19 from rfl, show dz2mk1R20 = dz2gR20 from rfl, show dz2mk1R21 = dz2gR21 from rfl, show dz2mk1R22 = dz2gR22 from rfl, show dz2mk1R23 = dz2gR23 from rfl, show dz2mk1R24 = dz2gR24 from rfl, show dz2mk1R25 = dz2gR25 from rfl, show dz2mk1R26 = dz2gR26 from rfl, show dz2mk1R27 = dz2gR27 from rfl]
  ac_rfl

set_option maxRecDepth 100000 in
/-- The circuit of the increment is `dz2gRest`. -/
theorem dz2jRest_eq : dz2jRest = dz2gRest := by
  simp only [dz2jRest, dz2gRest, show dz2jR0 = dz2gR0 from rfl, show dz2jR1 = dz2gR1 from rfl, show dz2jR2 = dz2gR2 from rfl, show dz2jR3 = dz2gR3 from rfl, show dz2jR4 = dz2gR4 from rfl, show dz2jR5 = dz2gR5 from rfl, show dz2jR6 = dz2gR6 from rfl, show dz2jR7 = dz2gR7 from rfl, show dz2jR8 = dz2gR8 from rfl, show dz2jR9 = dz2gR9 from rfl, show dz2jR10 = dz2gR10 from rfl, show dz2jR11 = dz2gR11 from rfl, show dz2jR12 = dz2gR12 from rfl, show dz2jR13 = dz2gR13 from rfl, show dz2jR14 = dz2gR14 from rfl, show dz2jR15 = dz2gR15 from rfl, show dz2jR16 = dz2gR16 from rfl, show dz2jR17 = dz2gR17 from rfl, show dz2jR18 = dz2gR18 from rfl, show dz2jR19 = dz2gR19 from rfl, show dz2jR20 = dz2gR20 from rfl, show dz2jR21 = dz2gR21 from rfl, show dz2jR22 = dz2gR22 from rfl, show dz2jR23 = dz2gR23 from rfl, show dz2jR24 = dz2gR24 from rfl, show dz2jR25 = dz2gR25 from rfl, show dz2jR26 = dz2gR26 from rfl, show dz2jR27 = dz2gR27 from rfl]

end LeanTheory.Life
