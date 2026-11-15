/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Diagonal
public import LeanTheory.Theory.Life.Gen.Dz2gData
public import LeanTheory.Theory.Life.Gen.Dz2jData

/-!
# The two salvos of the register machine

The pulling salvo of the zero test `DZ2` (`regPull`: `dz2gPullS`, from `dz2gAll`) and the
pushing salvo of the increment (`regPush`: `dz2jPullS`, from `dz2jAll`), as `Salvo`s of
`Theory/Life/Diagonal` (research note `N-20`), and parameters of a register diagonal for which
both fit (at every phase, `Theory/Life/SalvoPhases`), with the gap `30` between salvos
(`regParams_good`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- A reaction ending in a still life can be prolonged. -/
theorem Reaction.extend_still {X Y : Finset Cell} {n : ℕ} {B : Set Cell}
    (h : Reaction X Y n (fun _ => B)) (hY : IsStillLife Y) (m : ℕ) :
    Reaction X Y (n + m) (fun _ => B) := by
  refine ⟨by rw [add_comm, Rule.evolve_add, h.evolve_eq, hY.evolve], fun i hi => ?_⟩
  by_cases hin : i ≤ n
  · exact h.subset i hin
  · rw [show i = (i - n) + n by omega, Rule.evolve_add, h.evolve_eq, hY.evolve, ← h.evolve_eq]
    exact h.subset n le_rfl

/-- The pulling salvo: moves the block one cell back (32 generations at position `0`). -/
def regPull : Salvo where
  S := dz2gPullS
  d := -1
  n := 32
  a := -1
  b := 9
  lo := 5
  hi := 9
  za := -1
  zb := 14
  zlo := 4
  zhi := 12
  four := dz2gPullS_four
  box := dz2gPullS_box
  hz := dz2gPullHz.extend_still (counter_isStillLife _) 3
  hhi := by norm_num

/-- The pushing salvo: moves the block one cell forward (36 generations at position `0`). -/
def regPush : Salvo where
  S := dz2jPullS
  d := 1
  n := 36
  a := -6
  b := 10
  lo := -7
  hi := 9
  za := -6
  zb := 15
  zlo := -7
  zhi := 15
  four := dz2jPullS_four
  box := dz2jPullS_box
  hz := dz2jPullHz
  hhi := by norm_num

/-- Parameters of a register diagonal carrying pulling and pushing salvos. -/
def regParams : DiagParams where
  A := -6
  B := 10
  ZA := -6
  N := 40
  g := 30
  U₁ := -21
  U₂ := 23

/-- The parameters are good: the gap `30` is enough for both salvos. -/
theorem regParams_good : regParams.Good := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [regParams]

end LeanTheory.Life
