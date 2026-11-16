/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepMov4
public import LeanTheory.Theory.Life.DecSepThrMain
public import LeanTheory.Theory.Life.DecSepIMain
public import LeanTheory.Theory.Life.DecSepXMain
public import LeanTheory.Theory.Life.DecSepAMain
public import LeanTheory.Theory.Life.FinalTheorem

/-!
# The separation facts of every `decJz` activation, and the undecidability of `EverAlive`

Research note `N-22`. The 37 fields of `DecSepRest` are collected from the five groups proved
separately (`dsepM_fields`, `dsepT_fields8`, `dsepA_fields`, `dsepX_fields`, `dsepI_fields`), which
discharges the last hypothesis of the undecidability corollary.

* `dsep_rest`: `DecSepRest` at every `decJz` instruction of a well-formed program;
* `exists_not_computablePred_everAlive'`: **some cell's `EverAlive` is not computable**.
-/

@[expose] public section

namespace LeanTheory.Life

open LeanTheory.Computability

namespace LP

/-- **The remaining separation facts of every `decJz` activation.** -/
theorem dsep_rest {p : Program} (hp : p.WellFormed) :
    ∀ i r z, p[i]? = some (.decJz r z) → DecSepRest p i r z := by
  intro i r z hi
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14⟩ := dsepM_fields hp hi
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := dsepT_fields8 hp hi
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := dsepA_fields hp hi
  obtain ⟨x1, x2, x3⟩ := dsepX_fields hp hi
  obtain ⟨l1, l2, l3, l4⟩ := dsepI_fields hp hi
  exact { flyC := m1, sideC := m2, chainC := m3, cpC := m4, flyN := m5, flyZ := m6,
          winN := m7, winZ := m8, unpN := m9, unpZ := m10, ansFlyN := m11, ansFlyZ := m12,
          capN := m13, capZ := m14,
          nQ1b := t1, nQ2 := t2, nQ3a := t3, nQ3b := t4,
          zQ1b := t5, zQ2 := t6, zQ3a := t7, zQ3b := t8,
          nQN := a1, nQF := a2, zQZ := a3, zQF := a4,
          nA2a := a5, nA2b := a6, zA2a := a7, zA2b := a8,
          nThr := x1, zThr := x2, zGate := x3,
          nIdle := l1, nLane := l2, zIdle := l3, zLane := l4 }

/-- **Undecidability of the Game of Life.** There is a cell `c` such that it is not computable,
from the finite initial pattern, whether `c` is alive at some generation. -/
theorem exists_not_computablePred_everAlive' :
    ∃ c : Cell, ¬ ComputablePred fun w : WindowData => EverAlive c w.cells :=
  exists_not_computablePred_everAlive_of_decSepRest fun _ hp _ => dsep_rest hp

end LP

end LeanTheory.Life
