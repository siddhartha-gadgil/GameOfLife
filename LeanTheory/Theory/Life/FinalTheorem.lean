/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepMain
public import LeanTheory.Theory.Life.DecSepMain

/-!
# Assembling the undecidability corollary

Research note `N-22`. The simulator of every well-formed single-halt counter machine is assembled
from the proved `inc` step (`isep_machineSteps_inc`), the halt activation (`hsep_haltSep`) and the
`decJz` step (`dsep_machineSteps_dec`), which takes the remaining separation fields of the `decJz`
activations (`DecSepRest`) as a hypothesis. That hypothesis is proved for every well-formed
program in `DecSepAll.lean` (`dsep_rest`), which states the unconditional theorem
`exists_not_computablePred_everAlive'`.

* `machineSteps_of_decSepRest`: `MachineSteps p` from `DecSepRest` at every `decJz` instruction;
* `exists_not_computablePred_everAlive_of_decSepRest`: the undecidability of `EverAlive` for some
  cell, from `DecSepRest` for every well-formed single-halt program.
-/

@[expose] public section

namespace LeanTheory.Life

open LeanTheory.Computability

namespace LP

/-- **The simulator steps**, given the remaining separation fields of the `decJz` activations. -/
theorem machineSteps_of_decSepRest {p : Program} (hp : p.WellFormed) (hs : p.SingleHalt)
    (hrest : ∀ i r z, p[i]? = some (.decJz r z) → DecSepRest p i r z) : MachineSteps p :=
  isep2_machineSteps hp hs (dsep_machineSteps_dec hp hrest)

/-- **Undecidability of `EverAlive`**, given the remaining separation fields of the `decJz`
activations of every well-formed single-halt program. -/
theorem exists_not_computablePred_everAlive_of_decSepRest
    (h : ∀ p : Program, p.WellFormed → p.SingleHalt →
      ∀ i r z, p[i]? = some (.decJz r z) → DecSepRest p i r z) :
    ∃ c : Cell, ¬ ComputablePred fun w : WindowData => EverAlive c w.cells :=
  exists_not_computablePred_everAlive fun p hp hs =>
    machineSteps_of_decSepRest hp hs (h p hp hs)

end LP

end LeanTheory.Life
