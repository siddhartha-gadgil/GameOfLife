/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepCross2
public import LeanTheory.Theory.Life.MainTheorem
public import LeanTheory.Theory.Life.HaltSepProof

/-!
# The separation facts of every `inc` activation

Research note `N-22`. **`IncSep` holds for the plan of every `inc` instruction of a well-formed
program** (`isep2_incSep`), for a ready register at the end of the body: the field `incSep` of
`MachineSteps` is discharged (`isep_machineSteps_inc`), and `MachineSteps p` follows from the
`decJz` step alone (`isep2_machineSteps`, with `hsep_haltSep` for the unique `halt`).

The fields, with the lemmas that prove them (the flight, gate, `RF_J` and increment fields in a
strong form, far from every piece of the machine):

* `sepC`, `sepR`, `sepM`: `isep_sepC`, `isep_sepR`, `isep_sepM` (`ActivationIncSepProof`);
* `flyC`, `flyR`, `outC`: `isep2_flyC`, `isep2_flyR`, `isep2_outC` (`ActivationIncSepProof4`);
* `entC`, `entR`: `incPlan_entC`, `incPlan_entR` (`ActivationIncEntrySep`);
* `flyM`: `isep2_flyM` (`ActivationIncSepProof3`);
* `gate`, `fl1`, `rf`, `fl2`, `inc`: `isep2_gate`, `isep2_fl1`, `isep2_rf`, `isep2_fl2`,
  `isep2_incRun` (`ActivationIncSepProof2`);
* `modLane`, `grpLane`, `earlyLane`, `lanes`, `laneBody`, `laneAct`: `incPlan_laneSep`
  (`LaneSep2`);
* `threads`: `isep2_threads` (`ActivationIncSepCross2`, with the timing `isep2_m4C`);
* `idle`: `isep2_idle` (`ActivationIncSepThreads`);
* `body`: `isep2_body` (`ActivationIncSepUnit`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-- **The separation facts of the activation of every `inc` instruction** of a well-formed
program, for a register ready at the end of the body. -/
theorem isep2_incSep (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {R0 : RegS}
    (hR : R0.Ready) : IncSep (incPlan p i r) R0 := by
  have hv := incPlan_valid hp hins
  have hL := incPlan_laneSep hp hins hR
  have hr := lt_numRegs_of_inc hins
  exact
    { sepC := isep_sepC hp hins
      sepR := isep_sepR hp hins
      sepM := isep_sepM hp hins
      flyC := fun j h1 h2 h hh => isep2_flyC hp hins j h1 (by omega) h (hv.memC h hh)
      entC := incPlan_entC hp hins
      outC := fun j hj h hh => isep2_outC hp (i + 1) j hj h (hv.memC h hh)
      flyR := fun j h1 h2 h hh => isep2_flyR hp hins j h1 (by omega) h (hv.memI h hh)
      entR := incPlan_entR hins
      flyM := fun j h1 h2 h hh => isep2_flyM hp hins j h1 (by omega) h (hv.memI h hh)
      gate := fun h hh hne => isep2_gate hp r h (hv.memI h hh) hne
      fl1 := fun j h1 h2 h hh => isep2_fl1 hp r hv.TgE j h1 (by omega) h (hv.memI h hh)
      rf := fun h hh hne => isep2_rf hp r h (hv.memI h hh) hne
      fl2 := fun j h1 h2 h hh => isep2_fl2 hp r hv.TgE j h1 (by omega) h (hv.memI h hh)
      modLane := hL.modLane
      grpLane := hL.grpLane
      inc := fun R hR' j _ h hh hn => isep2_incRun hp hr hR' j h (hv.memI h hh) hn
      earlyLane := hL.earlyLane
      threads := isep2_threads hp hins hR
      idle := isep2_idle hp hins hR
      body := isep2_body hp hins
      lanes := hL.lanes
      laneBody := hL.laneBody
      laneAct := hL.laneAct }

/-- **The field `incSep` of `MachineSteps`** for every well-formed program. -/
theorem isep_machineSteps_inc (hp : p.WellFormed) :
    ∀ (s : MState) (r : ℕ), MInv p s → p[s.pc]? = some (.inc r) →
      IncSep (incPlan p s.pc r) ((s.reg r).later 930) :=
  fun _ r hinv hins => isep2_incSep hp hins ((hinv.2 r (lt_numRegs_of_inc hins)).later 930)

/-- **`MachineSteps` from the `decJz` step alone**: for a well-formed program with a single
`halt`, the separation facts of the `inc` activations (`isep_machineSteps_inc`) and of the halt
activation (`hsep_haltSep`) are proved. -/
theorem isep2_machineSteps (hp : p.WellFormed) (hs : p.SingleHalt)
    (hdec : ∀ (s : MState) (r z : ℕ), MInv p s → p[s.pc]? = some (.decJz r z) →
      ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ p.step s.cfg = some s'.cfg ∧ MInv p s' ∧
        conway.evolve τ (encM p s) = encM p s' ∧
        ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p) :
    MachineSteps p :=
  ⟨isep_machineSteps_inc hp, hdec, hsep_haltSep hp hs⟩

end LP

end LeanTheory.Life
