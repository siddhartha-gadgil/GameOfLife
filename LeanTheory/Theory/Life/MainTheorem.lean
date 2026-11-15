/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncRegion
public import LeanTheory.Theory.Life.ActivationHalt
public import LeanTheory.Theory.Life.Simulation
public import LeanTheory.Theory.Life.StartFamily
public import LeanTheory.Theory.Computability.CounterMachineSingleHalt

/-!
# The main theorem, conditional on the step lemmas

Research notes `N-21`, `N-22`: the assembly of the simulator of a counter program in Life from
its step lemmas, and the resulting undecidability of `EverAlive`.

* **The invariant** `MInv p s`: `InvM p s` and every register of the program ready
  (`RegS.Ready`). The start states satisfy it (`startM_minv`).
* **The `inc` step with its bookkeeping** (`inc_step_full`): `inc_step_of_plan` with two more
  conclusions, a positive duration and the other registers simply later; with it the `inc` step
  keeps `MInv` (`inc_step_minv`).
* **What is still open** is bundled in `MachineSteps p`: the separation facts of the `inc`
  activations (`incSep`; the region facts are discharged by `IncPlan.region`), the `decJz` step
  (`dec`, stated in its expected form), and the separation facts of the halt activation of the
  unique `halt` (`haltSep`).
* **The simulator** `simulatorOf` (`S = MState`, `proj = cfg`, `enc = encM p`,
  `cH = haltCellC p`, `region = machRegion p`, the duration and the next state chosen from the
  step lemmas), and the **conditional main theorems**:
  `not_computablePred_everAlive_of_machineSteps` (for a given program with an undecidable halting
  problem) and `exists_not_computablePred_everAlive` (some cell `c` for which `EverAlive c` is
  undecidable, given `MachineSteps p` for every well-formed program with a single `halt`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The `inc` step with its bookkeeping -/

/-- **The `inc` step, from an activation plan, with its bookkeeping**: as `inc_step_of_plan`, and
moreover the duration is positive and every register other than `r` is the old register later by
the duration (part of the statement of `inc_step_of_plan`). -/
theorem inc_step_full {p : Program} {r : ℕ} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hins : p[s.pc]? = some (.inc r)) (hready : (s.reg r).Ready) (P : IncPlan p s.pc r)
    (hv : P.Valid) (hsep : IncSep P ((s.reg r).later 930))
    (hreg : IncRegion P ((s.reg r).later 930)) :
    ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ (∀ r', r' ≠ r → s'.reg r' = (s.reg r').later τ) ∧
      p.step s.cfg = some s'.cfg ∧ InvM p s' ∧ (s'.reg r).Ready ∧
      conway.evolve τ (encM p s) = encM p s' ∧
      ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p :=
  inc_step_of_plan hp s hinv hins hready P hv hsep hreg

/-! ### The invariant of the simulator -/

/-- **The invariant of the simulator**: `InvM` and every register of the program ready. -/
def MInv (p : Program) (s : MState) : Prop :=
  InvM p s ∧ ∀ r < numRegs p, (s.reg r).Ready

/-- The start states satisfy the invariant (for a well-formed program). -/
theorem startM_minv {p : Program} (hp : p.WellFormed) (n : ℕ) : MInv p (startM n) :=
  ⟨startM_inv hp.length_pos n, fun _ _ => ⟨RegS.inv_ofNat _, rfl, QBeforeL.nil 29 0⟩⟩

/-- **A good step** from `s`: a positive duration `ts.1` and a next state `ts.2` with the
invariant, simulating the step of the counter machine inside the region of the machine. -/
def GoodStep (p : Program) (s : MState) (ts : ℕ × MState) : Prop :=
  0 < ts.1 ∧ p.step s.cfg = some ts.2.cfg ∧ MInv p ts.2 ∧
    conway.evolve ts.1 (encM p s) = encM p ts.2 ∧
    ∀ j ≤ ts.1, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p

/-- **The `inc` step keeps the invariant**, given the separation facts of its activation plan
(the region facts are discharged by `IncPlan.region`). -/
theorem inc_step_minv {p : Program} {r : ℕ} (hp : p.WellFormed) (s : MState) (hinv : MInv p s)
    (hins : p[s.pc]? = some (.inc r)) (hsep : IncSep (incPlan p s.pc r) ((s.reg r).later 930)) :
    ∃ ts, GoodStep p s ts := by
  obtain ⟨τ, s', hτ, hoth, hstep, hinv', hrdy, hev, hsub⟩ := inc_step' hp s hinv.1 hins
    (hinv.2 r (lt_numRegs_of_inc hins)) hsep
  refine ⟨(τ, s'), hτ, hstep, ⟨hinv', fun r' hr' => ?_⟩, hev, hsub⟩
  by_cases he : r' = r
  · exact he ▸ hrdy
  · rw [hoth r' he]
    exact (hinv.2 r' hr').later τ

/-! ### What is still open -/

/-- **The step lemmas still to be proved** for the program `p`, as hypotheses. -/
structure MachineSteps (p : Program) : Prop where
  /-- The separation facts of the activation plan of every `inc` step from a state with the
  invariant (the hypothesis of `inc_step'`; the region facts are discharged). -/
  incSep : ∀ (s : MState) (r : ℕ), MInv p s → p[s.pc]? = some (.inc r) →
    IncSep (incPlan p s.pc r) ((s.reg r).later 930)
  /-- **The `decJz` step**: from a state with the invariant and the instruction `decJz r z`, the
  machine evolves, in a positive number of generations and inside the region of the machine,
  into the encoding of a state with the invariant whose configuration is the next one of the
  counter machine. -/
  dec : ∀ (s : MState) (r z : ℕ), MInv p s → p[s.pc]? = some (.decJz r z) →
    ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ p.step s.cfg = some s'.cfg ∧ MInv p s' ∧
      conway.evolve τ (encM p s) = encM p s' ∧
      ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p
  /-- The separation facts of the halt activation of the unique `halt`, the last instruction. -/
  haltSep : HaltSep p (p.length - 1)

/-- The step of a `halt` instruction is `none`. -/
theorem step_of_halt {p : Program} {c : Cfg} (h : p[c.pc]? = some .halt) : p.step c = none := by
  rw [Program.step]
  rw [h]
  rfl

/-- **Every step of the counter machine from a state with the invariant is a good step.** -/
theorem exists_goodStep {p : Program} (hp : p.WellFormed) (M : MachineSteps p) {s : MState}
    (hinv : MInv p s) {c' : Cfg} (hstep : p.step s.cfg = some c') : ∃ ts, GoodStep p s ts := by
  rcases hi : p[s.pc]? with _ | ins
  · rw [List.getElem?_eq_none_iff] at hi
    exact absurd hinv.1.1 (by omega)
  · cases ins with
    | inc r =>
      exact inc_step_minv hp s hinv hi (M.incSep s r hinv hi)
    | decJz r z =>
      obtain ⟨τ, s', h⟩ := M.dec s r z hinv hi
      exact ⟨(τ, s'), h⟩
    | halt =>
      rw [step_of_halt (c := s.cfg) hi] at hstep
      exact absurd hstep (by simp)

/-- The program counter of a `halt` of a program with a single `halt` is the last one. -/
theorem pc_of_halt {p : Program} (hs : p.SingleHalt) {a : ℕ} (h : p[a]? = some .halt) :
    a = p.length - 1 := by
  have hlt : a < p.length := (List.getElem?_eq_some_iff.1 h).1
  by_contra hne
  exact hs a (by omega) h

/-! ### The simulator -/

open Classical in
/-- The duration and the next state: a good step when there is one, else `(1, s)`. -/
noncomputable def nextStep (p : Program) (s : MState) : ℕ × MState :=
  if h : ∃ ts, GoodStep p s ts then h.choose else (1, s)

/-- The chosen step is good whenever some step is. -/
theorem nextStep_good {p : Program} {s : MState} (h : ∃ ts, GoodStep p s ts) :
    GoodStep p s (nextStep p s) := by
  rw [nextStep, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- The chosen duration is positive. -/
theorem nextStep_pos (p : Program) (s : MState) : 0 < (nextStep p s).1 := by
  by_cases h : ∃ ts, GoodStep p s ts
  · exact (nextStep_good h).1
  · rw [nextStep, dite_eq_right_of_eq_false (eq_false h)]
    exact Nat.one_pos

/-- **The simulator of a well-formed program with a single `halt`**, from its step lemmas. -/
noncomputable def simulatorOf {p : Program} (hp : p.WellFormed) (hs : p.SingleHalt)
    (M : MachineSteps p) : Simulator p where
  S := MState
  proj := MState.cfg
  enc := encM p
  Inv := MInv p
  next s := (nextStep p s).2
  dur s := (nextStep p s).1
  region := machRegion p
  cH := haltCellC p
  cH_notMem := haltCellC_notMem p
  dur_pos := nextStep_pos p
  step s c' hinv hstep := by
    obtain ⟨_, h1, h2, h3, h4⟩ := nextStep_good (exists_goodStep hp M hinv hstep)
    exact ⟨Option.some.inj (h1.symm.trans hstep), h2, h3, h4⟩
  halt s hinv hstep := by
    have ha := halt_of_step_none hinv.1 hstep
    exact halt_everAlive hp s hinv.1 hstep (pc_of_halt hs ha ▸ M.haltSep)

end LP

open LP

/-! ### The main theorems -/

/-- **The conditional main theorem**: for a well-formed counter program `p` with a single `halt`
and an undecidable halting problem, given the step lemmas `MachineSteps p`, it is undecidable
whether the halt cell `haltCellC p` is ever alive in the evolution of a finite configuration. -/
theorem not_computablePred_everAlive_of_machineSteps (p : Program) (hp : p.WellFormed)
    (hs : p.SingleHalt) (M : MachineSteps p)
    (hP : ¬ ComputablePred fun n : ℕ => p.Halts (Cfg.init n)) :
    ¬ ComputablePred fun w : WindowData => EverAlive (haltCellC p) w.cells := by
  obtain ⟨f, hf, hcells⟩ := exists_startFamily p
  exact not_computablePred_everAlive_of_simulator (simulatorOf hp hs M) hP startM startM_cfg
    (startM_minv hp) f hf hcells

/-- **The final corollary**: if every well-formed counter program with a single `halt` has its
step lemmas, then there is a cell `c` such that whether `c` is ever alive in the evolution of a
given finite configuration is undecidable. -/
theorem exists_not_computablePred_everAlive
    (h : ∀ p : Program, p.WellFormed → p.SingleHalt → MachineSteps p) :
    ∃ c : Cell, ¬ ComputablePred fun w : WindowData => EverAlive c w.cells := by
  obtain ⟨p, hp, hs, hP⟩ := exists_program_halts_not_computable_single
  exact ⟨haltCellC p, not_computablePred_everAlive_of_machineSteps p hp hs (h p hp hs) hP⟩

end LeanTheory.Life
