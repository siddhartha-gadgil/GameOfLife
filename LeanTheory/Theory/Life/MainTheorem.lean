/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncPlan
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
* **What is still open** is bundled in `MachineSteps p`: the separation and region facts of the
  `inc` activations (`incSep`), the `decJz` step (`dec`, stated in its expected form), and the
  separation facts of the halt activation of the unique `halt` (`haltSep`).
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
the duration. (The proof is that of `inc_step_of_plan`, whose statement hides these facts.) -/
theorem inc_step_full {p : Program} {r : ℕ} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hins : p[s.pc]? = some (.inc r)) (hready : (s.reg r).Ready) (P : IncPlan p s.pc r)
    (hv : P.Valid) (hsep : IncSep P ((s.reg r).later 930))
    (hreg : IncRegion P ((s.reg r).later 930)) :
    ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ (∀ r', r' ≠ r → s'.reg r' = (s.reg r').later τ) ∧
      p.step s.cfg = some s'.cfg ∧ InvM p s' ∧ (s'.reg r).Ready ∧
      conway.evolve τ (encM p s) = encM p s' ∧
      ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p := by
  have hr := lt_numRegs_of_inc hins
  have hLM := machPieces_sep p hp
  have hinvR : ∀ r' ∈ List.range (numRegs p), (s.reg r').Inv :=
    fun r' h => hinv.2.2.1 r' (List.mem_range.1 h)
  have hlate := hv.late
  have hTend : P.Tend % 30 = 0 := by
    have := hv.T0cE
    simp only [IncPlan.Tend, IncPlan.Tc]
    omega
  -- the body, with every register idle
  have S1 := (body_window hp hv.memB hsep.body).par
    (regsOn_reaction p s.reg 930 (List.range (numRegs p)) List.nodup_range hinvR
      fun j _ r₁ h₁ r₂ h₂ hne => (hsep.lanes r₁ (List.mem_range.1 h₁) r₂ (List.mem_range.1 h₂)
        hne).mono (regStrip_subset (hinvR r₁ h₁) p r₁ j) (regStrip_subset (hinvR r₂ h₂) p r₂ j))
    fun j _ a ha b hb => by
      obtain ⟨r', hr', hb⟩ := mem_stripsOn.1 hb
      exact hsep.laneBody r' (List.mem_range.1 hr') a ha b
        (regStrip_subset (hinvR r' hr') p r' j hb)
  -- the two threads inside the idle machine, with the other registers idle
  have hC := P.contThread hp hv hsep
  obtain ⟨R', hval, hrdy, hI⟩ := P.incThread hp hv (hready.later 930) hsep
  have hCI := hC.par hI hsep.threads
  set A := dd P.LCraw ++ dd P.LIraw with hAdef
  have hA : ∀ x ∈ A, x ∈ machPieces p := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hv.memC x (mem_dd.1 h)
    · exact hv.memI x (mem_dd.1 h)
  have hCI' : Reaction (piecesAt A 2010 ∪ ((unitWL p s.pc incDWL).cells 2010 ∪
        ((unitWL p s.pc incRWL).cells 2010 ∪ regAt p r ((s.reg r).later 930))))
      (piecesAt A (2010 + (P.Tend - 2010)) ∪ (ctrlAt p (s.pc + 1) ∪ regAt p r R'))
      (P.Tend - 2010) (fun j => P.contFoot j ∪ P.incFoot ((s.reg r).later 930) j) := by
    refine hCI.congrPQ ?_ ?_
    · rw [hAdef, piecesAt_append]
      ac_rfl
    · rw [hAdef, piecesAt_append, show 2010 + (P.Tend - 2010) = P.Tend by omega]
      ac_rfl
  have W2 := window_mem hLM hA 2010 (P.Tend - 2010) hCI' fun j hj g hg hn =>
    hsep.idle j hj g hg fun h => hn (by
      rcases List.mem_append.1 h with h | h
      · exact List.mem_append_left _ (mem_dd.2 h)
      · exact List.mem_append_right _ (mem_dd.2 h))
  set others := (List.range (numRegs p)).filter (fun r' => r' ≠ r) with hoth
  have hothR : ∀ r' ∈ others, r' < numRegs p ∧ r' ≠ r := fun r' h => by
    simp only [hoth, List.mem_filter, List.mem_range, ne_eq, decide_eq_true_eq] at h
    exact h
  have hinvO : ∀ r' ∈ others, ((s.reg r').later 930).Inv :=
    fun r' h => (hinv.2.2.1 r' (hothR r' h).1).later 930
  have S2 := W2.par (regsOn_reaction p (fun r' => (s.reg r').later 930) (P.Tend - 2010) others
      (List.nodup_range.filter _) hinvO
      fun j _ r₁ h₁ r₂ h₂ hne => (hsep.lanes r₁ (hothR r₁ h₁).1 r₂ (hothR r₂ h₂).1 hne).mono
        (regStrip_subset (hinvO r₁ h₁) p r₁ j) (regStrip_subset (hinvO r₂ h₂) p r₂ j))
    fun j hj a ha b hb => by
      obtain ⟨r', hr', hb⟩ := mem_stripsOn.1 hb
      exact hsep.laneAct j hj r' (hothR r' hr').1 (hothR r' hr').2 a ha b
        (regStrip_subset (hinvO r' hr') p r' j hb)
  have e12 : piecesAt (machPieces p) (1080 + 930) ∪
        ((unitWL p s.pc incDWL).cells 2010 ∪ (unitWL p s.pc incRWL).cells 2010) ∪
        regsOn p (fun r' => (s.reg r').later 930) (List.range (numRegs p)) =
      piecesAt (machPieces p) 2010 ∪ ((unitWL p s.pc incDWL).cells 2010 ∪
        ((unitWL p s.pc incRWL).cells 2010 ∪ regAt p r ((s.reg r).later 930))) ∪
        regsOn p (fun r' => (s.reg r').later 930) others := by
    rw [regsOn_split _ _ hr, show 1080 + 930 = 2010 by norm_num]
    ac_rfl
  have S := S1.seq_eq e12 S2
  set τ := 930 + (P.Tend - 2010) with hτ
  set s' : MState := ⟨s.pc + 1, s.T + τ, incRegs s r R' τ⟩ with hs'
  have estart : encM p s = piecesAt (machPieces p) 1080 ∪ ctrlAt p s.pc ∪
      regsOn p s.reg (List.range (numRegs p)) := by
    rw [encM, machAt, regsAt_eq, piecesAt_mod _ (show s.T % 30 = 1080 % 30 by
      have := hinv.2.1; omega)]
  have eend : encM p s' = piecesAt (machPieces p) (2010 + (P.Tend - 2010)) ∪
      (ctrlAt p (s.pc + 1) ∪ regAt p r R') ∪
        regsOn p (fun r' => ((s.reg r').later 930).later (P.Tend - 2010)) others := by
    rw [encM, machAt, regsAt_eq, regsOn_split _ _ hr]
    have h1 : piecesAt (machPieces p) s'.T = piecesAt (machPieces p) (2010 + (P.Tend - 2010)) :=
      piecesAt_mod _ (by have := hinv.2.1; change (s.T + τ) % 30 = _; omega)
    have h2 : regsOn p s'.reg others =
        regsOn p (fun r' => ((s.reg r').later 930).later (P.Tend - 2010)) others :=
      regsOn_congr fun r' h => by
        change incRegs s r R' τ r' = _
        rw [incRegs, Function.update_of_ne (hothR r' h).2, RegS.later_later, hτ]
    have h3 : s'.reg r = R' := by
      change incRegs s r R' τ r = R'
      rw [incRegs, Function.update_self]
    rw [h1, h2, h3]
    simp only [union_assoc]
    rfl
  refine ⟨τ, s', by omega, fun r' hne => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change incRegs s r R' τ r' = _
    rw [incRegs, Function.update_of_ne hne]
  · -- the counter machine
    rw [Program.step]
    change (p[s.pc]?.bind fun ins => ins.exec s.cfg) = _
    rw [hins, Option.bind_some]
    change some (⟨s.pc + 1, Function.update (fun r' => (s.reg r').val) r ((s.reg r).val + 1)⟩ :
      Cfg) = some ⟨s.pc + 1, fun r' => (incRegs s r R' τ r').val⟩
    refine congrArg some (Cfg.ext rfl (funext fun r' => ?_))
    by_cases he : r' = r
    · subst he
      dsimp only
      rw [Function.update_self, incRegs, Function.update_self, hval, RegS.val_later]
    · dsimp only
      rw [Function.update_of_ne he, incRegs, Function.update_of_ne he, RegS.val_later]
  · -- the invariant
    refine ⟨succ_lt_of_inc hp hins, ?_, fun r' hr' => ?_, fun r' hr' => ?_⟩
    · have := hinv.2.1
      change (s.T + τ) % 30 = 0
      omega
    · change (incRegs s r R' τ r').Inv
      by_cases he : r' = r
      · subst he
        rw [incRegs, Function.update_self]
        exact hrdy.1
      · rw [incRegs, Function.update_of_ne he]
        exact (hinv.2.2.1 r' hr').later τ
    · have he : r' ≠ r := by omega
      change (incRegs s r R' τ r').val = 0
      rw [incRegs, Function.update_of_ne he, RegS.val_later]
      exact hinv.2.2.2 r' hr'
  · change (incRegs s r R' τ r).Ready
    rw [incRegs, Function.update_self]
    exact hrdy
  · rw [estart, eend]
    exact S.evolve_eq
  · intro j hj
    rw [estart]
    refine (S.subset j hj).trans ?_
    have hstrips : ∀ (reg : ℕ → RegS) (l : List ℕ) (k : ℕ), (∀ r' ∈ l, r' < numRegs p) →
        (∀ r' ∈ l, (reg r').Inv) → stripsOn p reg l k ⊆ machRegion p := by
      intro reg l k hl hi x hx
      obtain ⟨r', hr', hx⟩ := mem_stripsOn.1 hx
      exact hreg.lanes r' (hl r' hr') (regStrip_subset (hi r' hr') p r' k hx)
    split_ifs with hj1
    · refine Set.union_subset (Set.union_subset hreg.pieces hreg.body) ?_
      exact hstrips _ _ _ (fun r' h => List.mem_range.1 h) hinvR
    · refine Set.union_subset (Set.union_subset hreg.pieces (hreg.threads _ (by omega))) ?_
      exact hstrips _ _ _ (fun r' h => (hothR r' h).1) hinvO

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

/-- **The `inc` step keeps the invariant**, given the separation and region facts of its
activation plan. -/
theorem inc_step_minv {p : Program} {r : ℕ} (hp : p.WellFormed) (s : MState) (hinv : MInv p s)
    (hins : p[s.pc]? = some (.inc r)) (hsep : IncSep (incPlan p s.pc r) ((s.reg r).later 930))
    (hreg : IncRegion (incPlan p s.pc r) ((s.reg r).later 930)) :
    ∃ ts, GoodStep p s ts := by
  obtain ⟨τ, s', hτ, hoth, hstep, hinv', hrdy, hev, hsub⟩ := inc_step_full hp s hinv.1 hins
    (hinv.2 r (lt_numRegs_of_inc hins)) _ (incPlan_valid hp hins) hsep hreg
  refine ⟨(τ, s'), hτ, hstep, ⟨hinv', fun r' hr' => ?_⟩, hev, hsub⟩
  by_cases he : r' = r
  · exact he ▸ hrdy
  · rw [hoth r' he]
    exact (hinv.2 r' hr').later τ

/-! ### What is still open -/

/-- **The step lemmas still to be proved** for the program `p`, as hypotheses. -/
structure MachineSteps (p : Program) : Prop where
  /-- The separation and region facts of the activation plan of every `inc` step from a state
  with the invariant (the hypotheses of `inc_step`). -/
  incSep : ∀ (s : MState) (r : ℕ), MInv p s → p[s.pc]? = some (.inc r) →
    IncSep (incPlan p s.pc r) ((s.reg r).later 930) ∧
      IncRegion (incPlan p s.pc r) ((s.reg r).later 930)
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
      obtain ⟨h1, h2⟩ := M.incSep s r hinv hi
      exact inc_step_minv hp s hinv hi h1 h2
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
