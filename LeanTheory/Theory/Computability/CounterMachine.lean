/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Computability.StateTransition
public import Mathlib.Logic.Function.Basic

/-!
# Counter (Minsky register) machines

A counter machine has registers indexed by `ℕ`, each holding a natural number, and a program which
is a finite list of instructions of exactly three kinds (research note `N-14`):

* `inc r`: increment register `r` and go to the next instruction;
* `decJz r l`: if register `r` is zero jump to instruction `l`, otherwise decrement it and go to
  the next instruction;
* `halt`: stop.

There is no unconditional jump: `decJz z l` on a register `z` known to be zero plays that role.

## Conventions

* A configuration `Cfg` is a program counter and a register file `regs : ℕ → ℕ`. No finiteness
  condition is imposed on `regs`: a program mentions finitely many registers and by
  `Program.step_regs_of_forall_ne` it never changes, and by `Program.step_congr` never reads,
  any other register.
* `Program.step P c = none` (the machine has halted) **iff** the instruction at `c.pc` is `halt`
  **or** `c.pc` is outside the program (`Program.step_eq_none_iff`). Falling off the end is
  therefore a way of halting; this is what makes programs composable. A program is
  `Program.WellFormed` when every jump target is inside the program and its last instruction is
  `halt`; such a program never leaves its range (`Program.WellFormed.pc_lt_of_reaches`) and so
  halts only at a `halt` instruction (`Program.WellFormed.halt_of_step_eq_none`).
* `Program.eval P c : Part Cfg` is the halting configuration reached from `c`, defined through
  `StateTransition.eval`.
* `Program.Computes P f`, for `f : ℕ →. ℕ`: started at instruction `0` with the input in register
  `0` and all other registers zero (`Cfg.init n`), the machine halts iff `f n` is defined, and
  then register `0` holds the value.

## Main definitions

* `Instr`, `Program`, `Cfg`, `Instr.exec`, `Program.step`, `Program.Reaches`, `Program.Reaches₁`,
  `Program.eval`, `Program.Halts`, `Program.Computes`.
* `Instr.relocate`, `Program.relocate` (shift all jump targets; `Program.mem_relocate_decJz`),
  `Cfg.shift`, `Program.seq` (sequential composition), `Program.WellFormed`.

## Main results

* Determinism: `Program.reaches_total`, `Program.eval_eq_of_reaches`, `Program.mem_eval_unique`,
  `Program.Computes.unique`.
* Embedding of a relocated subprogram in a larger program: `Program.step_embed`,
  `Program.reaches_embed`, `Program.reaches₁_embed`, `Program.halts_of_halts_embed`, and the
  special cases `Program.reaches_seq_left`, `Program.reaches_seq_right`.
* `Program.Halts.induction`: strong induction along a halting run.

## Sanity checks

* `Program.step_of_halt`, `Program.step_of_length_le`: a halting configuration has no successor.
* `haltProg_eval`, `haltProg_computes`: the program `[halt]` halts at once and computes the
  identity.
* `succProg_computes`: `[inc 0, halt]` computes the successor.
* `addProg_eval`, `addProg_eval_three_four`: a four-instruction program adding register `1` to
  register `0`.
* `loopProg_eval`, `loopProg_computes`: `[decJz 1 0]` never halts on an initial configuration.
* `not_wellFormed_loopProg`, `wellFormed_addProg`: fixtures for `Program.WellFormed`.
-/

@[expose] public section

namespace LeanTheory.Computability

open Function

/-- An instruction of a counter machine. -/
inductive Instr where
  /-- Increment register `r` and go to the next instruction. -/
  | inc (r : ℕ)
  /-- If register `r` is zero jump to instruction `l`; otherwise decrement register `r` and go to
  the next instruction. -/
  | decJz (r : ℕ) (l : ℕ)
  /-- Stop. -/
  | halt
  deriving DecidableEq, Repr

/-- A counter machine program: a finite list of instructions, numbered from `0`. -/
abbrev Program := List Instr

/-- A configuration of a counter machine: a program counter and the contents of the registers. -/
@[ext] structure Cfg where
  /-- The program counter: the index of the instruction to execute next. -/
  pc : ℕ
  /-- The contents of the registers. -/
  regs : ℕ → ℕ

/-- The initial configuration for the input `n`: the program counter is `0`, register `0` holds `n`
and every other register holds `0`. -/
def Cfg.init (n : ℕ) : Cfg := ⟨0, update (fun _ => 0) 0 n⟩

/-- The configuration `c` with its program counter moved forward by `k`. -/
def Cfg.shift (k : ℕ) (c : Cfg) : Cfg := ⟨c.pc + k, c.regs⟩

/-- Moving the program counter by zero changes nothing. -/
@[simp] theorem Cfg.shift_zero (c : Cfg) : c.shift 0 = c := rfl

/-- The effect of one instruction on a configuration; `none` for `halt`. -/
def Instr.exec : Instr → Cfg → Option Cfg
  | .inc r, c => some ⟨c.pc + 1, update c.regs r (c.regs r + 1)⟩
  | .decJz r l, c =>
    if c.regs r = 0 then some ⟨l, c.regs⟩ else some ⟨c.pc + 1, update c.regs r (c.regs r - 1)⟩
  | .halt, _ => none

/-- The instruction with its jump target (if any) moved forward by `k`. -/
def Instr.relocate (k : ℕ) : Instr → Instr
  | .inc r => .inc r
  | .decJz r l => .decJz r (l + k)
  | .halt => .halt

/-- A relocated instruction acts on a shifted configuration as the original instruction acts on
the original configuration. -/
theorem Instr.exec_relocate (k : ℕ) (i : Instr) (c : Cfg) :
    (i.relocate k).exec (c.shift k) = (i.exec c).map (Cfg.shift k) := by
  cases i with
  | inc r => simp [Instr.exec, Instr.relocate, Cfg.shift, Nat.add_right_comm]
  | decJz r l =>
    by_cases h : c.regs r = 0 <;>
      simp [Instr.exec, Instr.relocate, Cfg.shift, h, Nat.add_right_comm]
  | halt => rfl

namespace Program

/-- One step of the machine: execute the instruction at the program counter. The result is `none`
when that instruction is `halt` or when the program counter is outside the program. -/
def step (P : Program) (c : Cfg) : Option Cfg := P[c.pc]?.bind fun i => i.exec c

/-- `P.Reaches c c'`: the program `P` takes `c` to `c'` in zero or more steps. -/
def Reaches (P : Program) : Cfg → Cfg → Prop := StateTransition.Reaches P.step

/-- `P.Reaches₁ c c'`: the program `P` takes `c` to `c'` in one or more steps. -/
def Reaches₁ (P : Program) : Cfg → Cfg → Prop := StateTransition.Reaches₁ P.step

/-- The halting configuration reached by `P` from `c`, if any. -/
def eval (P : Program) (c : Cfg) : Part Cfg := StateTransition.eval P.step c

/-- `P.Halts c`: the run of `P` from `c` reaches a configuration without successor. -/
def Halts (P : Program) (c : Cfg) : Prop := (P.eval c).Dom

/-- `P.Computes f`: on the initial configuration for the input `n` the program halts iff `f n` is
defined, and then register `0` holds the value `f n`. -/
def Computes (P : Program) (f : ℕ →. ℕ) : Prop :=
  ∀ n, (P.eval (Cfg.init n)).map (fun c => c.regs 0) = f n

/-! ### One step -/

/-- The step function at an instruction `inc`. -/
theorem step_of_inc {P : Program} {c : Cfg} {r : ℕ} (h : P[c.pc]? = some (.inc r)) :
    P.step c = some ⟨c.pc + 1, update c.regs r (c.regs r + 1)⟩ := by
  simp [step, h, Instr.exec]

/-- The step function at an instruction `decJz` whose register is zero: jump. -/
theorem step_of_decJz_zero {P : Program} {c : Cfg} {r l : ℕ} (h : P[c.pc]? = some (.decJz r l))
    (hr : c.regs r = 0) : P.step c = some ⟨l, c.regs⟩ := by
  simp [step, h, Instr.exec, hr]

/-- The step function at an instruction `decJz` whose register is positive: decrement. -/
theorem step_of_decJz_pos {P : Program} {c : Cfg} {r l : ℕ} (h : P[c.pc]? = some (.decJz r l))
    (hr : c.regs r ≠ 0) : P.step c = some ⟨c.pc + 1, update c.regs r (c.regs r - 1)⟩ := by
  simp [step, h, Instr.exec, hr]

/-- A configuration at a `halt` instruction has no successor. -/
theorem step_of_halt {P : Program} {c : Cfg} (h : P[c.pc]? = some .halt) : P.step c = none := by
  simp [step, h, Instr.exec]

/-- A configuration whose program counter is outside the program has no successor. -/
theorem step_of_length_le {P : Program} {c : Cfg} (h : P.length ≤ c.pc) : P.step c = none := by
  simp [step, List.getElem?_eq_none h]

/-- Halting is exactly: the current instruction is `halt`, or the program counter is outside the
program. -/
theorem step_eq_none_iff {P : Program} {c : Cfg} :
    P.step c = none ↔ P[c.pc]? = some .halt ∨ P.length ≤ c.pc := by
  constructor
  · intro h
    rcases hi : P[c.pc]? with _ | i
    · exact Or.inr (List.getElem?_eq_none_iff.1 hi)
    · cases i with
      | inc r => rw [step_of_inc hi] at h; cases h
      | decJz r l =>
        by_cases hr : c.regs r = 0
        · rw [step_of_decJz_zero hi hr] at h; cases h
        · rw [step_of_decJz_pos hi hr] at h; cases h
      | halt => exact Or.inl rfl
  · rintro (h | h)
    · exact step_of_halt h
    · exact step_of_length_le h

/-- A step never changes a register that no instruction of the program mentions. -/
theorem step_regs_of_forall_ne {P : Program} {c c' : Cfg} {x : ℕ} (h : P.step c = some c')
    (hinc : .inc x ∉ P) (hdec : ∀ l, .decJz x l ∉ P) : c'.regs x = c.regs x := by
  rcases hi : P[c.pc]? with _ | i
  · simp [step, hi] at h
  · have hmem : i ∈ P := List.mem_of_getElem? hi
    cases i with
    | inc r =>
      rw [step_of_inc hi] at h
      cases h
      have : x ≠ r := by rintro rfl; exact hinc hmem
      simp [this]
    | decJz r l =>
      have : x ≠ r := by rintro rfl; exact hdec l hmem
      by_cases hr : c.regs r = 0
      · rw [step_of_decJz_zero hi hr] at h; cases h; rfl
      · rw [step_of_decJz_pos hi hr] at h; cases h; simp [this]
    | halt => rw [step_of_halt hi] at h; cases h

/-- The step function only reads the registers mentioned in the program: if two register files
agree on every register mentioned by `P`, the successors (if any) have the same program counter
and again agree on those registers. -/
theorem step_congr {P : Program} {pc : ℕ} {σ τ : ℕ → ℕ}
    (h : ∀ x, (.inc x ∈ P ∨ ∃ l, .decJz x l ∈ P) → σ x = τ x) :
    Option.Rel (fun c d : Cfg => c.pc = d.pc ∧
      ∀ x, (.inc x ∈ P ∨ ∃ l, .decJz x l ∈ P) → c.regs x = d.regs x)
      (P.step ⟨pc, σ⟩) (P.step ⟨pc, τ⟩) := by
  rcases hi : P[pc]? with _ | i
  · simp [step, hi]
  · have hmem : i ∈ P := List.mem_of_getElem? hi
    cases i with
    | inc r =>
      have e := h r (Or.inl hmem)
      rw [step_of_inc (c := ⟨pc, σ⟩) hi, step_of_inc (c := ⟨pc, τ⟩) hi]
      refine Option.Rel.some ⟨rfl, fun x hx => ?_⟩
      by_cases hxr : x = r
      · subst hxr; simp [e]
      · simp [hxr, h x hx]
    | decJz r l =>
      have e : σ r = τ r := h r (Or.inr ⟨l, hmem⟩)
      by_cases hr : σ r = 0
      · rw [step_of_decJz_zero (c := ⟨pc, σ⟩) hi hr,
          step_of_decJz_zero (c := ⟨pc, τ⟩) hi (show τ r = 0 from e ▸ hr)]
        exact Option.Rel.some ⟨rfl, h⟩
      · rw [step_of_decJz_pos (c := ⟨pc, σ⟩) hi hr,
          step_of_decJz_pos (c := ⟨pc, τ⟩) hi (show τ r ≠ 0 from e ▸ hr)]
        refine Option.Rel.some ⟨rfl, fun x hx => ?_⟩
        by_cases hxr : x = r
        · subst hxr; simp [e]
        · simp [hxr, h x hx]
    | halt =>
      rw [step_of_halt (c := ⟨pc, σ⟩) hi, step_of_halt (c := ⟨pc, τ⟩) hi]
      exact Option.Rel.none

/-! ### Runs -/

/-- Every configuration reaches itself. -/
@[refl] theorem Reaches.refl {P : Program} (c : Cfg) : P.Reaches c c := Relation.ReflTransGen.refl

/-- Runs compose. -/
@[trans] theorem Reaches.trans {P : Program} {a b c : Cfg} (h₁ : P.Reaches a b)
    (h₂ : P.Reaches b c) : P.Reaches a c := Relation.ReflTransGen.trans h₁ h₂

/-- A single step is a run. -/
theorem Reaches.single {P : Program} {a b : Cfg} (h : P.step a = some b) : P.Reaches a b :=
  Relation.ReflTransGen.single h

/-- Prepend one step to a run. -/
theorem Reaches.head {P : Program} {a b c : Cfg} (h : P.step a = some b) (h₂ : P.Reaches b c) :
    P.Reaches a c := Relation.ReflTransGen.head h h₂

/-- Append one step to a run. -/
theorem Reaches.tail {P : Program} {a b c : Cfg} (h₁ : P.Reaches a b) (h : P.step b = some c) :
    P.Reaches a c := Relation.ReflTransGen.tail h₁ h

/-- A single step is a nonempty run. -/
theorem Reaches₁.single {P : Program} {a b : Cfg} (h : P.step a = some b) : P.Reaches₁ a b :=
  Relation.TransGen.single h

/-- A nonempty run is a run. -/
theorem Reaches₁.reaches {P : Program} {a b : Cfg} (h : P.Reaches₁ a b) : P.Reaches a b :=
  Relation.TransGen.to_reflTransGen h

/-- A step followed by a run is a nonempty run. -/
theorem Reaches₁.head {P : Program} {a b c : Cfg} (h : P.step a = some b) (h₂ : P.Reaches b c) :
    P.Reaches₁ a c := Relation.TransGen.head' h h₂

/-- A run followed by a step is a nonempty run. -/
theorem Reaches.tail₁ {P : Program} {a b c : Cfg} (h₁ : P.Reaches a b) (h : P.step b = some c) :
    P.Reaches₁ a c := Relation.TransGen.tail' h₁ h

/-- A nonempty run followed by a run is a nonempty run. -/
theorem Reaches₁.trans_reaches {P : Program} {a b c : Cfg} (h₁ : P.Reaches₁ a b)
    (h₂ : P.Reaches b c) : P.Reaches₁ a c := Relation.TransGen.trans_left h₁ h₂

/-- A nonempty run starts with a step. -/
theorem Reaches₁.exists_step {P : Program} {a c : Cfg} (h : P.Reaches₁ a c) :
    ∃ b, P.step a = some b ∧ P.Reaches b c := Relation.TransGen.head'_iff.1 h

/-- **Determinism**: two runs from the same configuration are comparable. -/
theorem reaches_total {P : Program} {a b c : Cfg} (hab : P.Reaches a b) (hac : P.Reaches a c) :
    P.Reaches b c ∨ P.Reaches c b := StateTransition.reaches_total hab hac

/-- A run from a halted configuration is trivial. -/
theorem Reaches.eq_of_step_eq_none {P : Program} {a b : Cfg} (h : P.Reaches a b)
    (ha : P.step a = none) : b = a := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, -⟩
  · rfl
  · have hc' : P.step a = some c := hc
    rw [ha] at hc'
    cases hc'

/-! ### Evaluation and halting -/

/-- `c'` is the result of running `P` from `c` iff `c'` is reachable from `c` and halted. -/
theorem mem_eval {P : Program} {c c' : Cfg} :
    c' ∈ P.eval c ↔ P.Reaches c c' ∧ P.step c' = none := StateTransition.mem_eval

/-- **Determinism**: the result of a run is unique. -/
theorem mem_eval_unique {P : Program} {c a b : Cfg} (ha : a ∈ P.eval c) (hb : b ∈ P.eval c) :
    a = b := Part.mem_unique ha hb

/-- Running from a later configuration of the same run gives the same result. -/
theorem eval_eq_of_reaches {P : Program} {c c' : Cfg} (h : P.Reaches c c') :
    P.eval c = P.eval c' := StateTransition.reaches_eval h

/-- If `c` reaches a halted configuration `c'`, the result of the run from `c` is `c'`. -/
theorem eval_eq_some {P : Program} {c c' : Cfg} (h : P.Reaches c c') (h' : P.step c' = none) :
    P.eval c = Part.some c' := Part.eq_some_iff.2 (mem_eval.2 ⟨h, h'⟩)

/-- A program halts from `c` iff `c` reaches a configuration without successor. -/
theorem halts_iff {P : Program} {c : Cfg} :
    P.Halts c ↔ ∃ c', P.Reaches c c' ∧ P.step c' = none := by
  simp only [Halts, Part.dom_iff_mem, mem_eval]

/-- A configuration without successor halts. -/
theorem halts_of_step_eq_none {P : Program} {c : Cfg} (h : P.step c = none) : P.Halts c :=
  halts_iff.2 ⟨c, Reaches.refl c, h⟩

/-- Halting is invariant along a run. -/
theorem halts_iff_of_reaches {P : Program} {c c' : Cfg} (h : P.Reaches c c') :
    P.Halts c ↔ P.Halts c' := by
  simp only [Halts, eval_eq_of_reaches h]

/-- A configuration that reaches itself in one or more steps does not halt. -/
theorem not_halts_of_reaches₁_self {P : Program} {c : Cfg} (h : P.Reaches₁ c c) : ¬P.Halts c := by
  intro hh
  obtain ⟨d, hd, hd0⟩ := halts_iff.1 hh
  have key : ∀ a, P.Reaches c a → P.Reaches₁ a c := by
    intro a ha
    induction ha with
    | refl => exact h
    | tail hab hb ih =>
      obtain ⟨b', hb', hbc⟩ := ih.exists_step
      cases Option.mem_unique hb hb'
      exact Relation.TransGen.trans_right hbc h
  obtain ⟨e, he, -⟩ := (key d hd).exists_step
  rw [hd0] at he
  cases he

/-- **Strong induction along a halting run.** To prove `C c` for a configuration from which `P`
halts, one may assume `C` for every configuration reached from `c` in one or more steps. -/
theorem Halts.induction {P : Program} {C : Cfg → Prop} {c : Cfg} (h : P.Halts c)
    (H : ∀ c, P.Halts c → (∀ c', P.Reaches₁ c c' → C c') → C c) : C c := by
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 h
  suffices hs : ∀ c', P.Reaches c c' → C c' from hs c (Reaches.refl c)
  refine StateTransition.evalInduction (C := fun a => ∀ c', P.Reaches a c' → C c') hb ?_
  intro a ha IH c' hc'
  have key : ∀ d, P.Reaches₁ a d → C d := by
    intro d hd
    obtain ⟨a₁, ha₁, h₁⟩ := hd.exists_step
    exact IH a₁ ha₁ d h₁
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨a₁, ha₁, h₁⟩
  · exact H a (Part.dom_iff_mem.2 ⟨b, ha⟩) key
  · exact IH a₁ ha₁ c' h₁

/-- A program computes at most one partial function. -/
theorem Computes.unique {P : Program} {f g : ℕ →. ℕ} (hf : P.Computes f) (hg : P.Computes g) :
    f = g := by
  funext n
  rw [← hf n, ← hg n]

/-! ### Relocation, embedding and sequential composition -/

/-- The program with every jump target moved forward by `k`: the code of `P` as it must be written
when placed at position `k` of a larger program. -/
def relocate (k : ℕ) (P : Program) : Program := P.map (Instr.relocate k)

/-- Relocation preserves the length. -/
@[simp] theorem length_relocate (k : ℕ) (P : Program) : (P.relocate k).length = P.length := by
  simp [relocate]

/-- Relocation by zero changes nothing. -/
@[simp] theorem relocate_zero (P : Program) : P.relocate 0 = P := by
  have : Instr.relocate 0 = id := by
    funext i
    cases i <;> rfl
  simp [relocate, this]

/-- Jump targets in a relocated program. -/
theorem mem_relocate_decJz {k x l : ℕ} {P : Program} :
    .decJz x l ∈ P.relocate k ↔ ∃ l', .decJz x l' ∈ P ∧ l = l' + k := by
  simp only [relocate, List.mem_map]
  constructor
  · rintro ⟨i, hi, he⟩
    cases i with
    | inc r => cases he
    | decJz r l' =>
      simp only [Instr.relocate, Instr.decJz.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨l', hi, rfl⟩
    | halt => cases he
  · rintro ⟨l', hi, rfl⟩
    exact ⟨_, hi, rfl⟩

/-- Sequential composition: the code of `P` followed by the code of `Q`, relocated. Control passes
from `P` to `Q` when `P` jumps to, or falls through to, its own length. -/
def seq (P Q : Program) : Program := P ++ Q.relocate P.length

/-- The length of a sequential composition. -/
@[simp] theorem length_seq (P Q : Program) : (P.seq Q).length = P.length + Q.length := by
  simp [seq]

/-- **Embedding, one step.** A step of `Q` is a step of any program containing the relocated code
of `Q`, between the shifted configurations. -/
theorem step_embed (pre post : Program) {Q : Program} {c c' : Cfg} (h : Q.step c = some c') :
    (pre ++ Q.relocate pre.length ++ post).step (c.shift pre.length) =
      some (c'.shift pre.length) := by
  rcases hi : Q[c.pc]? with _ | i
  · simp [step, hi] at h
  · have hlt : c.pc < Q.length := (List.getElem?_eq_some_iff.1 hi).1
    have hget : (pre ++ Q.relocate pre.length ++ post)[(c.shift pre.length).pc]? =
        some (i.relocate pre.length) := by
      have h₁ : c.pc + pre.length < (pre ++ Q.relocate pre.length).length := by
        simp only [List.length_append, length_relocate]
        omega
      rw [Cfg.shift, List.getElem?_append_left h₁,
        List.getElem?_append_right (Nat.le_add_left _ _)]
      simp [relocate, hi]
    have hq : i.exec c = some c' := by simpa [step, hi] using h
    rw [step, hget, Option.bind_some, Instr.exec_relocate, hq, Option.map_some]

/-- **Embedding, runs.** A run of `Q` is a run of any program containing the relocated code of
`Q`, between the shifted configurations. -/
theorem reaches_embed (pre post : Program) {Q : Program} {c c' : Cfg} (h : Q.Reaches c c') :
    (pre ++ Q.relocate pre.length ++ post).Reaches (c.shift pre.length) (c'.shift pre.length) := by
  induction h with
  | refl => exact Reaches.refl _
  | tail _ hb ih => exact ih.tail (step_embed pre post hb)

/-- **Embedding, nonempty runs.** -/
theorem reaches₁_embed (pre post : Program) {Q : Program} {c c' : Cfg} (h : Q.Reaches₁ c c') :
    (pre ++ Q.relocate pre.length ++ post).Reaches₁ (c.shift pre.length)
      (c'.shift pre.length) := by
  obtain ⟨b, hb, hbc⟩ := h.exists_step
  exact Reaches₁.head (step_embed pre post hb) (reaches_embed pre post hbc)

/-- **Embedding reflects halting.** If a program containing the relocated code of `Q` halts from a
shifted configuration, then `Q` halts from the original configuration (possibly by leaving its
own code, after which the larger program continues). -/
theorem halts_of_halts_embed (pre post : Program) {Q : Program} {c : Cfg}
    (h : (pre ++ Q.relocate pre.length ++ post).Halts (c.shift pre.length)) : Q.Halts c := by
  refine Halts.induction (C := fun d => ∀ c, d = c.shift pre.length → Q.Halts c) h ?_ c rfl
  rintro d - IH c rfl
  rcases hs : Q.step c with _ | c'
  · exact halts_of_step_eq_none hs
  · exact (halts_iff_of_reaches (Reaches.single hs)).2
      (IH _ (Reaches₁.single (step_embed pre post hs)) c' rfl)

/-- A run of `P` is a run of `P ++ R`. -/
theorem reaches_append_left {P : Program} (R : Program) {c c' : Cfg} (h : P.Reaches c c') :
    (P ++ R).Reaches c c' := by
  simpa using reaches_embed [] R h

/-- If `P ++ R` halts from `c` then so does `P`. -/
theorem halts_of_halts_append_left {P : Program} (R : Program) {c : Cfg}
    (h : (P ++ R).Halts c) : P.Halts c :=
  halts_of_halts_embed [] R (by simpa using h)

/-- A run of `P` is a run of `P.seq Q`. -/
theorem reaches_seq_left {P : Program} (Q : Program) {c c' : Cfg} (h : P.Reaches c c') :
    (P.seq Q).Reaches c c' := reaches_append_left _ h

/-- A run of `Q` is a run of `P.seq Q` between the shifted configurations. -/
theorem reaches_seq_right (P : Program) {Q : Program} {c c' : Cfg} (h : Q.Reaches c c') :
    (P.seq Q).Reaches (c.shift P.length) (c'.shift P.length) := by
  simpa [seq] using reaches_embed P [] h

/-- If `P.seq Q` halts from `c` then so does `P`. -/
theorem halts_of_halts_seq_left {P : Program} (Q : Program) {c : Cfg} (h : (P.seq Q).Halts c) :
    P.Halts c := halts_of_halts_append_left _ h

/-- If `P.seq Q` halts from a shifted configuration then `Q` halts from the original one. -/
theorem halts_of_halts_seq_right (P : Program) {Q : Program} {c : Cfg}
    (h : (P.seq Q).Halts (c.shift P.length)) : Q.Halts c :=
  halts_of_halts_embed P [] (by simpa [seq] using h)

/-! ### Well-formed programs -/

/-- A program is well formed when every jump target lies inside the program and the last
instruction is `halt`. Such a program can only stop at a `halt` instruction. -/
def WellFormed (P : Program) : Prop :=
  (∀ r l, .decJz r l ∈ P → l < P.length) ∧ P.getLast? = some .halt

/-- A step of a well-formed program stays inside the program. -/
theorem WellFormed.pc_lt_of_step {P : Program} (hP : P.WellFormed) {c c' : Cfg}
    (h : P.step c = some c') : c'.pc < P.length := by
  have hlast : P[P.length - 1]? = some .halt := by
    rw [← List.getLast?_eq_getElem?]
    exact hP.2
  rcases hi : P[c.pc]? with _ | i
  · simp [step, hi] at h
  · have hlt : c.pc < P.length := (List.getElem?_eq_some_iff.1 hi).1
    have hne : i ≠ .halt → c.pc + 1 < P.length := by
      intro hne
      by_contra hcon
      have : c.pc = P.length - 1 := by omega
      rw [this, hlast] at hi
      exact hne (Option.some.inj hi).symm
    cases i with
    | inc r =>
      rw [step_of_inc hi] at h
      cases h
      exact hne (by simp)
    | decJz r l =>
      by_cases hr : c.regs r = 0
      · rw [step_of_decJz_zero hi hr] at h
        cases h
        exact hP.1 r l (List.mem_of_getElem? hi)
      · rw [step_of_decJz_pos hi hr] at h
        cases h
        exact hne (by simp)
    | halt => rw [step_of_halt hi] at h; cases h

/-- A run of a well-formed program that starts inside the program stays inside it. -/
theorem WellFormed.pc_lt_of_reaches {P : Program} (hP : P.WellFormed) {c c' : Cfg}
    (h : P.Reaches c c') (hc : c.pc < P.length) : c'.pc < P.length := by
  induction h with
  | refl => exact hc
  | tail _ hb _ => exact hP.pc_lt_of_step hb

/-- A well-formed program started inside its range halts only at a `halt` instruction. -/
theorem WellFormed.halt_of_step_eq_none {P : Program} (hP : P.WellFormed) {c c' : Cfg}
    (h : P.Reaches c c') (hc : c.pc < P.length) (h' : P.step c' = none) :
    P[c'.pc]? = some .halt := by
  rcases step_eq_none_iff.1 h' with h₁ | h₁
  · exact h₁
  · exact absurd (hP.pc_lt_of_reaches h hc) (by omega)

end Program

/-! ### Sanity programs -/

open Program

/-- The program that halts at once. -/
def haltProg : Program := [.halt]

/-- `haltProg` started at instruction `0` halts immediately, in the same configuration. -/
theorem haltProg_eval (σ : ℕ → ℕ) : haltProg.eval ⟨0, σ⟩ = Part.some ⟨0, σ⟩ :=
  eval_eq_some (Reaches.refl _) (step_of_halt rfl)

/-- `haltProg` computes the identity function. -/
theorem haltProg_computes : haltProg.Computes fun n => Part.some n := by
  intro n
  simp [Cfg.init, haltProg_eval]

/-- The program incrementing register `0` once. -/
def succProg : Program := [.inc 0, .halt]

/-- `succProg` computes the successor function. -/
theorem succProg_computes : succProg.Computes fun n => Part.some (n + 1) := by
  intro n
  have h : succProg.eval (Cfg.init n) =
      Part.some ⟨1, update (Cfg.init n).regs 0 ((Cfg.init n).regs 0 + 1)⟩ :=
    eval_eq_some (Reaches.single (step_of_inc rfl)) (step_of_halt rfl)
  rw [h]
  simp [Cfg.init]

/-- The program adding register `1` to register `0` (and clearing register `1`), using register
`2`, assumed zero, for the backward jump. -/
def addProg : Program := [.decJz 1 3, .inc 0, .decJz 2 0, .halt]

/-- `addProg` takes registers `(a, b, 0, …)` to `(a + b, 0, 0, …)` and halts at instruction `3`. -/
theorem addProg_eval (σ : ℕ → ℕ) (h2 : σ 2 = 0) :
    addProg.eval ⟨0, σ⟩ = Part.some ⟨3, update (update σ 0 (σ 0 + σ 1)) 1 0⟩ := by
  refine eval_eq_some ?_ (step_of_halt rfl)
  induction hk : σ 1 generalizing σ with
  | zero =>
    have e : update (update σ 0 (σ 0 + 0)) 1 0 = σ := by
      funext x
      by_cases h1 : x = 1 <;> by_cases h0 : x = 0 <;> simp_all
    rw [e]
    exact Reaches.single (step_of_decJz_zero rfl hk)
  | succ k ih =>
    have s₁ : addProg.step ⟨0, σ⟩ = some ⟨1, update σ 1 k⟩ := by
      rw [step_of_decJz_pos rfl (by simp [hk])]
      simp [hk]
    have s₂ : addProg.step ⟨1, update σ 1 k⟩ = some ⟨2, update (update σ 1 k) 0 (σ 0 + 1)⟩ := by
      rw [step_of_inc rfl]
      simp
    have s₃ : addProg.step ⟨2, update (update σ 1 k) 0 (σ 0 + 1)⟩ =
        some ⟨0, update (update σ 1 k) 0 (σ 0 + 1)⟩ :=
      step_of_decJz_zero rfl (by simp [h2])
    have e : update (update (update (update σ 1 k) 0 (σ 0 + 1)) 0
        (update (update σ 1 k) 0 (σ 0 + 1) 0 + update (update σ 1 k) 0 (σ 0 + 1) 1)) 1 0 =
        update (update σ 0 (σ 0 + (k + 1))) 1 0 := by
      funext x
      by_cases h1 : x = 1 <;> by_cases h0 : x = 0 <;> simp_all
      omega
    rw [← e]
    exact Reaches.head s₁ (Reaches.head s₂ (Reaches.head s₃
      (ih _ (by simp [h2]) (by simp))))

/-- A concrete instance of `addProg_eval`: `3 + 4 = 7`. -/
theorem addProg_eval_three_four :
    (addProg.eval ⟨0, update (update (fun _ => 0) 0 3) 1 4⟩).map (fun c => c.regs 0) =
      Part.some 7 := by
  rw [addProg_eval _ (by simp)]
  simp

/-- `addProg` is well formed. -/
theorem wellFormed_addProg : addProg.WellFormed := by
  refine ⟨fun r l h => ?_, rfl⟩
  simp only [addProg, List.mem_cons, Instr.decJz.injEq, reduceCtorEq, List.not_mem_nil,
    or_false, false_or] at h
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [addProg]

/-- The program that jumps to itself for ever when register `1` is zero. -/
def loopProg : Program := [.decJz 1 0]

/-- `loopProg` never halts on an initial configuration: its `eval` has empty domain there. -/
theorem loopProg_eval (n : ℕ) : loopProg.eval (Cfg.init n) = Part.none := by
  have h : loopProg.step (Cfg.init n) = some (Cfg.init n) :=
    step_of_decJz_zero rfl (by simp [Cfg.init])
  exact Part.eq_none_iff'.2 (not_halts_of_reaches₁_self (Reaches₁.single h))

/-- `loopProg` computes the nowhere defined function. -/
theorem loopProg_computes : loopProg.Computes fun _ => Part.none := by
  intro n
  simp [loopProg_eval]

/-- `loopProg` is not well formed: it does not end with `halt`. -/
theorem not_wellFormed_loopProg : ¬loopProg.WellFormed := by
  rintro ⟨-, h⟩
  simp [loopProg] at h

end LeanTheory.Computability
