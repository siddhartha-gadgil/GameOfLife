/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Computability.CounterMachine

/-!
# A structured loop language compiled to counter machines

Proofs about raw jump programs are painful, so counter programs are produced from a small
structured language `Stmt` on the same registers, with a big-step semantics `Exec`:

* `skip`;
* `inc r`: increment register `r`;
* `seq s t`: `s`, then `t`;
* `loop r s`: `while r ≠ 0 do (r := r - 1; s)`. The decrement is part of the loop test, exactly
  as in the machine instruction `decJz`.

## Compilation

`Stmt.compileAux z s` is the code of `s`, entered at instruction `0` and left by reaching its own
length. A loop becomes

```
0:        decJz r (L + 2)
1 … L:    code of the body, relocated by 1
L + 1:    decJz z 0
```

where `z` is a register that holds zero and that `s` does not mention, so that the last
instruction is an unconditional jump. `Stmt.compile s` takes `z := s.zeroReg = max 1 s.bound`,
the least register above all registers of `s` and above the input register `0`, and appends
`halt`.

## Main results

* `Exec.deterministic` (with the convenient forms `exec_iff_eq_of_exec`, `exec_seq_iff_of_exec`),
  `Exec.regs_eq_of_bound_le` (a statement changes no register at or above its bound).
* `Stmt.reaches_compileAux`: an execution of `s` is a run of its code.
* `Stmt.exists_exec_of_halts_compileAux`: conversely, if the code of `s` halts then `s` has an
  execution. The proof is by structural induction, with strong induction along the halting run
  (`Program.Halts.induction`) for loops.
* `Stmt.mem_eval_compile`: the halting configurations of `s.compile` are exactly the final states
  of `s`, at the `halt` instruction; `Stmt.eval_compile_eq_some`, `Stmt.eval_compile_eq_none`,
  `Stmt.eval_compile_eq_map` are convenient forms, and `Stmt.computes_compile` turns a
  description of the executions of `s` into `Program.Computes`.
* `Stmt.wellFormed_compile`: compiled programs are well formed.

## Loop rules and macros

* `exec_loop_iff_of_seq`: a loop whose body is deterministic and total along a known sequence of
  states `S 0, S 1, …` stops at the first `S k` whose loop register is zero, and diverges if
  there is none. `exec_loop_iff_of_count` is the special case of a counted loop.
* `Stmt.clear`, `Stmt.move`, `Stmt.move₂`, `Stmt.copy`, `Stmt.assign`, `Stmt.clearRange` with
  exact characterizations `exec_clear_iff`, `exec_move_iff`, `exec_move₂_iff`, `exec_copy_iff`,
  `exec_assign_iff`, `exec_clearRange_iff`.

## Sanity checks

* `compile_move_eq`: the code generated for `move 1 0` is literally `addProg`.
* `not_exec_spin`, `eval_compile_spin`: `inc 0; while 0 ≠ 0 do (dec 0; inc 0)` has no execution
  and its compiled program never halts.
* `compile_double_computes`: a compiled program computing `n ↦ 2 * n`.
-/

@[expose] public section

namespace LeanTheory.Computability

open Function Program

/-- Statements of the structured loop language on registers. -/
inductive Stmt where
  /-- Do nothing. -/
  | skip
  /-- Increment register `r`. -/
  | inc (r : ℕ)
  /-- Sequential composition. -/
  | seq (s t : Stmt)
  /-- `while r ≠ 0 do (r := r - 1; s)`. -/
  | loop (r : ℕ) (s : Stmt)
  deriving DecidableEq, Repr

/-- Big-step semantics: `Exec s σ σ'` means that `s` started on the register file `σ` terminates
with the register file `σ'`. -/
inductive Exec : Stmt → (ℕ → ℕ) → (ℕ → ℕ) → Prop where
  /-- `skip` changes nothing. -/
  | skip (σ : ℕ → ℕ) : Exec .skip σ σ
  /-- `inc r` increments register `r`. -/
  | inc (r : ℕ) (σ : ℕ → ℕ) : Exec (.inc r) σ (update σ r (σ r + 1))
  /-- Sequential composition. -/
  | seq {s t : Stmt} {σ₁ σ₂ σ₃ : ℕ → ℕ} : Exec s σ₁ σ₂ → Exec t σ₂ σ₃ → Exec (.seq s t) σ₁ σ₃
  /-- A loop whose register is zero stops. -/
  | loopDone {r : ℕ} {s : Stmt} {σ : ℕ → ℕ} : σ r = 0 → Exec (.loop r s) σ σ
  /-- A loop whose register is positive decrements it, runs the body and starts again. -/
  | loopStep {r : ℕ} {s : Stmt} {σ₁ σ₂ σ₃ : ℕ → ℕ} : σ₁ r ≠ 0 →
      Exec s (update σ₁ r (σ₁ r - 1)) σ₂ → Exec (.loop r s) σ₂ σ₃ → Exec (.loop r s) σ₁ σ₃

/-! ### Inversion -/

/-- Executions of `skip`. -/
@[simp] theorem exec_skip_iff {σ σ' : ℕ → ℕ} : Exec .skip σ σ' ↔ σ' = σ :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .skip σ⟩

/-- Executions of `inc r`. -/
@[simp] theorem exec_inc_iff {r : ℕ} {σ σ' : ℕ → ℕ} :
    Exec (.inc r) σ σ' ↔ σ' = update σ r (σ r + 1) :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .inc r σ⟩

/-- Executions of `seq s t`. -/
@[simp] theorem exec_seq_iff {s t : Stmt} {σ σ' : ℕ → ℕ} :
    Exec (.seq s t) σ σ' ↔ ∃ τ, Exec s σ τ ∧ Exec t τ σ' :=
  ⟨fun h => by cases h with | seq h₁ h₂ => exact ⟨_, h₁, h₂⟩, fun ⟨_, h₁, h₂⟩ => .seq h₁ h₂⟩

/-- Executions of a loop, unfolded once. -/
theorem exec_loop_iff {r : ℕ} {s : Stmt} {σ σ' : ℕ → ℕ} :
    Exec (.loop r s) σ σ' ↔ (σ r = 0 ∧ σ' = σ) ∨
      (σ r ≠ 0 ∧ ∃ τ, Exec s (update σ r (σ r - 1)) τ ∧ Exec (.loop r s) τ σ') := by
  constructor
  · intro h
    cases h with
    | loopDone h0 => exact Or.inl ⟨h0, rfl⟩
    | loopStep h0 hb hl => exact Or.inr ⟨h0, _, hb, hl⟩
  · rintro (⟨h0, rfl⟩ | ⟨h0, τ, hb, hl⟩)
    · exact .loopDone h0
    · exact .loopStep h0 hb hl

/-- **Determinism** of the big-step semantics. -/
theorem Exec.deterministic {s : Stmt} {σ σ₁ σ₂ : ℕ → ℕ} (h₁ : Exec s σ σ₁) (h₂ : Exec s σ σ₂) :
    σ₁ = σ₂ := by
  induction h₁ generalizing σ₂ with
  | skip σ => cases h₂; rfl
  | inc r σ => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₃ h₄ =>
      cases ih₁ h₃
      exact ih₂ h₄
  | loopDone h0 =>
    cases h₂ with
    | loopDone _ => rfl
    | loopStep h0' _ _ => exact absurd h0 h0'
  | loopStep h0 _ _ ih₁ ih₂ =>
    cases h₂ with
    | loopDone h0' => exact absurd h0' h0
    | loopStep _ hb hl =>
      cases ih₁ hb
      exact ih₂ hl

/-- To describe all executions of `s` from `σ` it suffices to exhibit one. -/
theorem exec_iff_eq_of_exec {s : Stmt} {σ τ σ' : ℕ → ℕ} (h : Exec s σ τ) :
    Exec s σ σ' ↔ σ' = τ :=
  ⟨fun h' => h'.deterministic h, fun e => e ▸ h⟩

/-- If `s` takes `σ` to `τ`, the executions of `seq s t` from `σ` are those of `t` from `τ`. -/
theorem exec_seq_iff_of_exec {s t : Stmt} {σ τ σ' : ℕ → ℕ} (h : Exec s σ τ) :
    Exec (.seq s t) σ σ' ↔ Exec t τ σ' := by
  rw [exec_seq_iff]
  constructor
  · rintro ⟨τ', h₁, h₂⟩
    rwa [h.deterministic h₁]
  · exact fun h₂ => ⟨τ, h, h₂⟩

namespace Stmt

/-- A strict upper bound for the registers mentioned in a statement. -/
def bound : Stmt → ℕ
  | skip => 0
  | inc r => r + 1
  | seq s t => max s.bound t.bound
  | loop r s => max (r + 1) s.bound

end Stmt

/-- A statement does not change the registers at or above its bound. -/
theorem Exec.regs_eq_of_bound_le {s : Stmt} {σ σ' : ℕ → ℕ} (h : Exec s σ σ') {x : ℕ}
    (hx : s.bound ≤ x) : σ' x = σ x := by
  induction h with
  | skip σ => rfl
  | inc r σ =>
    have : x ≠ r := by simp only [Stmt.bound] at hx; omega
    simp [this]
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.bound, max_le_iff] at hx
    rw [ih₂ hx.2, ih₁ hx.1]
  | loopDone _ => rfl
  | @loopStep r s σ₁ σ₂ σ₃ _ _ _ ih₁ ih₂ =>
    have hx' := hx
    simp only [Stmt.bound, max_le_iff] at hx'
    have : x ≠ r := by omega
    rw [ih₂ hx, ih₁ hx'.2]
    simp [this]

/-! ### Loop rules -/

/-- **Loop rule.** Let `S 0, S 1, …` be register files such that, whenever the loop register of
`S k` is positive, the body run after the decrement has exactly one final state, `S (k + 1)`.
Then the loop started in `S 0` stops exactly in the first `S k` whose loop register is zero; if
there is no such `k` it has no execution. -/
theorem exec_loop_iff_of_seq {r : ℕ} {s : Stmt} (S : ℕ → ℕ → ℕ)
    (hS : ∀ k, S k r ≠ 0 → ∀ τ, Exec s (update (S k) r (S k r - 1)) τ ↔ τ = S (k + 1))
    (σ' : ℕ → ℕ) :
    Exec (.loop r s) (S 0) σ' ↔ ∃ k, S k r = 0 ∧ (∀ j < k, S j r ≠ 0) ∧ σ' = S k := by
  constructor
  · intro h
    have key : ∀ st τ σ', Exec st τ σ' → ∀ j, st = .loop r s → τ = S j →
        ∃ k, j ≤ k ∧ S k r = 0 ∧ (∀ i, j ≤ i → i < k → S i r ≠ 0) ∧ σ' = S k := by
      intro st τ σ' h
      induction h with
      | skip σ => intro j h; cases h
      | inc r σ => intro j h; cases h
      | seq _ _ _ _ => intro j h; cases h
      | loopDone h0 =>
        intro j hst hτ
        cases hst
        subst hτ
        exact ⟨j, le_rfl, h0, fun i h₁ h₂ => by omega, rfl⟩
      | loopStep h0 hb _ _ ihl =>
        intro j hst hτ
        cases hst
        subst hτ
        obtain ⟨k, hjk, hk0, hmin, rfl⟩ := ihl (j + 1) rfl ((hS j h0 _).1 hb)
        refine ⟨k, by omega, hk0, fun i h₁ h₂ => ?_, rfl⟩
        rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁'
        · exact h0
        · exact hmin i h₁' h₂
    obtain ⟨k, -, hk0, hmin, rfl⟩ := key _ _ _ h 0 rfl rfl
    exact ⟨k, hk0, fun j hj => hmin j (Nat.zero_le _) hj, rfl⟩
  · rintro ⟨k, hk0, hmin, rfl⟩
    have key : ∀ d j, j + d = k → Exec (.loop r s) (S j) (S k) := by
      intro d
      induction d with
      | zero =>
        intro j hj
        obtain rfl : j = k := by omega
        exact .loopDone hk0
      | succ d ih =>
        intro j hj
        have h0 : S j r ≠ 0 := hmin j (by omega)
        exact .loopStep h0 ((hS j h0 _).2 rfl) (ih (j + 1) (by omega))
    exact key k 0 (by omega)

/-- **Counted loop rule.** If moreover the loop register of `S k` is `σ r - k`, the loop started
in `σ = S 0` runs exactly `σ r` times and stops in `S (σ r)`. -/
theorem exec_loop_iff_of_count {r : ℕ} {s : Stmt} {σ : ℕ → ℕ} (S : ℕ → ℕ → ℕ) (h0 : S 0 = σ)
    (hr : ∀ k, S k r = σ r - k)
    (hS : ∀ k, k < σ r → ∀ τ, Exec s (update (S k) r (σ r - k - 1)) τ ↔ τ = S (k + 1))
    (σ' : ℕ → ℕ) : Exec (.loop r s) σ σ' ↔ σ' = S (σ r) := by
  subst h0
  rw [exec_loop_iff_of_seq S (fun k hk τ => by
    rw [hr k] at hk ⊢
    exact hS k (by omega) τ)]
  constructor
  · rintro ⟨k, hk0, hmin, rfl⟩
    have h₁ : S 0 r ≤ k := by
      have := hr k
      omega
    have h₂ : ¬S 0 r < k := fun hlt => hmin _ hlt (by rw [hr]; omega)
    rw [show S 0 r = k by omega]
  · rintro rfl
    exact ⟨S 0 r, by rw [hr]; omega, fun j hj => by rw [hr]; omega, rfl⟩

/-! ### Macros -/

namespace Stmt

/-- `clear r`: set register `r` to zero. -/
def clear (r : ℕ) : Stmt := loop r skip

/-- `move src dst`: add register `src` to register `dst` and set `src` to zero. -/
def move (src dst : ℕ) : Stmt := loop src (inc dst)

/-- `move₂ src d₁ d₂`: add register `src` to both `d₁` and `d₂` and set `src` to zero. -/
def move₂ (src d₁ d₂ : ℕ) : Stmt := loop src (seq (inc d₁) (inc d₂))

/-- `copy src dst tmp`: add register `src` to register `dst`, keeping `src`; the register `tmp`
must be zero and is zero again afterwards. -/
def copy (src dst tmp : ℕ) : Stmt := seq (move₂ src dst tmp) (move tmp src)

/-- `assign src dst tmp`: set register `dst` to the value of register `src`, keeping `src`; the
register `tmp` must be zero and is zero again afterwards. -/
def assign (src dst tmp : ℕ) : Stmt := seq (clear dst) (copy src dst tmp)

/-- `clearRange b n`: set the registers `b, …, b + n - 1` to zero. -/
def clearRange (b : ℕ) : ℕ → Stmt
  | 0 => skip
  | n + 1 => seq (clear (b + n)) (clearRange b n)

end Stmt

open Stmt

/-- `clear r` sets register `r` to zero and changes nothing else. -/
theorem exec_clear_iff {r : ℕ} {σ σ' : ℕ → ℕ} : Exec (clear r) σ σ' ↔ σ' = update σ r 0 := by
  rw [clear, exec_loop_iff_of_count (fun k => update σ r (σ r - k)) (by simp) (by simp)
    (fun k hk τ => by
      rw [exec_skip_iff]
      refine iff_of_eq (congrArg _ ?_)
      funext x
      grind [update_apply])]
  simp

/-- `move src dst` adds register `src` to register `dst` and sets `src` to zero. -/
theorem exec_move_iff {src dst : ℕ} (h : src ≠ dst) {σ σ' : ℕ → ℕ} :
    Exec (move src dst) σ σ' ↔ σ' = update (update σ dst (σ dst + σ src)) src 0 := by
  rw [move, exec_loop_iff_of_count (fun k => update (update σ dst (σ dst + k)) src (σ src - k))
    (by simp) (by simp)
    (fun k hk τ => by
      rw [exec_inc_iff]
      refine iff_of_eq (congrArg _ ?_)
      funext x
      grind [update_apply])]
  simp

/-- `move₂ src d₁ d₂` adds register `src` to `d₁` and to `d₂` and sets `src` to zero. -/
theorem exec_move₂_iff {src d₁ d₂ : ℕ} (h₁ : src ≠ d₁) (h₂ : src ≠ d₂) (h₁₂ : d₁ ≠ d₂)
    {σ σ' : ℕ → ℕ} : Exec (move₂ src d₁ d₂) σ σ' ↔
      σ' = update (update (update σ d₁ (σ d₁ + σ src)) d₂ (σ d₂ + σ src)) src 0 := by
  rw [move₂, exec_loop_iff_of_count
    (fun k => update (update (update σ d₁ (σ d₁ + k)) d₂ (σ d₂ + k)) src (σ src - k))
    (by simp) (by simp)
    (fun k hk τ => by
      simp only [exec_seq_iff, exec_inc_iff, exists_eq_left]
      refine iff_of_eq (congrArg _ ?_)
      funext x
      grind [update_apply])]
  simp

/-- `copy src dst tmp` adds register `src` to register `dst` and changes nothing else, provided
`tmp` is zero. -/
theorem exec_copy_iff {src dst tmp : ℕ} (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    {σ σ' : ℕ → ℕ} (ht : σ tmp = 0) :
    Exec (copy src dst tmp) σ σ' ↔ σ' = update σ dst (σ dst + σ src) := by
  simp only [copy, exec_seq_iff, exec_move₂_iff h₁ h₂ h₃, exec_move_iff (Ne.symm h₂),
    exists_eq_left]
  refine iff_of_eq (congrArg _ ?_)
  funext x
  grind [update_apply]

/-- `assign src dst tmp` sets register `dst` to the value of register `src` and changes nothing
else, provided `tmp` is zero. -/
theorem exec_assign_iff {src dst tmp : ℕ} (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    {σ σ' : ℕ → ℕ} (ht : σ tmp = 0) :
    Exec (assign src dst tmp) σ σ' ↔ σ' = update σ dst (σ src) := by
  have ht' : update σ dst 0 tmp = 0 := by simp [Ne.symm h₃, ht]
  simp only [assign, exec_seq_iff, exec_clear_iff, exists_eq_left, exec_copy_iff h₁ h₂ h₃ ht']
  refine iff_of_eq (congrArg _ ?_)
  funext x
  grind [update_apply]

/-- `clearRange b n` sets the registers `b, …, b + n - 1` to zero and changes nothing else. -/
theorem exec_clearRange_iff {b n : ℕ} {σ σ' : ℕ → ℕ} :
    Exec (clearRange b n) σ σ' ↔ σ' = fun x => if b ≤ x ∧ x < b + n then 0 else σ x := by
  induction n generalizing σ with
  | zero =>
    simp only [clearRange, exec_skip_iff]
    refine iff_of_eq (congrArg _ ?_)
    funext x
    grind
  | succ n ih =>
    simp only [clearRange, exec_seq_iff, exec_clear_iff, exists_eq_left, ih]
    refine iff_of_eq (congrArg _ ?_)
    funext x
    grind [update_apply]

/-! ### Compilation to counter machines -/

namespace Stmt

/-- The code of a statement, entered at instruction `0` and left by reaching its own length; `z` is
a register assumed to hold zero and not mentioned in the statement, used for backward jumps. -/
def compileAux (z : ℕ) : Stmt → Program
  | skip => []
  | inc r => [.inc r]
  | seq s t => (compileAux z s).seq (compileAux z t)
  | loop r s =>
    [.decJz r ((compileAux z s).length + 2)] ++ (compileAux z s).relocate 1 ++ [.decJz z 0]

/-- The register used as zero register when compiling `s`: the first register that is neither
mentioned in `s` nor the input and output register `0`. -/
def zeroReg (s : Stmt) : ℕ := max 1 s.bound

/-- The counter program of a statement: its code, with `s.zeroReg` as zero register, followed by
`halt`. -/
def compile (s : Stmt) : Program := compileAux s.zeroReg s ++ [.halt]

/-- The first instruction of the code of a loop. -/
theorem compileAux_loop_getElem?_zero (z r : ℕ) (s : Stmt) :
    (compileAux z (loop r s))[0]? = some (.decJz r ((compileAux z s).length + 2)) := rfl

/-- The last instruction of the code of a loop. -/
theorem compileAux_loop_getElem?_last (z r : ℕ) (s : Stmt) :
    (compileAux z (loop r s))[(compileAux z s).length + 1]? = some (.decJz z 0) := by
  have h₁ : ([Instr.decJz r ((compileAux z s).length + 2)] ++
      (compileAux z s).relocate 1).length = (compileAux z s).length + 1 := by
    simp
  rw [compileAux, List.getElem?_append_right (le_of_eq h₁), h₁, Nat.sub_self]
  rfl

/-- The length of the code of a loop. -/
theorem length_compileAux_loop (z r : ℕ) (s : Stmt) :
    (compileAux z (loop r s)).length = (compileAux z s).length + 2 := by
  simp [compileAux]

/-- A run of the code of the body of a loop, inside the code of the loop. -/
theorem reaches_compileAux_loop_body (z r : ℕ) (s : Stmt) {c c' : Cfg}
    (h : (compileAux z s).Reaches c c') :
    (compileAux z (loop r s)).Reaches (c.shift 1) (c'.shift 1) :=
  reaches_embed [.decJz r ((compileAux z s).length + 2)] [.decJz z 0] h

/-- **Compiler correctness, forward.** An execution of `s` is a run of its code from instruction
`0` to the end of the code. -/
theorem reaches_compileAux {z : ℕ} {s : Stmt} {σ σ' : ℕ → ℕ} (h : Exec s σ σ')
    (hz : σ z = 0) (hb : s.bound ≤ z) :
    (compileAux z s).Reaches ⟨0, σ⟩ ⟨(compileAux z s).length, σ'⟩ := by
  induction h with
  | skip σ => exact Reaches.refl _
  | inc r σ => exact Reaches.single (step_of_inc rfl)
  | @seq s t σ₁ σ₂ σ₃ h₁ _ ih₁ ih₂ =>
    simp only [bound, max_le_iff] at hb
    have hz₂ : σ₂ z = 0 := by rw [h₁.regs_eq_of_bound_le hb.1, hz]
    have r₁ := reaches_seq_left (compileAux z t) (ih₁ hz hb.1)
    have r₂ := reaches_seq_right (compileAux z s) (ih₂ hz₂ hb.2)
    simp only [Cfg.shift, Nat.zero_add] at r₂
    rw [compileAux, length_seq, Nat.add_comm]
    exact r₁.trans r₂
  | @loopDone r s σ h0 =>
    rw [length_compileAux_loop]
    exact Reaches.single (step_of_decJz_zero (compileAux_loop_getElem?_zero z r s) h0)
  | @loopStep r s σ₁ σ₂ σ₃ h0 hbody _ ih₁ ih₂ =>
    have hb' := hb
    simp only [bound, max_le_iff] at hb'
    have hzr : z ≠ r := by omega
    have hz₁ : update σ₁ r (σ₁ r - 1) z = 0 := by simp [hzr, hz]
    have hz₂ : σ₂ z = 0 := by rw [hbody.regs_eq_of_bound_le hb'.2, hz₁]
    have r₁ := reaches_compileAux_loop_body z r s (ih₁ hz₁ hb'.2)
    simp only [Cfg.shift, Nat.zero_add] at r₁
    exact Reaches.head (step_of_decJz_pos (compileAux_loop_getElem?_zero z r s) h0)
      (r₁.trans (Reaches.head
        (step_of_decJz_zero (compileAux_loop_getElem?_last z r s) hz₂) (ih₂ hz₂ hb)))

/-- **Compiler correctness, backward.** If the code of `s` halts from instruction `0`, then `s`
has an execution from the same registers. -/
theorem exists_exec_of_halts_compileAux {z : ℕ} {s : Stmt} {σ : ℕ → ℕ}
    (h : (compileAux z s).Halts ⟨0, σ⟩) (hz : σ z = 0) (hb : s.bound ≤ z) : ∃ σ', Exec s σ σ' := by
  induction s generalizing σ with
  | skip => exact ⟨σ, .skip σ⟩
  | inc r => exact ⟨_, .inc r σ⟩
  | seq s t ih₁ ih₂ =>
    simp only [bound, max_le_iff] at hb
    obtain ⟨σ₁, h₁⟩ := ih₁ (halts_of_halts_seq_left _ h) hz hb.1
    have hz₁ : σ₁ z = 0 := by rw [h₁.regs_eq_of_bound_le hb.1, hz]
    have r₁ := reaches_seq_left (compileAux z t) (reaches_compileAux h₁ hz hb.1)
    have h' : ((compileAux z s).seq (compileAux z t)).Halts
        ((⟨0, σ₁⟩ : Cfg).shift (compileAux z s).length) := by
      simpa [Cfg.shift] using (halts_iff_of_reaches r₁).1 h
    obtain ⟨σ₂, h₂⟩ := ih₂ (halts_of_halts_seq_right _ h') hz₁ hb.2
    exact ⟨σ₂, .seq h₁ h₂⟩
  | loop r s ih =>
    have hb' := hb
    simp only [bound, max_le_iff] at hb'
    have hzr : z ≠ r := by omega
    refine Halts.induction
      (C := fun c => ∀ σ, c = ⟨0, σ⟩ → σ z = 0 → ∃ σ', Exec (loop r s) σ σ') h ?_ σ rfl hz
    rintro c hc IH σ rfl hz
    by_cases h0 : σ r = 0
    · exact ⟨σ, .loopDone h0⟩
    · have s₁ := step_of_decJz_pos (c := ⟨0, σ⟩) (compileAux_loop_getElem?_zero z r s) h0
      have hz₁ : update σ r (σ r - 1) z = 0 := by simp [hzr, hz]
      have h₁ : (compileAux z (loop r s)).Halts
          ((⟨0, update σ r (σ r - 1)⟩ : Cfg).shift 1) := by
        simpa [Cfg.shift] using (halts_iff_of_reaches (Reaches.single s₁)).1 hc
      obtain ⟨σ₂, hbody⟩ := ih
        (halts_of_halts_embed [.decJz r ((compileAux z s).length + 2)] [.decJz z 0] h₁) hz₁ hb'.2
      have hz₂ : σ₂ z = 0 := by rw [hbody.regs_eq_of_bound_le hb'.2, hz₁]
      have r₁ := reaches_compileAux_loop_body z r s (reaches_compileAux hbody hz₁ hb'.2)
      simp only [Cfg.shift, Nat.zero_add] at r₁
      have r₂ : (compileAux z (loop r s)).Reaches₁ ⟨0, σ⟩ ⟨0, σ₂⟩ :=
        Reaches₁.head s₁ (r₁.tail
          (step_of_decJz_zero (compileAux_loop_getElem?_last z r s) hz₂))
      obtain ⟨σ₃, hl⟩ := IH _ r₂ σ₂ rfl hz₂
      exact ⟨σ₃, .loopStep h0 hbody hl⟩

/-- **Compiler correctness.** Started at instruction `0` with the zero register `s.zeroReg` zero,
the program `s.compile` halts exactly in the final states of `s`, at its `halt` instruction. -/
theorem mem_eval_compile {s : Stmt} {σ : ℕ → ℕ} (hz : σ s.zeroReg = 0) {c : Cfg} :
    c ∈ s.compile.eval ⟨0, σ⟩ ↔ ∃ σ', Exec s σ σ' ∧ c = ⟨s.compile.length - 1, σ'⟩ := by
  have hb : s.bound ≤ s.zeroReg := le_max_right _ _
  have hlen : s.compile.length - 1 = (compileAux s.zeroReg s).length := by simp [compile]
  have fwd : ∀ σ', Exec s σ σ' → (⟨s.compile.length - 1, σ'⟩ : Cfg) ∈ s.compile.eval ⟨0, σ⟩ := by
    intro σ' h
    rw [hlen]
    exact mem_eval.2 ⟨reaches_append_left _ (reaches_compileAux h hz hb),
      step_of_halt (by simp [compile])⟩
  constructor
  · intro hc
    obtain ⟨σ', h⟩ := exists_exec_of_halts_compileAux
      (halts_of_halts_append_left [.halt] (Part.dom_iff_mem.2 ⟨c, hc⟩)) hz hb
    exact ⟨σ', h, mem_eval_unique hc (fwd σ' h)⟩
  · rintro ⟨σ', h, rfl⟩
    exact fwd σ' h

/-- The result of running a compiled statement that has an execution. -/
theorem eval_compile_eq_some {s : Stmt} {σ σ' : ℕ → ℕ} (hz : σ s.zeroReg = 0) (h : Exec s σ σ') :
    s.compile.eval ⟨0, σ⟩ = Part.some ⟨s.compile.length - 1, σ'⟩ :=
  Part.eq_some_iff.2 ((mem_eval_compile hz).2 ⟨σ', h, rfl⟩)

/-- A compiled statement without execution never halts. -/
theorem eval_compile_eq_none {s : Stmt} {σ : ℕ → ℕ} (hz : σ s.zeroReg = 0)
    (h : ∀ σ', ¬Exec s σ σ') : s.compile.eval ⟨0, σ⟩ = Part.none :=
  Part.eq_none_iff.2 fun _ hc =>
    let ⟨σ', h', _⟩ := (mem_eval_compile hz).1 hc
    h σ' h'

/-- If the final states of `s` from `σ` are the states `F a` for `a` in a partial value `o`, the
compiled program evaluates to the corresponding partial configuration. -/
theorem eval_compile_eq_map {s : Stmt} {σ : ℕ → ℕ} (hz : σ s.zeroReg = 0) {α : Type*}
    (o : Part α) (F : α → ℕ → ℕ) (h : ∀ σ', Exec s σ σ' ↔ ∃ a ∈ o, σ' = F a) :
    s.compile.eval ⟨0, σ⟩ = o.map fun a => ⟨s.compile.length - 1, F a⟩ := by
  refine Part.ext fun c => ?_
  rw [mem_eval_compile hz, Part.mem_map_iff]
  constructor
  · rintro ⟨σ', hσ', rfl⟩
    obtain ⟨a, ha, rfl⟩ := (h σ').1 hσ'
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨F a, (h _).2 ⟨a, ha, rfl⟩, rfl⟩

/-- The zero register of a statement is zero in every initial configuration. -/
theorem init_regs_zeroReg (s : Stmt) (n : ℕ) : (Cfg.init n).regs s.zeroReg = 0 := by
  have : s.zeroReg ≠ 0 := by
    have : 1 ≤ s.zeroReg := le_max_left _ _
    omega
  simp [Cfg.init, this]

/-- **Compiled statements compute what they execute.** If `f n` is the content of register `0`
after executing `s` on the initial registers for the input `n`, then `s.compile` computes `f`. -/
theorem computes_compile {s : Stmt} {f : ℕ →. ℕ}
    (h : ∀ n v, v ∈ f n ↔ ∃ σ', Exec s (Cfg.init n).regs σ' ∧ σ' 0 = v) :
    s.compile.Computes f := by
  intro n
  have hz := init_regs_zeroReg s n
  refine Part.ext fun v => ?_
  rw [h, Part.mem_map_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨σ', hσ', rfl⟩ := (mem_eval_compile (σ := (Cfg.init n).regs) hz).1 hc
    exact ⟨σ', hσ', rfl⟩
  · rintro ⟨σ', hσ', rfl⟩
    exact ⟨_, (mem_eval_compile (σ := (Cfg.init n).regs) hz).2 ⟨σ', hσ', rfl⟩, rfl⟩

/-- Every jump in the code of a statement goes to a position inside the code or just after it. -/
theorem le_length_of_mem_compileAux {z : ℕ} {s : Stmt} {x l : ℕ}
    (h : .decJz x l ∈ compileAux z s) : l ≤ (compileAux z s).length := by
  induction s generalizing l with
  | skip => simp [compileAux] at h
  | inc r => simp [compileAux] at h
  | seq s t ih₁ ih₂ =>
    simp only [compileAux, Program.seq, List.mem_append, mem_relocate_decJz] at h
    rw [compileAux, length_seq]
    rcases h with h | ⟨l', h, rfl⟩
    · have := ih₁ h
      omega
    · have := ih₂ h
      omega
  | loop r s ih =>
    rw [length_compileAux_loop]
    simp only [compileAux, List.mem_append, List.mem_singleton, Instr.decJz.injEq,
      mem_relocate_decJz] at h
    rcases h with (⟨-, rfl⟩ | ⟨l', h, rfl⟩) | ⟨-, rfl⟩
    · omega
    · have := ih h
      omega
    · omega

/-- Compiled statements are well-formed programs: every jump stays inside the program and the last
instruction is `halt`. -/
theorem wellFormed_compile (s : Stmt) : s.compile.WellFormed := by
  refine ⟨fun x l h => ?_, by simp [compile]⟩
  simp only [compile, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h
  have := le_length_of_mem_compileAux h
  simp only [compile, List.length_append, List.length_singleton]
  omega

end Stmt

/-! ### Sanity checks -/

/-- The code generated for `move 1 0` is literally the hand-written `addProg`. -/
theorem compile_move_eq : (move 1 0).compile = addProg := rfl

/-- A statement that never terminates: after `inc 0` the loop on register `0` re-increments it
for ever. -/
def spin : Stmt := seq (inc 0) (loop 0 (inc 0))

/-- `spin` has no execution. -/
theorem not_exec_spin (σ σ' : ℕ → ℕ) : ¬Exec spin σ σ' := by
  simp only [spin, exec_seq_iff, exec_inc_iff, exists_eq_left]
  rw [exec_loop_iff_of_seq (fun _ => update σ 0 (σ 0 + 1)) (fun k _ τ => by
    rw [exec_inc_iff]
    refine iff_of_eq (congrArg _ ?_)
    funext x
    grind [update_apply])]
  simp

/-- The program compiled from `spin` never halts. -/
theorem eval_compile_spin (n : ℕ) : spin.compile.eval (Cfg.init n) = Part.none :=
  eval_compile_eq_none (init_regs_zeroReg spin n) (not_exec_spin _)

/-- A statement doubling register `0`, with scratch registers `1` and `2`. -/
def double : Stmt := seq (move₂ 0 1 2) (seq (move 1 0) (move 2 0))

/-- The program compiled from `double` computes `n ↦ 2 * n`. -/
theorem compile_double_computes : double.compile.Computes fun n => Part.some (2 * n) := by
  refine computes_compile fun n v => ?_
  have h₁ : (0 : ℕ) ≠ 1 := by omega
  have h₂ : (0 : ℕ) ≠ 2 := by omega
  have h₃ : (1 : ℕ) ≠ 2 := by omega
  simp only [double, exec_seq_iff, exec_move₂_iff h₁ h₂ h₃, exec_move_iff h₁.symm,
    exec_move_iff h₂.symm, exists_eq_left, Part.mem_some_iff, Cfg.init]
  constructor
  · rintro rfl
    simp
    omega
  · simp
    omega

end LeanTheory.Computability
