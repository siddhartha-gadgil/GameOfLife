/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.BoxCert
public meta import LeanTheory.Theory.Life.BoxCert

/-!
# Evolution certificates for a predicate on cells

A generalization of `Theory/Life/BoxCert`: an evolution certificate that checks, at every
generation, that every live cell satisfies a given Boolean predicate `p : ℤ → ℤ → Bool`. Boxes
are the special case `p x y = (a ≤ x ≤ b ∧ lo ≤ y ≤ hi)`; other useful predicates bound
diagonals (`x - y`, `x + y`), which is what gliders on diagonal lanes need.

* `rowCheck`, `cellCheck`: Boolean checks that every set bit of a row, resp. every live cell of a
  window, satisfies `p`; `cellCheck_sound`.
* `EvolvesP p n x y ts x' y' ts'`: the certificate predicate `Evolves` with one additional kernel
  fact per generation, `cellCheck p x y rows 128 = true`.
* `EvolvesP.forall_le`: soundness, every cell at every generation `i ≤ n` satisfies `p`.
* The tactic **`life_invariant`** proves goals
  `∀ i ≤ n, ∀ c ∈ conway.evolve i W, p c.1 c.2 = true` for a closed window `W` (or a definition
  that unfolds to one) and a closed predicate `p`.

Windows wider than 128 cells are rejected by the check (the bound keeps the per-row loop
structural).

**Sanity.** `glider_invariant_fixture` (the glider stays on its diagonal band),
`glider_invariant_narrow_false` (a narrower band is false). A wrong predicate is refused by the
kernel, not by the tactic.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- `rowCheck p y n x r`: every set bit `j < n` of `r` gives a cell `(x + j, y)` satisfying `p`.
Stops as soon as the rest of the row is empty. -/
def rowCheck (p : ℤ → ℤ → Bool) (y : ℤ) : ℕ → ℤ → ℕ → Bool
  | 0, _, _ => true
  | n + 1, x, r => r == 0 || ((r % 2 != 1 || p x y) && rowCheck p y n (x + 1) (r / 2))

/-- Soundness of `rowCheck`. -/
theorem rowCheck_sound {p : ℤ → ℤ → Bool} {y : ℤ} {n : ℕ} {x : ℤ} {r : ℕ}
    (h : rowCheck p y n x r = true) : ∀ j < n, r.testBit j = true → p (x + j) y = true := by
  induction n generalizing x r with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj hb
    simp only [rowCheck, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with h0 | ⟨h1, h2⟩
    · subst h0
      simp at hb
    · cases j with
      | zero =>
        rw [Nat.testBit_zero, decide_eq_true_eq] at hb
        simpa [hb] using h1
      | succ j =>
        rw [Nat.testBit_succ] at hb
        have := ih h2 j (by omega) hb
        rwa [show x + 1 + (j : ℤ) = x + ((j + 1 : ℕ) : ℤ) by push_cast; omega] at this

/-- Every live cell of the window `(x, y, rows)` satisfies `p` (rows narrower than `2 ^ w`). -/
def cellCheck (p : ℤ → ℤ → Bool) (x y : ℤ) (rows : List ℕ) (w : ℕ) : Bool :=
  (List.range rows.length).all fun i =>
    decide (rows.getD i 0 < 2 ^ w) && rowCheck p (y + i) w x (rows.getD i 0)

/-- **Soundness of `cellCheck`.** -/
theorem cellCheck_sound {p : ℤ → ℤ → Bool} {x y : ℤ} {rows : List ℕ} {w : ℕ}
    (h : cellCheck p x y rows w = true) : ∀ c ∈ ofRows x y rows, p c.1 c.2 = true := by
  intro c hc
  have hx := (le_of_mem_ofRows hc).1
  have hy := (le_of_mem_ofRows hc).2
  have hlen := snd_lt_of_mem_ofRows hc
  rw [mem_ofRows, bitAt] at hc
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c.1 - x by omega)
  obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c.2 - y by omega)
  rw [hj, hi, rowZ_natCast, tb_natCast] at hc
  simp only [cellCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨hw, hr⟩ := h i (by omega)
  have hjw : j < w := by
    by_contra hcon
    have h1 := Nat.ge_two_pow_of_testBit hc
    have h2 : 2 ^ w ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have := rowCheck_sound hr j hjw hc
  rwa [show x + (j : ℤ) = c.1 by omega, show y + (i : ℤ) = c.2 by omega] at this

/-- Evolution certificate with a predicate on cells: as `Evolves`, and the window of every
generation passes `cellCheck p … 128`. Rows are tagged literals. -/
inductive EvolvesP (p : ℤ → ℤ → Bool) : ℕ → ℤ → ℤ → List ℕ → ℤ → ℤ → List ℕ → Prop where
  /-- No generation: the window passes the check. -/
  | done (x y : ℤ) (rows : List ℕ) (hb : cellCheck p x y (rows.map untag) 128 = true) :
      EvolvesP p 0 x y rows x y rows
  /-- One generation, certified row by row, from a window that passes the check. -/
  | step (n : ℕ) (x y : ℤ) (rows rows₁ : List ℕ) (x' y' : ℤ) (rows' : List ℕ)
      (hb : cellCheck p x y (rows.map untag) 128 = true) (h : RowsStep 0 0 rows rows₁)
      (e : EvolvesP p n (x - 1) (y - 1) rows₁ x' y' rows') :
      EvolvesP p (n + 1) x y rows x' y' rows'
  /-- Replace a window by its trimmed form. -/
  | trim (n : ℕ) (x y : ℤ) (full : List ℕ) (t pre : ℕ) (rows : List ℕ) (x' y' : ℤ)
      (rows' : List ℕ) (h : Padded t pre rows full)
      (e : EvolvesP p n (x + t) (y + pre) rows x' y' rows') :
      EvolvesP p n x y full x' y' rows'

/-- **Soundness**: every live cell at every generation `i ≤ n` satisfies `p`. -/
theorem EvolvesP.forall_le {p : ℤ → ℤ → Bool} {n : ℕ} {x y : ℤ} {rows : List ℕ} {x' y' : ℤ}
    {rows' : List ℕ} (h : EvolvesP p n x y rows x' y' rows') :
    ∀ i ≤ n, ∀ c ∈ conway.evolve i (ofRows x y (rows.map untag)), p c.1 c.2 = true := by
  induction h with
  | done x y rows hb =>
    intro i hi
    obtain rfl : i = 0 := by omega
    exact cellCheck_sound hb
  | step n x y rows rows₁ x' y' rows' hb h e ih =>
    intro i hi
    cases i with
    | zero => exact cellCheck_sound hb
    | succ j =>
      have h1 := h.eq
      rw [untag_zero] at h1
      rw [Rule.evolve_succ', step_ofRows, stepRows, h1]
      exact ih j (by omega)
  | trim n x y full t pre rows x' y' rows' h e ih =>
    intro i hi
    rw [h.ofRows_eq]
    exact ih i hi

/-- Soundness on plain rows. -/
theorem EvolvesP.forall_le' {p : ℤ → ℤ → Bool} {n : ℕ} {x y : ℤ} {ts rows : List ℕ} {x' y' : ℤ}
    {ts' : List ℕ} (h₀ : Tagged ts rows) (h : EvolvesP p n x y ts x' y' ts') :
    ∀ i ≤ n, ∀ c ∈ conway.evolve i (ofRows x y rows), p c.1 c.2 = true := by
  rw [← h₀.eq]
  exact h.forall_le

namespace Cert

open Lean Meta Elab Tactic

/-- Simulates `n` generations from the window `(x, y, rows)` and builds a proof of
`EvolvesP p n x y ts x' y' ts'`; the predicate is checked by the kernel only. -/
meta def mkEvolvesP (pE : Expr) (n : Nat) (x y : Int) (rows : List Nat) :
    Int × Int × List Nat × Expr × Expr × Expr := Id.run do
  let rowsE₀ := listE rows
  let mut stages : Array Stage := #[]
  let mut cx := x
  let mut cy := y
  let mut cur := rows
  let mut curE := rowsE₀
  for _ in [0:n] do
    let (rows₁, _, rows₁E, stepPf) := mkRowsStep 0 0 cur
    let (pre, post, t, trimmed) := trimRows rows₁
    let (trimmedE, _, padPf) := mkPadded t pre trimmed post
    stages := stages.push
      { x := cx, y := cy, rowsE := curE, rows₁E, stepPf, t, pre, trimmedE, padPf }
    cx := cx - 1 + t
    cy := cy - 1 + pre
    cur := trimmed
    curE := trimmedE
  let xE := intE cx
  let yE := intE cy
  let mut pf := mkAppN (mkConst ``EvolvesP.done) #[pE, xE, yE, curE, boxLeaf]
  let mut k := 0
  for s in stages.reverse do
    let inner := mkAppN (mkConst ``EvolvesP.trim)
      #[pE, natE k, intE (s.x - 1), intE (s.y - 1), s.rows₁E, natE s.t, natE s.pre,
        s.trimmedE, xE, yE, curE, s.padPf, pf]
    pf := mkAppN (mkConst ``EvolvesP.step)
      #[pE, natE k, intE s.x, intE s.y, s.rowsE, s.rows₁E, xE, yE, curE, boxLeaf, s.stepPf,
        inner]
    k := k + 1
  return (cx, cy, cur, rowsE₀, curE, pf)

/-- **`life_invariant`**: prove `∀ i ≤ n, ∀ c ∈ conway.evolve i W, p c.1 c.2 = true` for closed
`n`, a closed window `W` and a closed predicate `p`, by an explicit proof term
(`EvolvesP.forall_le'`) whose leaves are kernel facts. -/
syntax (name := lifeInvariant) "life_invariant" : tactic

/-- The elaborator of `life_invariant`. -/
@[tactic lifeInvariant] meta def evalLifeInvariant : Tactic := fun _ => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let err : MetaM Unit := throwError
    "life_invariant: expected `∀ i ≤ n, ∀ c ∈ conway.evolve i W, p c.1 c.2 = true`"
  forallTelescope ty fun xs body => do
    unless xs.size == 4 do err
    let hiTy ← inferType xs[1]!
    let_expr LE.le _ _ _ nE := hiTy | err
    let hcTy ← inferType xs[3]!
    let_expr Membership.mem _ _ _ evE _ := hcTy | err
    unless evE.isAppOfArity ``Rule.evolve 3 do err
    let_expr Eq _ lhs _ := body | err
    let pE := lhs.getAppFn
    unless !pE.hasLooseBVars && !pE.hasFVar && lhs.getAppNumArgs == 2 do err
    let n ← natOf nE
    let (xe, ye, rowse) ← asOfRows (evE.getArg! 2)
    let x ← intOf xe
    let y ← intOf ye
    let rows ← natListOf rowse
    let (x', y', _, tsE, ts'E, pf) := mkEvolvesP pE n x y rows
    let (_, rowsE, tagPf) := mkTagged rows
    g.assign (mkAppN (mkConst ``EvolvesP.forall_le')
      #[pE, natE n, intE x, intE y, tsE, rowsE, intE x', intE y', ts'E, tagPf, pf])
  replaceMainGoal []

end Cert

/-- **Sanity** (accepted fixture): in its first 16 generations the glider stays in the
diagonal band `-1 ≤ x - y ≤ 1`. -/
theorem glider_invariant_fixture :
    ∀ i ≤ 16, ∀ c ∈ conway.evolve i (ofRows 0 0 [2, 4, 7]),
      (fun x y : ℤ => decide (-2 ≤ x - y) && decide (x - y ≤ 2)) c.1 c.2 = true := by
  life_invariant

/-- **Sanity** (the check has content): the narrower band `x - y = 0` fails already at
generation 0. A certificate for it is refused by the kernel (the `meta` builder does not check
the predicate). -/
theorem glider_invariant_narrow_false :
    ¬ ∀ i ≤ 4, ∀ c ∈ conway.evolve i (ofRows 0 0 [2, 4, 7]),
      (fun x y : ℤ => decide (x - y = 0)) c.1 c.2 = true := by
  intro h
  have h1 := h 0 (by norm_num) (1, 0) (by rw [Rule.evolve_zero, mem_ofRows]; rfl)
  simp at h1

end LeanTheory.Life
