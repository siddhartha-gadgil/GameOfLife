/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Boxes
public meta import LeanTheory.Certificates.LifeCert
public meta import LeanTheory.Theory.Life.Boxes

/-!
# Evolution certificates that deliver a footprint

`life_cert` certifies the result of an evolution. For composing components one also needs to
know where the pattern is at every intermediate generation. This module extends the
certificate so that it delivers a rectangular footprint at no extra cost in generations.

* `EvolvesIn a b lo hi n x y ts x' y' ts'`: the certificate predicate `Evolves` of
  `Certificates/LifeSim` with, at every generation, one additional kernel fact: the Boolean
  check `boxCheck` that the (trimmed) window of that generation lies in the box
  `Box a b lo hi`.
* `EvolvesIn.reaction`: soundness, in the form of a reaction with a constant box as footprint:
  `Reaction (ofRows x y rows) (ofRows x' y' rows') n (fun _ => Box a b lo hi)`.
* The tactic **`life_reaction`** proves goals of the form
  `Reaction S T n (fun _ => Box a b lo hi)` for closed data, where `S` and `T` are (or unfold
  to) windows. As with `life_cert`, the window of `T` must be the trimmed result; the untrusted
  `meta` simulation also checks the box and reports the generation at which the pattern leaves
  it.

**Sanity.** `glider_reaction_fixture` (accepted: four generations of the glider inside a 4 × 4
box), and a rejected fixture (`fail_if_success`: the same with a box that is one row too
small).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- Evolution certificate with a box: as `Evolves`, and the window of every generation passes
`boxCheck` for the box with bounds `a`, `b`, `lo`, `hi`. Rows are tagged literals. -/
inductive EvolvesIn (a b lo hi : ℤ) : ℕ → ℤ → ℤ → List ℕ → ℤ → ℤ → List ℕ → Prop where
  /-- No generation: the window lies in the box. -/
  | done (x y : ℤ) (rows : List ℕ) (hb : boxCheck x y (rows.map untag) a b lo hi = true) :
      EvolvesIn a b lo hi 0 x y rows x y rows
  /-- One generation, certified row by row, from a window in the box. -/
  | step (n : ℕ) (x y : ℤ) (rows rows₁ : List ℕ) (x' y' : ℤ) (rows' : List ℕ)
      (hb : boxCheck x y (rows.map untag) a b lo hi = true) (h : RowsStep 0 0 rows rows₁)
      (e : EvolvesIn a b lo hi n (x - 1) (y - 1) rows₁ x' y' rows') :
      EvolvesIn a b lo hi (n + 1) x y rows x' y' rows'
  /-- Replace a window by its trimmed form. -/
  | trim (n : ℕ) (x y : ℤ) (full : List ℕ) (t pre : ℕ) (rows : List ℕ) (x' y' : ℤ)
      (rows' : List ℕ) (h : Padded t pre rows full)
      (e : EvolvesIn a b lo hi n (x + t) (y + pre) rows x' y' rows') :
      EvolvesIn a b lo hi n x y full x' y' rows'

/-- A certificate with a box is in particular a certificate. -/
theorem EvolvesIn.evolves {a b lo hi : ℤ} {n : ℕ} {x y : ℤ} {rows : List ℕ} {x' y' : ℤ}
    {rows' : List ℕ} (h : EvolvesIn a b lo hi n x y rows x' y' rows') :
    Evolves n x y rows x' y' rows' := by
  induction h with
  | done x y rows hb => exact Evolves.done x y rows
  | step n x y rows rows₁ x' y' rows' hb h e ih =>
    exact Evolves.step n x y rows rows₁ x' y' rows' h ih
  | trim n x y full t pre rows x' y' rows' h e ih =>
    exact Evolves.trim n x y full t pre rows x' y' rows' h ih

/-- Every generation of a certified evolution lies in the box. -/
theorem EvolvesIn.subset_box {a b lo hi : ℤ} {n : ℕ} {x y : ℤ} {rows : List ℕ} {x' y' : ℤ}
    {rows' : List ℕ} (h : EvolvesIn a b lo hi n x y rows x' y' rows') :
    ∀ i ≤ n, (conway.evolve i (ofRows x y (rows.map untag)) : Set Cell) ⊆ Box a b lo hi := by
  induction h with
  | done x y rows hb =>
    intro i hi
    obtain rfl : i = 0 := by omega
    exact coe_ofRows_subset_box hb
  | step n x y rows rows₁ x' y' rows' hb h e ih =>
    intro i hi
    cases i with
    | zero => exact coe_ofRows_subset_box hb
    | succ j =>
      have h1 := h.eq
      rw [untag_zero] at h1
      rw [Rule.evolve_succ', step_ofRows, stepRows, h1]
      exact ih j (by omega)
  | trim n x y full t pre rows x' y' rows' h e ih =>
    intro i hi
    rw [h.ofRows_eq]
    exact ih i hi

/-- **Soundness**: a certificate with a box is a reaction whose footprint is the box. `ts` and
`ts'` are the tagged forms of the rows. -/
theorem EvolvesIn.reaction {a b lo hi : ℤ} {n : ℕ} {x y : ℤ} {ts rows : List ℕ} {x' y' : ℤ}
    {ts' rows' : List ℕ} (h₀ : Tagged ts rows) (h : EvolvesIn a b lo hi n x y ts x' y' ts')
    (h₁ : Tagged ts' rows') :
    Reaction (ofRows x y rows) (ofRows x' y' rows') n (fun _ => Box a b lo hi) := by
  refine ⟨Evolves.sound h₀ h.evolves h₁, fun i hi => ?_⟩
  rw [← h₀.eq]
  exact h.subset_box i hi

/-- Sequential composition of reactions with the same constant footprint. -/
theorem Reaction.seq_const {P Q R : Finset Cell} {n m : ℕ} {B : Set Cell}
    (h : Reaction P Q n (fun _ => B)) (h' : Reaction Q R m (fun _ => B)) :
    Reaction P R (n + m) (fun _ => B) :=
  (h.seq h').mono fun i _ => by
    split_ifs <;> exact subset_rfl

/-- A window as a padded window at another origin. -/
theorem ofRows_eq_padRows' (x₀ y₀ x y : ℤ) (pre t : ℕ) (rows : List ℕ) (hx : x = x₀ + t)
    (hy : y = y₀ + pre) : ofRows x y rows = ofRows x₀ y₀ (padRows pre t rows) := by
  rw [ofRows_padRows, hx, hy]

namespace Cert

open Lean Meta Elab Tactic

/-- `meta` copy of `boxCheck` on plain rows. -/
meta def boxCheckM (x y : Int) (rows : List Nat) (a b lo hi : Int) : Bool :=
  decide (a ≤ x) && decide (lo ≤ y) && decide (y + rows.length ≤ hi + 1) &&
    rows.all fun r => decide (r < 2 ^ (b + 1 - x).toNat)

/-- The kernel fact `true = true`, to be checked against `boxCheck … = true`. -/
meta def boxLeaf : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- Simulates `n` generations from the window `(x, y, rows)` and builds a proof of
`EvolvesIn a b lo hi n x y ts x' y' ts'`. Fails if the pattern leaves the box. Returns the final
window, the expressions of the initial and final tagged rows, and the proof. -/
meta def mkEvolvesIn (a b lo hi : Int) (n : Nat) (x y : Int) (rows : List Nat) :
    Except String (Int × Int × List Nat × Expr × Expr × Expr) := do
  let boxArgs := #[intE a, intE b, intE lo, intE hi]
  let rowsE₀ := listE rows
  let mut stages : Array Stage := #[]
  let mut cx := x
  let mut cy := y
  let mut cur := rows
  let mut curE := rowsE₀
  for i in [0:n] do
    unless boxCheckM cx cy cur a b lo hi do
      throw s!"at generation {i} the pattern leaves the box: its window is \
        ofRows ({cx}) ({cy}) with {cur.length} rows"
    let (rows₁, _, rows₁E, stepPf) := mkRowsStep 0 0 cur
    let (pre, post, t, trimmed) := trimRows rows₁
    let (trimmedE, _, padPf) := mkPadded t pre trimmed post
    stages := stages.push
      { x := cx, y := cy, rowsE := curE, rows₁E, stepPf, t, pre, trimmedE, padPf }
    cx := cx - 1 + t
    cy := cy - 1 + pre
    cur := trimmed
    curE := trimmedE
  unless boxCheckM cx cy cur a b lo hi do
    throw s!"at generation {n} the pattern leaves the box: its window is \
      ofRows ({cx}) ({cy}) with {cur.length} rows"
  let xE := intE cx
  let yE := intE cy
  let mut pf := mkAppN (mkConst ``EvolvesIn.done) (boxArgs ++ #[xE, yE, curE, boxLeaf])
  let mut k := 0
  for s in stages.reverse do
    let inner := mkAppN (mkConst ``EvolvesIn.trim)
      (boxArgs ++ #[natE k, intE (s.x - 1), intE (s.y - 1), s.rows₁E, natE s.t, natE s.pre,
        s.trimmedE, xE, yE, curE, s.padPf, pf])
    pf := mkAppN (mkConst ``EvolvesIn.step)
      (boxArgs ++ #[natE k, intE s.x, intE s.y, s.rowsE, s.rows₁E, xE, yE, curE, boxLeaf,
        s.stepPf, inner])
    k := k + 1
  return (cx, cy, cur, rowsE₀, curE, pf)

/-- **`life_reaction`**: prove `Reaction S T n (fun _ => Box a b lo hi)` for closed data, where
`S` and `T` are (or unfold to) windows and `T` is the trimmed window of the result, by an
explicit proof term (`EvolvesIn.reaction`) whose leaves are kernel facts. -/
syntax (name := lifeReaction) "life_reaction" : tactic

/-- The elaborator of `life_reaction`. -/
@[tactic lifeReaction] meta def evalLifeReaction : Tactic := fun _ => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``Reaction 4 do
    throwError "life_reaction: expected a goal `Reaction S T n (fun _ => Box a b lo hi)`"
  let n ← natOf (ty.getArg! 2)
  let .lam _ _ body _ := ty.getArg! 3
    | throwError "life_reaction: the footprint must be `fun _ => Box a b lo hi`"
  unless body.isAppOfArity ``Box 4 && !body.hasLooseBVars do
    throwError "life_reaction: the footprint must be `fun _ => Box a b lo hi`"
  let a ← intOf (body.getArg! 0)
  let b ← intOf (body.getArg! 1)
  let lo ← intOf (body.getArg! 2)
  let hi ← intOf (body.getArg! 3)
  let (xe, ye, rowse) ← asOfRows (ty.getArg! 0)
  let x ← intOf xe
  let y ← intOf ye
  let rows ← natListOf rowse
  let (xe', ye', rowse') ← asOfRows (ty.getArg! 1)
  let ex ← intOf xe'
  let ey ← intOf ye'
  let erows ← natListOf rowse'
  match mkEvolvesIn a b lo hi n x y rows with
  | .error msg => throwError "life_reaction: {msg}"
  | .ok (x', y', rows', tsE, ts'E, pf) =>
    unless ex == x' && ey == y' && erows == rows' do
      throwError "life_reaction: the stated result differs from the computed one, which is the \
        (trimmed) window\n  ofRows ({x'}) ({y'}) {rows'}"
    let (_, rowsE, tagPf) := mkTagged rows
    let (_, rows'E, tagPf') := mkTagged rows'
    g.assign (mkAppN (mkConst ``EvolvesIn.reaction)
      #[intE a, intE b, intE lo, intE hi, natE n, intE x, intE y, tsE, rowsE, intE x', intE y',
        ts'E, rows'E, tagPf, pf, tagPf'])
    replaceMainGoal []

end Cert

/-- **Sanity** (accepted fixture): four generations of the glider stay in a 4 × 4 box. -/
theorem glider_reaction_fixture :
    Reaction (ofRows 0 0 [2, 4, 7]) (ofRows 1 1 [2, 4, 7]) 4 (fun _ => Box 0 3 0 3) := by
  life_reaction

/-- **Sanity** (rejected fixture): the box with one row less is refused. -/
example : True := by
  fail_if_success
    have : Reaction (ofRows 0 0 [2, 4, 7]) (ofRows 1 1 [2, 4, 7]) 4 (fun _ => Box 0 3 0 2) := by
      life_reaction
  trivial

end LeanTheory.Life
