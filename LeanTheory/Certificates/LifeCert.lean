/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.LifeSim
public meta import Lean.Elab.Tactic.Basic
public meta import LeanTheory.Certificates.LifeSim

/-!
# The tactic `life_cert`: evolution certificates as explicit proof terms

`life_cert` proves goals of the form

* `conway.evolve n (ofRows x y rows) = ofRows x' y' rows'`, or
* `conway.evolve n (ofRows x y rows) = ∅`,

where `n`, the origins and the rows are closed terms (either side may also be a definition that
unfolds to a window). It follows the SubsetSum pattern: untrusted `meta` code simulates the
`n` generations and assembles a term of `Evolves n x y rows x' y' rows'` (`Certificates/LifeSim`),
trimming the window after every generation; `Evolves.sound` turns it into the statement. The
kernel checks one fact `nextRow (untag u) (untag m) (untag d) = untag r` per row and generation,
and one fact `untag r <<< t = untag r'` per row for each trimming, each by evaluating a fixed
number of bitwise operations on natural number literals. Rows are stored as tagged literals
(`Certificates/LifeSim`), so that literals of wide sparse rows do not collide in the kernel's
hash tables. No `decide` of any kind is involved, and nothing here is trusted: a wrong
simulation produces a term that the kernel rejects.

The window on the right-hand side must be the **trimmed** window of the result (no empty rows
above or below, some row with its lowest bit set); otherwise the tactic fails and reports the
trimmed result it computed.

**Sanity.** `glider_evolve_four` (accepted: the glider moves one cell diagonally in four
generations), `blinker_evolve_two` (accepted), `domino_evolve_one` (accepted, dies out), and a
rejected fixture (`fail_if_success`: a false displacement of the glider is refused).
-/

public section

namespace LeanTheory.Life.Cert

open Lean Meta Elab Tactic

/-- `meta` copy of `xor3`. -/
meta def xor3M (a b c : Nat) : Nat := a ^^^ b ^^^ c

/-- `meta` copy of `maj3`. -/
meta def maj3M (a b c : Nat) : Nat := (a &&& b) ||| (a &&& c) ||| (b &&& c)

/-- `meta` copy of `nextRow`, used only to propose the rows; the kernel re-evaluates
`nextRow` itself in every leaf. -/
meta def nextRowM (u m d : Nat) : Nat :=
  let su := xor3M (u <<< 2) (u <<< 1) u
  let cu := maj3M (u <<< 2) (u <<< 1) u
  let sd := xor3M (d <<< 2) (d <<< 1) d
  let cd := maj3M (d <<< 2) (d <<< 1) d
  let sm := (m <<< 2) ^^^ m
  let cm := (m <<< 2) &&& m
  let ones := xor3M su sd sm
  let carry := maj3M su sd sm
  let odd := (cu ^^^ cd) ^^^ (cm ^^^ carry)
  let two := (cu &&& cd) ||| (cm &&& carry)
  let exactlyOne := odd ^^^ (odd &&& two)
  exactlyOne &&& (ones ||| (m <<< 1))

/-- The type `ℕ` as an expression. -/
meta def natTy : Expr := mkConst ``Nat

/-- A raw natural number literal. -/
meta def natE (n : Nat) : Expr := mkRawNatLit n

/-- An integer as a constructor applied to a raw literal. -/
meta def intE : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (natE n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (natE n)

/-- The empty list of naturals. -/
meta def nilE : Expr := mkApp (mkConst ``List.nil [Level.zero]) natTy

/-- `h :: t` for a list of naturals. -/
meta def consE (h t : Expr) : Expr := mkApp3 (mkConst ``List.cons [Level.zero]) natTy h t

/-- The tagged form of a row: the row above bit 64 and, in the low 64 bits, its residue modulo
a 64-bit prime. Different rows get different hashes (up to rare coincidences), which is all that
matters; the kernel never computes a tag. -/
meta def tagM (r : Nat) : Nat := (r <<< 64) ||| (r % 18446744073709551557)

/-- The tagged literal of a row. -/
meta def tagE (r : Nat) : Expr := natE (tagM r)

/-- The term `untag e` for the tagged literal `e` of the row `r`. -/
meta def untagE (r : Nat) : Expr := mkApp (mkConst ``untag) (tagE r)

/-- A list of rows as an expression of tagged literals. -/
meta def listE : List Nat → Expr
  | [] => nilE
  | a :: l => consE (tagE a) (listE l)

/-- The kernel fact `untag e = untag e` for the tagged literal `e` of the row `r`, to be checked
against a statement `f … = untag e`. No untagged literal occurs in it. -/
meta def reflE (r : Nat) : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) natTy (untagE r)

/-- Builds a proof of `Tagged ts rows` for the tagged literals `ts` of `rows`. Returns the
expressions of `ts` and of `rows` (plain literals), and the proof. -/
meta def mkTagged : List Nat → Expr × Expr × Expr
  | [] => (nilE, nilE, mkConst ``Tagged.nil)
  | r :: rs =>
    let (tsE, rsE, pf) := mkTagged rs
    (consE (tagE r) tsE, consE (natE r) rsE,
      mkAppN (mkConst ``Tagged.cons)
        #[tagE r, natE r, tsE, rsE, mkApp2 (mkConst ``Eq.refl [Level.one]) natTy (natE r), pf])

/-- Builds the rows `rs = stepAux u m ds` and a proof of `RowsStep` for their tagged literals.
Returns the value of `rs`, the expressions of the tagged `ds` and `rs`, and the proof. -/
meta def mkRowsStep (u m : Nat) : List Nat → List Nat × Expr × Expr × Expr
  | [] =>
    let r₁ := nextRowM u m 0
    let r₂ := nextRowM m 0 0
    ([r₁, r₂], nilE, listE [r₁, r₂],
      mkAppN (mkConst ``RowsStep.nil) #[tagE u, tagE m, tagE r₁, tagE r₂, reflE r₁, reflE r₂])
  | d :: ds =>
    let r := nextRowM u m d
    let (rs, dsE, rsE, pf) := mkRowsStep m d ds
    (r :: rs, consE (tagE d) dsE, consE (tagE r) rsE,
      mkAppN (mkConst ``RowsStep.cons)
        #[tagE u, tagE m, tagE d, tagE r, dsE, rsE, reflE r, pf])

/-- The number of trailing zero bits of a positive number (`0` for `0`). -/
meta partial def trailingZeros (n : Nat) : Nat :=
  if n == 0 || n % 2 == 1 then 0 else trailingZeros (n / 2) + 1

/-- Trims a window: returns the number `pre` of empty rows above, the number `post` of empty
rows below, the common number `t` of empty columns on the left, and the trimmed rows. -/
meta def trimRows (rows : List Nat) : Nat × Nat × Nat × List Nat :=
  let l₁ := rows.dropWhile (· == 0)
  let pre := rows.length - l₁.length
  let l₂ := (l₁.reverse.dropWhile (· == 0)).reverse
  let post := l₁.length - l₂.length
  let t := match (l₂.filter (· != 0)).map trailingZeros with
    | [] => 0
    | a :: as => as.foldl min a
  (pre, post, t, l₂.map (· >>> t))

/-- Builds a proof of `Padded t 0 rows full` for the trimmed rows followed by `post` empty rows.
Returns the expressions of `rows` and `full`, and the proof. -/
meta def mkPaddedCore (t : Nat) : List Nat → Nat → Expr × Expr × Expr
  | [], 0 => (nilE, nilE, mkApp (mkConst ``Padded.nil) (natE t))
  | [], post + 1 =>
    let (rowsE, fullE, pf) := mkPaddedCore t [] post
    (rowsE, consE (natE 0) fullE, mkApp3 (mkConst ``Padded.zero) (natE t) fullE pf)
  | r :: rs, post =>
    let r' := r <<< t
    let (rowsE, fullE, pf) := mkPaddedCore t rs post
    (consE (tagE r) rowsE, consE (tagE r') fullE,
      mkAppN (mkConst ``Padded.row) #[natE t, tagE r, tagE r', rowsE, fullE, reflE r', pf])

/-- Builds a proof of `Padded t pre rows full`. Returns the expressions of `rows` and `full`, and
the proof. -/
meta def mkPadded (t pre : Nat) (rows : List Nat) (post : Nat) : Expr × Expr × Expr := Id.run do
  let (rowsE, fullE, pf) := mkPaddedCore t rows post
  let mut fullE := fullE
  let mut pf := pf
  for k in [0:pre] do
    pf := mkAppN (mkConst ``Padded.lead) #[natE t, natE k, rowsE, fullE, pf]
    fullE := consE (natE 0) fullE
  return (rowsE, fullE, pf)

/-- One generation followed by trimming, as data for the assembly of `Evolves`. -/
structure Stage where
  /-- Origin before the generation. -/
  x : Int
  /-- Origin before the generation. -/
  y : Int
  /-- The rows before the generation. -/
  rowsE : Expr
  /-- The rows after the generation, before trimming. -/
  rows₁E : Expr
  /-- Proof of `RowsStep 0 0 rows rows₁`. -/
  stepPf : Expr
  /-- Number of empty columns removed on the left. -/
  t : Nat
  /-- Number of empty rows removed above. -/
  pre : Nat
  /-- The trimmed rows. -/
  trimmedE : Expr
  /-- Proof of `Padded t pre trimmed rows₁`. -/
  padPf : Expr

/-- Simulates `n` generations from the window `(x, y, rows)` and builds a proof of
`Evolves n x y ts x' y' ts'` for the tagged rows. Returns the final window, the expressions of
the initial and final tagged rows, and the proof. -/
meta def mkEvolves (n : Nat) (x y : Int) (rows : List Nat) :
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
  let mut pf := mkApp3 (mkConst ``Evolves.done) xE yE curE
  let mut k := 0
  for s in stages.reverse do
    let inner := mkAppN (mkConst ``Evolves.trim)
      #[natE k, intE (s.x - 1), intE (s.y - 1), s.rows₁E, natE s.t, natE s.pre, s.trimmedE,
        xE, yE, curE, s.padPf, pf]
    pf := mkAppN (mkConst ``Evolves.step)
      #[natE k, intE s.x, intE s.y, s.rowsE, s.rows₁E, xE, yE, curE, s.stepPf, inner]
    k := k + 1
  return (cx, cy, cur, rowsE₀, curE, pf)

/-- Evaluates a closed natural number expression by reduction. -/
meta partial def natOf (e : Expr) : MetaM Nat := do
  let e ← whnfD (← instantiateMVars e)
  if let some n := e.rawNatLit? then return n
  if let some n := e.nat? then return n
  if e.isConstOf ``Nat.zero then return 0
  if e.isAppOfArity ``Nat.succ 1 then return (← natOf e.appArg!) + 1
  throwError "life_cert: expected a closed natural number, got{indentExpr e}"

/-- Evaluates a closed integer expression by reduction. -/
meta def intOf (e : Expr) : MetaM Int := do
  let e ← instantiateMVars e
  if let some z := e.int? then return z
  let e ← whnfD e
  if e.isAppOfArity ``Int.ofNat 1 then return Int.ofNat (← natOf e.appArg!)
  if e.isAppOfArity ``Int.negSucc 1 then return Int.negSucc (← natOf e.appArg!)
  throwError "life_cert: expected a closed integer, got{indentExpr e}"

/-- Evaluates a closed list of natural numbers by reduction. -/
meta partial def natListOf (e : Expr) : MetaM (List Nat) := do
  let e ← whnfD (← instantiateMVars e)
  if e.isAppOfArity ``List.nil 1 then return []
  if e.isAppOfArity ``List.cons 3 then
    return (← natOf (e.getArg! 1)) :: (← natListOf (e.getArg! 2))
  throwError "life_cert: expected a closed list of natural numbers, got{indentExpr e}"

/-- Unfolds definitions until the expression is a window `ofRows x y rows`, and returns its
three arguments. -/
meta partial def asOfRows (e : Expr) : MetaM (Expr × Expr × Expr) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``ofRows 3 then
    return (e.getArg! 0, e.getArg! 1, e.getArg! 2)
  match ← unfoldDefinition? e with
  | some e' => asOfRows e'
  | none => throwError "life_cert: expected a window `ofRows x y rows`, got{indentExpr e}"

/-- **`life_cert`**: prove `conway.evolve n (ofRows x y rows) = ofRows x' y' rows'` or
`conway.evolve n (ofRows x y rows) = ∅` for closed data by an explicit proof term
(`Evolves.sound`) whose leaves are kernel facts on natural number literals. -/
syntax (name := lifeCert) "life_cert" : tactic

/-- The elaborator of `life_cert`. -/
@[tactic lifeCert] meta def evalLifeCert : Tactic := fun _ => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Eq _ lhs rhs := ty | throwError "life_cert: expected an equation"
  unless lhs.isAppOfArity ``Rule.evolve 3 do
    throwError "life_cert: expected `conway.evolve n S` on the left-hand side"
  unless (lhs.getArg! 0).isConstOf ``conway do
    throwError "life_cert: the rule must be `conway`"
  let n ← natOf (lhs.getArg! 1)
  let (xe, ye, rowse) ← asOfRows (lhs.getArg! 2)
  let x ← intOf xe
  let y ← intOf ye
  let rows ← natListOf rowse
  let (x', y', rows', tsE, ts'E, pf) := mkEvolves n x y rows
  let (_, rowsE, tagPf) := mkTagged rows
  let args := #[natE n, intE x, intE y, tsE, rowsE, intE x', intE y']
  if rhs.isAppOfArity ``EmptyCollection.emptyCollection 2 then
    unless rows' == [] do
      throwError "life_cert: the result is not empty; it is the window\n  \
        ofRows ({x'}) ({y'}) {rows'}"
    g.assign (mkAppN (mkConst ``Evolves.sound_empty) (args ++ #[tagPf, pf]))
  else
    let (xe', ye', rowse') ← asOfRows rhs
    let ex ← intOf xe'
    let ey ← intOf ye'
    let erows ← natListOf rowse'
    unless ex == x' && ey == y' && erows == rows' do
      throwError "life_cert: the stated result differs from the computed one, which is the \
        (trimmed) window\n  ofRows ({x'}) ({y'}) {rows'}"
    let (_, rows'E, tagPf') := mkTagged rows'
    g.assign (mkAppN (mkConst ``Evolves.sound) (args ++ #[ts'E, rows'E, tagPf, pf, tagPf']))
  replaceMainGoal []

end LeanTheory.Life.Cert

namespace LeanTheory.Life

/-- **Sanity** (accepted fixture): the glider `.O. / ..O / OOO` moves one cell to the right and
one cell down in four generations. -/
theorem glider_evolve_four : conway.evolve 4 (ofRows 0 0 [2, 4, 7]) = ofRows 1 1 [2, 4, 7] := by
  life_cert

/-- **Sanity** (accepted fixture): the blinker returns to itself after two generations. -/
theorem blinker_evolve_two : conway.evolve 2 (ofRows (-1) 0 [7]) = ofRows (-1) 0 [7] := by
  life_cert

/-- **Sanity** (accepted fixture, empty result): a domino dies in one generation. -/
theorem domino_evolve_one : conway.evolve 1 (ofRows 0 0 [3]) = ∅ := by
  life_cert

/-- **Sanity** (rejected fixture): a false displacement of the glider is refused. -/
example : True := by
  fail_if_success
    have : conway.evolve 4 (ofRows 0 0 [2, 4, 7]) = ofRows 1 0 [2, 4, 7] := by life_cert
  trivial

end LeanTheory.Life
