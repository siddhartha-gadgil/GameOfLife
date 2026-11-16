/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.BoxCert
public import LeanTheory.Theory.Life.Guns
public import LeanTheory.Theory.Life.LayoutPieces
public meta import LeanTheory.Certificates.LifeCert
public meta import LeanTheory.Theory.Life.BoxCert

/-!
# Evolution certificates with a box and holes

Research note `N-22`. `life_reaction` (`BoxCert`) certifies that every generation of an
evolution lies in a box. A station of a module and the gliders it captures run inside a box that
also contains corners of the boxes of the neighbouring stations; the run itself stays clear of
them. This module certifies such tighter footprints: a box with holes.

* `tightSet a b lo hi H`: the cells of `Box a b lo hi` outside the boxes of the list `H`;
* `rowFree r l h`: no bit of the row `r` in the columns `l … h` (`rowFree_testBit`);
* `holeRows x B rows y`: no cell of the window `ofRows x y rows` in the box `B`
  (`holeRows_not_mem`);
* `tightChk`: the box check of `boxCheck` and the hole checks, `tightChk_sound`;
* `EvolvesP chk n x y rows`: the certificate predicate of `Evolves` (`Certificates/LifeSim`)
  without the result, with one kernel fact `chk x y rows = true` per generation;
* `TightRun S n F`: every generation `k ≤ n` of `S` lies in `F`; `EvolvesP.tightRun`;
* the tactic **`dsepI_tight`** proves `TightRun (ofRows x y rows) n (tightSet a b lo hi H)` for
  closed data, by an explicit proof term whose leaves are kernel facts.

**Sanity.** `dsepI_tight_fixture` (accepted: the glider for four generations in a box with a hole
it avoids), and a rejected fixture (the hole on the glider's path is refused).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-! ### Boxes with holes -/

/-- **A box with holes**: the cells of `Box a b lo hi` outside the boxes of `H`. -/
def tightSet (a b lo hi : ℤ) (H : List LP.BoxT) : Set Cell :=
  {c | c ∈ Box a b lo hi ∧ ∀ B ∈ H, c ∉ Box B.a B.b B.lo B.hi}

/-- No bit of the row `r` in the columns `l … h`. -/
def rowFree (r : ℕ) (l h : ℤ) : Bool :=
  decide (h < 0) || (r >>> l.toNat) % 2 ^ (h + 1 - (l.toNat : ℤ)).toNat == 0

/-- **Soundness of `rowFree`.** -/
theorem rowFree_testBit {r : ℕ} {l h : ℤ} (hf : rowFree r l h = true) {j : ℕ} (h1 : l ≤ j)
    (h2 : (j : ℤ) ≤ h) : r.testBit j = false := by
  simp only [rowFree, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
  rcases hf with hf | hf
  · omega
  · have hl : l.toNat ≤ j := by omega
    have hw : j - l.toNat < (h + 1 - (l.toNat : ℤ)).toNat := by omega
    have e : (r >>> l.toNat).testBit (j - l.toNat) = r.testBit j := by
      rw [Nat.testBit_shiftRight, Nat.add_sub_cancel' hl]
    have := Nat.testBit_mod_two_pow (r >>> l.toNat) (h + 1 - (l.toNat : ℤ)).toNat (j - l.toNat)
    rw [hf, Nat.zero_testBit, e] at this
    simp only [hw, decide_true, Bool.true_and] at this
    exact this.symm

/-- No cell of the window `ofRows x y rows` in the box `B` (rows from row `y` on). -/
def holeRows (x : ℤ) (B : LP.BoxT) : List ℕ → ℤ → Bool
  | [], _ => true
  | r :: rs, y => (decide (y < B.lo) || decide (B.hi < y) || rowFree r (B.a - x) (B.b - x)) &&
      holeRows x B rs (y + 1)

/-- The checker gives every row. -/
theorem holeRows_get {x : ℤ} {B : LP.BoxT} : ∀ (rows : List ℕ) (y : ℤ), holeRows x B rows y = true →
    ∀ i < rows.length, y + i < B.lo ∨ B.hi < y + i ∨ rowFree (rows.getD i 0) (B.a - x) (B.b - x)
  | [], _, _, i, hi => absurd hi (by simp)
  | r :: rs, y, h, i, hi => by
    simp only [holeRows, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases i with _ | i
    · simp only [Nat.cast_zero, add_zero, List.getD_cons_zero]
      rcases h1 with (h1 | h1) | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · have := holeRows_get rs (y + 1) h2 i (by simpa using hi)
      simp only [List.getD_cons_succ]
      push_cast
      rcases this with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr h)

/-- **Soundness of `holeRows`.** -/
theorem holeRows_not_mem {x y : ℤ} {rows : List ℕ} {B : LP.BoxT} (h : holeRows x B rows y = true)
    {c : Cell} (hc : c ∈ ofRows x y rows) : c ∉ Box B.a B.b B.lo B.hi := by
  have hx := (le_of_mem_ofRows hc).1
  have hy := (le_of_mem_ofRows hc).2
  have hlen := snd_lt_of_mem_ofRows hc
  rw [mem_ofRows, bitAt] at hc
  obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c.2 - y by omega)
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ c.1 - x by omega)
  rw [hi, hj, rowZ_natCast, tb_natCast] at hc
  rintro ⟨b1, b2, b3, b4⟩
  rcases holeRows_get rows y h i (by omega) with h' | h' | h'
  · omega
  · omega
  · rw [rowFree_testBit h' (by omega) (by omega)] at hc
    exact Bool.false_ne_true hc

/-- The check of one generation: the window in the box and outside every hole. -/
def tightChk (a b lo hi : ℤ) (H : List LP.BoxT) (x y : ℤ) (rows : List ℕ) : Bool :=
  boxCheck x y rows a b lo hi && H.all fun B => holeRows x B rows y

/-- **Soundness of `tightChk`.** -/
theorem tightChk_sound {a b lo hi : ℤ} {H : List LP.BoxT} {x y : ℤ} {rows : List ℕ}
    (h : tightChk a b lo hi H x y rows = true) :
    (ofRows x y rows : Set Cell) ⊆ tightSet a b lo hi H := by
  simp only [tightChk, Bool.and_eq_true, List.all_eq_true] at h
  intro c hc
  exact ⟨coe_ofRows_subset_box h.1 hc, fun B hB => holeRows_not_mem (h.2 B hB) (mem_coe.1 hc)⟩

/-! ### Certificates without the result -/

/-- **Evolution certificate with a check**: as `Evolves`, without the result, and the window of
every generation passes `chk`. Rows are tagged literals. -/
inductive EvolvesP (chk : ℤ → ℤ → List ℕ → Bool) : ℕ → ℤ → ℤ → List ℕ → Prop where
  /-- No generation: the window passes the check. -/
  | done (x y : ℤ) (rows : List ℕ) (hb : chk x y (rows.map untag) = true) : EvolvesP chk 0 x y rows
  /-- One generation, certified row by row, from a window that passes the check. -/
  | step (n : ℕ) (x y : ℤ) (rows rows₁ : List ℕ) (hb : chk x y (rows.map untag) = true)
      (h : RowsStep 0 0 rows rows₁) (e : EvolvesP chk n (x - 1) (y - 1) rows₁) :
      EvolvesP chk (n + 1) x y rows
  /-- Replace a window by its trimmed form. -/
  | trim (n : ℕ) (x y : ℤ) (full : List ℕ) (t pre : ℕ) (rows : List ℕ)
      (h : Padded t pre rows full) (e : EvolvesP chk n (x + t) (y + pre) rows) :
      EvolvesP chk n x y full

/-- Every generation of a certified evolution lies in a set containing every window that passes
the check. -/
theorem EvolvesP.subset {chk : ℤ → ℤ → List ℕ → Bool} {F : Set Cell}
    (hF : ∀ x y rows, chk x y rows = true → (ofRows x y rows : Set Cell) ⊆ F) {n : ℕ} {x y : ℤ}
    {rows : List ℕ} (h : EvolvesP chk n x y rows) :
    ∀ i ≤ n, (conway.evolve i (ofRows x y (rows.map untag)) : Set Cell) ⊆ F := by
  induction h with
  | done x y rows hb =>
    intro i hi
    obtain rfl : i = 0 := by omega
    exact hF _ _ _ hb
  | step n x y rows rows₁ hb h e ih =>
    intro i hi
    cases i with
    | zero => exact hF _ _ _ hb
    | succ j =>
      have h1 := h.eq
      rw [untag_zero] at h1
      rw [Rule.evolve_succ', step_ofRows, stepRows, h1]
      exact ih j (by omega)
  | trim n x y full t pre rows h e ih =>
    intro i hi
    rw [h.ofRows_eq]
    exact ih i hi

/-- **Every generation `k ≤ n` of `S` lies in `F`.** -/
def TightRun (S : Finset Cell) (n : ℕ) (F : Set Cell) : Prop :=
  ∀ k ≤ n, (conway.evolve k S : Set Cell) ⊆ F

/-- **Soundness**: a certificate with the checks of a box with holes. -/
theorem EvolvesP.tightRun {a b lo hi : ℤ} {H : List LP.BoxT} {n : ℕ} {x y : ℤ} {ts rows : List ℕ}
    (h₀ : Tagged ts rows) (h : EvolvesP (tightChk a b lo hi H) n x y ts) :
    TightRun (ofRows x y rows) n (tightSet a b lo hi H) := by
  intro k hk
  rw [← h₀.eq]
  exact h.subset (fun _ _ _ hc => tightChk_sound hc) k hk

/-- A run in `F` is a run in every superset of `F`. -/
theorem TightRun.mono {S : Finset Cell} {n : ℕ} {F G : Set Cell} (h : TightRun S n F)
    (hFG : F ⊆ G) : TightRun S n G :=
  fun k hk => (h k hk).trans hFG

/-- A translated run. -/
theorem TightRun.translate {S : Finset Cell} {n : ℕ} {F : Set Cell} (h : TightRun S n F)
    (v : Cell) : TightRun (translate v S) n ((fun c => v + c) '' F) := by
  intro k hk c hc
  rw [Rule.evolve_translate, mem_coe, mem_translate] at hc
  exact ⟨c - v, h k hk (mem_coe.2 hc), by simp⟩

namespace Cert

open Lean Meta Elab Tactic

/-- `meta` copy of `rowFree`. -/
meta def rowFreeM (r : Nat) (l h : Int) : Bool :=
  decide (h < 0) || (r >>> l.toNat) % 2 ^ (h + 1 - (l.toNat : Int)).toNat == 0

/-- `meta` copy of `holeRows`. -/
meta def holeRowsM (x : Int) (B : Int × Int × Int × Int) : List Nat → Int → Bool
  | [], _ => true
  | r :: rs, y => (decide (y < B.2.2.1) || decide (B.2.2.2 < y) ||
      rowFreeM r (B.1 - x) (B.2.1 - x)) && holeRowsM x B rs (y + 1)

/-- `meta` copy of `tightChk`. -/
meta def tightChkM (a b lo hi : Int) (H : List (Int × Int × Int × Int)) (x y : Int)
    (rows : List Nat) : Bool :=
  boxCheckM x y rows a b lo hi && H.all fun B => holeRowsM x B rows y

/-- Simulates `n` generations from the window `(x, y, rows)` and builds a proof of
`EvolvesP chk n x y ts` for the check expression `chkE`. Fails if a generation fails the check.
Returns the expression of the initial tagged rows and the proof. -/
meta def mkEvolvesP (chkE : Expr) (chk : Int → Int → List Nat → Bool) (n : Nat) (x y : Int)
    (rows : List Nat) : Except String (Expr × Expr) := do
  let rowsE₀ := listE rows
  let mut stages : Array Stage := #[]
  let mut cx := x
  let mut cy := y
  let mut cur := rows
  let mut curE := rowsE₀
  for i in [0:n] do
    unless chk cx cy cur do
      throw s!"at generation {i} the pattern fails the check: its window is \
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
  unless chk cx cy cur do
    throw s!"at generation {n} the pattern fails the check: its window is \
      ofRows ({cx}) ({cy}) with {cur.length} rows"
  let mut pf := mkAppN (mkConst ``EvolvesP.done) #[chkE, intE cx, intE cy, curE, boxLeaf]
  let mut k := 0
  for s in stages.reverse do
    let inner := mkAppN (mkConst ``EvolvesP.trim)
      #[chkE, natE k, intE (s.x - 1), intE (s.y - 1), s.rows₁E, natE s.t, natE s.pre,
        s.trimmedE, s.padPf, pf]
    pf := mkAppN (mkConst ``EvolvesP.step)
      #[chkE, natE k, intE s.x, intE s.y, s.rowsE, s.rows₁E, boxLeaf, s.stepPf, inner]
    k := k + 1
  return (rowsE₀, pf)

/-- Evaluates a closed list of boxes `[⟨a, b, lo, hi⟩, …]` by reduction. -/
meta partial def boxListOf (e : Expr) : MetaM (List (Int × Int × Int × Int)) := do
  let e ← whnfD (← instantiateMVars e)
  if e.isAppOfArity ``List.nil 1 then return []
  if e.isAppOfArity ``List.cons 3 then
    let B ← whnfD (e.getArg! 1)
    unless B.isAppOfArity ``LP.BoxT.mk 4 do
      throwError "dsepI_tight: expected a box `⟨a, b, lo, hi⟩`, got{indentExpr B}"
    let a ← intOf (B.getArg! 0)
    let b ← intOf (B.getArg! 1)
    let lo ← intOf (B.getArg! 2)
    let hi ← intOf (B.getArg! 3)
    return (a, b, lo, hi) :: (← boxListOf (e.getArg! 2))
  throwError "dsepI_tight: expected a closed list of boxes, got{indentExpr e}"

/-- **`dsepI_tight`**: prove `TightRun S n (tightSet a b lo hi H)` for closed data, where `S` is
(or unfolds to) a window, by an explicit proof term (`EvolvesP.tightRun`) whose leaves are kernel
facts. -/
syntax (name := dsepITight) "dsepI_tight" : tactic

/-- The elaborator of `dsepI_tight`. -/
@[tactic dsepITight] meta def evalDsepITight : Tactic := fun _ => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``TightRun 3 do
    throwError "dsepI_tight: expected a goal `TightRun S n (tightSet a b lo hi H)`"
  let n ← natOf (ty.getArg! 1)
  let F ← instantiateMVars (ty.getArg! 2)
  unless F.isAppOfArity ``tightSet 5 do
    throwError "dsepI_tight: the footprint must be `tightSet a b lo hi H`"
  let aE := F.getArg! 0
  let bE := F.getArg! 1
  let loE := F.getArg! 2
  let hiE := F.getArg! 3
  let HE := F.getArg! 4
  let a ← intOf aE
  let b ← intOf bE
  let lo ← intOf loE
  let hi ← intOf hiE
  let H ← boxListOf HE
  let (xe, ye, rowse) ← asOfRows (ty.getArg! 0)
  let x ← intOf xe
  let y ← intOf ye
  let rows ← natListOf rowse
  let chkE := mkAppN (mkConst ``tightChk) #[aE, bE, loE, hiE, HE]
  match mkEvolvesP chkE (tightChkM a b lo hi H) n x y rows with
  | .error msg => throwError "dsepI_tight: {msg}"
  | .ok (tsE, pf) =>
    let (_, rowsE, tagPf) := mkTagged rows
    g.assign (mkAppN (mkConst ``EvolvesP.tightRun)
      #[aE, bE, loE, hiE, HE, natE n, intE x, intE y, tsE, rowsE, tagPf, pf])
    replaceMainGoal []

end Cert

/-- **Sanity** (accepted fixture): four generations of the glider stay in a box, outside a hole
at its corner. -/
theorem dsepI_tight_fixture :
    TightRun (ofRows 0 0 [2, 4, 7]) 4 (tightSet 0 3 0 3 [⟨3, 3, 0, 0⟩]) := by
  dsepI_tight

/-- **Sanity** (rejected fixture): a hole on the glider's path is refused. -/
example : True := by
  fail_if_success
    have : TightRun (ofRows 0 0 [2, 4, 7]) 4 (tightSet 0 3 0 3 [⟨2, 2, 2, 2⟩]) := by
      dsepI_tight
  trivial

end LeanTheory.Life
