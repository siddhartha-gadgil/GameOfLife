/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncEntry

/-!
# The arrival of a link at its entry copy: the window rule, proved

Research note `N-22`, item (c). The window rule of `R-31` (`solveE`) was a computation; here it
becomes a theorem for the links of the layout:

* `upCorners_tau`: moving the hairpin of an up-going link by `ΔH` changes the arrival time by
  `-4 ΔH` (the route law);
* `hairReg_e`, `hairCont_e`: one hairpin step `e` moves the hairpin by `-2`, so it delays the
  arrival by `8`;
* `upLink_offset`: with `e = solveE …` the link arrives at window offset `ρ* ∈ {4, 5}`;
* `arrival_eq`: the arriving world line **is** the side line of the entry copy delayed by
  `δ + 30 k`, the form required by `entry_reaction`;
* `incLink_offset`: both links of an `inc` instruction (continue and INC link, with the hairpins
  and windows of `incSpecs`) arrive at offset `4` or `5`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- **The route law for the arrival**: the arrival time of an up-going link plus `4 H` does not
depend on the hairpin `H` (of the parity of the source column). -/
theorem upCorners_tau (p : Program) (b s c H H' : ℤ) (a : ℕ) (t : ℤ) {g : WL} (hdx : g.dx = 1)
    (hdy : g.dy = 1) (hH : (H - c) % 2 = 0) (hH' : (H' - c) % 2 = 0)
    (hd : (destU p a t - c) % 2 = 0) :
    (route g (upCorners p b s c H a t)).2.tau + 4 * H =
      (route g (upCorners p b s c H' a t)).2.tau + 4 * H' := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy
  subst hdx hdy
  simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append, route,
    reflect, WL.shift, rfIn, rfOut, rfX, rfCU, rfCV]
  omega

/-- One step `e` of a regular hairpin moves it by `-2`. -/
theorem hairReg_e (p : Program) (s e c : ℤ) : hairReg p s e c = hairReg p s 0 c - 2 * e := by
  unfold hairReg fixp
  omega

/-- One step `e` of a continue hairpin moves it by `-2`. -/
theorem hairCont_e (p : Program) (G e c : ℤ) : hairCont p G e c = hairCont p G 0 c - 2 * e := by
  unfold hairCont fixp
  omega

/-- **The window rule, proved for an up-going link**: if `e` steps of the hairpin delay the
arrival by `8 e` (`hlin`), then with `e = solveE g mk win` the link arrives at offset
`ρ* ∈ {4, 5}` of the window. -/
theorem upLink_offset (g win : WL) (mk : ℤ → List Corner)
    (hlin : ∀ e, (route g (mk e)).2.tau = (route g (mk 0)).2.tau + 8 * e) :
    ((route g (mk (solveE g mk win))).2.tau - win.tau) % 30 = 4 ∨
      ((route g (mk (solveE g mk win))).2.tau - win.tau) % 30 = 5 := by
  rw [hlin]
  have h := window_rule (((route g (mk 0)).2.tau - win.tau) % 30)
    (rhoStar (((route g (mk 0)).2.tau - win.tau) % 30)) (rhoStar_parity _)
  simp only [solveE]
  unfold rhoStar at h ⊢
  omega

/-- The arrival of a link from a unit column (the continue or the INC link) is linear in the
hairpin steps: `8` generations per step, for the hairpins `hairReg` and `hairCont`. -/
theorem unitLink_lin (p : Program) (i a : ℕ) (w τ b s : ℤ) (hair : ℤ → ℤ)
    (hh : ∀ e, hair e = hair 0 - 2 * e) (hpar : (hair 0 - (A p i + w)) % 2 = 0) (t : ℤ)
    (hd : (destU p a t - (A p i + w)) % 2 = 0) (e : ℤ) :
    (route (unitWL p i ⟨1, 1, w, τ⟩) (upCorners p b s (A p i + w) (hair e) a t)).2.tau =
      (route (unitWL p i ⟨1, 1, w, τ⟩) (upCorners p b s (A p i + w) (hair 0) a t)).2.tau +
        8 * e := by
  have := upCorners_tau p b s (A p i + w) (hair e) (hair 0) a t
    (g := unitWL p i ⟨1, 1, w, τ⟩) rfl rfl (by rw [hh]; omega) hpar hd
  rw [hh e] at this ⊢
  omega

/-- **The arriving world line is the side line of the entry copy, delayed by `δ + 30 k`**: a
glider flying `NE` through the input corner of copy `t` of unit `a`, at offset `δ` of the window
`destWin p a t`. -/
theorem arrival_eq (p : Program) (a : ℕ) (t : ℤ) {g : WL} (hdx : g.dx = 1) (hdy : g.dy = -1)
    (ht : g.Through (destU p a t) (destV p t)) :
    g = (destWin p a t).shift 0 0 ((g.tau - (destWin p a t).tau) % 30 +
      30 * ((g.tau - (destWin p a t).tau) / 30)) := by
  have hu := unitD_uv p a
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy
  subst hdx hdy
  simp only [WL.Through, destV, sideV] at ht
  simp only [destWin, unitWL, sideWL, WL.shift, WL.mk.injEq, true_and]
  constructor <;> omega

/-- **Both links of an `inc` instruction arrive at window offset `4` or `5`**: the continue
(`incD`, continue hairpin with any extra delay `G`, to any unit `a`) and the INC link (`incR`,
regular hairpin of slot `1`), each with `e` chosen by `solveE` for the window of its entry copy. -/
theorem incLink_offset (p : Program) (i a : ℕ) (b G e' : ℤ) (w τ s : ℤ) (hair : ℤ → ℤ → ℤ)
    (hw : (w = incD ∧ τ = 605 ∧ s = 0 ∧ hair = hairCont p G) ∨
      (w = incR ∧ τ = 1029 ∧ s = 1 ∧ hair = fun e c => hairReg p 1 e c)) :
    let c := A p i + w
    let t := copyIdx (unitC0 p a) e' c
    let mk := fun e => upCorners p b s c (hair e c) a t
    let g := unitWL p i ⟨1, 1, w, τ⟩
    ((route g (mk (solveE g mk (destWin p a t)))).2.tau - (destWin p a t).tau) % 30 = 4 ∨
      ((route g (mk (solveE g mk (destWin p a t)))).2.tau - (destWin p a t).tau) % 30 = 5 := by
  intro c t mk g
  have ha := A_even p a
  have hc := copyBeta_spec (unitC0 p a) e' c
  have hh : ∀ e, hair e c = hair 0 c - 2 * e := by
    rcases hw with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · exact fun e => hairCont_e p G e c
    · exact fun e => hairReg_e p 1 e c
  have hpar : (hair 0 c - c) % 2 = 0 := by
    rcases hw with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · exact hairCont_par p G 0 c
    · exact hairReg_par p 1 0 c
  refine upLink_offset g (destWin p a t) mk fun e =>
    unitLink_lin p i a w τ b s (fun e => hair e c) hh hpar t ?_ e
  simp only [destU, inCol] at hc ⊢
  omega

end LP

end LeanTheory.Life
