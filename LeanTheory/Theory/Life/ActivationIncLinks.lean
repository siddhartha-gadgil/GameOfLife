/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationInc

/-!
# The links of an `inc` activation: lines, times and the remaining separation

Continuation of `ActivationInc` (research note `N-22`, layer 3):

* `downCorners_lines`, `mergeCorners_lines`: the merge link (and every down-going link) meets
  each corner on the input line of its reflector, for every program;
* `RouteTimed`, `upCorners_timed`, `downCorners_timed`: **the route law** — every leg of a link
  takes `2 |Δ| - 5` generations, so the corners are met in order as soon as the legs are at least
  `40` long; stated with the closed formula of the first meeting time;
* `RouteSep`, `routeOK_of`: `RouteOK` splits into the world-line part (`RouteLines`), the time part
  (`RouteTimed`) and the pure separation part (`RouteSep`), which is what remains to be proved for
  the links of the layout.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Lines of the down-going links -/

/-- **The lines of a down-going link** (`downCorners`: merge, `C`, `KNZ`): a glider flying `SE`
on the source column `c` meets every corner on its input line, provided the hairpin `H` and the
channel `cd` have the parity of `c` and the port corner `(cd, vp)` has odd `u + v`; it leaves
flying `NE` on the port line through the port corner. -/
theorem downCorners_lines (p : Program) (b s c H cd vp : ℤ) (r : ℕ) (idx : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0)
    (hd : (cd - c) % 2 = 0) (hv : (cd + vp) % 2 = 1) :
    RouteLines g (downCorners p b s c H cd vp r idx) ∧
      (route g (downCorners p b s c H cd vp r idx)).2.dx = 1 ∧
      (route g (downCorners p b s c H cd vp r idx)).2.dy = -1 ∧
      (route g (downCorners p b s c H cd vp r idx)).2.Through cd vp := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  set vO := trackOut p b s c
  set vB := trackBack p b s c
  simp only [downCorners, bandCorners, List.cons_append, List.nil_append, route, RouteLines]
  have p1 : (c - rfCU 3 + vO - rfCV 3) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l1 : OnLine g ⟨3, c, vO, .band b s false⟩ :=
    onLine_of_through (by simp [hdx, rfIn]) (by simp [hdy, rfIn]) p1
      (by simp only [WL.Through, hdx, hdy, hl]; ring)
  obtain ⟨t1, x1, y1⟩ := reflect_through g ⟨3, c, vO, .band b s false⟩ p1
  set g1 := (reflect g ⟨3, c, vO, .band b s false⟩).2
  simp only [rfOut] at x1 y1
  have p2 : (H - rfCU 7 + vO - rfCV 7) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l2 : OnLine g1 ⟨7, H, vO, .band b s true⟩ :=
    onLine_of_through (by simp [x1, rfIn]) (by simp [y1, rfIn]) p2
      (by simp only [WL.Through, x1, y1] at t1 ⊢; linarith)
  obtain ⟨t2, x2, y2⟩ := reflect_through g1 ⟨7, H, vO, .band b s true⟩ p2
  set g2 := (reflect g1 ⟨7, H, vO, .band b s true⟩).2
  simp only [rfOut] at x2 y2
  have p3 : (H - rfCU 4 + vB - rfCV 4) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l3 : OnLine g2 ⟨4, H, vB, .band b (9 - s) true⟩ :=
    onLine_of_through (by simp [x2, rfIn]) (by simp [y2, rfIn]) p3
      (by simp only [WL.Through, x2, y2] at t2 ⊢; linarith)
  obtain ⟨t3, x3, y3⟩ := reflect_through g2 ⟨4, H, vB, .band b (9 - s) true⟩ p3
  set g3 := (reflect g2 ⟨4, H, vB, .band b (9 - s) true⟩).2
  simp only [rfOut] at x3 y3
  have p4 : (cd - rfCU 2 + vB - rfCV 2) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l4 : OnLine g3 ⟨2, cd, vB, .band b (9 - s) false⟩ :=
    onLine_of_through (by simp [x3, rfIn]) (by simp [y3, rfIn]) p4
      (by simp only [WL.Through, x3, y3] at t3 ⊢; linarith)
  obtain ⟨t4, x4, y4⟩ := reflect_through g3 ⟨2, cd, vB, .band b (9 - s) false⟩ p4
  set g4 := (reflect g3 ⟨2, cd, vB, .band b (9 - s) false⟩).2
  simp only [rfOut] at x4 y4
  have p5 : (cd - rfCU 4 + vp - rfCV 4) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l5 : OnLine g4 ⟨4, cd, vp, .left r idx⟩ :=
    onLine_of_through (by simp [x4, rfIn]) (by simp [y4, rfIn]) p5
      (by simp only [WL.Through, x4, y4] at t4 ⊢; linarith)
  obtain ⟨t5, x5, y5⟩ := reflect_through g4 ⟨4, cd, vp, .left r idx⟩ p5
  simp only [rfOut] at x5 y5
  exact ⟨⟨l1, l2, l3, l4, l5, trivial⟩, x5, y5, t5⟩

/-- **The lines of the merge link of register `r`**: a glider flying `SE` on the output column of
merge unit `N + r` meets every corner of `mergeCorners p r e` on its input line, for every `e`,
and leaves flying `NE` on the INC port line of module `r`. -/
theorem mergeCorners_lines (p : Program) (r : ℕ) (e : ℤ) {g : WL} (hdx : g.dx = 1)
    (hdy : g.dy = 1) (hl : g.lane = A p (p.length + r) + haltD) :
    RouteLines g (mergeCorners p r e) ∧ (route g (mergeCorners p r e)).2.dx = 1 ∧
      (route g (mergeCorners p r e)).2.dy = -1 ∧
      (route g (mergeCorners p r e)).2.Through (U p r + incChan p) incPortV := by
  have hA := A_even p (p.length + r)
  have hU := U_even p r
  have hc : (incChan p) % 2 = 0 := by
    have := fixp_parity (uL - 62 * (2 * D p)) (1 - incPortV % 2)
    unfold incChan leftChan
    simp only [incPortV] at this ⊢
    omega
  refine downCorners_lines p _ 0 _ _ _ _ r _ hdx hdy hl (hairReg_par _ _ _ _) ?_ ?_
  · simp only [haltD]; omega
  · simp only [incPortV]; omega

/-! ### Times: the route law -/

/-- The corners of a route are met in order, from time `T` on: each meeting time is at least the
end of the previous reflection. -/
def RouteTimed : WL → List Corner → ℤ → Prop
  | _, [], _ => True
  | g, c :: cs, T => T ≤ meetT g c ∧ RouteTimed (reflect g c).2 cs (meetT g c + 30)

/-- **The route law for an up-going link**: from the `SE` glider `g` on the column `c`, the first
corner is met at `g.tau + 2 (c + OUT) - 10`, and every later leg of length `Δ` (in `u` or `v`)
takes about `2 Δ` generations; so the corners are met in order when every leg is at least `40`
long. -/
theorem upCorners_timed (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) {g : WL} (hdx : g.dx = 1)
    (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0) (hd : (destU p a t - c) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) (T : ℤ)
    (h0 : T ≤ g.tau + 2 * (c + trackOut p b s c) - 10) (hcH : H + 40 ≤ c)
    (hdH : H + 40 ≤ destU p a t) (hOB : trackOut p b s c + 40 ≤ trackBack p b s c)
    (hDB : destV p t + 40 ≤ trackBack p b s c) :
    RouteTimed g (upCorners p b s c H a t) T := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl h0
  subst hdx hdy hl
  simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append, RouteTimed,
    reflect, meetT, delayS, WL.shift, rfIn, rfOut, rfX, rfCU, rfCV]
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

/-- **The route law for a down-going link** (`downCorners`), as `upCorners_timed`. -/
theorem downCorners_timed (p : Program) (b s c H cd vp : ℤ) (r : ℕ) (idx : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0)
    (hd : (cd - c) % 2 = 0) (hv : (cd + vp) % 2 = 1) (T : ℤ)
    (h0 : T ≤ g.tau + 2 * (c + trackOut p b s c) - 10) (hcH : H + 40 ≤ c) (hdH : H + 40 ≤ cd)
    (hOB : trackOut p b s c + 40 ≤ trackBack p b s c) (hDB : trackBack p b s c + 40 ≤ vp) :
    RouteTimed g (downCorners p b s c H cd vp r idx) T := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl h0
  subst hdx hdy hl
  simp only [downCorners, bandCorners, List.cons_append, List.nil_append, RouteTimed,
    reflect, meetT, delayS, WL.shift, rfIn, rfOut, rfX, rfCU, rfCV]
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

/-- **The times of a link from a unit output to an entry copy** (continue `w = 68`, INC link
`w = 157`): the output glider of unit `i` at template time `2010 + d` (the end of the body, the
activation delayed by `d`) meets every corner of the link in order, for every hairpin left of
`HI + 90` of the parity of the column, every sub-band `b ≥ 0`, slot `s ≤ 4` and entry copy chosen
by `copyIdx` with a predecessor number `0 ≤ e' < P`. -/
theorem unitLink_timed (p : Program) (i a : ℕ) (w τ b s H e' d : ℤ)
    (hw : (w = 68 ∧ τ = 605) ∨ (w = 157 ∧ τ = 1029)) (hb : 0 ≤ b) (hs : 0 ≤ s ∧ s ≤ 4)
    (hH : (H - (A p i + w)) % 2 = 0) (hHI : H ≤ HI p + 90) (he : 0 ≤ e' ∧ e' < P p) :
    RouteTimed ((unitWL p i ⟨1, 1, w, τ⟩).shift 0 0 d)
      (upCorners p b s (A p i + w) H a (copyIdx (unitC0 p a) e' (A p i + w))) (2010 + d) := by
  have hu := unitD_uv p i
  have ha := A_even p a
  have hai := A_even p i
  have hv := VU_even p
  have hc := copyBeta_spec (unitC0 p a) e' (A p i + w)
  have hr := copyIdx_range p (C0 := unitC0 p a) (c := A p i + w) he
  have hC0 : unitC0 p a % 2 = 1 ∧ -237 ≤ unitC0 p a := by
    obtain h | h | h := unitC0_cases p a <;> rw [h] <;> exact ⟨rfl, by norm_num⟩
  have hA0 := A_nonneg p (a := a) (by omega)
  have hAi := A_nonneg p (a := i) (by omega)
  have hHI' : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hVT := VT_mod p
  refine upCorners_timed p b s (A p i + w) H a _ (g := (unitWL p i ⟨1, 1, w, τ⟩).shift 0 0 d)
    rfl rfl ?_ hH ?_ ?_ (2010 + d) ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift]; omega
  · simp only [destU, inCol] at hc ⊢; omega
  · simp only [destU, destV, inCol, sideV]; omega
  · simp only [unitWL, WL.shift, trackOut, track, VU] at hu ⊢
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · omega
  · simp only [destU, inCol]; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [destV, sideV, trackBack, track, VU]; omega

/-! ### What remains of `RouteOK`: separation -/

/-- **The separation part of `RouteOK`**: before each corner the flight boxes lie in `Z` and are
far from every piece of `L`; the reflector of each corner is a piece of `L` whose relay box lies in
`Z` and is far from every other piece; the final glider box lies in `Z`. -/
def RouteSep (L : List Piece) (Z : Set Cell) : WL → List Corner → ℕ → Prop
  | g, [], T => g.box T ⊆ Z
  | g, c :: cs, T =>
      (∀ i : ℕ, (T : ℤ) + i ≤ meetT g c → g.box (T + i) ⊆ Z) ∧
      (∀ i : ℕ, (T : ℤ) + i < meetT g c → ∀ h ∈ L, FarApart 2 (g.box (T + i)) h.box) ∧
      relayBox c ⊆ Z ∧
      (∃ L' : List Piece, L.Perm ((reflect g c).1.piece :: L') ∧
        ∀ h ∈ L', FarApart 2 (relayBox c) h.box) ∧
      RouteSep L Z (reflect g c).2 cs ((meetT g c).toNat + 30)

/-- The outgoing world line of a corner met on its input line is diagonal. -/
theorem reflect_dir (g : WL) (c : Corner) : (reflect g c).2.Dir := by
  simp only [reflect]
  exact WL.Dir.shift (rfOut_dir _) _ _ _

/-- **`RouteOK` from its three parts**: world lines, times, separation. -/
theorem routeOK_of {L : List Piece} {Z : Set Cell} :
    ∀ (cs : List Corner) (g : WL) (T : ℕ), g.Dir → RouteLines g cs → RouteTimed g cs T →
      RouteSep L Z g cs T → RouteOK L Z g cs T
  | [], _, _, hd, _, _, hs => ⟨hd, hs⟩
  | c :: cs, g, T, hd, ⟨hl, hls⟩, ⟨ht, hts⟩, ⟨s1, s2, s3, s4, s5⟩ => by
    refine ⟨hd, hl, ht, s1, s2, s3, s4, routeOK_of cs _ _ (reflect_dir g c) hls ?_ s5⟩
    have h0 : (0 : ℤ) ≤ meetT g c := le_trans (Int.natCast_nonneg T) ht
    rw [show (((meetT g c).toNat + 30 : ℕ) : ℤ) = meetT g c + 30 by
      push_cast; rw [Int.toNat_of_nonneg h0]]
    exact hts

end LP

end LeanTheory.Life
