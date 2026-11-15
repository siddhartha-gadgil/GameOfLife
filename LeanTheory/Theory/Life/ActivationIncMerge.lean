/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncArrive

/-!
# The merge unit, the merge link and the INC input of the module

Item (d) of the `inc` activation (research note `N-22`):

* `mergeStart_eq`: the output of the entry chain of the merge unit `N + r` (copy `0`) is the
  glider of the merge route's first world line `unitWL (N + r) haltDWL`, delayed by a multiple of
  `30` when the control left at a time `≡ 0 (mod 30)` (so `route_delay` gives the reflectors of
  `mergeSpecs`);
* `downCorners_tau`, `mergeLink_lin`, `mergeLink_offset`: the merge link arrives at offset `4` or
  `5` of the window `incWin` of the module (the window rule with `mergeE`);
* `mergeLink_timed`: its corners are met in order (route law), for every program;
* `incWin_eq`, `module_side_arrival`: the window of the INC OR gate of the module is the side line
  of the OR gate placed at `(-1132, -1291)` with delay `14`; the arriving glider is its side input;
* `incGate_reaction`: the INC OR gate (phase `16` in `moduleSpecs`) releases its output in `134`
  generations; `incGate_out`: the output is the glider of `rfJ_in` (the input line of `RF_J`)
  delayed by `1140 + 30 k`;
* `rfJCorner`, `rfJ_reflect`: `RF_J` is the reflector `reflect g rfJCorner` of a corner, with the
  piece of `moduleSpecs` (image `4`, phase `25`) and the outgoing line `incInWL` (placed and
  delayed): `reflect_reaction`, `window_reflect` and `RouteOK` apply to it like to a route corner;
  `rfJ_onLine`, `rfJ_meet`: the gate output meets it on its input line at time `1085 + 30 k`, and
  the input of `dz2eAny_module` is reached at time `1140 + 30 k ≡ 0 (mod 30)`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The merge unit -/

/-- **The output of the merge unit's entry chain is the merge route's glider**: copy `0`'s output
of unit `a` at time `T` lies on `unitWL a haltDWL` delayed by `T + 166 - 1080`. -/
theorem mergeStart_eq (p : Program) (a : ℕ) (T : ℤ) :
    translate (unitDX p a + 35, unitDY p a + 64) orIn =
      ((unitWL p a haltDWL).shift 0 0 (T + 166 - 1080)).cells T := by
  have hd : haltDWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  rw [WL.shift_cells (show WL.Dir (unitWL p a haltDWL) from hd), unitWL,
    WL.shift_cells hd, translate_translate,
    show T - (T + 166 - 1080) - 0 = (-166 : ℤ) + 1080 by ring]
  have e : haltDWL.cells ((-166 : ℤ) + 1080) = translate (35, 64) orIn := by
    rw [orIn, translate_ofRows]
    rfl
  rw [e, translate_translate]
  congr 1
  ext <;> simp

/-! ### The merge link -/

/-- **The route law for the arrival of a down-going link**: the arrival time plus `4 H` does not
depend on the hairpin `H` (of the parity of the source column). -/
theorem downCorners_tau (p : Program) (b s c H H' cd vp : ℤ) (r : ℕ) (idx : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hH : (H - c) % 2 = 0) (hH' : (H' - c) % 2 = 0)
    (hd : (cd - c) % 2 = 0) :
    (route g (downCorners p b s c H cd vp r idx)).2.tau + 4 * H =
      (route g (downCorners p b s c H' cd vp r idx)).2.tau + 4 * H' := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy
  subst hdx hdy
  simp only [downCorners, bandCorners, List.cons_append, List.nil_append, route,
    reflect, WL.shift, rfIn, rfOut, rfX, rfCU, rfCV]
  omega

/-- The channel of the INC port has the parity of the merge column. -/
theorem incChan_even (p : Program) : incChan p % 2 = 0 := by
  have := fixp_parity (uL - 62 * (2 * D p)) (1 - incPortV % 2)
  unfold incChan leftChan
  simp only [incPortV] at this ⊢
  omega

/-- The arrival of the merge link is linear in its hairpin steps: `8` generations per step. -/
theorem mergeLink_lin (p : Program) (r : ℕ) {g : WL} (hdx : g.dx = 1) (hdy : g.dy = 1)
    (e : ℤ) :
    (route g (mergeCorners p r e)).2.tau = (route g (mergeCorners p r 0)).2.tau + 8 * e := by
  have hA := A_even p (p.length + r)
  have hU := U_even p r
  have hc := incChan_even p
  have := downCorners_tau p (mergeBand p r) 0 (A p (p.length + r) + haltD)
    (hairReg p 0 e (A p (p.length + r) + haltD)) (hairReg p 0 0 (A p (p.length + r) + haltD))
    (U p r + incChan p) incPortV r (2 * D p) hdx hdy (hairReg_par _ _ _ _) (hairReg_par _ _ _ _)
    (by simp only [haltD]; omega)
  rw [hairReg_e p 0 e] at this
  simp only [mergeCorners]
  rw [hairReg_e p 0 e]
  omega

/-- **The merge link arrives at offset `4` or `5` of the INC window of module `r`** (the window
rule with `mergeE`). -/
theorem mergeLink_offset (p : Program) (r : ℕ) :
    ((route (unitWL p (p.length + r) haltDWL) (mergeCorners p r (mergeE p r))).2.tau -
        (modWL p r incWin).tau) % 30 = 4 ∨
      ((route (unitWL p (p.length + r) haltDWL) (mergeCorners p r (mergeE p r))).2.tau -
        (modWL p r incWin).tau) % 30 = 5 :=
  upLink_offset _ _ _ (mergeLink_lin p r rfl rfl)

/-- **The merge link meets its corners in order** (route law), from the time `T` at which the
glider leaves the merge unit's chain (`T ≤ tau + 914`), for every hairpin step `0 ≤ e`. -/
theorem mergeLink_timed (p : Program) {r : ℕ} (hr : (r : ℤ) < R p) (e : ℤ) (he : 0 ≤ e)
    (D' T : ℤ) (hT : T ≤ D' + 914) :
    RouteTimed ((unitWL p (p.length + r) haltDWL).shift 0 0 D') (mergeCorners p r e) T := by
  have hu := unitD_uv p (p.length + r)
  have hA := A_even p (p.length + r)
  have hA0 := A_nonneg p (a := ((p.length + r : ℕ) : ℤ)) (by omega)
  push_cast at hu hA hA0
  have hU := U_even p r
  have hUg := U_ge p (r := r) (by omega)
  have hc := incChan_even p
  have hcb := fixp_bounds (uL - 62 * (2 * D p)) (1 - incPortV % 2)
  have hHI : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hP := one_le_P p
  have hD := one_le_D p
  have h3 := (sep03_band_modules p).1
  have hH := hairReg_le p (s := 0) (e := e) (c := A p (p.length + r) + haltD) (by norm_num) he
  have hVT := VT_mod p
  have hmb : 1 ≤ mergeBand p r := by unfold mergeBand N; omega
  simp only [mergeCorners]
  refine downCorners_timed p _ 0 _ _ _ _ r _ (g := (unitWL p (p.length + r) haltDWL).shift 0 0 D')
    rfl rfl ?_ (hairReg_par _ _ _ _) ?_ ?_ T ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift, haltDWL, haltD]; omega
  · simp only [haltD]; omega
  · simp only [incPortV]; omega
  · simp only [unitWL, WL.shift, trackOut, track, VU, haltDWL, haltD] at hu ⊢; omega
  · simp only [haltD] at hH ⊢; omega
  · simp only [incChan, leftChan, uL, modLeft, slabR] at hcb hUg ⊢
    have := le_max_left (238 : ℤ) (86 + 58 * P p)
    simp only [haltD] at hH ⊢; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, incPortV, mergeBand, NB, modTop, N, R] at h3 hr ⊢; omega

/-! ### The INC OR gate of the module -/

/-- **The INC window of a module is the side line of its OR gate**: the gate at
`(-1132, -1291)` (module frame), delay `14` (phase `16`). -/
theorem incWin_eq (p : Program) (r : ℕ) :
    modWL p r incWin = (sideBase.shift (-1132) (-1291) 14).shift (modDX p r) (modDY p r) 0 := by
  simp only [modWL, incWin, sideBase, WL.shift, WL.mk.injEq, true_and]
  constructor <;> ring

/-- **The arriving glider is the side input of the INC OR gate**: on the INC window of module `r`
at offset `δ ∈ {4, 5}` (and `k` periods), at time `194 + 30 k`. -/
theorem module_side_arrival (p : Program) (r : ℕ) (δ k : ℤ) (hδ : δ = 4 ∨ δ = 5) :
    ((modWL p r incWin).shift 0 0 (δ + 30 * k)).cells (194 + 30 * k) =
      translate (modDX p r - 1132, modDY p r - 1291) (sideIn δ) := by
  have hd : sideBase.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  rw [incWin_eq, WL.shift_cells (show WL.Dir ((sideBase.shift (-1132) (-1291) 14).shift
      (modDX p r) (modDY p r) 0) from hd),
    WL.shift_cells (show WL.Dir (sideBase.shift (-1132) (-1291) 14) from hd),
    WL.shift_cells hd, sideIn_cells hδ, translate_translate, translate_translate]
  congr 1
  · ext <;> simp <;> ring
  · congr 1
    ring

/-- The INC OR gate of module `r` as placed in `moduleSpecs`. -/
def incGateSpec (p : Program) (r : ℕ) : PSpec := ⟨.orGate, modDX p r - 1132, modDY p r - 1291, 16⟩

/-- **The INC OR gate relays the side input** (`orGate_side6/7` placed): at a time `T ≡ 14
(mod 30)` the gate is at phase `0`; `134` generations later it is back in its cycle and its output
is the through output moved by `(35, 64)`. -/
theorem incGate_reaction (p : Program) (r : ℕ) {δ : ℤ} (hδ : δ = 4 ∨ δ = 5) (T : ℕ)
    (hT : T % 30 = 14) :
    Reaction (conway.evolve (T % 30) (incGateSpec p r).piece.rest ∪
        translate (modDX p r - 1132, modDY p r - 1291) (sideIn δ))
      (conway.evolve ((T + 134) % 30) (incGateSpec p r).piece.rest ∪
        translate (modDX p r - 1132 + 35, modDY p r - 1291 + 64) orIn) 134
      (fun _ => (fun c => (modDX p r - 1132, modDY p r - 1291) + c) '' Box 0 90 0 60) := by
  have h : Reaction (orGate ∪ sideIn δ) (phase orGate 134 ∪ translate (35, 64) orIn) 134
      (fun _ => Box 0 90 0 60) := by
    rcases hδ with rfl | rfl
    · exact orGate_side6
    · exact orGate_side7
  have h' := h.translate (modDX p r - 1132, modDY p r - 1291)
  rw [incGateSpec, orGate_placed_at, orGate_placed_at, translate_union, translate_union,
    translate_translate] at *
  rw [phase_congr orGate (a := 16 + T) (b := 0) (by omega),
    phase_congr orGate (a := 16 + (T + 134)) (b := 134) (by omega),
    show phase orGate 0 = orGate by rw [phase, Nat.zero_mod, Rule.evolve_zero]]
  convert h' using 3

/-- **The output of the INC OR gate is on the input line of `RF_J`**: at time `328 + 30 k` it is
the glider of `rfJ_in` (module frame, placed at module `r`) delayed by `1140 + 30 k`. -/
theorem incGate_out (p : Program) (r : ℕ) (k : ℤ) :
    translate (modDX p r - 1132 + 35, modDY p r - 1291 + 64) orIn =
      ((modWL p r ⟨1, 1, 173, 3431⟩).shift 0 0 (1140 + 30 * k)).cells (328 + 30 * k) := by
  have hd : (⟨1, 1, 173, 3431⟩ : WL).Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  rw [WL.shift_cells (show WL.Dir (modWL p r ⟨1, 1, 173, 3431⟩) from hd), modWL,
    WL.shift_cells hd, translate_translate,
    show (328 + 30 * k) - (1140 + 30 * k) - 0 = (-812 : ℤ) by ring]
  have e : (⟨1, 1, 173, 3431⟩ : WL).cells (-812) = translate (-1132 + 35, -1291 + 64) orIn := by
    rw [orIn, translate_ofRows]
    rfl
  rw [e, translate_translate]
  congr 1
  ext <;> simp <;> ring

/-! ### `RF_J` as a corner -/

/-- The corner of `RF_J` in module `r` (image `4`, corner point `(U_r + 173, -1910)`). -/
def rfJCorner (p : Program) (r : ℕ) : Corner := ⟨4, U p r + 173, -1910, .left r (-1)⟩

/-- **`RF_J` is the reflector of its corner**: for the gate output delayed by `d ≡ 0 (mod 30)`,
`reflect` gives exactly the piece of `moduleSpecs` (image `4` at `(-850, -1044)`, phase `25`) and
the outgoing line of `dz2eOp`'s input, placed and delayed by `d`. -/
theorem rfJ_reflect (p : Program) (r : ℕ) (d : ℤ) (hd : d % 30 = 0) :
    reflect ((modWL p r ⟨1, 1, 173, 3431⟩).shift 0 0 d) (rfJCorner p r) =
      (⟨.rf 4, modDX p r - 850, modDY p r - 1044, 25⟩, (modWL p r incInWL).shift 0 0 d) := by
  have hU := U_even p r
  simp only [reflect, rfJCorner, modWL, modDX, modDY, WL.shift, rfIn, rfOut, rfX, rfY, rfCU,
    rfCV, incInWL, Prod.mk.injEq, PSpec.mk.injEq, WL.mk.injEq, true_and]
  refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩

/-- The gate output meets `RF_J` on its input line. -/
theorem rfJ_onLine (p : Program) (r : ℕ) (d : ℤ) :
    OnLine ((modWL p r ⟨1, 1, 173, 3431⟩).shift 0 0 d) (rfJCorner p r) := by
  have hU := U_even p r
  refine onLine_of_through rfl rfl ?_ ?_
  · simp only [rfJCorner, rfCU, rfCV]; omega
  · simp only [WL.Through, rfJCorner, modWL, modDX, modDY, WL.shift]; omega

/-- **The gate output meets `RF_J` at time `1085 + 30 k`** (delay `d = 1140 + 30 k`), `757`
generations after leaving the gate at `328 + 30 k`. -/
theorem rfJ_meet (p : Program) (r : ℕ) (k : ℤ) :
    meetT ((modWL p r ⟨1, 1, 173, 3431⟩).shift 0 0 (1140 + 30 * k)) (rfJCorner p r) =
      1085 + 30 * k := by
  have hU := U_even p r
  simp only [meetT, delayS, rfJCorner, modWL, modDX, modDY, WL.shift, rfIn, rfX, rfCU, rfCV]
  omega

/-- The output of `RF_J` reaches the input of `dz2eOp` (placed at module `r`) at time
`1140 + 30 k`, `25` generations after the end of the reflection. -/
theorem rfJ_to_dz2e (p : Program) (r : ℕ) (k : ℤ) :
    ((modWL p r incInWL).shift 0 0 (1140 + 30 * k)).cells (1140 + 30 * k) =
      translate (modDX p r, modDY p r) (incInWL.cells 0) := by
  have hd : incInWL.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  rw [WL.shift_cells (show WL.Dir (modWL p r incInWL) from hd), modWL, WL.shift_cells hd,
    translate_translate]
  congr 1
  · ext <;> simp
  · congr 1
    ring

end LP

end LeanTheory.Life
