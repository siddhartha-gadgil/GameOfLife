/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncMerge
public import LeanTheory.Theory.Life.Gen.BodyDecRun

/-!
# The links of a `decJz` activation: closed forms, lines, the control and the tokens

Research note `N-22`, layer 3, for an instruction `decJz r z` at `i` (caller number
`j = callerIdx p r i`, `q = D - 1 - j`). The body of unit `i` emits the token `KNZ`, the control
`C` and the token `KZ` (`bodyDec_unit`), on the first world lines of the three routes of `decSpecs`
(`decCornN`, `decCornC`, `decCornZ`, `decSpecs_eq`). This module proves, for every program:

* **closed forms of the routes** (`downCorners_final`, `ztokCorners_final`): the final world line
  of a down-going link and of the Z token link, as an explicit function of the corners;
* **lines** (`decKNZ_lines`, `decC_lines`, `ztokCorners_lines`, `decKZ_lines`): every corner is
  met on the input line of its reflector;
* **the control `C` at the DEC chain** (`decC_offset`, `decC_window`): `C` arrives on the window
  of DEC copy `2 j` at offset `4 + 2 σ` (`σ = 2 (q mod 2)`), i.e. at offset `4` (`q` even, side
  certificate `orSide6`) or `8` (`q` odd, side certificate `orSide10`, `Gen/ActSideDec`);
* **the shift of the module's world lines** (`decShift_eq`, `decShift_mod`): the delay `sh` by which
  the layout times the module's world lines (`cp0WL`, `nzAnsWL`, `zAnsWL`) is
  `2385 + 254 m + (15 + 16 m) mod 30 + 30 k` (`m = 2 D - 1 - 2 j`, slot `k` of `C`), a multiple of
  `30`;
* **the tokens** (`decKNZ_target`, `decKZ_target`): `KNZ` and `KZ` end **exactly** on the token
  world lines of the station certificates (`tokNZWL j`, `tokZWL j`, module frame, timed for
  `cp0WL`), delayed by `sh`: the token of caller `j` reaches station `j` exactly with the answer
  (`R-31` §4.2, `δ_NZ = 0`, `δ_Z = -1` in `R-29`'s numbering, now proved instead of fitted).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The body of a `dec` unit -/

/-- **The body of a `dec` unit on world lines** (`bodyDecRun_rest`): the control at the body input
at time `0` becomes, `3180` generations later, the gliders of the template outputs `L` (`KNZ`),
`R` (`C`) and `D'` (`KZ`), at template time `4260 = 3180 + 1080`. -/
theorem bodyDec_wl :
    conway.evolve 3180 (bodyDecRest ∪ bodyIn) =
      bodyDecRest ∪ decLWL.cells 4260 ∪ decRWL.cells 4260 ∪ decDWL.cells 4260 := by
  have e1 : decLWL.cells 4260 = ofRows 399 554 [1, 6, 3] := rfl
  have e2 : decRWL.cells 4260 = ofRows 760 633 [1, 6, 3] := rfl
  have e3 : decDWL.cells 4260 = ofRows 868 681 [5, 6, 2] := rfl
  rw [bodyIn, bodyDecRun_rest, e1, e2, e3]
  ac_rfl

/-- **The body of a `dec` unit, placed in unit `a`**: the control glider at the entrance becomes
the gliders of `KNZ`, `C` and `KZ` on their layout world lines. -/
theorem bodyDec_unit (p : Program) (a : ℕ) :
    conway.evolve 3180 (translate (unitDX p a, unitDY p a) bodyDecRest ∪ ctrlAt p a) =
      translate (unitDX p a, unitDY p a) bodyDecRest ∪ (unitWL p a decLWL).cells 4260 ∪
        (unitWL p a decRWL).cells 4260 ∪ (unitWL p a decDWL).cells 4260 := by
  have hL : decLWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have hR : decRWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have hD : decDWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  rw [ctrlAt, ← translate_union, Rule.evolve_translate, bodyDec_wl, unitWL_cells p a hL,
    unitWL_cells p a hR, unitWL_cells p a hD, translate_union, translate_union, translate_union]

/-! ### Closed forms of the routes -/

/-- **The final world line of a down-going link** (`KNZ`, `C`, merge): from a `SE` glider on the
column `c`, the link leaves `NE` on the port line `vp`, with reference time `tau + 4 c - 4 H - 25`
(the route law; independent of the channel, the tracks and the port line). -/
theorem downCorners_final (p : Program) (b s c H cd vp : ℤ) (r : ℕ) (idx : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0)
    (hd : (cd - c) % 2 = 0) (hv : (cd + vp) % 2 = 1) :
    (route g (downCorners p b s c H cd vp r idx)).2 = ⟨1, -1, -vp, g.tau + 4 * c - 4 * H - 25⟩ := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl
  subst hdx hdy hl
  simp only [downCorners, bandCorners, List.cons_append, List.nil_append, route, reflect,
    WL.shift, rfIn, rfOut, rfX, rfY, rfCU, rfCV, WL.mk.injEq, true_and]
  constructor <;> omega

/-- **The final world line of the Z token link** (`ztokCorners`): from a `SE` glider on the column
`c`, the link leaves `NW` on the station column `U_r + 1230 + 144 j`, with reference time
`tau + 4 c - 4 H + 4 (U_r + zTokChan j) + 4 zTokDepth j - 30`. -/
theorem ztokCorners_final (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0)
    (hd : (U p r + zTokChan p j - c) % 2 = 0) :
    (route g (ztokCorners p b c H r j)).2 =
      ⟨-1, -1, -(U p r + zTokStation j),
        g.tau + 4 * c - 4 * H + 4 * (U p r + zTokChan p j) + 4 * zTokDepth p j - 30⟩ := by
  have ho := trackOut_par p b 2 c
  have hb := trackBack_par p b 2 c
  have hU := U_even p r
  obtain ⟨-, h2, h3⟩ := zTokChan_parity p 0 r j
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl
  subst hdx hdy hl
  simp only [ztokCorners, bandCorners, List.cons_append, List.nil_append, route, reflect,
    WL.shift, rfIn, rfOut, rfX, rfY, rfCU, rfCV, WL.mk.injEq, true_and, zTokStation] at *
  generalize zTokChan p j = cz at *
  generalize zTokDepth p j = wd at *
  constructor <;> omega

/-! ### The routes of a `decJz` instruction -/

/-- The corners of the token `KNZ` of `decJz r _` at instruction `i` (as in `decSpecs`). -/
def decCornN (p : Program) (i r : ℕ) : List Corner :=
  downCorners p (instrBand i) 0 (A p i + decL)
    (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
    (U p r + nzTokChan p (callerIdx p r i)) (nzTokPortV (callerIdx p r i)) r
    (2 * D p + 1 + 2 * (callerIdx p r i))

/-- The corners of the control `C` (as in `decSpecs`). -/
def decCornC (p : Program) (i r : ℕ) : List Corner :=
  downCorners p (instrBand i) 1 (A p i + decR) (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
    (U p r + decChan p (2 * (callerIdx p r i))) (decPortV p (2 * (callerIdx p r i))) r
    (2 * (callerIdx p r i))

/-- The corners of the token `KZ` (as in `decSpecs`). -/
def decCornZ (p : Program) (i r : ℕ) : List Corner :=
  ztokCorners p (instrBand i) (A p i + decD) (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD)) r
    (callerIdx p r i)

/-- The world line of `C` at the end of its route (on the port line of DEC copy `2 j`). -/
def decGC (p : Program) (i r : ℕ) : WL := (route (unitWL p i decRWL) (decCornC p i r)).2

/-- The slot of `C` in the window of DEC copy `2 j`. -/
def decSlot (p : Program) (i r : ℕ) : ℤ := slot (decGC p i r) (decWin p r (2 * (callerIdx p r i)))

/-- **The shift of the module's world lines** for the activation (`sh` of `decSpecs`): the delay
of the control `C'` of the DEC chain relative to the reference `cp0WL`. -/
def decShift (p : Program) (i r : ℕ) : ℤ :=
  ((cprimeWL p r (2 * (callerIdx p r i))).shift 0 0 (30 * (decSlot p i r - 20))).tau -
    (modWL p r cp0WL).tau

/-- The NZ answer of caller `j` leaving its station, delayed by the shift (`gN` of `decSpecs`). -/
def decGN (p : Program) (i r : ℕ) : WL :=
  (modWL p r (nzAnsWL (callerIdx p r i))).shift 0 0 (decShift p i r)

/-- The Z answer of caller `j` leaving its station, delayed by the shift (`gZ` of `decSpecs`). -/
def decGZ (p : Program) (i r : ℕ) : WL :=
  (modWL p r (zAnsWL (callerIdx p r i))).shift 0 0 (decShift p i r)

/-- The entry copy of the NZ answer at unit `i + 1`. -/
def decTN (p : Program) (i r : ℕ) : ℤ :=
  copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (U p r + nzAnsChan p (callerIdx p r i))

/-- The entry copy of the Z answer at unit `z`. -/
def decTZ (p : Program) (i r z : ℕ) : ℤ :=
  copyIdx (unitC0 p z) (predIdx p z i (if i + 1 = z then 1 else 0))
    (U p r + zAnsChan p (callerIdx p r i))

/-- The corners of the NZ answer with hairpin step `e`. -/
def decMkN (p : Program) (i r : ℕ) (e : ℤ) : List Corner :=
  nzAnsCorners p (instrBand i) r (callerIdx p r i)
    (hairReg p 3 e (U p r + nzAnsChan p (callerIdx p r i))) (i + 1) (decTN p i r)

/-- The corners of the Z answer with hairpin step `e`. -/
def decMkZ (p : Program) (i r z : ℕ) (e : ℤ) : List Corner :=
  zAnsCorners p (instrBand i) r (callerIdx p r i)
    (hairReg p 4 e (U p r + zAnsChan p (callerIdx p r i))) z (decTZ p i r z)

/-- The hairpin step of the NZ answer (window rule). -/
def decEA (p : Program) (i r : ℕ) : ℤ :=
  solveE (decGN p i r) (decMkN p i r) (destWin p (i + 1) (decTN p i r))

/-- The hairpin step of the Z answer (window rule). -/
def decEB (p : Program) (i r z : ℕ) : ℤ :=
  solveE (decGZ p i r) (decMkZ p i r z) (destWin p z (decTZ p i r z))

/-- **The routes of `decSpecs`, named.** -/
theorem decSpecs_eq (p : Program) (i r z : ℕ) :
    decSpecs p i r z =
      [(unitWL p i decLWL, decCornN p i r), (unitWL p i decRWL, decCornC p i r),
        (unitWL p i decDWL, decCornZ p i r), (decGN p i r, decMkN p i r (decEA p i r)),
        (decGZ p i r, decMkZ p i r z (decEB p i r z))] := rfl

/-! ### Lines of the control and the tokens -/

/-- The first world line of a `dec` output `w` (column `w`) placed in unit `i` is a `SE` line on
the column `A_i + w`. -/
theorem unitWL_dec_lane (p : Program) (i : ℕ) (w τ : ℤ) :
    (unitWL p i ⟨1, 1, w, τ⟩).dx = 1 ∧ (unitWL p i ⟨1, 1, w, τ⟩).dy = 1 ∧
      (unitWL p i ⟨1, 1, w, τ⟩).lane = A p i + w := by
  have hu := unitD_uv p i
  refine ⟨rfl, rfl, ?_⟩
  simp only [unitWL, WL.shift]
  omega

/-- **The lines of the token `KNZ`**: every corner is met on the input line of its reflector; the
token leaves `NE` through the port corner of its channel. -/
theorem decKNZ_lines (p : Program) (i r : ℕ) :
    RouteLines (unitWL p i decLWL) (decCornN p i r) ∧
      (route (unitWL p i decLWL) (decCornN p i r)).2.Through
        (U p r + nzTokChan p (callerIdx p r i)) (nzTokPortV (callerIdx p r i)) := by
  obtain ⟨h1, h2, h3⟩ := unitWL_dec_lane p i (-155) 2665
  have hp := nzTokChan_parity p i r (callerIdx p r i)
  have hU := U_even p r
  have := downCorners_lines p (instrBand i) 0 (A p i + decL)
    (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
    (U p r + nzTokChan p (callerIdx p r i)) (nzTokPortV (callerIdx p r i)) r
    (2 * D p + 1 + 2 * (callerIdx p r i)) (g := unitWL p i decLWL) h1 h2 h3
    (by unfold hairKNZ; have := fixp_parity (hairC p (qOf p ↑(callerIdx p r i)) (A p ↑i + decR)
          - 62 - 2 * eN (qOf p ↑(callerIdx p r i))) ((A p ↑i + decL) % 2); omega)
    hp.1 (by omega)
  exact ⟨this.1, this.2.2.2⟩

/-- **The lines of the control `C`**: every corner is met on the input line of its reflector; `C`
leaves `NE` through the port corner of DEC copy `2 j`. -/
theorem decC_lines (p : Program) (i r : ℕ) :
    RouteLines (unitWL p i decRWL) (decCornC p i r) ∧
      (decGC p i r).Through (U p r + decChan p (2 * (callerIdx p r i)))
        (decPortV p (2 * (callerIdx p r i))) := by
  obtain ⟨h1, h2, h3⟩ := unitWL_dec_lane p i 127 1221
  have hp := decChan_parity p i r (callerIdx p r i)
  have hU := U_even p r
  have := downCorners_lines p (instrBand i) 1 (A p i + decR)
    (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
    (U p r + decChan p (2 * (callerIdx p r i))) (decPortV p (2 * (callerIdx p r i))) r
    (2 * (callerIdx p r i)) (g := unitWL p i decRWL) h1 h2 h3
    (by unfold hairC; have := fixp_parity (HI p + 90 - 2 * eCtot (qOf p ↑(callerIdx p r i)))
          ((A p ↑i + decR) % 2); omega)
    hp.1 (by omega)
  exact ⟨this.1, this.2.2.2⟩

/-- **The lines of the Z token link**: a glider flying `SE` on the source column `c` (of the
parity of the channel) meets every corner of `ztokCorners` on its input line. -/
theorem ztokCorners_lines (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0)
    (hd : (U p r + zTokChan p j - c) % 2 = 0) :
    RouteLines g (ztokCorners p b c H r j) := by
  have ho := trackOut_par p b 2 c
  have hb := trackBack_par p b 2 c
  have hU := U_even p r
  obtain ⟨-, h2, h3⟩ := zTokChan_parity p 0 r j
  set vO := trackOut p b 2 c
  set vB := trackBack p b 2 c
  set cd := U p r + zTokChan p j
  set wd := zTokDepth p j
  set st := U p r + zTokStation j
  have hcw : (cd + wd) % 2 = 1 := by omega
  have hsw : (st + wd) % 2 = 1 := by omega
  simp only [ztokCorners, bandCorners, List.cons_append, List.nil_append, RouteLines]
  have p1 : (c - rfCU 3 + vO - rfCV 3) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l1 : OnLine g ⟨3, c, vO, .band b 2 false⟩ :=
    onLine_of_through (by simp [hdx, rfIn]) (by simp [hdy, rfIn]) p1
      (by simp only [WL.Through, hdx, hdy, hl]; ring)
  obtain ⟨t1, x1, y1⟩ := reflect_through g ⟨3, c, vO, .band b 2 false⟩ p1
  set g1 := (reflect g ⟨3, c, vO, .band b 2 false⟩).2
  simp only [rfOut] at x1 y1
  have p2 : (H - rfCU 7 + vO - rfCV 7) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l2 : OnLine g1 ⟨7, H, vO, .band b 2 true⟩ :=
    onLine_of_through (by simp [x1, rfIn]) (by simp [y1, rfIn]) p2
      (by simp only [WL.Through, x1, y1] at t1 ⊢; linarith)
  obtain ⟨t2, x2, y2⟩ := reflect_through g1 ⟨7, H, vO, .band b 2 true⟩ p2
  set g2 := (reflect g1 ⟨7, H, vO, .band b 2 true⟩).2
  simp only [rfOut] at x2 y2
  have p3 : (H - rfCU 4 + vB - rfCV 4) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l3 : OnLine g2 ⟨4, H, vB, .band b (9 - 2) true⟩ :=
    onLine_of_through (by simp [x2, rfIn]) (by simp [y2, rfIn]) p3
      (by simp only [WL.Through, x2, y2] at t2 ⊢; linarith)
  obtain ⟨t3, x3, y3⟩ := reflect_through g2 ⟨4, H, vB, .band b (9 - 2) true⟩ p3
  set g3 := (reflect g2 ⟨4, H, vB, .band b (9 - 2) true⟩).2
  simp only [rfOut] at x3 y3
  have p4 : (cd - rfCU 2 + vB - rfCV 2) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l4 : OnLine g3 ⟨2, cd, vB, .band b (9 - 2) false⟩ :=
    onLine_of_through (by simp [x3, rfIn]) (by simp [y3, rfIn]) p4
      (by simp only [WL.Through, x3, y3] at t3 ⊢; linarith)
  obtain ⟨t4, x4, y4⟩ := reflect_through g3 ⟨2, cd, vB, .band b (9 - 2) false⟩ p4
  set g4 := (reflect g3 ⟨2, cd, vB, .band b (9 - 2) false⟩).2
  simp only [rfOut] at x4 y4
  have p5 : (cd - rfCU 3 + wd - rfCV 3) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l5 : OnLine g4 ⟨3, cd, wd, .right r j 2⟩ :=
    onLine_of_through (by simp [x4, rfIn]) (by simp [y4, rfIn]) p5
      (by simp only [WL.Through, x4, y4] at t4 ⊢; linarith)
  obtain ⟨t5, x5, y5⟩ := reflect_through g4 ⟨3, cd, wd, .right r j 2⟩ p5
  set g5 := (reflect g4 ⟨3, cd, wd, .right r j 2⟩).2
  simp only [rfOut] at x5 y5
  have p6 : (st - rfCU 0 + wd - rfCV 0) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l6 : OnLine g5 ⟨0, st, wd, .right r j 3⟩ :=
    onLine_of_through (by simp [x5, rfIn]) (by simp [y5, rfIn]) p6
      (by simp only [WL.Through, x5, y5] at t5 ⊢; linarith)
  exact ⟨l1, l2, l3, l4, l5, l6, trivial⟩

/-- **The lines of the token `KZ`.** -/
theorem decKZ_lines (p : Program) (i r : ℕ) :
    RouteLines (unitWL p i decDWL) (decCornZ p i r) := by
  obtain ⟨h1, h2, h3⟩ := unitWL_dec_lane p i 188 787
  exact ztokCorners_lines p _ _ _ r _ h1 h2 h3
    (by unfold hairKZ; exact hairReg_par _ _ _ _) (zTokChan_parity p i r _).1

/-! ### The control `C` at the DEC chain -/

/-- The closed form of `C` at the end of its route. -/
theorem decGC_eq (p : Program) (i r : ℕ) :
    decGC p i r = ⟨1, -1, -decPortV p (2 * (callerIdx p r i)),
      (unitWL p i decRWL).tau + 4 * (A p i + decR) -
        4 * hairC p (qOf p (callerIdx p r i)) (A p i + decR) - 25⟩ := by
  obtain ⟨h1, h2, h3⟩ := unitWL_dec_lane p i 127 1221
  have hp := decChan_parity p i r (callerIdx p r i)
  have hU := U_even p r
  exact downCorners_final p _ _ _ _ _ _ r _ h1 h2 h3
    (by unfold hairC; have := fixp_parity (HI p + 90 - 2 * eCtot (qOf p ↑(callerIdx p r i)))
          ((A p ↑i + decR) % 2); omega)
    hp.1 (by omega)

/-- The arrival of `C` relative to the window of DEC copy `2 j`, as an explicit number. -/
theorem decC_rel (p : Program) (i r : ℕ) :
    (decGC p i r).tau - (decWin p r (2 * (callerIdx p r i))).tau =
      1221 - 2 * (A p i + VU p) + 4 * (A p i + decR) -
        4 * hairC p (qOf p (callerIdx p r i)) (A p i + decR) - 25 -
        (6801 + 140 * (2 * D p - 1 - 2 * (callerIdx p r i)) +
          (15 + 16 * (2 * D p - 1 - 2 * (callerIdx p r i))) % 30 - 2 * U p r) := by
  have hu := unitD_uv p i
  have hU := U_even p r
  rw [decGC_eq]
  simp only [decWin, modWL, modDX, unitWL, decRWL, WL.shift]
  omega

/-- **`C` arrives at offset `4 + 2 σ` of the window of DEC copy `2 j`** (`4` for even `q`, `8` for
odd `q`), for every program. -/
theorem decC_offset (p : Program) (i r : ℕ) :
    ((decGC p i r).tau - (decWin p r (2 * (callerIdx p r i))).tau) % 30 =
      4 + 2 * sigma (qOf p (callerIdx p r i)) := by
  rw [decC_rel]
  have hA := A_mod p i
  have hV := VT_mod p
  have hU := U_mod p r
  have hH := HI_mod p
  generalize (callerIdx p r i : ℤ) = j
  unfold hairC eCtot fixp eC sigma qOf VU decR at *
  generalize xC (D p - 1 - j) = x
  omega

/-- **`C` arrives on the window of DEC copy `2 j`**, delayed by its offset `4 + 2 σ` and its slot:
the form required by the side input of the DEC chain. -/
theorem decC_window (p : Program) (i r : ℕ) :
    decGC p i r = (decWin p r (2 * (callerIdx p r i))).shift 0 0
      (4 + 2 * sigma (qOf p (callerIdx p r i)) + 30 * decSlot p i r) := by
  have ho := decC_offset p i r
  have hU := U_even p r
  have hr := decC_rel p i r
  rw [decSlot, slot]
  rw [decGC_eq] at ho hr ⊢
  simp only [decWin, modWL, modDX, modDY, WL.shift, decPortV, WL.mk.injEq, true_and] at ho hr ⊢
  constructor <;> omega

/-- **The shift of the module's world lines**: `sh = 2385 + 254 m + (15 + 16 m) mod 30 + 30 k` for
the DEC copy `m = 2 D - 1 - 2 j` (from the downstream end) and the slot `k` of `C`. -/
theorem decShift_eq (p : Program) (i r : ℕ) :
    decShift p i r = 2385 + 254 * (2 * D p - 1 - 2 * (callerIdx p r i)) +
      (15 + 16 * (2 * D p - 1 - 2 * (callerIdx p r i))) % 30 + 30 * decSlot p i r := by
  simp only [decShift, cprimeWL, cp0WL, modWL, WL.shift]
  ring

/-- **The shift is a multiple of `30`**: the module's world lines keep their phases. -/
theorem decShift_mod (p : Program) (i r : ℕ) : decShift p i r % 30 = 0 := by
  rw [decShift_eq]
  omega

/-! ### The tokens reach their stations exactly -/

/-- The world line of the NZ token in the capture certificate of station `j` (module frame,
timed for `cp0WL`): `NE` on the port line `1256 + 144 j`. -/
def tokNZWL (j : ℤ) : WL := ⟨1, -1, -(1256 + 144 * j), 8806⟩

/-- The world line of the Z token in the capture certificate of station `j` (module frame, timed
for `cp0WL`): `NW` on the station column `1230 + 144 j`. -/
def tokZWL (j : ℤ) : WL := ⟨-1, -1, -(1230 + 144 * j), 16087 + 576 * j⟩

/-- **The token `KNZ` ends exactly on the token line of station `j`** (delayed by the shift), for
every program: `δ_NZ = 0`. -/
theorem decKNZ_target (p : Program) (i r : ℕ) :
    (route (unitWL p i decLWL) (decCornN p i r)).2 =
      (modWL p r (tokNZWL (callerIdx p r i))).shift 0 0 (decShift p i r) := by
  obtain ⟨h1, h2, h3⟩ := unitWL_dec_lane p i (-155) 2665
  have hp := nzTokChan_parity p i r (callerIdx p r i)
  have hU := U_even p r
  have hf := downCorners_final p (instrBand i) 0 (A p i + decL)
    (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
    (U p r + nzTokChan p (callerIdx p r i)) (nzTokPortV (callerIdx p r i)) r
    (2 * D p + 1 + 2 * (callerIdx p r i)) (g := unitWL p i decLWL) h1 h2 h3
    (by unfold hairKNZ; have := fixp_parity (hairC p (qOf p ↑(callerIdx p r i)) (A p ↑i + decR)
          - 62 - 2 * eN (qOf p ↑(callerIdx p r i))) ((A p ↑i + decL) % 2); omega)
    hp.1 (by omega)
  rw [decCornN, hf, decShift_eq]
  have hs := decC_rel p i r
  have hA := A_mod p i
  have hV := VT_mod p
  have hUm := U_mod p r
  have hH := HI_mod p
  have hu := unitD_uv p i
  rw [decSlot, slot, hs]
  simp only [tokNZWL, modWL, modDX, modDY, unitWL, decLWL, WL.shift, nzTokPortV, WL.mk.injEq,
    true_and]
  generalize (callerIdx p r i : ℤ) = j at *
  unfold hairKNZ hairC eCtot eN fixp eC sigma qOf VU decR decL at *
  generalize xC (D p - 1 - j) = x
  constructor <;> omega

/-- **The token `KZ` ends exactly on the token line of station `j`** (delayed by the shift), for
every program: `δ_Z = -1` in `R-29`'s numbering is the timing of the capture certificate. -/
theorem decKZ_target (p : Program) (i r : ℕ) :
    (route (unitWL p i decDWL) (decCornZ p i r)).2 =
      (modWL p r (tokZWL (callerIdx p r i))).shift 0 0 (decShift p i r) := by
  obtain ⟨h1, h2, h3⟩ := unitWL_dec_lane p i 188 787
  have hf := ztokCorners_final p (instrBand i) (A p i + decD)
    (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD)) r (callerIdx p r i)
    (g := unitWL p i decDWL) h1 h2 h3 (by unfold hairKZ; exact hairReg_par _ _ _ _)
    (zTokChan_parity p i r _).1
  rw [decCornZ, hf, decShift_eq]
  have hs := decC_rel p i r
  have hA := A_mod p i
  have hV := VT_mod p
  have hUm := U_mod p r
  have hU := U_even p r
  have hH := HI_mod p
  have hu := unitD_uv p i
  have hz := zAnsDepth_eq p (callerIdx p r i)
  rw [decSlot, slot, hs]
  simp only [tokZWL, modWL, modDX, modDY, unitWL, decDWL, WL.shift, zTokStation, WL.mk.injEq,
    true_and]
  generalize (callerIdx p r i : ℤ) = j at *
  unfold zTokChan zTokDepth uR hairKZ hairReg eKZ dZ0 hairC eCtot fixp eC sigma qOf VU decR
    decD at *
  generalize xC (D p - 1 - j) = x
  constructor <;> omega

end LP

end LeanTheory.Life
