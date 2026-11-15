/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecLinks

/-!
# The answers of a `decJz` activation: lines, closed forms, arrival offsets and times

Research note `N-22`, layer 3. The answer of `decJz r z` at instruction `i` leaves station `j`
of module `r` (`decGN`: the NZ answer, `SW` on the NZ answer port line; `decGZ`: the Z answer,
`SE` on the Z station column) and flies to entry copy `decTN` of unit `i + 1`, resp. `decTZ` of
unit `z` (`decMkN`, `decMkZ` of `decSpecs`). This module proves, for every program:

* **lines** (`ansTail_lines`, `nzAnsCorners_lines`, `zAnsCorners_lines`, `decAnsN_lines`,
  `decAnsZ_lines`): every corner is met on the input line of its reflector and the answer arrives
  `NE` through the input corner of its entry copy;
* **closed forms** (`ansTail_final`, `nzAnsCorners_final`, `zAnsCorners_final`);
* **arrival offsets** (`decAnsN_offset`, `decAnsZ_offset`, `decAnsN_arrival`,
  `decAnsZ_arrival`): with the hairpin steps of `decSpecs` the answers arrive at offset `4` or `5`
  of the window of their entry copy (the window rule), i.e. on `(destWin a t).shift 0 0 (δ + 30 k)`,
  the form required by `entry_reaction`;
* **times** (`ctrlTime`, `ctrlTime_mod`, `decNZ_late`, `decZ_late`): the control reaches the
  entrance of the next unit at a time `≡ 0 (mod 30)`, and only after everything the activation
  started in module `r` has finished: for NZ the circuit's rest (`sh + 11190`) and the absorption
  of the unpaired Z token at station `j` (`sh + 12662 + 288 j`), for Z the circuit's rest after
  the Z restore (`sh + 27240`); `sh` is the shift `decShift` of the module's world lines.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The tail of an answer: from the channel up to the entry copy -/

/-- **The lines of the tail of an answer** (`upCornersK 5`): a glider flying `NW` on the channel
column `c` meets every corner on its input line and leaves `NE` through the input corner of the
entry copy, provided the hairpin and the input column have the parity of `c` and the input corner
has odd `u + v`. -/
theorem ansTail_lines (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) {g : WL} (hdx : g.dx = -1)
    (hdy : g.dy = -1) (hl : g.lane = -c) (hH : (H - c) % 2 = 0)
    (hd : (destU p a t - c) % 2 = 0) (hv : (destU p a t + destV p t) % 2 = 1) :
    RouteLines g (upCornersK 5 p b s c H a t) ∧ (route g (upCornersK 5 p b s c H a t)).2.dx = 1 ∧
      (route g (upCornersK 5 p b s c H a t)).2.dy = -1 ∧
      (route g (upCornersK 5 p b s c H a t)).2.Through (destU p a t) (destV p t) := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  set vO := trackOut p b s c
  set vB := trackBack p b s c
  set cd := destU p a t
  set vD := destV p t
  simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, route, RouteLines]
  have p1 : (c - rfCU 5 + vO - rfCV 5) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l1 : OnLine g ⟨5, c, vO, .band b s false⟩ :=
    onLine_of_through (by simp [hdx, rfIn]) (by simp [hdy, rfIn]) p1
      (by simp only [WL.Through, hdx, hdy, hl]; ring)
  obtain ⟨t1, x1, y1⟩ := reflect_through g ⟨5, c, vO, .band b s false⟩ p1
  set g1 := (reflect g ⟨5, c, vO, .band b s false⟩).2
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
  have p4 : (cd - rfCU 6 + vB - rfCV 6) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l4 : OnLine g3 ⟨6, cd, vB, .band b (9 - s) false⟩ :=
    onLine_of_through (by simp [x3, rfIn]) (by simp [y3, rfIn]) p4
      (by simp only [WL.Through, x3, y3] at t3 ⊢; linarith)
  obtain ⟨t4, x4, y4⟩ := reflect_through g3 ⟨6, cd, vB, .band b (9 - s) false⟩ p4
  set g4 := (reflect g3 ⟨6, cd, vB, .band b (9 - s) false⟩).2
  simp only [rfOut] at x4 y4
  have p5 : (cd - rfCU 1 + vD - rfCV 1) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l5 : OnLine g4 ⟨1, cd, vD, .slab a t⟩ :=
    onLine_of_through (by simp [x4, rfIn]) (by simp [y4, rfIn]) p5
      (by simp only [WL.Through, x4, y4] at t4 ⊢; linarith)
  obtain ⟨t5, x5, y5⟩ := reflect_through g4 ⟨1, cd, vD, .slab a t⟩ p5
  simp only [rfOut] at x5 y5
  exact ⟨⟨l1, l2, l3, l4, l5, trivial⟩, x5, y5, t5⟩

/-- **The closed form of the tail of an answer**: from a `NW` glider on the column `c`, the answer
leaves `NE` through the input corner of the entry copy, with reference time
`tau + 4 (BACK - OUT) - 4 H - 4 v_t - 25`. -/
theorem ansTail_final (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) {g : WL} (hdx : g.dx = -1)
    (hdy : g.dy = -1) (hl : g.lane = -c) (hH : (H - c) % 2 = 0)
    (hd : (destU p a t - c) % 2 = 0) (hv : (destU p a t + destV p t) % 2 = 1) :
    (route g (upCornersK 5 p b s c H a t)).2 = ⟨1, -1, -destV p t,
      g.tau + 4 * (trackBack p b s c - trackOut p b s c) - 4 * H - 4 * destV p t - 25⟩ := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl
  subst hdx hdy hl
  simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, route, reflect,
    WL.shift, rfIn, rfOut, rfX, rfY, rfCU, rfCV, WL.mk.injEq, true_and]
  generalize destU p a t = cd at *
  generalize destV p t = vD at *
  generalize trackOut p b s c = vO at *
  generalize trackBack p b s c = vB at *
  constructor <;> omega

/-! ### The NZ and Z answers -/

/-- **The lines of an NZ answer**: a glider flying `SW` on the NZ answer port line of caller `j`
meets every corner of `nzAnsCorners` on its input line and leaves `NE` through the input corner of
the entry copy. -/
theorem nzAnsCorners_lines (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) {g : WL}
    (hdx : g.dx = -1) (hdy : g.dy = 1) (hl : g.lane = nzAnsPortV j)
    (hH : (H - (U p r + nzAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + nzAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) :
    RouteLines g (nzAnsCorners p b r j H a t) ∧ (route g (nzAnsCorners p b r j H a t)).2.dx = 1 ∧
      (route g (nzAnsCorners p b r j H a t)).2.dy = -1 ∧
      (route g (nzAnsCorners p b r j H a t)).2.Through (destU p a t) (destV p t) := by
  have hU := U_even p r
  have hp := nzAnsChan_parity p j
  have p0 : (U p r + nzAnsChan p j - rfCU 0 + nzAnsPortV j - rfCV 0) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  have l0 : OnLine g ⟨0, U p r + nzAnsChan p j, nzAnsPortV j, .left r (2 * D p + 2 + 2 * j)⟩ :=
    onLine_of_through (by simp [hdx, rfIn]) (by simp [hdy, rfIn]) p0
      (by simp only [WL.Through, hdx, hdy, hl]; ring)
  obtain ⟨t0, x0, y0⟩ := reflect_through g
    ⟨0, U p r + nzAnsChan p j, nzAnsPortV j, .left r (2 * D p + 2 + 2 * j)⟩ p0
  simp only [rfOut] at x0 y0
  have h := ansTail_lines p b 3 (U p r + nzAnsChan p j) H a t x0 y0
    (by simp only [WL.Through, x0, y0] at t0; omega) hH hd hv
  simp only [nzAnsCorners, route, RouteLines]
  exact ⟨⟨l0, h.1⟩, h.2⟩

/-- **The closed form of an NZ answer**: reference time `tau + 744 - 4 H - 4 v_t - 30`. -/
theorem nzAnsCorners_final (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) {g : WL}
    (hdx : g.dx = -1) (hdy : g.dy = 1) (hl : g.lane = nzAnsPortV j)
    (hH : (H - (U p r + nzAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + nzAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) :
    (route g (nzAnsCorners p b r j H a t)).2 =
      ⟨1, -1, -destV p t, g.tau + 744 - 4 * H - 4 * destV p t - 30⟩ := by
  have hU := U_even p r
  have hp := nzAnsChan_parity p j
  have p0 : (U p r + nzAnsChan p j - rfCU 0 + nzAnsPortV j - rfCV 0) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  obtain ⟨t0, x0, y0⟩ := reflect_through g
    ⟨0, U p r + nzAnsChan p j, nzAnsPortV j, .left r (2 * D p + 2 + 2 * j)⟩ p0
  simp only [rfOut] at x0 y0
  have h := ansTail_final p b 3 (U p r + nzAnsChan p j) H a t x0 y0
    (by simp only [WL.Through, x0, y0] at t0; omega) hH hd hv
  simp only [nzAnsCorners, route]
  rw [h]
  have hBO : trackBack p b 3 (U p r + nzAnsChan p j) - trackOut p b 3 (U p r + nzAnsChan p j) =
      186 := by unfold trackBack trackOut track; ring
  rw [hBO]
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl
  subst hdx hdy hl
  simp only [reflect, WL.shift, rfIn, rfOut, rfX, rfCU, rfCV, WL.mk.injEq, true_and]
  omega

/-- **The lines of a Z answer**: a glider flying `SE` on the Z station column of caller `j` meets
every corner of `zAnsCorners` on its input line and leaves `NE` through the input corner of the
entry copy. -/
theorem zAnsCorners_lines (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = U p r + zAnsStation j)
    (hH : (H - (U p r + zAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + zAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) :
    RouteLines g (zAnsCorners p b r j H a t) ∧ (route g (zAnsCorners p b r j H a t)).2.dx = 1 ∧
      (route g (zAnsCorners p b r j H a t)).2.dy = -1 ∧
      (route g (zAnsCorners p b r j H a t)).2.Through (destU p a t) (destV p t) := by
  have hU := U_even p r
  have hp := zAnsChan_parity p j
  have p0 : (U p r + zAnsStation j - rfCU 4 + zAnsDepth p j - rfCV 4) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  have l0 : OnLine g ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩ :=
    onLine_of_through (by simp [hdx, rfIn]) (by simp [hdy, rfIn]) p0
      (by simp only [WL.Through, hdx, hdy, hl]; ring)
  obtain ⟨t0, x0, y0⟩ :=
    reflect_through g ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩ p0
  set g0 := (reflect g ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩).2
  simp only [rfOut] at x0 y0
  have p1 : (U p r + zAnsChan p j - rfCU 6 + zAnsDepth p j - rfCV 6) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  have l1 : OnLine g0 ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩ :=
    onLine_of_through (by simp [x0, rfIn]) (by simp [y0, rfIn]) p1
      (by simp only [WL.Through, x0, y0] at t0 ⊢; linarith)
  obtain ⟨t1, x1, y1⟩ :=
    reflect_through g0 ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩ p1
  simp only [rfOut] at x1 y1
  have h := ansTail_lines p b 4 (U p r + zAnsChan p j) H a t x1 y1
    (by simp only [WL.Through, x1, y1] at t1; omega) hH hd hv
  simp only [zAnsCorners, route, RouteLines]
  exact ⟨⟨l0, l1, h.1⟩, h.2⟩

/-- **The closed form of a Z answer**: reference time
`tau + 4 v_d + 4 (U_r + zAnsChan j) + 248 - 4 H - 4 v_t - 35`. -/
theorem zAnsCorners_final (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = U p r + zAnsStation j)
    (hH : (H - (U p r + zAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + zAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) :
    (route g (zAnsCorners p b r j H a t)).2 = ⟨1, -1, -destV p t,
      g.tau + 4 * zAnsDepth p j + 4 * (U p r + zAnsChan p j) + 248 - 4 * H - 4 * destV p t - 35⟩
    := by
  have hU := U_even p r
  have hp := zAnsChan_parity p j
  have p0 : (U p r + zAnsStation j - rfCU 4 + zAnsDepth p j - rfCV 4) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  obtain ⟨t0, x0, y0⟩ :=
    reflect_through g ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩ p0
  set g0 := (reflect g ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩).2 with hg0
  simp only [rfOut] at x0 y0
  have p1 : (U p r + zAnsChan p j - rfCU 6 + zAnsDepth p j - rfCV 6) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  obtain ⟨t1, x1, y1⟩ :=
    reflect_through g0 ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩ p1
  set g1 := (reflect g0 ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩).2 with hg1
  simp only [rfOut] at x1 y1
  have h := ansTail_final p b 4 (U p r + zAnsChan p j) H a t x1 y1
    (by simp only [WL.Through, x1, y1] at t1; omega) hH hd hv
  simp only [zAnsCorners, route]
  rw [← hg0, ← hg1, h]
  have hBO : trackBack p b 4 (U p r + zAnsChan p j) - trackOut p b 4 (U p r + zAnsChan p j) =
      62 := by unfold trackBack trackOut track; ring
  rw [hBO]
  have e1 : g1.tau = g.tau + 4 * (U p r + zAnsChan p j) + 4 * zAnsDepth p j - 10 := by
    rw [hg1, hg0]
    obtain ⟨dx, dy, lane, tau⟩ := g
    simp only at hdx hdy hl
    subst hdx hdy hl
    simp only [reflect, WL.shift, rfIn, rfOut, rfX, rfCU, rfCV, zAnsStation] at p0 p1 ⊢
    generalize zAnsChan p j = cA at *
    generalize zAnsDepth p j = vd at *
    omega
  simp only [WL.mk.injEq, true_and]
  omega

/-! ### The answers of a `decJz` instruction -/

/-- The NZ answer of the activation leaves its station `SW` on the NZ answer port line. -/
theorem decGN_dir (p : Program) (i r : ℕ) :
    (decGN p i r).dx = -1 ∧ (decGN p i r).dy = 1 ∧
      (decGN p i r).lane = nzAnsPortV (callerIdx p r i) := by
  have hU := U_even p r
  refine ⟨rfl, rfl, ?_⟩
  simp only [decGN, modWL, modDX, modDY, nzAnsWL, WL.shift, nzAnsPortV]
  omega

/-- The Z answer of the activation leaves its station `SE` on the Z station column. -/
theorem decGZ_dir (p : Program) (i r : ℕ) :
    (decGZ p i r).dx = 1 ∧ (decGZ p i r).dy = 1 ∧
      (decGZ p i r).lane = U p r + zAnsStation (callerIdx p r i) := by
  have hU := U_even p r
  refine ⟨rfl, rfl, ?_⟩
  simp only [decGZ, modWL, modDX, modDY, zAnsWL, WL.shift, zAnsStation]
  omega

/-- The input column of the entry copy of the NZ answer has the parity of its channel. -/
theorem decTN_par (p : Program) (i r : ℕ) :
    (destU p (i + 1) (decTN p i r) - (U p r + nzAnsChan p (callerIdx p r i))) % 2 = 0 ∧
      (destU p (i + 1) (decTN p i r) + destV p (decTN p i r)) % 2 = 1 := by
  have ha := A_even p (i + 1)
  have hv := VU_even p
  have hc := copyBeta_spec (unitC0 p (i + 1)) (predIdx p (i + 1) i 0)
    (U p r + nzAnsChan p (callerIdx p r i))
  have hC0 : unitC0 p (i + 1) % 2 = 1 := by
    obtain h | h | h := unitC0_cases p (i + 1) <;> rw [h] <;> rfl
  simp only [decTN, destU, destV, inCol, sideV] at hc ⊢
  push_cast at ha ⊢
  constructor <;> omega

/-- The input column of the entry copy of the Z answer has the parity of its channel. -/
theorem decTZ_par (p : Program) (i r z : ℕ) :
    (destU p z (decTZ p i r z) - (U p r + zAnsChan p (callerIdx p r i))) % 2 = 0 ∧
      (destU p z (decTZ p i r z) + destV p (decTZ p i r z)) % 2 = 1 := by
  have ha := A_even p z
  have hv := VU_even p
  have hc := copyBeta_spec (unitC0 p z) (predIdx p z i (if i + 1 = z then 1 else 0))
    (U p r + zAnsChan p (callerIdx p r i))
  have hC0 : unitC0 p z % 2 = 1 := by
    obtain h | h | h := unitC0_cases p z <;> rw [h] <;> rfl
  simp only [decTZ, destU, destV, inCol, sideV] at hc ⊢
  constructor <;> omega

/-- **The lines of the NZ answer of `decJz`**, for every hairpin step `e`. -/
theorem decAnsN_lines (p : Program) (i r : ℕ) (e : ℤ) :
    RouteLines (decGN p i r) (decMkN p i r e) ∧ (route (decGN p i r) (decMkN p i r e)).2.dx = 1 ∧
      (route (decGN p i r) (decMkN p i r e)).2.dy = -1 ∧
      (route (decGN p i r) (decMkN p i r e)).2.Through (destU p (i + 1) (decTN p i r))
        (destV p (decTN p i r)) := by
  obtain ⟨h1, h2, h3⟩ := decGN_dir p i r
  exact nzAnsCorners_lines p _ r _ _ _ _ h1 h2 h3 (hairReg_par _ _ _ _) (decTN_par p i r).1
    (decTN_par p i r).2

/-- **The lines of the Z answer of `decJz`**, for every hairpin step `e`. -/
theorem decAnsZ_lines (p : Program) (i r z : ℕ) (e : ℤ) :
    RouteLines (decGZ p i r) (decMkZ p i r z e) ∧
      (route (decGZ p i r) (decMkZ p i r z e)).2.dx = 1 ∧
      (route (decGZ p i r) (decMkZ p i r z e)).2.dy = -1 ∧
      (route (decGZ p i r) (decMkZ p i r z e)).2.Through (destU p z (decTZ p i r z))
        (destV p (decTZ p i r z)) := by
  obtain ⟨h1, h2, h3⟩ := decGZ_dir p i r
  exact zAnsCorners_lines p _ r _ _ _ _ h1 h2 h3 (hairReg_par _ _ _ _) (decTZ_par p i r z).1
    (decTZ_par p i r z).2

/-- The final world line of the NZ answer of `decJz` (closed form). -/
theorem decAnsN_final (p : Program) (i r : ℕ) (e : ℤ) :
    (route (decGN p i r) (decMkN p i r e)).2 = ⟨1, -1, -destV p (decTN p i r),
      (decGN p i r).tau + 744 - 4 * hairReg p 3 e (U p r + nzAnsChan p (callerIdx p r i)) -
        4 * destV p (decTN p i r) - 30⟩ := by
  obtain ⟨h1, h2, h3⟩ := decGN_dir p i r
  exact nzAnsCorners_final p _ r _ _ _ _ h1 h2 h3 (hairReg_par _ _ _ _) (decTN_par p i r).1
    (decTN_par p i r).2

/-- The final world line of the Z answer of `decJz` (closed form). -/
theorem decAnsZ_final (p : Program) (i r z : ℕ) (e : ℤ) :
    (route (decGZ p i r) (decMkZ p i r z e)).2 = ⟨1, -1, -destV p (decTZ p i r z),
      (decGZ p i r).tau + 4 * zAnsDepth p (callerIdx p r i) +
        4 * (U p r + zAnsChan p (callerIdx p r i)) + 248 -
        4 * hairReg p 4 e (U p r + zAnsChan p (callerIdx p r i)) -
        4 * destV p (decTZ p i r z) - 35⟩ := by
  obtain ⟨h1, h2, h3⟩ := decGZ_dir p i r
  exact zAnsCorners_final p _ r _ _ _ _ h1 h2 h3 (hairReg_par _ _ _ _) (decTZ_par p i r z).1
    (decTZ_par p i r z).2

/-! ### Arrival offsets: the window rule -/

/-- **The NZ answer arrives at offset `4` or `5`** of the window of its entry copy. -/
theorem decAnsN_offset (p : Program) (i r : ℕ) :
    ((route (decGN p i r) (decMkN p i r (decEA p i r))).2.tau -
        (destWin p (i + 1) (decTN p i r)).tau) % 30 = 4 ∨
      ((route (decGN p i r) (decMkN p i r (decEA p i r))).2.tau -
        (destWin p (i + 1) (decTN p i r)).tau) % 30 = 5 := by
  refine upLink_offset _ _ (decMkN p i r) fun e => ?_
  rw [decAnsN_final, decAnsN_final, hairReg_e p 3 e]
  simp only
  ring

/-- **The Z answer arrives at offset `4` or `5`** of the window of its entry copy. -/
theorem decAnsZ_offset (p : Program) (i r z : ℕ) :
    ((route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2.tau -
        (destWin p z (decTZ p i r z)).tau) % 30 = 4 ∨
      ((route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2.tau -
        (destWin p z (decTZ p i r z)).tau) % 30 = 5 := by
  refine upLink_offset _ _ (decMkZ p i r z) fun e => ?_
  rw [decAnsZ_final, decAnsZ_final, hairReg_e p 4 e]
  simp only
  ring

/-- The window offset of a world line `g` arriving on the window `win`. -/
def offOf (g win : WL) : ℤ := (g.tau - win.tau) % 30

/-- The window slot of a world line `g` arriving on the window `win` (`slot`). -/
theorem slot_spec (g win : WL) : g.tau - win.tau = offOf g win + 30 * slot g win := by
  unfold offOf slot
  omega

/-- **The NZ answer arrives on the side line of its entry copy**, delayed by its offset
`δ ∈ {4, 5}` and its slot: the form required by `entry_reaction`. -/
theorem decAnsN_arrival (p : Program) (i r : ℕ) :
    let g := (route (decGN p i r) (decMkN p i r (decEA p i r))).2
    let win := destWin p (i + 1) (decTN p i r)
    (offOf g win = 4 ∨ offOf g win = 5) ∧ g = win.shift 0 0 (offOf g win + 30 * slot g win) := by
  intro g win
  refine ⟨decAnsN_offset p i r, ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := decAnsN_lines p i r (decEA p i r)
  rw [← slot_spec]
  have h := arrival_eq p (i + 1) (decTN p i r) h1 h2 h3
  rw [show (g.tau - win.tau) % 30 + 30 * ((g.tau - win.tau) / 30) = g.tau - win.tau by omega]
    at h
  exact h

/-- **The Z answer arrives on the side line of its entry copy**, delayed by its offset
`δ ∈ {4, 5}` and its slot. -/
theorem decAnsZ_arrival (p : Program) (i r z : ℕ) :
    let g := (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
    let win := destWin p z (decTZ p i r z)
    (offOf g win = 4 ∨ offOf g win = 5) ∧ g = win.shift 0 0 (offOf g win + 30 * slot g win) := by
  intro g win
  refine ⟨decAnsZ_offset p i r z, ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := decAnsZ_lines p i r z (decEB p i r z)
  rw [← slot_spec]
  have h := arrival_eq p z (decTZ p i r z) h1 h2 h3
  rw [show (g.tau - win.tau) % 30 + 30 * ((g.tau - win.tau) / 30) = g.tau - win.tau by omega]
    at h
  exact h

/-! ### Times of the next control -/

/-- **The time at which the control reaches the entrance of the next unit** (`ctrlAt`), for a
link arriving on entry copy `t` in slot `k`: the side input at `180 + 30 k + (16 t mod 30)`
(`side_arrival`), the entry chain `134 + 254 t`, the flight to the body input `166`. -/
def ctrlTime (k t : ℤ) : ℤ := 180 + 30 * k + 16 * t % 30 + 134 + 254 * t + 166

/-- The control reaches the entrance at a time `≡ 0 (mod 30)` (as `InvM` requires). -/
theorem ctrlTime_mod (k t : ℤ) : ctrlTime k t % 30 = 0 := by
  unfold ctrlTime
  omega

/-- A lower bound of the arrival time in terms of the reference time of the arriving world line. -/
theorem ctrlTime_ge (p : Program) (a : ℕ) (t : ℤ) (g : WL) :
    g.tau + 450 + 114 * t + 2 * (A p a + VU p) - 29 ≤
      ctrlTime (slot g (destWin p a t)) t := by
  have hu := unitD_uv p a
  unfold ctrlTime slot
  simp only [destWin, unitWL, sideWL, WL.shift]
  omega

/-- **After an NZ answer the next control comes late enough**: the control reaches the entrance of
unit `i + 1` after the register circuit's rest (`sh + 11190`) and after the absorption of the
unpaired Z token at station `j` (`sh + 12662 + 288 j`), for every program. -/
theorem decNZ_late (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    decShift p i r + 12662 + 288 * (callerIdx p r i : ℤ) ≤
      ctrlTime (slot (route (decGN p i r) (decMkN p i r (decEA p i r))).2
        (destWin p (i + 1) (decTN p i r))) (decTN p i r) := by
  refine le_trans ?_ (ctrlTime_ge p (i + 1) _ _)
  rw [decAnsN_final]
  have hj := callerIdx_lt_D p hi
  have hU := U_ge p (r := r) (by omega)
  have hUe := U_even p r
  have hA := A_nonneg p (a := ((i + 1 : ℕ) : ℤ)) (by omega)
  have hH := hairReg_le p (s := 3) (e := decEA p i r)
    (c := U p r + nzAnsChan p (callerIdx p r i)) (by norm_num) (solveE_bounds _ _ _).1
  have hHI : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hP := one_le_P p
  have ht : 0 ≤ decTN p i r := by
    have := predIdx_nonneg p (i + 1) i 0
    unfold decTN copyIdx; omega
  have hVT : VT p ≤ -3444 := by
    have := one_le_D p
    have := one_le_R p
    have := zero_le_N p
    unfold VT ceil30 NB; omega
  simp only [decGN, modWL, modDX, nzAnsWL, WL.shift, destV, sideV, VU] at hH ⊢
  simp only [U0, slabR, modLeft] at hU
  have := le_max_left (238 : ℤ) (86 + 58 * P p)
  push_cast at hA ⊢
  have hD1 := one_le_D p
  have hDn : D p = (numCallers p : ℤ) := rfl
  omega

/-- **After a Z answer the next control comes late enough**: the control reaches the entrance of
unit `z` after the register circuit's rest at the end of the Z restore (`sh + 27240`), for every
program. -/
theorem decZ_late (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    decShift p i r + 27240 ≤
      ctrlTime (slot (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
        (destWin p z (decTZ p i r z))) (decTZ p i r z) := by
  refine le_trans ?_ (ctrlTime_ge p z _ _)
  rw [decAnsZ_final]
  have hj := callerIdx_lt_D p hi
  have hU := U_ge p (r := r) (by omega)
  have hUe := U_even p r
  have hA := A_nonneg p (a := ((z : ℕ) : ℤ)) (by omega)
  have hH := hairReg_le p (s := 4) (e := decEB p i r z)
    (c := U p r + zAnsChan p (callerIdx p r i)) (by norm_num) (solveE_bounds _ _ _).1
  have hHI : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hP := one_le_P p
  have ht : 0 ≤ decTZ p i r z := by
    have := predIdx_nonneg p z i (if i + 1 = z then 1 else 0)
    unfold decTZ copyIdx; omega
  have hVT : VT p ≤ -3444 := by
    have := one_le_D p
    have := one_le_R p
    have := zero_le_N p
    unfold VT ceil30 NB; omega
  have hz := zAnsDepth_eq p (callerIdx p r i)
  have hc : uR p + 124 * qOf p (callerIdx p r i) - 1 ≤ zAnsChan p (callerIdx p r i) := by
    unfold zAnsChan; exact (fixp_bounds _ _).1
  simp only [decGZ, modWL, modDX, zAnsWL, WL.shift, destV, sideV, VU] at hH ⊢
  simp only [U0, slabR, modLeft] at hU
  have := le_max_left (238 : ℤ) (86 + 58 * P p)
  simp only [qOf, uR] at hz hc ⊢
  have hD1 := one_le_D p
  have hDn : D p = (numCallers p : ℤ) := rfl
  omega

end LP

end LeanTheory.Life
