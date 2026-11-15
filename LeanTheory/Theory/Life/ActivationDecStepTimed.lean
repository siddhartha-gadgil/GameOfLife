/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecRun
public import LeanTheory.Theory.Life.ActivationDecStation
public import LeanTheory.Theory.Life.ActivationDecTimed
public import LeanTheory.Theory.Life.ActivationIncThread

/-!
# The `decJz` step: route laws with corner windows and the times of the activation

Research note `N-22`, the `decJz` activation of `decJz r z` at instruction `i` (caller
`j = callerIdx p r i`, shift `sh = decShift p i r`). For every well-formed program:

* **route laws with corner windows** (`RouteTimedX`, the satisfiable form of the route conditions)
  for the control `C` and the tokens `KNZ`, `KZ` from the end of the body (template time `4260`:
  `decC_timedX`, `decKNZ_timedX`, `decKZ_timedX`, with `ztokCorners_timedX`), and for the answers
  from their dispatch at station `j` (`nzAnsCorners_timedX`, `zAnsCorners_timedX`,
  `decAnsN_timedX`, `decAnsZ_timedX`);
* **token ordering** (`decC_end`, `decKNZ_end`, `decKZ_end`): each glider leaves the window of its
  last corner before it reaches its destination (the DEC chain, the station of caller `j`);
* **the answer links** (`decAnsN_plan`, `decAnsZ_plan`): lines, route law, arrival on the side line
  of the entry copy at offset `4` or `5`, end of the route before the arrival;
* **the times of the activation** (`decTA`, `decTS`, `decDispN`, `decDispZ`, `decT0N`, `decT0Z`,
  `decEndN`, `decEndZ` with `decTS_facts`, `decN_times`, `decZ_times`): the register run starts at
  `decTS = sh - 300 ≡ 0 (mod 30)`, and the activation ends (`≡ 0 (mod 30)`) after everything it
  started in the module has finished.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- **The control `C` meets its corners in order with corner windows** from the end of the body
(template time `4260`), for every program. -/
theorem decC_timedX (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    RouteTimedX (unitWL p i decRWL) (decCornC p i r) 4260 := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  obtain ⟨h1, h2, h3'⟩ := unitWL_dec_lane p i 127 1221
  have hp := decChan_parity p i r (callerIdx p r i)
  have hR : decR = 127 := rfl
  have hu := unitD_uv p i
  have hVT := VT_mod p
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hH := hairC_le p hq (A p i + decR)
  have hcl := leftChan_in_extent p (idx := 2 * (callerIdx p r i))
    (v := decPortV p (2 * (callerIdx p r i))) ⟨by omega, by omega⟩
  have hsl := slabR_ge p
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  refine downCorners_timedX p _ _ _ _ _ _ r _ h1 h2 h3'
    (by unfold hairC; have := fixp_parity (HI p + 90 - 2 * eCtot (qOf p ↑(callerIdx p r i)))
          ((A p ↑i + decR) % 2); omega) hp.1 (by have := U_even p r; omega) 4260 ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift, trackOut, track, VU] at hu ⊢; omega
  · omega
  · unfold decChan; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, decPortV, modTop, instrBand] at h3 hb ⊢; omega

/-- **The token `KNZ` meets its corners in order with corner windows** from the end of the body. -/
theorem decKNZ_timedX (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    RouteTimedX (unitWL p i decLWL) (decCornN p i r) 4260 := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  obtain ⟨h1, h2, h3'⟩ := unitWL_dec_lane p i (-155) 2665
  have hp := nzTokChan_parity p i r (callerIdx p r i)
  have hR : decR = 127 := rfl
  have hL : decL = -155 := rfl
  have hu := unitD_uv p i
  have hVT := VT_mod p
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hH := hairC_le p hq (A p i + decR)
  have hK := hairKNZ_le p hq (A p i + decR) (A p i + decL)
  have hcl := leftChan_in_extent p (idx := 2 * D p + 1 + 2 * (callerIdx p r i))
    (v := nzTokPortV (callerIdx p r i)) ⟨by omega, by omega⟩
  have hsl := slabR_ge p
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  refine downCorners_timedX p _ _ _ _ _ _ r _ h1 h2 h3'
    (by unfold hairKNZ; have := fixp_parity (hairC p (qOf p ↑(callerIdx p r i)) (A p ↑i + decR)
          - 62 - 2 * eN (qOf p ↑(callerIdx p r i))) ((A p ↑i + decL) % 2); omega)
    hp.1 (by have := U_even p r; omega) 4260 ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift, trackOut, track, VU] at hu ⊢; omega
  · omega
  · unfold nzTokChan; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, nzTokPortV, modTop, instrBand] at h3 hb ⊢; omega


/-- **The route law with corner windows for the Z token link** (`ztokCorners_timed` with the first
corner `20` generations later). -/
theorem ztokCorners_timedX (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0)
    (hd : (U p r + zTokChan p j - c) % 2 = 0) (T : ℤ)
    (h0 : T + 20 ≤ g.tau + 2 * (c + trackOut p b 2 c) - 10) (hcH : H + 40 ≤ c)
    (hdH : H + 40 ≤ U p r + zTokChan p j)
    (hOB : trackOut p b 2 c + 40 ≤ trackBack p b 2 c)
    (hBW : trackBack p b 2 c + 40 ≤ zTokDepth p j)
    (hSt : U p r + zTokStation j + 40 ≤ U p r + zTokChan p j) :
    RouteTimedX g (ztokCorners p b c H r j) T := by
  have ho := trackOut_par p b 2 c
  have hb := trackBack_par p b 2 c
  have hU := U_even p r
  obtain ⟨-, h2, h3⟩ := zTokChan_parity p 0 r j
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl h0
  subst hdx hdy hl
  simp only [ztokCorners, bandCorners, List.cons_append, List.nil_append, RouteTimedX,
    reflect, meetT, delayS, WL.shift, rfIn, rfOut, rfX, rfY, rfCU, rfCV, zTokStation] at *
  generalize zTokChan p j = cz at *
  generalize zTokDepth p j = wd at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

/-- **The token `KZ` meets its corners in order with corner windows** from the end of the body. -/
theorem decKZ_timedX (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    RouteTimedX (unitWL p i decDWL) (decCornZ p i r) 4260 := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  obtain ⟨h1, h2, h3'⟩ := unitWL_dec_lane p i 188 787
  have hUe := U_even p r
  have hu := unitD_uv p i
  have hVT := VT_mod p
  have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
  have hk := hairReg_le p (s := 2) (e := eKZ (qOf p (callerIdx p r i))) (c := A p i + decD)
    (by norm_num) (eKZ_spec hq).2.1
  have hz := zAnsDepth_eq p (callerIdx p r i)
  have hzc := fixp_bounds (uR p + 124 * qOf p (callerIdx p r i) + 62)
    (1 - zTokDepth p (callerIdx p r i) % 2)
  have hsl := le_max_left (238 : ℤ) (86 + 58 * P p)
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  refine ztokCorners_timedX p _ _ _ r _ h1 h2 h3' (by unfold hairKZ; exact hairReg_par _ _ _ _)
    (zTokChan_parity p i r _).1 4260 ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift, trackOut, track, VU] at hu ⊢; omega
  · unfold hairKZ decD at *; omega
  · unfold hairKZ zTokChan at *
    simp only [modLeft, slabR, U0, uR] at *; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, zTokDepth, modTop, instrBand] at h3 hb hz ⊢; omega
  · unfold zTokChan zTokStation; simp only [uR, qOf] at hzc ⊢; omega




/-- **The route law with corner windows for an NZ answer**: from the dispatched glider flying `SW`
on the NZ answer port line, every corner is met in order when every leg is at least `40` long and
the first corner is met at least `20` generations after the start. -/
theorem nzAnsCorners_timedX (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) {g : WL}
    (hdx : g.dx = -1) (hdy : g.dy = 1) (hl : g.lane = nzAnsPortV j)
    (hH : (H - (U p r + nzAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + nzAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) (T : ℤ)
    (h0 : T + 20 ≤ meetT g ⟨0, U p r + nzAnsChan p j, nzAnsPortV j, .left r (2 * D p + 2 + 2 * j)⟩)
    (hPO : trackOut p b 3 (U p r + nzAnsChan p j) + 40 ≤ nzAnsPortV j)
    (hcH : H + 40 ≤ U p r + nzAnsChan p j) (hdH : H + 40 ≤ destU p a t)
    (hOB : trackOut p b 3 (U p r + nzAnsChan p j) + 40 ≤ trackBack p b 3 (U p r + nzAnsChan p j))
    (hDB : destV p t + 40 ≤ trackBack p b 3 (U p r + nzAnsChan p j)) :
    RouteTimedX g (nzAnsCorners p b r j H a t) T := by
  have ho := trackOut_par p b 3 (U p r + nzAnsChan p j)
  have hb := trackBack_par p b 3 (U p r + nzAnsChan p j)
  have hU := U_even p r
  have hp := nzAnsChan_parity p j
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl
  subst hdx hdy hl
  simp only [nzAnsCorners, upCornersK, bandCorners, List.cons_append, List.nil_append, RouteTimedX,
    reflect, meetT, delayS, WL.shift, rfIn, rfOut, rfX, rfY, rfCU, rfCV, nzAnsPortV] at *
  generalize nzAnsChan p j = cA at *
  generalize trackOut p b 3 (U p r + cA) = vO at *
  generalize trackBack p b 3 (U p r + cA) = vB at *
  generalize destU p a t = cd at *
  generalize destV p t = vD at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

/-- **The route law with corner windows for a Z answer**: from the dispatched glider flying `SE` on
the Z station column, every corner is met in order when every leg is at least `40` long. -/
theorem zAnsCorners_timedX (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = U p r + zAnsStation j)
    (hH : (H - (U p r + zAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + zAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) (T : ℤ)
    (h0 : T + 20 ≤ meetT g ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩)
    (hSC : U p r + zAnsStation j + 40 ≤ U p r + zAnsChan p j)
    (hOD : trackOut p b 4 (U p r + zAnsChan p j) + 40 ≤ zAnsDepth p j)
    (hcH : H + 40 ≤ U p r + zAnsChan p j) (hdH : H + 40 ≤ destU p a t)
    (hOB : trackOut p b 4 (U p r + zAnsChan p j) + 40 ≤ trackBack p b 4 (U p r + zAnsChan p j))
    (hDB : destV p t + 40 ≤ trackBack p b 4 (U p r + zAnsChan p j)) :
    RouteTimedX g (zAnsCorners p b r j H a t) T := by
  have ho := trackOut_par p b 4 (U p r + zAnsChan p j)
  have hb := trackBack_par p b 4 (U p r + zAnsChan p j)
  have hU := U_even p r
  have hp := zAnsChan_parity p j
  obtain ⟨dx, dy, lane, tau⟩ := g
  simp only at hdx hdy hl
  subst hdx hdy hl
  simp only [zAnsCorners, upCornersK, bandCorners, List.cons_append, List.nil_append, RouteTimedX,
    reflect, meetT, delayS, WL.shift, rfIn, rfOut, rfX, rfY, rfCU, rfCV, zAnsStation] at *
  generalize zAnsChan p j = cA at *
  generalize trackOut p b 4 (U p r + cA) = vO at *
  generalize trackBack p b 4 (U p r + cA) = vB at *
  generalize destU p a t = cd at *
  generalize destV p t = vD at *
  generalize zAnsDepth p j = vd at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega


/-- A `decJz` instruction is not the last one of a well-formed program. -/
theorem succ_lt_of_dec {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hins : p[i]? = some (.decJz r z)) : i + 1 < p.length := by
  have hi : i < p.length := (List.getElem?_eq_some_iff.1 hins).1
  by_contra hc
  have he : i = p.length - 1 := by omega
  have hlast : p[p.length - 1]? = some .halt := by
    rw [← List.getLast?_eq_getElem?]
    exact hp.2
  rw [← he, hins] at hlast
  cases hlast

/-- The jump target of a `decJz` instruction of a well-formed program is an instruction. -/
theorem lt_of_dec {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hins : p[i]? = some (.decJz r z)) : z < p.length :=
  hp.1 r z (List.mem_of_getElem? hins)

/-- The entry copy of the NZ answer is a copy of the entry chain of unit `i + 1`. -/
theorem decTN_range {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) : 0 ≤ decTN p i r ∧ decTN p i r < 2 * P p := by
  have h1 := succ_lt_of_dec hp hi
  have h := copyIdx_range p (C0 := unitC0 p (i + 1)) (c := U p r + nzAnsChan p (callerIdx p r i))
    ⟨predIdx_nonneg _ _ _ _, predIdx_lt_P p (a := i + 1) (off := 0) hi (by simp [predContrib])
      (by omega)⟩
  exact ⟨h.1, h.2.1⟩

/-- The entry copy of the Z answer is a copy of the entry chain of unit `z`. -/
theorem decTZ_range {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) : 0 ≤ decTZ p i r z ∧ decTZ p i r z < 2 * P p := by
  have h1 := lt_of_dec hp hi
  have h := copyIdx_range p (C0 := unitC0 p z) (c := U p r + zAnsChan p (callerIdx p r i))
    ⟨predIdx_nonneg _ _ _ _, predIdx_lt_P p (a := z) (off := if i + 1 = z then 1 else 0) hi
      (by simp only [predContrib]; split_ifs <;> omega) (by omega)⟩
  exact ⟨h.1, h.2.1⟩

/-- **The NZ answer meets its corners in order with corner windows** from its dispatch at station
`j` (`sh + 11042 + 288 j`), for every well-formed program. -/
theorem decAnsN_timedX {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) :
    RouteTimedX (decGN p i r) (decMkN p i r (decEA p i r))
      (decShift p i r + 11042 + 288 * (callerIdx p r i : ℤ)) := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  obtain ⟨g1, g2, g3⟩ := decGN_dir p i r
  have ht := decTN_range hp hi
  have hpar := decTN_par p i r
  have hUe := U_even p r
  have hH := hairReg_le p (s := 3) (e := decEA p i r)
    (c := U p r + nzAnsChan p (callerIdx p r i)) (by norm_num) (solveE_bounds _ _ _).1
  have hA1 := A_nonneg p (a := ((i + 1 : ℕ) : ℤ)) (by omega)
  have hC := unitC0_cases p (i + 1)
  have hcl := leftChan_in_extent p (idx := 2 * D p + 2 + 2 * (callerIdx p r i))
    (v := nzAnsPortV (callerIdx p r i)) ⟨by omega, by omega⟩
  have hsl := slabR_ge p
  have hVT := VT_mod p
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  refine nzAnsCorners_timedX p _ r _ _ _ _ g1 g2 g3 (hairReg_par _ _ _ _) hpar.1 hpar.2 _
    ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [meetT, delayS, decGN, modWL, nzAnsWL, WL.shift, rfIn, rfX, rfCU, rfCV, modDX,
      nzAnsPortV, nzAnsChan, uL] at hcl ⊢
    omega
  · simp only [trackOut, track, nzAnsPortV, modTop, instrBand] at h3 hb ⊢; omega
  · unfold nzAnsChan at *; omega
  · simp only [destU, inCol] at ht ⊢; push_cast at hA1 ⊢; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [destV, sideV, trackBack, track, VU, modTop, instrBand] at h3 hb ht ⊢; omega

/-- **The Z answer meets its corners in order with corner windows** from its dispatch at station `j`
(`sh + 13062 + 288 j`), for every well-formed program. -/
theorem decAnsZ_timedX {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) :
    RouteTimedX (decGZ p i r) (decMkZ p i r z (decEB p i r z))
      (decShift p i r + 13062 + 288 * (callerIdx p r i : ℤ)) := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  obtain ⟨g1, g2, g3⟩ := decGZ_dir p i r
  have ht := decTZ_range hp hi
  have hpar := decTZ_par p i r z
  have hUe := U_even p r
  have hH := hairReg_le p (s := 4) (e := decEB p i r z)
    (c := U p r + zAnsChan p (callerIdx p r i)) (by norm_num) (solveE_bounds _ _ _).1
  have hA1 := A_nonneg p (a := ((z : ℕ) : ℤ)) (by omega)
  have hC := unitC0_cases p z
  have hz := zAnsDepth_eq p (callerIdx p r i)
  have hc := fixp_bounds (uR p + 124 * qOf p (callerIdx p r i))
    (1 - zAnsDepth p (callerIdx p r i) % 2)
  have hsl := slabR_ge p
  have hVT := VT_mod p
  have hib : 1 ≤ instrBand (i : ℤ) := by unfold instrBand; omega
  refine zAnsCorners_timedX p _ r _ _ _ _ g1 g2 g3 (hairReg_par _ _ _ _) hpar.1 hpar.2 _
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [meetT, delayS, decGZ, modWL, zAnsWL, WL.shift, rfIn, rfX, rfCU, rfCV, modDX,
      zAnsStation] at hz ⊢
    simp only [qOf] at hz
    omega
  · unfold zAnsChan zAnsStation at *; simp only [uR, qOf] at hc ⊢; omega
  · simp only [trackOut, track, modTop, instrBand] at h3 hb hz ⊢; simp only [qOf] at hz; omega
  · unfold zAnsChan at *; simp only [uR, qOf, modLeft] at hc hU2 hH ⊢; omega
  · simp only [destU, inCol] at ht ⊢; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [destV, sideV, trackBack, track, VU, modTop, instrBand] at h3 hb ht ⊢; omega


/-- **`C` leaves its last corner before it reaches the DEC chain**: the end of the route (with
corner windows) is before the arrival on the side input of DEC copy `2 j`. -/
theorem decC_end (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    (routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 : ℤ) + 20 ≤
      180 + 30 * decSlot p i r + (15 + 16 * (2 * D p - 1 - 2 * (callerIdx p r i : ℤ))) % 30 := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  have h := routeEndX_snoc _ ⟨4, U p r + decChan p (2 * (callerIdx p r i)),
    decPortV p (2 * (callerIdx p r i)), .left r (2 * (callerIdx p r i))⟩ (unitWL p i decRWL) 4260
    (decC_timedX p hi)
  change (routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 : ℤ) = (decGC p i r).tau - _ + _ - _
    at h
  rw [decC_window] at h
  have hcl := leftChan_in_extent p (idx := 2 * (callerIdx p r i))
    (v := decPortV p (2 * (callerIdx p r i))) ⟨by omega, by omega⟩
  have hUe := U_even p r
  have hs := sigma_cases (qOf p (callerIdx p r i))
  simp only [decWin, modWL, WL.shift, rfOut, rfX, rfCU, rfCV, decPortV, modDX, decChan,
    uL] at h hcl ⊢
  omega

/-- **The token `KNZ` leaves its last corner before its station**: the end of its route is before
the capture time `sh + 10350 + 288 j` at station `j`. -/
theorem decKNZ_end (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    (routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 : ℤ) + 90 ≤
      decShift p i r + 10350 + 288 * (callerIdx p r i : ℤ) := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  have h := routeEndX_snoc _ ⟨4, U p r + nzTokChan p (callerIdx p r i),
    nzTokPortV (callerIdx p r i), .left r (2 * D p + 1 + 2 * (callerIdx p r i))⟩
    (unitWL p i decLWL) 4260 (decKNZ_timedX p hi)
  change (routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 : ℤ) =
    (route (unitWL p i decLWL) (decCornN p i r)).2.tau - _ + _ - _ at h
  rw [decKNZ_target] at h
  have hcl := leftChan_in_extent p (idx := 2 * D p + 1 + 2 * (callerIdx p r i))
    (v := nzTokPortV (callerIdx p r i)) ⟨by omega, by omega⟩
  have hUe := U_even p r
  simp only [tokNZWL, modWL, WL.shift, rfOut, rfX, rfCU, rfCV, nzTokPortV, modDX, nzTokChan,
    uL] at h hcl ⊢
  omega

/-- **The token `KZ` leaves its last corner before its station**: the end of its route is before
the capture time `sh + 12390 + 288 j` at station `j`. -/
theorem decKZ_end (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    (routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 : ℤ) + 90 ≤
      decShift p i r + 12390 + 288 * (callerIdx p r i : ℤ) := by
  obtain ⟨hA, hU, hU2, hHI, hP, hD, hj, h3, hb⟩ := dec_layout_facts p hi
  have h := routeEndX_snoc (bandCorners p (instrBand i) 2 (A p i + decD)
      (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
      (U p r + zTokChan p (callerIdx p r i)) 3 2 ++
      [⟨3, U p r + zTokChan p (callerIdx p r i), zTokDepth p (callerIdx p r i),
        .right r (callerIdx p r i) 2⟩])
    ⟨0, U p r + zTokStation (callerIdx p r i), zTokDepth p (callerIdx p r i),
      .right r (callerIdx p r i) 3⟩ (unitWL p i decDWL) 4260 (by
        have := decKZ_timedX p hi
        simp only [decCornZ, ztokCorners, List.append_assoc, List.cons_append, List.nil_append]
          at this ⊢
        exact this)
  have e : decCornZ p i r = bandCorners p (instrBand i) 2 (A p i + decD)
      (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD))
      (U p r + zTokChan p (callerIdx p r i)) 3 2 ++
      [⟨3, U p r + zTokChan p (callerIdx p r i), zTokDepth p (callerIdx p r i),
        .right r (callerIdx p r i) 2⟩] ++
      [⟨0, U p r + zTokStation (callerIdx p r i), zTokDepth p (callerIdx p r i),
        .right r (callerIdx p r i) 3⟩] := by
    simp [decCornZ, ztokCorners]
  rw [← e, decKZ_target] at h
  have hz := zAnsDepth_eq p (callerIdx p r i)
  have hUe := U_even p r
  simp only [tokZWL, modWL, WL.shift, rfOut, rfX, rfCU, rfCV, zTokStation, modDX, zTokDepth,
    qOf] at h hz ⊢
  omega


/-- The end of a route (corner windows) whose last corner is the input corner of an entry copy. -/
theorem slab_endX (cs : List Corner) (u v : ℤ) (tag : CTag) (g : WL) (T : ℕ)
    (ht : RouteTimedX g (cs ++ [⟨1, u, v, tag⟩]) T) (hv : (u + v) % 2 = 1) :
    (routeEndX g (cs ++ [⟨1, u, v, tag⟩]) T : ℤ) =
      (route g (cs ++ [⟨1, u, v, tag⟩])).2.tau + 37 + 2 * (u + v + 9) - 20 := by
  rw [routeEndX_snoc cs _ g T ht]
  simp only [rfOut, rfX, rfCU, rfCV]
  omega

/-- **The facts of the NZ answer link**, dispatched at `Td = sh + 11042 + 288 j`: lines, route law
with corner windows, arrival on the side line of its entry copy at offset `4` or `5`, and the end
of the route before the arrival on the side input. -/
theorem decAnsN_plan {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (Td : ℕ)
    (hTd : (Td : ℤ) = decShift p i r + 11042 + 288 * (callerIdx p r i : ℤ)) :
    RouteLines (decGN p i r) (decMkN p i r (decEA p i r)) ∧
      RouteTimedX (decGN p i r) (decMkN p i r (decEA p i r)) Td ∧
      (offOf (route (decGN p i r) (decMkN p i r (decEA p i r))).2
          (destWin p (i + 1) (decTN p i r)) = 4 ∨
        offOf (route (decGN p i r) (decMkN p i r (decEA p i r))).2
          (destWin p (i + 1) (decTN p i r)) = 5) ∧
      (route (decGN p i r) (decMkN p i r (decEA p i r))).2 =
        (destWin p (i + 1) (((decTN p i r).toNat : ℕ) : ℤ)).shift 0 0
          (offOf (route (decGN p i r) (decMkN p i r (decEA p i r))).2
              (destWin p (i + 1) (decTN p i r)) +
            30 * slot (route (decGN p i r) (decMkN p i r (decEA p i r))).2
              (destWin p (i + 1) (decTN p i r))) ∧
      (routeEndX (decGN p i r) (decMkN p i r (decEA p i r)) Td : ℤ) + 20 ≤
        180 + 30 * slot (route (decGN p i r) (decMkN p i r (decEA p i r))).2
          (destWin p (i + 1) (decTN p i r)) + 16 * decTN p i r % 30 := by
  have ht := decTN_range hp hi
  have htN : (((decTN p i r).toNat : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  have htim : RouteTimedX (decGN p i r) (decMkN p i r (decEA p i r)) Td := by
    rw [hTd]; exact decAnsN_timedX hp hi
  obtain ⟨hoff, harr⟩ := decAnsN_arrival p i r
  have hpar := decTN_par p i r
  refine ⟨(decAnsN_lines p i r _).1, htim, hoff, by rw [htN]; exact harr, ?_⟩
  have e : decMkN p i r (decEA p i r) =
      (⟨0, U p r + nzAnsChan p (callerIdx p r i), nzAnsPortV (callerIdx p r i),
        .left r (2 * D p + 2 + 2 * (callerIdx p r i))⟩ ::
        bandCorners p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))
          (hairReg p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i)))
          (destU p (i + 1) (decTN p i r)) 5 6) ++
        [⟨1, destU p (i + 1) (decTN p i r), destV p (decTN p i r), .slab (i + 1) (decTN p i r)⟩]
      := by simp [decMkN, nzAnsCorners, upCornersK]
  have hend := slab_endX _ _ _ _ (decGN p i r) Td (e ▸ htim) hpar.2
  rw [← e] at hend
  have hsl := slot_spec (route (decGN p i r) (decMkN p i r (decEA p i r))).2
    (destWin p (i + 1) (decTN p i r))
  have hw : (destWin p (i + 1) (decTN p i r)).tau =
      1 + 140 * decTN p i r + 16 * decTN p i r % 30 - 4 * unitDX p (i + 1) := by
    simp only [destWin, unitWL, sideWL, WL.shift]; ring
  have hu := unitD_uv p (i + 1)
  have hC := unitC0_cases p (i + 1)
  generalize offOf (route (decGN p i r) (decMkN p i r (decEA p i r))).2
    (destWin p (i + 1) (decTN p i r)) = o at *
  generalize slot (route (decGN p i r) (decMkN p i r (decEA p i r))).2
    (destWin p (i + 1) (decTN p i r)) = k at *
  simp only [destU, destV, inCol, sideV] at hend
  omega

/-- **The facts of the Z answer link**, dispatched at `Td = sh + 13062 + 288 j`: lines, route law
with corner windows, arrival on the side line of its entry copy at offset `4` or `5`, and the end
of the route before the arrival on the side input. -/
theorem decAnsZ_plan {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (Td : ℕ)
    (hTd : (Td : ℤ) = decShift p i r + 13062 + 288 * (callerIdx p r i : ℤ)) :
    RouteLines (decGZ p i r) (decMkZ p i r z (decEB p i r z)) ∧
      RouteTimedX (decGZ p i r) (decMkZ p i r z (decEB p i r z)) Td ∧
      (offOf (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
          (destWin p z (decTZ p i r z)) = 4 ∨
        offOf (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
          (destWin p z (decTZ p i r z)) = 5) ∧
      (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2 =
        (destWin p z (((decTZ p i r z).toNat : ℕ) : ℤ)).shift 0 0
          (offOf (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
              (destWin p z (decTZ p i r z)) +
            30 * slot (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
              (destWin p z (decTZ p i r z))) ∧
      (routeEndX (decGZ p i r) (decMkZ p i r z (decEB p i r z)) Td : ℤ) + 20 ≤
        180 + 30 * slot (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
          (destWin p z (decTZ p i r z)) + 16 * decTZ p i r z % 30 := by
  have ht := decTZ_range hp hi
  have htN : (((decTZ p i r z).toNat : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  have htim : RouteTimedX (decGZ p i r) (decMkZ p i r z (decEB p i r z)) Td := by
    rw [hTd]; exact decAnsZ_timedX hp hi
  obtain ⟨hoff, harr⟩ := decAnsZ_arrival p i r z
  have hpar := decTZ_par p i r z
  refine ⟨(decAnsZ_lines p i r z _).1, htim, hoff, by rw [htN]; exact harr, ?_⟩
  have e : decMkZ p i r z (decEB p i r z) =
      (⟨4, U p r + zAnsStation (callerIdx p r i), zAnsDepth p (callerIdx p r i),
        .right r (callerIdx p r i) 0⟩ ::
        ⟨6, U p r + zAnsChan p (callerIdx p r i), zAnsDepth p (callerIdx p r i),
          .right r (callerIdx p r i) 1⟩ ::
        bandCorners p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))
          (hairReg p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i)))
          (destU p z (decTZ p i r z)) 5 6) ++
        [⟨1, destU p z (decTZ p i r z), destV p (decTZ p i r z), .slab z (decTZ p i r z)⟩]
      := by simp [decMkZ, zAnsCorners, upCornersK]
  have hend := slab_endX _ _ _ _ (decGZ p i r) Td (e ▸ htim) hpar.2
  rw [← e] at hend
  have hsl := slot_spec (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
    (destWin p z (decTZ p i r z))
  have hw : (destWin p z (decTZ p i r z)).tau =
      1 + 140 * decTZ p i r z + 16 * decTZ p i r z % 30 - 4 * unitDX p z := by
    simp only [destWin, unitWL, sideWL, WL.shift]; ring
  have hu := unitD_uv p z
  have hC := unitC0_cases p z
  generalize offOf (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
    (destWin p z (decTZ p i r z)) = o at *
  generalize slot (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2
    (destWin p z (decTZ p i r z)) = k at *
  simp only [destU, destV, inCol, sideV] at hend
  omega


/-- The DEC copy `m = 2 D - 1 - 2 j` (from the downstream end) receiving `C`. -/
def decM (p : Program) (i r : ℕ) : ℕ := 2 * numCallers p - 1 - 2 * callerIdx p r i

/-- The DEC copy as an integer. -/
theorem decM_cast (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    (decM p i r : ℤ) = 2 * D p - 1 - 2 * (callerIdx p r i : ℤ) := by
  have hj := callerIdx_lt_D p hi
  unfold decM D
  omega

/-- The time at which `C` reaches the side input of DEC copy `m`. -/
def decTA (p : Program) (i r : ℕ) : ℕ :=
  (180 + 30 * decSlot p i r + (15 + 16 * (decM p i r : ℤ)) % 30).toNat

/-- **The start of the register run**: `C'` at the run input, `decShift - 300`. -/
def decTS (p : Program) (i r : ℕ) : ℕ := decTA p i r + (134 + decM p i r * 254) + 1771

/-- The route of `C` ends between the end of the body and the arrival at the DEC chain. -/
theorem decTA_facts (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    4260 ≤ routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ∧
      routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 + 20 ≤ decTA p i r ∧
      (decTA p i r : ℤ) = 180 + 30 * decSlot p i r + (15 + 16 * (decM p i r : ℤ)) % 30 := by
  have h1 := le_routeEndX _ _ _ (decC_timedX p hi)
  have h2 := decC_end p hi
  rw [← decM_cast p hi] at h2
  have e : (decTA p i r : ℤ) = 180 + 30 * decSlot p i r + (15 + 16 * (decM p i r : ℤ)) % 30 :=
    Int.toNat_of_nonneg (by omega)
  refine ⟨h1, by omega, e⟩

/-- The start of the register run is `decShift - 300`, a multiple of `30`. -/
theorem decTS_facts (p : Program) {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    (decTS p i r : ℤ) = decShift p i r - 300 ∧ decTS p i r % 30 = 0 ∧ 4260 ≤ decTA p i r := by
  obtain ⟨h1, h2, h3⟩ := decTA_facts p hi
  have hd := dec_run_time p i r
  rw [← decM_cast p hi] at hd
  have e : (decTS p i r : ℤ) = decShift p i r - 300 := by
    simp only [decTS]; push_cast; omega
  refine ⟨e, by omega, by omega⟩

/-- The final world line of the NZ answer. -/
def decFinN (p : Program) (i r : ℕ) : WL := (route (decGN p i r) (decMkN p i r (decEA p i r))).2

/-- The final world line of the Z answer. -/
def decFinZ (p : Program) (i r z : ℕ) : WL :=
  (route (decGZ p i r) (decMkZ p i r z (decEB p i r z))).2

/-- The window slot of the NZ answer at its entry copy. -/
def decKN (p : Program) (i r : ℕ) : ℤ := slot (decFinN p i r) (destWin p (i + 1) (decTN p i r))

/-- The window slot of the Z answer at its entry copy. -/
def decKZ (p : Program) (i r z : ℕ) : ℤ := slot (decFinZ p i r z) (destWin p z (decTZ p i r z))

/-- The entry copy of the NZ answer, as a natural number. -/
def decTNn (p : Program) (i r : ℕ) : ℕ := (decTN p i r).toNat

/-- The entry copy of the Z answer, as a natural number. -/
def decTZn (p : Program) (i r z : ℕ) : ℕ := (decTZ p i r z).toNat

/-- **The dispatch of the NZ answer** at station `j` (`sh + 11042 + 288 j`). -/
def decDispN (p : Program) (i r : ℕ) : ℕ := decTS p i r + 11342 + 288 * callerIdx p r i

/-- **The dispatch of the Z answer** at station `j` (`sh + 13062 + 288 j`). -/
def decDispZ (p : Program) (i r : ℕ) : ℕ := decTS p i r + 13362 + 288 * callerIdx p r i

/-- The arrival of the NZ answer at the side input of its entry copy. -/
def decT0N (p : Program) (i r : ℕ) : ℕ := (180 + 30 * decKN p i r + 16 * decTN p i r % 30).toNat

/-- The arrival of the Z answer at the side input of its entry copy. -/
def decT0Z (p : Program) (i r z : ℕ) : ℕ :=
  (180 + 30 * decKZ p i r z + 16 * decTZ p i r z % 30).toNat

/-- **The end of an NZ activation**: the control at the entrance of unit `i + 1`. -/
def decEndN (p : Program) (i r : ℕ) : ℕ := decT0N p i r + (134 + decTNn p i r * 254) + 166

/-- **The end of a Z activation**: the control at the entrance of unit `z`. -/
def decEndZ (p : Program) (i r z : ℕ) : ℕ := decT0Z p i r z + (134 + decTZn p i r z * 254) + 166

/-- **The times of an NZ activation**: dispatch, end of the answer route before the arrival, the end
of the activation (a multiple of `30`), after the absorption of the unpaired `KZ` token. -/
theorem decN_times {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) :
    (decDispN p i r : ℤ) = decShift p i r + 11042 + 288 * (callerIdx p r i : ℤ) ∧
      routeEndX (decGN p i r) (decMkN p i r (decEA p i r)) (decDispN p i r) + 20 ≤ decT0N p i r ∧
      (decT0N p i r : ℤ) = 180 + 30 * decKN p i r + 16 * ((decTNn p i r : ℕ) : ℤ) % 30 ∧
      decEndN p i r % 30 = 0 ∧ decTS p i r + 12962 + 288 * callerIdx p r i ≤ decEndN p i r ∧
      decDispN p i r ≤ decT0N p i r := by
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have hD : (decDispN p i r : ℤ) = decShift p i r + 11042 + 288 * (callerIdx p r i : ℤ) := by
    simp only [decDispN]; push_cast; omega
  obtain ⟨-, htim, -, -, hend⟩ := decAnsN_plan hp hi _ hD
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  have hle := le_routeEndX _ _ _ htim
  have hT0 : (decT0N p i r : ℤ) = 180 + 30 * decKN p i r + 16 * decTN p i r % 30 :=
    Int.toNat_of_nonneg (by unfold decKN decFinN; omega)
  have hlate := decNZ_late p hi
  have hE : (decEndN p i r : ℤ) = ctrlTime (decKN p i r) (decTN p i r) := by
    simp only [decEndN, ctrlTime]; push_cast; rw [hT0, htN]; ring
  have hm := ctrlTime_mod (decKN p i r) (decTN p i r)
  refine ⟨hD, ?_, by rw [hT0, htN], by omega, ?_, by unfold decKN decFinN at hT0; omega⟩
  · unfold decKN decFinN at hT0; omega
  · unfold decKN decFinN at hE; omega

/-- **The times of a Z activation**: dispatch, end of the answer route before the arrival, the end
of the activation (a multiple of `30`), after the circuit's rest at the end of the Z restore. -/
theorem decZ_times {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) :
    (decDispZ p i r : ℤ) = decShift p i r + 13062 + 288 * (callerIdx p r i : ℤ) ∧
      routeEndX (decGZ p i r) (decMkZ p i r z (decEB p i r z)) (decDispZ p i r) + 20 ≤
        decT0Z p i r z ∧
      (decT0Z p i r z : ℤ) = 180 + 30 * decKZ p i r z + 16 * ((decTZn p i r z : ℕ) : ℤ) % 30 ∧
      decEndZ p i r z % 30 = 0 ∧ decTS p i r + 27540 ≤ decEndZ p i r z ∧
      decDispZ p i r ≤ decT0Z p i r z := by
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have hD : (decDispZ p i r : ℤ) = decShift p i r + 13062 + 288 * (callerIdx p r i : ℤ) := by
    simp only [decDispZ]; push_cast; omega
  obtain ⟨-, htim, -, -, hend⟩ := decAnsZ_plan hp hi _ hD
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  have hle := le_routeEndX _ _ _ htim
  have hT0 : (decT0Z p i r z : ℤ) = 180 + 30 * decKZ p i r z + 16 * decTZ p i r z % 30 :=
    Int.toNat_of_nonneg (by unfold decKZ decFinZ; omega)
  have hlate := decZ_late p hi
  have hE : (decEndZ p i r z : ℤ) = ctrlTime (decKZ p i r z) (decTZ p i r z) := by
    simp only [decEndZ, ctrlTime]; push_cast; rw [hT0, htN]; ring
  have hm := ctrlTime_mod (decKZ p i r z) (decTZ p i r z)
  refine ⟨hD, ?_, by rw [hT0, htN], by omega, ?_, by unfold decKZ decFinZ at hT0; omega⟩
  · unfold decKZ decFinZ at hT0; omega
  · unfold decKZ decFinZ at hE; omega

end LP

end LeanTheory.Life
