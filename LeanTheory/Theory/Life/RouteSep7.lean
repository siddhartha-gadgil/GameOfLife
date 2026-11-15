/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RouteSep6

/-!
# Separation of the links of a `decJz` instruction

The five routes of a `decJz r z` instruction `i` (caller `j` of register `r`, `decSpecs`): the
tokens KNZ (slot `0`) and KZ (slot `2`) and the control `C` (slot `1`) from the unit to module `r`,
the NZ answer (slot `3`) from module `r` to unit `i + 1` and the Z answer (slot `4`) from module
`r` to unit `z`. `decLinks_sep`: all five satisfy the corrected separation condition `RouteSepX`
(`RouteSep`) in the region of the machine, for every well-formed program and every delay
`d ≡ 0 (mod 30)`: the three links from the unit from template time `4260 + d` on (the end of the
body of the unit, `bodyDecRun_rest`), the NZ answer from the time it has passed its station
(`u ≤ U_r - 553`) and the Z answer from the time it has passed the Z stations (`v ≥ 710`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- **The lines of the KZ link**: a glider flying `SE` on the source column `c` meets every
corner of `ztokCorners` on its input line. -/
theorem ztokCorners_lines (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) {g : WL} (hdx : g.dx = 1)
    (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0)
    (hd : (U p r + zTokChan p j - c) % 2 = 0)
    (hv1 : (U p r + zTokChan p j + zTokDepth p j) % 2 = 1)
    (hv2 : (U p r + zTokStation j + zTokDepth p j) % 2 = 1) :
    RouteLines g (ztokCorners p b c H r j) := by
  have ho := trackOut_par p b 2 c
  have hb := trackBack_par p b 2 c
  set vO := trackOut p b 2 c
  set vB := trackBack p b 2 c
  set cd := U p r + zTokChan p j
  set wd := zTokDepth p j
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
  have p6 : (U p r + zTokStation j - rfCU 0 + wd - rfCV 0) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  have l6 : OnLine g5 ⟨0, U p r + zTokStation j, wd, .right r j 3⟩ :=
    onLine_of_through (by simp [x5, rfIn]) (by simp [y5, rfIn]) p6
      (by simp only [WL.Through, x5, y5] at t5 ⊢; linarith)
  exact ⟨l1, l2, l3, l4, l5, l6, trivial⟩

/-- **The routes of a `decJz` instruction**, with their parameters. -/
theorem decSpecs_form (p : Program) (i r z : ℕ) :
    ∃ sh eA eB : ℤ, 0 ≤ eA ∧ eA ≤ 14 ∧ 0 ≤ eB ∧ eB ≤ 14 ∧
      decSpecs p i r z =
        [(unitWL p i decLWL, downCorners p (instrBand i) 0 (A p i + decL)
            (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
            (U p r + nzTokChan p (callerIdx p r i)) (nzTokPortV (callerIdx p r i)) r
            (2 * D p + 1 + 2 * (callerIdx p r i))),
          (unitWL p i decRWL, downCorners p (instrBand i) 1 (A p i + decR)
            (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
            (U p r + decChan p (2 * (callerIdx p r i))) (decPortV p (2 * (callerIdx p r i))) r
            (2 * (callerIdx p r i))),
          (unitWL p i decDWL, ztokCorners p (instrBand i) (A p i + decD)
            (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD)) r (callerIdx p r i)),
          ((modWL p r (nzAnsWL (callerIdx p r i))).shift 0 0 sh,
            nzAnsCorners p (instrBand i) r (callerIdx p r i)
              (hairReg p 3 eA (U p r + nzAnsChan p (callerIdx p r i))) (i + 1)
              (copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0)
                (U p r + nzAnsChan p (callerIdx p r i)))),
          ((modWL p r (zAnsWL (callerIdx p r i))).shift 0 0 sh,
            zAnsCorners p (instrBand i) r (callerIdx p r i)
              (hairReg p 4 eB (U p r + zAnsChan p (callerIdx p r i))) z
              (copyIdx (unitC0 p z) (predIdx p z i (if i + 1 = z then 1 else 0))
                (U p r + zAnsChan p (callerIdx p r i))))] := by
  simp only [decSpecs]
  exact ⟨_, _, _, (solveE_bounds _ _ _).1, (solveE_bounds _ _ _).2,
    (solveE_bounds _ _ _).1, (solveE_bounds _ _ _).2, rfl⟩

/-- The pieces of the unit of a `decJz` instruction are far from the source legs of its three
links from template time `4260` on (columns `-155`, `127`, `188` of the unit, below
`v = V_U + 949`, `V_U + 1389`, `V_U + 1546`). -/
theorem decUnit_far {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) {s : PSpec}
    (hs : s ∈ unitSpecs p i) (v2 : ℤ) :
    FarRect s.bx (A p i + decL - 4) (A p i + decL + 4) (VU p + 949) v2 ∧
      FarRect s.bx (A p i + decR - 4) (A p i + decR + 4) (VU p + 1389) v2 ∧
      FarRect s.bx (A p i + decD - 4) (A p i + decD + 4) (VU p + 1546) v2 := by
  have hd := unitD_uv p i
  have hk : unitKind p i = .dec := by simp [unitKind, hi]
  unfold unitSpecs at hs
  rw [hk] at hs
  unfold FarRect
  simp only [decL, decR, decD]
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨t, ht, rfl⟩ := mem_chainSpecs hs
    rw [chain_bx]
    simp only
    omega
  · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs
    obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hg
    have hk'' := List.mem_range.1 hk'
    simp only [PSpec.bx_mk]
    interval_cases k <;>
      simp only [Base.piece, bodyDecPieces, bodyDecG0, bodyDecG1, bodyDecG2, bodyDecG3, bodyDecG4,
        bodyDecG5, bodyDecG6, bodyDecG7, List.getD_cons_zero, List.getD_cons_succ] <;> omega

/-- Check of the 29 corners of a `decJz` instruction against a leg excluding one corner. -/
syntax "dec_own1 " term : tactic

set_option hygiene false in
macro_rules
  | `(tactic| dec_own1 $h) => `(tactic| (
      intro c' hc' n1
      rw [$h:term] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl n1 | (refine corner_farRect ?_; (try simp only); omega)))

/-- Check of the 29 corners of a `decJz` instruction against a leg excluding two corners. -/
syntax "dec_own2 " term : tactic

set_option hygiene false in
macro_rules
  | `(tactic| dec_own2 $h) => `(tactic| (
      intro c' hc' n1 n2
      rw [$h:term] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl n1 | exact absurd rfl n2 |
          (refine corner_farRect ?_; (try simp only); omega)))

set_option maxHeartbeats 2000000 in
-- The proof checks the 29 corners of the instruction against 15 legs by `omega` in one
-- declaration (about 450 small goals).
/-- **The routes of every `decJz` instruction are separated**: for every well-formed program,
every `decJz r z` instruction `i` and every delay `d ≡ 0 (mod 30)`, the tokens KNZ, KZ and the
control `C` satisfy `RouteSepX` from every time `T ≥ 4260 + d`, the NZ answer from every time
after which it is at `u ≤ U_r - 553` (past its station) and the Z answer from every time after
which it is at `v ≥ 710` (past the Z stations), for the pieces of the machine, in the region of
the machine. -/
theorem decLinks_sep {p : Program} (hp : p.WellFormed) {i r z : ℕ}
    (hi : p[i]? = some (.decJz r z)) {d : ℤ} (hd : d % 30 = 0) {T : ℤ} :
    (4260 + d ≤ T → ∀ x ∈ (instrSpecs p i).take 3,
      RouteSepX (machPieces p) (machRegion p) (x.1.shift 0 0 d) x.2 T) ∧
    (∀ x ∈ ((instrSpecs p i).drop 3).take 1,
      (∀ t : ℤ, T ≤ t → (x.1.shift 0 0 d).cu t ≤ U p r - 553) →
      RouteSepX (machPieces p) (machRegion p) (x.1.shift 0 0 d) x.2 T) ∧
    (∀ x ∈ (instrSpecs p i).drop 4, (∀ t : ℤ, T ≤ t → 710 ≤ (x.1.shift 0 0 d).cv t) →
      RouteSepX (machPieces p) (machRegion p) (x.1.shift 0 0 d) x.2 T) := by
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨sh, eA, eB, hea1, hea2, heb1, heb2, heq⟩ := decSpecs_form p i r z
  have hspec : instrSpecs p i = decSpecs p i r z := by simp [instrSpecs, hi]
  -- names
  set j : ℤ := (callerIdx p r i : ℤ) with hjdef
  set q := qOf p j with hqdef
  set tN := copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (U p r + nzAnsChan p j) with htN
  set tZ := copyIdx (unitC0 p z) (predIdx p z i (if i + 1 = z then 1 else 0))
    (U p r + zAnsChan p j) with htZ
  have hI : instrCorners p i = specCorners (decSpecs p i r z) := by
    simp [instrCorners, hspec]
  rw [heq] at hI
  simp only [specCorners, List.flatMap_cons, List.flatMap_nil, List.append_nil, downCorners,
    ztokCorners, nzAnsCorners, zAnsCorners, upCornersK, bandCorners, List.cons_append,
    List.nil_append] at hI
  -- facts of the program
  have hi1 := succ_lt_of_wf hp hi (by simp)
  have hz := jump_lt_of_wf hp hi
  have hrR := reg_lt_R p hi
  simp only [regBound] at hrR
  have hR : (r : ℤ) < R p := by unfold R; omega
  have hjD := callerIdx_lt_D p hi
  have hDe : D p = (numCallers p : ℤ) := rfl
  have hj : 0 ≤ j ∧ j < D p := ⟨by omega, by omega⟩
  have hq : q = D p - 1 - j := rfl
  have hq0 : 0 ≤ q := by omega
  have hoff1 : 0 < predContrib p.length (i + 1) i (.decJz r z) := by simp [predContrib]
  have hoff2 : (if i + 1 = z then 1 else 0) < predContrib p.length z i (.decJz r z) := by
    simp [predContrib]
  have hp1 := predIdx_lt_P p hi hoff1 (by omega)
  have hp2 := predIdx_lt_P p hi hoff2 (by omega)
  have ht1 := copyIdx_range p (C0 := unitC0 p (i + 1)) (c := U p r + nzAnsChan p j)
    ⟨predIdx_nonneg p _ _ _, hp1⟩
  have ht2 := copyIdx_range p (C0 := unitC0 p z) (c := U p r + zAnsChan p j)
    ⟨predIdx_nonneg p _ _ _, hp2⟩
  rw [← htN] at ht1
  rw [← htZ] at ht2
  have hownN : Owns p (instrBand i) (.slab (i + 1 : ℕ) tN) :=
    owns_of_tagOf ⟨_, 0, _, rfl, hi, hoff1, ht1.2.2.1, ht1.2.2.2⟩
  have hownZ : Owns p (instrBand i) (.slab z tZ) :=
    owns_of_tagOf ⟨_, _, _, rfl, hi, hoff2, ht2.2.2.1, ht2.2.2.2⟩
  have hownL : ∀ idx : ℤ, (idx = 2 * j ∨ idx = 2 * D p + 1 + 2 * j ∨
      idx = 2 * D p + 2 + 2 * j) → Owns p (instrBand i) (.left r idx) :=
    fun idx h => owns_of_tagOf ⟨z, r, rfl, hi, h⟩
  have hownR : Owns p (instrBand i) (.right r j 0) := owns_of_tagOf ⟨z, r, rfl, hi, rfl⟩
  have htNZ : i + 1 = z → tN ≠ tZ := by
    intro h e
    have h' : predIdx p z i (if i + 1 = z then 1 else 0) = predIdx p (i + 1) i 0 + 1 := by
      subst h; simp [predIdx]
    have := copyBeta_spec (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (U p r + nzAnsChan p j)
    have := copyBeta_spec (unitC0 p z) (predIdx p z i (if i + 1 = z then 1 else 0))
      (U p r + zAnsChan p j)
    rw [← htN] at *
    rw [← htZ] at *
    omega
  -- parities
  have hpN : (destU p (i + 1) tN - (U p r + nzAnsChan p j)) % 2 = 0 ∧
      (destU p (i + 1) tN + destV p tN) % 2 = 1 := by
    have := (copyBeta_spec (unitC0 p (i + 1)) (predIdx p (i + 1) i 0)
      (U p r + nzAnsChan p j)).2.2
    rw [← htN] at this
    have := A_even p (i + 1 : ℕ)
    have := VU_even p
    have hodd : unitC0 p (i + 1) % 2 = 1 := by
      rcases unitC0_cases p (i + 1) with h | h | h <;> rw [h] <;> norm_num
    unfold destU destV inCol sideV at *
    constructor <;> omega
  have hpZ : (destU p z tZ - (U p r + zAnsChan p j)) % 2 = 0 ∧
      (destU p z tZ + destV p tZ) % 2 = 1 := by
    have := (copyBeta_spec (unitC0 p z) (predIdx p z i (if i + 1 = z then 1 else 0))
      (U p r + zAnsChan p j)).2.2
    rw [← htZ] at this
    have := A_even p z
    have := VU_even p
    have hodd : unitC0 p z % 2 = 1 := by
      rcases unitC0_cases p z with h | h | h <;> rw [h] <;> norm_num
    unfold destU destV inCol sideV at *
    constructor <;> omega
  have hpKNZ := nzTokChan_parity p i r j
  have hpC := decChan_parity p i r j
  have hpKZ := zTokChan_parity p i r j
  have hUe := U_even p r
  have hvKNZ : (U p r + nzTokChan p j + nzTokPortV j) % 2 = 1 := by
    clear * - hpKNZ hUe; omega
  have hvC : (U p r + decChan p (2 * j) + decPortV p (2 * j)) % 2 = 1 := by
    clear * - hpC hUe; omega
  have hvKZ1 : (U p r + zTokChan p j + zTokDepth p j) % 2 = 1 := by
    clear * - hpKZ hUe; omega
  have hvKZ2 : (U p r + zTokStation j + zTokDepth p j) % 2 = 1 := by
    clear * - hpKZ hUe; omega
  have hHKNZ : (hairKNZ p q (A p i + decR) (A p i + decL) - (A p i + decL)) % 2 = 0 := by
    have := fixp_parity (hairC p q (A p i + decR) - 62 - 2 * eN q) ((A p i + decL) % 2)
    unfold hairKNZ; clear * - this; omega
  have hHC : (hairC p q (A p i + decR) - (A p i + decR)) % 2 = 0 := by
    have := fixp_parity (HI p + 90 - 2 * eCtot q) ((A p i + decR) % 2)
    unfold hairC; clear * - this; omega
  have hHKZ : (hairKZ p q (A p i + decD) - (A p i + decD)) % 2 = 0 := hairReg_par p 2 _ _
  have hH3 := hairReg_par p 3 eA (U p r + nzAnsChan p j)
  have hH4p := hairReg_par p 4 eB (U p r + zAnsChan p j)
  have hgN : ((modWL p r (nzAnsWL j)).shift 0 0 sh).dx = -1 ∧
      ((modWL p r (nzAnsWL j)).shift 0 0 sh).dy = 1 ∧
      ((modWL p r (nzAnsWL j)).shift 0 0 sh).lane = nzAnsPortV j := by
    refine ⟨rfl, rfl, ?_⟩
    have := modD_uv p r
    simp only [modWL, nzAnsWL, WL.shift, nzAnsPortV]
    omega
  have hgZ : ((modWL p r (zAnsWL j)).shift 0 0 sh).dx = 1 ∧
      ((modWL p r (zAnsWL j)).shift 0 0 sh).dy = 1 ∧
      ((modWL p r (zAnsWL j)).shift 0 0 sh).lane = U p r + zAnsStation j := by
    refine ⟨rfl, rfl, ?_⟩
    have := modD_uv p r
    simp only [modWL, zAnsWL, WL.shift, zAnsStation]
    omega
  clear_value j q tN tZ
  clear htN htZ hp1 hp2 hoff1 hoff2
  -- the parity facts are passed as arguments only; the context of the checks has none
  have hpar : ((U p r + nzTokChan p j - (A p i + decL)) % 2 = 0 ∧
      (U p r + nzTokChan p j + nzTokPortV j) % 2 = 1 ∧
      (hairKNZ p q (A p i + decR) (A p i + decL) - (A p i + decL)) % 2 = 0) ∧
    ((U p r + decChan p (2 * j) - (A p i + decR)) % 2 = 0 ∧
      (U p r + decChan p (2 * j) + decPortV p (2 * j)) % 2 = 1 ∧
      (hairC p q (A p i + decR) - (A p i + decR)) % 2 = 0) ∧
    ((U p r + zTokChan p j - (A p i + decD)) % 2 = 0 ∧
      (U p r + zTokChan p j + zTokDepth p j) % 2 = 1 ∧
      (U p r + zTokStation j + zTokDepth p j) % 2 = 1 ∧
      (hairKZ p q (A p i + decD) - (A p i + decD)) % 2 = 0) ∧
    ((destU p (i + 1) tN - (U p r + nzAnsChan p j)) % 2 = 0 ∧
      (destU p (i + 1) tN + destV p tN) % 2 = 1 ∧
      (hairReg p 3 eA (U p r + nzAnsChan p j) - (U p r + nzAnsChan p j)) % 2 = 0) ∧
    ((destU p z tZ - (U p r + zAnsChan p j)) % 2 = 0 ∧
      (destU p z tZ + destV p tZ) % 2 = 1 ∧
      (hairReg p 4 eB (U p r + zAnsChan p j) - (U p r + zAnsChan p j)) % 2 = 0) :=
    ⟨⟨hpKNZ.1, hvKNZ, hHKNZ⟩, ⟨hpC.1, hvC, hHC⟩, ⟨hpKZ.1, hvKZ1, hvKZ2, hHKZ⟩,
      ⟨hpN.1, hpN.2, hH3⟩, ⟨hpZ.1, hpZ.2, hH4p⟩⟩
  clear hpKNZ hpC hpKZ hUe hvKNZ hvC hvKZ1 hvKZ2 hHKNZ hHC hHKZ hH3 hH4p hpN hpZ
  have hx : ∀ x ∈ decSpecs p i r z, x ∈ instrSpecs p i := fun x hx => by rwa [hspec]
  rw [heq] at hx
  -- the numeric facts of the corners
  have hf := layout_facts p
  have hRs := slabR_ge p
  have hb : instrBand (i : ℤ) = 1 + i := rfl
  have hiN : (i : ℤ) < N p := by unfold N; exact_mod_cast hlt
  have hA0 := A_nonneg p (a := i) (by omega)
  have hAz0 := A_nonneg p (a := z) (by omega)
  have hA1 : A p (i + 1 : ℕ) = A p i + PU p := by push_cast; exact A_succ p i
  have hAz : (z < i ∧ A p z + PU p ≤ A p i) ∨ (z = i ∧ A p z = A p i ∧ unitC0 p z = -237) ∨
      (z = i + 1 ∧ A p z = A p i + PU p) ∨ (i + 1 < z ∧ A p i + 2 * PU p ≤ A p z) := by
    rcases lt_trichotomy z i with h | rfl | h
    · exact Or.inl ⟨h, A_add_le p (by exact_mod_cast h)⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, by rw [unitC0_dec hi]; rfl⟩)
    · rcases Nat.lt_or_ge (i + 1) z with h' | h'
      · have := A_add_le p (a := (i + 1 : ℕ)) (a' := z) (by exact_mod_cast h')
        exact Or.inr (Or.inr (Or.inr ⟨h', by omega⟩))
      · have : z = i + 1 := by omega
        subst this
        exact Or.inr (Or.inr (Or.inl ⟨rfl, hA1⟩))
  have htNZ' : z ≠ i + 1 ∨ (tN ≠ tZ ∧ unitC0 p z = unitC0 p (i + 1)) := by
    by_cases h : z = i + 1
    · exact Or.inr ⟨htNZ h.symm, by rw [h]⟩
    · exact Or.inl h
  clear htNZ
  have hgi := unit_module_gap p (a := i) (r := r) ⟨by omega, by omega⟩ (by omega)
  have hgi1 := unit_module_gap p (a := (i + 1 : ℕ)) (r := r) ⟨by omega, by push_cast; omega⟩
    (by omega)
  have hgz := unit_module_gap p (a := z) (r := r) ⟨by omega, by unfold N at *; omega⟩
    (by omega)
  have hU0 := (U_ge p (r := r) (by omega)).1
  have hsep := sep09_decJz p (q := q) (cN := A p i + decL) (cC := A p i + decR)
    (cZ := A p i + decD) (cA := U p r + nzAnsChan p j) (cB := U p r + zAnsChan p j) hq0
    ⟨hea1, hea2⟩ ⟨heb1, heb2⟩
  have heN := (eN_spec hq0).2
  have hH4 := hairReg_le p (s := 4) (e := eB) (c := U p r + zAnsChan p j) (by norm_num) heb1
  have hHC : hairC p q (A p i + decR) ≤ HI p + 90 := by
    have := fixp_bounds (HI p + 90 - 2 * eCtot q) ((A p i + decR) % 2)
    have hx := xC_spec hq0
    have := eC_bounds q
    have := sigma_bounds q
    unfold hairC eCtot at *; omega
  have hcN := fixp_bounds (uL - 62 * (2 * D p + 1 + 2 * j)) (1 - nzTokPortV j % 2)
  have hcC := fixp_bounds (uL - 62 * (2 * j)) (1 - decPortV p (2 * j) % 2)
  have hcA := fixp_bounds (uL - 62 * (2 * D p + 2 + 2 * j)) (1 - nzAnsPortV j % 2)
  have hcZ := fixp_bounds (uR p + 124 * qOf p j + 62) (1 - zTokDepth p j % 2)
  have hcB := fixp_bounds (uR p + 124 * qOf p j) (1 - zAnsDepth p j % 2)
  have hvd := zAnsDepth_eq p j
  have hwd : zTokDepth p j = zAnsDepth p j + 61 := rfl
  have hchN : nzTokChan p j = fixp (uL - 62 * (2 * D p + 1 + 2 * j)) (1 - nzTokPortV j % 2) := rfl
  have hchC : decChan p (2 * j) = fixp (uL - 62 * (2 * j)) (1 - decPortV p (2 * j) % 2) := rfl
  have hchA : nzAnsChan p j = fixp (uL - 62 * (2 * D p + 2 + 2 * j)) (1 - nzAnsPortV j % 2) :=
    rfl
  have hchZ : zTokChan p j = fixp (uR p + 124 * qOf p j + 62) (1 - zTokDepth p j % 2) := rfl
  have hchB : zAnsChan p j = fixp (uR p + 124 * qOf p j) (1 - zAnsDepth p j % 2) := rfl
  rw [← hchN] at hcN
  rw [← hchC] at hcC
  rw [← hchA] at hcA
  rw [← hchZ] at hcZ
  rw [← hchB] at hcB
  clear hchN hchC hchA hchZ hchB
  have huL : uL = -793 := rfl
  have huR : uR p = 1410 + 144 * D p := rfl
  have hpN : nzTokPortV j = 1256 + 144 * j := rfl
  have hpC : decPortV p (2 * j) = -3351 - 99 * (2 * D p - 1 - 2 * j) := rfl
  have hpA : nzAnsPortV j = 1325 + 144 * j := rfl
  have hsZ : zTokStation j = 1230 + 144 * j := rfl
  have hsA : zAnsStation j = 1301 + 144 * j := rfl
  have hL : decL = -155 := rfl
  have hRc : decR = 127 := rfl
  have hDc : decD = 188 := rfl
  have hml : modLeft p = -823 - 248 * D p := rfl
  have hdN : destU p (i + 1) tN = A p (i + 1 : ℕ) + unitC0 p (i + 1) - 61 * tN := by
    unfold destU inCol; ring
  have hdZ : destU p z tZ = A p z + unitC0 p z - 61 * tZ := by unfold destU inCol; ring
  have hvN : destV p tN = VU p + 76 - 99 * tN := by unfold destV sideV; ring
  have hvZ : destV p tZ = VU p + 76 - 99 * tZ := by unfold destV sideV; ring
  have hc0N : -237 ≤ unitC0 p (i + 1) ∧ unitC0 p (i + 1) ≤ -67 := by
    rcases unitC0_cases p (i + 1) with h | h | h <;> rw [h] <;> norm_num
  have hc0Z : -237 ≤ unitC0 p z ∧ unitC0 p z ≤ -67 := by
    rcases unitC0_cases p z with h | h | h <;> rw [h] <;> norm_num
  have hci := unitC0_dec hi
  have hT0 := tracks_range p (instrBand i) 0 (A p i + decL)
  have hT1 := tracks_range p (instrBand i) 1 (A p i + decR)
  have hT2 := tracks_range p (instrBand i) 2 (A p i + decD)
  have hT3 := tracks_range p (instrBand i) 3 (U p r + nzAnsChan p j)
  have hT4 := tracks_range p (instrBand i) 4 (U p r + zAnsChan p j)
  have hnh : ∀ x : ℕ, p[x]? = some .halt → x ≠ i := by
    intro x hx' h; subst h; rw [hi] at hx'; simp at hx'
  have hsplit := ownSplit_instr hp hlt
  refine ⟨?_, ?_, ?_⟩
  · intro hT x hxm
    simp only [hspec, heq, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
      or_false] at hxm
    rcases hxm with rfl | rfl | rfl
    · -- KNZ
      have hxm := hx _ List.mem_cons_self
      refine unitDownLink_sep hp hsplit (a := i) (w := decL) (τ := 2665) (vS := VU p + 949) hb
        (by clear hpar hd; omega) (instrRoute_corner hlt hxm) (instrRoute_mem hlt hxm)
        (by norm_num) (by rw [hci]; simp [C0dec, decL]) hnh hpar.1.2.2 hpar.1.1 hpar.1.2.1 hR
        (by clear hpar hd; omega) (by clear hpar hd; rw [huL] at hcN; omega)
        (hownL _ (Or.inr (Or.inl rfl))) ?_ ?_ ?_ (fun s' hs' => (decUnit_far hi hs' _).1) hd ?_
      · clear hpar hd; dec_own1 hI
      · clear hpar hd; dec_own2 hI
      · clear hpar hd; dec_own2 hI
      · clear hpar
        intro t' ht'
        have := (unitWL_center p i decL 2665 d t').2
        omega
    · -- C
      have hxm := hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
      refine unitDownLink_sep hp hsplit (a := i) (w := decR) (τ := 1221) (vS := VU p + 1389) hb
        (by clear hpar hd; omega) (instrRoute_corner hlt hxm) (instrRoute_mem hlt hxm)
        (by norm_num) (by rw [hci]; simp [C0dec, decR]) hnh hpar.2.1.2.2 hpar.2.1.1
        hpar.2.1.2.1 hR (by clear hpar hd; omega) (by clear hpar hd; rw [huL] at hcC; omega)
        (hownL _ (Or.inl rfl)) ?_ ?_ ?_ (fun s' hs' => (decUnit_far hi hs' _).2.1) hd ?_
      · clear hpar hd; dec_own1 hI
      · clear hpar hd; dec_own2 hI
      · clear hpar hd; dec_own2 hI
      · clear hpar
        intro t' ht'
        have := (unitWL_center p i decR 1221 d t').2
        omega
    · -- KZ
      have hxm := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hu := unitD_uv p i
      have hpz := hpar.2.2.1
      have hlines := ztokCorners_lines p (instrBand i) (A p i + decD)
        (hairKZ p q (A p i + decD)) r j (g := unitWL p i ⟨1, 1, decD, 787⟩) rfl rfl
        (by simp only [unitWL, WL.shift]; clear hpar hd; omega) hpz.2.2.2 hpz.1 hpz.2.1 hpz.2.2.1
      have hcm := instrRoute_corner hlt hxm
      have hpc := ztokCorners_par (p := p) (b := instrBand i) (r := r) (j := j) hpz.2.2.2 hpz.1
        hpz.2.1 hpz.2.2.1
      have hok : ∀ x ∈ ztokCorners p (instrBand i) (A p i + decD) (hairKZ p q (A p i + decD)) r j,
          CornerOK p x := fun x hx' => ⟨hcm x hx', ztokCorners_k x hx', hpc x hx'⟩
      have hchain := ztok_chain hp hsplit (by clear hpar hd; omega) hR hj hownR hok
        (by clear hpar hd hlines hpz hpc hok; dec_own2 hI)
        (by clear hpar hd hlines hpz hpc hok; dec_own2 hI)
      clear hpz hpc
      refine unitLink_sep hp hsplit (a := i) (w := decD) (τ := 787) (vS := VU p + 1546) hb
        (by clear hpar hd; omega) (by norm_num) hlines hchain (instrRoute_mem hlt hxm)
        (by rw [hci]; simp [C0dec, decD]) hnh ?_ (fun s' hs' => (decUnit_far hi hs' _).2.2) hd ?_
      · clear hpar hd hlines hchain hok; dec_own1 hI
      · clear hpar hlines hchain hok
        intro t' ht'
        have := (unitWL_center p i decD 787 d t').2
        omega
  · intro x hxm hT
    simp only [hspec, heq, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hxm
    subst hxm
    have hxm := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
    refine nzAnsLink_sep hp hlt hxm hgN hR hj hpar.2.2.2.1.2.2 hpar.2.2.2.1.1 hpar.2.2.2.1.2.1
      (by clear hpar hd; unfold N R at *; omega) ⟨ht1.1, ht1.2.1⟩ hownN
      (hownL _ (Or.inr (Or.inr rfl))) ?_ ?_ ?_ hd hT
    · clear hpar hd hT hxm; dec_own2 hI
    · clear hpar hd hT hxm; dec_own2 hI
    · clear hpar hd hT hxm; dec_own2 hI
  · intro x hxm hT
    simp only [hspec, heq, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil,
      or_false] at hxm
    subst hxm
    have hxm := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    refine zAnsLink_sep hp hlt hxm hgZ hR hj hpar.2.2.2.2.2.2 hpar.2.2.2.2.1 hpar.2.2.2.2.2.1
      (by clear hpar hd; unfold N R at *; omega) ⟨ht2.1, ht2.2.1⟩ hownZ hownR ?_ ?_ ?_ hd hT
    · clear hpar hd hT hxm; dec_own2 hI
    · clear hpar hd hT hxm; dec_own2 hI
    · clear hpar hd hT hxm; dec_own2 hI

end LP

end LeanTheory.Life
