/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RouteSep4

/-!
# Separation of the links of an `inc` instruction and of the merge links

The two routes of an `inc r` instruction `i` (`incSpecs`): the continue (slot `0`, from the
output column `A_i + 68` of the unit to an entry copy of unit `i + 1`) and the INC link (slot `1`,
from `A_i + 157` to an entry copy of the merge unit `N + r`). `incLinks_sep`: both satisfy the
corrected separation condition `RouteSepX` (`RouteSep`) in the region of the machine, for every
well-formed program and every delay `d ≡ 0 (mod 30)`, from template time `2010 + d` on (the end
of the body of the unit, `bodyInc_wl`). `mergeLink_sep`: the merge link of every register with an
`inc` (from the output column `A_{N+r} + 14` of the merge unit to the INC port of module `r`), from
template time `917 + d` on (below the entry chain of the merge unit).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- **The routes of an `inc` instruction**, with their hairpin parameters. -/
theorem incSpecs_form (p : Program) (i r : ℕ) :
    ∃ G ec el : ℤ, 0 ≤ G ∧ 0 ≤ ec ∧ ec ≤ 14 ∧ 0 ≤ el ∧ el ≤ 14 ∧
      incSpecs p i r =
        [(unitWL p i incDWL, upCorners p (instrBand i) 0 (A p i + incD)
            (hairCont p G ec (A p i + incD)) (i + 1)
            (copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (A p i + incD))),
          (unitWL p i incRWL, upCorners p (instrBand i) 1 (A p i + incR)
            (hairReg p 1 el (A p i + incR)) (p.length + r)
            (copyIdx C0halt (predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0))
              (A p i + incR)))] := by
  simp only [incSpecs]
  exact ⟨_, _, _, G_nonneg _, (solveE_bounds _ _ _).1, (solveE_bounds _ _ _).2,
    (solveE_bounds _ _ _).1, (solveE_bounds _ _ _).2, rfl⟩

/-- The pieces of the unit of an `inc` instruction: the entry chain at `v ≤ V_U + 122`, the body
groups with `u ≤ A + 113` or `v ≤ V_U + 311`, all at `v ≤ V_U + 433`. -/
theorem incUnit_pieces {p : Program} {i r : ℕ} (hi : p[i]? = some (.inc r)) {s : PSpec}
    (hs : s ∈ unitSpecs p i) :
    s.bx.b + s.bx.hi ≤ VU p + 433 ∧
      (s.bx.b - s.bx.lo ≤ A p i + 113 ∨ s.bx.b + s.bx.hi ≤ VU p + 311) := by
  have hd := unitD_uv p i
  have hk : unitKind p i = .inc := by simp [unitKind, hi]
  unfold unitSpecs at hs
  rw [hk] at hs
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨t, ht, rfl⟩ := mem_chainSpecs hs
    rw [chain_bx]
    simp only
    omega
  · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    have hj' := List.mem_range.1 hj
    simp only [PSpec.bx_mk]
    interval_cases j <;>
      simp only [Base.piece, bodyIncPieces, bodyIncG0, bodyIncG1, bodyIncG2, List.getD_cons_zero,
        List.getD_cons_succ] <;> omega

/-- The facts of the hairpins, tracks and destinations of the links of an `inc` instruction
used by the checks of its corners. -/
theorem inc_facts {p : Program} (hp : p.WellFormed) {i r : ℕ} (hi : p[i]? = some (.inc r))
    {G ec el : ℤ} (hG : 0 ≤ G) (hec : 0 ≤ ec) (hel : 0 ≤ el ∧ el ≤ 14) :
    i + 1 < p.length ∧
    hairCont p G ec (A p i + incD) ≤ HI p - 62 ∧
    HI p + 61 ≤ hairReg p 1 el (A p i + incR) ∧ hairReg p 1 el (A p i + incR) ≤ HI p + 90 ∧
    A p (i + 1 : ℕ) = A p i + PU p ∧ A p (i + 1 : ℕ) + PU p ≤ A p (p.length + r : ℕ) ∧
    0 ≤ A p i := by
  have hi1 := succ_lt_of_wf hp hi (by simp)
  have h1 := fixp_bounds (HI p - 62 - G - 2 * ec) ((A p i + incD) % 2)
  have h2 := fixp_bounds (HI p + 90 * 1 - 2 * el) ((A p i + incR) % 2)
  refine ⟨hi1, by unfold hairCont; omega, by unfold hairReg; omega, by unfold hairReg; omega,
    by push_cast; exact A_succ p i, A_add_le p (by push_cast; omega), A_nonneg p (by omega)⟩

/-- **The routes of every `inc` instruction are separated**: for every well-formed program, every
`inc r` instruction `i`, every delay `d ≡ 0 (mod 30)` and every time `T ≥ 2010 + d` (the end of
the body of the unit), the continue and the INC link satisfy `RouteSepX` for the pieces of the
machine, in the region of the machine. -/
theorem incLinks_sep {p : Program} (hp : p.WellFormed) {i r : ℕ} (hi : p[i]? = some (.inc r))
    {d : ℤ} (hd : d % 30 = 0) {T : ℤ} (hT : 2010 + d ≤ T) :
    ∀ x ∈ instrSpecs p i, RouteSepX (machPieces p) (machRegion p) (x.1.shift 0 0 d) x.2 T := by
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨G, ec, el, hG, hec, hec', hel, hel', heq⟩ := incSpecs_form p i r
  have hspec : instrSpecs p i = incSpecs p i r := by simp [instrSpecs, hi]
  have hI : instrCorners p i = upCorners p (instrBand i) 0 (A p i + incD)
      (hairCont p G ec (A p i + incD)) (i + 1)
      (copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (A p i + incD)) ++
      upCorners p (instrBand i) 1 (A p i + incR) (hairReg p 1 el (A p i + incR)) (p.length + r)
        (copyIdx C0halt (predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0))
          (A p i + incR)) := by
    simp [instrCorners, specCorners, hspec, heq]
  obtain ⟨hi1, hHc, hHl1, hHl2, hA1, hAm, hA0⟩ := inc_facts hp hi hG hec ⟨hel, hel'⟩
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have hiN : (i : ℤ) < N p := by unfold N; exact_mod_cast hlt
  have hr := reg_lt_R p hi
  simp only [regBound] at hr
  have hRr : (r : ℤ) < R p := by unfold R; omega
  have hoff1 : 0 < predContrib p.length (i + 1) i (.inc r) := by simp [predContrib]
  have hoff2 : (if i + 1 = p.length + r then 1 else 0) <
      predContrib p.length (p.length + r) i (.inc r) := by simp [predContrib]
  have hp1 := predIdx_lt_P p hi hoff1 (by omega)
  have hp2 := predIdx_lt_P p hi hoff2 (by omega)
  set tc := copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (A p i + incD) with htc
  set tl := copyIdx C0halt (predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0))
    (A p i + incR) with htl
  have ht1 := copyIdx_range p (C0 := unitC0 p (i + 1)) (c := A p i + incD)
    ⟨predIdx_nonneg p _ _ _, hp1⟩
  have ht2 := copyIdx_range p (C0 := C0halt) (c := A p i + incR) ⟨predIdx_nonneg p _ _ _, hp2⟩
  rw [← htc] at ht1
  rw [← htl] at ht2
  have hown1 : Owns p (instrBand i) (.slab (i + 1 : ℕ) tc) :=
    owns_of_tagOf ⟨_, 0, _, rfl, hi, hoff1, ht1.2.2.1, ht1.2.2.2⟩
  have hown2 : Owns p (instrBand i) (.slab (p.length + r : ℕ) tl) :=
    owns_of_tagOf ⟨_, _, _, rfl, hi, hoff2, ht2.2.2.1, ht2.2.2.2⟩
  have hc1 : -237 ≤ unitC0 p (i + 1) ∧ unitC0 p (i + 1) ≤ -67 ∧ unitC0 p (i + 1) % 2 = 1 := by
    rcases unitC0_cases p (i + 1) with h | h | h <;> rw [h] <;> norm_num
  have hc2 := unitC0_merge p r
  have hci := unitC0_inc hi
  have hnh : ∀ x : ℕ, p[x]? = some .halt → x ≠ i := by
    intro x hx h; subst h; rw [hi] at hx; simp at hx
  have hb : instrBand (i : ℤ) = 1 + i := rfl
  have hto0 := tracks_range p (instrBand i) 0 (A p i + incD)
  have hto1 := tracks_range p (instrBand i) 1 (A p i + incR)
  have hpar1 : (destU p (i + 1) tc - (A p i + incD)) % 2 = 0 ∧
      (destU p (i + 1) tc + destV p tc) % 2 = 1 := by
    have := (copyBeta_spec (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (A p i + incD)).2.2
    rw [← htc] at this
    have := A_even p i
    have := A_even p (i + 1 : ℕ)
    have := VU_even p
    have hodd : unitC0 p (i + 1) % 2 = 1 := by
      rcases unitC0_cases p (i + 1) with h | h | h <;> rw [h] <;> norm_num
    unfold destU destV inCol sideV at *
    constructor <;> omega
  have hpar2 : (destU p (p.length + r) tl - (A p i + incR)) % 2 = 0 ∧
      (destU p (p.length + r) tl + destV p tl) % 2 = 1 := by
    have := (copyBeta_spec C0halt (predIdx p (p.length + r) i
      (if i + 1 = p.length + r then 1 else 0)) (A p i + incR)).2.2
    rw [← htl] at this
    have := A_even p i
    have := A_even p (p.length + r : ℕ)
    have := VU_even p
    unfold destU destV inCol sideV at *
    rw [hc2]
    simp only [C0halt] at *
    constructor <;> omega
  clear_value tc tl
  clear htc htl hp1 hp2 hoff1 hoff2
  have hd1 : destU p (i + 1) tc = A p (i + 1 : ℕ) + unitC0 p (i + 1) - 61 * tc := by
    unfold destU inCol; ring
  have hd2 : destU p (p.length + r) tl = A p (p.length + r : ℕ) + C0halt - 61 * tl := by
    unfold destU inCol; rw [hc2]; ring
  have hv1 : destV p tc = VU p + 76 - 99 * tc := by unfold destV sideV; ring
  have hv2 : destV p tl = VU p + 76 - 99 * tl := by unfold destV sideV; ring
  have hincD : incD = 68 := rfl
  have hincR : incR = 157 := rfl
  have hC0 : C0halt = -67 := rfl
  intro x hx
  rw [hspec, heq] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · -- the continue
    have hxm : (unitWL p i ⟨1, 1, incD, 605⟩, upCorners p (instrBand i) 0 (A p i + incD)
        (hairCont p G ec (A p i + incD)) (i + 1) tc) ∈ instrSpecs p i := by
      rw [hspec, heq]; exact List.mem_cons_self
    refine unitUpLink_sep hp hlt hxm (by norm_num) (by rw [hci, hincD]; simp [C0inc])
      hnh (hairCont_par p G ec (A p i + incD)) hpar1.1 hpar1.2 (by omega) ⟨ht1.1, ht1.2.1⟩ hown1
      (vS := VU p + 632) ?_ ?_ ?_ ?_ hd ?_
    · clear hpar1 hpar2 hd hT
      intro c' hc' n1
      rw [hI] at hc'
      simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl n1 | (refine corner_farRect ?_; simp only; omega)
    · clear hpar1 hpar2 hd hT
      intro c' hc' n1 n2
      rw [hI] at hc'
      simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl n1 | exact absurd rfl n2 |
          (refine corner_farRect ?_; simp only; omega)
    · clear hpar1 hpar2 hd hT
      intro c' hc' n1 n2
      rw [hI] at hc'
      simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl n1 | exact absurd rfl n2 |
          (refine corner_farRect ?_; simp only; omega)
    · clear hpar1 hpar2 hd hT
      intro s' hs'
      have := incUnit_pieces hi hs'
      unfold FarRect
      omega
    · clear hpar1 hpar2 hd
      intro t' ht'
      have := (unitWL_center p i incD 605 d t').2
      omega
  · -- the INC link
    have hxm : (unitWL p i ⟨1, 1, incR, 1029⟩, upCorners p (instrBand i) 1 (A p i + incR)
        (hairReg p 1 el (A p i + incR)) (p.length + r) tl) ∈ instrSpecs p i := by
      rw [hspec, heq]; exact List.mem_cons_of_mem _ List.mem_cons_self
    refine unitUpLink_sep hp hlt hxm (by norm_num) (by rw [hci, hincR]; simp [C0inc])
      hnh (hairReg_par p 1 el (A p i + incR)) hpar2.1 hpar2.2 (by unfold N R at *; omega)
      ⟨ht2.1, ht2.2.1⟩ hown2 (vS := VU p + 331) ?_ ?_ ?_ ?_ hd ?_
    · clear hpar1 hpar2 hd hT
      intro c' hc' n1
      rw [hI] at hc'
      simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl n1 | (refine corner_farRect ?_; simp only; omega)
    · clear hpar1 hpar2 hd hT
      intro c' hc' n1 n2
      rw [hI] at hc'
      simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl n1 | exact absurd rfl n2 |
          (refine corner_farRect ?_; simp only; omega)
    · clear hpar1 hpar2 hd hT
      intro c' hc' n1 n2
      rw [hI] at hc'
      simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl n1 | exact absurd rfl n2 |
          (refine corner_farRect ?_; simp only; omega)
    · clear hpar1 hpar2 hd hT
      intro s' hs'
      have := incUnit_pieces hi hs'
      unfold FarRect
      omega
    · clear hpar1 hpar2 hd
      intro t' ht'
      have := (unitWL_center p i incR 1029 d t').2
      omega

/-- The INC channel of a module is even. -/
theorem incChan_even' (p : Program) : incChan p % 2 = 0 := by
  have := fixp_parity (uL - 62 * (2 * D p)) (1 - incPortV % 2)
  unfold incChan leftChan
  simp only [incPortV] at this ⊢
  omega

/-- The kind of a merge unit. -/
theorem unitKind_merge (p : Program) (r : ℕ) : unitKind p (p.length + r) = .merge := by
  simp [unitKind]

/-- **The merge link of every register with an `inc` is separated**: for every well-formed program,
every register `r` with an `inc` caller, every delay `d ≡ 0 (mod 30)` and every time
`T ≥ 917 + d` (the glider below the entry chain of the merge unit; `mergeLink_sep'` from
`914 + d`), the merge link satisfies
`RouteSepX` for the pieces of the machine, in the region of the machine. -/
theorem mergeLink_sep {p : Program} (hp : p.WellFormed) {r : ℕ} (hr : r < numRegs p)
    (hu : mergeUsed p r = true) {d : ℤ} (hd : d % 30 = 0) {T : ℤ} (hT : 917 + d ≤ T) :
    ∀ x ∈ mergeSpecs p r, RouteSepX (machPieces p) (machRegion p) (x.1.shift 0 0 d) x.2 T := by
  intro x hx
  have hcorner := mergeRoute_corner hr hu hx
  have hmem := mergeRoute_mem hr hu hx
  simp only [mergeSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have hRr : (r : ℤ) < R p := by unfold R; exact_mod_cast hr
  have hsplit := ownSplit_merge hp r
  have hown := mergeCorners_desc hr
  have hv := mergeCorners_valid p hr
  have he := solveE_bounds (unitWL p (p.length + r) haltDWL) (mergeCorners p r)
    (modWL p r incWin)
  have hH := hairReg_le p (s := 0) (e := mergeE p r) (c := A p (p.length + r : ℕ) + haltD)
    (by norm_num) he.1
  have hl := fixp_bounds (uL - 62 * (2 * D p)) (1 - incPortV % 2)
  have hgap := unit_module_gap p (a := (p.length + r : ℕ)) (r := r)
    ⟨by omega, by unfold N R; push_cast; omega⟩ (by omega)
  have hA := A_nonneg p (a := (p.length + r : ℕ)) (by omega)
  have hU := (U_ge p (r := r) (by omega)).1
  have hb : mergeBand p r = 1 + ((p.length + r : ℕ) : ℤ) := by
    unfold mergeBand N; push_cast; ring
  have hto := tracks_range p (mergeBand p r) 0 (A p (p.length + r : ℕ) + haltD)
  have hcd : U p r - 794 - 62 * (2 * D p) ≤ U p r + incChan p ∧
      U p r + incChan p ≤ U p r - 793 - 62 * (2 * D p) := by
    unfold incChan leftChan uL at *; omega
  have hhaltD : haltD = 14 := rfl
  unfold modLeft at hgap
  have hown' : Owns p (mergeBand p r) (.left r (2 * D p)) := Or.inr ⟨r, by unfold mergeBand; ring,
    rfl, rfl⟩
  have hIm : specCorners (mergeSpecs p r) = mergeCorners p r (mergeE p r) := by
    simp [specCorners, mergeSpecs]
  simp only [mergeCorners, ← Nat.cast_add] at hIm hcorner hmem ⊢
  refine unitDownLink_sep hp hsplit hb (by unfold mergeBand; omega) hcorner hmem (by norm_num)
    (by rw [unitC0_merge]; simp [C0halt, haltD]) ?_ (hairReg_par p 0 _ _) ?_ ?_
    (by exact_mod_cast hRr) (by have := one_le_D p; omega) hcd hown' (vS := VU p + 128)
    ?_ ?_ ?_ ?_ hd ?_
  · intro x hx h; rw [h] at hx
    have := (List.getElem?_eq_some_iff.1 hx).1; omega
  · have := incChan_even' p; have := U_even p r; have := A_even p (p.length + r : ℕ)
    simp only [haltD]; omega
  · have := incChan_even' p; have := U_even p r
    simp only [incPortV]; omega
  · intro c' hc' n1
    rw [hIm] at hc'
    rcases mem_downCorners.1 hc' with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl n1 | (refine corner_farRect ?_; simp only; omega)
  · intro c' hc' n1 n2
    rw [hIm] at hc'
    rcases mem_downCorners.1 hc' with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl n1 | exact absurd rfl n2 |
        (refine corner_farRect ?_; simp only; omega)
  · intro c' hc' n1 n2
    rw [hIm] at hc'
    rcases mem_downCorners.1 hc' with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl n1 | exact absurd rfl n2 |
        (refine corner_farRect ?_; simp only; omega)
  · intro s' hs'
    have := unitSpecs_nobody_uv p _ (Or.inr (unitKind_merge p r)) hs'
    exact farRect_of_uv this (Or.inr (Or.inr (Or.inl (by omega))))
  · intro t' ht'
    have := (unitWL_center p (p.length + r) 14 629 d t').2
    change VU p + 128 + 2 ≤ ((unitWL p (p.length + r) ⟨1, 1, 14, 629⟩).shift 0 0 d).cv t'
    omega

/-! ### The merge link from the release of the merge unit's chain -/

/-- `RouteSepX` from an earlier time: the extra generations of the first flight in the region and
far from every piece. -/
theorem routeSepX_extend {L : List Piece} {Z : Set Cell} {g : WL} {c : Corner} {cs : List Corner}
    {T T' : ℤ} (h : RouteSepX L Z g (c :: cs) T')
    (hx : ∀ t : ℤ, T ≤ t → t < T' → g.box t ⊆ Z ∧ ∀ h ∈ L, FarApart 2 (g.box t) h.box) :
    RouteSepX L Z g (c :: cs) T := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun t ht1 ht2 => ?_, fun t ht1 ht2 => ?_, h3, h4, h5⟩
  · by_cases ht : t < T'
    · exact (hx t ht1 ht).1
    · exact h1 t (by omega) ht2
  · by_cases ht : t < T'
    · exact (hx t ht1 ht).2
    · exact h2 t (by omega) ht2

/-- **The merge glider just below the merge unit's chain** (template times `914 … 916` after the
delay `d`): in the region and far from every piece of the machine (the entry chain is `≥ 24`
rows above it). -/
theorem merge_first {p : Program} (hp : p.WellFormed) {r : ℕ} (hr : r < numRegs p)
    (hu : mergeUsed p r = true) {d t : ℤ} (ht : 914 + d ≤ t ∧ t ≤ 916 + d) :
    ((unitWL p (p.length + r) haltDWL).shift 0 0 d).box t ⊆ machRegion p ∧
      ∀ h ∈ machPieces p,
        FarApart 2 (((unitWL p (p.length + r) haltDWL).shift 0 0 d).box t) h.box := by
  set a := p.length + r with ha
  have hcm := mergeRoute_corner hr hu (x := (unitWL p a haltDWL, mergeCorners p r (mergeE p r)))
    (by simp [mergeSpecs, ha])
  have hc1 : (⟨3, A p a + haltD, trackOut p (mergeBand p r) 0 (A p a + haltD),
      .band (mergeBand p r) 0 false⟩ : Corner) ∈ allCorners p := by
    refine hcm _ ?_
    simp only [mergeCorners, downCorners, bandCorners, List.cons_append, ha]
    push_cast
    exact List.mem_cons_self
  have hu' := unitD_uv p a
  have hf := layout_facts p
  have hRs := slabR_ge_rs p
  have hRr : (r : ℤ) < R p := by unfold R; exact_mod_cast hr
  have haN : (a : ℤ) < N p + R p := by unfold N; push_cast [ha]; omega
  have hpx : ((unitWL p a haltDWL).shift 0 0 d).px t = unitDX p a + 71 ∧
      ((unitWL p a haltDWL).shift 0 0 d).py t = unitDY p a + 57 := by
    simp only [WL.px, WL.py, WL.qt, unitWL, haltDWL, WL.shift]; omega
  have hcu : ((unitWL p a haltDWL).shift 0 0 d).cu t = A p a + 14 := by
    simp only [WL.cu]; omega
  have hcv : ((unitWL p a haltDWL).shift 0 0 d).cv t = VU p + 128 := by
    simp only [WL.cv]; omega
  refine ⟨box_sub_region hc1 (by simp only [haltD]; omega), ?_⟩
  intro h hh
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  rw [PSpec.piece_box]
  have hr' : A p a + 10 ≤ ((unitWL p a haltDWL).shift 0 0 d).cu t - 4 ∧
      ((unitWL p a haltDWL).shift 0 0 d).cu t + 4 ≤ A p a + 18 ∧
      VU p + 126 ≤ ((unitWL p a haltDWL).shift 0 0 d).cv t - 2 ∧
      ((unitWL p a haltDWL).shift 0 0 d).cv t + 6 ≤ VU p + 134 := by omega
  rcases mem_machSpecs hs with ⟨a', ha', hs'⟩ | ⟨r', hr'', hs'⟩ | ⟨c', hc', hb'⟩
  · by_cases h : a' = a
    · rw [h] at hs'
      unfold unitSpecs at hs'
      rw [show unitKind p a = .merge from unitKind_merge p r] at hs'
      simp only [List.append_nil] at hs'
      obtain ⟨t', -, rfl⟩ := mem_chainSpecs hs'
      rw [chain_bx]
      refine Box.farApart ?_
      simp only
      omega
    · exact far_glider (slab_unit_other (a := a) (by omega) a' s ha' h hs') hr'
  · exact far_glider (slab_module (a := a) haN (by omega) r' s hr'' hs') hr'
  · rw [hb']
    refine far_glider (corner_farRect ?_) hr'
    have hv := allCorners_valid hp c' hc'
    obtain ⟨k', u, v, tag⟩ := c'
    simp only at hv ⊢
    have hc0 := unitC0_merge p r
    cases tag with
    | band b n hb =>
      simp only [Valid] at hv
      obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8⟩ := hv
      omega
    | halt a'' => simp only [Valid] at hv; omega
    | slab a'' t'' =>
      simp only [Valid] at hv
      have hc0' := unitC0_cases p a''.toNat
      rcases lt_trichotomy a'' a with h | h | h
      · have := A_add_le p h; omega
      · have h' : a''.toNat = a := by omega
        have hc0' : unitC0 p a = -67 := hc0
        rw [h', hc0'] at hv; subst h; simp only [haltD] at *; omega
      · have := A_add_le p h; omega
    | left r' idx =>
      simp only [Valid] at hv
      have := unit_module_gap p (a := a) (r := r') ⟨by omega, by omega⟩ (by omega)
      unfold modLeft at this; omega
    | right r' j' w =>
      simp only [Valid] at hv
      have := unit_module_gap p (a := a) (r := r') ⟨by omega, by omega⟩ (by omega)
      unfold modLeft at this; omega

/-- **The merge link from the release of the merge unit's chain** (template time `914 + d`, the
time `T1` of the increment plan): `RouteSepX` from every `T ≥ 914 + d`. -/
theorem mergeLink_sep' {p : Program} (hp : p.WellFormed) {r : ℕ} (hr : r < numRegs p)
    (hu : mergeUsed p r = true) {d : ℤ} (hd : d % 30 = 0) {T : ℤ} (hT : 914 + d ≤ T) :
    ∀ x ∈ mergeSpecs p r, RouteSepX (machPieces p) (machRegion p) (x.1.shift 0 0 d) x.2 T := by
  intro x hx
  by_cases h3 : 917 + d ≤ T
  · exact mergeLink_sep hp hr hu hd h3 x hx
  have hx' := hx
  simp only [mergeSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx'
  subst hx'
  have h := mergeLink_sep hp hr hu hd (le_refl (917 + d)) _ hx
  simp only [mergeCorners, downCorners, bandCorners, List.cons_append] at h ⊢
  refine routeSepX_extend h fun t ht1 ht2 => merge_first hp hr hu ⟨by omega, by omega⟩

/-- The world line delayed by `0` is the world line (for the undelayed forms of the links). -/
theorem WL.shift_zero_rs (w : WL) : w.shift 0 0 0 = w := by
  obtain ⟨dx, dy, lane, tau⟩ := w
  simp [WL.shift]

end LP

end LeanTheory.Life
