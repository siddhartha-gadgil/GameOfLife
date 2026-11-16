/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepUnit

/-!
# The two threads of an `inc` activation: their pieces and their moving parts

Research note `N-22`. For the fields `idle` and `threads` of `IncSep` (`ActivationIncStep`):

* `isep2CMov`, `isep2IMov`: the moving parts of the footprints of the continue thread and of the
  increment thread (`contFoot = boxesOf (dd LCraw) ∪ isep2CMov`, `isep2_contFoot_eq`;
  `incFoot ⊆ boxesOf (dd LIraw) ∪ isep2IMov`, `isep2_incFoot_sub`);
* `isep2_static`: every piece of the continue thread is separated from every piece of the
  increment thread (distinct places of corners, distinct units, units and modules), and
  `isep2_LC_not_LI`: no piece belongs to both threads;
* `isep2_CMov_far`, `isep2_IMov_far`: the moving part of each thread is far from every piece of
  the machine outside the thread (from the strong forms of the flight fields, `isep2_rfoot_far`
  for the routes, `isep2_entry_far` for the entry chains);
* `isep2_idle`: the field `idle`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-! ### The moving parts of the footprints -/

/-- The moving part of the footprint of the continue thread. -/
def isep2CMov (P : IncPlan p i r) (j : ℕ) : Set Cell :=
  if j ≤ P.Tc - 2010 then linkFootW p (i + 1) P.tc (unitWL p i incDWL) P.csC 2010 P.T0c j
  else (fun c => (unitDX p (i + 1), unitDY p (i + 1)) + c) ''
    chainOutWL.box (-166 + ((j - (P.Tc - 2010) : ℕ) : ℤ))

/-- The footprint of the continue thread: its pieces and its moving part. -/
theorem isep2_contFoot_eq (P : IncPlan p i r) (j : ℕ) :
    P.contFoot j = boxesOf (dd P.LCraw) ∪ isep2CMov P j := by
  unfold IncPlan.contFoot isep2CMov
  split_ifs <;> rfl

/-- The moving part of the footprint of the increment thread before the gate. -/
def isep2EMov (P : IncPlan p i r) (j : ℕ) : Set Cell :=
  if j ≤ P.T1 - 2010 + (P.eM - P.T1) then
    (if j ≤ P.T1 - 2010 then
      linkFootW p (mergeUnit p r) P.tl (unitWL p i incRWL) P.csR 2010 P.T0l j
    else routeFootX P.gM P.csM P.T1 (j - (P.T1 - 2010)))
  else if j + 16 ≤ P.Tg - 2010 then
    (route P.gM P.csM).2.box ((P.eM : ℤ) + ((j - (P.T1 - 2010 + (P.eM - P.T1)) : ℕ) : ℤ))
  else gateBox p r

/-- The footprint of the increment thread before the gate: its pieces and its moving part. -/
theorem isep2_earlyFoot_eq (P : IncPlan p i r) (j : ℕ) :
    P.earlyFoot j = boxesOf (dd P.LIraw) ∪ isep2EMov P j := by
  unfold IncPlan.earlyFoot isep2EMov
  split_ifs <;> rfl

/-- The moving part of the footprint of the increment thread (with the register). -/
def isep2IMov (P : IncPlan p i r) (R0 : RegS) (j : ℕ) : Set Cell :=
  if j ≤ P.Tg - 2010 then isep2EMov P j ∪ regStrip p r R0 (j + R0.m)
  else if j - (P.Tg - 2010) ≤ 946 then
    modFootW p r P.km P.Tg (j - (P.Tg - 2010)) ∪
      regStrip p r (R0.later (P.Tg - 2010)) (j - (P.Tg - 2010) + (R0.later (P.Tg - 2010)).m)
  else (conway.evolve (j - (P.Tg - 2010) - 946)
    (incStart p r ∪ regAt p r ((R0.later (P.Tg - 2010)).later 946)) : Set Cell)

/-- The footprint of the increment thread lies in its pieces and its moving part. -/
theorem isep2_incFoot_sub (P : IncPlan p i r) (R0 : RegS) (j : ℕ) :
    P.incFoot R0 j ⊆ boxesOf (dd P.LIraw) ∪ isep2IMov P R0 j := by
  unfold IncPlan.incFoot isep2IMov
  split_ifs with h1 h2
  · rw [isep2_earlyFoot_eq]
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  · unfold modRunFootW
    simp only [h2, ↓reduceIte]
    exact (Set.union_assoc _ _ _).subset
  · unfold modRunFootW
    simp only [h2, ↓reduceIte]
    exact subset_rfl

/-! ### The pieces of the two threads -/

/-- The pieces of the continue thread: reflectors of its corners and copies of the entry chain
of unit `i + 1`. -/
theorem isep2_LC_cases {x : Piece} (hx : x ∈ (incPlan p i r).LCraw) :
    (∃ c ∈ (incPlan p i r).csC, x.box = (cornerSpec c).piece.box) ∨
      ∃ t' ≤ (incPlan p i r).tc, x = (PSpec.mk .orGate (unitDX p (i + 1) - 35 * (t' : ℤ))
        (unitDY p (i + 1) - 64 * (t' : ℤ)) (14 * t' % 30)).piece := by
  rcases List.mem_append.1 hx with hx | hx
  · exact Or.inl (route_piece_box hx)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    obtain ⟨t', ht', rfl⟩ := mem_chainSpecs hs
    exact Or.inr ⟨t', by omega, rfl⟩

/-- The pieces of the increment thread: reflectors of the corners of the INC link and of the
merge link, copies of the entry chain of the merge unit, and pieces of module `r`. -/
theorem isep2_LI_cases {x : Piece} (hx : x ∈ (incPlan p i r).LIraw) :
    (∃ c ∈ (incPlan p i r).csR ++ (incPlan p i r).csM, x.box = (cornerSpec c).piece.box) ∨
      (∃ t' ≤ (incPlan p i r).tl, x =
        (PSpec.mk .orGate (unitDX p (p.length + r) - 35 * (t' : ℤ))
          (unitDY p (p.length + r) - 64 * (t' : ℤ)) (14 * t' % 30)).piece) ∨
      ∃ s ∈ moduleSpecs p r, x = s.piece := by
  simp only [IncPlan.LIraw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (((hx | hx) | hx) | hx | hx) | hx
  · obtain ⟨c, hc, he⟩ := route_piece_box hx
    exact Or.inl ⟨c, List.mem_append_left _ hc, he⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    obtain ⟨t', ht', rfl⟩ := mem_chainSpecs hs
    exact Or.inr (Or.inl ⟨t', by omega, rfl⟩)
  · obtain ⟨c, hc, he⟩ := route_piece_box hx
    exact Or.inl ⟨c, List.mem_append_right _ hc, he⟩
  · exact Or.inr (Or.inr ⟨_, mem_moduleSpecs_head (List.mem_append_right _
      (List.mem_cons_of_mem _ List.mem_cons_self)), hx⟩)
  · exact Or.inr (Or.inr ⟨_, mem_moduleSpecs_head (List.mem_append_right _
      List.mem_cons_self), hx⟩)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    exact Or.inr (Or.inr ⟨s, mem_moduleSpecs_head (List.mem_append_left _ hs), rfl⟩)

/-- The corners of the continue are corners of the machine. -/
theorem isep2_csC_corner (hins : p[i]? = some (.inc r)) :
    ∀ c ∈ (incPlan p i r).csC, c ∈ allCorners p :=
  instrRoute_corner (List.getElem?_eq_some_iff.1 hins).1
    (x := (unitWL p i incDWL, (incPlan p i r).csC))
    (by rw [isep_instrSpecs hins]; exact List.mem_cons_self)

/-- The corners of the INC link are corners of the machine. -/
theorem isep2_csR_corner (hins : p[i]? = some (.inc r)) :
    ∀ c ∈ (incPlan p i r).csR, c ∈ allCorners p :=
  instrRoute_corner (List.getElem?_eq_some_iff.1 hins).1
    (x := (unitWL p i incRWL, (incPlan p i r).csR))
    (by rw [isep_instrSpecs hins]; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-- The corners of the merge link are corners of the machine. -/
theorem isep2_csM_corner (hins : p[i]? = some (.inc r)) :
    ∀ c ∈ (incPlan p i r).csM, c ∈ allCorners p :=
  mergeRoute_corner (lt_numRegs_of_inc hins) (mergeUsed_of_inc hins)
    (x := (unitWL p (p.length + r) haltDWL, mergeCorners p r (mergeE p r)))
    (by simp [mergeSpecs])

/-- **The corners of the continue and of the increment thread are at distinct places.** -/
theorem isep2_tags (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ c ∈ (incPlan p i r).csC, ∀ c' ∈ (incPlan p i r).csR ++ (incPlan p i r).csM,
      c.tag ≠ c'.tag := by
  have hi1 := succ_lt_of_inc hp hins
  intro c hc c' hc'
  rw [isep2_csC_eq hp hins] at hc
  have hcM : (incPlan p i r).csM = mergeCorners p r (mergeE p r) := rfl
  rw [isep2_csR_eq hins, hcM, isep2_mergeCorners_eq] at hc'
  simp only [bandCorners, isep2SlabC, isep2PortC, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc hc'
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, CTag.band.injEq, CTag.slab.injEq, reduceCtorEq, not_false_eq_true,
      instrBand, mergeBand, N, not_and] <;> omega

/-- **Every piece of the continue thread is separated from every piece of the increment
thread.** -/
theorem isep2_static (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ x ∈ (incPlan p i r).LCraw, ∀ y ∈ (incPlan p i r).LIraw, Piece.Sep x y := by
  have hi1 := succ_lt_of_inc hp hins
  have hr := lt_numRegs_of_inc hins
  have hR : (r : ℤ) < R p := by unfold R; exact_mod_cast hr
  have htc := incTc_range hp hins
  have htl := incTl_range hins
  have hf := layout_facts p
  intro x hx y hy
  rcases isep2_LC_cases hx with ⟨c, hc, hxb⟩ | ⟨t', ht', rfl⟩ <;>
    rcases isep2_LI_cases hy with ⟨c', hc', hyb⟩ | ⟨t'', ht'', rfl⟩ | ⟨s, hs, rfl⟩
  · -- two corners at distinct places
    have hcc : c ∈ allCorners p := isep2_csC_corner hins c hc
    have hcc' : c' ∈ allCorners p := by
      rcases List.mem_append.1 hc' with h | h
      · exact isep2_csR_corner hins c' h
      · exact isep2_csM_corner hins c' h
    have := corner_gap61 p (allCorners_valid hp c hcc) (allCorners_valid hp c' hcc')
      (isep2_tags hp hins c hc c' hc')
    unfold Piece.Sep
    rw [hxb, hyb, PSpec.piece_box, PSpec.piece_box]
    exact (corner_far (by omega)).farApart
  · -- a corner and a copy of the merge chain
    have hcc : c ∈ allCorners p := isep2_csC_corner hins c hc
    have h := corner_unit_sep p (allCorners_valid hp c hcc) (a := p.length + r)
      (s := PSpec.mk .orGate (unitDX p (p.length + r) - 35 * (t'' : ℤ))
        (unitDY p (p.length + r) - 64 * (t'' : ℤ)) (14 * t'' % 30))
      (List.mem_append_left _ (List.mem_map.2 ⟨t'', List.mem_range.2 (by
        have : (t'' : ℤ) < 2 * P p := by
          have : ((incPlan p i r).tl : ℤ) = incTl p i r := Int.toNat_of_nonneg htl.1
          omega
        unfold P at this; omega), rfl⟩))
    unfold Piece.Sep at h ⊢
    rw [hxb]
    exact h
  · -- a corner and a module piece
    have hcc : c ∈ allCorners p := isep2_csC_corner hins c hc
    have h := corner_module_sep p (allCorners_valid hp c hcc) hs
    unfold Piece.Sep at h ⊢
    rw [hxb]
    exact h
  · -- a copy of the chain of unit `i + 1` and a corner
    have hcc' : c' ∈ allCorners p := by
      rcases List.mem_append.1 hc' with h | h
      · exact isep2_csR_corner hins c' h
      · exact isep2_csM_corner hins c' h
    have h := corner_unit_sep p (allCorners_valid hp c' hcc') (a := i + 1)
      (s := PSpec.mk .orGate (unitDX p (i + 1) - 35 * (t' : ℤ))
        (unitDY p (i + 1) - 64 * (t' : ℤ)) (14 * t' % 30))
      (List.mem_append_left _ (List.mem_map.2 ⟨t', List.mem_range.2 (by
        have : (t' : ℤ) < 2 * P p := by
          have : ((incPlan p i r).tc : ℤ) = incTc p i := Int.toNat_of_nonneg htc.1
          omega
        unfold P at this; omega), rfl⟩))
    unfold Piece.Sep at h ⊢
    rw [hyb]
    exact FarApart.symm' h
  · -- two copies of chains of distinct units
    rw [Piece.Sep, isep2_chain_box, isep2_chain_box]
    have := A_add_le p (a := ((i + 1 : ℕ) : ℤ)) (a' := ((p.length + r : ℕ) : ℤ))
      (by push_cast; omega)
    have h1 := unitD_uv p (i + 1)
    have h2 := unitD_uv p (p.length + r)
    have : ((incPlan p i r).tc : ℤ) = incTc p i := Int.toNat_of_nonneg htc.1
    have : ((incPlan p i r).tl : ℤ) = incTl p i r := Int.toNat_of_nonneg htl.1
    refine isep2_far_box fun z ⟨z1, z2, z3, z4⟩ => ?_
    omega
  · -- a copy of the chain of unit `i + 1` and a module piece
    have hu := (moduleSpecs_uv p r hs).1
    have h1 := unitD_uv p (i + 1)
    have hgap := unit_module_gap p (a := ((i + 1 : ℕ) : ℤ)) (r := r) ⟨by omega, by
      unfold N R; push_cast; omega⟩ (by omega)
    have hRs := slabR_ge_rs p
    have : ((incPlan p i r).tc : ℤ) = incTc p i := Int.toNat_of_nonneg htc.1
    rw [Piece.Sep, isep2_chain_box, PSpec.piece_box]
    refine isep2_far_box fun z ⟨z1, z2, z3, z4⟩ => ?_
    unfold BoxT.InUV at hu
    unfold modLeft at hgap
    omega

/-- The corners of the continue are of images `< 8`. -/
theorem isep2_csC_k (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ c ∈ (incPlan p i r).csC, c.k < 8 := by
  intro c hc
  rw [isep2_csC_eq hp hins] at hc
  simp only [bandCorners, isep2SlabC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp

/-- The box of a piece of the continue thread is not empty. -/
theorem isep2_LC_nonempty (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {x : Piece}
    (hx : x ∈ (incPlan p i r).LCraw) : ∃ z : Cell, z ∈ x.box := by
  rcases isep2_LC_cases hx with ⟨c, hc, hxb⟩ | ⟨t', ht', rfl⟩
  · have hk : c.k < 8 := isep2_csC_k hp hins c hc
    have := cornerSpec_nonempty hk
    rw [hxb, PSpec.piece_box]
    exact ⟨((cornerSpec c).bx.a, (cornerSpec c).bx.lo), le_rfl, this.1, le_rfl, this.2⟩
  · rw [isep2_chain_box]
    exact ⟨(unitDX p (i + 1) - 35 * (t' : ℤ), unitDY p (i + 1) - 64 * (t' : ℤ)),
      le_rfl, by omega, le_rfl, by omega⟩

/-- **No piece belongs to both threads.** -/
theorem isep2_LC_not_LI (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {x : Piece}
    (hx : x ∈ (incPlan p i r).LCraw) : x ∉ (incPlan p i r).LIraw := by
  intro hy
  obtain ⟨z, hz⟩ := isep2_LC_nonempty hp hins hx
  exact isep2_static hp hins x hx x hy z hz z hz ⟨by omega, by omega, by omega, by omega⟩

/-! ### The moving parts are far from the idle pieces -/

/-- The pieces of the continue thread are pieces of the machine. -/
theorem isep2_LC_mem (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ x ∈ (incPlan p i r).LCraw, x ∈ machPieces p := (incPlan_valid hp hins).memC

/-- The pieces of the increment thread are pieces of the machine. -/
theorem isep2_LI_mem (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ x ∈ (incPlan p i r).LIraw, x ∈ machPieces p := (incPlan_valid hp hins).memI

/-- **The moving part of the continue thread is far from every piece of the machine outside the
thread.** -/
theorem isep2_CMov_far (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j < (incPlan p i r).Tend - 2010, ∀ h ∈ machPieces p, h ∉ (incPlan p i r).LCraw →
      FarApart 2 (isep2CMov (incPlan p i r) j) h.box := by
  intro j hj h hh hn
  have hv := incPlan_valid hp hins
  have hi1 := succ_lt_of_inc hp hins
  have htc := incTc_range hp hins
  have htcN : ((incPlan p i r).tc : ℤ) = incTc p i := Int.toNat_of_nonneg htc.1
  unfold isep2CMov
  split_ifs with h1
  · unfold linkFootW
    split_ifs with h2 h3
    · obtain ⟨c, cs, hcs⟩ : ∃ c cs, (incPlan p i r).csC = c :: cs := ⟨_, _, rfl⟩
      have hsep := isep_sepC hp hins
      have htim := hv.timedC
      have hlin := hv.linesC
      have hk := isep2_csC_k hp hins
      rw [hcs] at hsep htim hlin hk h2 ⊢
      exact isep2_rfoot_far cs c _ 2010 hsep htim hlin hk j h2 h hh fun hm =>
        hn (List.mem_append_left _ (by rw [hcs]; exact hm))
    · have := isep2_flyC hp hins (2010 + j) (by omega) (by omega) h hh
      push_cast at this
      exact this
    · exact isep2_entry_far hp (a := i + 1) (by unfold N R; push_cast; have := one_le_R p; omega)
        (by rw [htcN]; exact htc.2) h hh fun hm => hn (List.mem_append_right _ hm)
  · have hT : (incPlan p i r).Tend = (incPlan p i r).Tc + 166 := rfl
    exact isep2_outC hp (i + 1) (j - ((incPlan p i r).Tc - 2010)) (by omega) h hh

/-- Membership facts of the pieces of the increment thread. -/
theorem isep2_LI_facts (P : IncPlan p i r) :
    gateP p r ∈ P.LIraw ∧ rfJP p r ∈ P.LIraw ∧ (∀ x ∈ modGroup p r, x ∈ P.LIraw) ∧
      (∀ x ∈ chainPieces p (mergeUnit p r) P.tl, x ∈ P.LIraw) ∧
      (∀ x ∈ (route (unitWL p i incRWL) P.csR).1.map PSpec.piece, x ∈ P.LIraw) ∧
      (∀ x ∈ (route P.gM P.csM).1.map PSpec.piece, x ∈ P.LIraw) := by
  refine ⟨by simp [IncPlan.LIraw], by simp [IncPlan.LIraw], fun x hx => by
    simp [IncPlan.LIraw, hx], fun x hx => by simp [IncPlan.LIraw, hx],
    fun x hx => by simp only [IncPlan.LIraw, List.mem_append]; tauto,
    fun x hx => by simp only [IncPlan.LIraw, List.mem_append]; tauto⟩

/-- **The moving part of the increment thread is far from every piece of the machine outside the
thread**, for a ready register. -/
theorem isep2_IMov_far (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {R0 : RegS}
    (hR : R0.Ready) : ∀ j < (incPlan p i r).Tend - 2010, ∀ h ∈ machPieces p,
      h ∉ (incPlan p i r).LIraw → FarApart 2 (isep2IMov (incPlan p i r) R0 j) h.box := by
  intro j hj h hh hn
  have hv := incPlan_valid hp hins
  have hr := lt_numRegs_of_inc hins
  have htl := incTl_range hins
  have htlN : ((incPlan p i r).tl : ℤ) = incTl p i r := Int.toNat_of_nonneg htl.1
  obtain ⟨hgI, hjI, hmI, hcI, hrI, hmrI⟩ := isep2_LI_facts (incPlan p i r)
  have hlane : ∀ R : RegS, R.Inv → ∀ n : ℕ, FarApart 2 (regStrip p r R (n + R.m)) h.box :=
    fun R hRi n => (FarApart.symm' (machPieces_laneClear hp r h hh).farApart).mono
      (regStrip_subset hRi p r n) le_rfl
  have hTg := hv.TgE
  -- the order of the times
  have hR1 := le_routeEndX _ _ 2010 hv.timedR
  have hR2 := hv.endR
  have hM1 := le_routeEndX _ _ _ hv.timedM
  have hM2 := hv.endM
  have hT1 : (incPlan p i r).T1 = (incPlan p i r).T0l + (134 + (incPlan p i r).tl * 254) := rfl
  have heM : (incPlan p i r).eM = routeEndX (incPlan p i r).gM (incPlan p i r).csM
    (incPlan p i r).T1 := rfl
  unfold isep2IMov
  split_ifs with h1 h2
  · refine FarApart.union_left ?_ (hlane R0 hR.1 j)
    unfold isep2EMov
    split_ifs with h3 h4 h5
    · unfold linkFootW
      split_ifs with h6 h7
      · obtain ⟨c, cs, hcs⟩ : ∃ c cs, (incPlan p i r).csR = c :: cs := ⟨_, _, rfl⟩
        have hsep := isep_sepR hp hins
        have htim := hv.timedR
        have hlin := hv.linesR
        have hk : ∀ c' ∈ (incPlan p i r).csR, c'.k < 8 := by
          intro c' hc'
          rw [isep2_csR_eq hins] at hc'
          simp only [bandCorners, isep2SlabC, List.cons_append, List.nil_append, List.mem_cons,
            List.not_mem_nil, or_false] at hc'
          rcases hc' with rfl | rfl | rfl | rfl | rfl <;> simp
        rw [hcs] at hsep htim hlin hk h6 ⊢
        exact isep2_rfoot_far cs c _ 2010 hsep htim hlin hk j h6 h hh fun hm =>
          hn (hrI h (by rw [hcs]; exact hm))
      · have := isep2_flyR hp hins (2010 + j) (by omega) (by omega) h hh
        push_cast at this
        exact this
      · exact isep2_entry_far hp (a := p.length + r)
          (by unfold N R; push_cast; omega) (by rw [htlN]; exact htl.2) h hh
          fun hm => hn (hcI h hm)
    · obtain ⟨c, cs, hcs⟩ : ∃ c cs, (incPlan p i r).csM = c :: cs := ⟨_, _, rfl⟩
      have hsep := isep_sepM hp hins
      have htim := hv.timedM
      have hlin := hv.linesM
      have hk : ∀ c' ∈ (incPlan p i r).csM, c'.k < 8 := by
        intro c' hc'
        have hcM : (incPlan p i r).csM = mergeCorners p r (mergeE p r) := rfl
        rw [hcM, isep2_mergeCorners_eq] at hc'
        simp only [bandCorners, isep2PortC, List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl | rfl | rfl | rfl <;> simp
      have hj' : (incPlan p i r).T1 + (j - ((incPlan p i r).T1 - 2010)) ≤ (incPlan p i r).eM := by
        omega
      rw [heM, hcs] at hj'
      rw [hcs] at hsep htim hlin hk ⊢
      exact isep2_rfoot_far cs c _ _ hsep htim hlin hk _ hj' h hh fun hm =>
        hn (hmrI h (by rw [hcs]; exact hm))
    · have := isep2_flyM hp hins ((incPlan p i r).eM +
        (j - ((incPlan p i r).T1 - 2010 + ((incPlan p i r).eM - (incPlan p i r).T1))))
        (by omega) (by omega) h hh
      push_cast at this
      exact this
    · exact isep2_gate hp r h hh fun he => hn (he ▸ hgI)
  · refine FarApart.union_left ?_ (hlane _ (hR.later _).1 _)
    unfold modFootW
    split_ifs with h3 h4 h5
    · exact isep2_gate hp r h hh fun he => hn (he ▸ hgI)
    · exact isep2_fl1 hp r hTg _ (by omega) h4 h hh
    · exact isep2_rf hp r h hh fun he => hn (he ▸ hjI)
    · exact isep2_fl2 hp r hTg _ (by omega) h2 h hh
  · exact isep2_incRun hp hr ((hR.later _).later 946) _ h hh fun hm => hn (hmI h hm)

/-! ### The field `idle` -/

/-- **`IncSep.idle`**: the two threads are far from every idle piece of the machine. -/
theorem isep2_idle (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {R0 : RegS}
    (hR : R0.Ready) : ∀ j < (incPlan p i r).Tend - 2010, ∀ g ∈ machPieces p,
      g ∉ (incPlan p i r).LCraw ++ (incPlan p i r).LIraw →
        FarApart 2 ((incPlan p i r).contFoot j ∪ (incPlan p i r).incFoot R0 j) g.box := by
  intro j hj g hg hn
  have hnC : g ∉ (incPlan p i r).LCraw := fun h => hn (List.mem_append_left _ h)
  have hnI : g ∉ (incPlan p i r).LIraw := fun h => hn (List.mem_append_right _ h)
  rw [isep2_contFoot_eq]
  refine FarApart.union_left (FarApart.union_left ?_ (isep2_CMov_far hp hins j hj g hg hnC))
    ((FarApart.union_left ?_ (isep2_IMov_far hp hins hR j hj g hg hnI)).mono
      (isep2_incFoot_sub _ R0 j) le_rfl)
  · exact isep2_boxesOf_far hp (fun x hx => isep2_LC_mem hp hins x (mem_dd.1 hx)) hg
      fun h => hnC (mem_dd.1 h)
  · exact isep2_boxesOf_far hp (fun x hx => isep2_LI_mem hp hins x (mem_dd.1 hx)) hg
      fun h => hnI (mem_dd.1 h)

end LP

end LeanTheory.Life
