/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepProof3

/-!
# The flights at the units: into the side input of an entry copy, out of a chain

Research note `N-22`. The fields `flyC`, `flyR` and `outC` of `IncSep` (`ActivationIncStep`) in a
strong form, far from every piece of the machine:

* `isep2_unit_cases`: the pieces of a unit are the copies of its entry chain and the groups of
  its body (`v ≥ V_U + 213` and `x ≥ x_a + 118` or `y ≥ y_a + 104` in the unit frame);
* `isep2_mem_flyEntry`, `isep2_flyEntry`: a link whose last corner is the input corner of copy
  `t` of unit `a` (image `1`) and which arrives on the window of the copy flies `NE` along the
  side line `v = V_U + 76 - 99 t`; from the end of the corner window to `16` generations before
  the arrival it is above the gate of copy `t` (`y ≥ y_a - 64 t + 36`), right of the reflector of
  the corner (`x ≥ rfX + 3`), between the side lines of the copies `t ± 1`, and inside the slab
  of the unit (`u ∈ [A_a + C0 - 61 t + 13, A_a + 29 t + 6]`): far from every piece;
* `isep2_outC`: the flight from the output of copy `0` of an entry chain to the body input of
  the unit (`u = A_a + 14`, `y ≤ y_a + 101`, `x ≤ x_a + 115`) is far from every piece;
* `isep2_flyC`, `isep2_flyR`: the fields `flyC` and `flyR` for the plan `incPlan` of every
  `inc` instruction.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-! ### The pieces of a unit -/

/-- The groups of the `dec` body are right of `x = 118` or below `y = 104` (unit frame). -/
theorem isep2_bodyDec_xy (i : ℕ) (hi : i < 8) :
    118 ≤ (Base.bodyDec i).piece.a ∨ 104 ≤ (Base.bodyDec i).piece.lo := by
  interval_cases i <;>
    simp only [Base.piece, bodyDecPieces, bodyDecG0, bodyDecG1, bodyDecG2, bodyDecG3, bodyDecG4,
      bodyDecG5, bodyDecG6, bodyDecG7, List.getD_cons_zero, List.getD_cons_succ] <;> norm_num

/-- The groups of the `inc` body are right of `x = 118` (unit frame). -/
theorem isep2_bodyInc_xy (i : ℕ) (hi : i < 3) : 118 ≤ (Base.bodyInc i).piece.a := by
  interval_cases i <;>
    simp only [Base.piece, bodyIncPieces, bodyIncG0, bodyIncG1, bodyIncG2, List.getD_cons_zero,
      List.getD_cons_succ] <;> norm_num

/-- **The pieces of unit `a`, by class**: a copy `t < 2P` of the entry chain, or a group of the
body (below `v = V_U + 213`, right of `x_a + 118` or below `y_a + 104`, inside the slab). -/
theorem isep2_unit_cases (p : Program) (a : ℕ) {s : PSpec} (hs : s ∈ unitSpecs p a) :
    (∃ t < 2 * numPreds p,
      s = ⟨.orGate, unitDX p a - 35 * (t : ℤ), unitDY p a - 64 * (t : ℤ), 14 * t % 30⟩) ∨
    (VU p + 213 ≤ s.bx.a + s.bx.lo ∧
      (unitDX p a + 118 ≤ s.bx.a ∨ unitDY p a + 104 ≤ s.bx.lo) ∧
      A p a - 180 ≤ s.bx.a - s.bx.hi ∧ s.bx.b - s.bx.lo ≤ A p a + 212) := by
  have hd := unitD_uv p a
  unfold unitSpecs at hs
  rcases List.mem_append.1 hs with hs | hs
  · exact Or.inl (mem_chainSpecs hs)
  · right
    cases hk : unitKind p a <;> rw [hk] at hs <;> simp only [List.not_mem_nil] at hs
    · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      have := bodyDec_uv i (List.mem_range.1 hi)
      have := isep2_bodyDec_xy i (List.mem_range.1 hi)
      simp only [PSpec.bx_mk]
      omega
    · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      have := bodyInc_uv i (List.mem_range.1 hi)
      have := isep2_bodyInc_xy i (List.mem_range.1 hi)
      simp only [PSpec.bx_mk]
      omega

/-- The box of a copy of an entry chain. -/
theorem isep2_chain_box (dx dy : ℤ) (t ph : ℕ) :
    (PSpec.mk .orGate (dx - 35 * (t : ℤ)) (dy - 64 * (t : ℤ)) ph).piece.box =
      Box (dx - 35 * t) (dx - 35 * t + 90) (dy - 64 * t) (dy - 64 * t + 32) := by
  have hb := base_boxes
  rw [isep2_spec_box]
  congr 1 <;> omega

/-! ### The flight into the side input of an entry copy -/

/-- The input corner of entry copy `t` of unit `a`. -/
def isep2SlabC (p : Program) (a : ℕ) (t : ℤ) : Corner := ⟨1, destU p a t, destV p t, .slab a t⟩

/-- **A link into entry copy `t` of unit `a`, between the end of its last corner window and `16`
generations before its arrival, in coordinates.** -/
theorem isep2_mem_flyEntry {a t : ℕ} {g : WL} {bc : List Corner} {T : ℕ}
    (htim : RouteTimedX g (bc ++ [isep2SlabC p a t]) T) {δ k : ℤ} (hδ : δ = 4 ∨ δ = 5)
    (hfin : (route g (bc ++ [isep2SlabC p a t])).2 = (destWin p a t).shift 0 0 (δ + 30 * k))
    {T0 : ℕ} (hT0 : (T0 : ℤ) = 180 + 30 * k + 16 * (t : ℤ) % 30) {j : ℕ}
    (hj1 : routeEndX g (bc ++ [isep2SlabC p a t]) T ≤ j) (hj2 : j + 16 ≤ T0) {c : Cell}
    (hc : c ∈ (route g (bc ++ [isep2SlabC p a t])).2.box j) :
    A p a + unitC0 p a + 13 - 61 * t ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ A p a + 6 + 29 * t ∧
      VU p + 74 - 99 * t ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ VU p + 82 - 99 * t ∧
      unitDY p a + 36 - 64 * t ≤ c.2 ∧ c.1 ≤ unitDX p a + 42 - 35 * t ∧
      rfX 1 (destU p a t) (destV p t) + 3 ≤ c.1 := by
  have hd := unitD_uv p a
  have hA := A_even p a
  have hVU := VU_even p
  have hC := unitC0_cases p a
  have hend := routeEndX_snoc bc (isep2SlabC p a t) g T htim
  rw [hfin] at hend hc
  generalize routeEndX g (bc ++ [isep2SlabC p a t]) T = E at hend hj1
  obtain ⟨c1, c2, c3, c4⟩ := hc
  simp only [destWin, unitWL, sideWL, isep2SlabC, destU, destV, inCol, sideV, WL.shift, WL.px,
    WL.py, WL.qt, rfOut, rfX, rfCU, rfCV] at hend c1 c2 c3 c4 ⊢
  omega

/-- **`IncSep.flyC` / `flyR`, strong form, for any link into an entry copy**: from the end of
the window of its last corner (the input corner of copy `t` of unit `a`) to `16` generations
before its arrival on the window of the copy, the glider is far from every piece of the
machine. -/
theorem isep2_flyEntry (hp : p.WellFormed) {a t : ℕ} (ht : (t : ℤ) < 2 * P p) {g : WL}
    {bc : List Corner} {T : ℕ} (hcS : isep2SlabC p a t ∈ allCorners p)
    (htim : RouteTimedX g (bc ++ [isep2SlabC p a t]) T) {δ k : ℤ} (hδ : δ = 4 ∨ δ = 5)
    (hfin : (route g (bc ++ [isep2SlabC p a t])).2 = (destWin p a t).shift 0 0 (δ + 30 * k))
    {T0 : ℕ} (hT0 : (T0 : ℤ) = 180 + 30 * k + 16 * (t : ℤ) % 30) :
    ∀ j : ℕ, routeEndX g (bc ++ [isep2SlabC p a t]) T ≤ j → j + 16 ≤ T0 →
      ∀ h ∈ machPieces p, FarApart 2 ((route g (bc ++ [isep2SlabC p a t])).2.box j) h.box := by
  intro j hj1 hj2 h hh
  have hf := layout_facts p
  have hd := unitD_uv p a
  have hC := unitC0_cases p a
  have hS := fun c (hc : c ∈ (route g (bc ++ [isep2SlabC p a t])).2.box j) =>
    isep2_mem_flyEntry htim hδ hfin hT0 hj1 hj2 hc
  have hVU : VU p ≤ VT p - 1644 := by rw [hf.2.2.2.2.1]
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  rcases mem_machSpecs hs with ⟨a', ha', hs⟩ | ⟨r', hr', hs⟩ | ⟨c, hc, hb⟩
  · rcases lt_trichotomy a' a with h' | rfl | h'
    · -- an earlier unit: far left
      have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := a') (a' := a) (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
    · rcases isep2_unit_cases p a' hs with ⟨t', ht', rfl⟩ | ⟨h1, h2, h3, h4⟩
      · rw [isep2_chain_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        rcases lt_trichotomy t' t with h'' | rfl | h''
        · omega
        · omega
        · omega
      · rw [PSpec.piece_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
    · -- a later unit: far right
      have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := a) (a' := a') (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
  · -- a module piece: far below
    have hu := (moduleSpecs_uv p r' hs).1
    rw [PSpec.piece_box]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hu
    omega
  · -- a corner
    have hv := allCorners_valid hp c hc
    have hcu := corner_uv c
    rw [PSpec.piece_box, hb]
    by_cases hcS' : c = isep2SlabC p a t
    · -- the own input corner: the glider is right of its reflector
      subst hcS'
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      simp only [isep2SlabC, cornerSpec, PSpec.bx_mk, Base.piece, rfP] at this ⊢
      omega
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hcu
    obtain ⟨k, u, v, tag⟩ := c
    simp only at hcu
    cases tag with
    | band b n h' => simp only [Valid] at hv; omega
    | halt a'' => simp only [Valid] at hv; omega
    | slab a'' t' =>
      simp only [Valid] at hv
      have hC'' := unitC0_cases p a''.toNat
      rcases lt_trichotomy a'' a with h' | rfl | h'
      · have := A_add_le p h'
        omega
      · rcases lt_trichotomy t' t with h'' | rfl | h''
        · omega
        · exfalso
          refine hcS' (eq_of_tag (allCorners_tags hp) hc hcS ?_)
          simp only [isep2SlabC]
        · omega
      · have := A_add_le p h'
        omega
    | left r' idx => simp only [Valid] at hv; omega
    | right r' j' w => simp only [Valid] at hv; omega

/-! ### The flight out of an entry chain -/

/-- **The flight out of the chain of unit `a`, in coordinates**: `u = A_a + 14`, `x ≤ x_a + 115`,
`y ∈ [y_a + 56, y_a + 101]`. -/
theorem isep2_mem_outC (p : Program) (a : ℕ) {j : ℕ} (hj : j < 166) {c : Cell}
    (hc : c ∈ (fun c => (unitDX p a, unitDY p a) + c) '' chainOutWL.box (-166 + (j : ℤ))) :
    A p a + 10 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ A p a + 18 ∧ VU p + 126 ≤ c.1 + c.2 ∧
      c.1 + c.2 ≤ VU p + 216 ∧ c.1 ≤ unitDX p a + 115 ∧ unitDY p a + 56 ≤ c.2 ∧
      c.2 ≤ unitDY p a + 101 := by
  have hd := unitD_uv p a
  obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hc
  simp only [chainOutWL, WL.px, WL.py, WL.qt, Prod.fst_add, Prod.snd_add] at d1 d2 d3 d4 ⊢
  omega

/-- **`IncSep.outC`, strong form**: the flight from the output of copy `0` of the entry chain of
unit `a` to the body input is far from every piece of the machine. -/
theorem isep2_outC (hp : p.WellFormed) (a : ℕ) :
    ∀ j : ℕ, j < 166 → ∀ h ∈ machPieces p, FarApart 2
      ((fun c => (unitDX p a, unitDY p a) + c) '' chainOutWL.box (-166 + (j : ℤ))) h.box := by
  intro j hj h hh
  have hf := layout_facts p
  have hd := unitD_uv p a
  have hS := fun c hc => isep2_mem_outC p a hj (c := c) hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  rcases mem_machSpecs hs with ⟨a', ha', hs⟩ | ⟨r', hr', hs⟩ | ⟨c, hc, hb⟩
  · rcases lt_trichotomy a' a with h' | rfl | h'
    · have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := a') (a' := a) (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
    · rcases isep2_unit_cases p a' hs with ⟨t', ht', rfl⟩ | ⟨h1, h2, h3, h4⟩
      · rw [isep2_chain_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
      · rw [PSpec.piece_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
    · have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := a) (a' := a') (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
  · have hu := (moduleSpecs_uv p r' hs).1
    rw [PSpec.piece_box]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hu
    omega
  · have hv := allCorners_valid hp c hc
    have hcu := corner_uv c
    rw [PSpec.piece_box, hb]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hcu
    obtain ⟨k, u, v, tag⟩ := c
    simp only at hcu
    cases tag with
    | band b n h' => simp only [Valid] at hv; omega
    | halt a'' => simp only [Valid] at hv; omega
    | slab a'' t' =>
      simp only [Valid] at hv
      have hC'' := unitC0_cases p a''.toNat
      rcases lt_trichotomy a'' a with h' | rfl | h'
      · have := A_add_le p h'
        omega
      · omega
      · have := A_add_le p h'
        omega
    | left r' idx => simp only [Valid] at hv; omega
    | right r' j' w => simp only [Valid] at hv; omega

/-! ### The fields `flyC`, `flyR`, `outC` for the plan of an `inc` instruction -/

/-- The corners of the continue: its band corners, then the input corner of its entry copy. -/
theorem isep2_csC_eq (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    (incPlan p i r).csC = bandCorners p (instrBand i) 0 (incCc p i)
      (hairCont p (incG p i r) (incEc p i r) (incCc p i))
      (destU p (i + 1) ((incPlan p i r).tc : ℤ)) 3 6 ++
        [isep2SlabC p (i + 1) (incPlan p i r).tc] := by
  have htc : incTc p i = (((incTc p i).toNat : ℕ) : ℤ) :=
    (Int.toNat_of_nonneg (incTc_range hp hins).1).symm
  change incMkc p i (incG p i r) (incEc p i r) = _
  unfold incMkc upCorners upCornersK isep2SlabC
  rw [htc]
  rfl

/-- The corners of the INC link: its band corners, then the input corner of its entry copy. -/
theorem isep2_csR_eq (hins : p[i]? = some (.inc r)) :
    (incPlan p i r).csR = bandCorners p (instrBand i) 1 (incCl p i)
      (hairReg p 1 (incEl p i r) (incCl p i))
      (destU p (p.length + r) ((incPlan p i r).tl : ℤ)) 3 6 ++
        [isep2SlabC p (p.length + r) (incPlan p i r).tl] := by
  have htl : incTl p i r = (((incTl p i r).toNat : ℕ) : ℤ) :=
    (Int.toNat_of_nonneg (incTl_range hins).1).symm
  change incMkl p i r (incEl p i r) = _
  unfold incMkl upCorners upCornersK isep2SlabC
  rw [htl]
  rfl

/-- **`IncSep.flyC`, strong form** (far from every piece of the machine). -/
theorem isep2_flyC (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j : ℕ, routeEndX (unitWL p i incDWL) (incPlan p i r).csC 2010 ≤ j →
      j + 16 ≤ (incPlan p i r).T0c → ∀ h ∈ machPieces p,
        FarApart 2 ((route (unitWL p i incDWL) (incPlan p i r).csC).2.box j) h.box := by
  have hv := incPlan_valid hp hins
  have hi : i < p.length := (List.getElem?_eq_some_iff.1 hins).1
  have hcs := isep2_csC_eq hp hins
  have ht := incTc_range hp hins
  have htc : ((incPlan p i r).tc : ℤ) = incTc p i := Int.toNat_of_nonneg ht.1
  have hcS : isep2SlabC p (i + 1) (incPlan p i r).tc ∈ allCorners p :=
    instrRoute_corner hi (x := (unitWL p i incDWL, (incPlan p i r).csC))
      (by rw [isep_instrSpecs hins]; exact List.mem_cons_self) _ (by rw [hcs]; simp)
  have htim := hv.timedC
  have hfin := hv.finC
  rw [hcs] at htim hfin ⊢
  exact isep2_flyEntry hp (by rw [htc]; exact ht.2) hcS htim hv.δcR hfin hv.T0cE

/-- **`IncSep.flyR`, strong form** (far from every piece of the machine). -/
theorem isep2_flyR (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j : ℕ, routeEndX (unitWL p i incRWL) (incPlan p i r).csR 2010 ≤ j →
      j + 16 ≤ (incPlan p i r).T0l → ∀ h ∈ machPieces p,
        FarApart 2 ((route (unitWL p i incRWL) (incPlan p i r).csR).2.box j) h.box := by
  have hv := incPlan_valid hp hins
  have hi : i < p.length := (List.getElem?_eq_some_iff.1 hins).1
  have hcs := isep2_csR_eq hins
  have ht := incTl_range hins
  have htl : ((incPlan p i r).tl : ℤ) = incTl p i r := Int.toNat_of_nonneg ht.1
  have hcS : isep2SlabC p (p.length + r) (incPlan p i r).tl ∈ allCorners p :=
    instrRoute_corner hi (x := (unitWL p i incRWL, (incPlan p i r).csR))
      (by rw [isep_instrSpecs hins]; exact List.mem_cons_of_mem _ List.mem_cons_self) _
      (by rw [hcs]; simp)
  have htim := hv.timedR
  have hfin := hv.finR
  rw [hcs] at htim hfin ⊢
  exact isep2_flyEntry hp (by rw [htl]; exact ht.2) hcS htim hv.δlR hfin hv.T0lE

end LP

end LeanTheory.Life
