/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncSepProof2

/-!
# The merge link's flight to the INC gate

Research note `N-22`. The field `flyM` of `IncSep` (`ActivationIncStep`) in a strong form: from
the end of the corner window of the INC port corner (`eM`) to `16` generations before the gate
(`Tg`), the merge glider flies `NE` along the port line `v = -2347` of module `r`, far from every
piece of the machine (`isep2_flyM`):

* `isep2_mem_flyM`: its glider box lies in `u ∈ [U_r + incChan + 11, U_r + 165]`,
  `v ∈ [-2349, -2341]`, below the INC gate (`y ≥ y_r - 1255`) and above the reflector of the port
  corner (`y ≤ rfY - 2`);
* the pieces: units and band corners far above, other modules far beside, the pieces of module
  `r` beside the port line (the register circuit at `v ≥ -2324`, the gate at `y ≤ y_r - 1259`),
  the port corners of the other left-zone channels on their port lines (`LeftPort`), and the port
  corner of the INC channel itself (the last corner of the merge link, by the uniqueness of tags).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-- The INC port corner of module `r`, the last corner of the merge link. -/
def isep2PortC (p : Program) (r : ℕ) : Corner :=
  ⟨4, U p r + incChan p, incPortV, .left r (2 * D p)⟩

/-- The merge corners are the band corners followed by the port corner. -/
theorem isep2_mergeCorners_eq (p : Program) (r : ℕ) (e : ℤ) :
    mergeCorners p r e = bandCorners p (mergeBand p r) 0 (A p (p.length + r) + haltD)
      (hairReg p 0 e (A p (p.length + r) + haltD)) (U p r + incChan p) 3 2 ++
        [isep2PortC p r] := rfl

/-- The port corner is a corner of the machine (for a register with an `inc`). -/
theorem isep2_portC_mem (hins : p[i]? = some (.inc r)) : isep2PortC p r ∈ allCorners p :=
  mergeRoute_corner (lt_numRegs_of_inc hins) (mergeUsed_of_inc hins)
    (x := (unitWL p (p.length + r) haltDWL, mergeCorners p r (mergeE p r)))
    (by simp [mergeSpecs]) _ (by simp [isep2_mergeCorners_eq])

/-- **The merge glider between the port corner and the gate, in coordinates.** -/
theorem isep2_mem_flyM (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) {j : ℕ}
    (hj1 : (incPlan p i r).eM ≤ j) (hj2 : j + 16 ≤ (incPlan p i r).Tg) {c : Cell}
    (hc : c ∈ ((route (incPlan p i r).gM (incPlan p i r).csM).2).box j) :
    U p r + incChan p + 11 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r + 165 ∧ -2349 ≤ c.1 + c.2 ∧
      c.1 + c.2 ≤ -2341 ∧ modDY p r - 1255 ≤ c.2 ∧
      c.2 ≤ rfY 4 (U p r + incChan p) incPortV - 2 := by
  have hv := incPlan_valid hp hins
  have hU := U_even p r
  have hc0 := incChan_even p
  have hend := routeEndX_snoc (bandCorners p (mergeBand p r) 0 (A p (p.length + r) + haltD)
      (hairReg p 0 (mergeE p r) (A p (p.length + r) + haltD)) (U p r + incChan p) 3 2)
    (isep2PortC p r) (incPlan p i r).gM (incPlan p i r).T1 hv.timedM
  have hfin := hv.finM
  have hTg := hv.TgE
  have hδ := hv.δmR
  change ((incPlan p i r).eM : ℤ) = (route (incPlan p i r).gM (incPlan p i r).csM).2.tau -
    (rfOut 4).tau + 4 * (rfOut 4).dx * rfX 4 (U p r + incChan p) incPortV - 20 at hend
  rw [hfin] at hend hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  simp only [modWL, incWin, WL.shift, WL.px, WL.py, WL.qt, rfOut, rfX, rfY, rfCU, rfCV,
    incPortV, modDX, modDY] at hend c1 c2 c3 c4 ⊢
  omega

/-- **`IncSep.flyM`, strong form**: the merge link's flight from the end of the corner window of
the port corner to `16` generations before the INC gate (included) is far from every piece of
the machine. -/
theorem isep2_flyM (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    ∀ j : ℕ, (incPlan p i r).eM ≤ j → j + 16 ≤ (incPlan p i r).Tg → ∀ h ∈ machPieces p,
      FarApart 2 (((route (incPlan p i r).gM (incPlan p i r).csM).2).box j) h.box := by
  intro j hj1 hj2 h hh
  have hm := modD_uv p r
  have hf := layout_facts p
  have hD := one_le_D p
  have hU := U_even p r
  have hc0 := incChan_even p
  have hcb : U p r + modLeft p + 29 ≤ U p r + incChan p ∧ U p r + incChan p ≤ U p r - 793 :=
    left_range p (r := r) (idx := 2 * D p) ⟨by omega, by omega⟩
      (by have := fixp_bounds (uL - 62 * (2 * D p)) (1 - incPortV % 2)
          unfold incChan leftChan uL at *; omega)
  have hS := fun c (hc : c ∈ ((route (incPlan p i r).gM (incPlan p i r).csM).2).box j) =>
    isep2_mem_flyM hp hins hj1 hj2 hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  rcases mem_machSpecs hs with ⟨a, ha, hs⟩ | ⟨r', hr', hs⟩ | ⟨c, hc, hb⟩
  · -- a unit piece: far above
    have hu := unitSpecs_uv p a hs
    rw [PSpec.piece_box]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hu
    omega
  · by_cases hrr : r' = r
    · subst hrr
      have hb := base_boxes
      rcases isep2_mod_cases p r' hs with ⟨i', hi', rfl⟩ | rfl | rfl | h1 | h1 | h1 | h1
      · have := (isep2_dz2g_uv i' hi').1
        rw [isep2_spec_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
      · rw [isep2_spec_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
      · rw [incGateSpec, isep2_spec_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
      all_goals
        rw [PSpec.piece_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        unfold modLeft at hcb
        omega
    · -- another module: far beside
      have hu := (moduleSpecs_uv p r' hs).1
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      rcases lt_or_gt_of_ne hrr with h' | h'
      · have := module_gap p (r := r') (r' := r) (by exact_mod_cast h')
        unfold modLeft modRight at *
        omega
      · have := module_gap p (r := r) (r' := r') (by exact_mod_cast h')
        unfold modLeft modRight at *
        omega
  · -- a corner of a route
    have hd := allCorners_desc hp c hc
    have hcu := corner_uv c
    rw [PSpec.piece_box, hb]
    by_cases hcP : c = isep2PortC p r
    · -- the port corner itself: the glider is below its reflector
      subst hcP
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      simp only [isep2PortC, cornerSpec, PSpec.bx_mk, Base.piece, rfP, rfX, rfY, rfCU, rfCV,
        incPortV] at this ⊢
      omega
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    obtain ⟨hv, -, -, hlp⟩ := hd
    unfold BoxT.InUV at hcu
    obtain ⟨k, u, v, tag⟩ := c
    simp only at hcu hlp
    cases tag with
    | band b n h' => simp only [Valid] at hv; omega
    | halt a' => simp only [Valid] at hv; omega
    | slab a' t => simp only [Valid] at hv; omega
    | left r' idx =>
      simp only [Valid] at hv
      rcases lt_trichotomy r' r with h' | rfl | h'
      · have := module_gap p (r := r') (r' := r) h'
        unfold modLeft modRight at *; omega
      · rcases hlp r idx rfl with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨j', h1, h2, h3, h4⟩ |
          ⟨j', h1, h2, h3, h4⟩
        · unfold decPortV at h3; omega
        · exfalso
          refine hcP (eq_of_tag (allCorners_tags hp) hc (isep2_portC_mem hins) ?_)
          simp only [isep2PortC, h1]
        · unfold nzTokPortV at h4; omega
        · unfold nzAnsPortV at h4; omega
      · have := module_gap p (r := r) (r' := r') h'
        unfold modLeft modRight at *; omega
    | right r' j' w =>
      simp only [Valid] at hv
      rcases lt_trichotomy r' r with h' | rfl | h'
      · have := module_gap p (r := r') (r' := r) h'
        unfold modLeft modRight at *; omega
      · omega
      · have := module_gap p (r := r) (r' := r') h'
        unfold modLeft modRight at *; omega

end LP

end LeanTheory.Life
