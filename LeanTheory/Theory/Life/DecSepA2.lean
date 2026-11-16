/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepA1

/-!
# Routes of a `decJz` activation far from the pieces that are not their reflectors

Research note `N-22`. Under the route separation `RouteSepX` (proved for the five routes of a
`decJz` instruction: `dsep_sepC`, `dsep_sepN`, `dsep_sepZ`, `dsep_sepAN`, `dsep_sepAZ`), the
footprint of a route with corner windows is far from every piece of the machine that is not one of
its reflectors (`isep2_rfoot_far`). A piece is not a reflector of a route:

* `dsepA_not_refl_tag`: if it is the reflector of a corner whose tag differs from the tags of all
  corners of the route (`corner_gap`: corners with distinct tags are `≥ 56` apart);
* `dsepA_not_refl_zone`: if its box has a cell in the zone of a module (no reflector of the machine
  there, `dsepM_corner_far`);
* `dsepA_not_refl_wide`: if its box is wider than `22` (the reflectors are `8` or `22` wide).

`dsepA_routeC_far`, `dsepA_routeN_far`, `dsepA_routeZ_far`: the footprints of `C`, `KNZ`, `KZ` up
to the end of their routes; `dsepA_routeAN_far`, `dsepA_routeAZ_far`: the answer links.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Not a reflector -/

/-- Two equal nonempty boxes have equal bounds. -/
theorem dsepA_box_eq {a b lo hi a' b' lo' hi' : ℤ} (hn : a ≤ b ∧ lo ≤ hi)
    (e : Box a b lo hi = Box a' b' lo' hi') : a = a' ∧ b = b' ∧ lo = lo' ∧ hi = hi' := by
  have h1 : (a, lo) ∈ Box a' b' lo' hi' := e ▸ ⟨le_rfl, hn.1, le_rfl, hn.2⟩
  have h2 : (b, hi) ∈ Box a' b' lo' hi' := e ▸ ⟨hn.1, le_rfl, hn.2, le_rfl⟩
  obtain ⟨x1, x2, x3, x4⟩ := h1
  obtain ⟨y1, y2, y3, y4⟩ := h2
  have h3 : (a', lo') ∈ Box a b lo hi := e.symm ▸ ⟨le_rfl, by simp only at *; omega, le_rfl,
    by simp only at *; omega⟩
  have h4 : (b', hi') ∈ Box a b lo hi := e.symm ▸ ⟨by simp only at *; omega, le_rfl,
    by simp only at *; omega, le_rfl⟩
  obtain ⟨z1, z2, z3, z4⟩ := h3
  obtain ⟨w1, w2, w3, w4⟩ := h4
  simp only at *
  omega

/-- The box of the reflector of a corner is nonempty. -/
theorem dsepA_corner_ne (c : Corner) :
    (cornerSpec c).bx.a ≤ (cornerSpec c).bx.b ∧ (cornerSpec c).bx.lo ≤ (cornerSpec c).bx.hi := by
  have := dsepT_base_ne (Base.rf c.k)
  simp only [cornerSpec, PSpec.bx]
  omega

/-- **A reflector of a corner of the machine is not a reflector of a route whose corners have
other tags.** -/
theorem dsepA_not_refl_tag (hp : p.WellFormed) {g : WL} {cs : List Corner}
    (hcs : ∀ c ∈ cs, c ∈ allCorners p) {c' : Corner} (hc' : c' ∈ allCorners p)
    (htag : ∀ c ∈ cs, c.tag ≠ c'.tag) {h : Piece}
    (hb : h.box = Box (cornerSpec c').bx.a (cornerSpec c').bx.b (cornerSpec c').bx.lo
      (cornerSpec c').bx.hi) : h ∉ reflP g cs := by
  intro hm
  obtain ⟨c, hc, hb2⟩ := dsepM_reflP_mem hm
  have hgap := corner_gap p (allCorners_valid hp c (hcs c hc)) (allCorners_valid hp c' hc')
    (htag c hc)
  have h1 := corner_uv c
  have h2 := corner_uv c'
  rw [hb] at hb2
  obtain ⟨e1, e2, e3, e4⟩ := dsepA_box_eq (dsepA_corner_ne c') hb2
  have hn := dsepA_corner_ne c'
  unfold BoxT.InUV at h1 h2
  omega

/-- **A piece with a cell in the zone of module `r'` is not a reflector of any route of the
machine.** -/
theorem dsepA_not_refl_zone (hp : p.WellFormed) (r' : ℕ) {g : WL} {cs : List Corner}
    (hcs : ∀ c ∈ cs, c ∈ allCorners p) {h : Piece} {x : Cell} (hx : x ∈ h.box)
    (hz : U p r' - 760 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r' + 1300 + 144 * D p ∧
      -4100 - 198 * D p ≤ x.1 + x.2 ∧ (x.1 - x.2 ≤ U p r' + 1170 ∨ x.1 + x.2 ≤ 1450)) :
    h ∉ reflP g cs := by
  intro hm
  obtain ⟨c, hc, hb⟩ := dsepM_reflP_mem hm
  have hf := dsepM_corner_far hp r' (S := {x}) (fun y hy => by
    rw [Set.mem_singleton_iff.1 hy]; exact hz) (hcs c hc)
  rw [hb] at hx
  exact hf x rfl x hx ⟨by omega, by omega, by omega, by omega⟩

/-- The reflectors are at most `22` wide. -/
theorem dsepA_rf_width (k : ℕ) : (Base.rf k).piece.b ≤ (Base.rf k).piece.a + 22 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp [Base.piece, rfP]

/-- **A piece wider than `22` is not a reflector of a route.** -/
theorem dsepA_not_refl_wide {g : WL} {cs : List Corner} {h : Piece}
    (hn : h.a ≤ h.b ∧ h.lo ≤ h.hi) (hw : h.a + 23 ≤ h.b) : h ∉ reflP g cs := by
  intro hm
  obtain ⟨c, -, hb⟩ := dsepM_reflP_mem hm
  obtain ⟨e1, e2, -, -⟩ := dsepA_box_eq hn hb
  have := dsepA_rf_width c.k
  simp only [cornerSpec, PSpec.bx] at e1 e2
  omega

/-! ### The routes far from the pieces that are not their reflectors -/

/-- The footprint of a flight before the end of its route is the route footprint. -/
theorem dsepA_flyFoot_route {g : WL} {cs : List Corner} {T t : ℕ}
    (ht : t ≤ routeEndX g cs T) : flyFoot g cs T t = routeFootX g cs T (t - T) := by
  simp only [flyFoot, ht, ↓reduceIte]

/-- **The route of `C`** is far from every piece of the machine that is not one of its
reflectors. -/
theorem dsepA_routeC_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (h1 : t ≤ routeEndX (unitWL p i decRWL) (decCornC p i r) 4260)
    {h : Piece} (hh : h ∈ machPieces p) (hn : h ∉ reflP (unitWL p i decRWL) (decCornC p i r)) :
    FarApart 2 (flyFoot (unitWL p i decRWL) (decCornC p i r) 4260 t) h.box := by
  rw [dsepA_flyFoot_route h1]
  exact isep2_rfoot_far _ _ _ _ (dsep_sepC hp hi) (decC_timedX p hi) (decC_lines p i r).1
    (by simp) (t - 4260)
    (show 4260 + (t - 4260) ≤ routeEndX _ (decCornC p i r) 4260 by omega) h hh hn

/-- **The route of `KNZ`** is far from every piece of the machine that is not one of its
reflectors. -/
theorem dsepA_routeN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (h1 : t ≤ routeEndX (unitWL p i decLWL) (decCornN p i r) 4260)
    {h : Piece} (hh : h ∈ machPieces p) (hn : h ∉ reflP (unitWL p i decLWL) (decCornN p i r)) :
    FarApart 2 (flyFoot (unitWL p i decLWL) (decCornN p i r) 4260 t) h.box := by
  rw [dsepA_flyFoot_route h1]
  exact isep2_rfoot_far _ _ _ _ (dsep_sepN hp hi) (decKNZ_timedX p hi) (decKNZ_lines p i r).1
    (by simp) (t - 4260)
    (show 4260 + (t - 4260) ≤ routeEndX _ (decCornN p i r) 4260 by omega) h hh hn

/-- **The route of `KZ`** is far from every piece of the machine that is not one of its
reflectors. -/
theorem dsepA_routeZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (h1 : t ≤ routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260)
    {h : Piece} (hh : h ∈ machPieces p) (hn : h ∉ reflP (unitWL p i decDWL) (decCornZ p i r)) :
    FarApart 2 (flyFoot (unitWL p i decDWL) (decCornZ p i r) 4260 t) h.box := by
  rw [dsepA_flyFoot_route h1]
  exact isep2_rfoot_far _ _ _ _ (dsep_sepZ hp hi) (decKZ_timedX p hi) (decKZ_lines p i r)
    (by simp) (t - 4260)
    (show 4260 + (t - 4260) ≤ routeEndX _ (decCornZ p i r) 4260 by omega) h hh hn

/-- **The route of the NZ answer** is far from every piece of the machine that is not one of its
reflectors. -/
theorem dsepA_routeAN_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {k : ℕ}
    (h1 : decDispN p i r + k ≤ routeEndX (decGN p i r) (decCsN p i r) (decDispN p i r))
    {h : Piece} (hh : h ∈ machPieces p) (hn : h ∉ reflP (decGN p i r) (decCsN p i r)) :
    FarApart 2 (routeFootX (decGN p i r) (decCsN p i r) (decDispN p i r) k) h.box := by
  have hD : ((decDispN p i r : ℕ) : ℤ) = decShift p i r + 11042 + 288 *
      (callerIdx p r i : ℤ) := by
    obtain ⟨h, -, -⟩ := decTS_facts p hi
    simp only [decDispN]; push_cast; omega
  obtain ⟨hl, htim, -, -, -⟩ := decAnsN_plan hp hi _ hD
  exact isep2_rfoot_far _ _ _ _ (dsep_sepAN hp hi) htim hl
    (by simp [upCornersK, bandCorners]) k h1 h hh hn

/-- **The route of the Z answer** is far from every piece of the machine that is not one of its
reflectors. -/
theorem dsepA_routeAZ_far (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {k : ℕ}
    (h1 : decDispZ p i r + k ≤ routeEndX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r))
    {h : Piece} (hh : h ∈ machPieces p) (hn : h ∉ reflP (decGZ p i r) (decCsZ p i r z)) :
    FarApart 2 (routeFootX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) k) h.box := by
  have hD : ((decDispZ p i r : ℕ) : ℤ) = decShift p i r + 13062 + 288 *
      (callerIdx p r i : ℤ) := by
    obtain ⟨h, -, -⟩ := decTS_facts p hi
    simp only [decDispZ]; push_cast; omega
  obtain ⟨hl, htim, -, -, -⟩ := decAnsZ_plan hp hi _ hD
  exact isep2_rfoot_far _ _ _ _ (dsep_sepAZ hp hi) htim hl
    (by simp [upCornersK, bandCorners]) k h1 h hh hn

end LP

end LeanTheory.Life
