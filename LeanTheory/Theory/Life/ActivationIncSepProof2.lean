/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RouteSep6
public import LeanTheory.Theory.Life.LaneSep2
public import LeanTheory.Theory.Life.ActivationIncSepProof
public import LeanTheory.Theory.Life.ActivationIncEntrySep

/-!
# The module fields of `IncSep`

Research note `N-22`. The fields of `IncSep` (`ActivationIncStep`) that live in module `r` of the
register of the `inc` instruction, in a stronger form: **far from every piece of the machine**
(not only from the pieces of the thread), except the piece(s) active in the footprint:

* `isep2_far_box`: a set is far from a box if every cell is `≥ 3` beside it in `x` or `y`, or
  `≥ 6` beside its `uv`-hull;
* `isep2_modLocal`: a set inside the `u`-band of module `r` (`[U_r - 760, U_r + 1170]`), below
  `v = -3299` and above `v = 1200` only in the lanes of the register, is far from every piece of
  the machine except, possibly, the register circuit, `RF_J` and the INC gate of the module (the
  units and the band are far above, the other modules far beside, the zone corners, the DEC
  chain, the stations and the eaters of the module beside or above it);
* `isep2_dz2g_uv`: the `uv`-hulls of the `28` groups of the register circuit are `≥ 6` from the
  INC gate box, the extended relay box of `RF_J` and the two flights of the module part;
* the fields: `isep2_gate` (the gate box), `isep2_rf` (the extended relay box of `RF_J`),
  `isep2_fl1` (the flight from the gate to `RF_J`), `isep2_fl2` (the flight from `RF_J` to the
  increment), `isep2_incRun` (the increment, for every ready register and every generation, far
  from every piece outside the register circuit: the run regions `dz2e*RegL`, `dz2jRegL`
  component by component against the gate and `RF_J`), `isep2_flyM` (the merge link's flight
  from its port corner to `16` generations before the gate, along `v = -2347`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program}

/-! ### Far from a box, pointwise -/

/-- **A set is far from a box** if every cell is `≥ 3` beside it in `x` or `y`, or `≥ 6` beside
its `uv`-hull. -/
theorem isep2_far_box {S : Set Cell} {a b lo hi : ℤ}
    (h : ∀ c ∈ S, c.1 + 3 ≤ a ∨ b + 3 ≤ c.1 ∨ c.2 + 3 ≤ lo ∨ hi + 3 ≤ c.2 ∨
      c.1 - c.2 + 6 ≤ a - hi ∨ b - lo + 6 ≤ c.1 - c.2 ∨ c.1 + c.2 + 6 ≤ a + lo ∨
      b + hi + 6 ≤ c.1 + c.2) :
    FarApart 2 S (Box a b lo hi) := by
  intro x hx y ⟨y1, y2, y3, y4⟩ ⟨n1, n2, n3, n4⟩
  have := h x hx
  push_cast at n1 n2 n3 n4
  omega

/-- The box of a placed spec, unfolded. -/
theorem isep2_spec_box (g : Base) (vx vy : ℤ) (ph : ℕ) :
    (PSpec.mk g vx vy ph).piece.box =
      Box (g.piece.a + vx) (g.piece.b + vx) (g.piece.lo + vy) (g.piece.hi + vy) := rfl

/-! ### The pieces of a module -/

/-- **The pieces of module `r`, by class**: a group of the register circuit, `RF_J`, the INC
gate, or a piece of the DEC chain (`v ≤ -3305`), of a station NZ (`u ≤ U_r - 353`,
`v ≥ 1209`), of a station Z (`u ≥ U_r + 1182`), or an eater (`u ≤ U_r - 388`, `v ≥ 1517`, or
`u ≥ U_r + 1488`). -/
theorem isep2_mod_cases (p : Program) (r : ℕ) {s : PSpec} (hs : s ∈ moduleSpecs p r) :
    (∃ i < 28, s = ⟨.dz2g i, modDX p r, modDY p r, 0⟩) ∨
      s = ⟨.rf 4, modDX p r - 850, modDY p r - 1044, 25⟩ ∨ s = incGateSpec p r ∨
      s.bx.b + s.bx.hi ≤ -3305 ∨
      (s.bx.b - s.bx.lo ≤ U p r - 353 ∧ 1209 ≤ s.bx.a + s.bx.lo) ∨
      U p r + 1182 ≤ s.bx.a - s.bx.hi ∨
      (s.bx.b - s.bx.lo ≤ U p r - 388 ∧ 1517 ≤ s.bx.a + s.bx.lo) := by
  have hb := base_boxes
  have hm := modD_uv p r
  have hD := one_le_D p
  have hD' : (D p) = (numCallers p : ℤ) := rfl
  unfold moduleSpecs at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ((((hs | hs | hs) | hs) | hs) | hs) | hs | hs
  · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    exact Or.inl ⟨i, List.mem_range.1 hi, rfl⟩
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (Or.inl hs))
  · obtain ⟨m, hm', rfl⟩ := mem_decChainSpecs hs
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    simp only [PSpec.bx_mk]
    omega
  · obtain ⟨j, hj, i, hi, rfl⟩ := mem_stationSpecs hs
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    have := stNZ_cases i hi
    simp only [PSpec.bx_mk]
    omega
  · obtain ⟨j, hj, i, hi, rfl⟩ := mem_stationZSpecs hs
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    have := stZ_cases i hi
    simp only [PSpec.bx_mk]
    omega
  · subst hs
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    simp only [PSpec.bx_mk]
    omega
  · subst hs
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    simp only [PSpec.bx_mk]
    omega

/-- **A set in the `u`-band of module `r`, below the band**, is far from every piece of the
machine except, possibly, the groups of the register circuit, `RF_J` and the INC gate of module
`r`, which are checked by the hypotheses (each is in the exception list `E` or far). -/
theorem isep2_modLocal (hp : p.WellFormed) (r : ℕ) {S : Set Cell} {E : List Piece}
    (hS : ∀ c ∈ S, U p r - 760 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r + 1170 ∧ -3299 ≤ c.1 + c.2 ∧
      (c.1 + c.2 ≤ 1200 ∨ (U p r - 113 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r - 69)))
    (hz : ∀ i < 28, (PSpec.mk (.dz2g i) (modDX p r) (modDY p r) 0).piece ∈ E ∨
      FarApart 2 S (PSpec.mk (.dz2g i) (modDX p r) (modDY p r) 0).piece.box)
    (hj : rfJP p r ∈ E ∨ FarApart 2 S (rfJP p r).box)
    (hg : gateP p r ∈ E ∨ FarApart 2 S (gateP p r).box) :
    ∀ h ∈ machPieces p, h ∉ E → FarApart 2 S h.box := by
  intro h hh hn
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  have hf := layout_facts p
  have hm := modD_uv p r
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
      rcases isep2_mod_cases p r' hs with ⟨i, hi, rfl⟩ | rfl | rfl | h1 | h1 | h1 | h1
      · rcases hz i hi with h2 | h2
        · exact absurd h2 hn
        · exact h2
      · rcases hj with h2 | h2
        · exact absurd h2 hn
        · exact h2
      · rcases hg with h2 | h2
        · exact absurd h2 hn
        · exact h2
      all_goals
        rw [PSpec.piece_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
    · -- another module: far beside
      have hu := (moduleSpecs_uv p r' hs).1
      have hD := one_le_D p
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
    have hv := allCorners_valid hp c hc
    have hcu := corner_uv c
    rw [PSpec.piece_box, hb]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hcu
    obtain ⟨k, u, v, tag⟩ := c
    simp only at hcu
    cases tag with
    | band b n h' => simp only [Valid] at hv; omega
    | halt a' => simp only [Valid] at hv; omega
    | slab a' t => simp only [Valid] at hv; omega
    | left r' idx =>
      simp only [Valid] at hv
      rcases lt_trichotomy r' r with h' | rfl | h'
      · have := module_gap p (r := r') (r' := r) h'
        unfold modLeft modRight at *; omega
      · omega
      · have := module_gap p (r := r) (r' := r') h'
        unfold modLeft modRight at *; omega
    | right r' j w =>
      simp only [Valid] at hv
      rcases lt_trichotomy r' r with h' | rfl | h'
      · have := module_gap p (r := r') (r' := r) h'
        unfold modLeft modRight at *; omega
      · omega
      · have := module_gap p (r := r) (r' := r') h'
        unfold modLeft modRight at *; omega

/-! ### The register circuit -/

/-- **The groups of the register circuit** (module frame): their `uv`-hulls lie at
`v ≥ -2324`, and are `≥ 6` from the gate box (`u ∈ [99, 249]`, `v ∈ [-2423, -2273]`), from the
extended relay box of `RF_J` (`u ∈ [156, 201]`, `v ∈ [-1929, -1884]`), from the flight from the
gate to `RF_J` (`u ∈ [169, 177]`, `v ∈ [-2297, -1921]`) and from the flight from `RF_J` to the
increment (`u ∈ [184, 200]`, `v ∈ [-1912, -1904]`). -/
theorem isep2_dz2g_uv (i : ℕ) (hi : i < 28) :
    -2324 ≤ (Base.dz2g i).piece.a + (Base.dz2g i).piece.lo ∧
    ((Base.dz2g i).piece.b - (Base.dz2g i).piece.lo + 6 ≤ 99 ∨
      249 + 6 ≤ (Base.dz2g i).piece.a - (Base.dz2g i).piece.hi ∨
      (Base.dz2g i).piece.b + (Base.dz2g i).piece.hi + 6 ≤ -2423 ∨
      -2273 + 6 ≤ (Base.dz2g i).piece.a + (Base.dz2g i).piece.lo) ∧
    ((Base.dz2g i).piece.b - (Base.dz2g i).piece.lo + 6 ≤ 156 ∨
      201 + 6 ≤ (Base.dz2g i).piece.a - (Base.dz2g i).piece.hi ∨
      (Base.dz2g i).piece.b + (Base.dz2g i).piece.hi + 6 ≤ -1929 ∨
      -1884 + 6 ≤ (Base.dz2g i).piece.a + (Base.dz2g i).piece.lo) ∧
    ((Base.dz2g i).piece.b - (Base.dz2g i).piece.lo + 6 ≤ 169 ∨
      177 + 6 ≤ (Base.dz2g i).piece.a - (Base.dz2g i).piece.hi ∨
      (Base.dz2g i).piece.b + (Base.dz2g i).piece.hi + 6 ≤ -2297 ∨
      -1921 + 6 ≤ (Base.dz2g i).piece.a + (Base.dz2g i).piece.lo) ∧
    ((Base.dz2g i).piece.b - (Base.dz2g i).piece.lo + 6 ≤ 184 ∨
      200 + 6 ≤ (Base.dz2g i).piece.a - (Base.dz2g i).piece.hi ∨
      (Base.dz2g i).piece.b + (Base.dz2g i).piece.hi + 6 ≤ -1912 ∨
      -1904 + 6 ≤ (Base.dz2g i).piece.a + (Base.dz2g i).piece.lo) := by
  interval_cases i <;>
    simp only [Base.piece, dz2gPieces, dz2gG0, dz2gG1, dz2gG2, dz2gG3, dz2gG4, dz2gG5, dz2gG6,
      dz2gG7, dz2gG8, dz2gG9, dz2gG10, dz2gG11, dz2gG12, dz2gG13, dz2gG14, dz2gG15, dz2gG16,
      dz2gG17, dz2gG18, dz2gG19, dz2gG20, dz2gG21, dz2gG22, dz2gG23, dz2gG24, dz2gG25, dz2gG26,
      dz2gG27, List.getD_cons_zero, List.getD_cons_succ] <;> norm_num

/-- A group of the register circuit of module `r` is a piece of the circuit. -/
theorem isep2_dz2g_mem (p : Program) (r : ℕ) {i : ℕ} (hi : i < 28) :
    (PSpec.mk (.dz2g i) (modDX p r) (modDY p r) 0).piece ∈ modGroup p r := by
  unfold modGroup groupSpecs
  exact List.mem_map_of_mem (List.mem_map_of_mem (List.mem_map_of_mem (List.mem_range.2 hi)))

/-- A set far (in `uv`, `≥ 6`) from a rectangle `[u1, u2] × [v1, v2]` of the module frame that
avoids every group's hull is far from every group of the register circuit. -/
theorem isep2_dz2g_far (p : Program) (r : ℕ) {S : Set Cell} {u1 u2 v1 v2 : ℤ}
    (hS : ∀ c ∈ S, U p r + u1 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r + u2 ∧ v1 ≤ c.1 + c.2 ∧
      c.1 + c.2 ≤ v2)
    {i : ℕ} (h : (Base.dz2g i).piece.b - (Base.dz2g i).piece.lo + 6 ≤ u1 ∨
      u2 + 6 ≤ (Base.dz2g i).piece.a - (Base.dz2g i).piece.hi ∨
      (Base.dz2g i).piece.b + (Base.dz2g i).piece.hi + 6 ≤ v1 ∨
      v2 + 6 ≤ (Base.dz2g i).piece.a + (Base.dz2g i).piece.lo) :
    FarApart 2 S (PSpec.mk (.dz2g i) (modDX p r) (modDY p r) 0).piece.box := by
  have hm := modD_uv p r
  rw [isep2_spec_box]
  refine isep2_far_box fun x hx => ?_
  have := hS x hx
  omega

/-! ### The INC gate and `RF_J` -/

/-- The gate box in coordinates. -/
theorem isep2_mem_gateBox {r : ℕ} {c : Cell} (hc : c ∈ gateBox p r) :
    modDX p r - 1132 ≤ c.1 ∧ c.1 ≤ modDX p r - 1042 ∧ modDY p r - 1291 ≤ c.2 ∧
      c.2 ≤ modDY p r - 1231 := by
  obtain ⟨d, ⟨d1, d2, d3, d4⟩, rfl⟩ := hc
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- The box of the INC gate piece. -/
theorem isep2_gateP_box (p : Program) (r : ℕ) :
    (gateP p r).box = Box (modDX p r - 1132) (modDX p r - 1042) (modDY p r - 1291)
      (modDY p r - 1259) := by
  have hb := base_boxes
  rw [gateP, incGateSpec, isep2_spec_box]
  congr 1 <;> omega

/-- The box of `RF_J`. -/
theorem isep2_rfJP_box (p : Program) (r : ℕ) :
    (rfJP p r).box = Box (modDX p r - 872) (modDX p r - 850) (modDY p r - 1042)
      (modDY p r - 1034) := by
  have hb := base_boxes
  rw [rfJP, isep2_spec_box]
  congr 1 <;> omega

/-- **The extended relay box of `RF_J`** in coordinates. -/
theorem isep2_relayBoxX_rfJ (p : Program) (r : ℕ) :
    relayBoxX (rfJCorner p r) = Box (modDX p r - 878) (modDX p r - 850) (modDY p r - 1051)
      (modDY p r - 1034) := by
  have hU := U_even p r
  simp only [relayBoxX, rxB, rxBox, rfJCorner, rfX, rfY, rfCU, rfCV, modDX, modDY]
  congr 1 <;> omega

/-- **`IncSep.gate`, strong form**: the gate box is far from every piece of the machine except
the gate itself. -/
theorem isep2_gate (hp : p.WellFormed) (r : ℕ) :
    ∀ h ∈ machPieces p, h ≠ gateP p r → FarApart 2 (gateBox p r) h.box := by
  have hm := modD_uv p r
  intro h hh hne
  refine isep2_modLocal hp r (E := [gateP p r]) (fun c hc => ?_) (fun i hi => Or.inr ?_)
    (Or.inr ?_) (Or.inl List.mem_cons_self) h hh (by simpa using hne)
  · have := isep2_mem_gateBox hc
    omega
  · exact isep2_dz2g_far p r (u1 := 99) (u2 := 249) (v1 := -2423) (v2 := -2273)
      (fun c hc => by have := isep2_mem_gateBox hc; omega) (isep2_dz2g_uv i hi).2.1
  · rw [isep2_rfJP_box]
    refine isep2_far_box fun x hx => ?_
    have := isep2_mem_gateBox hx
    omega

/-- **`IncSep.rf`, strong form**: the extended relay box of `RF_J` is far from every piece of
the machine except `RF_J`. -/
theorem isep2_rf (hp : p.WellFormed) (r : ℕ) :
    ∀ h ∈ machPieces p, h ≠ rfJP p r → FarApart 2 (relayBoxX (rfJCorner p r)) h.box := by
  have hm := modD_uv p r
  intro h hh hne
  rw [isep2_relayBoxX_rfJ]
  refine isep2_modLocal hp r (E := [rfJP p r])
    (S := Box (modDX p r - 878) (modDX p r - 850) (modDY p r - 1051) (modDY p r - 1034))
    (fun c hc => ?_) (fun i hi => Or.inr ?_) (Or.inl List.mem_cons_self) (Or.inr ?_) h hh
    (by simpa using hne)
  · obtain ⟨c1, c2, c3, c4⟩ := hc
    omega
  · refine isep2_dz2g_far p r (u1 := 156) (u2 := 201) (v1 := -1929) (v2 := -1884)
      (fun c hc => ?_) (isep2_dz2g_uv i hi).2.2.1
    obtain ⟨c1, c2, c3, c4⟩ := hc
    omega
  · rw [isep2_gateP_box]
    refine isep2_far_box fun x hx => ?_
    obtain ⟨x1, x2, x3, x4⟩ := hx
    omega

/-! ### The two flights of the module part -/

/-- **The flight from the gate to `RF_J`** in coordinates: at `Tg + j` (`Tg = 194 + 30 k`) the
glider box is at `X = ⌊(j - 4377) / 4⌋` of the module frame, `y = x - 173`. -/
theorem isep2_mem_gateOut {r : ℕ} {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {j : ℕ}
    {c : Cell} (hc : c ∈ (gateOutWL p r k).box ((Tg : ℤ) + j)) :
    modDX p r + ((j : ℤ) - 4377) / 4 - 1 ≤ c.1 ∧ c.1 ≤ modDX p r + ((j : ℤ) - 4377) / 4 + 3 ∧
      modDY p r + ((j : ℤ) - 4377) / 4 - 174 ≤ c.2 ∧
      c.2 ≤ modDY p r + ((j : ℤ) - 4377) / 4 - 170 := by
  have hU := U_even p r
  obtain ⟨c1, c2, c3, c4⟩ := hc
  simp only [gateOutWL, modWL, WL.shift, WL.px, WL.py, WL.qt, modDX, modDY] at c1 c2 c3 c4 ⊢
  omega

/-- **`IncSep.fl1`, strong form**: the flight from the gate to `RF_J`, from `134` to `871`
generations after the arrival at the gate (both included), is far from every piece of the
machine. -/
theorem isep2_fl1 (hp : p.WellFormed) (r : ℕ) {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k)
    (j : ℕ) (hj1 : 134 ≤ j) (hj2 : j ≤ 871) :
    ∀ h ∈ machPieces p, FarApart 2 ((gateOutWL p r k).box ((Tg : ℤ) + j)) h.box := by
  have hm := modD_uv p r
  intro h hh
  refine isep2_modLocal hp r (E := []) (fun c hc => ?_) (fun i hi => Or.inr ?_) (Or.inr ?_)
    (Or.inr ?_) h hh List.not_mem_nil
  · have := isep2_mem_gateOut hTg hc
    omega
  · exact isep2_dz2g_far p r (u1 := 169) (u2 := 177) (v1 := -2297) (v2 := -1921)
      (fun c hc => by have := isep2_mem_gateOut hTg hc; omega) (isep2_dz2g_uv i hi).2.2.2.1
  · rw [isep2_rfJP_box]
    refine isep2_far_box fun x hx => ?_
    have := isep2_mem_gateOut hTg hx
    omega
  · rw [isep2_gateP_box]
    refine isep2_far_box fun x hx => ?_
    have := isep2_mem_gateOut hTg hx
    omega

/-- **The flight from `RF_J` to the increment** in coordinates: at `Tg + j` the glider box is at
`X = ⌊(j - 4372) / 4⌋` of the module frame, `y = -x - 1910`. -/
theorem isep2_mem_rfJOut {r : ℕ} {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k) {j : ℕ}
    {c : Cell} (hc : c ∈ (rfJOutWL p r k).box ((Tg : ℤ) + j)) :
    modDX p r + ((j : ℤ) - 4372) / 4 - 1 ≤ c.1 ∧ c.1 ≤ modDX p r + ((j : ℤ) - 4372) / 4 + 3 ∧
      modDY p r - ((j : ℤ) - 4372) / 4 - 1911 ≤ c.2 ∧
      c.2 ≤ modDY p r - ((j : ℤ) - 4372) / 4 - 1907 := by
  have hU := U_even p r
  obtain ⟨c1, c2, c3, c4⟩ := hc
  simp only [rfJOutWL, modWL, incInWL, WL.shift, WL.px, WL.py, WL.qt, modDX,
    modDY] at c1 c2 c3 c4 ⊢
  omega

/-- **`IncSep.fl2`, strong form**: the flight from `RF_J` to the increment, from `931` to `946`
generations after the arrival at the gate (both included), is far from every piece of the
machine. -/
theorem isep2_fl2 (hp : p.WellFormed) (r : ℕ) {k : ℤ} {Tg : ℕ} (hTg : (Tg : ℤ) = 194 + 30 * k)
    (j : ℕ) (hj1 : 931 ≤ j) (hj2 : j ≤ 946) :
    ∀ h ∈ machPieces p, FarApart 2 ((rfJOutWL p r k).box ((Tg : ℤ) + j)) h.box := by
  have hm := modD_uv p r
  intro h hh
  refine isep2_modLocal hp r (E := []) (fun c hc => ?_) (fun i hi => Or.inr ?_) (Or.inr ?_)
    (Or.inr ?_) h hh List.not_mem_nil
  · have := isep2_mem_rfJOut hTg hc
    omega
  · exact isep2_dz2g_far p r (u1 := 184) (u2 := 200) (v1 := -1912) (v2 := -1904)
      (fun c hc => by have := isep2_mem_rfJOut hTg hc; omega) (isep2_dz2g_uv i hi).2.2.2.2
  · rw [isep2_rfJP_box]
    refine isep2_far_box fun x hx => ?_
    have := isep2_mem_rfJOut hTg hx
    omega
  · rw [isep2_gateP_box]
    refine isep2_far_box fun x hx => ?_
    have := isep2_mem_rfJOut hTg hx
    omega

/-! ### Separated pieces of a pairwise separated list -/

/-- **Two distinct members of a pairwise separated list are separated.** -/
theorem isep2_pairwise_sep : ∀ {l : List Piece}, l.Pairwise Piece.Sep → ∀ {a b : Piece},
    a ∈ l → b ∈ l → a ≠ b → Piece.Sep a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hne => by
    rcases List.pairwise_cons.1 h with ⟨h1, h2⟩
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · exact absurd (ha'.trans hb'.symm) hne
    · subst ha'
      exact h1 b hb'
    · subst hb'
      exact Piece.Sep.symm' (h1 a ha')
    · exact isep2_pairwise_sep h2 ha' hb' hne

/-- **The boxes of a list of pieces of the machine are far from every other piece of the
machine.** -/
theorem isep2_boxesOf_far (hp : p.WellFormed) {L : List Piece} (hL : ∀ x ∈ L, x ∈ machPieces p)
    {h : Piece} (hh : h ∈ machPieces p) (hn : h ∉ L) : FarApart 2 (boxesOf L) h.box := by
  intro x hx y hy
  obtain ⟨g, hg, hxg⟩ := mem_boxesOf.1 hx
  exact isep2_pairwise_sep (machPieces_sep p hp) (hL g hg) hh (fun he => hn (he ▸ hg)) x hxg y hy

/-! ### The increment -/

/-- The hull of the run regions (module frame): the box `u ∈ [-738, 798]`, `v ∈ [-2324, 670]`,
or the lanes. -/
def isep2RunHull : Set Cell :=
  {c | (-738 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ 798 ∧ -2324 ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ 670) ∨
    (-113 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ -69 ∧ 354 ≤ c.1 + c.2)}

/-- A component inside the hull. -/
theorem isep2_BU_hull {a b lo hi U₁ U₂ V₁ V₂ : ℤ}
    (h : -738 ≤ U₁ ∧ U₂ ≤ 798 ∧ -2324 ≤ V₁ ∧ V₂ ≤ 670) :
    BU a b lo hi U₁ U₂ V₁ V₂ ⊆ isep2RunHull := by
  rintro c ⟨-, c5, c6, c7, c8⟩
  exact Or.inl ⟨by omega, by omega, by omega, by omega⟩

/-- The lanes inside the hull. -/
theorem isep2_lanes_hull : regLanes ⊆ isep2RunHull := by
  rintro c ⟨c1, c2, c3⟩
  exact Or.inr ⟨c1, c2, c3⟩

set_option maxRecDepth 100000 in
/-- **The run regions of the increment lie in the hull.** -/
theorem isep2_incRunBox_hull : incRunBox ⊆ isep2RunHull := by
  have key : ∀ L : List (Set Cell), AllSub isep2RunHull L → unionL L ⊆ isep2RunHull :=
    fun _ h => unionL_subset_of h
  unfold incRunBox dz2eRegion dz2e1Region dz2e2Region dz2e3Region dz2jRegion
  refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
    (key _ ?_) (key _ ?_)) (key _ ?_)) (key _ ?_)) (key _ ?_) <;>
  simp only [dz2eRegL, dz2e1RegL, dz2e2RegL, dz2e3RegL, dz2jRegL, AllSub] <;>
  repeat' apply And.intro
  all_goals first
    | exact isep2_BU_hull (by norm_num) | exact isep2_lanes_hull | trivial

set_option maxRecDepth 100000 in
/-- **The run regions avoid the INC gate** (module frame), component by component. -/
theorem isep2_incRunBox_gate : FarApart 2 incRunBox (Box (-1132) (-1042) (-1291) (-1259)) := by
  have key : ∀ L : List (Set Cell), FarAll (Box (-1132) (-1042) (-1291) (-1259)) L →
      FarApart 2 (unionL L) (Box (-1132) (-1042) (-1291) (-1259)) := fun _ h => farApart_unionL h
  unfold incRunBox dz2eRegion dz2e1Region dz2e2Region dz2e3Region dz2jRegion
  refine (((((key _ ?_).union_left (key _ ?_)).union_left (key _ ?_)).union_left
    (key _ ?_)).union_left (key _ ?_)) <;>
  simp only [dz2eRegL, dz2e1RegL, dz2e2RegL, dz2e3RegL, dz2jRegL, FarAll] <;>
  repeat' apply And.intro
  all_goals first
    | exact BU.farApart_box (by norm_num) | exact regLanes_farApart_box (by norm_num) | trivial

set_option maxRecDepth 100000 in
/-- **The run regions avoid `RF_J`** (module frame), component by component. -/
theorem isep2_incRunBox_rfJ : FarApart 2 incRunBox (Box (-872) (-850) (-1042) (-1034)) := by
  have key : ∀ L : List (Set Cell), FarAll (Box (-872) (-850) (-1042) (-1034)) L →
      FarApart 2 (unionL L) (Box (-872) (-850) (-1042) (-1034)) := fun _ h => farApart_unionL h
  unfold incRunBox dz2eRegion dz2e1Region dz2e2Region dz2e3Region dz2jRegion
  refine (((((key _ ?_).union_left (key _ ?_)).union_left (key _ ?_)).union_left
    (key _ ?_)).union_left (key _ ?_)) <;>
  simp only [dz2eRegL, dz2e1RegL, dz2e2RegL, dz2e3RegL, dz2jRegL, FarAll] <;>
  repeat' apply And.intro
  all_goals first
    | exact BU.farApart_box (by norm_num) | exact regLanes_farApart_box (by norm_num) | trivial

/-- Translation of a set far from a box. -/
theorem isep2_far_translate {A : Set Cell} {a b lo hi : ℤ} (v : Cell)
    (h : FarApart 2 A (Box a b lo hi)) :
    FarApart 2 ((fun c => v + c) '' A) (Box (a + v.1) (b + v.1) (lo + v.2) (hi + v.2)) := by
  rintro _ ⟨x, hx, rfl⟩ y ⟨y1, y2, y3, y4⟩ ⟨n1, n2, n3, n4⟩
  refine h x hx (y - v) ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at * <;> omega

/-- **The run regions placed at module `r` are far from every piece of the machine outside the
register circuit.** -/
theorem isep2_incRunBox_far (hp : p.WellFormed) (r : ℕ) :
    ∀ h ∈ machPieces p, h ∉ modGroup p r →
      FarApart 2 ((fun c => (modDX p r, modDY p r) + c) '' incRunBox) h.box := by
  have hm := modD_uv p r
  refine isep2_modLocal hp r (fun c hc => ?_) (fun i hi => Or.inl (isep2_dz2g_mem p r hi))
    (Or.inr ?_) (Or.inr ?_)
  · obtain ⟨d, hd, rfl⟩ := hc
    have := isep2_incRunBox_hull hd
    simp only [isep2RunHull, Set.mem_ofPred_eq] at this
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  · rw [isep2_rfJP_box]
    have h := isep2_far_translate (modDX p r, modDY p r) isep2_incRunBox_rfJ
    convert h using 2 <;> simp only <;> ring
  · rw [isep2_gateP_box]
    have h := isep2_far_translate (modDX p r, modDY p r) isep2_incRunBox_gate
    convert h using 2 <;> simp only <;> ring

/-- The register circuit of module `r` consists of pieces of the machine. -/
theorem isep2_modGroup_mem {r : ℕ} (hr : r < numRegs p) : ∀ x ∈ modGroup p r, x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  exact moduleSpecs_mem hr (by simp [moduleSpecs, hs])

/-- **`IncSep.inc`, strong form**: the increment at module `r`, for every ready register and at
every generation, is far from every piece of the machine outside the register circuit. -/
theorem isep2_incRun (hp : p.WellFormed) {r : ℕ} (hr : r < numRegs p) {R : RegS} (hR : R.Ready)
    (j : ℕ) : ∀ h ∈ machPieces p, h ∉ modGroup p r →
      FarApart 2 (conway.evolve j (incStart p r ∪ regAt p r R) : Set Cell) h.box := by
  intro h hh hn
  refine FarApart.mono ?_ (lane_incRun_sub p r hR j) le_rfl
  refine FarApart.union_left (FarApart.union_left (isep2_incRunBox_far hp r h hh hn)
    (isep2_boxesOf_far hp (isep2_modGroup_mem hr) hh hn)) ?_
  exact FarApart.symm' (machPieces_laneClear hp r h hh).farApart

end LP

end LeanTheory.Life
