/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecStepRegion

/-!
# The `decJz` step

Research note `N-22`: **one `decJz r z` instruction of a well-formed program is simulated by the
machine**, from `encM s` to `encM s'`, with every generation in `machRegion p`, for every register
value, conditional only on the separation facts `DecSep` of the activation.

1. **Body** (`[1080, 4260]`): the body of the `dec` unit `i` (`decBody_window`), every register
   idle.
2. **Two threads** from `4260` to the end, inside the idle machine, with the other registers idle:
   * value `≥ 1` (`decThreadN` with the unpaired `KZ`, `decUnpZProc`): the control, the DEC chain,
     the register run (pull or static block), the NZ answer captured with `KNZ` at station `j`,
     the answer link to unit `i + 1`; the register holds one less;
   * value `0` (`decThreadZ` with the unpaired `KNZ`, `decUnpNProc`): the zero test `dz2mk0`, the
     Z answer captured with `KZ`, the answer link to unit `z`; the register is unchanged.
3. The end pattern is `encM s'` (`s'.T = s.T + τ`, `τ = end - 1080 > 0`, `≡ 0 (mod 30)`), every
   other register `τ` generations later, every register ready.

The region facts are proved here (`decFootMN_region`, `decFootMZ_region`, …): every footprint lies
at `u ≥ uMin - 300`, by the anchors of `ActivationDecStepRegion` and the boxes of the certificates.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Registers -/

/-- The registers after an NZ activation: register `r` replaced, the others later. -/
def decRegs (s : MState) (r : ℕ) (R' : RegS) (n : ℕ) : ℕ → RegS :=
  Function.update (fun r' => (s.reg r').later n) r R'

/-- **The body stage**: the body of unit `i` with every register idle. -/
theorem decBodyStage {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hs : DecSep p i r z) (reg : ℕ → RegS)
    (hinvR : ∀ r' ∈ List.range (numRegs p), (reg r').Inv) :
    Reaction (piecesAt (machPieces p) 1080 ∪ ctrlAt p i ∪ regsOn p reg (List.range (numRegs p)))
      (piecesAt (machPieces p) (1080 + 3180) ∪ ((unitWL p i decLWL).cells 4260 ∪
        ((unitWL p i decRWL).cells 4260 ∪ (unitWL p i decDWL).cells 4260)) ∪
        regsOn p (fun r' => (reg r').later 3180) (List.range (numRegs p))) 3180
      (fun j => boxesOf (machPieces p) ∪ bodyDecBox p i ∪
        stripsOn p reg (List.range (numRegs p)) j) :=
  (decBody_window hp (bodyDecGroup_mem hi) hs.body).par
    (regsOn_reaction p reg 3180 (List.range (numRegs p)) List.nodup_range hinvR
      fun j _ r₁ h₁ r₂ h₂ hne => (hs.lanes r₁ (List.mem_range.1 h₁) r₂ (List.mem_range.1 h₂)
        hne).mono (regStrip_subset (hinvR r₁ h₁) p r₁ j) (regStrip_subset (hinvR r₂ h₂) p r₂ j))
    fun j _ a ha b hb => by
      obtain ⟨r', hr', hb⟩ := mem_stripsOn.1 hb
      exact hs.laneBody r' (List.mem_range.1 hr') a ha b
        (regStrip_subset (hinvR r' hr') p r' j hb)

/-! ### Anchors of the activation -/

/-- **The anchors of a `decJz` activation**: module `r`, the entry chains of units `i`, `i + 1`
and `z`. -/
theorem decAnchors {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) :
    uMin p ≤ U p r - 738 ∧ uMin p ≤ A p i - 32 ∧ uMin p ≤ A p ((i + 1 : ℕ) : ℤ) - 32 ∧
      uMin p ≤ A p z - 32 := by
  have hP := one_le_P p
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  refine ⟨dR_uMin_le_mod (lt_numRegs_of_dec hi), dR_uMin_le_chain (t := 0)
    (decChain_mem hlt (by push_cast; omega)), dR_uMin_le_chain (t := 0)
    (decChain_mem (succ_lt_of_dec hp hi) (by push_cast; omega)), dR_uMin_le_chain (t := 0)
    (decChain_mem (lt_of_dec hp hi) (by push_cast; omega))⟩

/-- The reflectors of a route of the activation have pieces of the machine. -/
theorem decRoute_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) {g : WL}
    {cs : List Corner} (hx : (g, cs) ∈ decSpecs p i r z) :
    ∀ x ∈ (route g cs).1, x.piece ∈ machPieces p :=
  fun _ h => decRefl_mem hi hx _ (List.mem_map_of_mem h)

/-! ### Region facts of the footprints -/

/-- The components of the body run of a `dec` unit lie at `u ≥ -180` (unit frame). -/
theorem bodyDecRegL_u : DecAllSub {c : Cell | -180 ≤ c.1 - c.2} bodyDecRegL := by
  simp only [bodyDecRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first | exact BU_subset_u' (by omega) | trivial

/-- **The body run of a `dec` unit lies at `u ≥ -180`** (unit frame). -/
theorem bodyDecRegion_u : bodyDecRegion ⊆ {c : Cell | -180 ≤ c.1 - c.2} :=
  unionL_subset_dec bodyDecRegL_u


/-- The least `u` of a glider flying `NE` grows. -/
theorem dR_mono_ne {w : WL} (hx : w.dx = 1) (hy : w.dy = -1) (e : ℕ) :
    ∀ t : ℕ, e ≤ t → w.duLo e ≤ w.duLo t :=
  fun t h => WL.duLo_mono hx hy (by exact_mod_cast h)

/-- The least `u` of a glider flying `NW` is constant. -/
theorem dR_mono_nw {w : WL} (hx : w.dx = -1) (hy : w.dy = -1) (e : ℕ) :
    ∀ t : ℕ, e ≤ t → w.duLo e ≤ w.duLo t :=
  fun t _ => by rw [WL.duLo_nw hx hy, WL.duLo_nw hx hy]

/-- A set at `u ≥ m` with `uMin ≤ m + 300` lies in the region. -/
theorem dR_region_of {p : Program} {S : Set Cell} {m : ℤ} (h : ∀ c ∈ S, m ≤ c.1 - c.2)
    (hm : uMin p - 300 ≤ m) : S ⊆ machRegion p :=
  fun c hc => by rw [dR_mem_machRegion]; exact le_trans hm (h c hc)

/-- **The footprint of the control** lies in the region. -/
theorem decFootC_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (t : ℕ) : decFootC p i r t ⊆ machRegion p := by
  obtain ⟨hU, hA, -, -⟩ := decAnchors hp hi
  have hu := modD_uv p r
  have hm := decM_cast p hi
  unfold decFootC
  split_ifs
  · refine dR_flyFoot_region ⟨Or.inl rfl, Or.inl rfl⟩ (decC_lines p i r).1 (decC_timedX p hi)
      (decRoute_mem hi (by rw [decSpecs_eq]; simp)) ?_ ?_ t
    · rw [WL.duLo_se rfl rfl]
      have := unitD_uv p i
      simp only [unitWL, decRWL, WL.shift]
      omega
    · have h := decC_window p i r
      exact dR_mono_ne (by change (decGC p i r).dx = 1; rw [h]; rfl)
        (by change (decGC p i r).dy = -1; rw [h]; rfl) _
  · refine dR_region_of (m := U p r - 13) (fun c hc => ?_) (by omega)
    have := dR_image_box_u hc
    simp only at this
    omega
  · refine dR_region_of (m := U p r - 33) (fun c hc => ?_) (by omega)
    obtain ⟨d, ⟨j, hj, h1, h2, h3, h4⟩, rfl⟩ := hc
    simp only [Prod.fst_add, Prod.snd_add] at *
    have : (j : ℤ) ≤ (decM p i r : ℤ) := by omega
    nlinarith
  · refine dR_region_of (m := U p r + 37) (fun c hc => ?_) (by omega)
    obtain ⟨d, hd, rfl⟩ := hc
    have h1 := WL.duLo_le hd
    rw [WL.duLo_se (w := cp0WL) rfl rfl] at h1
    simp only [cp0WL, Prod.fst_add, Prod.snd_add] at *
    omega

/-- The start of the joint approach of `KNZ` and its station, as the certificate's start. -/
theorem decTokWStartN_eq {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    decTokWStartN p i r = translate (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ)) (stCaptureNZG ∪ stTokENZ) := by
  have hc := (decCap_cast p hi).1
  obtain ⟨hS, hS30, -⟩ := decTS_facts p hi
  have h90 : 90 ≤ decCapN p i r := by unfold decCapN; omega
  have hK : (tokNZWL 0).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have hE : stTokENZ = (tokNZWL 0).cells 10260 := rfl
  have e1 : ((decCapN p i r - 90 : ℕ) : ℤ) = 10260 + 288 * ((callerIdx p r i : ℕ) : ℤ) +
      decShift p i r := by push_cast [Nat.cast_sub h90]; omega
  unfold decTokWStartN decTokN
  rw [stNZOne, stNZ_one_at, e1, modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩, tokNZWL_step,
    cells_step hK, translate_translate, ← hE,
    show ((modDX p r, modDY p r) + (72 * ((callerIdx p r i : ℕ) : ℤ),
      72 * ((callerIdx p r i : ℕ) : ℤ)) : Cell) = (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r + 72 * ((callerIdx p r i : ℕ) : ℤ)) from rfl, ← translate_union,
    phase_congr stNZG (a := 12 * callerIdx p r i % 30 + (decCapN p i r - 90)) (b := 0)
      (by unfold decCapN at *; omega),
    show phase stNZG 0 = stNZG by rw [phase, Nat.zero_mod, Rule.evolve_zero], ← stCaptureNZG_eq]

/-- The start of the joint approach of `KZ` and its station, as the certificate's start. -/
theorem decTokWStartZ_eq {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    decTokWStartZ p i r = translate (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) (stCaptureZG ∪ stTokEZ) := by
  have hc := (decCap_cast p hi).2
  obtain ⟨hS, hS30, -⟩ := decTS_facts p hi
  have h90 : 90 ≤ decCapZ p i r := by unfold decCapZ; omega
  have hK : (tokZWL 0).Dir := ⟨Or.inr rfl, Or.inr rfl⟩
  have hE : stTokEZ = (tokZWL 0).cells 12300 := rfl
  have e1 : ((decCapZ p i r - 90 : ℕ) : ℤ) = 12300 + 288 * ((callerIdx p r i : ℕ) : ℤ) +
      decShift p i r := by push_cast [Nat.cast_sub h90]; omega
  unfold decTokWStartZ decTokZ
  rw [stZOne, stZ_one_at, e1, modShift_cells p r ⟨Or.inr rfl, Or.inr rfl⟩, tokZWL_step,
    cells_step hK, translate_translate, ← hE,
    show ((modDX p r, modDY p r) + (72 * ((callerIdx p r i : ℕ) : ℤ),
      -72 * ((callerIdx p r i : ℕ) : ℤ)) : Cell) = (modDX p r + 72 * ((callerIdx p r i : ℕ) : ℤ),
      modDY p r - 72 * ((callerIdx p r i : ℕ) : ℤ)) from Prod.ext rfl (by simp; ring),
    ← translate_union,
    phase_congr stZG (a := 12 * callerIdx p r i % 30 + (decCapZ p i r - 90)) (b := 0)
      (by unfold decCapZ at *; omega),
    show phase stZG 0 = stZG by rw [phase, Nat.zero_mod, Rule.evolve_zero], ← stCaptureZG_eq]

/-- **The footprint of `KNZ`** lies in the region, up to the capture. -/
theorem tokFootN_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) {t : ℕ} (ht : t ≤ decCapN p i r) :
    tokFootN p i r t ⊆ machRegion p := by
  obtain ⟨hU, hA, -, -⟩ := decAnchors hp hi
  have hu := modD_uv p r
  unfold tokFootN
  split_ifs with h
  · refine dR_flyFoot_region ⟨Or.inl rfl, Or.inl rfl⟩ (decKNZ_lines p i r).1 (decKNZ_timedX p hi)
      (decRoute_mem hi (by rw [decSpecs_eq]; simp)) ?_ ?_ t
    · rw [WL.duLo_se rfl rfl]
      have := unitD_uv p i
      simp only [unitWL, decLWL, WL.shift]
      omega
    · rw [decKNZ_target]
      exact dR_mono_ne rfl rfl _
  · refine dR_region_of (m := U p r - 556) (fun c hc => ?_) (by omega)
    rw [decTokWStartN_eq hi, Rule.evolve_translate] at hc
    have := dR_translate_u (stTokWNZ.subset _ (by omega)) hc
    simp only at this
    omega

/-- **The footprint of `KZ`** lies in the region, up to the capture. -/
theorem tokFootZ_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) {t : ℕ} (ht : t ≤ decCapZ p i r) :
    tokFootZ p i r t ⊆ machRegion p := by
  obtain ⟨hU, hA, -, -⟩ := decAnchors hp hi
  have hu := modD_uv p r
  unfold tokFootZ
  split_ifs with h
  · refine dR_flyFoot_region ⟨Or.inl rfl, Or.inl rfl⟩ (decKZ_lines p i r) (decKZ_timedX p hi)
      (decRoute_mem hi (by rw [decSpecs_eq]; simp)) ?_ ?_ t
    · rw [WL.duLo_se rfl rfl]
      have := unitD_uv p i
      simp only [unitWL, decDWL, WL.shift]
      omega
    · rw [decKZ_target]
      exact dR_mono_nw rfl rfl _
  · refine dR_region_of (m := U p r + 1162) (fun c hc => ?_) (by omega)
    rw [decTokWStartZ_eq hi, Rule.evolve_translate] at hc
    have := dR_translate_u (stTokWZ.subset _ (by omega)) hc
    simp only at this
    omega

/-- A chain of copies moved by `(72, ±72)` keeps `u` up to `144` per copy (the `u`-lower bound of
the base region applies to `NZ` copies unchanged). -/
theorem dR_chainNZ_u {R : Set Cell} {m : ℤ} (hR : ∀ c ∈ R, m ≤ c.1 - c.2) {L : ℕ} {c : Cell}
    (hc : c ∈ chainFoot R (72, 72) L) : m ≤ c.1 - c.2 := by
  obtain ⟨j, -, hj⟩ := hc
  have := hR _ hj
  simp only at this
  linarith

/-- A chain of copies moved by `(72, -72)` lies at `u ≥` the bound of its base region. -/
theorem dR_chainZ_u {R : Set Cell} {m : ℤ} (hR : ∀ c ∈ R, m ≤ c.1 - c.2) {L : ℕ} {c : Cell}
    (hc : c ∈ chainFoot R (72, -72) L) : m ≤ c.1 - c.2 := by
  obtain ⟨j, -, hj⟩ := hc
  have := hR _ hj
  simp only at this
  have : (0 : ℤ) ≤ j := by positivity
  linarith

/-- The station region of an NZ pass lies at `u ≥ -539`. -/
theorem stNZRY_u : ∀ c ∈ stNZRY, -539 ≤ c.1 - c.2 := by
  rintro c (((⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) | ⟨h1, h2, h3, h4⟩) |
    ⟨m, -, -, h1, h2, h3, h4⟩) <;> omega

/-- The station region of a Z pass lies at `u ≥ 1145`. -/
theorem stZR_u : ∀ c ∈ stZR, 1145 ≤ c.1 - c.2 := by
  rintro c (((⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) | ⟨h1, h2, h3, h4⟩) |
    ⟨m, h0, -, h1, h2, h3, h4⟩) <;> omega

/-- **The footprint of the NZ answer** from the cut lies in the region. -/
theorem decAnsFootN_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (t : ℕ) : decAnsFootN p i r t ⊆ machRegion p := by
  obtain ⟨hU, -, -, -⟩ := decAnchors hp hi
  have hu := modD_uv p r
  unfold decAnsFootN
  split_ifs
  · refine WL.dbox_region ?_
    rw [WL.duLo_se rfl rfl]
    simp only [decAnsWLN, modWL, ansNZWL, WL.shift]
    omega
  · refine dR_region_of (m := U p r - 539) (fun c hc => ?_) (by omega)
    obtain ⟨d, hd, rfl⟩ := hc
    have := dR_chainNZ_u stNZRY_u hd
    simp only [Prod.fst_add, Prod.snd_add]
    omega

/-- **The footprint of the Z answer** from the cut lies in the region. -/
theorem decAnsFootZ_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) {t : ℕ} (ht : decCutZ p i r ≤ t) :
    decAnsFootZ p i r t ⊆ machRegion p := by
  obtain ⟨hU, -, -, -⟩ := decAnchors hp hi
  obtain ⟨hS, -, -⟩ := decTS_facts p hi
  have hu := modD_uv p r
  have hUe := U_even p r
  unfold decAnsFootZ
  split_ifs
  · refine WL.dbox_region ?_
    have ht' : (decCutZ p i r : ℤ) ≤ t := by exact_mod_cast ht
    simp only [decCutZ] at ht'
    push_cast at ht'
    simp only [WL.duLo, WL.px, WL.py, WL.qt, decAnsWLZ, modWL, ansZWL, WL.shift, modDX,
      modDY] at hu ⊢
    omega
  · refine dR_region_of (m := U p r + 1145) (fun c hc => ?_) (by omega)
    obtain ⟨d, hd, rfl⟩ := hc
    have := dR_chainZ_u stZR_u hd
    simp only [Prod.fst_add, Prod.snd_add]
    omega

/-- A placed run region at `u ≥ -738` (module frame) lies in the region. -/
theorem dR_modImg_region {p : Program} {r : ℕ} (hU : uMin p ≤ U p r - 738) {S : Set Cell}
    (hS : S ⊆ {c : Cell | -738 ≤ c.1 - c.2}) : modImg p r S ⊆ machRegion p := by
  have hu := modD_uv p r
  refine dR_region_of (m := U p r - 738) (fun c hc => ?_) (by omega)
  obtain ⟨d, hd, rfl⟩ := hc
  have : -738 ≤ d.1 - d.2 := hS hd
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- Pieces of the machine lie in the region. -/
theorem dR_boxes_region {p : Program} {L : List Piece} (h : ∀ x ∈ L, x ∈ machPieces p) :
    boxesOf L ⊆ machRegion p :=
  (boxesOf_subset h).trans (dR_pieces_region p)

/-- **The rest of an NZ run** lies in the region. -/
theorem restFootN_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (t : ℕ) : restFootN p i r t ⊆ machRegion p := by
  obtain ⟨hU, -, -, -⟩ := decAnchors hp hi
  unfold restFootN
  split_ifs
  · exact dR_modImg_region hU decRestRegNZ_u
  · exact Set.union_subset (dR_boxes_region (modGroup_mem (lt_numRegs_of_dec hi)))
      (dR_modLanes_region hU)

/-- **The rest of the Z run** lies in the region. -/
theorem restFootZ_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (t : ℕ) : restFootZ p i r t ⊆ machRegion p := by
  obtain ⟨hU, -, -, -⟩ := decAnchors hp hi
  unfold restFootZ
  split_ifs
  · exact dR_modImg_region hU dz2mk0RestRegion_u
  · exact Set.union_subset (dR_boxes_region (modGroup_mem (lt_numRegs_of_dec hi)))
      (dR_modLanes_region hU)

/-- **A link into an entry chain with a side window stays in the region.** -/
theorem dR_linkFootW_region {p : Program} {a t : ℕ} {g : WL} {cs : List Corner} {T T0 : ℕ}
    (hd : g.Dir) (hl : RouteLines g cs) (htim : RouteTimedX g cs T)
    (hmem : ∀ x ∈ (route g cs).1, x.piece ∈ machPieces p) (h0 : uMin p - 300 ≤ g.duLo T)
    (hdx : (route g cs).2.dx = 1) (hdy : (route g cs).2.dy = -1)
    (hent : entryFoot p a t ⊆ machRegion p) (j : ℕ) :
    linkFootW p a t g cs T T0 j ⊆ machRegion p := by
  obtain ⟨h1, h2⟩ := dR_route_region cs g T hd hl htim hmem h0
  unfold linkFootW
  split_ifs with ha hb
  · exact h1 j ha
  · exact WL.dbox_region (h2.trans (WL.duLo_mono hdx hdy (by omega)))
  · exact hent

/-- **The end of an NZ activation** lies in the region, up to its end. -/
theorem finFootN_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) {t : ℕ} (_ht : t ≤ decEndN p i r) :
    finFootN p i r t ⊆ machRegion p := by
  obtain ⟨hU, -, hA1, -⟩ := decAnchors hp hi
  have hu := modD_uv p r
  have hc := decCap_cast p hi
  obtain ⟨hD, -, -, -, -, -⟩ := decN_times hp hi
  unfold finFootN
  split_ifs with h1 h2
  · refine dR_region_of (m := U p r - 575) (fun c hc' => ?_) (by omega)
    have hs := (stationNZ_captureE p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
      (decCapN p i r) hc.1).subset (t - decCapN p i r) (by unfold decDispN decCapN at *; omega) hc'
    have := dR_image_box_u hs
    simp only at this
    omega
  · obtain ⟨g1, g2, -⟩ := decGN_dir p i r
    obtain ⟨hl, htim, -, hfin, -⟩ := decAnsN_plan hp hi _ hD
    refine dR_linkFootW_region ⟨Or.inr g1, Or.inl g2⟩ hl htim
      (decRoute_mem hi (by rw [decSpecs_eq]; simp)) ?_ ?_ ?_ (dR_entryFoot_region _ hA1) _
    · have hUe := U_even p r
      simp only [WL.duLo, WL.px, WL.py, WL.qt, decGN, modWL, nzAnsWL, WL.shift, modDX,
        modDY] at hu ⊢
      rw [hD]
      omega
    · rw [hfin]; rfl
    · rw [hfin]; rfl
  · exact dR_chainOut_region hA1 _

/-- **The end of a Z activation** lies in the region, up to its end. -/
theorem finFootZ_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) {t : ℕ} (_ht : t ≤ decEndZ p i r z) :
    finFootZ p i r z t ⊆ machRegion p := by
  obtain ⟨hU, -, -, hAz⟩ := decAnchors hp hi
  have hu := modD_uv p r
  have hc := decCap_cast p hi
  obtain ⟨hD, -, -, -, -, -⟩ := decZ_times hp hi
  unfold finFootZ
  split_ifs with h1 h2
  · refine dR_region_of (m := U p r + 1138) (fun c hc' => ?_) (by omega)
    have hs := (stationZ_captureE p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
      (decCapZ p i r) hc.2).subset (t - decCapZ p i r) (by unfold decDispZ decCapZ at *; omega) hc'
    have := dR_image_box_u hs
    simp only at this
    omega
  · obtain ⟨g1, g2, g3⟩ := decGZ_dir p i r
    obtain ⟨hl, htim, -, hfin, -⟩ := decAnsZ_plan hp hi _ hD
    refine dR_linkFootW_region ⟨Or.inl g1, Or.inl g2⟩ hl htim
      (decRoute_mem hi (by rw [decSpecs_eq]; simp)) ?_ ?_ ?_ (dR_entryFoot_region _ hAz) _
    · rw [WL.duLo_se g1 g2, g3]
      simp only [zAnsStation]
      omega
    · rw [hfin]; rfl
    · rw [hfin]; rfl
  · exact dR_chainOut_region hAz _

/-- **The unpaired `KZ`** (NZ activation) lies in the region, up to the end. -/
theorem unpFootZ_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (t : ℕ) : unpFootZ p i r t ⊆ machRegion p := by
  obtain ⟨hU, -, -, -⟩ := decAnchors hp hi
  have hu := modD_uv p r
  have hc := decCap_cast p hi
  unfold unpFootZ
  split_ifs with h1 h2
  · exact tokFootZ_region hp hi h1
  · refine dR_region_of (m := U p r + 1173) (fun c hc' => ?_) (by omega)
    have hs := (stationZ_unpaired p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
      (decCapZ p i r) hc.2).subset (t - decCapZ p i r) (by omega) hc'
    have := dR_image_box_u hs
    simp only at this
    omega
  · exact Set.empty_subset _

/-- **The unpaired `KNZ`** (Z activation) lies in the region, up to the end. -/
theorem unpFootN_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (t : ℕ) : unpFootN p i r t ⊆ machRegion p := by
  obtain ⟨hU, -, -, -⟩ := decAnchors hp hi
  have hu := modD_uv p r
  have hc := decCap_cast p hi
  unfold unpFootN
  split_ifs with h1 h2
  · exact tokFootN_region hp hi h1
  · refine dR_region_of (m := U p r - 539) (fun c hc' => ?_) (by omega)
    have hs := (stationNZ_unpaired p r (callerIdx p r i) (decShift p i r) (decShift_mod p i r)
      (decCapN p i r) hc.1).subset (t - decCapN p i r) (by omega) hc'
    have := dR_image_box_u hs
    simp only at this
    omega
  · exact Set.empty_subset _

/-- **The control, the run and the NZ answer** lie in the region. -/
theorem qFootN_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (t : ℕ) : qFootN p i r t ⊆ machRegion p := by
  obtain ⟨hU, -, -, -⟩ := decAnchors hp hi
  have hr := lt_numRegs_of_dec hi
  have hLC := dR_boxes_region (decLC_mem hi)
  have hLS := dR_boxes_region (decLSN_mem hi)
  have hLG := dR_boxes_region (modGroup_mem hr)
  unfold qFootN
  split_ifs
  · rw [boxesOf_append]
    exact Set.union_subset (Set.union_subset hLG hLS) (Set.union_subset
      (Set.union_subset hLC (decFootC_region hp hi t)) (dR_modLanes_region hU))
  · rw [boxesOf_append]
    exact Set.union_subset (Set.union_subset hLC hLS) (dR_modImg_region hU decRunRegNZ_u)
  · exact Set.union_subset hLC (Set.union_subset (restFootN_region hp hi t)
      (Set.union_subset hLS (decAnsFootN_region hp hi t)))

/-- **The control, the run and the Z answer** lie in the region. -/
theorem qFootZ_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (t : ℕ) : qFootZ p i r t ⊆ machRegion p := by
  obtain ⟨hU, -, -, -⟩ := decAnchors hp hi
  have hr := lt_numRegs_of_dec hi
  have hLC := dR_boxes_region (decLC_mem hi)
  have hLS := dR_boxes_region (decLSZ_mem hi)
  have hLG := dR_boxes_region (modGroup_mem hr)
  unfold qFootZ
  split_ifs with h1 h2
  · rw [boxesOf_append]
    exact Set.union_subset (Set.union_subset hLG hLS) (Set.union_subset
      (Set.union_subset hLC (decFootC_region hp hi t)) (dR_modLanes_region hU))
  · rw [boxesOf_append]
    exact Set.union_subset (Set.union_subset hLC hLS) (dR_modImg_region hU decRunRegZ_u)
  · exact Set.union_subset hLC (Set.union_subset (restFootZ_region hp hi t)
      (Set.union_subset hLS (decAnsFootZ_region hp hi (by omega))))

/-- **The main thread of an NZ activation** lies in the region, up to its end. -/
theorem footMN_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) {t : ℕ} (ht : t ≤ decEndN p i r) :
    footMN p i r t ⊆ machRegion p := by
  unfold footMN
  split_ifs with h
  · exact Set.union_subset (dR_boxes_region fun x hx => decLFN_mem hp hi x (mem_dd.2 (by
        rcases List.mem_append.1 (mem_dd.1 hx) with h | h
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h)))
      (Set.union_subset (qFootN_region hp hi t) (Set.union_subset
        (dR_boxes_region (decLNu_mem hi)) (tokFootN_region hp hi h)))
  · rw [boxesOf_append, boxesOf_append]
    exact Set.union_subset (Set.union_subset (Set.union_subset
      (dR_boxes_region (decLC_mem hi)) (dR_boxes_region (decLSN_mem hi)))
      (dR_boxes_region (decLN_mem hi))) (Set.union_subset (restFootN_region hp hi t)
      (Set.union_subset (dR_boxes_region (decLFN_mem hp hi)) (finFootN_region hp hi ht)))

/-- **The main thread of a Z activation** lies in the region, up to its end. -/
theorem footMZ_region {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) {t : ℕ} (ht : t ≤ decEndZ p i r z) :
    footMZ p i r z t ⊆ machRegion p := by
  unfold footMZ
  split_ifs with h
  · exact Set.union_subset (dR_boxes_region fun x hx => decLFZ_mem hp hi x (mem_dd.2 (by
        rcases List.mem_append.1 (mem_dd.1 hx) with h | h
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h)))
      (Set.union_subset (qFootZ_region hp hi t) (Set.union_subset
        (dR_boxes_region (decLZu_mem hi)) (tokFootZ_region hp hi h)))
  · rw [boxesOf_append, boxesOf_append]
    exact Set.union_subset (Set.union_subset (Set.union_subset
      (dR_boxes_region (decLC_mem hi)) (dR_boxes_region (decLSZ_mem hi)))
      (dR_boxes_region (decLZ_mem hi))) (Set.union_subset (restFootZ_region hp hi t)
      (Set.union_subset (dR_boxes_region (decLFZ_mem hp hi)) (finFootZ_region hp hi ht)))

/-! ### The step -/

/-- The diagonals of the registers, the pieces at phase `T ≡ 0`, the control: `encM` split. -/
theorem decEncM_start {p : Program} {s : MState} (hinv : InvM p s) :
    encM p s = piecesAt (machPieces p) 1080 ∪ ctrlAt p s.pc ∪
      regsOn p s.reg (List.range (numRegs p)) := by
  rw [encM, machAt, regsAt_eq, piecesAt_mod _ (show s.T % 30 = 1080 % 30 by
    have := hinv.2.1; omega)]

/-- **The `decJz` step for a register of value `≥ 1`.** -/
theorem decStepNZ {p : Program} {r z : ℕ} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hrdy : ∀ r' < numRegs p, (s.reg r').Ready) (hins : p[s.pc]? = some (.decJz r z))
    (hsep : DecSep p s.pc r z) (hpos : (s.reg r).val ≠ 0) :
    ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ (∀ r', r' ≠ r → s'.reg r' = (s.reg r').later τ) ∧
      p.step s.cfg = some s'.cfg ∧ InvM p s' ∧ (∀ r' < numRegs p, (s'.reg r').Ready) ∧
      conway.evolve τ (encM p s) = encM p s' ∧
      ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p := by
  have hr := lt_numRegs_of_dec hins
  have hLM := machPieces_sep p hp
  have hinvR : ∀ r' ∈ List.range (numRegs p), (s.reg r').Inv :=
    fun r' h => hinv.2.2.1 r' (List.mem_range.1 h)
  obtain ⟨hTS, hTS30, hTA⟩ := decTS_facts p hins
  obtain ⟨-, -, -, hE30, hEnd, -⟩ := decN_times hp hins
  have t1 : 4260 ≤ decTS p s.pc r := by unfold decTS; omega
  have hCapZ : decCapZ p s.pc r = decTS p s.pc r + 12690 + 288 * callerIdx p r s.pc := rfl
  have hE1 : 4260 ≤ decEndN p s.pc r := by omega
  have hE2 : decCapZ p s.pc r + 272 ≤ decEndN p s.pc r := by omega
  -- the body
  have S1 := decBodyStage hp hins hsep s.reg hinvR
  -- the two threads
  obtain ⟨R', hval, hrdy', hM⟩ := decThreadN hp hins hsep ((hrdy r hr).later 3180)
    (by rw [RegS.val_later]; omega)
  have hT2 := decUnpZProc hp hins (decLZu_mem hins) hsep.sepZ hsep.flyZ hsep.winZ hsep.unpZ
    (decEndN p s.pc r) hE2
  have hCI := hM.par hT2 fun k hk => hsep.nThr (4260 + k) (by omega) (by omega)
  set Aact := decLMN p s.pc r ++ decLZu p s.pc r with hAdef
  have hA : ∀ x ∈ Aact, x ∈ machPieces p := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · simp only [decLMN, List.mem_append] at h
      rcases h with (((h | h) | h) | h) | h
      · exact decLC_mem hins x h
      · exact modGroup_mem hr x h
      · exact decLSN_mem hins x h
      · exact decLNu_mem hins x h
      · exact decLFN_mem hp hins x (mem_dd.2 (by
          rcases List.mem_append.1 (mem_dd.1 h) with h | h
          · exact List.mem_append_left _ (List.mem_append_right _ h)
          · exact List.mem_append_right _ h))
    · exact decLZu_mem hins x h
  have hCI' : Reaction (piecesAt Aact 4260 ∪ ((unitWL p s.pc decLWL).cells 4260 ∪
        ((unitWL p s.pc decRWL).cells 4260 ∪ ((unitWL p s.pc decDWL).cells 4260 ∪
          regAt p r ((s.reg r).later 3180)))))
      (piecesAt Aact (4260 + (decEndN p s.pc r - 4260)) ∪ (ctrlAt p (s.pc + 1) ∪ regAt p r R'))
      (decEndN p s.pc r - 4260)
      (fun k => footMN p s.pc r (4260 + k) ∪ (boxesOf (decLZu p s.pc r) ∪
        unpFootZ p s.pc r (4260 + k))) := by
    refine hCI.congrPQ ?_ ?_
    · rw [hAdef, piecesAt_append]
      ac_rfl
    · rw [hAdef, piecesAt_append, show 4260 + (decEndN p s.pc r - 4260) = decEndN p s.pc r by
        omega]
      ac_rfl
  have W2 := window_mem hLM hA 4260 (decEndN p s.pc r - 4260) hCI' fun k hk g hg hn =>
    hsep.nIdle (4260 + k) (by omega) (by omega) g hg hn
  set others := (List.range (numRegs p)).filter (fun r' => r' ≠ r) with hoth
  have hothR : ∀ r' ∈ others, r' < numRegs p ∧ r' ≠ r := fun r' h => by
    simp only [hoth, List.mem_filter, List.mem_range, ne_eq, decide_eq_true_eq] at h
    exact h
  have hinvO : ∀ r' ∈ others, ((s.reg r').later 3180).Inv :=
    fun r' h => (hinv.2.2.1 r' (hothR r' h).1).later 3180
  have S2 := W2.par (regsOn_reaction p (fun r' => (s.reg r').later 3180)
      (decEndN p s.pc r - 4260) others (List.nodup_range.filter _) hinvO
      fun j _ r₁ h₁ r₂ h₂ hne => (hsep.lanes r₁ (hothR r₁ h₁).1 r₂ (hothR r₂ h₂).1 hne).mono
        (regStrip_subset (hinvO r₁ h₁) p r₁ j) (regStrip_subset (hinvO r₂ h₂) p r₂ j))
    fun j hj a ha b hb => by
      obtain ⟨r', hr', hb⟩ := mem_stripsOn.1 hb
      exact hsep.nLane (4260 + j) (by omega) (by omega) r' (hothR r' hr').1 (hothR r' hr').2
        a ha b (regStrip_subset (hinvO r' hr') p r' j hb)
  have e12 : piecesAt (machPieces p) (1080 + 3180) ∪ ((unitWL p s.pc decLWL).cells 4260 ∪
        ((unitWL p s.pc decRWL).cells 4260 ∪ (unitWL p s.pc decDWL).cells 4260)) ∪
        regsOn p (fun r' => (s.reg r').later 3180) (List.range (numRegs p)) =
      piecesAt (machPieces p) 4260 ∪ ((unitWL p s.pc decLWL).cells 4260 ∪
        ((unitWL p s.pc decRWL).cells 4260 ∪ ((unitWL p s.pc decDWL).cells 4260 ∪
          regAt p r ((s.reg r).later 3180)))) ∪
        regsOn p (fun r' => (s.reg r').later 3180) others := by
    rw [regsOn_split _ _ hr, show 1080 + 3180 = 4260 by norm_num]
    ac_rfl
  have S := S1.seq_eq e12 S2
  set τ := 3180 + (decEndN p s.pc r - 4260) with hτ
  set s' : MState := ⟨s.pc + 1, s.T + τ, decRegs s r R' τ⟩ with hs'
  have eend : encM p s' = piecesAt (machPieces p) (4260 + (decEndN p s.pc r - 4260)) ∪
      (ctrlAt p (s.pc + 1) ∪ regAt p r R') ∪
        regsOn p (fun r' => ((s.reg r').later 3180).later (decEndN p s.pc r - 4260)) others := by
    rw [encM, machAt, regsAt_eq, regsOn_split _ _ hr]
    have h1 : piecesAt (machPieces p) s'.T =
        piecesAt (machPieces p) (4260 + (decEndN p s.pc r - 4260)) :=
      piecesAt_mod _ (by have := hinv.2.1; change (s.T + τ) % 30 = _; omega)
    have h2 : regsOn p s'.reg others =
        regsOn p (fun r' => ((s.reg r').later 3180).later (decEndN p s.pc r - 4260)) others :=
      regsOn_congr fun r' h => by
        change decRegs s r R' τ r' = _
        rw [decRegs, Function.update_of_ne (hothR r' h).2, RegS.later_later', hτ]
    have h3 : s'.reg r = R' := by
      change decRegs s r R' τ r = R'
      rw [decRegs, Function.update_self]
    rw [h1, h2, h3]
    simp only [union_assoc]
    rfl
  refine ⟨τ, s', by omega, fun r' hne => ?_, ?_, ?_, fun r' hr' => ?_, ?_, ?_⟩
  · change decRegs s r R' τ r' = _
    rw [decRegs, Function.update_of_ne hne]
  · -- the counter machine
    rw [Program.step]
    change (p[s.pc]?.bind fun ins => ins.exec s.cfg) = _
    rw [hins, Option.bind_some]
    simp only [Instr.exec, MState.cfg, hpos, ↓reduceIte]
    change some (⟨s.pc + 1, Function.update (fun r' => (s.reg r').val) r ((s.reg r).val - 1)⟩ :
      Cfg) = some ⟨s.pc + 1, fun r' => (decRegs s r R' τ r').val⟩
    refine congrArg some (Cfg.ext rfl (funext fun r' => ?_))
    by_cases he : r' = r
    · subst he
      dsimp only
      rw [Function.update_self, decRegs, Function.update_self]
      rw [RegS.val_later] at hval
      omega
    · dsimp only
      rw [Function.update_of_ne he, decRegs, Function.update_of_ne he, RegS.val_later]
  · -- the invariant
    refine ⟨succ_lt_of_dec hp hins, ?_, fun r' hr' => ?_, fun r' hr' => ?_⟩
    · have := hinv.2.1
      change (s.T + τ) % 30 = 0
      omega
    · change (decRegs s r R' τ r').Inv
      by_cases he : r' = r
      · subst he
        rw [decRegs, Function.update_self]
        exact hrdy'.1
      · rw [decRegs, Function.update_of_ne he]
        exact (hinv.2.2.1 r' hr').later τ
    · have he : r' ≠ r := by omega
      change (decRegs s r R' τ r').val = 0
      rw [decRegs, Function.update_of_ne he, RegS.val_later]
      exact hinv.2.2.2 r' hr'
  · change (decRegs s r R' τ r').Ready
    by_cases he : r' = r
    · subst he
      rw [decRegs, Function.update_self]
      exact hrdy'
    · rw [decRegs, Function.update_of_ne he]
      exact (hrdy r' hr').later τ
  · rw [decEncM_start hinv, eend]
    exact S.evolve_eq
  · intro j hj
    rw [decEncM_start hinv]
    obtain ⟨hU, -, -, -⟩ := decAnchors hp hins
    refine (S.subset j hj).trans ?_
    have hstrips : ∀ (reg : ℕ → RegS) (l : List ℕ) (k : ℕ), (∀ r' ∈ l, r' < numRegs p) →
        (∀ r' ∈ l, (reg r').Inv) → stripsOn p reg l k ⊆ machRegion p := by
      intro reg l k hl hi' x hx
      obtain ⟨r', hr', hx⟩ := mem_stripsOn.1 hx
      exact dR_modLanes_region (dR_uMin_le_mod (hl r' hr'))
        (regStrip_subset (hi' r' hr') p r' k hx)
    have hbody : bodyDecBox p s.pc ⊆ machRegion p := by
      obtain ⟨-, hA, -, -⟩ := decAnchors hp hins
      have := unitD_uv p s.pc
      refine dR_region_of (m := A p s.pc - 180) (fun c hc => ?_) (by omega)
      obtain ⟨d, hd, rfl⟩ := hc
      have : -180 ≤ d.1 - d.2 := bodyDecRegion_u hd
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    split_ifs with hj1
    · refine Set.union_subset (Set.union_subset (dR_pieces_region p) hbody) ?_
      exact hstrips _ _ _ (fun r' h => List.mem_range.1 h) hinvR
    · refine Set.union_subset (Set.union_subset (dR_pieces_region p) (Set.union_subset
        (footMN_region hp hins (by omega)) (Set.union_subset
          (dR_boxes_region (decLZu_mem hins)) (unpFootZ_region hp hins _)))) ?_
      exact hstrips _ _ _ (fun r' h => (hothR r' h).1) hinvO

/-- **The `decJz` step for a register of value `0`.** -/
theorem decStepZ {p : Program} {r z : ℕ} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hrdy : ∀ r' < numRegs p, (s.reg r').Ready) (hins : p[s.pc]? = some (.decJz r z))
    (hsep : DecSep p s.pc r z) (h0 : (s.reg r).val = 0) :
    ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ (∀ r', r' ≠ r → s'.reg r' = (s.reg r').later τ) ∧
      p.step s.cfg = some s'.cfg ∧ InvM p s' ∧ (∀ r' < numRegs p, (s'.reg r').Ready) ∧
      conway.evolve τ (encM p s) = encM p s' ∧
      ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p := by
  have hr := lt_numRegs_of_dec hins
  have hLM := machPieces_sep p hp
  have hinvR : ∀ r' ∈ List.range (numRegs p), (s.reg r').Inv :=
    fun r' h => hinv.2.2.1 r' (List.mem_range.1 h)
  obtain ⟨hTS, hTS30, hTA⟩ := decTS_facts p hins
  obtain ⟨-, -, -, hE30, hEnd, hDT⟩ := decZ_times hp hins
  have hEZ : decT0Z p s.pc r z ≤ decEndZ p s.pc r z := by unfold decEndZ; omega
  have hDZ : decDispZ p s.pc r = decTS p s.pc r + 13362 + 288 * callerIdx p r s.pc := rfl
  have t1 : 4260 ≤ decTS p s.pc r := by unfold decTS; omega
  have hCapN : decCapN p s.pc r = decTS p s.pc r + 10650 + 288 * callerIdx p r s.pc := rfl
  have hE1 : 4260 ≤ decEndZ p s.pc r z := by omega
  have hE2 : decCapN p s.pc r + 292 ≤ decEndZ p s.pc r z := by omega
  -- the body
  have S1 := decBodyStage hp hins hsep s.reg hinvR
  -- the two threads
  have hM := decThreadZ hp hins hsep ((hrdy r hr).later 3180) (by rw [RegS.val_later]; exact h0)
  have hT2 := decUnpNProc hp hins (decLNu_mem hins) hsep.sepN hsep.flyN hsep.winN hsep.unpN
    (decEndZ p s.pc r z) hE2
  have hCI0 := hM.par hT2 fun k hk => hsep.zThr (4260 + k) (by omega) (by omega)
  have hCI := hCI0.par (gateIdle p r 4260 (decEndZ p s.pc r z - 4260))
    fun k hk => hsep.zGate (4260 + k) (by omega) (by omega)
  have hgate : gateP p r ∈ machPieces p :=
    decModule_mem hr (by simp [moduleSpecs, incGateSpec])
  set Aact := decLMZ p s.pc r z ++ decLNu p s.pc r ++ [gateP p r] with hAdef
  have hA : ∀ x ∈ Aact, x ∈ machPieces p := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    swap
    · rw [List.mem_singleton.1 hx]; exact hgate
    rcases List.mem_append.1 hx with h | h
    · simp only [decLMZ, List.mem_append] at h
      rcases h with (((h | h) | h) | h) | h
      · exact decLC_mem hins x h
      · exact modGroup_mem hr x h
      · exact decLSZ_mem hins x h
      · exact decLZu_mem hins x h
      · exact decLFZ_mem hp hins x (mem_dd.2 (by
          rcases List.mem_append.1 (mem_dd.1 h) with h | h
          · exact List.mem_append_left _ (List.mem_append_right _ h)
          · exact List.mem_append_right _ h))
    · exact decLNu_mem hins x h
  have hCI' : Reaction (piecesAt Aact 4260 ∪ ((unitWL p s.pc decDWL).cells 4260 ∪
        ((unitWL p s.pc decRWL).cells 4260 ∪ ((unitWL p s.pc decLWL).cells 4260 ∪
          regAt p r ((s.reg r).later 3180)))))
      (piecesAt Aact (4260 + (decEndZ p s.pc r z - 4260)) ∪ (ctrlAt p z ∪ regAt p r
        (((s.reg r).later 3180).later (decEndZ p s.pc r z - 4260))))
      (decEndZ p s.pc r z - 4260)
      (fun k => footMZ p s.pc r z (4260 + k) ∪ (boxesOf (decLNu p s.pc r) ∪
        unpFootN p s.pc r (4260 + k)) ∪ gateFoot p r) := by
    refine hCI.congrPQ ?_ ?_
    · rw [hAdef, piecesAt_append, piecesAt_append]
      ac_rfl
    · rw [hAdef, piecesAt_append, piecesAt_append,
        show 4260 + (decEndZ p s.pc r z - 4260) = decEndZ p s.pc r z by omega]
      ac_rfl
  have W2 := window_mem hLM hA 4260 (decEndZ p s.pc r z - 4260) hCI' fun k hk g hg hn =>
    hsep.zIdle (4260 + k) (by omega) (by omega) g hg hn
  set others := (List.range (numRegs p)).filter (fun r' => r' ≠ r) with hoth
  have hothR : ∀ r' ∈ others, r' < numRegs p ∧ r' ≠ r := fun r' h => by
    simp only [hoth, List.mem_filter, List.mem_range, ne_eq, decide_eq_true_eq] at h
    exact h
  have hinvO : ∀ r' ∈ others, ((s.reg r').later 3180).Inv :=
    fun r' h => (hinv.2.2.1 r' (hothR r' h).1).later 3180
  have S2 := W2.par (regsOn_reaction p (fun r' => (s.reg r').later 3180)
      (decEndZ p s.pc r z - 4260) others (List.nodup_range.filter _) hinvO
      fun j _ r₁ h₁ r₂ h₂ hne => (hsep.lanes r₁ (hothR r₁ h₁).1 r₂ (hothR r₂ h₂).1 hne).mono
        (regStrip_subset (hinvO r₁ h₁) p r₁ j) (regStrip_subset (hinvO r₂ h₂) p r₂ j))
    fun j hj a ha b hb => by
      obtain ⟨r', hr', hb⟩ := mem_stripsOn.1 hb
      exact hsep.zLane (4260 + j) (by omega) (by omega) r' (hothR r' hr').1 (hothR r' hr').2
        a ha b (regStrip_subset (hinvO r' hr') p r' j hb)
  have e12 : piecesAt (machPieces p) (1080 + 3180) ∪ ((unitWL p s.pc decLWL).cells 4260 ∪
        ((unitWL p s.pc decRWL).cells 4260 ∪ (unitWL p s.pc decDWL).cells 4260)) ∪
        regsOn p (fun r' => (s.reg r').later 3180) (List.range (numRegs p)) =
      piecesAt (machPieces p) 4260 ∪ ((unitWL p s.pc decDWL).cells 4260 ∪
        ((unitWL p s.pc decRWL).cells 4260 ∪ ((unitWL p s.pc decLWL).cells 4260 ∪
          regAt p r ((s.reg r).later 3180)))) ∪
        regsOn p (fun r' => (s.reg r').later 3180) others := by
    rw [regsOn_split _ _ hr, show 1080 + 3180 = 4260 by norm_num]
    ac_rfl
  have S := S1.seq_eq e12 S2
  set τ := 3180 + (decEndZ p s.pc r z - 4260) with hτ
  set s' : MState := ⟨z, s.T + τ, fun r' => (s.reg r').later τ⟩ with hs'
  have eend : encM p s' = piecesAt (machPieces p) (4260 + (decEndZ p s.pc r z - 4260)) ∪
      (ctrlAt p z ∪ regAt p r (((s.reg r).later 3180).later (decEndZ p s.pc r z - 4260))) ∪
        regsOn p (fun r' => ((s.reg r').later 3180).later (decEndZ p s.pc r z - 4260)) others := by
    rw [encM, machAt, regsAt_eq, regsOn_split _ _ hr]
    have h1 : piecesAt (machPieces p) s'.T =
        piecesAt (machPieces p) (4260 + (decEndZ p s.pc r z - 4260)) :=
      piecesAt_mod _ (by have := hinv.2.1; change (s.T + τ) % 30 = _; omega)
    have h2 : regsOn p s'.reg others =
        regsOn p (fun r' => ((s.reg r').later 3180).later (decEndZ p s.pc r z - 4260)) others :=
      regsOn_congr fun r' _ => by
        change (s.reg r').later τ = _
        rw [RegS.later_later', hτ]
    have h3 : s'.reg r = ((s.reg r).later 3180).later (decEndZ p s.pc r z - 4260) := by
      change (s.reg r).later τ = _
      rw [RegS.later_later', hτ]
    rw [h1, h2, h3]
    simp only [union_assoc]
    rfl
  refine ⟨τ, s', by omega, fun r' _ => rfl, ?_, ?_, fun r' hr' => (hrdy r' hr').later τ, ?_, ?_⟩
  · -- the counter machine
    rw [Program.step]
    change (p[s.pc]?.bind fun ins => ins.exec s.cfg) = _
    rw [hins, Option.bind_some]
    simp only [Instr.exec, MState.cfg, h0, ↓reduceIte]
    exact congrArg some (Cfg.ext rfl (funext fun r' => (RegS.val_later _ _).symm))
  · -- the invariant
    refine ⟨lt_of_dec hp hins, ?_, fun r' hr' => (hinv.2.2.1 r' hr').later τ,
      fun r' hr' => ?_⟩
    · have := hinv.2.1
      change (s.T + τ) % 30 = 0
      omega
    · change ((s.reg r').later τ).val = 0
      rw [RegS.val_later]
      exact hinv.2.2.2 r' hr'
  · rw [decEncM_start hinv, eend]
    exact S.evolve_eq
  · intro j hj
    rw [decEncM_start hinv]
    obtain ⟨hU, -, -, -⟩ := decAnchors hp hins
    refine (S.subset j hj).trans ?_
    have hstrips : ∀ (reg : ℕ → RegS) (l : List ℕ) (k : ℕ), (∀ r' ∈ l, r' < numRegs p) →
        (∀ r' ∈ l, (reg r').Inv) → stripsOn p reg l k ⊆ machRegion p := by
      intro reg l k hl hi' x hx
      obtain ⟨r', hr', hx⟩ := mem_stripsOn.1 hx
      exact dR_modLanes_region (dR_uMin_le_mod (hl r' hr'))
        (regStrip_subset (hi' r' hr') p r' k hx)
    have hbody : bodyDecBox p s.pc ⊆ machRegion p := by
      obtain ⟨-, hA, -, -⟩ := decAnchors hp hins
      have := unitD_uv p s.pc
      refine dR_region_of (m := A p s.pc - 180) (fun c hc => ?_) (by omega)
      obtain ⟨d, hd, rfl⟩ := hc
      have : -180 ≤ d.1 - d.2 := bodyDecRegion_u hd
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    split_ifs with hj1
    · refine Set.union_subset (Set.union_subset (dR_pieces_region p) hbody) ?_
      exact hstrips _ _ _ (fun r' h => List.mem_range.1 h) hinvR
    · refine Set.union_subset (Set.union_subset (dR_pieces_region p) (Set.union_subset
        (Set.union_subset (footMZ_region hp hins (by omega)) (Set.union_subset
          (dR_boxes_region (decLNu_mem hins)) (unpFootN_region hp hins _)))
        (fun c hc => dR_pieces_region p (mem_boxesOf.2 ⟨_, hgate, gateFoot_subset p r hc⟩))))
        ?_
      exact hstrips _ _ _ (fun r' h => (hothR r' h).1) hinvO

/-- **The `decJz` step** (every register value): for a well-formed program, a state with the
invariant (`InvM` and every register ready) and the instruction `decJz r z` at the program counter,
given the separation facts `DecSep` of the activation, the machine evolves `encM s` into `encM s'`
for the next state `s'` of the counter machine, inside the region of the machine, in `τ > 0`
generations, with every other register `τ` generations later and every register ready. -/
theorem decJz_step_full {p : Program} {r z : ℕ} (hp : p.WellFormed) (s : MState)
    (hinv : InvM p s) (hrdy : ∀ r' < numRegs p, (s.reg r').Ready)
    (hins : p[s.pc]? = some (.decJz r z)) (hsep : DecSep p s.pc r z) :
    ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ (∀ r', r' ≠ r → s'.reg r' = (s.reg r').later τ) ∧
      p.step s.cfg = some s'.cfg ∧ InvM p s' ∧ (∀ r' < numRegs p, (s'.reg r').Ready) ∧
      conway.evolve τ (encM p s) = encM p s' ∧
      ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p := by
  by_cases h0 : (s.reg r).val = 0
  · exact decStepZ hp s hinv hrdy hins hsep h0
  · exact decStepNZ hp s hinv hrdy hins hsep h0

/-- **The `decJz` step in the form of the `dec` field of `MachineSteps`** (with `MInv p s`
unfolded: `InvM p s ∧ ∀ r < numRegs p, (s.reg r).Ready`), conditional only on `DecSep`. -/
theorem decJz_step' {p : Program} (hp : p.WellFormed) (hsep : ∀ (s : MState) (r z : ℕ),
      (InvM p s ∧ ∀ r' < numRegs p, (s.reg r').Ready) → p[s.pc]? = some (.decJz r z) →
      DecSep p s.pc r z) :
    ∀ (s : MState) (r z : ℕ), (InvM p s ∧ ∀ r' < numRegs p, (s.reg r').Ready) →
      p[s.pc]? = some (.decJz r z) →
      ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ p.step s.cfg = some s'.cfg ∧
        (InvM p s' ∧ ∀ r' < numRegs p, (s'.reg r').Ready) ∧
        conway.evolve τ (encM p s) = encM p s' ∧
        ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p := by
  intro s r z hm hins
  obtain ⟨τ, s', h1, -, h3, h4, h5, h6, h7⟩ :=
    decJz_step_full hp s hm.1 hm.2 hins (hsep s r z hm hins)
  exact ⟨τ, s', h1, h3, ⟨h4, h5⟩, h6, h7⟩

end LP

end LeanTheory.Life
