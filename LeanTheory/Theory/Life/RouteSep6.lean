/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RouteSep5

/-!
# The legs of the `decJz` links in the module zones

The legs of the routes of a `decJz` instruction outside the band and the unit slabs:

* `legRightDown`, `legRzoneWd`, `ztok_chain`: the KZ token link down the Z token channel of the
  right zone and along its depth line `w_d` to the Z token station;
* `nzport_module_own`, `nzport_corner`, `legLeftUp`: the NZ answer from its station along its port
  line to the NZ answer channel of the left zone, and up the channel to the band;
* `legRzoneVd`, `legRightUp`: the Z answer from its station column along its depth line `v_d` to
  the Z answer channel of the right zone, and up the channel to the band;
* `unitLink_sep`: a link from a source column of a unit with any separated chain of corners.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The right zone -/

/-- **The Z token channel leg of a KZ link** (`SE`, down the Z token channel of caller `j` of
module `r`, from `BACK` to the depth line `w_d`), given the check of the corners of its owner. -/
theorem legRightDown {p : Program} (hp : p.WellFormed) {b c : ℤ} {r : ℕ} {j : ℤ}
    {own : List Corner} (hsplit : OwnSplit p b own) (hb : 1 ≤ b ∧ b ≤ N p + R p)
    (hr : (r : ℤ) < R p) (hj : 0 ≤ j ∧ j < D p) (hown' : Owns p b (.right r j 0))
    (h1 : CornerOK p ⟨2, U p r + zTokChan p j, trackBack p b 2 c, .band b (9 - 2) false⟩)
    (h2 : CornerOK p ⟨3, U p r + zTokChan p j, zTokDepth p j, .right r j 2⟩)
    (hown : ∀ c' ∈ own, c'.tag ≠ .band b (9 - 2) false → c'.tag ≠ .right r j 2 →
      FarRect (cornerSpec c').bx (U p r + zTokChan p j - 4) (U p r + zTokChan p j + 4)
        (trackBack p b 2 c + 11) (zTokDepth p j - 7)) :
    LegOK p ⟨2, U p r + zTokChan p j, trackBack p b 2 c, .band b (9 - 2) false⟩
      ⟨3, U p r + zTokChan p j, zTokDepth p j, .right r j 2⟩ := by
  have hts := tracks_range p b 2 c
  have hf := layout_facts p
  have hz := fixp_bounds (uR p + 124 * qOf p j + 62) (1 - zTokDepth p j % 2)
  have hU := (U_ge p (r := r) (by omega)).1
  have hcd : U p r + 1471 + 144 * D p + 124 * (D p - 1 - j) ≤ U p r + zTokChan p j ∧
      U p r + zTokChan p j ≤ U p r + 1472 + 144 * D p + 124 * (D p - 1 - j) := by
    unfold zTokChan uR qOf at *; omega
  refine legOK_of hp h1 h2 (u1 := U p r + zTokChan p j - 4) (u2 := U p r + zTokChan p j + 4)
    (v1 := trackBack p b 2 c + 11) (v2 := zTokDepth p j - 7) ?_ (zone_unit ?_) ?_ ?_
  · intro cu cv r1 r2
    simp only [Ray, outD, behindIn] at r1 r2 ⊢
    omega
  · unfold modLeft at *; omega
  · intro r' s' _ hs'
    by_cases h : r' = r
    · subst h; exact right_module_own (by omega) s' hs'
    · exact zone_module_other (r := r) (by unfold modLeft modRight at *; omega) r' s' h hs'
  · refine hsplit _ hown fun c' _ hd hband _ n2 =>
      right_corner hr hj hown' (by omega) (by omega) hd hband (Or.inl ⟨hcd.1, hcd.2, n2⟩)

/-- **The depth leg of a KZ link** (`SW`, along `w_d` of caller `j` of module `r`, from the Z token
channel to the Z token station column). -/
theorem legRzoneWd {p : Program} (hp : p.WellFormed) {r : ℕ} {j : ℤ} (hr : (r : ℤ) < R p)
    (hj : 0 ≤ j ∧ j < D p)
    (h1 : CornerOK p ⟨3, U p r + zTokChan p j, zTokDepth p j, .right r j 2⟩)
    (h2 : CornerOK p ⟨0, U p r + zTokStation j, zTokDepth p j, .right r j 3⟩) :
    LegOK p ⟨3, U p r + zTokChan p j, zTokDepth p j, .right r j 2⟩
      ⟨0, U p r + zTokStation j, zTokDepth p j, .right r j 3⟩ := by
  have hf := layout_facts p
  have hz := fixp_bounds (uR p + 124 * qOf p j + 62) (1 - zTokDepth p j % 2)
  have hd := zAnsDepth_eq p j
  have hU := (U_ge p (r := r) (by omega)).1
  have hwd : zTokDepth p j = 1561 + 180 * (D p - 1 - j) := by
    unfold zTokDepth qOf at *; omega
  refine legOK_of hp h1 h2 (u1 := U p r + zTokStation j + 9)
    (u2 := U p r + zTokChan p j - 9) (v1 := zTokDepth p j - 2) (v2 := zTokDepth p j + 6) ?_
    (zone_unit ?_) ?_ ?_
  · intro cu cv r1 r2
    simp only [Ray, outD, behindIn] at r1 r2 ⊢
    omega
  · unfold modLeft zTokStation at *; omega
  · intro r' s' _ hs'
    by_cases h : r' = r
    · subst h
      exact rzone_module_own (by unfold zTokStation; omega) (by omega) s' hs'
    · exact zone_module_other (r := r)
        (by unfold modLeft modRight zTokStation zTokChan uR qOf at *; omega) r' s' h hs'
  · intro c' hc' n1 n2
    exact rzone_corner (r := r) hj
      ⟨by unfold zTokStation; omega, by unfold modRight zTokChan uR qOf at *; omega⟩
      (allCorners_valid hp c' hc') (Or.inr ⟨hwd, n1, n2⟩)

/-- The parities of the corners of a KZ link. -/
theorem ztokCorners_par {p : Program} {b c H : ℤ} {r : ℕ} {j : ℤ} (hH : (H - c) % 2 = 0)
    (hd : (U p r + zTokChan p j - c) % 2 = 0)
    (hv1 : (U p r + zTokChan p j + zTokDepth p j) % 2 = 1)
    (hv2 : (U p r + zTokStation j + zTokDepth p j) % 2 = 1) :
    ∀ x ∈ ztokCorners p b c H r j, CPar x := by
  have ho := trackOut_par p b 2 c
  have hk := trackBack_par p b 2 c
  intro x hx
  rcases mem_ztokCorners.1 hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [CPar, rfCU, rfCV] <;> omega

/-- The images of the corners of a KZ link are below `8`. -/
theorem ztokCorners_k {p : Program} {b c H : ℤ} {r : ℕ} {j : ℤ} :
    ∀ x ∈ ztokCorners p b c H r j, x.k < 8 := by
  intro x hx
  rcases mem_ztokCorners.1 hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- **The chain of a KZ link**: its legs in the band, down the Z token channel and along `w_d`,
given the checks of the corners of its owner. -/
theorem ztok_chain {p : Program} (hp : p.WellFormed) {b c H : ℤ} {r : ℕ} {j : ℤ}
    {own : List Corner} (hsplit : OwnSplit p b own) (hb : 1 ≤ b ∧ b ≤ N p + R p)
    (hr : (r : ℤ) < R p) (hj : 0 ≤ j ∧ j < D p) (hown' : Owns p b (.right r j 0))
    (hok : ∀ x ∈ ztokCorners p b c H r j, CornerOK p x)
    (hown2 : ∀ c' ∈ own, c'.tag ≠ .band b 2 true → c'.tag ≠ .band b (9 - 2) true →
      FarRect (cornerSpec c').bx (H - 4) (H + 4) (trackOut p b 2 c + 11)
        (trackBack p b 2 c - 7))
    (hown4 : ∀ c' ∈ own, c'.tag ≠ .band b (9 - 2) false → c'.tag ≠ .right r j 2 →
      FarRect (cornerSpec c').bx (U p r + zTokChan p j - 4) (U p r + zTokChan p j + 4)
        (trackBack p b 2 c + 11) (zTokDepth p j - 7)) :
    ChainOK p (ztokCorners p b c H r j) := by
  have h1 := hok _ (mem_ztokCorners.2 (Or.inl rfl))
  have h2 := hok _ (mem_ztokCorners.2 (Or.inr (Or.inl rfl)))
  have h3 := hok _ (mem_ztokCorners.2 (Or.inr (Or.inr (Or.inl rfl))))
  have h4 := hok _ (mem_ztokCorners.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 := hok _ (mem_ztokCorners.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 := hok _ (mem_ztokCorners.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  simp only [ztokCorners, bandCorners, List.cons_append, List.nil_append, ChainOK]
  exact ⟨h1, legOut hp (Or.inl rfl) hb (by norm_num) h1 h2, h2,
    legHair hp hsplit hb (by norm_num) h2 h3 hown2, h3,
    legBack hp (Or.inr rfl) hb (by norm_num) h3 h4, h4,
    legRightDown hp hsplit hb hr hj hown' h4 h5 hown4, h5, legRzoneWd hp hr hj h5 h6, h6⟩

/-! ### The NZ answer in the left zone -/

/-- **The port line of the NZ answer of caller `j` is clear of module `r`**: a rectangle on the
port line `v = 1325 + 144 j`, left of the stations (`u ≤ U_r - 549`), is far from every piece of
the module. -/
theorem nzport_module_own {p : Program} {r : ℕ} {j u1 u2 : ℤ} (hj : 0 ≤ j ∧ j < D p)
    (hu2 : u2 ≤ U p r - 549) :
    ∀ s ∈ moduleSpecs p r, FarRect s.bx u1 u2 (1325 + 144 * j - 2) (1325 + 144 * j + 6) := by
  intro s hs
  have hb := base_boxes
  have hD : (D p) = (numCallers p : ℤ) := rfl
  have hm := modD_uv p r
  unfold FarRect
  rcases moduleSpecs_cls p r hs with ⟨i, ph, hi⟩ | ph | ph | ⟨m, ph, hm'⟩ |
    ⟨i, j', ph, hi, hj'⟩ | ⟨i, j', ph, hi, hj'⟩ | ph | ph
  · have := dz2g_facts i hi
    simp only [PSpec.bx_mk]; omega
  · simp only [PSpec.bx_mk]; omega
  · simp only [PSpec.bx_mk]; omega
  · simp only [PSpec.bx_mk]; omega
  · have := stNZ_cases i hi
    simp only [PSpec.bx_mk]
    rcases lt_trichotomy (j' : ℤ) j with h | h | h <;> omega
  · have := stZ_cases i hi
    simp only [PSpec.bx_mk]; omega
  · simp only [PSpec.bx_mk]; omega
  · simp only [PSpec.bx_mk]; omega

/-- **The port line of the NZ answer of caller `j` of module `r` is clear of the corners**: the
reflector of every corner other than the NZ answer port corner is far from a rectangle on the
port line inside the zones of module `r`, left of its stations. -/
theorem nzport_corner {p : Program} {r : ℕ} {j u1 u2 : ℤ} (hr : (r : ℤ) < R p)
    (hj : 0 ≤ j ∧ j < D p) (hu : U p r + modLeft p + 20 ≤ u1 ∧ u2 ≤ U p r - 549) {c : Corner}
    (hd : Desc p c) (hne : c.tag ≠ .left r (2 * D p + 2 + 2 * j)) :
    FarRect (cornerSpec c).bx u1 u2 (1325 + 144 * j - 2) (1325 + 144 * j + 6) := by
  have hf := layout_facts p
  refine corner_farRect ?_
  obtain ⟨hv, -, -, hport⟩ := hd
  obtain ⟨k', u, v, tag⟩ := c
  simp only at hne hport ⊢
  cases tag with
  | band b' n h =>
    simp only [Valid] at hv
    obtain ⟨hv1', hv2', hv3, hv4, hv5, hv6, hv7, hv8⟩ := hv
    omega
  | halt a' => simp only [Valid] at hv; omega
  | slab a' t => simp only [Valid] at hv; omega
  | left r' idx' =>
    simp only [Valid] at hv
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · have hne' : idx' ≠ 2 * D p + 2 + 2 * j := fun h' => hne (by rw [h'])
      rcases hport _ idx' rfl with ⟨h0, h1, h2⟩ | ⟨h1, h2⟩ | ⟨j', h0, h1, h2, h3⟩ |
        ⟨j', h0, h1, h2, h3⟩
      · simp only [decPortV] at h2; omega
      · simp only [incPortV] at h2; omega
      · simp only [nzTokPortV] at h3
        rcases lt_or_ge j' (j + 1) with h | h <;> omega
      · simp only [nzAnsPortV] at h3
        have : j' ≠ j := fun h'' => hne' (by rw [h2, h''])
        rcases lt_or_gt_of_ne this with h | h <;> omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega
  | right r' j' w =>
    simp only [Valid] at hv
    rcases lt_trichotomy r' r with h | rfl | h
    · have := module_gap p (r := r') (r' := r) h
      unfold modLeft modRight at *; omega
    · omega
    · have := module_gap p (r := r) (r' := r') h
      unfold modLeft modRight at *; omega

/-- **The channel leg of an NZ answer** (`NW`, up the NZ answer channel `idx` of the left zone of
module `r`, from the port corner to the `OUT` track of slot `3`), given the check of the corners of
its owner. -/
theorem legLeftUp {p : Program} (hp : p.WellFormed) {b chan port : ℤ} {r : ℕ} {idx : ℤ}
    {own : List Corner} (hsplit : OwnSplit p b own) (hb : 1 ≤ b ∧ b ≤ N p + R p)
    (hr : (r : ℤ) < R p) (hidx : 0 ≤ idx ∧ idx ≤ 4 * D p)
    (hcd : U p r - 794 - 62 * idx ≤ chan ∧ chan ≤ U p r - 793 - 62 * idx)
    (hown' : Owns p b (.left r idx))
    (h1 : CornerOK p ⟨0, chan, port, .left r idx⟩)
    (h2 : CornerOK p ⟨5, chan, trackOut p b 3 chan, .band b 3 false⟩)
    (hown : ∀ c' ∈ own, c'.tag ≠ .left r idx → c'.tag ≠ .band b 3 false →
      FarRect (cornerSpec c').bx (chan - 4) (chan + 4) (trackOut p b 3 chan + 11) (port - 7)) :
    LegOK p ⟨0, chan, port, .left r idx⟩ ⟨5, chan, trackOut p b 3 chan, .band b 3 false⟩ := by
  have hts := tracks_range p b 3 chan
  have hf := layout_facts p
  have hl := left_range p hidx hcd
  refine legOK_of hp h1 h2 (u1 := chan - 4) (u2 := chan + 4) (v1 := trackOut p b 3 chan + 11)
    (v2 := port - 7) ?_ (zone_unit ?_) ?_ ?_
  · intro cu cv r1 r2
    simp only [Ray, outD, behindIn] at r1 r2 ⊢
    omega
  · have := (U_ge p (r := r) (by omega)).1
    omega
  · intro r' s' _ hs'
    by_cases h : r' = r
    · subst h; exact left_module_own hl.2 s' hs'
    · exact zone_module_other (r := r) (by unfold modRight at *; omega) r' s' h hs'
  · refine hsplit _ hown fun c' _ hd hband n1 _ =>
      left_corner hr hidx hcd hown' (by omega) (by omega) hd hband n1

/-! ### The Z answer in the right zone -/

/-- **The depth leg of a Z answer** (`NE`, along `v_d` of caller `j` of module `r`, from the Z
answer station column to the Z answer channel). -/
theorem legRzoneVd {p : Program} (hp : p.WellFormed) {r : ℕ} {j : ℤ} (hr : (r : ℤ) < R p)
    (hj : 0 ≤ j ∧ j < D p)
    (h1 : CornerOK p ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩)
    (h2 : CornerOK p ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩) :
    LegOK p ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩
      ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩ := by
  have hf := layout_facts p
  have hz := fixp_bounds (uR p + 124 * qOf p j) (1 - zAnsDepth p j % 2)
  have hd := zAnsDepth_eq p j
  have hU := (U_ge p (r := r) (by omega)).1
  refine legOK_of hp h1 h2 (u1 := U p r + zAnsStation j + 9)
    (u2 := U p r + zAnsChan p j - 9) (v1 := zAnsDepth p j - 2) (v2 := zAnsDepth p j + 6) ?_
    (zone_unit ?_) ?_ ?_
  · intro cu cv r1 r2
    simp only [Ray, outD, behindIn] at r1 r2 ⊢
    omega
  · unfold modLeft zAnsStation at *; omega
  · intro r' s' _ hs'
    by_cases h : r' = r
    · subst h
      exact rzone_module_own (by unfold zAnsStation; omega) (by unfold qOf at hd; omega) s' hs'
    · exact zone_module_other (r := r)
        (by unfold modLeft modRight zAnsStation zAnsChan uR qOf at *; omega) r' s' h hs'
  · intro c' hc' n1 n2
    exact rzone_corner (r := r) hj
      ⟨by unfold zAnsStation; omega, by unfold modRight zAnsChan uR qOf at *; omega⟩
      (allCorners_valid hp c' hc') (Or.inl ⟨by unfold qOf at hd; omega, n1, n2⟩)

/-- **The channel leg of a Z answer** (`NW`, up the Z answer channel of caller `j` of module `r`,
from `v_d` to the `OUT` track of slot `4`), given the check of the corners of its owner. -/
theorem legRightUp {p : Program} (hp : p.WellFormed) {b : ℤ} {r : ℕ} {j : ℤ}
    {own : List Corner} (hsplit : OwnSplit p b own) (hb : 1 ≤ b ∧ b ≤ N p + R p)
    (hr : (r : ℤ) < R p) (hj : 0 ≤ j ∧ j < D p) (hown' : Owns p b (.right r j 0))
    (h1 : CornerOK p ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩)
    (h2 : CornerOK p ⟨5, U p r + zAnsChan p j, trackOut p b 4 (U p r + zAnsChan p j),
      .band b 4 false⟩)
    (hown : ∀ c' ∈ own, c'.tag ≠ .right r j 1 → c'.tag ≠ .band b 4 false →
      FarRect (cornerSpec c').bx (U p r + zAnsChan p j - 4) (U p r + zAnsChan p j + 4)
        (trackOut p b 4 (U p r + zAnsChan p j) + 11) (zAnsDepth p j - 7)) :
    LegOK p ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩
      ⟨5, U p r + zAnsChan p j, trackOut p b 4 (U p r + zAnsChan p j), .band b 4 false⟩ := by
  have hts := tracks_range p b 4 (U p r + zAnsChan p j)
  have hf := layout_facts p
  have hz := fixp_bounds (uR p + 124 * qOf p j) (1 - zAnsDepth p j % 2)
  have hU := (U_ge p (r := r) (by omega)).1
  have hcd : U p r + 1409 + 144 * D p + 124 * (D p - 1 - j) ≤ U p r + zAnsChan p j ∧
      U p r + zAnsChan p j ≤ U p r + 1410 + 144 * D p + 124 * (D p - 1 - j) := by
    unfold zAnsChan uR qOf at *; omega
  refine legOK_of hp h1 h2 (u1 := U p r + zAnsChan p j - 4) (u2 := U p r + zAnsChan p j + 4)
    (v1 := trackOut p b 4 (U p r + zAnsChan p j) + 11) (v2 := zAnsDepth p j - 7) ?_
    (zone_unit ?_) ?_ ?_
  · intro cu cv r1 r2
    simp only [Ray, outD, behindIn] at r1 r2 ⊢
    omega
  · unfold modLeft at *; omega
  · intro r' s' _ hs'
    by_cases h : r' = r
    · subst h; exact right_module_own (by omega) s' hs'
    · exact zone_module_other (r := r) (by unfold modLeft modRight at *; omega) r' s' h hs'
  · refine hsplit _ hown fun c' _ hd hband n1 _ =>
      right_corner hr hj hown' (by omega) (by omega) hd hband (Or.inr ⟨hcd.1, hcd.2, n1⟩)

/-! ### Lines of the answers -/

/-- **The lines of the band part of an answer**: a glider flying `NW` on the channel `c` meets
every corner of `upCornersK 5` on its input line (hairpin and destination column of the parity of
`c`, destination corner on an odd `u + v`). -/
theorem upCornersK5_lines (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) {g : WL} (hdx : g.dx = -1)
    (hdy : g.dy = -1) (hl : g.lane = -c) (hH : (H - c) % 2 = 0) (hd : (destU p a t - c) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) : RouteLines g (upCornersK 5 p b s c H a t) := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  set vO := trackOut p b s c
  set vB := trackBack p b s c
  set cd := destU p a t
  set vD := destV p t
  simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, RouteLines]
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
  exact ⟨l1, l2, l3, l4, l5, trivial⟩

/-- **The lines of the NZ answer**: a glider flying `SW` on the port line of the NZ answer of
caller `j` of module `r` meets every corner of the NZ answer on its input line. -/
theorem nzAnsCorners_lines (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) {g : WL}
    (hdx : g.dx = -1) (hdy : g.dy = 1) (hl : g.lane = nzAnsPortV j)
    (hH : (H - (U p r + nzAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + nzAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) : RouteLines g (nzAnsCorners p b r j H a t) := by
  have hU := U_even p r
  have hc := nzAnsChan_parity p j
  have p0 : (U p r + nzAnsChan p j - rfCU 0 + nzAnsPortV j - rfCV 0) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  have l0 : OnLine g ⟨0, U p r + nzAnsChan p j, nzAnsPortV j, .left r (2 * D p + 2 + 2 * j)⟩ :=
    onLine_of_through (by simp [hdx, rfIn]) (by simp [hdy, rfIn]) p0
      (by simp only [WL.Through, hdx, hdy, hl]; ring)
  obtain ⟨t0, x0, y0⟩ := reflect_through g
    ⟨0, U p r + nzAnsChan p j, nzAnsPortV j, .left r (2 * D p + 2 + 2 * j)⟩ p0
  simp only [rfOut] at x0 y0
  refine ⟨l0, upCornersK5_lines p b 3 _ H a t x0 y0 ?_ hH hd hv⟩
  simp only [WL.Through, x0, y0] at t0
  linarith

/-- **The lines of the Z answer**: a glider flying `SE` on the Z answer station column of caller
`j` of module `r` meets every corner of the Z answer on its input line. -/
theorem zAnsCorners_lines (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) {g : WL}
    (hdx : g.dx = 1) (hdy : g.dy = 1) (hl : g.lane = U p r + zAnsStation j)
    (hH : (H - (U p r + zAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + zAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) : RouteLines g (zAnsCorners p b r j H a t) := by
  have hU := U_even p r
  have hc := zAnsChan_parity p j
  have p0 : (U p r + zAnsStation j - rfCU 4 + zAnsDepth p j - rfCV 4) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  have l0 : OnLine g ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩ :=
    onLine_of_through (by simp [hdx, rfIn]) (by simp [hdy, rfIn]) p0
      (by simp only [WL.Through, hdx, hdy, hl]; ring)
  obtain ⟨t0, x0, y0⟩ := reflect_through g ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩
    p0
  set g0 := (reflect g ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩).2
  simp only [rfOut] at x0 y0
  have p1 : (U p r + zAnsChan p j - rfCU 6 + zAnsDepth p j - rfCV 6) % 2 = 0 := by
    simp only [rfCU, rfCV]; omega
  have l1 : OnLine g0 ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩ :=
    onLine_of_through (by simp [x0, rfIn]) (by simp [y0, rfIn]) p1
      (by simp only [WL.Through, x0, y0] at t0 ⊢; linarith)
  obtain ⟨t1, x1, y1⟩ := reflect_through g0 ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩
    p1
  simp only [rfOut] at x1 y1
  refine ⟨l0, l1, upCornersK5_lines p b 4 _ H a t x1 y1 ?_ hH hd hv⟩
  simp only [WL.Through, x1, y1] at t1
  linarith

/-! ### Links of the `decJz` instructions -/

/-- **Every corner of the machine is described.** -/
theorem allCorners_desc {p : Program} (hp : p.WellFormed) : ∀ c ∈ allCorners p, Desc p c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨i, hi, hc⟩ := List.mem_flatMap.1 hc
    exact instrCorners_desc hp (List.mem_range.1 hi) c hc
  · obtain ⟨r, hr, hc⟩ := List.mem_flatMap.1 hc
    exact mergeCorners_desc (List.mem_range.1 (List.mem_filter.1 hr).1) c hc

/-- The first corner of a chain is a corner of a route of the machine. -/
theorem ChainOK.head {p : Program} {c : Corner} {cs : List Corner} (h : ChainOK p (c :: cs)) :
    CornerOK p c := by
  cases cs with
  | nil => exact h
  | cons _ _ => exact h.1

/-- **A link from a source column of unit `a` with a separated chain** (first corner `SE → SW` on
its `OUT` track) is separated from every time `T` at which the glider is at `v ≥ vS + 2`, given
the checks of the corners of its owner and of the pieces of unit `a` against its source leg. -/
theorem unitLink_sep {p : Program} (hp : p.WellFormed) {a : ℕ} {b s w τ vS : ℤ}
    {rest : List Corner} {own : List Corner} (hsplit : OwnSplit p b own) (hb : b = 1 + (a : ℤ))
    (hbr : b ≤ N p + R p) (hs : 0 ≤ s ∧ s ≤ 4)
    (hlines : RouteLines (unitWL p a ⟨1, 1, w, τ⟩)
      (⟨3, A p a + w, trackOut p b s (A p a + w), .band b s false⟩ :: rest))
    (hchain : ChainOK p (⟨3, A p a + w, trackOut p b s (A p a + w), .band b s false⟩ :: rest))
    (hmem : ∀ x ∈ (route (unitWL p a ⟨1, 1, w, τ⟩)
      (⟨3, A p a + w, trackOut p b s (A p a + w), .band b s false⟩ :: rest)).1,
      x ∈ machSpecs p)
    (hw : unitC0 p a + 81 ≤ w ∧ w ≤ 188) (hnh : ∀ x : ℕ, p[x]? = some .halt → x ≠ a)
    (hown0 : ∀ c' ∈ own, c'.tag ≠ .band b s false →
      FarRect (cornerSpec c').bx (A p a + w - 4) (A p a + w + 4) vS
        (trackOut p b s (A p a + w) - 7))
    (hunit : ∀ s' ∈ unitSpecs p a, FarRect s'.bx (A p a + w - 4) (A p a + w + 4) vS
      (trackOut p b s (A p a + w) - 7))
    {d : ℤ} (hd30 : d % 30 = 0) {T : ℤ}
    (hT : ∀ t' : ℤ, T ≤ t' → vS + 2 ≤ ((unitWL p a ⟨1, 1, w, τ⟩).shift 0 0 d).cv t') :
    RouteSepX (machPieces p) (machRegion p) ((unitWL p a ⟨1, 1, w, τ⟩).shift 0 0 d)
      (⟨3, A p a + w, trackOut p b s (A p a + w), .band b s false⟩ :: rest) T := by
  have hf := layout_facts p
  have hR := slabR_ge p
  have hlines' := routeLines_delay d _ _ hlines
  refine routeSepX_of hp _ _ _ (List.cons_ne_nil _ _) hlines' ?_ hchain
    (route_mem_delay hmem hd30)
  intro c hc
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
  subst hc
  have hts := tracks_range p b s (A p a + w)
  have hc0 := unitC0_cases p a
  refine startOK_of hp hchain.head hlines'.1
    (u1 := A p a + w - 4) (u2 := A p a + w + 4) (v1 := vS)
    (v2 := trackOut p b s (A p a + w) - 7) ?_ ?_ (slab_module (a := a) (by omega)
      (by omega)) ?_
  · intro t' h1 _ hray
    simp only [Ray, behindIn] at hray ⊢
    have hc := (unitWL_center p a w τ d t').1
    have := hT t' h1
    omega
  · intro a' s' _ hs'
    by_cases h : a' = a
    · subst h; exact hunit s' hs'
    · exact slab_unit_other (a := a) (by omega) a' s' (by omega) h hs'
  · refine hsplit _ (fun c' hc' n1 => hown0 c' hc' n1) fun c' _ hd' hband _ => ?_
    exact src_corner hb (by omega) hw hnh (by omega) hd' hband

/-- **The NZ answer of caller `j` of module `r` (owned by instruction `i`) is separated** from
every time `T` at which the glider has passed its station (`u ≤ U_r - 553`), given the checks of
the corners of instruction `i` against its channel, hairpin and destination legs. -/
theorem nzAnsLink_sep {p : Program} (hp : p.WellFormed) {i : ℕ} (hi : i < p.length) {r : ℕ}
    {j H : ℤ} {a : ℕ} {t : ℤ} {g : WL}
    (hx : (g, nzAnsCorners p (instrBand i) r j H a t) ∈ instrSpecs p i)
    (hg : g.dx = -1 ∧ g.dy = 1 ∧ g.lane = nzAnsPortV j) (hr : (r : ℤ) < R p)
    (hj : 0 ≤ j ∧ j < D p) (hH : (H - (U p r + nzAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + nzAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) (ha : (a : ℤ) < N p + R p)
    (ht : 0 ≤ t ∧ t < 2 * P p) (hownS : Owns p (instrBand i) (.slab a t))
    (hownL : Owns p (instrBand i) (.left r (2 * D p + 2 + 2 * j)))
    (hownC : ∀ c' ∈ instrCorners p i, c'.tag ≠ .left r (2 * D p + 2 + 2 * j) →
      c'.tag ≠ .band (instrBand i) 3 false →
      FarRect (cornerSpec c').bx (U p r + nzAnsChan p j - 4) (U p r + nzAnsChan p j + 4)
        (trackOut p (instrBand i) 3 (U p r + nzAnsChan p j) + 11) (nzAnsPortV j - 7))
    (hown2 : ∀ c' ∈ instrCorners p i, c'.tag ≠ .band (instrBand i) 3 true →
      c'.tag ≠ .band (instrBand i) (9 - 3) true →
      FarRect (cornerSpec c').bx (H - 4) (H + 4)
        (trackOut p (instrBand i) 3 (U p r + nzAnsChan p j) + 11)
        (trackBack p (instrBand i) 3 (U p r + nzAnsChan p j) - 7))
    (hown4 : ∀ c' ∈ instrCorners p i, c'.tag ≠ .band (instrBand i) (9 - 3) false →
      c'.tag ≠ .slab a t →
      FarRect (cornerSpec c').bx (destU p a t - 4) (destU p a t + 4) (destV p t + 11)
        (trackBack p (instrBand i) 3 (U p r + nzAnsChan p j) - 7))
    {d : ℤ} (hd30 : d % 30 = 0) {T : ℤ}
    (hT : ∀ t' : ℤ, T ≤ t' → (g.shift 0 0 d).cu t' ≤ U p r - 553) :
    RouteSepX (machPieces p) (machRegion p) (g.shift 0 0 d) (nzAnsCorners p (instrBand i) r j H a t)
      T := by
  have hf := layout_facts p
  have hiN : (i : ℤ) < N p := by unfold N; exact_mod_cast hi
  have hb : 1 ≤ instrBand i ∧ instrBand i ≤ N p + R p := by unfold instrBand; omega
  have hcorner := instrRoute_corner hi hx
  have hU := U_even p r
  have hcp := nzAnsChan_parity p j
  have hl := fixp_bounds (uL - 62 * (2 * D p + 2 + 2 * j)) (1 - nzAnsPortV j % 2)
  have hcd : U p r - 794 - 62 * (2 * D p + 2 + 2 * j) ≤ U p r + nzAnsChan p j ∧
      U p r + nzAnsChan p j ≤ U p r - 793 - 62 * (2 * D p + 2 + 2 * j) := by
    unfold nzAnsChan leftChan uL at *; omega
  have hpar := upCornersK_par (p := p) (k0 := 5) (b := instrBand i) (s := 3) (Or.inr rfl) hH hd hv
  have hok : ∀ x ∈ nzAnsCorners p (instrBand i) r j H a t, CornerOK p x := by
    intro x hx'
    refine ⟨hcorner x hx', ?_, ?_⟩
    · rcases List.mem_cons.1 hx' with rfl | hx'
      · simp
      · exact upCornersK_k (by norm_num) x hx'
    · rcases List.mem_cons.1 hx' with rfl | hx'
      · simp only [CPar, rfCU, rfCV]; omega
      · exact hpar x hx'
  have hlines := nzAnsCorners_lines p (instrBand i) r j H a t hg.1 hg.2.1 hg.2.2 hH hd hv
  have hlines' := routeLines_delay d _ _ hlines
  have hsplit := ownSplit_instr hp hi
  have hchain : ChainOK p (nzAnsCorners p (instrBand i) r j H a t) := by
    have hup := upBand_chain hp (Or.inr rfl) hsplit hb (by norm_num) ha ht hownS
      (fun x hx' => hok x (List.mem_cons_of_mem _ hx')) hown2 hown4
    have h0 := hok _ List.mem_cons_self
    have h1 := hok ⟨5, U p r + nzAnsChan p j, trackOut p (instrBand i) 3 (U p r + nzAnsChan p j),
      .band (instrBand i) 3 false⟩ (by simp [nzAnsCorners, upCornersK, bandCorners])
    simp only [nzAnsCorners, upCornersK, bandCorners, List.cons_append, List.nil_append] at hup ⊢
    exact ⟨h0, legLeftUp hp hsplit hb hr ⟨by omega, by omega⟩ hcd hownL h0 h1 hownC, hup⟩
  refine routeSepX_of hp _ _ _ (List.cons_ne_nil _ _) hlines' ?_ hchain
    (route_mem_delay (instrRoute_mem hi hx) hd30)
  intro c hc
  simp only [nzAnsCorners, List.head?_cons, Option.mem_def, Option.some.injEq] at hc
  subst hc
  refine startOK_of hp (hok _ List.mem_cons_self) hlines'.1
    (u1 := U p r + nzAnsChan p j + 9) (u2 := U p r - 549) (v1 := nzAnsPortV j - 2)
    (v2 := nzAnsPortV j + 6) ?_ (zone_unit ?_) ?_ ?_
  · intro t' h1 _ hray
    simp only [Ray, behindIn] at hray ⊢
    have := hT t' h1
    omega
  · have := (U_ge p (r := r) (by omega)).1
    unfold modLeft at *; omega
  · intro r' s' _ hs'
    by_cases h : r' = r
    · subst h; exact nzport_module_own hj le_rfl s' hs'
    · exact zone_module_other (r := r) (by unfold modLeft modRight at *; omega) r' s' h hs'
  · intro c' hc' n1
    exact nzport_corner hr hj ⟨by unfold modLeft at *; omega, le_rfl⟩
      (allCorners_desc hp c' hc') n1

/-- **The Z answer of caller `j` of module `r` (owned by instruction `i`) is separated** from
every time `T` at which the glider has passed the Z stations (`v ≥ 710`), given the checks of the
corners of instruction `i` against its channel, hairpin and destination legs. -/
theorem zAnsLink_sep {p : Program} (hp : p.WellFormed) {i : ℕ} (hi : i < p.length) {r : ℕ}
    {j H : ℤ} {a : ℕ} {t : ℤ} {g : WL}
    (hx : (g, zAnsCorners p (instrBand i) r j H a t) ∈ instrSpecs p i)
    (hg : g.dx = 1 ∧ g.dy = 1 ∧ g.lane = U p r + zAnsStation j) (hr : (r : ℤ) < R p)
    (hj : 0 ≤ j ∧ j < D p) (hH : (H - (U p r + zAnsChan p j)) % 2 = 0)
    (hd : (destU p a t - (U p r + zAnsChan p j)) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) (ha : (a : ℤ) < N p + R p)
    (ht : 0 ≤ t ∧ t < 2 * P p) (hownS : Owns p (instrBand i) (.slab a t))
    (hownR : Owns p (instrBand i) (.right r j 0))
    (hownC : ∀ c' ∈ instrCorners p i, c'.tag ≠ .right r j 1 →
      c'.tag ≠ .band (instrBand i) 4 false →
      FarRect (cornerSpec c').bx (U p r + zAnsChan p j - 4) (U p r + zAnsChan p j + 4)
        (trackOut p (instrBand i) 4 (U p r + zAnsChan p j) + 11) (zAnsDepth p j - 7))
    (hown2 : ∀ c' ∈ instrCorners p i, c'.tag ≠ .band (instrBand i) 4 true →
      c'.tag ≠ .band (instrBand i) (9 - 4) true →
      FarRect (cornerSpec c').bx (H - 4) (H + 4)
        (trackOut p (instrBand i) 4 (U p r + zAnsChan p j) + 11)
        (trackBack p (instrBand i) 4 (U p r + zAnsChan p j) - 7))
    (hown4 : ∀ c' ∈ instrCorners p i, c'.tag ≠ .band (instrBand i) (9 - 4) false →
      c'.tag ≠ .slab a t →
      FarRect (cornerSpec c').bx (destU p a t - 4) (destU p a t + 4) (destV p t + 11)
        (trackBack p (instrBand i) 4 (U p r + zAnsChan p j) - 7))
    {d : ℤ} (hd30 : d % 30 = 0) {T : ℤ}
    (hT : ∀ t' : ℤ, T ≤ t' → 710 ≤ (g.shift 0 0 d).cv t') :
    RouteSepX (machPieces p) (machRegion p) (g.shift 0 0 d) (zAnsCorners p (instrBand i) r j H a t)
      T := by
  have hf := layout_facts p
  have hiN : (i : ℤ) < N p := by unfold N; exact_mod_cast hi
  have hb : 1 ≤ instrBand i ∧ instrBand i ≤ N p + R p := by unfold instrBand; omega
  have hcorner := instrRoute_corner hi hx
  have hU := U_even p r
  have hcp := zAnsChan_parity p j
  have hpar := upCornersK_par (p := p) (k0 := 5) (b := instrBand i) (s := 4) (Or.inr rfl) hH hd hv
  have hok : ∀ x ∈ zAnsCorners p (instrBand i) r j H a t, CornerOK p x := by
    intro x hx'
    refine ⟨hcorner x hx', ?_, ?_⟩
    · rcases List.mem_cons.1 hx' with rfl | hx'
      · simp
      rcases List.mem_cons.1 hx' with rfl | hx'
      · simp
      · exact upCornersK_k (by norm_num) x hx'
    · rcases List.mem_cons.1 hx' with rfl | hx'
      · simp only [CPar, rfCU, rfCV]; omega
      rcases List.mem_cons.1 hx' with rfl | hx'
      · simp only [CPar, rfCU, rfCV]; omega
      · exact hpar x hx'
  have hlines := zAnsCorners_lines p (instrBand i) r j H a t hg.1 hg.2.1 hg.2.2 hH hd hv
  have hlines' := routeLines_delay d _ _ hlines
  have hsplit := ownSplit_instr hp hi
  have hchain : ChainOK p (zAnsCorners p (instrBand i) r j H a t) := by
    have hup := upBand_chain hp (Or.inr rfl) hsplit hb (by norm_num) ha ht hownS
      (fun x hx' => hok x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx'))) hown2 hown4
    have h0 := hok _ List.mem_cons_self
    have h0' := hok _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have h1 := hok ⟨5, U p r + zAnsChan p j, trackOut p (instrBand i) 4 (U p r + zAnsChan p j),
      .band (instrBand i) 4 false⟩ (by simp [zAnsCorners, upCornersK, bandCorners])
    simp only [zAnsCorners, upCornersK, bandCorners, List.cons_append, List.nil_append] at hup ⊢
    exact ⟨h0, legRzoneVd hp hr hj h0 h0', h0', legRightUp hp hsplit hb hr hj hownR h0' h1 hownC,
      hup⟩
  refine routeSepX_of hp _ _ _ (List.cons_ne_nil _ _) hlines' ?_ hchain
    (route_mem_delay (instrRoute_mem hi hx) hd30)
  intro c hc
  simp only [zAnsCorners, List.head?_cons, Option.mem_def, Option.some.injEq] at hc
  subst hc
  have hdep := zAnsDepth_eq p j
  refine startOK_of hp (hok _ List.mem_cons_self) hlines'.1
    (u1 := U p r + zAnsStation j - 4) (u2 := U p r + zAnsStation j + 4) (v1 := 708)
    (v2 := zAnsDepth p j - 7) ?_ (zone_unit ?_) ?_ ?_
  · intro t' h1 _ hray
    simp only [Ray, behindIn] at hray ⊢
    have := hT t' h1
    omega
  · have := (U_ge p (r := r) (by omega)).1
    unfold modLeft zAnsStation at *; omega
  · intro r' s' _ hs'
    by_cases h : r' = r
    · subst h; exact rzone_module_own (by unfold zAnsStation; omega) (by norm_num) s' hs'
    · exact zone_module_other (r := r) (by unfold modLeft modRight zAnsStation at *; omega) r' s'
        h hs'
  · intro c' hc' n1
    have := zstation_corner (v1 := 708) (v2 := zAnsDepth p j - 7) hj (by norm_num)
      (allCorners_valid hp c' hc') n1
    rwa [show U p r + zAnsStation j - 4 = U p r + 1297 + 144 * j by unfold zAnsStation; ring,
      show U p r + zAnsStation j + 4 = U p r + 1305 + 144 * j by unfold zAnsStation; ring]

end LP

end LeanTheory.Life
