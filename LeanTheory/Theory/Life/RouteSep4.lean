/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RouteSep3

/-!
# Separation of the legs in the band, the halt line

* `OwnSplit`: the corners of the machine split into the corners of one owner (an instruction or a
  merge link) and the described corners of the other sub-bands (`allCorners_split`);
* the legs of the links in the band (`legOut`, `legHair`, `legBack`, `legDst`, `legLeftDown`)
  and their chains (`upBand_chain`, `downBand_chain`): `LegOK` from the leg-kind lemmas of
  `RouteSep3`, given the checks of the corners of the owner;
* the route of a `halt` instruction (`haltCorners`): from the output column `A_i + 14` of the unit
  down to the top track of the band, one reflector, then `SW` for ever. `haltLink_sep`: its
  corrected separation condition `RouteSepX` (`RouteSep`) for every well-formed program, from the
  time the glider is below the entry chain of the unit.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Owners -/

/-- The corners of the machine split into the corners `own` of sub-band `b` and the described
corners of the other sub-bands. -/
def OwnSplit (p : Program) (b : ℤ) (own : List Corner) : Prop :=
  ∀ Q : Corner → Prop, (∀ c ∈ own, Q c) →
    (∀ c ∈ allCorners p, Desc p c → (∀ b' k h, c.tag = .band b' k h → b' ≠ b) → Q c) →
    ∀ c ∈ allCorners p, Q c

/-- The corners of an instruction split the corners of the machine. -/
theorem ownSplit_instr {p : Program} (hp : p.WellFormed) {i : ℕ} (hi : i < p.length) :
    OwnSplit p (instrBand i) (instrCorners p i) :=
  fun _ hown hfor => allCorners_split hp hi hown fun c hc hd hb => hfor c hc hd hb

/-- The corners of a merge link split the corners of the machine. -/
theorem ownSplit_merge {p : Program} (hp : p.WellFormed) (r : ℕ) :
    OwnSplit p (mergeBand p r) (specCorners (mergeSpecs p r)) :=
  fun _ hown hfor => allCorners_split_merge hp hown hfor

/-! ### The legs in the band -/

/-- The tracks of a link lie in its sub-band. -/
theorem tracks_range (p : Program) (b s c : ℤ) :
    VT p + 660 * b + 62 * s ≤ trackOut p b s c ∧ trackOut p b s c ≤ VT p + 660 * b + 62 * s + 1 ∧
      VT p + 660 * b + 62 * (9 - s) ≤ trackBack p b s c ∧
      trackBack p b s c ≤ VT p + 660 * b + 62 * (9 - s) + 1 := by
  unfold trackOut trackBack track; omega

/-- **The `OUT` leg** of a link (from its source column to its hairpin, `SW`). -/
theorem legOut {p : Program} (hp : p.WellFormed) {k0 : ℕ} (hk0 : k0 = 3 ∨ k0 = 5)
    {b s c H : ℤ} (hb : 1 ≤ b ∧ b ≤ N p + R p) (hs : 0 ≤ s ∧ s ≤ 4)
    (h1 : CornerOK p ⟨k0, c, trackOut p b s c, .band b s false⟩)
    (h2 : CornerOK p ⟨7, H, trackOut p b s c, .band b s true⟩) :
    LegOK p ⟨k0, c, trackOut p b s c, .band b s false⟩
      ⟨7, H, trackOut p b s c, .band b s true⟩ := by
  have ht := tracks_range p b s c
  have hf := layout_facts p
  refine legOK_of hp h1 h2 (u1 := H + 9) (u2 := c - 9) (v1 := trackOut p b s c - 2)
    (v2 := trackOut p b s c + 6) ?_ (band_unit (by omega)) (band_module (by omega)) ?_
  · intro cu cv r1 r2
    rcases hk0 with rfl | rfl <;> simp only [Ray, outD, behindIn] at r1 r2 ⊢ <;> omega
  · intro c' hc' n1 n2
    exact track_corner hb (by omega) ⟨ht.1, ht.2.1⟩ (allCorners_valid hp c' hc') n2 n1

/-- **The `BACK` leg** of a link (from its hairpin to its destination column, `NE`). -/
theorem legBack {p : Program} (hp : p.WellFormed) {k4 : ℕ} (hk4 : k4 = 6 ∨ k4 = 2)
    {b s c H cd : ℤ} (hb : 1 ≤ b ∧ b ≤ N p + R p) (hs : 0 ≤ s ∧ s ≤ 4)
    (h1 : CornerOK p ⟨4, H, trackBack p b s c, .band b (9 - s) true⟩)
    (h2 : CornerOK p ⟨k4, cd, trackBack p b s c, .band b (9 - s) false⟩) :
    LegOK p ⟨4, H, trackBack p b s c, .band b (9 - s) true⟩
      ⟨k4, cd, trackBack p b s c, .band b (9 - s) false⟩ := by
  have ht := tracks_range p b s c
  have hf := layout_facts p
  refine legOK_of hp h1 h2 (u1 := H + 9) (u2 := cd - 9) (v1 := trackBack p b s c - 2)
    (v2 := trackBack p b s c + 6) ?_ (band_unit (by omega)) (band_module (by omega)) ?_
  · intro cu cv r1 r2
    rcases hk4 with rfl | rfl <;> simp only [Ray, outD, behindIn] at r1 r2 ⊢ <;> omega
  · intro c' hc' n1 n2
    exact track_corner hb (by omega) ⟨ht.2.2.1, ht.2.2.2⟩ (allCorners_valid hp c' hc') n1 n2

/-- **The hairpin leg** of a link (`SE`, from `OUT` to `BACK`), given the check of the corners
of its owner. -/
theorem legHair {p : Program} (hp : p.WellFormed) {b s c H : ℤ} {own : List Corner}
    (hsplit : OwnSplit p b own) (hb : 1 ≤ b ∧ b ≤ N p + R p) (hs : 0 ≤ s ∧ s ≤ 4)
    (h1 : CornerOK p ⟨7, H, trackOut p b s c, .band b s true⟩)
    (h2 : CornerOK p ⟨4, H, trackBack p b s c, .band b (9 - s) true⟩)
    (hown : ∀ c' ∈ own, c'.tag ≠ .band b s true → c'.tag ≠ .band b (9 - s) true →
      FarRect (cornerSpec c').bx (H - 4) (H + 4) (trackOut p b s c + 11)
        (trackBack p b s c - 7)) :
    LegOK p ⟨7, H, trackOut p b s c, .band b s true⟩
      ⟨4, H, trackBack p b s c, .band b (9 - s) true⟩ := by
  have ht := tracks_range p b s c
  have hf := layout_facts p
  refine legOK_of hp h1 h2 (u1 := H - 4) (u2 := H + 4) (v1 := trackOut p b s c + 11)
    (v2 := trackBack p b s c - 7) ?_ (band_unit (by omega)) (band_module (by omega)) ?_
  · intro cu cv r1 r2
    simp only [Ray, outD, behindIn] at r1 r2 ⊢
    omega
  · refine hsplit _ hown fun c' _ hd hband _ _ => hair_corner hb ⟨by omega, by omega⟩ hd hband

/-- **The destination leg of an up-going link** (`NW`, up the input column of entry copy `t` of
unit `a`, from `BACK` to the input corner), given the check of the corners of its owner. -/
theorem legDst {p : Program} (hp : p.WellFormed) {b s c : ℤ} {a : ℕ} {t : ℤ} {own : List Corner}
    (hsplit : OwnSplit p b own) (hs : 0 ≤ s ∧ s ≤ 4)
    (ha : (a : ℤ) < N p + R p) (ht : 0 ≤ t ∧ t < 2 * P p) (hown' : Owns p b (.slab a t))
    (h1 : CornerOK p ⟨6, destU p a t, trackBack p b s c, .band b (9 - s) false⟩)
    (h2 : CornerOK p ⟨1, destU p a t, destV p t, .slab a t⟩)
    (hown : ∀ c' ∈ own, c'.tag ≠ .band b (9 - s) false → c'.tag ≠ .slab a t →
      FarRect (cornerSpec c').bx (destU p a t - 4) (destU p a t + 4) (destV p t + 11)
        (trackBack p b s c - 7)) :
    LegOK p ⟨6, destU p a t, trackBack p b s c, .band b (9 - s) false⟩
      ⟨1, destU p a t, destV p t, .slab a t⟩ := by
  have hts := tracks_range p b s c
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have hc0 := unitC0_cases p a
  refine legOK_of hp h1 h2 (u1 := destU p a t - 4) (u2 := destU p a t + 4)
    (v1 := destV p t + 11) (v2 := trackBack p b s c - 7) ?_ ?_
    (slab_module ha (by unfold destU inCol slabR at *; omega)) ?_
  · intro cu cv r1 r2
    simp only [Ray, outD, behindIn] at r1 r2 ⊢
    omega
  · intro a' s' _ hs'
    by_cases h : a' = a
    · subst h; exact dst_unit_own ht.1 s' hs'
    · exact slab_unit_other (a := a) (by unfold destU inCol slabR at *; omega) a' s'
        (by omega) h hs'
  · refine hsplit _ hown fun c' _ hd hband n1 n2 =>
      dst_corner ha ht hown' (by omega) hd hband n2

/-- **The destination leg of a down-going link** (`SE`, down the channel `idx` of the left zone
of module `r`, from `BACK` to the port corner), given the check of the corners of its owner. -/
theorem legLeftDown {p : Program} (hp : p.WellFormed) {b s c cd vp : ℤ} {r : ℕ} {idx : ℤ}
    {own : List Corner} (hsplit : OwnSplit p b own) (hb : 1 ≤ b ∧ b ≤ N p + R p)
    (hs : 0 ≤ s ∧ s ≤ 4) (hr : (r : ℤ) < R p) (hidx : 0 ≤ idx ∧ idx ≤ 4 * D p)
    (hcd : U p r - 794 - 62 * idx ≤ cd ∧ cd ≤ U p r - 793 - 62 * idx)
    (hown' : Owns p b (.left r idx))
    (h1 : CornerOK p ⟨2, cd, trackBack p b s c, .band b (9 - s) false⟩)
    (h2 : CornerOK p ⟨4, cd, vp, .left r idx⟩)
    (hown : ∀ c' ∈ own, c'.tag ≠ .band b (9 - s) false → c'.tag ≠ .left r idx →
      FarRect (cornerSpec c').bx (cd - 4) (cd + 4) (trackBack p b s c + 11) (vp - 7)) :
    LegOK p ⟨2, cd, trackBack p b s c, .band b (9 - s) false⟩ ⟨4, cd, vp, .left r idx⟩ := by
  have hts := tracks_range p b s c
  have hf := layout_facts p
  have hl := left_range p hidx hcd
  refine legOK_of hp h1 h2 (u1 := cd - 4) (u2 := cd + 4) (v1 := trackBack p b s c + 11)
    (v2 := vp - 7) ?_ (zone_unit ?_) ?_ ?_
  · intro cu cv r1 r2
    simp only [Ray, outD, behindIn] at r1 r2 ⊢
    omega
  · have := (U_ge p (r := r) (by omega)).1
    omega
  · intro r' s' _ hs'
    by_cases h : r' = r
    · subst h; exact left_module_own hl.2 s' hs'
    · exact zone_module_other (r := r) (by unfold modRight at *; omega) r' s' h hs'
  · refine hsplit _ hown fun c' _ hd hband n1 n2 =>
      left_corner hr hidx hcd hown' (by omega) (by omega) hd hband n2

/-! ### Chains of the links in the band -/

/-- The parities of the corners of a link up to an entry copy (first image `3` or `5`). -/
theorem upCornersK_par {p : Program} {k0 : ℕ} (hk0 : k0 = 3 ∨ k0 = 5) {b s c H : ℤ} {a : ℕ}
    {t : ℤ} (hH : (H - c) % 2 = 0) (hd : (destU p a t - c) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) : ∀ x ∈ upCornersK k0 p b s c H a t, CPar x := by
  have ho := trackOut_par p b s c
  have hk := trackBack_par p b s c
  intro x hx
  simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hk0 with rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [CPar, rfCU, rfCV] <;> omega

/-- The parities of the corners of a link down to a left-zone port. -/
theorem downCorners_par {p : Program} {b s c H cd vp : ℤ} {r : ℕ} {idx : ℤ}
    (hH : (H - c) % 2 = 0) (hd : (cd - c) % 2 = 0) (hv : (cd + vp) % 2 = 1) :
    ∀ x ∈ downCorners p b s c H cd vp r idx, CPar x := by
  have ho := trackOut_par p b s c
  have hk := trackBack_par p b s c
  intro x hx
  rcases mem_downCorners.1 hx with rfl | rfl | rfl | rfl | rfl <;> simp only [CPar, rfCU, rfCV] <;>
    omega

/-- **The chain of a link up to an entry copy** (from its first band corner): its legs in the
band and up the input column, given the checks of the corners of its owner. -/
theorem upBand_chain {p : Program} (hp : p.WellFormed) {k0 : ℕ} (hk0 : k0 = 3 ∨ k0 = 5)
    {b s c H : ℤ} {a : ℕ} {t : ℤ} {own : List Corner} (hsplit : OwnSplit p b own)
    (hb : 1 ≤ b ∧ b ≤ N p + R p) (hs : 0 ≤ s ∧ s ≤ 4) (ha : (a : ℤ) < N p + R p)
    (ht : 0 ≤ t ∧ t < 2 * P p) (hown' : Owns p b (.slab a t))
    (hok : ∀ x ∈ upCornersK k0 p b s c H a t, CornerOK p x)
    (hown2 : ∀ c' ∈ own, c'.tag ≠ .band b s true → c'.tag ≠ .band b (9 - s) true →
      FarRect (cornerSpec c').bx (H - 4) (H + 4) (trackOut p b s c + 11)
        (trackBack p b s c - 7))
    (hown4 : ∀ c' ∈ own, c'.tag ≠ .band b (9 - s) false → c'.tag ≠ .slab a t →
      FarRect (cornerSpec c').bx (destU p a t - 4) (destU p a t + 4) (destV p t + 11)
        (trackBack p b s c - 7)) :
    ChainOK p (upCornersK k0 p b s c H a t) := by
  have h := fun x hx => hok x hx
  simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, ChainOK]
  exact ⟨h1, legOut hp hk0 hb hs h1 h2, h2, legHair hp hsplit hb hs h2 h3 hown2, h3,
    legBack hp (Or.inl rfl) hb hs h3 h4, h4, legDst hp hsplit hs ha ht hown' h4 h5 hown4, h5⟩

/-- **The chain of a link down to a left-zone port**: its legs in the band and down the channel,
given the checks of the corners of its owner. -/
theorem downBand_chain {p : Program} (hp : p.WellFormed) {b s c H cd vp : ℤ} {r : ℕ} {idx : ℤ}
    {own : List Corner} (hsplit : OwnSplit p b own) (hb : 1 ≤ b ∧ b ≤ N p + R p)
    (hs : 0 ≤ s ∧ s ≤ 4) (hr : (r : ℤ) < R p) (hidx : 0 ≤ idx ∧ idx ≤ 4 * D p)
    (hcd : U p r - 794 - 62 * idx ≤ cd ∧ cd ≤ U p r - 793 - 62 * idx)
    (hown' : Owns p b (.left r idx))
    (hok : ∀ x ∈ downCorners p b s c H cd vp r idx, CornerOK p x)
    (hown2 : ∀ c' ∈ own, c'.tag ≠ .band b s true → c'.tag ≠ .band b (9 - s) true →
      FarRect (cornerSpec c').bx (H - 4) (H + 4) (trackOut p b s c + 11)
        (trackBack p b s c - 7))
    (hown4 : ∀ c' ∈ own, c'.tag ≠ .band b (9 - s) false → c'.tag ≠ .left r idx →
      FarRect (cornerSpec c').bx (cd - 4) (cd + 4) (trackBack p b s c + 11) (vp - 7)) :
    ChainOK p (downCorners p b s c H cd vp r idx) := by
  have h1 := hok _ (mem_downCorners.2 (Or.inl rfl))
  have h2 := hok _ (mem_downCorners.2 (Or.inr (Or.inl rfl)))
  have h3 := hok _ (mem_downCorners.2 (Or.inr (Or.inr (Or.inl rfl))))
  have h4 := hok _ (mem_downCorners.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 := hok _ (mem_downCorners.2 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  simp only [downCorners, bandCorners, List.cons_append, List.nil_append, ChainOK]
  exact ⟨h1, legOut hp (Or.inl rfl) hb hs h1 h2, h2, legHair hp hsplit hb hs h2 h3 hown2, h3,
    legBack hp (Or.inr rfl) hb hs h3 h4, h4,
    legLeftDown hp hsplit hb hs hr hidx hcd hown' h4 h5 hown4, h5⟩

/-- The centre of a glider flying `SE` on a unit world line, delayed by `d`. -/
theorem unitWL_center (p : Program) (a : ℕ) (lane tau d t : ℤ) :
    (((unitWL p a ⟨1, 1, lane, tau⟩).shift 0 0 d).cu t = A p a + lane) ∧
      ((unitWL p a ⟨1, 1, lane, tau⟩).shift 0 0 d).cv t =
        2 * ((t - tau - d) / 4) + VU p - lane := by
  have hu := unitD_uv p a
  simp only [WL.cu, WL.cv, WL.px, WL.py, WL.qt, unitWL, WL.shift]
  constructor <;> omega

/-- The images of the corners of a link up to an entry copy are below `8`. -/
theorem upCornersK_k {p : Program} {k0 : ℕ} (hk0 : k0 < 8) {b s c H : ℤ} {a : ℕ} {t : ℤ} :
    ∀ x ∈ upCornersK k0 p b s c H a t, x.k < 8 := by
  intro x hx
  simp only [upCornersK, bandCorners, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- The images of the corners of a link down to a left-zone port are below `8`. -/
theorem downCorners_k {p : Program} {b s c H cd vp : ℤ} {r : ℕ} {idx : ℤ} :
    ∀ x ∈ downCorners p b s c H cd vp r idx, x.k < 8 := by
  intro x hx
  rcases mem_downCorners.1 hx with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega

/-- **A link from a source column of unit `i` up to an entry copy is separated** (`RouteSepX` in
the region of the machine, for every delay `d ≡ 0 (mod 30)`), from every time `T` at which the
glider is at `v ≥ vS + 2`, given the checks of the corners of instruction `i` against its source,
hairpin and destination legs, and of the pieces of unit `i` against its source leg. -/
theorem unitUpLink_sep {p : Program} (hp : p.WellFormed) {i : ℕ} (hi : i < p.length)
    {s H w τ vS : ℤ} {a : ℕ} {t : ℤ}
    (hx : (unitWL p i ⟨1, 1, w, τ⟩, upCorners p (instrBand i) s (A p i + w) H a t) ∈
      instrSpecs p i)
    (hs : 0 ≤ s ∧ s ≤ 4) (hw : unitC0 p i + 81 ≤ w ∧ w ≤ 188)
    (hnh : ∀ x : ℕ, p[x]? = some .halt → x ≠ i) (hH : (H - (A p i + w)) % 2 = 0)
    (hd : (destU p a t - (A p i + w)) % 2 = 0) (hv : (destU p a t + destV p t) % 2 = 1)
    (ha : (a : ℤ) < N p + R p) (ht : 0 ≤ t ∧ t < 2 * P p)
    (hown' : Owns p (instrBand i) (.slab a t))
    (hown0 : ∀ c' ∈ instrCorners p i, c'.tag ≠ .band (instrBand i) s false →
      FarRect (cornerSpec c').bx (A p i + w - 4) (A p i + w + 4) vS
        (trackOut p (instrBand i) s (A p i + w) - 7))
    (hown2 : ∀ c' ∈ instrCorners p i, c'.tag ≠ .band (instrBand i) s true →
      c'.tag ≠ .band (instrBand i) (9 - s) true →
      FarRect (cornerSpec c').bx (H - 4) (H + 4) (trackOut p (instrBand i) s (A p i + w) + 11)
        (trackBack p (instrBand i) s (A p i + w) - 7))
    (hown4 : ∀ c' ∈ instrCorners p i, c'.tag ≠ .band (instrBand i) (9 - s) false →
      c'.tag ≠ .slab a t →
      FarRect (cornerSpec c').bx (destU p a t - 4) (destU p a t + 4) (destV p t + 11)
        (trackBack p (instrBand i) s (A p i + w) - 7))
    (hunit : ∀ s' ∈ unitSpecs p i, FarRect s'.bx (A p i + w - 4) (A p i + w + 4) vS
      (trackOut p (instrBand i) s (A p i + w) - 7))
    {d : ℤ} (hd30 : d % 30 = 0) {T : ℤ}
    (hT : ∀ t' : ℤ, T ≤ t' → vS + 2 ≤ ((unitWL p i ⟨1, 1, w, τ⟩).shift 0 0 d).cv t') :
    RouteSepX (machPieces p) (machRegion p) ((unitWL p i ⟨1, 1, w, τ⟩).shift 0 0 d)
      (upCorners p (instrBand i) s (A p i + w) H a t) T := by
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have hiN : (i : ℤ) < N p := by unfold N; exact_mod_cast hi
  have hb : 1 ≤ instrBand i ∧ instrBand i ≤ N p + R p := by unfold instrBand; omega
  have hcorner := instrRoute_corner hi hx
  have hpar := upCornersK_par (k0 := 3) (b := instrBand i) (s := s) (Or.inl rfl) hH hd hv
  have hok : ∀ x ∈ upCorners p (instrBand i) s (A p i + w) H a t, CornerOK p x :=
    fun x hx' => ⟨hcorner x hx', upCornersK_k (by norm_num) x hx', hpar x hx'⟩
  have hu := unitD_uv p i
  have hlines := (upCorners_lines p (instrBand i) s (A p i + w) H a t
    (g := unitWL p i ⟨1, 1, w, τ⟩) rfl rfl (by simp only [unitWL, WL.shift]; omega) hH hd hv).1
  have hlines' := routeLines_delay d _ _ hlines
  refine routeSepX_of hp _ _ _ (by simp [upCorners, upCornersK, bandCorners]) hlines' ?_
    (upBand_chain hp (Or.inl rfl) (ownSplit_instr hp hi) hb hs ha ht hown' hok hown2 hown4)
    (route_mem_delay (instrRoute_mem hi hx) hd30)
  intro c hc
  simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append,
    List.head?_cons, Option.mem_def, Option.some.injEq] at hc
  subst hc
  have hts := tracks_range p (instrBand i) s (A p i + w)
  refine startOK_of hp (hok _ (by simp [upCorners, upCornersK, bandCorners])) hlines'.1
    (u1 := A p i + w - 4) (u2 := A p i + w + 4) (v1 := vS)
    (v2 := trackOut p (instrBand i) s (A p i + w) - 7) ?_ ?_ (slab_module (a := i) (by omega)
      (by omega)) ?_
  · intro t' h1 _ hray
    simp only [Ray, behindIn] at hray ⊢
    have hc := (unitWL_center p i w τ d t').1
    have := hT t' h1
    omega
  · intro a' s' _ hs'
    have hc0 := unitC0_cases p i
    by_cases h : a' = i
    · subst h; exact hunit s' hs'
    · exact slab_unit_other (a := i) (by omega) a' s' (by omega) h hs'
  · refine ownSplit_instr hp hi _ (fun c' hc' n1 => hown0 c' hc' n1) fun c' _ hd' hband _ => ?_
    exact src_corner (b := instrBand i) rfl (by omega) hw hnh (by omega) hd' hband

/-- **A link from a source column of unit `a` down to a left-zone port is separated**
(`RouteSepX` in the region of the machine, for every delay `d ≡ 0 (mod 30)`), from every time `T`
at which the glider is at `v ≥ vS + 2`, given the checks of the corners of its owner against its
source, hairpin and channel legs, and of the pieces of unit `a` against its source leg. -/
theorem unitDownLink_sep {p : Program} (hp : p.WellFormed) {a : ℕ} {b s w τ H cd vp vS : ℤ}
    {r : ℕ} {idx : ℤ} {own : List Corner} (hsplit : OwnSplit p b own) (hb : b = 1 + (a : ℤ))
    (hbr : b ≤ N p + R p)
    (hcorner : ∀ x ∈ downCorners p b s (A p a + w) H cd vp r idx, x ∈ allCorners p)
    (hmem : ∀ x ∈ (route (unitWL p a ⟨1, 1, w, τ⟩)
      (downCorners p b s (A p a + w) H cd vp r idx)).1, x ∈ machSpecs p)
    (hs : 0 ≤ s ∧ s ≤ 4) (hw : unitC0 p a + 81 ≤ w ∧ w ≤ 188)
    (hnh : ∀ x : ℕ, p[x]? = some .halt → x ≠ a) (hH : (H - (A p a + w)) % 2 = 0)
    (hd : (cd - (A p a + w)) % 2 = 0) (hv : (cd + vp) % 2 = 1)
    (hr : (r : ℤ) < R p) (hidx : 0 ≤ idx ∧ idx ≤ 4 * D p)
    (hcd : U p r - 794 - 62 * idx ≤ cd ∧ cd ≤ U p r - 793 - 62 * idx)
    (hown' : Owns p b (.left r idx))
    (hown0 : ∀ c' ∈ own, c'.tag ≠ .band b s false →
      FarRect (cornerSpec c').bx (A p a + w - 4) (A p a + w + 4) vS
        (trackOut p b s (A p a + w) - 7))
    (hown2 : ∀ c' ∈ own, c'.tag ≠ .band b s true → c'.tag ≠ .band b (9 - s) true →
      FarRect (cornerSpec c').bx (H - 4) (H + 4) (trackOut p b s (A p a + w) + 11)
        (trackBack p b s (A p a + w) - 7))
    (hown4 : ∀ c' ∈ own, c'.tag ≠ .band b (9 - s) false → c'.tag ≠ .left r idx →
      FarRect (cornerSpec c').bx (cd - 4) (cd + 4) (trackBack p b s (A p a + w) + 11) (vp - 7))
    (hunit : ∀ s' ∈ unitSpecs p a, FarRect s'.bx (A p a + w - 4) (A p a + w + 4) vS
      (trackOut p b s (A p a + w) - 7))
    {d : ℤ} (hd30 : d % 30 = 0) {T : ℤ}
    (hT : ∀ t' : ℤ, T ≤ t' → vS + 2 ≤ ((unitWL p a ⟨1, 1, w, τ⟩).shift 0 0 d).cv t') :
    RouteSepX (machPieces p) (machRegion p) ((unitWL p a ⟨1, 1, w, τ⟩).shift 0 0 d)
      (downCorners p b s (A p a + w) H cd vp r idx) T := by
  have hf := layout_facts p
  have hR := slabR_ge_rs p
  have hbr' : 1 ≤ b ∧ b ≤ N p + R p := ⟨by omega, hbr⟩
  have hpar := downCorners_par (p := p) (b := b) (s := s) (r := r) (idx := idx) hH hd hv
  have hok : ∀ x ∈ downCorners p b s (A p a + w) H cd vp r idx, CornerOK p x :=
    fun x hx' => ⟨hcorner x hx', downCorners_k x hx', hpar x hx'⟩
  have hu := unitD_uv p a
  have hlines := (downCorners_lines p b s (A p a + w) H cd vp r idx
    (g := unitWL p a ⟨1, 1, w, τ⟩) rfl rfl (by simp only [unitWL, WL.shift]; omega) hH hd hv).1
  have hlines' := routeLines_delay d _ _ hlines
  refine routeSepX_of hp _ _ _ (by simp [downCorners, bandCorners]) hlines' ?_
    (downBand_chain hp hsplit hbr' hs hr hidx hcd hown' hok hown2 hown4)
    (route_mem_delay hmem hd30)
  intro c hc
  simp only [downCorners, bandCorners, List.cons_append, List.nil_append,
    List.head?_cons, Option.mem_def, Option.some.injEq] at hc
  subst hc
  have hts := tracks_range p b s (A p a + w)
  have hc0 := unitC0_cases p a
  refine startOK_of hp (hok _ (by simp [downCorners, bandCorners])) hlines'.1
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

/-- The halt corner of unit `i` is met on its input line by the halt output. -/
theorem haltCorners_lines (p : Program) (i : ℕ) (d : ℤ) :
    RouteLines ((unitWL p i haltDWL).shift 0 0 d) (haltCorners p i) := by
  have hu := unitD_uv p i
  have ha := A_even p i
  have ho := trackOut_par p 0 0 (A p i + haltD)
  refine routeLines_delay d _ _ ⟨onLine_of_through (by rfl) (by rfl) ?_ ?_, trivial⟩
  · simp only [rfCU, rfCV, haltD] at ho ⊢; omega
  · simp only [WL.Through, unitWL, haltDWL, WL.shift, haltD]; omega

/-- The pieces of a unit without body (`halt`, merge): the copies of the entry chain, at `v ≤ V_U +
122`. -/
theorem unitSpecs_nobody_uv (p : Program) (a : ℕ)
    (hk : unitKind p a = .halt ∨ unitKind p a = .merge) {s : PSpec} (hs : s ∈ unitSpecs p a) :
    s.bx.InUV (A p a - 32) (A p a + 58 * P p + 212) (VU p - 198 * P p) (VU p + 122) := by
  have hd := unitD_uv p a
  have hP := one_le_P p
  unfold unitSpecs at hs
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨t, ht, rfl⟩ := mem_chainSpecs hs
    rw [chain_bx]
    have ht' : (t : ℤ) < 2 * P p := by unfold P; omega
    unfold BoxT.InUV; simp only; omega
  · rcases hk with hk | hk <;> rw [hk] at hs <;> simp at hs

/-- The kind of the unit of a `halt` instruction. -/
theorem unitKind_halt {p : Program} {i : ℕ} (hi : p[i]? = some .halt) : unitKind p i = .halt := by
  simp [unitKind, hi]

/-- **The halt line is separated** (`R-31` §6, the part up to the reflector of the top track):
for every well-formed program, every `halt` instruction `i` and every delay `d ≡ 0 (mod 30)`, the
halt glider satisfies `RouteSepX` from template time `917` on (when it is below the entry chain
of its unit). -/
theorem haltLink_sep {p : Program} (hp : p.WellFormed) {i : ℕ} (hi : p[i]? = some .halt) {d : ℤ}
    (hd : d % 30 = 0) {T : ℤ} (hT : 917 + d ≤ T) :
    RouteSepX (machPieces p) (machRegion p) ((unitWL p i haltDWL).shift 0 0 d)
      (haltCorners p i) T := by
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have hx : (unitWL p i haltDWL, haltCorners p i) ∈ instrSpecs p i := by simp [instrSpecs, hi]
  have hc : (⟨3, A p i + haltD, trackOut p 0 0 (A p i + haltD), .halt i⟩ : Corner) ∈
      allCorners p := instrRoute_corner hlt hx _ (by simp [haltCorners])
  have hf := layout_facts p
  have hu := unitD_uv p i
  have ha := A_even p i
  have hA0 := A_nonneg p (a := i) (by omega)
  have hiN : (i : ℤ) < N p := by unfold N; exact_mod_cast hlt
  have hpar : CPar ⟨3, A p i + haltD, trackOut p 0 0 (A p i + haltD), .halt i⟩ := by
    have := trackOut_par p 0 0 (A p i + haltD)
    simp only [CPar, rfCU, rfCV, haltD] at this ⊢; omega
  refine routeSepX_of hp _ _ _ (by simp [haltCorners]) (haltCorners_lines p i d) ?_
    ⟨hc, by norm_num, hpar⟩ (route_mem_delay (instrRoute_mem hlt hx) hd)
  intro c hc'
  simp only [haltCorners, List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
  subst hc'
  refine startOK_of hp ⟨hc, by norm_num, hpar⟩ (haltCorners_lines p i d).1
    (u1 := A p i + 10) (u2 := A p i + 18) (v1 := VU p + 128)
    (v2 := trackOut p 0 0 (A p i + haltD) - 7) ?_ ?_ ?_ ?_
  · intro t h1 h2 hray
    simp only [Ray, behindIn] at hray
    obtain ⟨e1, e2⟩ := unitWL_center p i 14 629 d t
    simp only [haltDWL, haltD] at hray e1 e2 ⊢
    omega
  · intro a s ha hs
    rcases lt_trichotomy a i with h | rfl | h
    · have hs' := unitSpecs_uv p a hs
      have := A_add_le p (a := a) (a' := i) (by exact_mod_cast h)
      refine farRect_of_uv hs' (Or.inl ?_)
      unfold PU at *; omega
    · have := unitSpecs_nobody_uv p a (Or.inl (unitKind_halt hi)) hs
      refine farRect_of_uv this (Or.inr (Or.inr (Or.inl ?_)))
      omega
    · have hs' := unitSpecs_uv p a hs
      have := A_add_le p (a := i) (a' := a) (by exact_mod_cast h)
      have hk : -180 ≤ (unitKind p a).uLo := by cases unitKind p a <;> simp [UKind.uLo]
      refine farRect_of_uv hs' (Or.inr (Or.inl ?_))
      unfold PU at *; omega
  · intro r s hr hs
    have h2 := (moduleSpecs_uv p r hs).1
    have h6 := (sep06_units_module0 p (a := i) (by have := one_le_R p; omega)).1
    have hU := (U_ge p (r := r) (by omega)).1
    refine farRect_of_uv h2 (Or.inr (Or.inl ?_))
    unfold slabR modLeft at *; omega
  · intro c' hc' hne
    have hv := allCorners_valid hp c' hc'
    refine corner_farRect ?_
    obtain ⟨k', u', v', tag'⟩ := c'
    simp only at hne ⊢
    have hO : trackOut p 0 0 (A p i + haltD) ≤ VT p + 1 := by
      unfold trackOut track; omega
    have hO' : VT p ≤ trackOut p 0 0 (A p i + haltD) := by
      unfold trackOut track; omega
    cases tag' with
    | band b n h => simp only [Valid] at hv; omega
    | halt a' =>
      simp only [Valid] at hv
      have hne' : a' ≠ i := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hne' with h | h
      · have := A_add_le p h; unfold PU at *; simp only [haltD] at *; omega
      · have := A_add_le p h; unfold PU at *; simp only [haltD] at *; omega
    | slab a' t' =>
      simp only [Valid] at hv
      have hc0 := unitC0_cases p a'.toNat
      rcases lt_trichotomy a' i with h | h | h
      · have := A_add_le p h; unfold PU at *; simp only [haltD] at *; omega
      · subst h; simp only [haltD] at *; omega
      · have := A_add_le p h; unfold PU at *; simp only [haltD] at *; omega
    | left r idx => simp only [Valid] at hv; omega
    | right r j w => simp only [Valid] at hv; omega

end LP

end LeanTheory.Life
