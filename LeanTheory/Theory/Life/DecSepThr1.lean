/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepMov4
public import LeanTheory.Theory.Life.ActivationIncSepMain

/-!
# Tools for the thread fields of `DecSep`: far from every piece but a list

Research note `N-22`. For the thread fields of `DecSep` (`ActivationDecStepThread`), every moving
part of an activation is shown far from every piece of the machine other than the pieces of its own
list. The tools:

* `dsepT_base_ne`: every base piece has a nonempty box, so the box of a piece of the machine
  determines it (`dsepT_eq_of_box`, from the separation of the machine `machPieces_sep`);
* `dsepT_far_list`: to be far from every piece of the machine outside a list `L` of pieces of the
  machine, it suffices to be far from the box of every unit piece, module piece and corner
  reflector whose box is not the box of a piece of `L` (`dsepT_far_specs`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program}

/-! ### Boxes determine the pieces of the machine -/

/-- The box of a piece as data. -/
def dsepTB (g : Piece) : BoxT := ⟨g.a, g.b, g.lo, g.hi⟩

/-- A base piece of a list or the default OR gate has a nonempty box. -/
theorem dsepT_getD_ne {l : List Piece} (hl : ∀ x ∈ l, x.a ≤ x.b ∧ x.lo ≤ x.hi) (i : ℕ) :
    (l.getD i orGateP).a ≤ (l.getD i orGateP).b ∧
      (l.getD i orGateP).lo ≤ (l.getD i orGateP).hi := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[i]? with _ | x
  · simp [orGateP]
  · exact hl x (List.mem_of_getElem? h)

/-- **Every base piece has a nonempty box.** -/
theorem dsepT_base_ne (b : Base) : b.piece.a ≤ b.piece.b ∧ b.piece.lo ≤ b.piece.hi := by
  cases b with
  | orGate => simp [Base.piece, orGateP]
  | rf k =>
    simp only [Base.piece]
    rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp [rfP]
  | bodyDec i =>
    exact dsepT_getD_ne (by
      simp only [bodyDecPieces, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        simp [bodyDecG0, bodyDecG1, bodyDecG2, bodyDecG3, bodyDecG4, bodyDecG5, bodyDecG6,
          bodyDecG7]) i
  | bodyInc i =>
    exact dsepT_getD_ne (by
      simp only [bodyIncPieces, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> simp [bodyIncG0, bodyIncG1, bodyIncG2]) i
  | dz2g i =>
    refine dsepT_getD_ne ?_ i
    simp only [dz2gPieces, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    simp [dz2gG0, dz2gG1, dz2gG2, dz2gG3, dz2gG4, dz2gG5, dz2gG6, dz2gG7, dz2gG8, dz2gG9,
      dz2gG10, dz2gG11, dz2gG12, dz2gG13, dz2gG14, dz2gG15, dz2gG16, dz2gG17, dz2gG18, dz2gG19,
      dz2gG20, dz2gG21, dz2gG22, dz2gG23, dz2gG24, dz2gG25, dz2gG26, dz2gG27]
  | stNZ i =>
    exact dsepT_getD_ne (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> simp [stNZ0P, stNZ1P, stNZ2P]) i
  | stZ i =>
    exact dsepT_getD_ne (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> simp [stZ0P, stZ1P, stZ2P]) i
  | eatNZ => simp [Base.piece, eatNZEndP]
  | eatZ => simp [Base.piece, eatZEndP]

/-- Every piece of the machine has a nonempty box. -/
theorem dsepT_mach_ne {g : Piece} (hg : g ∈ machPieces p) : g.a ≤ g.b ∧ g.lo ≤ g.hi := by
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hg
  have := dsepT_base_ne s.base
  simp only [PSpec.piece, Piece.place]
  omega

/-- **Two pieces of the machine with the same box are equal.** -/
theorem dsepT_eq_of_box (hp : p.WellFormed) {g h : Piece} (hg : g ∈ machPieces p)
    (hh : h ∈ machPieces p) (e : dsepTB g = dsepTB h) : g = h := by
  by_contra hne
  have : Std.Symm Piece.Sep := ⟨fun _ _ h => Piece.Sep.symm' h⟩
  have hs := (machPieces_sep p hp).forall hg hh hne
  have hn := dsepT_mach_ne hg
  simp only [dsepTB, BoxT.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  refine hs (g.a, g.lo) ⟨le_rfl, hn.1, le_rfl, hn.2⟩ (g.a, g.lo) ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [] <;> omega
  · simp only [Near]; omega

/-! ### Far from every piece outside a list -/

/-- **Far from every piece of the machine whose box is not excluded**: it suffices to be far from
every unit piece, every module piece and every corner reflector whose box is not excluded. -/
theorem dsepT_far_specs {S : Set Cell} {own : BoxT → Prop}
    (hU : ∀ a < p.length + numRegs p, ∀ s ∈ unitSpecs p a, ¬ own s.bx →
      FarApart 2 S (Box s.bx.a s.bx.b s.bx.lo s.bx.hi))
    (hM : ∀ r < numRegs p, ∀ s ∈ moduleSpecs p r, ¬ own s.bx →
      FarApart 2 S (Box s.bx.a s.bx.b s.bx.lo s.bx.hi))
    (hC : ∀ c ∈ allCorners p, ¬ own (cornerSpec c).bx →
      FarApart 2 S (Box (cornerSpec c).bx.a (cornerSpec c).bx.b (cornerSpec c).bx.lo
        (cornerSpec c).bx.hi)) :
    ∀ g ∈ machPieces p, ¬ own (dsepTB g) → FarApart 2 S g.box := by
  intro g hg hn
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
  have e : dsepTB s.piece = s.bx := rfl
  rw [e] at hn
  rw [PSpec.piece_box]
  rcases mem_machSpecs hs with ⟨a, ha, hs⟩ | ⟨r, hr, hs⟩ | ⟨c, hc, hb⟩
  · exact hU a ha s hs hn
  · exact hM r hr s hs hn
  · rw [hb] at hn ⊢
    exact hC c hc hn

/-- **Far from every piece of the machine outside a list** `L` of pieces of the machine, from far
from every piece whose box is not the box of a piece of `L`. -/
theorem dsepT_far_list (hp : p.WellFormed) {S : Set Cell} {L : List Piece}
    (hL : ∀ x ∈ L, x ∈ machPieces p)
    (h : ∀ g ∈ machPieces p, ¬ (∃ x ∈ L, dsepTB x = dsepTB g) → FarApart 2 S g.box) :
    ∀ g ∈ machPieces p, g ∉ L → FarApart 2 S g.box := by
  intro g hg hn
  refine h g hg fun ⟨x, hx, e⟩ => hn ?_
  rw [← dsepT_eq_of_box hp (hL x hx) hg e]
  exact hx

/-! ### Far from the machine outside module `r` -/

/-- A set far in `uv` from a box with a `uv`-hull is far from the box. -/
theorem dsepT_far_uv {S : Set Cell} {B : BoxT} {u1 u2 v1 v2 : ℤ} (hB : B.InUV u1 u2 v1 v2)
    (h : ∀ x ∈ S, x.1 - x.2 + 6 ≤ u1 ∨ u2 + 6 ≤ x.1 - x.2 ∨ x.1 + x.2 + 6 ≤ v1 ∨
      v2 + 6 ≤ x.1 + x.2) :
    FarApart 2 S (Box B.a B.b B.lo B.hi) := by
  refine isep2_far_box fun x hx => ?_
  have := h x hx
  unfold BoxT.InUV at hB
  omega

/-- **A set in the band of module `r` is far from every piece of the machine whose box is not
excluded**, once it is far from the excluded-free pieces of module `r` and from the corners of
the zones of module `r`: the set lies in `u ∈ [U_r + modLeft + 12, U_r + modRight + 150]` and
above `v = modTop - 60`. -/
theorem dsepT_mod_far (hp : p.WellFormed) {r : ℕ} {S : Set Cell} {own : BoxT → Prop}
    (hS : ∀ x ∈ S, U p r + modLeft p + 12 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + modRight p + 150 ∧
      modTop p - 60 ≤ x.1 + x.2)
    (hM : ∀ s ∈ moduleSpecs p r, ¬ own s.bx → FarApart 2 S (Box s.bx.a s.bx.b s.bx.lo s.bx.hi))
    (hZ : ∀ c ∈ allCorners p, ((∃ idx, c.tag = .left r idx) ∨ ∃ j w, c.tag = .right r j w) →
      ¬ own (cornerSpec c).bx →
      FarApart 2 S (Box (cornerSpec c).bx.a (cornerSpec c).bx.b (cornerSpec c).bx.lo
        (cornerSpec c).bx.hi)) :
    ∀ g ∈ machPieces p, ¬ own (dsepTB g) → FarApart 2 S g.box := by
  have hf := layout_facts p
  have hU0 := U_ge p (r := r) (by omega)
  have hsl : 86 + 58 * P p ≤ slabR p := by unfold slabR; omega
  refine dsepT_far_specs ?_ ?_ ?_
  · intro a ha s hs _
    have hu := unitSpecs_uv p a hs
    have h6 := (sep06_units_module0 p (a := a) (by
      have : (a : ℤ) < p.length + numRegs p := by exact_mod_cast ha
      unfold N R; omega)).1
    refine dsepT_far_uv hu fun x hx => ?_
    have := hS x hx
    unfold modLeft at *
    omega
  · intro r' hr' s hs hn
    rcases lt_trichotomy r' r with h | rfl | h
    · have hu := (moduleSpecs_uv p r' hs).1
      have := U_add_le p (r := r') (r' := r) (by exact_mod_cast h)
      refine dsepT_far_uv hu fun x hx => ?_
      have := hS x hx
      unfold modLeft modRight PM at *
      omega
    · exact hM s hs hn
    · have hu := (moduleSpecs_uv p r' hs).1
      have := U_add_le p (r := r) (r' := r') (by exact_mod_cast h)
      refine dsepT_far_uv hu fun x hx => ?_
      have := hS x hx
      unfold modLeft modRight PM at *
      omega
  · intro c hc hn
    have hv := allCorners_valid hp c hc
    have hcu := corner_uv c
    obtain ⟨k, u, v, tag⟩ := c
    dsimp only at hcu
    cases tag with
    | band b n h' =>
      refine dsepT_far_uv hcu fun x hx => ?_
      have := hS x hx
      simp only [Valid] at hv
      simp only [modTop] at *
      omega
    | halt a' =>
      refine dsepT_far_uv hcu fun x hx => ?_
      have := hS x hx
      simp only [Valid] at hv
      simp only [modTop] at *
      omega
    | slab a' t' =>
      refine dsepT_far_uv hcu fun x hx => ?_
      have := hS x hx
      simp only [Valid] at hv
      simp only [modTop] at *
      omega
    | left r' idx =>
      rcases lt_trichotomy r' r with h | h | h
      · have := U_add_le p h
        refine dsepT_far_uv hcu fun x hx => ?_
        have := hS x hx
        simp only [Valid] at hv
        unfold modLeft modRight PM at *
        omega
      · subst h
        exact hZ _ hc (Or.inl ⟨idx, rfl⟩) hn
      · have := U_add_le p h
        refine dsepT_far_uv hcu fun x hx => ?_
        have := hS x hx
        simp only [Valid] at hv
        unfold modLeft modRight PM at *
        omega
    | right r' j w =>
      rcases lt_trichotomy r' r with h | h | h
      · have := U_add_le p h
        refine dsepT_far_uv hcu fun x hx => ?_
        have := hS x hx
        simp only [Valid] at hv
        unfold modLeft modRight PM at *
        omega
      · subst h
        exact hZ _ hc (Or.inr ⟨j, w, rfl⟩) hn
      · have := U_add_le p h
        refine dsepT_far_uv hcu fun x hx => ?_
        have := hS x hx
        simp only [Valid] at hv
        unfold modLeft modRight PM at *
        omega

/-! ### The ports of the left zone -/

/-- The port line of left-zone channel `idx`: the DEC copies `2 j`, the INC copy `2 D`, the NZ
tokens `2 D + 1 + 2 j` and the NZ answers `2 D + 2 + 2 j`. -/
def dsepTPort (p : Program) (idx v : ℤ) : Prop :=
  (idx = 2 * D p ∧ v = incPortV) ∨ ∃ j : ℤ, 0 ≤ j ∧ j < D p ∧
    ((idx = 2 * j ∧ v = decPortV p (2 * j)) ∨ (idx = 2 * D p + 1 + 2 * j ∧ v = nzTokPortV j) ∨
      (idx = 2 * D p + 2 + 2 * j ∧ v = nzAnsPortV j))

/-- A band corner list has no left-zone corner. -/
theorem dsepT_band_left (p : Program) (b s c H cd : ℤ) (k0 k4 : ℕ) :
    ∀ x ∈ bandCorners p b s c H cd k0 k4, ∀ r idx, x.tag ≠ .left r idx := by
  simp [bandCorners]

/-- An up-going link has no left-zone corner. -/
theorem dsepT_up_left (k0 : ℕ) (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) :
    ∀ x ∈ upCornersK k0 p b s c H a t, ∀ r idx, x.tag ≠ .left r idx := by
  simp [upCornersK, bandCorners]

/-- **The left-zone corners of the machine are on the port lines of their channels.** -/
theorem dsepT_left_port {p : Program} :
    ∀ c ∈ allCorners p, ∀ r idx, c.tag = .left r idx → dsepTPort p idx c.v := by
  intro c hc r idx ht
  unfold allCorners at hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨i, -, hc⟩ := List.mem_flatMap.1 hc
    unfold instrCorners specCorners instrSpecs at hc
    split at hc
    · simp only [haltCorners, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp at ht
    · obtain ⟨x, hx, hc⟩ := List.mem_flatMap.1 hc
      simp only [incSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact absurd ht (dsepT_up_left _ _ _ _ _ _ _ _ c hc r idx)
      · exact absurd ht (dsepT_up_left _ _ _ _ _ _ _ _ c hc r idx)
    · rename_i r' z' hi'
      have hj := callerIdx_lt_D p hi'
      have hD : D p = (numCallers p : ℤ) := rfl
      obtain ⟨x, hx, hc⟩ := List.mem_flatMap.1 hc
      simp only [decSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · simp only [downCorners, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with hc | rfl
        · exact absurd ht (dsepT_band_left _ _ _ _ _ _ _ _ c hc r idx)
        · simp only [CTag.left.injEq] at ht
          exact Or.inr ⟨_, by omega, by omega, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩
      · simp only [downCorners, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with hc | rfl
        · exact absurd ht (dsepT_band_left _ _ _ _ _ _ _ _ c hc r idx)
        · simp only [CTag.left.injEq] at ht
          exact Or.inr ⟨_, by omega, by omega, Or.inl ⟨by omega, rfl⟩⟩
      · simp only [ztokCorners, bandCorners, List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at ht
      · simp only [nzAnsCorners, List.mem_cons] at hc
        rcases hc with rfl | hc
        · simp only [CTag.left.injEq] at ht
          exact Or.inr ⟨_, by omega, by omega, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩
        · exact absurd ht (dsepT_up_left _ _ _ _ _ _ _ _ c hc r idx)
      · simp only [zAnsCorners, List.mem_cons] at hc
        rcases hc with rfl | rfl | hc
        · simp at ht
        · simp at ht
        · exact absurd ht (dsepT_up_left _ _ _ _ _ _ _ _ c hc r idx)
    · simp at hc
  · obtain ⟨r', -, hc⟩ := List.mem_flatMap.1 hc
    simp only [specCorners, mergeSpecs, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at hc
    simp only [mergeCorners, downCorners, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with hc | rfl
    · exact absurd ht (dsepT_band_left _ _ _ _ _ _ _ _ c hc r idx)
    · simp only [CTag.left.injEq] at ht
      exact Or.inl ⟨by omega, rfl⟩

/-! ### Sets placed at module `r` -/

/-- **A set placed at module `r` far from a box**, from the set far from the box moved back to the
frame of the module. -/
theorem dsepT_modImg_far {r : ℕ} {S : Set Cell} {a b lo hi : ℤ}
    (h : FarApart 2 S (Box (a - modDX p r) (b - modDX p r) (lo - modDY p r) (hi - modDY p r))) :
    FarApart 2 (modImg p r S) (Box a b lo hi) := by
  rintro _ ⟨x, hx, rfl⟩ y ⟨y1, y2, y3, y4⟩ hn
  refine h x hx (y - (modDX p r, modDY p r)) ⟨?_, ?_, ?_, ?_⟩ ?_
  · simp only [Prod.fst_sub]; omega
  · simp only [Prod.fst_sub]; omega
  · simp only [Prod.snd_sub]; omega
  · simp only [Prod.snd_sub]; omega
  · obtain ⟨n1, n2, n3, n4⟩ := hn
    simp only [Near, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at *
    omega

/-- A cell of a set placed at module `r`, in the frame of the module. -/
theorem dsepT_mem_modImg {r : ℕ} {S : Set Cell} {x : Cell} (hx : x ∈ modImg p r S) :
    (x.1 - modDX p r, x.2 - modDY p r) ∈ S := by
  obtain ⟨d, hd, rfl⟩ := hx
  convert hd using 1
  ext <;> simp

/-- The zone of a module-local set (module frame, `dsepM_corner_far`): right of the left zone,
inside the band of the module, above the bands, and left of `u = 1170` or below `v = 1450`. -/
def dsepTZone (p : Program) : Set Cell :=
  {x | -760 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ 1300 + 144 * D p ∧ -4100 - 198 * D p ≤ x.1 + x.2 ∧
    (x.1 - x.2 ≤ 1170 ∨ x.1 + x.2 ≤ 1450)}

/-- The lanes of the register diagonal lie in the zone. -/
theorem dsepT_regLanes_zone : regLanes ⊆ dsepTZone p := by
  have := one_le_D p
  rintro x ⟨x1, x2, x3⟩
  simp only [dsepTZone, Set.mem_ofPred_eq]
  omega

/-- A component in the zone. -/
theorem dsepT_BU_zone {a b lo hi U₁ U₂ V₁ V₂ : ℤ} (h1 : -760 ≤ U₁ ∨ -760 ≤ a - hi)
    (h2 : U₂ ≤ 1170 ∨ b - lo ≤ 1170 ∨ V₂ ≤ 1450 ∨ b + hi ≤ 1450)
    (h3 : -4298 ≤ V₁ ∨ -4298 ≤ a + lo) (h4 : U₂ ≤ 1444 ∨ b - lo ≤ 1444) :
    BU a b lo hi U₁ U₂ V₁ V₂ ⊆ dsepTZone p := by
  have := one_le_D p
  rintro x ⟨⟨x1, x2, x3, x4⟩, x5, x6, x7, x8⟩
  simp only [dsepTZone, Set.mem_ofPred_eq]
  omega

/-- **A set in the zone of module `r` is far from every piece of the machine outside a list**
`L`, from far from the module pieces whose boxes are not boxes of `L`. -/
theorem dsepT_zone_far (hp : p.WellFormed) {r : ℕ} {S : Set Cell} (hS : S ⊆ dsepTZone p)
    {L : List Piece} (hL : ∀ x ∈ L, x ∈ machPieces p)
    (hM : ∀ s ∈ moduleSpecs p r, ¬ (∃ x ∈ L, dsepTB x = s.bx) →
      FarApart 2 (modImg p r S) (Box s.bx.a s.bx.b s.bx.lo s.bx.hi)) :
    ∀ g ∈ machPieces p, g ∉ L → FarApart 2 (modImg p r S) g.box := by
  have hf := layout_facts p
  have hu := modD_uv p r
  have hU0 := U_ge p (r := r) (by omega)
  have hsl : 86 + 58 * P p ≤ slabR p := by unfold slabR; omega
  have hX : ∀ x ∈ modImg p r S, U p r - 760 ≤ x.1 - x.2 ∧ x.1 - x.2 ≤ U p r + 1300 + 144 * D p ∧
      -4100 - 198 * D p ≤ x.1 + x.2 ∧ (x.1 - x.2 ≤ U p r + 1170 ∨ x.1 + x.2 ≤ 1450) := by
    intro x hx
    have h := hS (dsepT_mem_modImg hx)
    simp only [dsepTZone, Set.mem_ofPred_eq] at h
    omega
  refine dsepT_far_list hp hL (dsepT_far_specs (own := fun B => ∃ x ∈ L, dsepTB x = B) ?_ ?_ ?_)
  · intro a ha s hs _
    have hu' := unitSpecs_uv p a hs
    have h6 := (sep06_units_module0 p (a := a) (by
      have : (a : ℤ) < p.length + numRegs p := by exact_mod_cast ha
      unfold N R; omega)).1
    refine dsepT_far_uv hu' fun x hx => ?_
    have := hX x hx
    unfold modLeft at *
    omega
  · intro r' hr' s hs hn
    rcases lt_trichotomy r' r with h | rfl | h
    · have hu' := (moduleSpecs_uv p r' hs).1
      have := U_add_le p (r := r') (r' := r) (by exact_mod_cast h)
      refine dsepT_far_uv hu' fun x hx => ?_
      have := hX x hx
      unfold PM at *
      omega
    · exact hM s hs hn
    · have hu' := (moduleSpecs_uv p r' hs).1
      have := U_add_le p (r := r) (r' := r') (by exact_mod_cast h)
      refine dsepT_far_uv hu' fun x hx => ?_
      have := hX x hx
      unfold PM at *
      omega
  · intro c hc _
    exact dsepM_corner_far hp r hX hc

/-! ### The pieces of module `r` by class, in the frame of the module -/

/-- The box of a base piece, as data. -/
def dsepTBase (b : Base) : BoxT := ⟨b.piece.a, b.piece.b, b.piece.lo, b.piece.hi⟩

/-- A box moved by `(x, y)`. -/
def BoxT.mv (B : BoxT) (x y : ℤ) : BoxT := ⟨B.a + x, B.b + x, B.lo + y, B.hi + y⟩

/-- The set of a box. -/
def BoxT.set (B : BoxT) : Set Cell := Box B.a B.b B.lo B.hi

/-- **A set placed at module `r` is far from the pieces of module `r` whose boxes are not
excluded**, from the boxes of the classes of pieces in the frame of the module (the groups,
`RF_J`, the INC gate, the DEC copies, the stations of both lines and the line-end eaters). -/
theorem dsepT_mod_cls {r : ℕ} {S : Set Cell} {own : BoxT → Prop}
    (hG : ∀ i < 28, ¬ own ((dsepTBase (.dz2g i)).mv (modDX p r) (modDY p r)) →
      FarApart 2 S (dsepTBase (.dz2g i)).set)
    (hJ : ¬ own ((dsepTBase (.rf 4)).mv (modDX p r - 850) (modDY p r - 1044)) →
      FarApart 2 S ((dsepTBase (.rf 4)).mv (-850) (-1044)).set)
    (hI : ¬ own ((dsepTBase .orGate).mv (modDX p r - 1132) (modDY p r - 1291)) →
      FarApart 2 S ((dsepTBase .orGate).mv (-1132) (-1291)).set)
    (hDm : ∀ m : ℤ, 0 ≤ m → m < 2 * D p →
      ¬ own ((dsepTBase .orGate).mv (modDX p r - 1700 - 35 * m) (modDY p r - 1727 - 64 * m)) →
      FarApart 2 S ((dsepTBase .orGate).mv (-1700 - 35 * m) (-1727 - 64 * m)).set)
    (hN : ∀ j : ℤ, 0 ≤ j → j < D p → ∀ i < 3,
      ¬ own ((dsepTBase (.stNZ i)).mv (modDX p r + 72 * j) (modDY p r + 72 * j)) →
      FarApart 2 S ((dsepTBase (.stNZ i)).mv (72 * j) (72 * j)).set)
    (hZ : ∀ j : ℤ, 0 ≤ j → j < D p → ∀ i < 3,
      ¬ own ((dsepTBase (.stZ i)).mv (modDX p r + 72 * j) (modDY p r - 72 * j)) →
      FarApart 2 S ((dsepTBase (.stZ i)).mv (72 * j) (-72 * j)).set)
    (hEN : ¬ own ((dsepTBase .eatNZ).mv (modDX p r + 72 * (D p - 1)) (modDY p r + 72 * (D p - 1)))
      → FarApart 2 S ((dsepTBase .eatNZ).mv (72 * (D p - 1)) (72 * (D p - 1))).set)
    (hEZ : ¬ own ((dsepTBase .eatZ).mv (modDX p r + 72 * (D p - 1)) (modDY p r - 72 * (D p - 1)))
      → FarApart 2 S ((dsepTBase .eatZ).mv (72 * (D p - 1)) (-72 * (D p - 1))).set) :
    ∀ s ∈ moduleSpecs p r, ¬ own s.bx →
      FarApart 2 (modImg p r S) (Box s.bx.a s.bx.b s.bx.lo s.bx.hi) := by
  have hD : D p = (numCallers p : ℤ) := rfl
  intro s hs hn
  refine dsepT_modImg_far ?_
  have key : ∀ (b : Base) (x y : ℤ) (ph : ℕ), (⟨b, modDX p r + x, modDY p r + y, ph⟩ : PSpec).bx =
      (dsepTBase b).mv (modDX p r + x) (modDY p r + y) := fun _ _ _ _ => rfl
  have key2 : ∀ (b : Base) (x y : ℤ),
      Box (((dsepTBase b).mv (modDX p r + x) (modDY p r + y)).a - modDX p r)
        (((dsepTBase b).mv (modDX p r + x) (modDY p r + y)).b - modDX p r)
        (((dsepTBase b).mv (modDX p r + x) (modDY p r + y)).lo - modDY p r)
        (((dsepTBase b).mv (modDX p r + x) (modDY p r + y)).hi - modDY p r) =
      ((dsepTBase b).mv x y).set := by
    intro b x y
    simp only [BoxT.mv, BoxT.set]
    congr 1 <;> ring
  rcases moduleSpecs_cls p r hs with ⟨i, ph, hi⟩ | ph | ph | ⟨m, ph, hm⟩ | ⟨i, j, ph, hi, hj⟩ |
    ⟨i, j, ph, hi, hj⟩ | ph | ph
  · have e := key (.dz2g i) 0 0 ph
    simp only [add_zero] at e
    rw [e] at hn ⊢
    have := key2 (.dz2g i) 0 0
    simp only [add_zero] at this
    rw [this]
    simpa [BoxT.mv] using hG i hi (by simpa [BoxT.mv] using hn)
  · have e := key (.rf 4) (-850) (-1044) ph
    simp only [← sub_eq_add_neg] at e
    rw [e] at hn ⊢
    rw [show modDX p r - 850 = modDX p r + -850 by ring, show modDY p r - 1044 =
      modDY p r + -1044 by ring, key2]
    exact hJ (by simpa [sub_eq_add_neg] using hn)
  · have e := key .orGate (-1132) (-1291) ph
    simp only [← sub_eq_add_neg] at e
    rw [e] at hn ⊢
    rw [show modDX p r - 1132 = modDX p r + -1132 by ring, show modDY p r - 1291 =
      modDY p r + -1291 by ring, key2]
    exact hI (by simpa [sub_eq_add_neg] using hn)
  · have e := key .orGate (-1700 - 35 * (m : ℤ)) (-1727 - 64 * (m : ℤ)) ph
    rw [show modDX p r + (-1700 - 35 * (m : ℤ)) = modDX p r - 1700 - 35 * (m : ℤ) by ring,
      show modDY p r + (-1727 - 64 * (m : ℤ)) = modDY p r - 1727 - 64 * (m : ℤ) by ring] at e
    rw [e] at hn ⊢
    rw [show modDX p r - 1700 - 35 * (m : ℤ) = modDX p r + (-1700 - 35 * (m : ℤ)) by ring,
      show modDY p r - 1727 - 64 * (m : ℤ) = modDY p r + (-1727 - 64 * (m : ℤ)) by ring, key2]
    exact hDm m (by omega) (by omega) hn
  · have e := key (.stNZ i) (72 * (j : ℤ)) (72 * (j : ℤ)) ph
    rw [e] at hn ⊢
    rw [key2]
    exact hN j (by omega) (by omega) i hi hn
  · have e := key (.stZ i) (72 * (j : ℤ)) (-72 * (j : ℤ)) ph
    rw [show modDY p r + -72 * (j : ℤ) = modDY p r - 72 * (j : ℤ) by ring] at e
    rw [e] at hn ⊢
    rw [show modDY p r - 72 * (j : ℤ) = modDY p r + -72 * (j : ℤ) by ring, key2]
    exact hZ j (by omega) (by omega) i hi (by
      rw [show modDY p r - 72 * (j : ℤ) = modDY p r + -72 * (j : ℤ) by ring] at hn
      convert hn using 2
      ring_nf)
  · have e := key .eatNZ (72 * (D p - 1)) (72 * (D p - 1)) ph
    rw [e] at hn ⊢
    rw [key2]
    exact hEN hn
  · have e := key .eatZ (72 * (D p - 1)) (-72 * (D p - 1)) ph
    rw [show modDY p r + -72 * (D p - 1) = modDY p r - 72 * (D p - 1) by ring] at e
    rw [e] at hn ⊢
    rw [show modDY p r - 72 * (D p - 1) = modDY p r + -72 * (D p - 1) by ring, key2]
    exact hEZ (by
      rw [show modDY p r - 72 * (D p - 1) = modDY p r + -72 * (D p - 1) by ring] at hn
      convert hn using 2
      ring_nf)

end LP

end LeanTheory.Life
