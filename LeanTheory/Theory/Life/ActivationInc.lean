/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.MachineState
public import LeanTheory.Theory.Life.Gen.BodyIncRun
public import LeanTheory.Theory.Life.Gen.Dz2eRun

/-!
# Towards the activation of an `inc` instruction

Layer 3 of the assembly plan (research note `N-22`) for an `inc` instruction: the control glider
at the entrance of unit `i` runs the body, the continue link to unit `i + 1` and the INC link to
the merge unit of the register, the merge link to the module, and the increment `dz2eOp` of the
register diagonal. This module proves the generic parts of that activation **inside the whole
machine** (every other piece idle):

* **reflections in world-line terms** (`reflect_reaction`): the reflector placed by
  `LayoutPieces.reflect g c` at a corner `c` turns the glider of the world line `g` into the
  glider of the outgoing world line `(reflect g c).2`, at the time `meetT g c`, for each of the
  eight images (`rfIn_cells`, `rfOut_cells` connect `Rf0Images` to the world lines `rfIn`, `rfOut`);
* **windows** (`window`, `window_reflect`): one active process (a flight, a reflection) beside
  the idle bundle of every other piece of a list with pairwise separated boxes;
* **routes** (`route_window`): a glider following a list of corners of `LayoutPieces.route`
  inside a list of idle pieces, under explicit, checkable separation conditions (`RouteOK`), ends
  on the world line `(route g cs).2`, with every generation inside the boxes of the pieces and a
  given set `Z`;
* **the lines of the links** (`onLine_of_through`, `reflect_through`, `upCorners_lines`,
  `unitLink_lines`, `incSpecs_lines`): for every program, both routes of every `inc` instruction
  (continue and INC link) meet each corner on the input line of its reflector (the world-line part
  of `RouteOK`), and arrive on the side line of the chosen entry copy;
* **time shifts** (`reflect_delay`, `route_delay`): the layout's routes, computed for one
  activation time, work at every time `≡ 0 (mod 30)`;
* **the body** (`bodyInc_wl`, `bodyInc_unit`): `bodyIncRun_rest` on world lines: the control at
  the entrance of unit `a` becomes the gliders of `unitWL a incDWL` and `unitWL a incRWL`, the first
  lines of the two routes of `incSpecs`;
* **the register end** (`rfJ_out`, `dz2eOp_module`, `RegS.val_push`, `RegS.inv_push`): `RF_J` of
  the module (phase `25`) emits the input of `dz2eOp`; `dz2eOp` placed at module `r` appends the
  pushing salvo to the register's queue; the value grows by one and the invariant is kept.

Not yet proved here: the separation conditions of `RouteOK` (flights and relays far from every
other piece of the machine) for the links of the layout, the arrival times (`T ≤ meetT`, the side
input residue of the entry copy), the entry chains of unit `i + 1` and of the merge unit, the merge
link, the INC OR gate of the module, and the composition of these windows into one step from
`encM` to `encM` (with the other registers' diagonals as processes).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The eight reflector images on world lines -/

/-- The reflector image `k` as a stage of a route (`Rf0Images`). -/
def rfStage : ℕ → Stage
  | 0 => rf0SWNW
  | 1 => rf0NWNE
  | 2 => rf0NESE
  | 3 => rf0SESW
  | 4 => rf0SENE
  | 5 => rf0NWSW
  | 6 => rf0NENW
  | _ => rf0SWSE

/-- The piece of image `k` is the piece of its stage. -/
theorem rfP_rest (k : ℕ) : (rfP k).rest = (rfStage k).G := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

/-- The box of the piece of image `k` is the rest box of its stage. -/
theorem rfP_box (k : ℕ) : (rfP k).box = (rfStage k).B := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

/-- Every reflection takes `30` generations. -/
theorem rfStage_Δ (k : ℕ) : (rfStage k).Δ = 30 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

/-- The input world lines of the reflectors are diagonal. -/
theorem rfIn_dir (k : ℕ) : (rfIn k).Dir := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [rfIn, WL.Dir, IsDir]

/-- The output world lines of the reflectors are diagonal. -/
theorem rfOut_dir (k : ℕ) : (rfOut k).Dir := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [rfOut, WL.Dir, IsDir]

/-- **The input of every reflector stage is the glider of `rfIn k` at time `-60`.** -/
theorem rfIn_cells (k : ℕ) : (rfIn k).cells (-60) = (rfStage k).In := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

/-- **The output of every reflector stage is the glider of `rfOut k` at time `-30`.** -/
theorem rfOut_cells (k : ℕ) : (rfOut k).cells (-30) = (rfStage k).Out := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

/-! ### Reflection at a corner of a route -/

/-- The delay `s` of `reflect g c`: the reflector at the corner `c` is at phase `0` at times
`≡ s (mod 30)`, and the incoming line is `rfIn` moved to the corner and delayed by `s`. -/
def delayS (g : WL) (c : Corner) : ℤ :=
  g.tau - (rfIn c.k).tau + 4 * (rfIn c.k).dx * rfX c.k c.u c.v

/-- The time at which the glider `g` enters the reflector of the corner `c`. -/
def meetT (g : WL) (c : Corner) : ℤ := delayS g c - 60

/-- The glider `g` arrives on the input line of the reflector of the corner `c`. -/
def OnLine (g : WL) (c : Corner) : Prop :=
  g = (rfIn c.k).shift (rfX c.k c.u c.v) (rfY c.k c.u c.v) (delayS g c)

/-- The translation of the reflector of the corner `c`. -/
def cornerV (c : Corner) : Cell := (rfX c.k c.u c.v, rfY c.k c.u c.v)

/-- The relay box of the reflector of the corner `c`, at its place. -/
def relayBox (c : Corner) : Set Cell := (fun x => cornerV c + x) '' (rfStage c.k).R

/-- The reflector image `k` is periodic with period `30`. -/
theorem rfStage_periodic (k n : ℕ) (hn : n % 30 = 0) :
    conway.evolve n (rfStage k).G = (rfStage k).G := by
  rw [conway.evolve_mod_of_evolve_eq (rfStage k).rest.evolve_eq n, hn, Rule.evolve_zero]

/-- The placed reflector of `reflect g c` at time `T` with `T ≡ s (mod 30)`. -/
theorem reflect_piece_at (g : WL) (c : Corner) (T : ℕ) (hT : ((T : ℤ) - delayS g c) % 30 = 0) :
    conway.evolve (T % 30) (reflect g c).1.piece.rest = translate (cornerV c) (rfStage c.k).G := by
  simp only [reflect, PSpec.piece, Base.piece, Piece.place, phase, cornerV]
  rw [Rule.evolve_translate, ← Rule.evolve_add, rfP_rest]
  congr 1
  apply rfStage_periodic
  have h1 := Int.emod_nonneg (-delayS g c) (by norm_num : (30 : ℤ) ≠ 0)
  have h2 := Int.toNat_of_nonneg h1
  unfold delayS at hT h1 h2
  omega

/-- **A reflection at a corner of a route, in world-line terms**: if the glider `g` arrives on the
input line of the corner `c`, the reflector placed by `reflect g c` turns it, from the time
`meetT g c` on, in `30` generations, into the glider of the outgoing world line `(reflect g c).2`,
inside the relay box of the corner. -/
theorem reflect_reaction {g : WL} {c : Corner} (hl : OnLine g c) (T : ℕ)
    (hT : (T : ℤ) = meetT g c) :
    Reaction (conway.evolve (T % 30) (reflect g c).1.piece.rest ∪ g.cells T)
      (conway.evolve ((T + 30) % 30) (reflect g c).1.piece.rest ∪ (reflect g c).2.cells (T + 30))
      30 (fun _ => relayBox c) := by
  unfold meetT at hT
  rw [reflect_piece_at g c T (by omega), reflect_piece_at g c (T + 30) (by push_cast; omega)]
  have hg : g.cells T = translate (cornerV c) (rfStage c.k).In := by
    rw [hl, WL.shift_cells (rfIn_dir _), show (T : ℤ) - delayS g c = -60 by omega, rfIn_cells,
      cornerV]
  have ho : (reflect g c).2.cells ((T : ℤ) + 30) = translate (cornerV c) (rfStage c.k).Out := by
    simp only [reflect]
    rw [WL.shift_cells (rfOut_dir _), ← rfOut_cells, cornerV]
    congr 2
    unfold delayS at hT
    omega
  rw [hg, ho, ← translate_union, ← translate_union]
  have h := ((rfStage c.k).relay.translate (cornerV c))
  rw [rfStage_Δ, phase, show 30 % 30 = 0 by norm_num, Rule.evolve_zero] at h
  exact h

/-- The world line `w` passes through the point `(u, v)` (`u = x - y`, `v = x + y`). -/
def WL.Through (w : WL) (u v : ℤ) : Prop := 2 * w.lane = (w.dx + w.dy) * u + (w.dy - w.dx) * v

/-- **A glider on the input line of a corner**: a glider flying in the input direction of the
image of the corner, through the corner point, is on the input line of the reflector, provided the
corner point has the parity of the image (`u - cu + v - cv` even). -/
theorem onLine_of_through {g : WL} {c : Corner} (hdx : g.dx = (rfIn c.k).dx)
    (hdy : g.dy = (rfIn c.k).dy) (hpar : (c.u - rfCU c.k + c.v - rfCV c.k) % 2 = 0)
    (ht : g.Through c.u c.v) : OnLine g c := by
  obtain ⟨dx, dy, lane, tau⟩ := g
  obtain ⟨k, u, v, tag⟩ := c
  simp only [OnLine, WL.Through, delayS, WL.shift, rfX, rfY] at *
  subst hdx hdy
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rfIn, rfCU, rfCV, WL.mk.injEq, true_and] at * <;> refine ⟨by omega, by ring⟩

/-- **The outgoing glider of a corner passes through the corner point** (in the output direction of
the image), provided the corner point has the parity of the image. -/
theorem reflect_through (g : WL) (c : Corner) (hpar : (c.u - rfCU c.k + c.v - rfCV c.k) % 2 = 0) :
    (reflect g c).2.Through c.u c.v ∧ (reflect g c).2.dx = (rfOut c.k).dx ∧
      (reflect g c).2.dy = (rfOut c.k).dy := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only [reflect, WL.Through, WL.shift, rfX, rfY] at *
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [rfOut, rfCU, rfCV, and_true] at * <;> omega

/-- Every corner of a route is met on its input line. -/
def RouteLines : WL → List Corner → Prop
  | _, [] => True
  | g, c :: cs => OnLine g c ∧ RouteLines (reflect g c).2 cs

/-- `trackOut` has the parity opposite to the source column. -/
theorem trackOut_par (p : Program) (b s c : ℤ) : (c + trackOut p b s c) % 2 = 1 := by
  have := VT_mod p
  unfold trackOut track
  omega

/-- `trackBack` has the parity opposite to the source column. -/
theorem trackBack_par (p : Program) (b s c : ℤ) : (c + trackBack p b s c) % 2 = 1 := by
  have := VT_mod p
  unfold trackBack track
  omega

/-- **The lines of an up-going link** (`upCorners`: continue, INC link, answers): a glider flying
`SE` on the source column `c` meets every corner on its input line, provided the hairpin `H` and
the destination column have the parity of `c` and the destination corner has odd `u + v`; it
leaves flying `NE` through the destination corner (on the side line of the entry copy). -/
theorem upCorners_lines (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) {g : WL} (hdx : g.dx = 1)
    (hdy : g.dy = 1) (hl : g.lane = c) (hH : (H - c) % 2 = 0) (hd : (destU p a t - c) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) :
    RouteLines g (upCorners p b s c H a t) ∧ (route g (upCorners p b s c H a t)).2.dx = 1 ∧
      (route g (upCorners p b s c H a t)).2.dy = -1 ∧
      (route g (upCorners p b s c H a t)).2.Through (destU p a t) (destV p t) := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  set vO := trackOut p b s c
  set vB := trackBack p b s c
  set cd := destU p a t
  set vD := destV p t
  simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append, route,
    RouteLines]
  -- corner 1: `SE → SW` at `(c, OUT)`
  have p1 : (c - rfCU 3 + vO - rfCV 3) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l1 : OnLine g ⟨3, c, vO, .band b s false⟩ :=
    onLine_of_through (by simp [hdx, rfIn]) (by simp [hdy, rfIn]) p1
      (by simp only [WL.Through, hdx, hdy, hl]; ring)
  obtain ⟨t1, x1, y1⟩ := reflect_through g ⟨3, c, vO, .band b s false⟩ p1
  set g1 := (reflect g ⟨3, c, vO, .band b s false⟩).2
  simp only [rfOut] at x1 y1
  -- corner 2: `SW → SE` at `(H, OUT)`
  have p2 : (H - rfCU 7 + vO - rfCV 7) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l2 : OnLine g1 ⟨7, H, vO, .band b s true⟩ :=
    onLine_of_through (by simp [x1, rfIn]) (by simp [y1, rfIn]) p2
      (by simp only [WL.Through, x1, y1] at t1 ⊢; linarith)
  obtain ⟨t2, x2, y2⟩ := reflect_through g1 ⟨7, H, vO, .band b s true⟩ p2
  set g2 := (reflect g1 ⟨7, H, vO, .band b s true⟩).2
  simp only [rfOut] at x2 y2
  -- corner 3: `SE → NE` at `(H, BACK)`
  have p3 : (H - rfCU 4 + vB - rfCV 4) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l3 : OnLine g2 ⟨4, H, vB, .band b (9 - s) true⟩ :=
    onLine_of_through (by simp [x2, rfIn]) (by simp [y2, rfIn]) p3
      (by simp only [WL.Through, x2, y2] at t2 ⊢; linarith)
  obtain ⟨t3, x3, y3⟩ := reflect_through g2 ⟨4, H, vB, .band b (9 - s) true⟩ p3
  set g3 := (reflect g2 ⟨4, H, vB, .band b (9 - s) true⟩).2
  simp only [rfOut] at x3 y3
  -- corner 4: `NE → NW` at `(cd, BACK)`
  have p4 : (cd - rfCU 6 + vB - rfCV 6) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l4 : OnLine g3 ⟨6, cd, vB, .band b (9 - s) false⟩ :=
    onLine_of_through (by simp [x3, rfIn]) (by simp [y3, rfIn]) p4
      (by simp only [WL.Through, x3, y3] at t3 ⊢; linarith)
  obtain ⟨t4, x4, y4⟩ := reflect_through g3 ⟨6, cd, vB, .band b (9 - s) false⟩ p4
  set g4 := (reflect g3 ⟨6, cd, vB, .band b (9 - s) false⟩).2
  simp only [rfOut] at x4 y4
  -- corner 5: `NW → NE` at `(cd, side line)`
  have p5 : (cd - rfCU 1 + vD - rfCV 1) % 2 = 0 := by simp only [rfCU, rfCV]; omega
  have l5 : OnLine g4 ⟨1, cd, vD, .slab a t⟩ :=
    onLine_of_through (by simp [x4, rfIn]) (by simp [y4, rfIn]) p5
      (by simp only [WL.Through, x4, y4] at t4 ⊢; linarith)
  obtain ⟨t5, x5, y5⟩ := reflect_through g4 ⟨1, cd, vD, .slab a t⟩ p5
  simp only [rfOut] at x5 y5
  exact ⟨⟨l1, l2, l3, l4, l5, trivial⟩, x5, y5, t5⟩

/-- **The lines of a link from a unit column to an entry copy**: the output of unit `i` on the
template column `w` (a `SE` world line `⟨1, 1, w, τ⟩` placed in unit `i`), routed by `upCorners`
with a hairpin of the parity of its column to the entry copy chosen by `copyIdx` of any unit `a`,
meets every corner on its input line and arrives `NE` through the input corner of the copy. This
covers the continue (`incD`) and the INC link (`incR`) of every `inc` instruction, for every
hairpin delay. -/
theorem unitLink_lines (p : Program) (i a : ℕ) (w τ b s H e : ℤ)
    (hH : (H - (A p i + w)) % 2 = 0) :
    RouteLines (unitWL p i ⟨1, 1, w, τ⟩)
        (upCorners p b s (A p i + w) H a (copyIdx (unitC0 p a) e (A p i + w))) ∧
      (route (unitWL p i ⟨1, 1, w, τ⟩)
        (upCorners p b s (A p i + w) H a (copyIdx (unitC0 p a) e (A p i + w)))).2.dx = 1 ∧
      (route (unitWL p i ⟨1, 1, w, τ⟩)
        (upCorners p b s (A p i + w) H a (copyIdx (unitC0 p a) e (A p i + w)))).2.dy = -1 ∧
      (route (unitWL p i ⟨1, 1, w, τ⟩)
        (upCorners p b s (A p i + w) H a (copyIdx (unitC0 p a) e (A p i + w)))).2.Through
        (destU p a (copyIdx (unitC0 p a) e (A p i + w)))
        (destV p (copyIdx (unitC0 p a) e (A p i + w))) := by
  have hu := unitD_uv p i
  have ha := A_even p a
  have hai := A_even p i
  have hv := VU_even p
  have hc := copyBeta_spec (unitC0 p a) e (A p i + w)
  have hC0 : unitC0 p a % 2 = 1 := by
    obtain h | h | h := unitC0_cases p a <;> rw [h] <;> rfl
  refine upCorners_lines p b s (A p i + w) H a _ rfl rfl ?_ hH ?_ ?_
  · simp only [unitWL, WL.shift]
    omega
  · simp only [destU, inCol] at hc ⊢
    omega
  · simp only [destU, destV, inCol, sideV]
    omega

/-- The hairpin of a continue link has the parity of its source column. -/
theorem hairCont_par (p : Program) (G e c : ℤ) : (hairCont p G e c - c) % 2 = 0 := by
  have := fixp_parity (HI p - 62 - G - 2 * e) (c % 2)
  unfold hairCont
  omega

/-- The hairpin of a regular link has the parity of its source column. -/
theorem hairReg_par (p : Program) (s e c : ℤ) : (hairReg p s e c - c) % 2 = 0 := by
  have := fixp_parity (HI p + 90 * s - 2 * e) (c % 2)
  unfold hairReg
  omega

/-- The merge units have the first input column of the halt/merge template. -/
theorem unitC0_merge (p : Program) (r : ℕ) : unitC0 p (p.length + r) = C0halt := by
  simp [unitC0, unitKind, UKind.C0]

/-- **Both routes of an `inc` instruction meet every corner on its input line** (the continue and
the INC link of `incSpecs`), for every program: the world-line conditions `OnLine` of `RouteOK`. -/
theorem incSpecs_lines (p : Program) (i r : ℕ) : ∀ x ∈ incSpecs p i r, RouteLines x.1 x.2 := by
  intro x hx
  simp only [incSpecs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact (unitLink_lines p i _ 68 605 _ 0 _ _ (hairCont_par _ _ _ _)).1
  · rw [show C0halt = unitC0 p (p.length + r) from (unitC0_merge p r).symm]
    exact (unitLink_lines p i _ 157 1029 _ 1 _ _ (hairReg_par _ _ _ _)).1

/-! ### Windows: one active process inside the idle machine -/

/-- Membership in the pieces of a list at phase `T`. -/
theorem mem_piecesAt {L : List Piece} {T : ℕ} {c : Cell} :
    c ∈ piecesAt L T ↔ ∃ g ∈ L, c ∈ conway.evolve (T % 30) g.rest := by
  induction L with
  | nil => simp [piecesAt]
  | cons g L ih =>
    simp only [piecesAt, List.foldr_cons, mem_union] at ih ⊢
    rw [ih]
    simp

/-- The pieces at phase `T` do not depend on the order of the list. -/
theorem piecesAt_perm {L L' : List Piece} (h : L.Perm L') (T : ℕ) :
    piecesAt L T = piecesAt L' T := by
  ext c
  simp only [mem_piecesAt, h.mem_iff]

/-- Membership in the boxes of a list. -/
theorem mem_boxesOf {L : List Piece} {c : Cell} : c ∈ boxesOf L ↔ ∃ g ∈ L, c ∈ g.box := by
  induction L with
  | nil => simp [boxesOf]
  | cons g L ih =>
    simp only [boxesOf, List.foldr_cons, Set.mem_union] at ih ⊢
    rw [ih]
    simp

/-- The boxes of a sublist lie in the boxes of the list. -/
theorem boxesOf_subset {L L' : List Piece} (h : ∀ g ∈ L', g ∈ L) : boxesOf L' ⊆ boxesOf L :=
  fun _ hc => by
    obtain ⟨g, hg, hc⟩ := mem_boxesOf.1 hc
    exact mem_boxesOf.2 ⟨g, h g hg, hc⟩

/-- A set far from every box of a list is far from their union. -/
theorem farApart_boxesOf {A : Set Cell} {L : List Piece} (h : ∀ g ∈ L, FarApart 2 A g.box) :
    FarApart 2 A (boxesOf L) := fun a ha b hb => by
  obtain ⟨g, hg, hb⟩ := mem_boxesOf.1 hb
  exact h g hg a ha b hb

/-- Pieces are symmetrically separated. -/
theorem Piece.Sep.symm' {g h : Piece} (hgh : Piece.Sep g h) : Piece.Sep h g := FarApart.symm' hgh

/-- **A window**: a process whose footprint stays far from every piece of a list runs beside the
idle pieces. -/
theorem window {L : List Piece} (hL : L.Pairwise Piece.Sep) (T n : ℕ) {X Y : Finset Cell}
    {F : ℕ → Set Cell} (h : Reaction X Y n F) (hfar : ∀ i < n, ∀ g ∈ L, FarApart 2 (F i) g.box) :
    Reaction (piecesAt L T ∪ X) (piecesAt L (T + n) ∪ Y) n (fun i => boxesOf L ∪ F i) := by
  have hb := (bundleAt L hL T n).reaction
  rw [bundleAt_P, bundleAt_Q] at hb
  refine (hb.par h fun i hi => ?_).mono fun i _ => ?_
  · rw [bundleAt_F]
    exact FarApart.symm' (farApart_boxesOf (hfar i hi))
  · rw [bundleAt_F]

/-- **A reflection window**: the reflector of the corner `c` (one piece of the list) turns the
glider while every other piece idles. -/
theorem window_reflect {L L' : List Piece} {g : WL} {c : Corner}
    (hperm : L.Perm ((reflect g c).1.piece :: L')) (hL : L.Pairwise Piece.Sep) (hl : OnLine g c)
    (T : ℕ) (hT : (T : ℤ) = meetT g c) (hfar : ∀ h ∈ L', FarApart 2 (relayBox c) h.box) :
    Reaction (piecesAt L T ∪ g.cells T) (piecesAt L (T + 30) ∪ (reflect g c).2.cells (T + 30)) 30
      (fun _ => boxesOf L ∪ relayBox c) := by
  have hL' : L'.Pairwise Piece.Sep :=
    ((hperm.pairwise_iff fun h => Piece.Sep.symm' h).1 hL).of_cons
  have h := window hL' T 30 (reflect_reaction hl T hT) fun _ _ h hh => hfar h hh
  rw [piecesAt_perm hperm, piecesAt_perm hperm]
  simp only [piecesAt, List.foldr_cons] at h ⊢
  have e1 : conway.evolve (T % 30) (reflect g c).1.piece.rest ∪ piecesAt L' T ∪ g.cells T =
      piecesAt L' T ∪ (conway.evolve (T % 30) (reflect g c).1.piece.rest ∪ g.cells T) := by
    ac_rfl
  have e2 : conway.evolve ((T + 30) % 30) (reflect g c).1.piece.rest ∪ piecesAt L' (T + 30) ∪
      (reflect g c).2.cells (↑T + 30) =
      piecesAt L' (T + 30) ∪ (conway.evolve ((T + 30) % 30) (reflect g c).1.piece.rest ∪
        (reflect g c).2.cells (↑T + 30)) := by
    ac_rfl
  simp only [piecesAt] at e1 e2
  rw [e1, e2]
  refine h.mono fun i _ => Set.union_subset_union (boxesOf_subset fun x hx => ?_) le_rfl
  exact hperm.mem_iff.2 (List.mem_cons_of_mem _ hx)

/-! ### Routes through the idle machine -/

/-- **The conditions for a glider to follow a list of corners through a list of idle pieces**,
from time `T`, inside the set `Z`: before each corner, the glider is on the input line of the
corner and flies to it with its boxes in `Z` and far from every piece; the reflector of the corner
is a piece of the list and its relay box (in `Z`) is far from every other piece. At the end the
glider's box is in `Z`. -/
def RouteOK (L : List Piece) (Z : Set Cell) : WL → List Corner → ℕ → Prop
  | g, [], T => g.Dir ∧ g.box T ⊆ Z
  | g, c :: cs, T => g.Dir ∧ OnLine g c ∧ (T : ℤ) ≤ meetT g c ∧
      (∀ i : ℕ, (T : ℤ) + i ≤ meetT g c → g.box (T + i) ⊆ Z) ∧
      (∀ i : ℕ, (T : ℤ) + i < meetT g c → ∀ h ∈ L, FarApart 2 (g.box (T + i)) h.box) ∧
      relayBox c ⊆ Z ∧
      (∃ L' : List Piece, L.Perm ((reflect g c).1.piece :: L') ∧
        ∀ h ∈ L', FarApart 2 (relayBox c) h.box) ∧
      RouteOK L Z (reflect g c).2 cs ((meetT g c).toNat + 30)

/-- The time at which the glider leaves the last corner of a route (started at time `T`). -/
def routeEnd : WL → List Corner → ℕ → ℕ
  | _, [], T => T
  | g, c :: cs, _ => routeEnd (reflect g c).2 cs ((meetT g c).toNat + 30)

/-- **A glider follows a route through the idle machine**: under `RouteOK`, the idle pieces and the
glider of `g` at time `T` become, at the end of the route, the idle pieces and the glider of the
final world line `(route g cs).2`, every generation inside the boxes of the pieces and `Z`. -/
theorem route_window {L : List Piece} (hL : L.Pairwise Piece.Sep) {Z : Set Cell} :
    ∀ (cs : List Corner) (g : WL) (T : ℕ), RouteOK L Z g cs T → T ≤ routeEnd g cs T ∧
      Reaction (piecesAt L T ∪ g.cells T)
        (piecesAt L (routeEnd g cs T) ∪ (route g cs).2.cells (routeEnd g cs T))
        (routeEnd g cs T - T) (fun _ => boxesOf L ∪ Z)
  | [], g, T, ⟨hd, hz⟩ => by
    refine ⟨le_rfl, ?_⟩
    have h := window hL T 0 (WL.flight hd T 0) fun i hi => absurd hi (Nat.not_lt_zero i)
    simp only [route, routeEnd, Nat.sub_self, Nat.cast_zero, add_zero] at h ⊢
    refine h.mono fun i hi => Set.union_subset_union le_rfl ?_
    rw [show i = 0 by omega, Nat.cast_zero, add_zero]
    exact hz
  | c :: cs, g, T, ⟨hd, hl, hle, hfz, hfl, hrz, ⟨L', hperm, hfar⟩, hrest⟩ => by
    obtain ⟨hend, hr⟩ := route_window hL cs _ _ hrest
    set m := (meetT g c).toNat with hm
    have hmT : ((m : ℕ) : ℤ) = meetT g c := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hTm : T ≤ m := by omega
    -- the flight to the corner
    have h1 := window hL T (m - T) (WL.flight hd T (m - T)) fun i hi =>
      hfl i (by omega)
    rw [show T + (m - T) = m by omega,
      show (T : ℤ) + ((m - T : ℕ) : ℤ) = (m : ℤ) by push_cast [Nat.cast_sub hTm]; ring] at h1
    -- the reflection
    have h2 := window_reflect hperm hL hl m hmT hfar
    have h12 := h1.seq h2
    have h123 := h12.seq hr
    simp only [routeEnd, route] at hend ⊢
    rw [← hm]
    refine ⟨by omega, ?_⟩
    rw [show routeEnd (reflect g c).2 cs (m + 30) - T =
      m - T + 30 + (routeEnd (reflect g c).2 cs (m + 30) - (m + 30)) by omega]
    refine h123.mono fun i _ => ?_
    split_ifs with ha hb
    · exact Set.union_subset_union le_rfl (hfz i (by push_cast [Nat.cast_sub hTm] at *; omega))
    · exact Set.union_subset_union le_rfl hrz
    · exact le_rfl

/-! ### Activations at any time `≡ 0 (mod 30)` -/

/-- A world line delayed by a multiple of `30` meets the same reflector, and leaves on the outgoing
world line delayed alike. -/
theorem reflect_delay (g : WL) (c : Corner) (d : ℤ) (hd : d % 30 = 0) :
    reflect (g.shift 0 0 d) c = ((reflect g c).1, (reflect g c).2.shift 0 0 d) := by
  simp only [reflect, WL.shift, mul_zero, sub_zero, add_zero, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · congr 2
    omega
  · congr 1
    ring

/-- **The routes of the layout work at every time `≡ 0 (mod 30)`**: the reflectors of a route do
not change when its glider is delayed by a multiple of `30`, and the final world line is delayed
alike. -/
theorem route_delay (d : ℤ) (hd : d % 30 = 0) : ∀ (g : WL) (cs : List Corner),
    route (g.shift 0 0 d) cs = ((route g cs).1, (route g cs).2.shift 0 0 d)
  | g, [] => rfl
  | g, c :: cs => by
    simp only [route, reflect_delay g c d hd, route_delay d hd _ cs]

/-! ### The body of an `inc` unit on world lines -/

/-- The body input is the glider of the template's halt/merge output line `haltDWL`, delayed by
`-1080` (the template time of the body input at copy `0` is `1080`). -/
theorem bodyIn_wl : bodyIn = (haltDWL.shift 0 0 (-1080)).cells 0 := rfl

/-- **The body of an `inc` unit on world lines** (`bodyIncRun_rest`): the control at the body input
at time `0` becomes, `930` generations later, the gliders of the template outputs `D` (continue,
`incDWL`) and `R` (INC link, `incRWL`), at template time `2010 = 930 + 1080`. -/
theorem bodyInc_wl :
    conway.evolve 930 (bodyIncRest ∪ bodyIn) =
      bodyIncRest ∪ incDWL.cells 2010 ∪ incRWL.cells 2010 := by
  rw [bodyIn, bodyIncRun_rest]
  rfl

/-- The world line of a template, placed in unit `a`, carries the template's glider translated to
the unit. -/
theorem unitWL_cells (p : Program) (a : ℕ) {w : WL} (hw : w.Dir) (t : ℤ) :
    (unitWL p a w).cells t = translate (unitDX p a, unitDY p a) (w.cells t) := by
  rw [unitWL, WL.shift_cells hw, sub_zero]

/-- **The body of an `inc` unit, placed in unit `a`**: the control glider at the entrance becomes
the gliders of the continue and of the INC link on their layout world lines (`unitWL a incDWL`,
`unitWL a incRWL`, the first lines of the routes of `incSpecs`). -/
theorem bodyInc_unit (p : Program) (a : ℕ) :
    conway.evolve 930 (translate (unitDX p a, unitDY p a) bodyIncRest ∪ ctrlAt p a) =
      translate (unitDX p a, unitDY p a) bodyIncRest ∪ (unitWL p a incDWL).cells 2010 ∪
        (unitWL p a incRWL).cells 2010 := by
  have hD : incDWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have hR : incRWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  rw [ctrlAt, ← translate_union, Rule.evolve_translate, bodyInc_wl, unitWL_cells p a hD,
    unitWL_cells p a hR, translate_union, translate_union]

/-! ### The register end of the increment -/

/-- The input glider of `dz2eOp` (module frame, time `0`) on its world line (`NE`). -/
def incInWL : WL := ⟨1, -1, 1910, 3426⟩

/-- The input of `dz2eOp` is the glider of `incInWL` at time `0`. -/
theorem incInWL_cells : incInWL.cells 0 = ofRows (-857) (-1054) [6, 5, 4] := rfl

/-- **`RF_J` of the module emits the input of `dz2eOp`**: `RF_J` is the reflector image `4` placed
at `(-850, -1044)` at phase `25` (`moduleSpecs`), i.e. delay `s ≡ 5 (mod 30)`; its output world
line with delay `5` is `incInWL`. -/
theorem rfJ_out : (rfOut 4).shift (-850) (-1044) 5 = incInWL := rfl

/-- The input line of `RF_J` (delay `5`): the `SE` output line of the INC OR gate of the module. -/
theorem rfJ_in : (rfIn 4).shift (-850) (-1044) 5 = ⟨1, 1, 173, 3431⟩ := rfl

/-- The register after the increment: the pushing salvo appended to the queue. -/
def RegS.push (R : RegS) (Vs' : ℤ) : RegS :=
  ⟨R.q ++ [(regPush, (7 : ℤ) + (((R.m + 6653) / 4 : ℕ) : ℤ))], R.K, R.m + 6990, Vs', R.Vb⟩

/-- Appending a salvo adds its move. -/
theorem qMove_append (q : List (Salvo × ℤ)) (σ : Salvo) (e : ℤ) :
    qMove (q ++ [(σ, e)]) = qMove q + σ.d := by
  induction q with
  | nil => simp [qMove]
  | cons x q ih => simp only [List.cons_append, qMove, ih]; ring

/-- **The increment raises the value of the register by one.** -/
theorem RegS.val_push (R : RegS) (hR : R.Inv) (Vs' : ℤ) : (R.push Vs').val = R.val + 1 := by
  have := hR.2.2.2
  simp only [RegS.val, RegS.push, qMove_append, regPush]
  omega

/-- The register after the increment satisfies the invariant. -/
theorem RegS.inv_push {R : RegS} (hR : R.Inv) {Vs' : ℤ}
    (hv' : DiagValid regParams Vs' R.Vb R.K
      (R.q ++ [(regPush, (7 : ℤ) + (((R.m + 6653) / 4 : ℕ) : ℤ))]))
    (hVs' : -34 ≤ Vs' + 2 * (((R.m + 6653) / 4 : ℕ) : ℤ)) : (R.push Vs').Inv := by
  obtain ⟨-, h2, -, h4⟩ := hR
  refine ⟨hv', h2, ?_, ?_⟩
  · have : (R.m + 6653) / 4 + 84 ≤ (R.m + 6990) / 4 := by omega
    simp only [RegS.push]
    omega
  · simp only [RegS.push, qMove_append, regPush]
    omega

/-- **The increment at module `r`** (`dz2eOp` placed at the module): the register circuit at rest,
the input glider of `incInWL` and the register diagonal become the circuit at rest and the diagonal
with the pushing salvo appended to its queue, `6990` generations later (a multiple of `30`). -/
theorem dz2eOp_module (p : Program) (r : ℕ) {R : RegS} (hR : R.Inv) {Vs' : ℤ}
    (hv' : DiagValid regParams Vs' R.Vb R.K
      (R.q ++ [(regPush, (7 : ℤ) + (((R.m + 6653) / 4 : ℕ) : ℤ))]))
    (hm : (R.m + 6653) % 4 = 0) (hVs' : -34 ≤ Vs' + 2 * (((R.m + 6653) / 4 : ℕ) : ℤ)) :
    conway.evolve 6990
        (translate (modDX p r, modDY p r) (dz2eRest ∪ incInWL.cells 0) ∪ regAt p r R) =
      translate (modDX p r, modDY p r) dz2eRest ∪ regAt p r (R.push Vs') := by
  rw [regAt, regAt, ← translate_union, Rule.evolve_translate, incInWL_cells]
  rw [dz2eOp R.q R.K R.Vs R.Vb Vs' R.m hR.1 hv' hm hR.2.1 hR.2.2.1 hVs', translate_union]
  rfl

end LP

end LeanTheory.Life
