/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncLinks

/-!
# Separation of the routes of the machine: the corner windows

Research note `N-22` (layer 3), report `R-31` §3 (#13 and the checks (C) "segments vs pieces").

**The separation part `RouteSep` of `RouteOK` (`ActivationIncLinks`) cannot hold for any route
of the layout.** Its flight condition asks the box `WL.box` of the glider to be far (`FarApart 2`)
from *every* piece of `L` at every time before the corner is met, and its reflection condition
asks the reflector of the corner to be a piece of `L`. But the glider box comes within two cells
of the box of its own reflector shortly before and after the reflection
(`rfIn_near`, `rfOut_near`): for the image `0` the incoming glider box at `meetT - 1` overlaps
the reflector box, and the outgoing glider box at `meetT + 30` (the start of the next flight) is
at distance `2` from it. So `RouteOK` holds for no route with a corner.

This module states the corrected separation condition `RouteSepX` with **corner windows** (the
convention of `ActivationHalt`, `reflect_early`): the flight to a corner is checked up to `20`
generations before the corner is met, the reflection is replaced by an extended reflection of
`60` generations (from `meetT - 20` to `meetT + 40`) inside the **extended relay box**
`relayBoxX` (the relay box of the image together with the glider boxes of those generations),
and the next flight starts at `meetT + 40`. Times are integers. The legs are in fact proved
separated on the larger windows `[meetT + 34, meetT' - 16]` (`LegOK`, `StartOK`). It then
provides the generic tools for the separation proofs:

* the glider centre `WL.cu`, `WL.cv` and the rays of the incoming and outgoing lines of every
  image (`in_center`, `out_center`, `out_center_at`) and the separation of the glider from its own
  reflector outside the window (`in_far`, `out_far`);
* `FarRect`: a box `≥ 6` (in `u` or `v`) from a rectangle in `(u, v)`, and `far_glider`;
* `flight_far`: a flight far from every piece of the machine, given a rectangle of the flight,
  the corners excluded from it and the separation of every other piece from the rectangle;
* `relay_ok`: the extended relay box of every corner of the machine is far from every other piece
  (`corner_gap61`: corners at distinct places are `≥ 61` apart in `u` or in `v`);
* the region of the machine (`box_sub_region`, `relayX_sub_region`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The near misses of `RouteSep` -/

/-- The box of the glider of a world line at time `t`, as data. -/
def gbx (w : WL) (t : ℤ) : BoxT := ⟨w.px t - 1, w.px t + 3, w.py t - 1, w.py t + 3⟩

/-- The glider box of `WL.box` is the box of `gbx`. -/
theorem box_gbx (w : WL) (t : ℤ) :
    w.box t = Box (gbx w t).a (gbx w t).b (gbx w t).lo (gbx w t).hi := rfl

/-- **The incoming glider is near its reflector before the corner is met**: for the image `0`
(at the origin, delay `0`), the glider box at `meetT - 1 = -61` and the reflector box are not far
apart (they overlap in `x` and are `0` apart in `y`). -/
theorem rfIn_near : ¬ (gbx (rfIn 0) (-61)).Far (cornerSpec ⟨0, rfCU 0, rfCV 0, .halt 0⟩).bx := by
  simp only [gbx, cornerSpec, PSpec.bx_mk, BoxT.Far, Base.piece, rfP, rfIn, rfX, rfY, rfCU, rfCV,
    WL.px, WL.py, WL.qt]
  norm_num

/-- **The outgoing glider is near its reflector when the next flight starts**: for the image `0`
(at the origin, delay `0`), the glider box at `meetT + 30 = -30` is only `2` rows from the
reflector box. -/
theorem rfOut_near : ¬ (gbx (rfOut 0) (-30)).Far (cornerSpec ⟨0, rfCU 0, rfCV 0, .halt 0⟩).bx := by
  simp only [gbx, cornerSpec, PSpec.bx_mk, BoxT.Far, Base.piece, rfP, rfOut, rfX, rfY, rfCU, rfCV,
    WL.px, WL.py, WL.qt]
  norm_num

/-! ### Extended relay boxes and the corrected separation condition -/

/-- The extended relay box of image `k` at the origin: the relay box of the image and the glider
boxes (`WL.box`) from `20` generations before the input to `10` generations after the output
(it contains the certified box `Box (-6) 10 (-27) 0` of `rf3_early` for the image `3`). -/
def rxBox : ℕ → BoxT
  | 0 => ⟨0, 28, -7, 10⟩
  | 1 => ⟨-10, 7, 0, 28⟩
  | 2 => ⟨-28, 0, -10, 7⟩
  | 3 => ⟨-7, 10, -28, 0⟩
  | 4 => ⟨-28, 0, -7, 10⟩
  | 5 => ⟨0, 28, -10, 7⟩
  | 6 => ⟨-7, 10, 0, 28⟩
  | _ => ⟨-10, 7, -28, 0⟩

/-- The extended relay box of the corner `c`, as data. -/
def rxB (c : Corner) : BoxT :=
  ⟨(rxBox c.k).a + rfX c.k c.u c.v, (rxBox c.k).b + rfX c.k c.u c.v,
    (rxBox c.k).lo + rfY c.k c.u c.v, (rxBox c.k).hi + rfY c.k c.u c.v⟩

/-- **The extended relay box of the corner `c`**: the place of the extended reflection, from
`20` generations before `meetT` to `40` after. -/
def relayBoxX (c : Corner) : Set Cell := Box (rxB c).a (rxB c).b (rxB c).lo (rxB c).hi

/-- **The corrected separation condition of a route** (corner windows, integer times): before each
corner the flight boxes, up to `20` generations before the corner is met, lie in `Z` and are far
from every piece of `L`; the reflector of the corner is a piece of `L` whose extended relay box
lies in `Z` and is far from every other piece; the next flight starts `40` generations after the
corner is met; the final glider box lies in `Z`. -/
def RouteSepX (L : List Piece) (Z : Set Cell) : WL → List Corner → ℤ → Prop
  | g, [], T => g.box T ⊆ Z
  | g, c :: cs, T =>
      (∀ t : ℤ, T ≤ t → t ≤ meetT g c - 20 → g.box t ⊆ Z) ∧
      (∀ t : ℤ, T ≤ t → t < meetT g c - 20 → ∀ h ∈ L, FarApart 2 (g.box t) h.box) ∧
      relayBoxX c ⊆ Z ∧
      (∃ L' : List Piece, L.Perm ((reflect g c).1.piece :: L') ∧
        ∀ h ∈ L', FarApart 2 (relayBoxX c) h.box) ∧
      RouteSepX L Z (reflect g c).2 cs (meetT g c + 40)

/-! ### Glider centres and the rays of the reflector lines -/

/-- The `u` of the centre of the glider box of `w` at time `t`. -/
def WL.cu (w : WL) (t : ℤ) : ℤ := w.px t - w.py t

/-- The `v` of the centre of the glider box of `w` at time `t`. -/
def WL.cv (w : WL) (t : ℤ) : ℤ := w.px t + w.py t

/-- The `uv`-hull of the glider box is the centre `± 4` in `u` and `-2 … +6` in `v`. -/
theorem gbx_uv (w : WL) (t : ℤ) :
    (gbx w t).InUV (w.cu t - 4) (w.cu t + 4) (w.cv t - 2) (w.cv t + 6) := by
  simp only [BoxT.InUV, gbx, WL.cu, WL.cv]; omega

/-- A point `(cu, cv)` on the ray from `(u, v)` in the direction `d` (`0` NW, `1` NE, `2` SE,
`3` SW), at least `m` from `(u, v)`. -/
def Ray : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → Prop
  | 0, u, v, cu, cv, m => cu = u ∧ cv ≤ v - m
  | 1, u, v, cu, cv, m => cv = v ∧ u + m ≤ cu
  | 2, u, v, cu, cv, m => cu = u ∧ v + m ≤ cv
  | _, u, v, cu, cv, m => cv = v ∧ cu ≤ u - m

/-- The direction of the outgoing glider of image `k`. -/
def outD : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 3 | 6 => 0 | _ => 2

/-- The direction opposite to the incoming glider of image `k` (where it comes from). -/
def behindIn : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 0 | 5 => 2 | 6 => 3 | _ => 1

/-- The parity condition of a corner: the reflector is placed exactly at its corner point. -/
def CPar (c : Corner) : Prop := (c.u - rfCU c.k + c.v - rfCV c.k) % 2 = 0

/-- The outgoing world line of the corner `c` delayed by `s`. -/
def outWL (c : Corner) (s : ℤ) : WL := (rfOut c.k).shift (rfX c.k c.u c.v) (rfY c.k c.u c.v) s

/-- The incoming world line of the corner `c` delayed by `s`. -/
def inWL (c : Corner) (s : ℤ) : WL := (rfIn c.k).shift (rfX c.k c.u c.v) (rfY c.k c.u c.v) s

/-- **The outgoing glider after the corner**: from `26` generations before the end of the
reflection window on (`t ≥ s - 26`, i.e. `meetT + 34`), the centre of the outgoing glider is on
the ray of its direction, at least `13` from the corner point. -/
theorem out_center {k : ℕ} (hk : k < 8) {u v s t : ℤ} (hp : (u - rfCU k + v - rfCV k) % 2 = 0)
    (ht : s - 26 ≤ t) :
    Ray (outD k) u v (((rfOut k).shift (rfX k u v) (rfY k u v) s).cu t)
      (((rfOut k).shift (rfX k u v) (rfY k u v) s).cv t) 13 := by
  interval_cases k <;>
    simp only [Ray, outD, WL.cu, WL.cv, WL.px, WL.py, WL.qt, WL.shift, rfOut, rfX, rfY, rfCU,
      rfCV] at hp ⊢ <;> omega

/-- **The incoming glider before the corner**: up to `76` generations before its delay
(`t ≤ s - 76`, i.e. up to `meetT - 16`), the centre of the incoming glider is on the ray behind
the corner, at least `13` from the corner point. -/
theorem in_center {k : ℕ} (hk : k < 8) {u v s t : ℤ} (hp : (u - rfCU k + v - rfCV k) % 2 = 0)
    (ht : t ≤ s - 76) :
    Ray (behindIn k) u v (((rfIn k).shift (rfX k u v) (rfY k u v) s).cu t)
      (((rfIn k).shift (rfX k u v) (rfY k u v) s).cv t) 13 := by
  interval_cases k <;>
    simp only [Ray, behindIn, WL.cu, WL.cv, WL.px, WL.py, WL.qt, WL.shift, rfIn, rfX, rfY, rfCU,
      rfCV] at hp ⊢ <;> omega

/-- At the start of the next flight (`t = s - 20`, i.e. `meetT + 40`) the outgoing glider is
within `20` of the corner point. -/
theorem out_center_at {k : ℕ} (hk : k < 8) {u v s : ℤ} (hp : (u - rfCU k + v - rfCV k) % 2 = 0) :
    u - 20 ≤ ((rfOut k).shift (rfX k u v) (rfY k u v) s).cu (s - 20) ∧
      ((rfOut k).shift (rfX k u v) (rfY k u v) s).cu (s - 20) ≤ u + 20 ∧
      v - 20 ≤ ((rfOut k).shift (rfX k u v) (rfY k u v) s).cv (s - 20) ∧
      ((rfOut k).shift (rfX k u v) (rfY k u v) s).cv (s - 20) ≤ v + 20 := by
  interval_cases k <;>
    simp only [WL.cu, WL.cv, WL.px, WL.py, WL.qt, WL.shift, rfOut, rfX, rfY, rfCU,
      rfCV] at hp ⊢ <;> omega

/-- **The outgoing glider is far from its own reflector** from `27` generations before its delay
on (`meetT + 33`). -/
theorem out_far {k : ℕ} (hk : k < 8) {u v s t : ℤ} (tag : CTag)
    (hp : (u - rfCU k + v - rfCV k) % 2 = 0) (ht : s - 27 ≤ t) :
    (gbx ((rfOut k).shift (rfX k u v) (rfY k u v) s) t).Far (cornerSpec ⟨k, u, v, tag⟩).bx := by
  interval_cases k <;>
    simp only [gbx, cornerSpec, PSpec.bx_mk, BoxT.Far, Base.piece, rfP, WL.px, WL.py, WL.qt,
      WL.shift, rfOut, rfX, rfY, rfCU, rfCV] at hp ⊢ <;> omega

/-- **The incoming glider is far from its own reflector** up to `73` generations before its delay
(`meetT - 13`). -/
theorem in_far {k : ℕ} (hk : k < 8) {u v s t : ℤ} (tag : CTag)
    (hp : (u - rfCU k + v - rfCV k) % 2 = 0) (ht : t ≤ s - 73) :
    (gbx ((rfIn k).shift (rfX k u v) (rfY k u v) s) t).Far (cornerSpec ⟨k, u, v, tag⟩).bx := by
  interval_cases k <;>
    simp only [gbx, cornerSpec, PSpec.bx_mk, BoxT.Far, Base.piece, rfP, WL.px, WL.py, WL.qt,
      WL.shift, rfIn, rfX, rfY, rfCU, rfCV] at hp ⊢ <;> omega

/-- **The extended relay box of a corner** lies within `29` of the corner point in `u` and in
`[-27, 31]` in `v`. -/
theorem rxB_uv {c : Corner} (hk : c.k < 8) (hp : CPar c) :
    (rxB c).InUV (c.u - 29) (c.u + 29) (c.v - 27) (c.v + 31) := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only [CPar] at hk hp
  simp only [rxB, BoxT.InUV]
  interval_cases k <;> simp only [rxBox, rfX, rfY, rfCU, rfCV] at hp ⊢ <;> omega

/-- The extended relay box contains the box of the reflector. -/
theorem rxB_contains {c : Corner} (hk : c.k < 8) :
    (rxB c).a ≤ (cornerSpec c).bx.a ∧ (cornerSpec c).bx.b ≤ (rxB c).b ∧
      (rxB c).lo ≤ (cornerSpec c).bx.lo ∧ (cornerSpec c).bx.hi ≤ (rxB c).hi := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only at hk
  simp only [rxB, cornerSpec, PSpec.bx_mk]
  interval_cases k <;> simp only [rxBox, Base.piece, rfP] <;> omega

/-! ### Boxes far from a rectangle in `(u, v)` -/

/-- The `uv`-hull of the box `B` is `≥ 6` (in `u` or in `v`) from the rectangle
`[u1, u2] × [v1, v2]`. -/
def FarRect (B : BoxT) (u1 u2 v1 v2 : ℤ) : Prop :=
  B.b - B.lo + 6 ≤ u1 ∨ u2 + 6 ≤ B.a - B.hi ∨ B.b + B.hi + 6 ≤ v1 ∨ v2 + 6 ≤ B.a + B.lo

/-- A box inside a `uv`-hull that is `≥ 6` from a rectangle is far from it. -/
theorem farRect_of_uv {B : BoxT} {a b c d u1 u2 v1 v2 : ℤ} (hB : B.InUV a b c d)
    (h : b + 6 ≤ u1 ∨ u2 + 6 ≤ a ∨ d + 6 ≤ v1 ∨ v2 + 6 ≤ c) : FarRect B u1 u2 v1 v2 := by
  unfold BoxT.InUV at hB; unfold FarRect; omega

/-- **A glider in the rectangle is far from every box far from the rectangle.** -/
theorem far_glider {w : WL} {t : ℤ} {B : BoxT} {u1 u2 v1 v2 : ℤ} (h : FarRect B u1 u2 v1 v2)
    (hr : u1 ≤ w.cu t - 4 ∧ w.cu t + 4 ≤ u2 ∧ v1 ≤ w.cv t - 2 ∧ w.cv t + 6 ≤ v2) :
    FarApart 2 (w.box t) (Box B.a B.b B.lo B.hi) := by
  refine Box.farApart ?_
  unfold FarRect at h
  simp only [WL.cu, WL.cv] at hr
  push_cast
  omega

/-- Far boxes as data are far apart. -/
theorem BoxT.Far.farApart {B C : BoxT} (h : B.Far C) :
    FarApart 2 (Box B.a B.b B.lo B.hi) (Box C.a C.b C.lo C.hi) := by
  refine Box.farApart ?_
  unfold BoxT.Far at h
  push_cast
  omega

/-- The box of a placed piece is the box of its data. -/
theorem PSpec.piece_box (s : PSpec) : s.piece.box = Box s.bx.a s.bx.b s.bx.lo s.bx.hi := rfl

/-! ### The region of the machine -/

/-- A fold of `min` is below every element and below the start. -/
theorem foldr_min_le (l : List PSpec) (f : PSpec → ℤ) :
    ∀ s ∈ l, l.foldr (fun s m => min m (f s)) 0 ≤ f s := by
  induction l with
  | nil => simp
  | cons x l ih =>
    intro s hs
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hs with rfl | hs
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (ih s hs)

/-- `uMin` is below the `u` of every piece. -/
theorem uMin_le {p : Program} {s : PSpec} (hs : s ∈ machSpecs p) : uMin p ≤ s.bx.a - s.bx.hi :=
  foldr_min_le _ (fun s => s.bx.a - s.bx.hi) s hs

/-- Every corner of the machine is the corner of a route reflector of the machine. -/
theorem corner_in_links {p : Program} {c : Corner} (hc : c ∈ allCorners p) :
    ∃ x ∈ linksPart p, x.bx = (cornerSpec c).bx := by
  have : (cornerSpec c).bx ∈ (linksPart p).map PSpec.bx := by
    rw [linksPart_bx]; exact List.mem_map.2 ⟨c, hc, rfl⟩
  obtain ⟨x, hx, h⟩ := List.mem_map.1 this
  exact ⟨x, hx, h⟩

/-- The route reflectors are pieces of the machine. -/
theorem links_mem_mach {p : Program} {x : PSpec} (hx : x ∈ linksPart p) : x ∈ machSpecs p :=
  List.mem_append_right _ hx

/-- The lowest `u` of the box of a reflector is at most `25` right of its corner point. -/
theorem corner_a_hi (c : Corner) : (cornerSpec c).bx.a - (cornerSpec c).bx.hi ≤ c.u + 25 := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only [cornerSpec, PSpec.bx_mk, rfX, rfY]
  match k with
  | 0 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 1 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 2 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 3 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 4 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 5 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 6 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | n + 7 =>
    have h2 : rfCU (n + 7) = 15 := by cases n <;> rfl
    have h3 : rfCV (n + 7) = -24 := by cases n <;> rfl
    simp only [Base.piece, h2, h3, rfP]; omega

/-- `uMin` is at most `25` right of every corner of the machine. -/
theorem corner_uMin {p : Program} {c : Corner} (hc : c ∈ allCorners p) : uMin p ≤ c.u + 25 := by
  obtain ⟨x, hx, hb⟩ := corner_in_links hc
  have h1 := uMin_le (links_mem_mach hx)
  have h2 := corner_a_hi c
  rw [hb] at h1
  omega

/-- **A glider box at most `250` left of a corner of the machine lies in its region.** -/
theorem box_sub_region {p : Program} {w : WL} {t : ℤ} {c : Corner} (hc : c ∈ allCorners p)
    (h : c.u - 250 ≤ w.cu t) : w.box t ⊆ machRegion p := by
  have := corner_uMin hc
  rintro x ⟨x1, -, -, x4⟩
  change uMin p - 300 ≤ x.1 - x.2
  simp only [WL.cu] at h
  omega

/-- **The extended relay box of a corner of the machine lies in its region.** -/
theorem relayX_sub_region {p : Program} {c : Corner} (hc : c ∈ allCorners p) (hk : c.k < 8)
    (hpar : CPar c) : relayBoxX c ⊆ machRegion p := by
  have := corner_uMin hc
  have h := rxB_uv hk hpar
  unfold BoxT.InUV at h
  rintro x ⟨x1, -, -, x4⟩
  change uMin p - 300 ≤ x.1 - x.2
  omega

/-! ### Tags identify corners -/

/-- In a list with pairwise distinct tags, two members with the same tag are equal. -/
theorem eq_of_tag {l : List Corner} (h : l.Pairwise fun c c' => c.tag ≠ c'.tag) {c c' : Corner}
    (hc : c ∈ l) (hc' : c' ∈ l) (ht : c.tag = c'.tag) : c = c' := by
  induction l with
  | nil => simp at hc
  | cons x l ih =>
    rcases List.pairwise_cons.1 h with ⟨h1, h2⟩
    rcases List.mem_cons.1 hc with h3 | h3 <;> rcases List.mem_cons.1 hc' with h4 | h4
    · rw [h3, h4]
    · subst h3; exact absurd ht (h1 _ h4)
    · subst h4; exact absurd ht.symm (h1 _ h3)
    · exact ih h2 h3 h4

/-- The box of a reflector is not empty. -/
theorem cornerSpec_nonempty {c : Corner} (hk : c.k < 8) :
    (cornerSpec c).bx.a ≤ (cornerSpec c).bx.b ∧ (cornerSpec c).bx.lo ≤ (cornerSpec c).bx.hi := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only at hk
  simp only [cornerSpec, PSpec.bx_mk]
  interval_cases k <;> simp only [Base.piece, rfP] <;> omega

/-- A piece whose box is the (nonempty) box of a reflector is not separated from that reflector. -/
theorem not_sep_same {c : Corner} (hk : c.k < 8) {x s : PSpec} (hx : x.bx = (cornerSpec c).bx)
    (hs : s.bx = (cornerSpec c).bx) : ¬ Piece.Sep x.piece s.piece := by
  intro h
  have hn := cornerSpec_nonempty hk
  refine h ((cornerSpec c).bx.a, (cornerSpec c).bx.lo) ?_ ((cornerSpec c).bx.a,
    (cornerSpec c).bx.lo) ?_ ?_
  · rw [PSpec.piece_box, hx]; exact ⟨le_rfl, hn.1, le_rfl, hn.2⟩
  · rw [PSpec.piece_box, hs]; exact ⟨le_rfl, hn.1, le_rfl, hn.2⟩
  · exact ⟨by omega, by omega, by omega, by omega⟩

/-! ### Corners at distinct places are `61` apart -/

/-- The input columns of a unit are `≥ 35` left of its pieces. -/
theorem unitC0_uLo35 (p : Program) (a : ℕ) : unitC0 p a + 35 ≤ (unitKind p a).uLo := by
  unfold unitC0; cases unitKind p a <;> simp [UKind.C0, C0dec, C0inc, C0halt, UKind.uLo]

/-- **Two corners with valid, distinct places are `≥ 61` apart in `u` or in `v`** (the margin of
`R-31` #13; `corner_gap` states `56` / `57`). -/
theorem corner_gap61 (p : Program) {c c' : Corner} (hc : Valid p c) (hc' : Valid p c')
    (hne : c.tag ≠ c'.tag) :
    c.u + 61 ≤ c'.u ∨ c'.u + 61 ≤ c.u ∨ c.v + 61 ≤ c'.v ∨ c'.v + 61 ≤ c.v := by
  obtain ⟨k, u, v, tag⟩ := c
  obtain ⟨k', u', v', tag'⟩ := c'
  have hf := layout_facts p
  simp only at hne ⊢
  cases tag with
  | band b n h =>
    cases tag' with
    | band b' n' h' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.band.injEq, not_and] at hne
      cases h <;> cases h' <;> simp at hne hc hc' <;>
        rcases lt_trichotomy b b' with hb | rfl | hb <;> omega
    | halt a' => simp only [Valid] at hc hc'; omega
    | slab a' t' => simp only [Valid] at hc hc'; omega
    | left r' i' => simp only [Valid] at hc hc'; omega
    | right r' j' w' => simp only [Valid] at hc hc'; omega
  | halt a =>
    cases tag' with
    | band b' n' h' => simp only [Valid] at hc hc'; omega
    | halt a' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.halt.injEq] at hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := A_add_le p h; omega
      · have := A_add_le p h; omega
    | slab a' t' => simp only [Valid] at hc hc'; omega
    | left r' i' => simp only [Valid] at hc hc'; omega
    | right r' j' w' => simp only [Valid] at hc hc'; omega
  | slab a t =>
    cases tag' with
    | band b' n' h' => simp only [Valid] at hc hc'; omega
    | halt a' => simp only [Valid] at hc hc'; omega
    | slab a' t' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.slab.injEq, not_and] at hne
      have h1 := unitC0_cases p a.toNat
      have h2 := unitC0_cases p a'.toNat
      rcases lt_trichotomy a a' with h | rfl | h
      · have := A_add_le p h; omega
      · omega
      · have := A_add_le p h; omega
    | left r' i' => simp only [Valid] at hc hc'; omega
    | right r' j' w' => simp only [Valid] at hc hc'; omega
  | left r i =>
    cases tag' with
    | band b' n' h' => simp only [Valid] at hc hc'; omega
    | halt a' => simp only [Valid] at hc hc'; omega
    | slab a' t' => simp only [Valid] at hc hc'; omega
    | left r' i' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.left.injEq, not_and] at hne
      rcases lt_trichotomy r r' with h | rfl | h
      · have := U_add_le p h; omega
      · omega
      · have := U_add_le p h; omega
    | right r' j' w' =>
      simp only [Valid] at hc hc'
      rcases lt_trichotomy r r' with h | rfl | h
      · have := U_add_le p h; omega
      · omega
      · have := U_add_le p h; omega
  | right r j w =>
    cases tag' with
    | band b' n' h' => simp only [Valid] at hc hc'; omega
    | halt a' => simp only [Valid] at hc hc'; omega
    | slab a' t' => simp only [Valid] at hc hc'; omega
    | left r' i' =>
      simp only [Valid] at hc hc'
      rcases lt_trichotomy r r' with h | rfl | h
      · have := U_add_le p h; omega
      · omega
      · have := U_add_le p h; omega
    | right r' j' w' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.right.injEq, not_and] at hne
      rcases lt_trichotomy r r' with h | rfl | h
      · have := U_add_le p h; omega
      · omega
      · have := U_add_le p h; omega

/-! ### The extended relay box of a corner is far from every other piece -/

/-- **The extended relay box of a corner with a valid place is far from every piece of every
unit.** -/
theorem rx_unit_far (p : Program) {c : Corner} (hc : Valid p c) (hk : c.k < 8) (hpar : CPar c)
    {a : ℕ} {s : PSpec} (hs : s ∈ unitSpecs p a) : (rxB c).Far s.bx := by
  have h1 := rxB_uv hk hpar
  have h2 := unitSpecs_uv p a hs
  have hf := layout_facts p
  have hk' : -180 ≤ (unitKind p a).uLo := by cases unitKind p a <;> simp [UKind.uLo]
  refine BoxT.far_of_uv h1 h2 ?_
  obtain ⟨k, u, v, tag⟩ := c
  simp only at h1 ⊢
  cases tag with
  | band b n h => simp only [Valid] at hc; omega
  | halt a' => simp only [Valid] at hc; omega
  | slab a' t =>
    simp only [Valid] at hc
    have hc0 := unitC0_cases p a'.toNat
    rcases lt_trichotomy a' a with h | h | h
    · have := A_add_le p h; omega
    · have h' : a'.toNat = a := by omega
      have := unitC0_uLo35 p a
      rw [h'] at hc; subst h; omega
    · have := A_add_le p h; omega
  | left r idx => simp only [Valid] at hc; omega
  | right r j w => simp only [Valid] at hc; omega

/-- **The extended relay box of a corner with a valid place is far from every piece of every
module.** -/
theorem rx_module_far (p : Program) {c : Corner} (hc : Valid p c) (hk : c.k < 8) (hpar : CPar c)
    {r : ℕ} {s : PSpec} (hs : s ∈ moduleSpecs p r) : (rxB c).Far s.bx := by
  have h1 := rxB_uv hk hpar
  obtain ⟨h2, h2'⟩ := moduleSpecs_uv p r hs
  have hf := layout_facts p
  unfold BoxT.Far
  obtain ⟨k, u, v, tag⟩ := c
  unfold BoxT.InUV at h1 h2
  simp only at h1 ⊢
  cases tag with
  | band b n h => simp only [Valid] at hc; omega
  | halt a' => simp only [Valid] at hc; omega
  | slab a' t => simp only [Valid] at hc; omega
  | left r' idx =>
    simp only [Valid] at hc
    rcases lt_trichotomy r' r with h | rfl | h
    · have := U_add_le p h; omega
    · omega
    · have := U_add_le p h; omega
  | right r' j w =>
    simp only [Valid] at hc
    rcases lt_trichotomy r' r with h | rfl | h
    · have := U_add_le p h; omega
    · obtain ⟨_, _, _, _, hw⟩ := hc
      rcases hw with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;>
        rcases h2' with h2' | h2' <;> omega
    · have := U_add_le p h; omega

/-- **The extended relay box of a corner is far from the reflector of every corner at a distinct
valid place.** -/
theorem rx_corner_far (p : Program) {c c' : Corner} (hc : Valid p c) (hc' : Valid p c')
    (hne : c.tag ≠ c'.tag) (hk : c.k < 8) (hpar : CPar c) : (rxB c).Far (cornerSpec c').bx :=
  BoxT.far_of_uv (rxB_uv hk hpar) (corner_uv c') (by have := corner_gap61 p hc hc' hne; omega)

/-- Membership in the pieces of the machine: a unit piece, a module piece or a route reflector. -/
theorem mem_machSpecs {p : Program} {s : PSpec} (hs : s ∈ machSpecs p) :
    (∃ a < p.length + numRegs p, s ∈ unitSpecs p a) ∨ (∃ r < numRegs p, s ∈ moduleSpecs p r) ∨
      ∃ c ∈ allCorners p, s.bx = (cornerSpec c).bx := by
  unfold machSpecs at hs
  rcases List.mem_append.1 hs with hs | hs
  · rcases List.mem_append.1 hs with hs | hs
    · exact Or.inl (mem_unitsPart hs)
    · exact Or.inr (Or.inl (mem_modulesPart hs))
  · exact Or.inr (Or.inr (mem_linksPart hs))

/-- **The reflection condition of `RouteSepX`**: for a corner of the machine whose reflector is
the piece `x` of the machine, the pieces of the machine are `x` and a list of pieces each far
from the extended relay box of the corner. -/
theorem relay_ok {p : Program} (hp : p.WellFormed) {c : Corner} (hc : c ∈ allCorners p)
    (hk : c.k < 8) (hpar : CPar c) {x : PSpec} (hx : x ∈ machSpecs p)
    (hxb : x.bx = (cornerSpec c).bx) :
    ∃ L' : List Piece, (machPieces p).Perm (x.piece :: L') ∧
      ∀ h ∈ L', FarApart 2 (relayBoxX c) h.box := by
  have hmem : x.piece ∈ machPieces p := List.mem_map_of_mem hx
  obtain ⟨l1, l2, heq⟩ := List.append_of_mem hmem
  refine ⟨l1 ++ l2, heq ▸ List.perm_middle, fun h hh => ?_⟩
  have hpw := machPieces_sep p hp
  rw [heq] at hpw
  have hsep : Piece.Sep x.piece h := by
    rcases List.mem_append.1 hh with hh | hh
    · exact Piece.Sep.symm' ((List.pairwise_append.1 hpw).2.2 h hh x.piece List.mem_cons_self)
    · exact (List.pairwise_cons.1 (List.pairwise_append.1 hpw).2.1).1 h hh
  have hhm : h ∈ machPieces p := by
    rw [heq]; rcases List.mem_append.1 hh with hh | hh
    · exact List.mem_append_left _ hh
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hh)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hhm
  have hv := allCorners_valid hp c hc
  rw [PSpec.piece_box]
  refine BoxT.Far.farApart ?_
  rcases mem_machSpecs hs with ⟨a, -, hs⟩ | ⟨r, -, hs⟩ | ⟨c', hc', hb'⟩
  · exact rx_unit_far p hv hk hpar hs
  · exact rx_module_far p hv hk hpar hs
  · by_cases ht : c.tag = c'.tag
    · have := eq_of_tag (allCorners_tags hp) hc hc' ht
      subst this
      exact absurd hsep (not_sep_same hk hxb hb')
    · rw [hb']
      exact rx_corner_far p hv (allCorners_valid hp c' hc') ht hk hpar

/-! ### Flights far from the machine -/

/-- **A flight far from every piece of the machine**: at time `t` the glider box lies in the
rectangle `[u1, u2] × [v1, v2]`; it is far from the reflectors of the corners of `E` (the ends of
the flight); every unit piece, module piece and reflector of a corner at a place other than those
of `E` is far from the rectangle. -/
theorem flight_far {p : Program} (hp : p.WellFormed) {w : WL} {t u1 u2 v1 v2 : ℤ}
    (E : List Corner) (hE : ∀ c ∈ E, c ∈ allCorners p)
    (hown : ∀ c ∈ E, (gbx w t).Far (cornerSpec c).bx)
    (hr : u1 ≤ w.cu t - 4 ∧ w.cu t + 4 ≤ u2 ∧ v1 ≤ w.cv t - 2 ∧ w.cv t + 6 ≤ v2)
    (hU : ∀ a s, a < p.length + numRegs p → s ∈ unitSpecs p a → FarRect s.bx u1 u2 v1 v2)
    (hM : ∀ r s, r < numRegs p → s ∈ moduleSpecs p r → FarRect s.bx u1 u2 v1 v2)
    (hC : ∀ c' ∈ allCorners p, (∀ c ∈ E, c'.tag ≠ c.tag) →
      FarRect (cornerSpec c').bx u1 u2 v1 v2) :
    ∀ h ∈ machPieces p, FarApart 2 (w.box t) h.box := by
  intro h hh
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  rw [PSpec.piece_box]
  rcases mem_machSpecs hs with ⟨a, ha, hs⟩ | ⟨r, hr', hs⟩ | ⟨c', hc', hb'⟩
  · exact far_glider (hU a s ha hs) hr
  · exact far_glider (hM r s hr' hs) hr
  · by_cases hx : ∃ c ∈ E, c'.tag = c.tag
    · obtain ⟨c, hcE, ht⟩ := hx
      have := eq_of_tag (allCorners_tags hp) hc' (hE c hcE) ht
      subst this
      rw [hb', box_gbx]
      exact (hown _ hcE).farApart
    · push Not at hx
      rw [hb']
      exact far_glider (hC c' hc' hx) hr

/-! ### Routes from legs -/

/-- A corner of a route of the machine: a corner of the machine, of an image `k < 8`, with the
parity of its image. -/
def CornerOK (p : Program) (c : Corner) : Prop := c ∈ allCorners p ∧ c.k < 8 ∧ CPar c

/-- **A leg of a route is separated**: whatever the delays, a glider leaving the corner `c1` that
arrives on the input line of `c2` is, from `34` generations after it met `c1` to `16`
generations before it meets `c2`, inside the region of the machine and far from every piece. -/
def LegOK (p : Program) (c1 c2 : Corner) : Prop :=
  ∀ s1 s2 : ℤ, outWL c1 s1 = inWL c2 s2 → ∀ t : ℤ, s1 - 26 ≤ t → t ≤ s2 - 76 →
    (outWL c1 s1).box t ⊆ machRegion p ∧
      ∀ h ∈ machPieces p, FarApart 2 ((outWL c1 s1).box t) h.box

/-- The corners of a route are corners of the machine and its consecutive legs are separated. -/
def ChainOK (p : Program) : List Corner → Prop
  | [] => True
  | [c] => CornerOK p c
  | c1 :: c2 :: cs => CornerOK p c1 ∧ LegOK p c1 c2 ∧ ChainOK p (c2 :: cs)

/-- The first flight of a route, from time `T` to `16` generations before the first corner: in
the region of the machine and far from every piece. -/
def StartOK (p : Program) (g : WL) (c : Corner) (T : ℤ) : Prop :=
  ∀ t : ℤ, T ≤ t → t ≤ meetT g c - 16 →
    g.box t ⊆ machRegion p ∧ ∀ h ∈ machPieces p, FarApart 2 (g.box t) h.box

/-- A glider met on the input line of a corner is the incoming world line of the corner. -/
theorem inWL_of_onLine {g : WL} {c : Corner} (h : OnLine g c) : g = inWL c (delayS g c) := h

/-- The outgoing glider of a corner is the outgoing world line of the corner. -/
theorem reflect_snd (g : WL) (c : Corner) : (reflect g c).2 = outWL c (delayS g c) := rfl

/-- The reflector of a route corner has the box of the corner. -/
theorem reflect_bx (g : WL) (c : Corner) : (reflect g c).1.bx = (cornerSpec c).bx := rfl

/-- **`RouteSepX` from the legs**: a route whose corners are met on their input lines, whose
first flight is separated from time `T` on, whose consecutive legs are separated and whose
reflectors are pieces of the machine, satisfies `RouteSepX` in the region of the machine. -/
theorem routeSepX_of {p : Program} (hp : p.WellFormed) :
    ∀ (cs : List Corner) (g : WL) (T : ℤ), cs ≠ [] → RouteLines g cs →
      (∀ c ∈ cs.head?, StartOK p g c T) → ChainOK p cs →
      (∀ x ∈ (route g cs).1, x ∈ machSpecs p) →
      RouteSepX (machPieces p) (machRegion p) g cs T
  | [], _, _, h, _, _, _, _ => absurd rfl h
  | c :: cs, g, T, _, ⟨hl, hls⟩, hs, hch, hmem => by
    have hst := hs c rfl
    have hcok : CornerOK p c := by
      cases cs with
      | nil => exact hch
      | cons _ _ => exact hch.1
    obtain ⟨hc, hk, hpar⟩ := hcok
    have hx : (reflect g c).1 ∈ machSpecs p := hmem _ List.mem_cons_self
    refine ⟨fun t h1 h2 => (hst t h1 (by omega)).1, fun t h1 h2 => (hst t h1 (by omega)).2,
      relayX_sub_region hc hk hpar, relay_ok hp hc hk hpar hx (reflect_bx g c), ?_⟩
    cases cs with
    | nil =>
      change (reflect g c).2.box (meetT g c + 40) ⊆ machRegion p
      refine box_sub_region hc ?_
      obtain ⟨k, u, v, tag⟩ := c
      have h := out_center_at hk hpar (s := delayS g ⟨k, u, v, tag⟩)
      rw [reflect_snd, outWL, show meetT g ⟨k, u, v, tag⟩ + 40 = delayS g ⟨k, u, v, tag⟩ - 20 by
        unfold meetT; ring]
      exact le_trans (by omega) h.1
    | cons c2 cs' =>
      obtain ⟨-, hleg, hch'⟩ := hch
      refine routeSepX_of hp (c2 :: cs') _ _ (List.cons_ne_nil _ _) hls ?_ hch' ?_
      · intro c' hc'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
        subst hc'
        intro t h1 h2
        have hw := inWL_of_onLine hls.1
        rw [reflect_snd] at hw ⊢
        rw [reflect_snd] at h2
        exact hleg _ _ hw t (by unfold meetT at h1; omega) (by unfold meetT at h2; omega)
      · intro x hx'
        exact hmem x (List.mem_cons_of_mem _ hx')

/-- A delayed glider is met on the input line of a corner if the glider is. -/
theorem onLine_delay {g : WL} {c : Corner} (h : OnLine g c) (d : ℤ) : OnLine (g.shift 0 0 d) c := by
  unfold OnLine at h ⊢
  have hs : delayS (g.shift 0 0 d) c = delayS g c + d := by
    simp only [delayS, WL.shift]; ring
  rw [hs]
  conv_lhs => rw [h]
  simp only [WL.shift]
  congr 1 <;> ring

/-- The outgoing glider of a delayed glider is delayed alike (any delay). -/
theorem reflect_delay_snd (g : WL) (c : Corner) (d : ℤ) :
    (reflect (g.shift 0 0 d) c).2 = (reflect g c).2.shift 0 0 d := by
  simp only [reflect, WL.shift, mul_zero, sub_zero, add_zero, WL.mk.injEq, true_and]
  ring

/-- **The lines of a route are kept by any delay.** -/
theorem routeLines_delay (d : ℤ) : ∀ (cs : List Corner) (g : WL), RouteLines g cs →
    RouteLines (g.shift 0 0 d) cs
  | [], _, _ => trivial
  | c :: cs, g, ⟨h1, h2⟩ => by
    refine ⟨onLine_delay h1 d, ?_⟩
    rw [reflect_delay_snd]
    exact routeLines_delay d cs _ h2

/-- The reflectors of a delayed route (delay `≡ 0 (mod 30)`) are those of the route. -/
theorem route_delay_fst {d : ℤ} (hd : d % 30 = 0) (g : WL) (cs : List Corner) :
    (route (g.shift 0 0 d) cs).1 = (route g cs).1 := by
  rw [route_delay d hd]

/-- **A leg from its rectangle**: if every glider centre on the rays of the two corners (`13`
after `c1`, `13` before `c2`) lies, with its box, in the rectangle `[u1, u2] × [v1, v2]` (and at
most `250` left of one of the corners), and every unit piece, module piece and reflector of a
corner at another place is far from the rectangle, the leg is separated. -/
theorem legOK_of {p : Program} (hp : p.WellFormed) {c1 c2 : Corner} (h1 : CornerOK p c1)
    (h2 : CornerOK p c2) {u1 u2 v1 v2 : ℤ}
    (hrect : ∀ cu cv : ℤ, Ray (outD c1.k) c1.u c1.v cu cv 13 →
      Ray (behindIn c2.k) c2.u c2.v cu cv 13 →
      u1 ≤ cu - 4 ∧ cu + 4 ≤ u2 ∧ v1 ≤ cv - 2 ∧ cv + 6 ≤ v2 ∧
        (c1.u - 250 ≤ cu ∨ c2.u - 250 ≤ cu))
    (hU : ∀ a s, a < p.length + numRegs p → s ∈ unitSpecs p a → FarRect s.bx u1 u2 v1 v2)
    (hM : ∀ r s, r < numRegs p → s ∈ moduleSpecs p r → FarRect s.bx u1 u2 v1 v2)
    (hC : ∀ c' ∈ allCorners p, c'.tag ≠ c1.tag → c'.tag ≠ c2.tag →
      FarRect (cornerSpec c').bx u1 u2 v1 v2) : LegOK p c1 c2 := by
  intro s1 s2 hw t ht1 ht2
  obtain ⟨hc1, hk1, hp1⟩ := h1
  obtain ⟨hc2, hk2, hp2⟩ := h2
  have ho := out_center hk1 hp1 (s := s1) ht1
  have hi := in_center hk2 hp2 (s := s2) ht2
  have hof := out_far hk1 c1.tag hp1 (s := s1) (t := t) (by omega)
  have hif := in_far hk2 c2.tag hp2 (s := s2) (t := t) (by omega)
  change Ray _ _ _ ((outWL c1 s1).cu t) ((outWL c1 s1).cv t) 13 at ho
  change Ray _ _ _ ((inWL c2 s2).cu t) ((inWL c2 s2).cv t) 13 at hi
  change (gbx (outWL c1 s1) t).Far (cornerSpec c1).bx at hof
  change (gbx (inWL c2 s2) t).Far (cornerSpec c2).bx at hif
  rw [← hw] at hi hif
  obtain ⟨r1, r2, r3, r4, r5⟩ := hrect _ _ ho hi
  refine ⟨?_, flight_far hp [c1, c2] ?_ ?_ ⟨r1, r2, r3, r4⟩ hU hM ?_⟩
  · rcases r5 with r5 | r5
    · exact box_sub_region hc1 r5
    · exact box_sub_region hc2 r5
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption
  · intro c' hc' hne
    exact hC c' hc' (hne c1 List.mem_cons_self)
      (hne c2 (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The first flight from its rectangle**: as `legOK_of`, for the flight of the glider `g` from
time `T` to `16` generations before it meets the first corner `c`. -/
theorem startOK_of {p : Program} (hp : p.WellFormed) {g : WL} {c : Corner} {T : ℤ}
    (h2 : CornerOK p c) (hl : OnLine g c) {u1 u2 v1 v2 : ℤ}
    (hrect : ∀ t : ℤ, T ≤ t → t ≤ meetT g c - 16 →
      Ray (behindIn c.k) c.u c.v (g.cu t) (g.cv t) 13 →
      u1 ≤ g.cu t - 4 ∧ g.cu t + 4 ≤ u2 ∧ v1 ≤ g.cv t - 2 ∧ g.cv t + 6 ≤ v2 ∧
        c.u - 250 ≤ g.cu t)
    (hU : ∀ a s, a < p.length + numRegs p → s ∈ unitSpecs p a → FarRect s.bx u1 u2 v1 v2)
    (hM : ∀ r s, r < numRegs p → s ∈ moduleSpecs p r → FarRect s.bx u1 u2 v1 v2)
    (hC : ∀ c' ∈ allCorners p, c'.tag ≠ c.tag → FarRect (cornerSpec c').bx u1 u2 v1 v2) :
    StartOK p g c T := by
  intro t ht1 ht2
  obtain ⟨hc, hk, hpar⟩ := h2
  have hw := inWL_of_onLine hl
  have ht2' : t ≤ delayS g c - 76 := by unfold meetT at ht2; omega
  have hi := in_center hk hpar (s := delayS g c) ht2'
  have hif := in_far hk c.tag hpar (s := delayS g c) (t := t) (by omega)
  change Ray _ _ _ ((inWL c (delayS g c)).cu t) ((inWL c (delayS g c)).cv t) 13 at hi
  change (gbx (inWL c (delayS g c)) t).Far (cornerSpec c).bx at hif
  rw [← hw] at hi hif
  obtain ⟨r1, r2, r3, r4, r5⟩ := hrect t ht1 ht2 hi
  refine ⟨box_sub_region hc r5, flight_far hp [c] ?_ ?_ ⟨r1, r2, r3, r4⟩ hU hM ?_⟩
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rw [hc']; exact hc
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rw [hc']; exact hif
  · intro c' hc' hne
    exact hC c' hc' (hne c List.mem_cons_self)

/-- A reflector far from a rectangle: the corner point `≥ 31` (in `u`) or `≥ 30` / `33` (in `v`)
from it. -/
theorem corner_farRect {c : Corner} {u1 u2 v1 v2 : ℤ}
    (h : c.u + 31 ≤ u1 ∨ u2 + 31 ≤ c.u ∨ c.v + 33 ≤ v1 ∨ v2 + 30 ≤ c.v) :
    FarRect (cornerSpec c).bx u1 u2 v1 v2 :=
  farRect_of_uv (corner_uv c) (by omega)

/-! ### Routes of the machine -/

/-- The reflectors of a route of instruction `i` are pieces of the machine. -/
theorem instrRoute_mem {p : Program} {i : ℕ} (hi : i < p.length) {x : WL × List Corner}
    (hx : x ∈ instrSpecs p i) : ∀ s ∈ (route x.1 x.2).1, s ∈ machSpecs p := by
  intro s hs
  refine links_mem_mach (List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩))
  exact List.mem_flatMap.2 ⟨x, hx, hs⟩

/-- The corners of a route of instruction `i` are corners of the machine. -/
theorem instrRoute_corner {p : Program} {i : ℕ} (hi : i < p.length) {x : WL × List Corner}
    (hx : x ∈ instrSpecs p i) : ∀ c ∈ x.2, c ∈ allCorners p := by
  intro c hc
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
    List.mem_flatMap.2 ⟨x, hx, hc⟩⟩)

/-- The reflectors of the merge route of a register with an `inc` are pieces of the machine. -/
theorem mergeRoute_mem {p : Program} {r : ℕ} (hr : r < numRegs p) (hu : mergeUsed p r = true)
    {x : WL × List Corner} (hx : x ∈ mergeSpecs p r) :
    ∀ s ∈ (route x.1 x.2).1, s ∈ machSpecs p := by
  intro s hs
  refine links_mem_mach (List.mem_append_right _ (List.mem_flatMap.2 ⟨r, ?_, ?_⟩))
  · exact List.mem_filter.2 ⟨List.mem_range.2 hr, hu⟩
  · exact List.mem_flatMap.2 ⟨x, hx, hs⟩

/-- The corners of the merge route of a register with an `inc` are corners of the machine. -/
theorem mergeRoute_corner {p : Program} {r : ℕ} (hr : r < numRegs p) (hu : mergeUsed p r = true)
    {x : WL × List Corner} (hx : x ∈ mergeSpecs p r) : ∀ c ∈ x.2, c ∈ allCorners p := by
  intro c hc
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨r, List.mem_filter.2
    ⟨List.mem_range.2 hr, hu⟩, List.mem_flatMap.2 ⟨x, hx, hc⟩⟩)

/-- The reflectors of a delayed route of the machine are pieces of the machine. -/
theorem route_mem_delay {p : Program} {g : WL} {cs : List Corner}
    (h : ∀ s ∈ (route g cs).1, s ∈ machSpecs p) {d : ℤ} (hd : d % 30 = 0) :
    ∀ s ∈ (route (g.shift 0 0 d) cs).1, s ∈ machSpecs p := by
  rw [route_delay_fst hd]; exact h

end LP

end LeanTheory.Life
