/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncReg

/-!
# A link into an entry chain, with exact footprints

Item (h) of the `inc` activation (research note `N-22`): the generic piece shared by the continue
(to unit `i + 1`) and the INC link (to the merge unit `N + r`):

* `upLink_end`: the time at which a glider leaves the last corner of an up-going link, in terms of
  its final world line;
* `entryFoot`: the footprint of the entry chain of unit `a` from copy `t`;
* `linkFoot`, `link_entry`: a glider follows a route (exact footprint `routeFoot`), flies on its
  final world line to the side input of copy `t` of unit `a`, and the copies `t, …, 0` carry it to
  the output of copy `0`; the pieces of a list `L` (containing the copies) idle beside it.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- **The end of a route**: the glider leaves the last corner `c` at the time given by the final
world line and the corner. -/
theorem routeEnd_snoc : ∀ (cs : List Corner) (c : Corner) (g : WL) (T : ℕ),
    RouteTimed g (cs ++ [c]) T →
    (routeEnd g (cs ++ [c]) T : ℤ) = (route g (cs ++ [c])).2.tau - (rfOut c.k).tau +
      4 * (rfOut c.k).dx * rfX c.k c.u c.v - 30
  | [], c, g, T, ⟨h, _⟩ => by
    simp only [List.nil_append, routeEnd, route]
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
    simp only [meetT, delayS, reflect, WL.shift]
    ring
  | c' :: cs, c, g, T, ⟨h, hs⟩ => by
    simp only [List.cons_append, routeEnd, route]
    refine routeEnd_snoc cs c _ _ ?_
    rw [show (((meetT g c').toNat + 30 : ℕ) : ℤ) = meetT g c' + 30 by
      push_cast; rw [Int.toNat_of_nonneg (by omega)]]
    exact hs

/-- **The end of an up-going link**: the glider leaves the last corner (the input corner of the
entry copy) at time `tau' + 37 + 2 (u + v + 9) - 30`, where `tau'` is the reference time of the
final world line and `(u, v)` the corner. -/
theorem upLink_end (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) (g : WL) (T : ℕ)
    (ht : RouteTimed g (upCorners p b s c H a t) T) (hv : (destU p a t + destV p t) % 2 = 1) :
    (routeEnd g (upCorners p b s c H a t) T : ℤ) =
      (route g (upCorners p b s c H a t)).2.tau + 37 + 2 * (destU p a t + destV p t + 9) - 30 := by
  have h := routeEnd_snoc (bandCorners p b s c H (destU p a t) 3 6)
    ⟨1, destU p a t, destV p t, .slab a t⟩ g T ht
  simp only [upCorners, upCornersK]
  rw [h]
  simp only [rfOut, rfX, rfCU, rfCV]
  omega

/-- The footprint of the entry chain of unit `a` from copy `t` (`entry_reaction`). -/
def entryFoot (p : Program) (a t : ℕ) : Set Cell :=
  (fun c => (unitDX p a - 35 * t, unitDY p a - 64 * t) + c) ''
    chainFoot (Box 0 90 (-6) 60) chainV (t + 1)

/-- The pieces of the copies `0 … t` of the entry chain of unit `a`. -/
def chainPieces (p : Program) (a t : ℕ) : List Piece :=
  (chainSpecs (t + 1) (unitDX p a) (unitDY p a)).map PSpec.piece

/-- **The footprint of a link into an entry chain**: the route, then the flight on the final world
line until the arrival time `T0`, then the entry chain. -/
def linkFoot (p : Program) (a t : ℕ) (g : WL) (cs : List Corner) (T T0 j : ℕ) : Set Cell :=
  if T + j ≤ routeEnd g cs T then routeFoot g cs T j
  else if T + j ≤ T0 then (route g cs).2.box ((T : ℤ) + j) else entryFoot p a t

/-- **A link into an entry chain**: the glider of `g` at time `T` follows the corners `cs`,
arrives on the side line of copy `t` of unit `a` at offset `δ ∈ {4, 5}` (time `T0`), and the
entry chain carries it to the output of copy `0`, `134 + 254 t` generations later; the pieces of
`L` idle beside it, and the footprint is `linkFoot`. -/
theorem link_entry (p : Program) {L : List Piece} (hL : L.Pairwise Piece.Sep) (a t : ℕ)
    {g : WL} {cs : List Corner} {T : ℕ} (hd : g.Dir) (hlines : RouteLines g cs)
    (htim : RouteTimed g cs T) (hsep : RouteSepM L g cs T) {δ k : ℤ} (hδ : δ = 4 ∨ δ = 5)
    (hfin : (route g cs).2 = (destWin p a t).shift 0 0 (δ + 30 * k)) {T0 : ℕ}
    (hT0 : (T0 : ℤ) = 180 + 30 * k + 16 * (t : ℤ) % 30) (hle : routeEnd g cs T ≤ T0)
    (hchain : ∀ x ∈ chainPieces p a t, x ∈ L)
    (hfly : ∀ j : ℕ, routeEnd g cs T ≤ j → j < T0 → ∀ h ∈ L,
      FarApart 2 ((route g cs).2.box j) h.box)
    (hent : ∀ h ∈ L, h ∉ chainPieces p a t → FarApart 2 (entryFoot p a t) h.box) :
    T ≤ T0 ∧ Reaction (piecesAt L T ∪ g.cells T)
      (piecesAt L (T0 + (134 + t * 254)) ∪ translate (unitDX p a + 35, unitDY p a + 64) orIn)
      (T0 + (134 + t * 254) - T) (fun j => boxesOf L ∪ linkFoot p a t g cs T T0 j) := by
  obtain ⟨hTe, h1⟩ := route_window_foot hL cs g T hd hlines htim hsep
  set e := routeEnd g cs T with he
  have hdf : (route g cs).2.Dir := by
    rw [hfin]
    exact ⟨Or.inl rfl, Or.inr rfl⟩
  have h2 := window hL e (T0 - e) (WL.flight hdf e (T0 - e)) fun j hj h hh =>
    hfly (e + j) (by omega) (by omega) h hh |> fun x => by
      rw [show ((e : ℤ) + (j : ℤ)) = ((e + j : ℕ) : ℤ) by push_cast; ring]; exact x
  rw [show e + (T0 - e) = T0 by omega,
    show (e : ℤ) + ((T0 - e : ℕ) : ℤ) = (T0 : ℤ) by push_cast [Nat.cast_sub hle]; ring] at h2
  have h3 := window_mem hL hchain T0 (134 + t * 254) (entry_reaction p a t hδ k T0 hT0) fun j _ h hh
    hne => hent h hh hne
  rw [hfin] at h1 h2
  have h123 := (h1.seq h2).seq h3
  refine ⟨by omega, ?_⟩
  rw [show T0 + (134 + t * 254) - T = e - T + (T0 - e) + (134 + t * 254) by omega]
  refine h123.mono fun j _ => ?_
  simp only [linkFoot, ← he]
  by_cases ha : j ≤ e - T
  · simp only [show j ≤ e - T + (T0 - e) by omega, ha, show T + j ≤ e by omega, ↓reduceIte]
    exact le_rfl
  · by_cases hb : j ≤ e - T + (T0 - e)
    · simp only [hb, ha, show ¬ T + j ≤ e by omega, show T + j ≤ T0 by omega, ↓reduceIte]
      rw [hfin, show (e : ℤ) + ((j - (e - T) : ℕ) : ℤ) = (T : ℤ) + j by
        push_cast [Nat.cast_sub hTe, Nat.cast_sub (show e - T ≤ j by omega)]; ring]
    · simp only [hb, show ¬ T + j ≤ e by omega, show ¬ T + j ≤ T0 by omega, ↓reduceIte]
      exact le_rfl

end LP

end LeanTheory.Life
