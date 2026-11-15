/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncMerge
public import LeanTheory.Theory.Life.ActivationIncLinks

/-!
# Composition tools for the activations

Generic tools for item (h) of the `inc` activation (research note `N-22`): composing the
activation inside the whole machine with **time-resolved footprints**, so that concurrent
processes (the continue and the INC link, which cross in space but not in time) can be run side
by side with `Reaction.par`.

* `piecesAt_mod`: the pieces at phase `T` depend on `T mod 30` only;
* `window_mem`: a window whose active pieces are given by **membership** (no permutation of the
  list needed); the rest of the list idles;
* `dd`: a list of pieces without repetitions (same members), pairwise separated when its members
  are pieces of a separated list (`dd_pairwise`);
* `routeFoot`, `RouteSepM`, `route_window_foot`: a glider following a route through a list of
  idle pieces, with the **exact** box of the glider (or the relay box of the corner being used) as
  footprint at every generation, under a membership form of the separation conditions;
  `RouteSep.toM`: the separation conditions of `RouteSep` (stated for the whole machine) give
  `RouteSepM` for every sublist containing the reflectors of the route;
  `RouteSep.foot_subset`: the footprint stays in the set `Z` of `RouteSep`;
* `regsOn`, `stripsOn`, `regsOn_reaction`: the diagonals of a list of registers idling side by side.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Pieces -/

/-- The pieces at phase `T` depend only on `T mod 30`. -/
theorem piecesAt_mod (L : List Piece) {a b : ℕ} (h : a % 30 = b % 30) :
    piecesAt L a = piecesAt L b := by
  unfold piecesAt
  rw [h]

/-- The pieces of a one-element list. -/
theorem piecesAt_single (g : Piece) (T : ℕ) :
    piecesAt [g] T = conway.evolve (T % 30) g.rest := by
  simp [piecesAt]

/-- **A window with the active pieces given by membership**: if the pieces `A` (all of them
pieces of `L`) take part in a reaction whose footprint stays far from every other piece of `L`,
the rest of `L` idles beside it. -/
theorem window_mem {L A : List Piece} (hL : L.Pairwise Piece.Sep) (hA : ∀ g ∈ A, g ∈ L)
    (T n : ℕ) {X Y : Finset Cell} {F : ℕ → Set Cell}
    (h : Reaction (piecesAt A T ∪ X) (piecesAt A (T + n) ∪ Y) n F)
    (hfar : ∀ i < n, ∀ g ∈ L, g ∉ A → FarApart 2 (F i) g.box) :
    Reaction (piecesAt L T ∪ X) (piecesAt L (T + n) ∪ Y) n (fun i => boxesOf L ∪ F i) := by
  classical
  have hL' : (L.filter fun g => g ∉ A).Pairwise Piece.Sep := hL.filter _
  have hsplit : ∀ t, piecesAt L t = piecesAt (L.filter fun g => g ∉ A) t ∪ piecesAt A t := by
    intro t
    ext c
    simp only [mem_union, mem_piecesAt, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨g, hg, hc⟩
      by_cases hgA : g ∈ A
      · exact Or.inr ⟨g, hgA, hc⟩
      · exact Or.inl ⟨g, ⟨hg, hgA⟩, hc⟩
    · rintro (⟨g, ⟨hg, -⟩, hc⟩ | ⟨g, hg, hc⟩)
      · exact ⟨g, hg, hc⟩
      · exact ⟨g, hA g hg, hc⟩
  have hw := window hL' T n h fun i hi g hg => by
    rw [List.mem_filter, decide_eq_true_eq] at hg
    exact hfar i hi g hg.1 hg.2
  rw [hsplit, hsplit, union_assoc, union_assoc]
  refine hw.mono fun i _ => Set.union_subset_union (boxesOf_subset fun x hx => ?_) le_rfl
  exact (List.mem_filter.1 hx).1

/-- The list without repetitions (same members). -/
noncomputable def dd (A : List Piece) : List Piece := by
  classical
  exact A.dedup

/-- Members of `dd A` are the members of `A`. -/
theorem mem_dd {A : List Piece} {g : Piece} : g ∈ dd A ↔ g ∈ A := by
  classical
  unfold dd
  convert List.mem_dedup

/-- The pieces of `dd A` are the pieces of `A`. -/
theorem piecesAt_dd (A : List Piece) (T : ℕ) : piecesAt (dd A) T = piecesAt A T := by
  ext c
  simp only [mem_piecesAt, mem_dd]

/-- The boxes of `dd A` are the boxes of `A`. -/
theorem boxesOf_dd (A : List Piece) : boxesOf (dd A) = boxesOf A := by
  ext c
  simp only [mem_boxesOf, mem_dd]

/-- `dd A` has no repetitions. -/
theorem dd_nodup (A : List Piece) : (dd A).Nodup := by
  classical
  unfold dd
  convert List.nodup_dedup A

/-- **A list without repetitions of pieces of a separated list is separated.** -/
theorem pairwise_of_nodup {L A : List Piece} (hL : L.Pairwise Piece.Sep) (hnd : A.Nodup)
    (hA : ∀ g ∈ A, g ∈ L) : A.Pairwise Piece.Sep := by
  obtain ⟨l, hp, hs⟩ := hnd.subperm hA
  exact (hp.pairwise_iff fun h => Piece.Sep.symm' h).1 (hL.sublist hs)

/-- `dd A` is separated when the members of `A` are pieces of a separated list. -/
theorem dd_pairwise {L A : List Piece} (hL : L.Pairwise Piece.Sep) (hA : ∀ g ∈ A, g ∈ L) :
    (dd A).Pairwise Piece.Sep :=
  pairwise_of_nodup hL (dd_nodup A) fun g hg => hA g (mem_dd.1 hg)

/-! ### Routes with exact footprints -/

/-- **The footprint of a route** from time `T`, at generation `i`: the box of the glider while it
flies to a corner, the relay box of the corner during the reflection, then the footprint of the
rest of the route. -/
def routeFoot : WL → List Corner → ℕ → ℕ → Set Cell
  | g, [], T, i => g.box ((T : ℤ) + i)
  | g, c :: cs, T, i =>
    if (T : ℤ) + i ≤ meetT g c then g.box ((T : ℤ) + i)
    else if (T : ℤ) + i ≤ meetT g c + 30 then relayBox c
    else routeFoot (reflect g c).2 cs ((meetT g c).toNat + 30) (T + i - ((meetT g c).toNat + 30))

/-- **The separation conditions of a route, by membership**: before each corner the glider is
far from every piece of `L`; the reflector of the corner is a piece of `L` and its relay box is
far from every other piece of `L`. -/
def RouteSepM (L : List Piece) : WL → List Corner → ℕ → Prop
  | _, [], _ => True
  | g, c :: cs, T =>
      (∀ i : ℕ, (T : ℤ) + i < meetT g c → ∀ h ∈ L, FarApart 2 (g.box (T + i)) h.box) ∧
      (reflect g c).1.piece ∈ L ∧
      (∀ h ∈ L, h ≠ (reflect g c).1.piece → FarApart 2 (relayBox c) h.box) ∧
      RouteSepM L (reflect g c).2 cs ((meetT g c).toNat + 30)

/-- A reflection with a single active piece, in the form of `window_mem`. -/
theorem reflect_reaction_single {g : WL} {c : Corner} (hl : OnLine g c) (T : ℕ)
    (hT : (T : ℤ) = meetT g c) :
    Reaction (piecesAt [(reflect g c).1.piece] T ∪ g.cells T)
      (piecesAt [(reflect g c).1.piece] (T + 30) ∪ (reflect g c).2.cells ((T + 30 : ℕ) : ℤ)) 30
      (fun _ => relayBox c) := by
  rw [piecesAt_single, piecesAt_single]
  have h := reflect_reaction hl T hT
  push_cast
  exact h

/-- **A glider follows a route through a list of idle pieces, with exact footprints**: the
pieces and the glider of `g` at time `T` become the pieces and the glider of the final world line
at the end of the route; at every generation the pattern lies in the boxes of the pieces and the
footprint `routeFoot` of the route. -/
theorem route_window_foot {L : List Piece} (hL : L.Pairwise Piece.Sep) :
    ∀ (cs : List Corner) (g : WL) (T : ℕ), g.Dir → RouteLines g cs → RouteTimed g cs T →
      RouteSepM L g cs T → T ≤ routeEnd g cs T ∧
      Reaction (piecesAt L T ∪ g.cells T)
        (piecesAt L (routeEnd g cs T) ∪ (route g cs).2.cells (routeEnd g cs T))
        (routeEnd g cs T - T) (fun i => boxesOf L ∪ routeFoot g cs T i)
  | [], g, T, hd, _, _, _ => by
    refine ⟨le_rfl, ?_⟩
    have h := window hL T 0 (WL.flight hd T 0) fun i hi => absurd hi (Nat.not_lt_zero i)
    simp only [route, routeEnd, Nat.sub_self, Nat.cast_zero, add_zero] at h ⊢
    refine h.mono fun i hi => Set.union_subset_union le_rfl ?_
    rw [show i = 0 by omega]
    simp [routeFoot]
  | c :: cs, g, T, hd, ⟨hl, hls⟩, ⟨ht, hts⟩, ⟨hfl, hmem, hfar, hrest⟩ => by
    set m := (meetT g c).toNat with hm
    have hmT : ((m : ℕ) : ℤ) = meetT g c := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hTm : T ≤ m := by omega
    have hts' : RouteTimed (reflect g c).2 cs (m + 30) := by
      rw [hmT]
      exact hts
    obtain ⟨hend, hr⟩ := route_window_foot hL cs _ _ (reflect_dir g c) hls hts' hrest
    have h1 := window hL T (m - T) (WL.flight hd T (m - T)) fun i hi =>
      hfl i (by omega)
    rw [show T + (m - T) = m by omega,
      show (T : ℤ) + ((m - T : ℕ) : ℤ) = (m : ℤ) by push_cast [Nat.cast_sub hTm]; ring] at h1
    have h2 := window_mem hL (A := [(reflect g c).1.piece]) (fun x hx => by
        rw [List.mem_singleton] at hx; exact hx ▸ hmem) m 30
      (reflect_reaction_single hl m hmT) fun i _ h hh hne =>
        hfar h hh (by simpa using hne)
    have h123 := (h1.seq h2).seq hr
    simp only [routeEnd, route] at hend ⊢
    rw [← hm]
    refine ⟨by omega, ?_⟩
    rw [show routeEnd (reflect g c).2 cs (m + 30) - T =
      m - T + 30 + (routeEnd (reflect g c).2 cs (m + 30) - (m + 30)) by omega]
    refine h123.mono fun i _ => ?_
    simp only [routeFoot, ← hmT, Int.toNat_natCast]
    by_cases ha : i ≤ m - T
    · have h' : (T : ℤ) + i ≤ m := by omega
      simp only [show i ≤ m - T + 30 by omega, ha, h', ↓reduceIte]
      exact le_rfl
    · by_cases hb : i ≤ m - T + 30
      · have h' : ¬ ((T : ℤ) + i ≤ m) := by omega
        have h'' : (T : ℤ) + i ≤ m + 30 := by omega
        simp only [hb, ha, h', h'', ↓reduceIte]
        exact le_rfl
      · have h' : ¬ ((T : ℤ) + i ≤ m) := by omega
        have h'' : ¬ ((T : ℤ) + i ≤ m + 30) := by omega
        simp only [hb, h', h'', ↓reduceIte]
        rw [show i - (m - T + 30) = T + i - (m + 30) by omega]

/-- **`RouteSep` (whole machine) gives `RouteSepM` for every sublist containing the
reflectors of the route.** -/
theorem RouteSep.toM {M L : List Piece} {Z : Set Cell} (hLM : ∀ h ∈ L, h ∈ M) :
    ∀ (cs : List Corner) (g : WL) (T : ℕ), (∀ x ∈ (route g cs).1, x.piece ∈ L) →
      RouteSep M Z g cs T → RouteSepM L g cs T
  | [], _, _, _, _ => trivial
  | c :: cs, g, T, hrf, ⟨_, s2, _, ⟨L', hperm, hfar⟩, s5⟩ => by
    refine ⟨fun i hi h hh => s2 i hi h (hLM h hh), hrf _ (by simp [route]), ?_,
      RouteSep.toM hLM cs _ _ (fun x hx => hrf x (by simp [route, hx])) s5⟩
    intro h hh hne
    have := hperm.mem_iff.1 (hLM h hh)
    rcases List.mem_cons.1 this with he | he
    · exact absurd he hne
    · exact hfar h he

/-- **The footprint of a route stays in the set `Z` of `RouteSep`** during the route. -/
theorem RouteSep.foot_subset {M : List Piece} {Z : Set Cell} :
    ∀ (cs : List Corner) (g : WL) (T : ℕ), RouteTimed g cs T → RouteSep M Z g cs T →
      ∀ i, T + i ≤ routeEnd g cs T → routeFoot g cs T i ⊆ Z
  | [], g, T, _, hs, i, hi => by
    simp only [routeEnd] at hi
    rw [show i = 0 by omega]
    have hs' : g.box T ⊆ Z := hs
    simpa [routeFoot] using hs'
  | c :: cs, g, T, ⟨ht, hts⟩, ⟨s1, _, s3, _, s5⟩, i, hi => by
    set m := (meetT g c).toNat with hm
    have hmT : ((m : ℕ) : ℤ) = meetT g c := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hts' : RouteTimed (reflect g c).2 cs (m + 30) := by
      rw [hmT]
      exact hts
    simp only [routeFoot, routeEnd] at hi ⊢
    rw [← hm] at hi ⊢
    rw [← hmT]
    by_cases ha : (T : ℤ) + i ≤ m
    · simp only [ha, ↓reduceIte]
      exact s1 i (by rw [← hmT]; exact ha)
    · by_cases hb : (T : ℤ) + i ≤ m + 30
      · simp only [ha, hb, ↓reduceIte]
        exact s3
      · simp only [ha, hb, ↓reduceIte]
        refine RouteSep.foot_subset cs _ _ hts' s5 _ ?_
        have := hi
        simp only [hm] at this ⊢
        omega

/-! ### Registers -/

/-- The diagonals of the registers of a list. -/
def regsOn (p : Program) (reg : ℕ → RegS) (l : List ℕ) : Finset Cell :=
  l.foldr (fun r S => regAt p r (reg r) ∪ S) ∅

/-- The strips of the diagonals of the registers of a list, `i` generations later. -/
def stripsOn (p : Program) (reg : ℕ → RegS) (l : List ℕ) (i : ℕ) : Set Cell :=
  l.foldr (fun r S => regStrip p r (reg r) (i + (reg r).m) ∪ S) ∅

/-- The diagonals of the registers `0 … n - 1` are those of the list `range n`. -/
theorem regsAt_eq (p : Program) (reg : ℕ → RegS) (n : ℕ) :
    regsAt p reg n = regsOn p reg (List.range n) := rfl

/-- Membership in the strips of a list of registers. -/
theorem mem_stripsOn {p : Program} {reg : ℕ → RegS} {l : List ℕ} {i : ℕ} {c : Cell} :
    c ∈ stripsOn p reg l i ↔ ∃ r ∈ l, c ∈ regStrip p r (reg r) (i + (reg r).m) := by
  induction l with
  | nil => simp [stripsOn]
  | cons r l ih =>
    simp only [stripsOn, List.foldr_cons, Set.mem_union] at ih ⊢
    rw [ih]
    simp

/-- Membership in the diagonals of a list of registers. -/
theorem mem_regsOn {p : Program} {reg : ℕ → RegS} {l : List ℕ} {c : Cell} :
    c ∈ regsOn p reg l ↔ ∃ r ∈ l, c ∈ regAt p r (reg r) := by
  induction l with
  | nil => simp [regsOn]
  | cons r l ih =>
    simp only [regsOn, List.foldr_cons, mem_union] at ih ⊢
    rw [ih]
    simp

/-- The diagonals of a list depend only on the registers of the list. -/
theorem regsOn_congr {p : Program} {reg reg' : ℕ → RegS} {l : List ℕ}
    (h : ∀ r ∈ l, reg r = reg' r) : regsOn p reg l = regsOn p reg' l := by
  ext c
  simp only [mem_regsOn]
  constructor
  · rintro ⟨r, hr, hc⟩
    exact ⟨r, hr, h r hr ▸ hc⟩
  · rintro ⟨r, hr, hc⟩
    exact ⟨r, hr, (h r hr).symm ▸ hc⟩

/-- The registers `0 … n - 1` split into register `r` and the others. -/
theorem regsOn_split (p : Program) (reg : ℕ → RegS) {n r : ℕ} (hr : r < n) :
    regsOn p reg (List.range n) =
      regAt p r (reg r) ∪ regsOn p reg ((List.range n).filter (fun r' => r' ≠ r)) := by
  ext c
  simp only [mem_union, mem_regsOn, List.mem_filter, List.mem_range, ne_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨r', hr', hc⟩
    by_cases he : r' = r
    · exact Or.inl (he ▸ hc)
    · exact Or.inr ⟨r', ⟨hr', he⟩, hc⟩
  · rintro (hc | ⟨r', ⟨hr', -⟩, hc⟩)
    · exact ⟨r, hr, hc⟩
    · exact ⟨r', hr', hc⟩

/-- **The diagonals of a list of distinct registers idle side by side**, when their strips stay
far apart. -/
theorem regsOn_reaction (p : Program) (reg : ℕ → RegS) (n : ℕ) :
    ∀ (l : List ℕ), l.Nodup → (∀ r ∈ l, (reg r).Inv) →
      (∀ i < n, ∀ r ∈ l, ∀ r' ∈ l, r ≠ r' →
        FarApart 2 (regStrip p r (reg r) (i + (reg r).m))
          (regStrip p r' (reg r') (i + (reg r').m))) →
      Reaction (regsOn p reg l) (regsOn p (fun r => (reg r).later n) l) n (stripsOn p reg l)
  | [], _, _, _ => by
    refine ⟨by simp [regsOn], fun i _ => ?_⟩
    simp [regsOn, stripsOn]
  | r :: l, hnd, hinv, hsep => by
    have hnd' := List.nodup_cons.1 hnd
    have ih := regsOn_reaction p reg n l hnd'.2 (fun r' hr' => hinv r' (List.mem_cons_of_mem _ hr'))
      fun i hi r1 h1 r2 h2 hne =>
        hsep i hi r1 (List.mem_cons_of_mem _ h1) r2 (List.mem_cons_of_mem _ h2) hne
    have h := (regAt_reaction p r (hinv r List.mem_cons_self) n).par ih fun i hi => by
      intro a ha b hb
      obtain ⟨r', hr', hb⟩ := mem_stripsOn.1 hb
      exact hsep i hi r List.mem_cons_self r' (List.mem_cons_of_mem _ hr')
        (fun he => hnd'.1 (he ▸ hr')) a ha b hb
    exact h

end LP

end LeanTheory.Life
