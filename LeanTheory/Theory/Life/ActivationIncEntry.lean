/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncModule
public import LeanTheory.Theory.Life.MergeSide
public import LeanTheory.Theory.Life.Gen.ActSide
public import LeanTheory.Theory.Life.OrChainTight

/-!
# Entering a unit: the side input, the entry chain and the flight to the body

Item (c) of the `inc` activation (research note `N-22`). A link arrives on the side line of entry
copy `t` of unit `a` (`destWin p a t`) at window offset `δ ∈ {4, 5}` (the window rule of
`R-31`, `solveE`), i.e. on the world line `(destWin p a t).shift 0 0 (δ + 30 k)`:

* `side_arrival`: at time `180 + 30 k + (16 t mod 30)` the glider is the side input `orSide6`
  (`δ = 4`) or `orSide7` (`δ = 5`, `Gen/ActSide`) of copy `t`, and copy `t` is at phase `0`;
* `entryRelay`: the copies `t, …, 0` carry it (side input, then through relays) to the output of
  copy `0`, in `134 + 254 t` generations (`orChainSide6T/7T`, `orGate_side6T/7T`), inside the
  copies of the **tight footprint** `orFoot` of the relays (`OrChainTight`; the crude box
  `Box 0 90 (-6) 60` meets the reflector of the input corner of copy `0` of a merge or halt
  unit);
* `chainSpecs_piecesAt`: the copies `0 … t` of the layout (`chainSpecs`, phases `14 u`) at time
  `T` with `T + 14 t ≡ m (mod 30)` are the chain `relayChain` of the certificates at phase `m`;
* `entry_reaction`: everything together in unit `a`, from the arriving glider to the output of
  the chain, with the copies of the layout as the start and the end;
* `orOut_flight`: the output of copy `0` flies to the body input `bodyIn` in `166` generations;
  the whole entry lasts `300 + 254 t ≡ 0 (mod 30)` generations from a time `≡ 16 t (mod 30)`, so the
  control reaches `ctrlAt p a` at a time `≡ 0 (mod 30)`, as `InvM` requires;
* `window_group`: a window with a group of active pieces (several concurrent processes are first
  combined by `Reaction.par`), the rest of the machine idle.

**Discrepancy with `R-31`.** The window rule puts arrivals at offsets `4, 5` of `sideWL`; the side
certificates of `MergeSide` (`orSide5`, `orSide6`, `orSide9`) are at offsets `3, 4, 7`; offset `5`
needed the new certificate `orGate_side7` (`scripts/life_cert/act_side.py`). (A simulation shows
the gate accepts every offset `0 … 12` with the same output.)
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The side input of an entry copy -/

/-- The side line of copy `0` of an entry chain (template frame). -/
def sideBase : WL := ⟨1, -1, -76, 1⟩

/-- The side line of copy `t` is the side line of copy `0` moved to copy `t`
(`(-35 t, -64 t)`), delayed by `16 t mod 30`. -/
theorem sideWL_eq (t : ℤ) : sideWL t = sideBase.shift (-35 * t) (-64 * t) (16 * t % 30) := by
  simp only [sideWL, sideBase, WL.shift, WL.mk.injEq, true_and]
  constructor <;> ring

/-- The side input at window offset `δ`: `orSide6` (offset `4`) or `orSide7` (offset `5`). -/
def sideIn (δ : ℤ) : Finset Cell := if δ = 4 then orSide6 else orSide7

/-- The side inputs are the gliders of the side line at offsets `4` and `5`, at time `180`. -/
theorem sideIn_cells {δ : ℤ} (hδ : δ = 4 ∨ δ = 5) :
    sideIn δ = sideBase.cells (180 - δ) := by
  rcases hδ with rfl | rfl <;> rfl

/-- **The arriving glider is the side input of copy `t`**: on the side line of copy `t` of unit
`a` at offset `δ ∈ {4, 5}` (and `k` whole periods), at time `180 + 30 k + (16 t mod 30)`. -/
theorem side_arrival (p : Program) (a : ℕ) (t δ k : ℤ) (hδ : δ = 4 ∨ δ = 5) :
    ((destWin p a t).shift 0 0 (δ + 30 * k)).cells (180 + 30 * k + 16 * t % 30) =
      translate (unitDX p a - 35 * t, unitDY p a - 64 * t) (sideIn δ) := by
  have hd : sideBase.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  rw [destWin, unitWL, sideWL_eq]
  rw [WL.shift_cells (show WL.Dir (((sideBase.shift (-35 * t) (-64 * t) (16 * t % 30)).shift
      (unitDX p a) (unitDY p a) 0)) from hd),
    WL.shift_cells (show WL.Dir ((sideBase.shift (-35 * t) (-64 * t) (16 * t % 30))) from hd),
    WL.shift_cells hd, sideIn_cells hδ, translate_translate, translate_translate]
  congr 1
  · ext <;> simp <;> ring
  · congr 1
    ring

/-! ### The entry chain -/

/-- The chain vector of the entry chains. -/
abbrev chainV : Cell := (35, 64)

/-- **The entry chain from the side input of copy `t` to the output of copy `0`**, in
`134 + 254 t` generations (copy `t` is the first copy of the certificate chain). -/
theorem entryRelay (t : ℕ) {S : Finset Cell} (hS : S = orSide6 ∨ S = orSide7) :
    Reaction (relayChain orGate 254 chainV (t + 1) 0 ∪ S)
      (relayChain orGate 254 chainV (t + 1) (134 + t * 254) ∪
        translate (((t + 1 : ℕ) : ℤ) * 35, ((t + 1 : ℕ) : ℤ) * 64) orIn)
      (134 + t * 254) (fun _ => chainFoot orFoot chainV (t + 1)) := by
  rcases t with _ | L
  · have h : Reaction (orGate ∪ S) (phase orGate 134 ∪ translate (35, 64) orIn) 134
        (fun _ => orFoot) := by
      rcases hS with rfl | rfl
      · exact orGate_side6T
      · exact orGate_side7T
    rw [relayChain_one, relayChain_one, phase, Nat.zero_mod, Rule.evolve_zero]
    simp only [zero_mul, add_zero, zero_add, Nat.cast_one, one_mul]
    exact h.mono fun _ _ => box_subset_chainFoot (by omega)
  · have h : Reaction (relayChain orGate 254 (35, 64) (L + 2) 0 ∪ S)
        (phase orGate (134 + (L + 1) * 254) ∪ translate (35, 64) (relayChain orGate 254 (35, 64)
          (L + 1) ((L + 1) * 254) ∪ translate (((L + 1 : ℕ) : ℤ) * (35, 64).1,
            ((L + 1 : ℕ) : ℤ) * (35, 64).2) orIn))
        (134 + (L + 1) * 254) (fun _ => chainFoot orFoot (35, 64) (L + 2)) := by
      rcases hS with rfl | rfl
      · exact orChainSide6T L
      · exact orChainSide7T L
    rw [show L + 1 + 1 = L + 2 by ring,
      relayChain_succ orGate 254 chainV (L + 1) (134 + (L + 1) * 254),
      show 134 + (L + 1) * 254 + 29 * 254 = (L + 1) * 254 + 30 * 250 by ring,
      relayChain_add_thirty]
    rw [translate_union, translate_translate] at h
    rw [union_assoc, show ((((L + 2 : ℕ) : ℤ) * 35, ((L + 2 : ℕ) : ℤ) * 64) : Cell) =
      (35, 64) + (((L + 1 : ℕ) : ℤ) * (35, 64).1, ((L + 1 : ℕ) : ℤ) * (35, 64).2) by
        ext <;> simp <;> ring]
    exact h

/-- Two phases of a piece that agree modulo `30` are equal. -/
theorem phase_congr (G : Finset Cell) {a b : ℕ} (h : a % 30 = b % 30) : phase G a = phase G b := by
  rw [phase, phase, h]

/-- The placed OR gate (`Base.orGate`) at time `T`. -/
theorem orGate_placed_at (dx dy : ℤ) (ph T : ℕ) :
    conway.evolve (T % 30) (PSpec.piece ⟨.orGate, dx, dy, ph⟩).rest =
      translate (dx, dy) (phase orGate (ph + T)) := by
  simp only [PSpec.piece, Base.piece, Piece.place, orGateP]
  rw [Rule.evolve_translate, evolve_phase orGate_rest.evolve_eq]
  congr 1
  apply phase_congr
  omega

/-- **The copies `0 … t` of an entry chain at time `T`** are the certificate chain started at copy
`t`, at phase `m`, whenever `T + 14 t ≡ m (mod 30)`. -/
theorem chainSpecs_piecesAt (t : ℕ) (dx dy : ℤ) (T m : ℕ) (hm : (T + 14 * t) % 30 = m % 30) :
    piecesAt ((chainSpecs (t + 1) dx dy).map PSpec.piece) T =
      translate (dx - 35 * t, dy - 64 * t) (relayChain orGate 254 chainV (t + 1) m) := by
  ext c
  rw [mem_piecesAt, mem_translate]
  simp only [chainSpecs, List.map_map, List.mem_map, List.mem_range, Function.comp,
    relayChain, mem_biUnion, Finset.mem_range, mem_translate]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, hc⟩
    rw [orGate_placed_at, mem_translate] at hc
    refine ⟨t - u, by omega, ?_⟩
    rw [phase_congr orGate (b := 14 * u % 30 + T) (by omega)]
    convert hc using 1
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;>
      push_cast [Nat.cast_sub (show u ≤ t by omega)] <;> ring
  · rintro ⟨j, hj, hc⟩
    refine ⟨_, ⟨t - j, by omega, rfl⟩, ?_⟩
    rw [orGate_placed_at, mem_translate]
    rw [phase_congr orGate (b := 14 * (t - j) % 30 + T) (by omega)] at hc
    convert hc using 1
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;>
      push_cast [Nat.cast_sub (show j ≤ t by omega)] <;> ring

/-- **The entry of unit `a` at copy `t`, with the copies of the layout**: the copies `0 … t` of
the entry chain of unit `a` at time `T0 = 180 + 30 k + (16 t mod 30)` and the glider arriving on
the side line of copy `t` at offset `δ ∈ {4, 5}` become, `134 + 254 t` generations later, the
copies at their later phases and the output glider of copy `0`. -/
theorem entry_reaction (p : Program) (a t : ℕ) {δ : ℤ} (hδ : δ = 4 ∨ δ = 5) (k : ℤ) (T0 : ℕ)
    (hT0 : (T0 : ℤ) = 180 + 30 * k + 16 * (t : ℤ) % 30) :
    Reaction
      (piecesAt ((chainSpecs (t + 1) (unitDX p a) (unitDY p a)).map PSpec.piece) T0 ∪
        ((destWin p a t).shift 0 0 (δ + 30 * k)).cells T0)
      (piecesAt ((chainSpecs (t + 1) (unitDX p a) (unitDY p a)).map PSpec.piece)
          (T0 + (134 + t * 254)) ∪ translate (unitDX p a + 35, unitDY p a + 64) orIn)
      (134 + t * 254)
      (fun _ => (fun c => (unitDX p a - 35 * t, unitDY p a - 64 * t) + c) ''
        chainFoot orFoot chainV (t + 1)) := by
  rw [chainSpecs_piecesAt t _ _ T0 0 (by omega),
    chainSpecs_piecesAt t _ _ (T0 + (134 + t * 254)) (134 + t * 254) (by omega), hT0,
    side_arrival p a t δ k hδ, ← translate_union]
  have hS : sideIn δ = orSide6 ∨ sideIn δ = orSide7 := by
    unfold sideIn; split_ifs <;> simp
  have h := (entryRelay t hS).translate (unitDX p a - 35 * t, unitDY p a - 64 * t)
  rw [show (unitDX p a + 35, unitDY p a + 64) = (unitDX p a - 35 * (t : ℤ),
      unitDY p a - 64 * (t : ℤ)) + (((t + 1 : ℕ) : ℤ) * 35, ((t + 1 : ℕ) : ℤ) * 64) by
    ext <;> simp <;> ring, ← translate_translate, ← translate_union]
  exact h

/-- The world line of the output of an entry chain (template frame): the body input `bodyIn` at
time `0`. -/
def chainOutWL : WL := ⟨1, 1, 14, -451⟩

/-- **The output of copy `0` flies to the body input**, in `166` generations (template frame). -/
theorem orOut_flight :
    Reaction (translate (35, 64) orIn) bodyIn 166 (fun i => chainOutWL.box (-166 + i)) := by
  have hd : chainOutWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have h := WL.flight hd (-166) 166
  have e1 : translate (35, 64) orIn = chainOutWL.cells (-166) := by
    rw [orIn, translate_ofRows]
    rfl
  have e2 : chainOutWL.cells ((-166 : ℤ) + ((166 : ℕ) : ℤ)) = bodyIn := rfl
  rw [e2] at h
  rw [e1]
  exact h

/-- **The output of copy `0` of unit `a` flies to the entrance `ctrlAt p a`**, in `166`
generations. -/
theorem orOut_flight_unit (p : Program) (a : ℕ) :
    Reaction (translate (unitDX p a + 35, unitDY p a + 64) orIn) (ctrlAt p a) 166
      (fun i => (fun c => (unitDX p a, unitDY p a) + c) '' chainOutWL.box (-166 + i)) := by
  have h := orOut_flight.translate (unitDX p a, unitDY p a)
  rw [translate_translate] at h
  exact h

/-- The whole entry takes a multiple of `30` generations from the arrival time: the control
reaches the body input at a time `≡ 0 (mod 30)`. -/
theorem entry_time (t : ℕ) (k : ℤ) (T0 : ℕ) (hT0 : (T0 : ℤ) = 180 + 30 * k + 16 * (t : ℤ) % 30) :
    (T0 + (134 + t * 254) + 166) % 30 = 0 := by
  omega

/-! ### Windows with a group of active pieces -/

/-- The pieces of a concatenation at phase `T`. -/
theorem piecesAt_append (A B : List Piece) (T : ℕ) :
    piecesAt (A ++ B) T = piecesAt A T ∪ piecesAt B T := by
  ext c
  simp only [mem_piecesAt, List.mem_append, mem_union]
  constructor
  · rintro ⟨g, hg | hg, hc⟩
    · exact Or.inl ⟨g, hg, hc⟩
    · exact Or.inr ⟨g, hg, hc⟩
  · rintro (⟨g, hg, hc⟩ | ⟨g, hg, hc⟩)
    · exact ⟨g, Or.inl hg, hc⟩
    · exact ⟨g, Or.inr hg, hc⟩

/-- **A window with a group of active pieces**: if the pieces `A` of the list (up to order, the
list is `A ++ L'`) take part in a reaction whose footprint stays far from every other piece, the
rest of the list idles beside it. Several concurrent processes are combined first by
`Reaction.par`. -/
theorem window_group {L A L' : List Piece} (hperm : L.Perm (A ++ L')) (hL : L.Pairwise Piece.Sep)
    (T n : ℕ) {X Y : Finset Cell} {F : ℕ → Set Cell}
    (h : Reaction (piecesAt A T ∪ X) (piecesAt A (T + n) ∪ Y) n F)
    (hfar : ∀ i < n, ∀ g ∈ L', FarApart 2 (F i) g.box) :
    Reaction (piecesAt L T ∪ X) (piecesAt L (T + n) ∪ Y) n (fun i => boxesOf L ∪ F i) := by
  have hL' : L'.Pairwise Piece.Sep :=
    (List.pairwise_append.1 ((hperm.pairwise_iff fun h => Piece.Sep.symm' h).1 hL)).2.1
  have hw := window hL' T n h hfar
  rw [piecesAt_perm hperm, piecesAt_perm hperm, piecesAt_append, piecesAt_append]
  rw [show piecesAt A T ∪ piecesAt L' T ∪ X = piecesAt L' T ∪ (piecesAt A T ∪ X) by ac_rfl,
    show piecesAt A (T + n) ∪ piecesAt L' (T + n) ∪ Y =
      piecesAt L' (T + n) ∪ (piecesAt A (T + n) ∪ Y) by ac_rfl]
  refine hw.mono fun i _ => Set.union_subset_union (boxesOf_subset fun x hx => ?_) le_rfl
  exact hperm.mem_iff.2 (List.mem_append_right _ hx)

end LP

end LeanTheory.Life
