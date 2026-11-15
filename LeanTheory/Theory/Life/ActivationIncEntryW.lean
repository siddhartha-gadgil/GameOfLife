/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncCompose
public import LeanTheory.Theory.Life.Gen.SideEarly

/-!
# Entering a unit with a side window

Research note `N-22`. The glider arriving on the side line of an OR gate comes within distance `2`
of the box of the gate in the last `10`-`11` generations before the side-input time `T0`
(`ActivationIncSepFalse.isep_side_near`), so the flight to an entry copy cannot be run beside
the idle gate up to `T0`. As for the route corners (`reflect_earlyX`), the gate and the glider are
run **together** from `T0 - 16` (the certificates `orGate_side6E`, `orGate_side7E` of
`Gen/SideEarly`, inside `Box 0 90 0 38`, which lies in the tight relay footprint `orFoot` and in
the gate box `Box 0 90 0 60`):

* `sideInE`, `side_approach`: the side input `16` generations early and its approach to the gate;
* `side_arrivalE`: the glider on the window of copy `t` at time `164 + 30 k + (16 t mod 30)`
  (`16` generations before `side_arrival`) is the early side input of copy `t`;
* `entryRelayW`: the chain (copy `t` at phase `14`) and the early side input become the output
  of copy `0`, in `16 + 134 + 254 t` generations, inside `chainFoot orFoot` (the other copies
  idle during the approach);
* `entry_reactionW`: the same with the copies of the layout of unit `a`, from `Ts = T0 - 16`;
  the footprint is the entry footprint of `entry_reaction` (it does not grow).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- The side input at window offset `δ`, `16` generations early: `orSide6E` (offset `4`) or
`orSide7E` (offset `5`). -/
def sideInE (δ : ℤ) : Finset Cell := if δ = 4 then orSide6E else orSide7E

/-- The early side inputs are the gliders of the side line at offsets `4` and `5`, at time
`164`. -/
theorem sideInE_cells {δ : ℤ} (hδ : δ = 4 ∨ δ = 5) :
    sideInE δ = sideBase.cells (164 - δ) := by
  rcases hδ with rfl | rfl <;> rfl

/-- Sanity: the early side input at offset `4` is `orSide6E`. -/
theorem sideInE_four : sideInE 4 = orSide6E := rfl

/-- Sanity: the early side input at offset `5` is `orSide7E`. -/
theorem sideInE_five : sideInE 5 = orSide7E := rfl

/-- **The approach of the side input** (`orGate_side6E`, `orGate_side7E`): the gate at phase `14`
and the early side input become the gate at phase `0` and the side input, in `16` generations,
inside `Box 0 90 0 38`. -/
theorem side_approach {δ : ℤ} (hδ : δ = 4 ∨ δ = 5) :
    Reaction (phase orGate 14 ∪ sideInE δ) (orGate ∪ sideIn δ) 16 (fun _ => Box 0 90 0 38) := by
  rcases hδ with rfl | rfl
  · exact orGate_side6E
  · exact orGate_side7E

/-- **The arriving glider is the early side input of copy `t`**: on the side line of copy `t` of
unit `a` at offset `δ ∈ {4, 5}`, at time `164 + 30 k + (16 t mod 30)`, `16` generations before
`side_arrival`. -/
theorem side_arrivalE (p : Program) (a : ℕ) (t δ k : ℤ) (hδ : δ = 4 ∨ δ = 5) :
    ((destWin p a t).shift 0 0 (δ + 30 * k)).cells (164 + 30 * k + 16 * t % 30) =
      translate (unitDX p a - 35 * t, unitDY p a - 64 * t) (sideInE δ) := by
  have hd : sideBase.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  rw [destWin, unitWL, sideWL_eq]
  rw [WL.shift_cells (show WL.Dir (((sideBase.shift (-35 * t) (-64 * t) (16 * t % 30)).shift
      (unitDX p a) (unitDY p a) 0)) from hd),
    WL.shift_cells (show WL.Dir ((sideBase.shift (-35 * t) (-64 * t) (16 * t % 30))) from hd),
    WL.shift_cells hd, sideInE_cells hδ, translate_translate, translate_translate]
  congr 1
  · ext <;> simp <;> ring
  · congr 1
    ring

/-- **The entry chain from the early side input of copy `t` to the output of copy `0`**: the
approach (copy `t`, the other copies idle) and then `entryRelay`, in `16 + 134 + 254 t`
generations, inside the tight chain footprint. -/
theorem entryRelayW (t : ℕ) {δ : ℤ} (hδ : δ = 4 ∨ δ = 5) :
    Reaction (relayChain orGate 254 chainV (t + 1) 14 ∪ sideInE δ)
      (relayChain orGate 254 chainV (t + 1) (134 + t * 254) ∪
        translate (((t + 1 : ℕ) : ℤ) * 35, ((t + 1 : ℕ) : ℤ) * 64) orIn)
      (16 + (134 + t * 254)) (fun _ => chainFoot orFoot chainV (t + 1)) := by
  have hrows := farApart_shift_of_rows (A := Box 0 90 0 32) (B := Box 0 90 0 32) (v := chainV)
    (fun _ h => (rest_y h).2) (fun _ h => (rest_y h).1) (by norm_num) (by norm_num)
  have hidle := (chain_idle_set (Δ := 254) orGate_rest hrows t (14 + 29 * 254) 16).translate
    chainV
  have hfar := farApart_shift_of_rows (A := Box 0 90 0 38) (B := Box 0 90 0 32) (v := chainV)
    (fun _ h => h.2.2.2) (fun _ h => (rest_y h).1) (by norm_num) (by norm_num)
  have h1 := (side_approach hδ).par hidle fun _ _ => farApart_chain_of hfar
  have hS : sideIn δ = orSide6 ∨ sideIn δ = orSide7 := by
    unfold sideIn; split_ifs <;> simp
  have h2 := entryRelay t hS
  have e1 : relayChain orGate 254 chainV (t + 1) 14 ∪ sideInE δ =
      phase orGate 14 ∪ sideInE δ ∪ translate chainV
        (relayChain orGate 254 chainV t (14 + 29 * 254)) := by
    rw [relayChain_succ]
    ac_rfl
  have e2 : orGate ∪ sideIn δ ∪ translate chainV
        (relayChain orGate 254 chainV t (14 + 29 * 254 + 16)) =
      relayChain orGate 254 chainV (t + 1) 0 ∪ sideIn δ := by
    rw [relayChain_succ, show 14 + 29 * 254 + 16 = 0 + 29 * 254 + 30 * 1 by norm_num,
      relayChain_add_thirty, phase, Nat.zero_mod, Rule.evolve_zero]
    ac_rfl
  rw [e1]
  refine (h1.seq_eq e2 h2).mono fun i _ => ?_
  split_ifs
  · refine Set.union_subset ?_ ?_
    · have hb : Box 0 90 0 38 ⊆ orFoot := fun c hc =>
        Or.inl ⟨hc.1, hc.2.1, by have := hc.2.2.1; omega, hc.2.2.2⟩
      exact hb.trans (box_subset_chainFoot (by omega))
    · exact (Set.image_mono (chainFoot_mono rest_subset_orFoot _ _)).trans image_chainFoot_subset
  · exact le_rfl

/-- **The entry of unit `a` at copy `t` with a side window**, with the copies of the layout: the
copies `0 … t` of the entry chain of unit `a` at time `Ts = 164 + 30 k + (16 t mod 30)` (`16`
generations before the side-input time `T0 = Ts + 16` of `entry_reaction`) and the glider on the
side line of copy `t` at offset `δ ∈ {4, 5}` become, `16 + 134 + 254 t` generations later, the
copies at their later phases and the output glider of copy `0`, inside the entry footprint of
`entry_reaction`. -/
theorem entry_reactionW (p : Program) (a t : ℕ) {δ : ℤ} (hδ : δ = 4 ∨ δ = 5) (k : ℤ) (Ts : ℕ)
    (hTs : (Ts : ℤ) = 164 + 30 * k + 16 * (t : ℤ) % 30) :
    Reaction
      (piecesAt ((chainSpecs (t + 1) (unitDX p a) (unitDY p a)).map PSpec.piece) Ts ∪
        ((destWin p a t).shift 0 0 (δ + 30 * k)).cells Ts)
      (piecesAt ((chainSpecs (t + 1) (unitDX p a) (unitDY p a)).map PSpec.piece)
          (Ts + (16 + (134 + t * 254))) ∪ translate (unitDX p a + 35, unitDY p a + 64) orIn)
      (16 + (134 + t * 254))
      (fun _ => (fun c => (unitDX p a - 35 * t, unitDY p a - 64 * t) + c) ''
        chainFoot orFoot chainV (t + 1)) := by
  rw [chainSpecs_piecesAt t _ _ Ts 14 (by omega),
    chainSpecs_piecesAt t _ _ (Ts + (16 + (134 + t * 254))) (134 + t * 254) (by omega), hTs,
    side_arrivalE p a t δ k hδ, ← translate_union]
  have h := (entryRelayW t hδ).translate (unitDX p a - 35 * t, unitDY p a - 64 * t)
  rw [show (unitDX p a + 35, unitDY p a + 64) = (unitDX p a - 35 * (t : ℤ),
      unitDY p a - 64 * (t : ℤ)) + (((t + 1 : ℕ) : ℤ) * 35, ((t + 1 : ℕ) : ℤ) * 64) by
    ext <;> simp <;> ring, ← translate_translate, ← translate_union]
  exact h

end LP

end LeanTheory.Life
