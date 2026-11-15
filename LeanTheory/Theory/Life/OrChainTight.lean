/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Gen.OrTight

/-!
# Merge chains with the tight footprint of the OR gate relay

The crude footprint `Box 0 90 (-6) 60` of the OR gate relays (`orGate_relay`, `orGate_side6`,
`orGate_side7`) contains the upper left corner of the gate's frame, where the reflector of the
input corner of entry copy `0` of a merge or halt unit sits (unit column `C0 = -67`: reflector box
`x ∈ [-1, 7]`, `y ∈ [54, 76]` in the unit frame), so the separation of the entry chain from that
reflector was false. The reactions never go there (`Gen/OrTight`):

* `orFoot = Box 0 90 (-6) 38 ∪ Box 49 73 36 60`: the tight footprint of every relay;
* `orGate_relayT`, `orGate_side6T`, `orGate_side7T`: the relays with footprint `orFoot` (the
  early part certified in `Gen/OrTight`, then the gate at rest beside the output glider);
* `chain_side_reaction_set`: `chain_side_reaction` with footprints of any shape;
* `orChainT`, `orChainSide6T`, `orChainSide7T`: the merge chains with footprint
  `chainFoot orFoot (35, 64)`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- **The tight footprint of an OR gate relay**: the gate's frame up to row `38`, and the box of
the output glider's flight. -/
def orFoot : Set Cell := Box 0 90 (-6) 38 ∪ Box 49 73 36 60

/-- The gate at rest lies in the tight footprint. -/
theorem rest_subset_orFoot : Box 0 90 0 32 ⊆ orFoot :=
  fun _ ⟨h1, h2, h3, h4⟩ => Or.inl ⟨h1, h2, by omega, by omega⟩

/-- The tight footprint lies in the crude one. -/
theorem orFoot_subset : orFoot ⊆ Box 0 90 (-6) 60 := by
  rintro _ (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) <;> exact ⟨by omega, by omega, by omega, by omega⟩

/-- Rows of the tight footprint. -/
theorem orFoot_y {c : Cell} (h : c ∈ orFoot) : -6 ≤ c.2 ∧ c.2 ≤ 60 := by
  rcases h with ⟨-, -, h3, h4⟩ | ⟨-, -, h3, h4⟩ <;> omega

/-- **The late part of a relay**: the gate at rest beside the output glider `orOutMid`, which
flies to the input place of the next copy. -/
theorem orGate_late (s : ℕ) :
    Reaction (phase orGate s ∪ orOutMid) (phase orGate (s + 88) ∪ translate (35, 64) orIn) 88
      (fun _ => Box 0 90 0 32 ∪ Box 49 73 36 60) :=
  (phase_reaction orGate_rest s 88).par orOutMid_flight
    fun _ _ => Box.farApart (Or.inr (Or.inr (Or.inl (by norm_num))))

/-- Gluing an early part inside `Box 0 90 (-6) 38` and the late part gives the tight footprint. -/
theorem orFoot_glue {P : Finset Cell} {s : ℕ}
    (h : Reaction P (phase orGate s ∪ orOutMid) s (fun _ => Box 0 90 (-6) 38)) :
    Reaction P (phase orGate (s + 88) ∪ translate (35, 64) orIn) (s + 88) (fun _ => orFoot) := by
  refine (h.seq (orGate_late s)).mono fun i _ => ?_
  split_ifs
  · exact Set.subset_union_left
  · exact Set.union_subset_union_left _ (box_subset_box le_rfl le_rfl (by norm_num) (by norm_num))

/-- **Certificate**: the through relay of the OR gate, with the tight footprint. -/
theorem orGate_relayT :
    Reaction (orGate ∪ orIn) (phase orGate 254 ∪ translate (35, 64) orIn) 254
      (fun _ => orFoot) :=
  orFoot_glue orGate_relay_early

/-- **Certificate**: the side relay `orSide6`, with the tight footprint. -/
theorem orGate_side6T :
    Reaction (orGate ∪ orSide6) (phase orGate 134 ∪ translate (35, 64) orIn) 134
      (fun _ => orFoot) :=
  orFoot_glue orGate_side6_early

/-- **Certificate**: the side relay `orSide7`, with the tight footprint. -/
theorem orGate_side7T :
    Reaction (orGate ∪ orSide7) (phase orGate 134 ∪ translate (35, 64) orIn) 134
      (fun _ => orFoot) :=
  orFoot_glue orGate_side7_early

/-! ### Chains entered from the side, footprints of any shape -/

/-- **A chain entered from the side**, footprints of any shape (`chain_side_reaction` with sets):
the copy at rest in `B`, the through relay in `R ⊇ B`, the side relay in `Rs ⊆ R`; each copy far
from all later copies. -/
theorem chain_side_reaction_set {G In S : Finset Cell} {Δ Δs : ℕ} {v : Cell} {B R Rs : Set Cell}
    (hG : Reaction G G 30 (fun _ => B))
    (hrel : Reaction (G ∪ In) (phase G Δ ∪ translate v In) Δ (fun _ => R))
    (hside : Reaction (G ∪ S) (phase G Δs ∪ translate v In) Δs (fun _ => Rs))
    (hΔ : (29 * Δ + Δs) % 30 = 0) (hBR : B ⊆ R) (hSR : Rs ⊆ R)
    (hs0 : ∀ j : ℕ, 1 ≤ j → FarApart 2 B {c | (c.1 - (j : ℤ) * v.1, c.2 - (j : ℤ) * v.2) ∈ B})
    (hs1 : ∀ j : ℕ, 1 ≤ j → FarApart 2 R {c | (c.1 - (j : ℤ) * v.1, c.2 - (j : ℤ) * v.2) ∈ B})
    (hs2 : ∀ j : ℕ, 1 ≤ j → FarApart 2 B {c | (c.1 - (j : ℤ) * v.1, c.2 - (j : ℤ) * v.2) ∈ R})
    (hs3 : ∀ j : ℕ, 1 ≤ j → FarApart 2 Rs {c | (c.1 - (j : ℤ) * v.1, c.2 - (j : ℤ) * v.2) ∈ B})
    (L : ℕ) :
    Reaction (relayChain G Δ v (L + 2) 0 ∪ S)
      (phase G (Δs + (L + 1) * Δ) ∪ translate v (relayChain G Δ v (L + 1) ((L + 1) * Δ) ∪
        translate (((L + 1 : ℕ) : ℤ) * v.1, ((L + 1 : ℕ) : ℤ) * v.2) In))
      (Δs + (L + 1) * Δ) (fun _ => chainFoot R v (L + 2)) := by
  have h1 := hside.par ((chain_idle_set (Δ := Δ) hG hs0 (L + 1) (29 * Δ) Δs).translate v)
    fun _ _ => farApart_chain_of hs3
  have h2 := (phase_reaction hG Δs ((L + 1) * Δ)).par ((chain_reaction_set hG hrel hBR hs0 hs1
    hs2 L).translate v) fun _ _ => farApart_chain_of hs2
  rw [relayChain_of_mod G Δ v (L + 1) (29 * Δ + Δs) hΔ] at h1
  have h := h1.seq_eq (by rw [translate_union]; ac_rfl) h2
  rw [relayChain_succ, phase, Nat.zero_mod, Rule.evolve_zero, zero_add,
    show G ∪ translate v (relayChain G Δ v (L + 1) (29 * Δ)) ∪ S =
      G ∪ S ∪ translate v (relayChain G Δ v (L + 1) (29 * Δ)) by ac_rfl]
  refine h.mono fun i _ => ?_
  split_ifs
  · exact Set.union_subset (hSR.trans (box_subset_chainFoot (by omega)))
      ((Set.image_mono (chainFoot_mono hBR v _)).trans image_chainFoot_subset)
  · exact Set.union_subset (hBR.trans (box_subset_chainFoot (by omega))) image_chainFoot_subset

/-- Copies of a set above row `hi` and a set below: a set with rows `≤ hi` is far from the copies
number `1, 2, …` of a set with rows `≥ lo`, when `hi + 2 < lo + v.2`. -/
theorem farApart_shift_of_rows {A B : Set Cell} {hi lo : ℤ} {v : Cell}
    (hA : ∀ c ∈ A, c.2 ≤ hi) (hB : ∀ c ∈ B, lo ≤ c.2) (h : hi + 2 < lo + v.2) (hv : 0 ≤ v.2) :
    ∀ j : ℕ, 1 ≤ j → FarApart 2 A {c | (c.1 - (j : ℤ) * v.1, c.2 - (j : ℤ) * v.2) ∈ B} := by
  intro j hj x hx y hy hn
  have h1 := hA x hx
  have h2 := hB _ hy
  have h3 := hn.2.2.1
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  simp only at h2
  push_cast at h3
  nlinarith

/-- Rows of the gate's frame at rest. -/
theorem rest_y {c : Cell} (h : c ∈ Box 0 90 0 32) : 0 ≤ c.2 ∧ c.2 ≤ 32 := ⟨h.2.2.1, h.2.2.2⟩

/-- **The merge chain, any length, with the tight footprint.** -/
theorem orChainT (L : ℕ) :
    Reaction (relayChain orGate 254 (35, 64) (L + 1) 0 ∪ orIn)
      (relayChain orGate 254 (35, 64) (L + 1) ((L + 1) * 254) ∪
        translate (((L + 1 : ℕ) : ℤ) * (35, 64).1, ((L + 1 : ℕ) : ℤ) * (35, 64).2) orIn)
      ((L + 1) * 254) (fun _ => chainFoot orFoot (35, 64) (L + 1)) :=
  chain_reaction_set orGate_rest orGate_relayT rest_subset_orFoot
    (farApart_shift_of_rows (fun _ h => (rest_y h).2) (fun _ h => (rest_y h).1) (by norm_num)
      (by norm_num))
    (farApart_shift_of_rows (fun _ h => (orFoot_y h).2) (fun _ h => (rest_y h).1) (by norm_num)
      (by norm_num))
    (farApart_shift_of_rows (fun _ h => (rest_y h).2) (fun _ h => (orFoot_y h).1) (by norm_num)
      (by norm_num)) L

/-- The side chain from a side relay with the tight footprint. -/
theorem orChainSideT {S : Finset Cell}
    (hside : Reaction (orGate ∪ S) (phase orGate 134 ∪ translate (35, 64) orIn) 134
      (fun _ => orFoot)) (L : ℕ) :
    Reaction (relayChain orGate 254 (35, 64) (L + 2) 0 ∪ S)
      (phase orGate (134 + (L + 1) * 254) ∪ translate (35, 64) (relayChain orGate 254 (35, 64)
        (L + 1) ((L + 1) * 254) ∪ translate (((L + 1 : ℕ) : ℤ) * (35, 64).1,
          ((L + 1 : ℕ) : ℤ) * (35, 64).2) orIn))
      (134 + (L + 1) * 254) (fun _ => chainFoot orFoot (35, 64) (L + 2)) :=
  chain_side_reaction_set orGate_rest orGate_relayT hside (by norm_num) rest_subset_orFoot le_rfl
    (farApart_shift_of_rows (fun _ h => (rest_y h).2) (fun _ h => (rest_y h).1) (by norm_num)
      (by norm_num))
    (farApart_shift_of_rows (fun _ h => (orFoot_y h).2) (fun _ h => (rest_y h).1) (by norm_num)
      (by norm_num))
    (farApart_shift_of_rows (fun _ h => (rest_y h).2) (fun _ h => (orFoot_y h).1) (by norm_num)
      (by norm_num))
    (farApart_shift_of_rows (fun _ h => (orFoot_y h).2) (fun _ h => (rest_y h).1) (by norm_num)
      (by norm_num)) L

/-- **The merge chain entered from the side** (`orSide6`), with the tight footprint. -/
theorem orChainSide6T (L : ℕ) :
    Reaction (relayChain orGate 254 (35, 64) (L + 2) 0 ∪ orSide6)
      (phase orGate (134 + (L + 1) * 254) ∪ translate (35, 64) (relayChain orGate 254 (35, 64)
        (L + 1) ((L + 1) * 254) ∪ translate (((L + 1 : ℕ) : ℤ) * (35, 64).1,
          ((L + 1 : ℕ) : ℤ) * (35, 64).2) orIn))
      (134 + (L + 1) * 254) (fun _ => chainFoot orFoot (35, 64) (L + 2)) :=
  orChainSideT orGate_side6T L

/-- **The merge chain entered from the side** (`orSide7`), with the tight footprint. -/
theorem orChainSide7T (L : ℕ) :
    Reaction (relayChain orGate 254 (35, 64) (L + 2) 0 ∪ orSide7)
      (phase orGate (134 + (L + 1) * 254) ∪ translate (35, 64) (relayChain orGate 254 (35, 64)
        (L + 1) ((L + 1) * 254) ∪ translate (((L + 1 : ℕ) : ℤ) * (35, 64).1,
          ((L + 1 : ℕ) : ℤ) * (35, 64).2) orIn))
      (134 + (L + 1) * 254) (fun _ => chainFoot orFoot (35, 64) (L + 2)) :=
  orChainSideT orGate_side7T L

end LeanTheory.Life
