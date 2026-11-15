/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Network
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Chains of relays, of any length

A *relay* is a periodic piece `G` (period `30`) with an input pattern `In`: in `Δ` generations
`G ∪ In` becomes `G` (advanced by `Δ` generations) together with `In` moved by `v`, which is the
input of a copy of the relay placed at `v` and started `Δ` generations later. Copies placed at
`0, v, 2 v, …` relay a signal from the first to the last. The merge chains of the register
machine (report `R-29`: copies of `blockedStream` as OR gates, `v = (35, 64)`) are such chains
(research notes `N-15`, `N-19`).

* `relayCopy G Δ v j`: copy `j` of the chain at the start, at phase `29 Δ j` (that is `- j Δ`
  modulo `30`);
* `chain_reaction`: for every length `L`, the chain and the input evolve in `L Δ` generations into
  the chain (every copy advanced by `L Δ`) and the input moved by `L v`, inside the union of the
  relay boxes of the copies.

The separation hypotheses are two inequalities in the second coordinate: a copy at rest is far
from the relay box of every later copy and conversely.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- The piece `G` at phase `m`, read modulo its period `30`. -/
def phase (G : Finset Cell) (m : ℕ) : Finset Cell := conway.evolve (m % 30) G

/-- Evolving a periodic piece advances its phase. -/
theorem evolve_phase {G : Finset Cell} (hG : conway.evolve 30 G = G) (m n : ℕ) :
    conway.evolve n (phase G m) = phase G (m + n) := by
  rw [phase, phase, ← Rule.evolve_add, conway.evolve_mod_of_evolve_eq hG (n + m % 30)]
  congr 1
  omega

/-- Copy `j` of a chain at the start: the piece at phase `29 Δ j`, placed at `j • v`. -/
def relayCopy (G : Finset Cell) (Δ : ℕ) (v : Cell) (j : ℕ) : Finset Cell :=
  translate ((j : ℤ) * v.1, (j : ℤ) * v.2) (phase G (29 * Δ * j))

/-- The copies `0, …, L - 1` of a chain, each advanced by `n` generations. -/
def relayChain (G : Finset Cell) (Δ : ℕ) (v : Cell) (L n : ℕ) : Finset Cell :=
  (Finset.range L).biUnion fun j =>
    translate ((j : ℤ) * v.1, (j : ℤ) * v.2) (phase G (29 * Δ * j + n))

/-- The footprint of a chain: the relay box of every copy. -/
def chainFoot (R : Set Cell) (v : Cell) (L : ℕ) : Set Cell :=
  {c | ∃ j < L, (c.1 - (j : ℤ) * v.1, c.2 - (j : ℤ) * v.2) ∈ R}

/-- The chain of length `L + 1`: the first copy and the chain of length `L` moved by `v`, which is
`Δ` generations behind. -/
theorem relayChain_succ (G : Finset Cell) (Δ : ℕ) (v : Cell) (L n : ℕ) :
    relayChain G Δ v (L + 1) n =
      phase G n ∪ translate v (relayChain G Δ v L (n + 29 * Δ)) := by
  ext c
  simp only [relayChain, mem_union, mem_biUnion, mem_range, mem_translate]
  have key : ∀ j : ℕ, c - (((j + 1 : ℕ) : ℤ) * v.1, ((j + 1 : ℕ) : ℤ) * v.2) =
      c - v - ((j : ℤ) * v.1, (j : ℤ) * v.2) := by
    intro j
    ext <;> simp <;> ring
  have kp : ∀ j : ℕ, 29 * Δ * (j + 1) + n = 29 * Δ * j + (n + 29 * Δ) := by
    intro j
    ring
  constructor
  · rintro ⟨j, hj, hc⟩
    rcases j with _ | j
    · left
      have e : c - (((0 : ℕ) : ℤ) * v.1, ((0 : ℕ) : ℤ) * v.2) = c := by ext <;> simp
      rw [e, show 29 * Δ * 0 + n = n by ring] at hc
      exact hc
    · right
      refine ⟨j, by omega, ?_⟩
      rw [← key, ← kp]
      exact hc
  · rintro (hc | ⟨j, hj, hc⟩)
    · refine ⟨0, by omega, ?_⟩
      have e : c - (((0 : ℕ) : ℤ) * v.1, ((0 : ℕ) : ℤ) * v.2) = c := by ext <;> simp
      rw [e, show 29 * Δ * 0 + n = n by ring]
      exact hc
    · refine ⟨j + 1, by omega, ?_⟩
      rw [key, kp]
      exact hc

/-- The chain does not depend on whole periods in its phase. -/
theorem relayChain_add_thirty (G : Finset Cell) (Δ : ℕ) (v : Cell) (L n m : ℕ) :
    relayChain G Δ v L (n + 30 * m) = relayChain G Δ v L n := by
  simp only [relayChain, phase]
  refine Finset.biUnion_congr rfl fun j _ => ?_
  rw [show (29 * Δ * j + (n + 30 * m)) % 30 = (29 * Δ * j + n) % 30 by omega]

/-- The chain of length `1` is its first copy. -/
theorem relayChain_one (G : Finset Cell) (Δ : ℕ) (v : Cell) (n : ℕ) :
    relayChain G Δ v 1 n = phase G n := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, relayChain_succ]
  simp [relayChain]

/-- A periodic piece idles at any phase, inside its box. -/
theorem phase_reaction {G : Finset Cell} {B : Set Cell} (hG : Reaction G G 30 (fun _ => B))
    (n m : ℕ) : Reaction (phase G n) (phase G (n + m)) m (fun _ => B) :=
  ⟨evolve_phase hG.evolve_eq n m, fun i _ => by
    rw [evolve_phase hG.evolve_eq, phase]
    exact hG.subset _ (Nat.mod_lt _ (by norm_num)).le⟩

/-- A box is far from the footprint of a chain moved by `v` if it lies far above it. -/
theorem farApart_box_chain {a b lo hi a' b' lo' hi' : ℤ} {v : Cell} {L : ℕ}
    (h : hi + 2 < lo' + v.2) (hv : 0 ≤ v.2) :
    FarApart 2 (Box a b lo hi) ((fun c => v + c) '' chainFoot (Box a' b' lo' hi') v L) := by
  rintro x ⟨-, -, -, hx⟩ _ ⟨c, ⟨j, -, -, -, hc, -⟩, rfl⟩ ⟨-, -, hn, -⟩
  have hp : 0 ≤ (j : ℤ) * v.2 := mul_nonneg (by positivity) hv
  simp only [Prod.snd_add] at hn hc
  push_cast at hn
  linarith

/-- A chain moved by `v` is far from a box above it (the other order). -/
theorem farApart_chain_box {a b lo hi a' b' lo' hi' : ℤ} {v : Cell} {L : ℕ}
    (h : hi + 2 < lo' + v.2) (hv : 0 ≤ v.2) :
    FarApart 2 ((fun c => v + c) '' chainFoot (Box a' b' lo' hi') v L) (Box a b lo hi) :=
  fun x hx y hy hn => farApart_box_chain h hv y hy x hx (near_comm.1 hn)

/-- The first copy's box lies in the chain footprint. -/
theorem box_subset_chainFoot {B : Set Cell} {v : Cell} {L : ℕ} (hL : 0 < L) :
    B ⊆ chainFoot B v L :=
  fun c hc => ⟨0, hL, by simpa using hc⟩

/-- The chain footprint moved by `v` lies in the longer chain footprint. -/
theorem image_chainFoot_subset {B : Set Cell} {v : Cell} {L : ℕ} :
    (fun c => v + c) '' chainFoot B v L ⊆ chainFoot B v (L + 1) := by
  rintro _ ⟨c, ⟨j, hj, hc⟩, rfl⟩
  refine ⟨j + 1, by omega, ?_⟩
  convert hc using 1
  ext <;> simp <;> ring

/-- Footprints grow with the box. -/
theorem chainFoot_mono {B B' : Set Cell} (h : B ⊆ B') (v : Cell) (L : ℕ) :
    chainFoot B v L ⊆ chainFoot B' v L :=
  fun _ ⟨j, hj, hc⟩ => ⟨j, hj, h hc⟩

/-- **A chain at rest**: copies far apart (each copy's box far above the next one) idle side by
side for any number of generations. -/
theorem chain_idle {G : Finset Cell} {Δ : ℕ} {v : Cell} {a b lo hi : ℤ}
    (hG : Reaction G G 30 (fun _ => Box a b lo hi)) (hsep : hi + 2 < lo + v.2) (hv : 0 ≤ v.2)
    (L n m : ℕ) :
    Reaction (relayChain G Δ v L n) (relayChain G Δ v L (n + m)) m
      (fun _ => chainFoot (Box a b lo hi) v L) := by
  induction L generalizing n with
  | zero =>
    refine ⟨by simp [relayChain], fun i _ c hc => ?_⟩
    simp [relayChain] at hc
  | succ L ih =>
    rw [relayChain_succ, relayChain_succ,
      show n + m + 29 * Δ = (n + 29 * Δ) + m by omega]
    refine ((phase_reaction hG n m).par ((ih (n + 29 * Δ)).translate v)
      fun _ _ => farApart_box_chain hsep hv).mono fun _ _ => ?_
    exact Set.union_subset (box_subset_chainFoot (by omega)) image_chainFoot_subset

/-- **A chain of relays, any length**: if a copy at rest stays in the box `Bx`, relays its input in
`Δ` generations inside the box `R ⊇ Bx`, and copies are placed far apart (in the second
coordinate, both orders), then the chain of `L + 1` copies relays the input from the first copy to
the place of a copy number `L + 1`, in `(L + 1) Δ` generations. -/
theorem chain_reaction {G In : Finset Cell} {Δ : ℕ} {v : Cell}
    {a b lo hi ra rb rlo rhi : ℤ}
    (hG : Reaction G G 30 (fun _ => Box a b lo hi))
    (hrel : Reaction (G ∪ In) (phase G Δ ∪ translate v In) Δ (fun _ => Box ra rb rlo rhi))
    (hBR : Box a b lo hi ⊆ Box ra rb rlo rhi)
    (hs0 : hi + 2 < lo + v.2) (hs1 : rhi + 2 < lo + v.2) (hs2 : hi + 2 < rlo + v.2)
    (hv : 0 ≤ v.2) (L : ℕ) :
    Reaction (relayChain G Δ v (L + 1) 0 ∪ In)
      (relayChain G Δ v (L + 1) ((L + 1) * Δ) ∪
        translate (((L + 1 : ℕ) : ℤ) * v.1, ((L + 1 : ℕ) : ℤ) * v.2) In)
      ((L + 1) * Δ) (fun _ => chainFoot (Box ra rb rlo rhi) v (L + 1)) := by
  induction L with
  | zero =>
    rw [relayChain_one, relayChain_one, phase, phase, Nat.zero_mod, Rule.evolve_zero,
      show (0 + 1) * Δ = Δ by ring]
    rw [phase] at hrel
    convert hrel.mono (fun _ _ => box_subset_chainFoot (B := Box ra rb rlo rhi) (v := v)
      (L := 0 + 1) (by omega)) using 3
    ext <;> simp
  | succ L ih =>
    -- stage 1: the first copy relays, the rest of the chain idles
    have h1 := hrel.par ((chain_idle (Δ := Δ) hG hs0 hv (L + 1) (29 * Δ) Δ).translate v)
      fun _ _ => farApart_box_chain hs1 hv
    -- stage 2: the first copy idles, the rest of the chain relays (it is `Δ` behind)
    have h2 := (phase_reaction hG Δ ((L + 1) * Δ)).par (ih.translate v)
      fun _ _ => farApart_box_chain hs2 hv
    have e1 : relayChain G Δ v (L + 1) (29 * Δ + Δ) = relayChain G Δ v (L + 1) 0 := by
      rw [show 29 * Δ + Δ = 0 + 30 * Δ by ring, relayChain_add_thirty]
    rw [e1] at h1
    have h := h1.seq_eq (by rw [translate_union]; ac_rfl) h2
    have e2 : relayChain G Δ v (L + 1 + 1) 0 ∪ In =
        G ∪ In ∪ translate v (relayChain G Δ v (L + 1) (29 * Δ)) := by
      rw [relayChain_succ, phase, Nat.zero_mod, Rule.evolve_zero, zero_add]
      ac_rfl
    have e3 : relayChain G Δ v (L + 1 + 1) ((L + 1 + 1) * Δ) ∪
        translate (((L + 1 + 1 : ℕ) : ℤ) * v.1, ((L + 1 + 1 : ℕ) : ℤ) * v.2) In =
        phase G (Δ + (L + 1) * Δ) ∪ (translate v (relayChain G Δ v (L + 1) ((L + 1) * Δ)) ∪
          translate v (translate (((L + 1 : ℕ) : ℤ) * v.1, ((L + 1 : ℕ) : ℤ) * v.2) In)) := by
      rw [relayChain_succ, translate_translate,
        show (L + 1 + 1) * Δ + 29 * Δ = (L + 1) * Δ + 30 * Δ by ring, relayChain_add_thirty,
        show Δ + (L + 1) * Δ = (L + 1 + 1) * Δ by ring]
      have : (((L + 1 + 1 : ℕ) : ℤ) * v.1, ((L + 1 + 1 : ℕ) : ℤ) * v.2) =
          v + (((L + 1 : ℕ) : ℤ) * v.1, ((L + 1 : ℕ) : ℤ) * v.2) := by
        ext <;> simp <;> ring
      rw [this]
      ac_rfl
    rw [e2, e3, show (L + 1 + 1) * Δ = Δ + (L + 1) * Δ by ring, ← translate_union]
    refine h.mono fun i _ => ?_
    split_ifs
    · exact Set.union_subset (box_subset_chainFoot (by omega))
        ((Set.image_mono (chainFoot_mono hBR v _)).trans image_chainFoot_subset)
    · exact Set.union_subset ((hBR.trans (box_subset_chainFoot (by omega))))
        image_chainFoot_subset

end LeanTheory.Life
