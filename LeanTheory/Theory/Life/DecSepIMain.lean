/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepI9

/-!
# The fields `nIdle`, `zIdle`, `nLane`, `zLane` of `DecSepRest`

Research note `N-22`. For every `decJz` instruction of a well-formed program:

* `dsepI_nIdle`, `dsepI_zIdle` (`DecSepI6`): the threads of the activation (and the INC gate in
  the `Z` thread) are far from every idle piece of the machine;
* `dsepI_nLane`, `dsepI_zLane`: the machine and the threads are far from the lanes of every other
  register (every part of the footprints is clear of them, `DecSepI7` … `DecSepI9`);
* **`dsepI_fields`**: the four fields, verbatim from `DecSepRest`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- The boxes of a list of pieces of the machine are clear of the lanes of every register. -/
theorem dsepI_boxes_lane (hp : p.WellFormed) (r' : ℕ) {L : List Piece}
    (hL : ∀ x ∈ L, x ∈ machPieces p) : LaneClear p r' (boxesOf L) :=
  laneClear_boxesOf fun g hg => machPieces_laneClear hp r' g (hL g hg)

/-- **`DecSep.nLane`**: the machine and the threads of an NZ activation are far from the lanes of
every other register. -/
theorem dsepI_nLane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decEndN p i r → ∀ r' < numRegs p, r' ≠ r →
      FarApart 2 (boxesOf (machPieces p) ∪ (footMN p i r t ∪ (boxesOf (decLZu p i r) ∪
        unpFootZ p i r t))) (modLanes p r') := by
  intro t h0 h1 r' _ hr
  have hrr := lt_numRegs_of_dec hi
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have pLC := decLC_mem hi
  have pG := modGroup_mem hrr
  have pSN := decLSN_mem hi
  have pNu := decLNu_mem hi
  have pZu := decLZu_mem hi
  have pFN := decLFN_mem hp hi
  have pN := decLN_mem hi
  have pF0 : ∀ x ∈ decLF0N p i r, x ∈ machPieces p := fun x hx => pFN x (by
    rcases List.mem_append.1 (mem_dd.1 hx) with hx | hx
    · exact mem_dd.2 (List.mem_append_left _ (List.mem_append_right _ hx))
    · exact mem_dd.2 (List.mem_append_right _ hx))
  have hB := fun {L : List Piece} (hL : ∀ x ∈ L, x ∈ machPieces p) => dsepI_boxes_lane hp r' hL
  have hApp := fun {A B : List Piece} (hA : ∀ x ∈ A, x ∈ machPieces p)
      (hB' : ∀ x ∈ B, x ∈ machPieces p) (x : Piece) (hx : x ∈ A ++ B) =>
    (List.mem_append.1 hx).elim (hA x) (hB' x)
  refine LaneClear.farApart (LaneClear.union (hB fun _ h => h) (LaneClear.union ?_
    (LaneClear.union (hB pZu) (dsepI_unpFootZ_lane hp hi hr h0))))
  unfold footMN
  split_ifs with hc
  · refine LaneClear.union (hB pF0) (LaneClear.union ?_ (LaneClear.union (hB pNu)
      (dsepI_tokFootN_lane hp hi hr h0 hc)))
    unfold qFootN
    split_ifs with h2 h3
    · exact LaneClear.union (hB (hApp pG pSN)) (LaneClear.union (LaneClear.union (hB pLC)
        (dsepI_footC_lane hi h0 h2)) ((modLanes_near p r).laneClear hr))
    · exact LaneClear.union (hB (hApp pLC pSN)) (dsepI_zone_lane dsepI_runNZ_zone hr)
    · exact LaneClear.union (hB pLC) (LaneClear.union (dsepI_restFootN_lane hr t)
        (LaneClear.union (hB pSN) (dsepI_ansFootN_lane hi hr (by omega))))
  · exact LaneClear.union (hB (hApp (hApp pLC pSN) pN)) (LaneClear.union
      (dsepI_restFootN_lane hr t) (LaneClear.union (hB pFN)
        (dsepI_finFootN_lane hp hi hr (by omega) h1)))

/-- **`DecSep.zLane`**: the machine, the threads of a Z activation and the INC gate are far from
the lanes of every other register. -/
theorem dsepI_zLane (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z → ∀ r' < numRegs p, r' ≠ r →
      FarApart 2 (boxesOf (machPieces p) ∪ (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪
        unpFootN p i r t) ∪ gateFoot p r)) (modLanes p r') := by
  intro t h0 h1 r' _ hr
  have hrr := lt_numRegs_of_dec hi
  obtain ⟨hTS, -, -⟩ := decTS_facts p hi
  have pLC := decLC_mem hi
  have pG := modGroup_mem hrr
  have pSZ := decLSZ_mem hi
  have pNu := decLNu_mem hi
  have pZu := decLZu_mem hi
  have pFZ := decLFZ_mem hp hi
  have pZ := decLZ_mem hi
  have pF0 : ∀ x ∈ decLF0Z p i r z, x ∈ machPieces p := fun x hx => pFZ x (by
    rcases List.mem_append.1 (mem_dd.1 hx) with hx | hx
    · exact mem_dd.2 (List.mem_append_left _ (List.mem_append_right _ hx))
    · exact mem_dd.2 (List.mem_append_right _ hx))
  have pGt : ∀ x ∈ [gateP p r], x ∈ machPieces p := fun x hx => by
    rw [List.mem_singleton.1 hx]
    exact dsepI_gate_mem hi
  have hB := fun {L : List Piece} (hL : ∀ x ∈ L, x ∈ machPieces p) => dsepI_boxes_lane hp r' hL
  have hApp := fun {A B : List Piece} (hA : ∀ x ∈ A, x ∈ machPieces p)
      (hB' : ∀ x ∈ B, x ∈ machPieces p) (x : Piece) (hx : x ∈ A ++ B) =>
    (List.mem_append.1 hx).elim (hA x) (hB' x)
  refine LaneClear.farApart (LaneClear.union (hB fun _ h => h) (LaneClear.union
    (LaneClear.union ?_ (LaneClear.union (hB pNu) (dsepI_unpFootN_lane hp hi hr h0)))
    ((hB pGt).mono fun x hx => mem_boxesOf.2
      ⟨gateP p r, List.mem_singleton_self _, gateFoot_subset p r hx⟩)))
  unfold footMZ
  split_ifs with hc
  · refine LaneClear.union (hB pF0) (LaneClear.union ?_ (LaneClear.union (hB pZu)
      (dsepI_tokFootZ_lane hp hi hr h0 hc)))
    unfold qFootZ
    split_ifs with h2 h3
    · exact LaneClear.union (hB (hApp pG pSZ)) (LaneClear.union (LaneClear.union (hB pLC)
        (dsepI_footC_lane hi h0 h2)) ((modLanes_near p r).laneClear hr))
    · exact LaneClear.union (hB (hApp pLC pSZ)) (dsepI_zone_lane dsepI_runZ_zone hr)
    · exact LaneClear.union (hB pLC) (LaneClear.union (dsepI_restFootZ_lane hr t)
        (LaneClear.union (hB pSZ) (dsepI_ansFootZ_lane hi hr (by omega))))
  · exact LaneClear.union (hB (hApp (hApp pLC pSZ) pZ)) (LaneClear.union
      (dsepI_restFootZ_lane hr t) (LaneClear.union (hB pFZ)
        (dsepI_finFootZ_lane hp hi hr (by omega) h1)))

/-- **The four fields `nIdle`, `nLane`, `zIdle`, `zLane` of `DecSepRest`**, verbatim, for every
`decJz` instruction of a well-formed program. -/
theorem dsepI_fields (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    (∀ t : ℕ, 4260 ≤ t → t < decEndN p i r → ∀ g ∈ machPieces p,
      g ∉ decLMN p i r ++ decLZu p i r →
      FarApart 2 (footMN p i r t ∪ (boxesOf (decLZu p i r) ∪ unpFootZ p i r t)) g.box) ∧
    (∀ t : ℕ, 4260 ≤ t → t < decEndN p i r → ∀ r' < numRegs p, r' ≠ r →
      FarApart 2 (boxesOf (machPieces p) ∪ (footMN p i r t ∪ (boxesOf (decLZu p i r) ∪
        unpFootZ p i r t))) (modLanes p r')) ∧
    (∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z → ∀ g ∈ machPieces p,
      g ∉ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] →
      FarApart 2 (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪ unpFootN p i r t) ∪ gateFoot p r)
        g.box) ∧
    (∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z → ∀ r' < numRegs p, r' ≠ r →
      FarApart 2 (boxesOf (machPieces p) ∪ (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪
        unpFootN p i r t) ∪ gateFoot p r)) (modLanes p r')) :=
  ⟨dsepI_nIdle hp hi, dsepI_nLane hp hi, dsepI_zIdle hp hi, dsepI_zLane hp hi⟩

end LP

end LeanTheory.Life
