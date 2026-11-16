/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepProof
public import LeanTheory.Theory.Life.ActivationIncSepProof4
public import LeanTheory.Theory.Life.ActivationIncSepUnit

/-!
# The fields of `DecSep` at the end of the answer links

Research note `N-22`. The fields of `DecSep` (`ActivationDecStepThread`) at the unit the answer
goes to, in strong forms (far from every piece of the machine), from the tools of the `inc`
activation (`ActivationIncSepProof4`, `ActivationIncSepUnit`):

* `dsep_flyAN`, `dsep_flyAZ`: the flight of the answer from the end of its last corner window to
  `16` generations before the side input of its entry copy (`isep2_flyEntry`);
* `dsep_entAN`, `dsep_entAZ`: the entry chain of the unit (`isep2_entry_far`);
* `dsep_outAN`, `dsep_outAZ`: the flight to the body input of the unit (`isep2_outC`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- The corners of the NZ answer end with the input corner of its entry copy. -/
theorem dsep_csN_eq (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    decCsN p i r =
      (⟨0, U p r + nzAnsChan p (callerIdx p r i), nzAnsPortV (callerIdx p r i),
        .left r (2 * D p + 2 + 2 * (callerIdx p r i))⟩ ::
        bandCorners p (instrBand i) 3 (U p r + nzAnsChan p (callerIdx p r i))
          (hairReg p 3 (decEA p i r) (U p r + nzAnsChan p (callerIdx p r i)))
          (destU p (i + 1) (decTN p i r)) 5 6) ++
        [isep2SlabC p (i + 1) ((decTNn p i r : ℕ) : ℤ)] := by
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  rw [htN]
  simp [decCsN, decMkN, nzAnsCorners, upCornersK, isep2SlabC]

/-- The corners of the Z answer end with the input corner of its entry copy. -/
theorem dsep_csZ_eq (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    decCsZ p i r z =
      (⟨4, U p r + zAnsStation (callerIdx p r i), zAnsDepth p (callerIdx p r i),
        .right r (callerIdx p r i) 0⟩ ::
        ⟨6, U p r + zAnsChan p (callerIdx p r i), zAnsDepth p (callerIdx p r i),
          .right r (callerIdx p r i) 1⟩ ::
        bandCorners p (instrBand i) 4 (U p r + zAnsChan p (callerIdx p r i))
          (hairReg p 4 (decEB p i r z) (U p r + zAnsChan p (callerIdx p r i)))
          (destU p z (decTZ p i r z)) 5 6) ++
        [isep2SlabC p z ((decTZn p i r z : ℕ) : ℤ)] := by
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  rw [htN]
  simp [decCsZ, decMkZ, zAnsCorners, upCornersK, isep2SlabC]

/-- **`DecSep.flyAN`, strong form**: the NZ answer from the end of its route to `16` generations
before its side input is far from every piece of the machine. -/
theorem dsep_flyAN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, routeEndX (decGN p i r) (decCsN p i r) (decDispN p i r) ≤ t →
      t + 16 < decT0N p i r → ∀ h ∈ machPieces p, FarApart 2 ((decFinN p i r).box t) h.box := by
  intro t h1 h2 h hh
  have hl : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨hD, -, hT0, -⟩ := decN_times hp hi
  obtain ⟨-, htim, hδ, hfin, -⟩ := decAnsN_plan hp hi _ hD
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  have e := dsep_csN_eq hp hi
  have hcS : isep2SlabC p (i + 1) ((decTNn p i r : ℕ) : ℤ) ∈ allCorners p :=
    instrRoute_corner hl (x := (decGN p i r, decMkN p i r (decEA p i r)))
      (by rw [dsep_instrSpecs hi]; simp) _ (by
        change _ ∈ decCsN p i r
        rw [e]; simp)
  change RouteTimedX (decGN p i r) (decCsN p i r) _ at htim
  change (route (decGN p i r) (decCsN p i r)).2 = _ at hfin
  rw [e] at htim hfin h1
  have := isep2_flyEntry hp (a := i + 1) (t := decTNn p i r) (by rw [htN]; exact ht.2) hcS htim
    hδ hfin (T0 := decT0N p i r) (by rw [hT0]; rfl) t h1
    (by omega) h hh
  change FarApart 2 ((route (decGN p i r) (decCsN p i r)).2.box t) h.box
  rw [e]
  exact this

/-- **`DecSep.flyAZ`, strong form**: the Z answer from the end of its route to `16` generations
before its side input is far from every piece of the machine. -/
theorem dsep_flyAZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, routeEndX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) ≤ t →
      t + 16 < decT0Z p i r z → ∀ h ∈ machPieces p,
        FarApart 2 ((decFinZ p i r z).box t) h.box := by
  intro t h1 h2 h hh
  have hl : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨hD, -, hT0, -⟩ := decZ_times hp hi
  obtain ⟨-, htim, hδ, hfin, -⟩ := decAnsZ_plan hp hi _ hD
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  have e := dsep_csZ_eq hp hi
  have hcS : isep2SlabC p z ((decTZn p i r z : ℕ) : ℤ) ∈ allCorners p :=
    instrRoute_corner hl (x := (decGZ p i r, decMkZ p i r z (decEB p i r z)))
      (by rw [dsep_instrSpecs hi]; simp) _ (by
        change _ ∈ decCsZ p i r z
        rw [e]; simp)
  change RouteTimedX (decGZ p i r) (decCsZ p i r z) _ at htim
  change (route (decGZ p i r) (decCsZ p i r z)).2 = _ at hfin
  rw [e] at htim hfin h1
  have hT0' : (decT0Z p i r z : ℤ) = 180 + 30 * decKZ p i r z +
      16 * ((decTZn p i r z : ℕ) : ℤ) % 30 := by
    rw [hT0, htN]
  have := isep2_flyEntry hp (a := z) (t := decTZn p i r z) (by rw [htN]; exact ht.2) hcS htim
    hδ hfin (T0 := decT0Z p i r z) (by rw [hT0']; rfl) t h1 (by omega) h hh
  change FarApart 2 ((route (decGZ p i r) (decCsZ p i r z)).2.box t) h.box
  rw [e]
  exact this

/-- **`DecSep.entAN`, strong form**: the entry chain of unit `i + 1` from the entry copy of the NZ
answer is far from every piece of the machine other than its copies. -/
theorem dsep_entAN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ h ∈ machPieces p, h ∉ chainPieces p (i + 1) (decTNn p i r) →
      FarApart 2 (entryFoot p (i + 1) (decTNn p i r)) h.box := by
  have h1 := succ_lt_of_dec hp hi
  have ht := decTN_range hp hi
  have htN : ((decTNn p i r : ℕ) : ℤ) = decTN p i r := Int.toNat_of_nonneg ht.1
  have hR := one_le_R p
  exact isep2_entry_far hp (by unfold N; omega) (by rw [htN]; exact ht.2)

/-- **`DecSep.entAZ`, strong form**: the entry chain of unit `z` from the entry copy of the Z
answer is far from every piece of the machine other than its copies. -/
theorem dsep_entAZ (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ h ∈ machPieces p, h ∉ chainPieces p z (decTZn p i r z) →
      FarApart 2 (entryFoot p z (decTZn p i r z)) h.box := by
  have h1 := jump_lt_of_wf hp hi
  have ht := decTZ_range hp hi
  have htN : ((decTZn p i r z : ℕ) : ℤ) = decTZ p i r z := Int.toNat_of_nonneg ht.1
  have hR := one_le_R p
  exact isep2_entry_far hp (by unfold N; omega) (by rw [htN]; exact ht.2)

/-- **`DecSep.outAN`, strong form** (far from every piece of the machine). -/
theorem dsep_outAN (hp : p.WellFormed) :
    ∀ t : ℕ, t < 166 → ∀ h ∈ machPieces p, FarApart 2
      ((fun c => (unitDX p (i + 1), unitDY p (i + 1)) + c) '' chainOutWL.box (-166 + (t : ℤ)))
      h.box :=
  isep2_outC hp (i + 1)

/-- **`DecSep.outAZ`, strong form** (far from every piece of the machine). -/
theorem dsep_outAZ (hp : p.WellFormed) :
    ∀ t : ℕ, t < 166 → ∀ h ∈ machPieces p, FarApart 2
      ((fun c => (unitDX p z, unitDY p z) + c) '' chainOutWL.box (-166 + (t : ℤ))) h.box :=
  isep2_outC hp z

/-! ### The body of the `dec` unit -/

/-- The hull of the components of the body run of a `dec` unit (unit frame). -/
def dsepBodyHull : Set Cell :=
  {c | 61 ≤ c.1 ∧ c.1 ≤ 871 ∧ 99 ≤ c.2 ∧ c.2 ≤ 758 ∧ -180 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ 212 ∧
    205 ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ 1554}

/-- The components of the body run of a `dec` unit lie in the hull. -/
theorem dsep_bodyDecRegL_hull : DecAllSub dsepBodyHull bodyDecRegL := by
  simp only [bodyDecRegL, DecAllSub]
  repeat' apply And.intro
  all_goals first
    | exact fun c ⟨⟨_, _, _, _⟩, _, _, _, _⟩ => show c ∈ dsepBodyHull by
        simp only [dsepBodyHull, Set.mem_ofPred_eq]; omega
    | trivial

/-- The region of the body of the `dec` unit `i`, in coordinates. -/
theorem dsep_mem_bodyDecBox {c : Cell} (hc : c ∈ bodyDecBox p i) :
    unitDX p i + 61 ≤ c.1 ∧ c.1 ≤ unitDX p i + 871 ∧ unitDY p i + 99 ≤ c.2 ∧
      c.2 ≤ unitDY p i + 758 ∧ -180 ≤ c.1 - c.2 - (unitDX p i - unitDY p i) ∧
      c.1 - c.2 - (unitDX p i - unitDY p i) ≤ 212 ∧
      c.1 + c.2 ≤ unitDX p i + unitDY p i + 1554 := by
  obtain ⟨d, hd, rfl⟩ := hc
  have h : d ∈ dsepBodyHull := unionL_subset_dec dsep_bodyDecRegL_hull hd
  simp only [dsepBodyHull, Set.mem_ofPred_eq] at h
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- **`DecSep.body`**: the region of the body of a `dec` unit is far from every piece of the
machine other than the body. -/
theorem dsep_body (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ g ∈ machPieces p, g ∉ bodyDecGroup p i → FarApart 2 (bodyDecBox p i) g.box := by
  intro h hh hn
  have hf := layout_facts p
  have hd := unitD_uv p i
  have hS := fun c (hc : c ∈ bodyDecBox p i) => dsep_mem_bodyDecBox hc
  have hkind : unitKind p i = .dec := by unfold unitKind; rw [hi]
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hh
  rcases mem_machSpecs hs with ⟨a', ha', hs⟩ | ⟨r', hr', hs⟩ | ⟨c, hc, hb⟩
  · rcases lt_trichotomy a' i with h' | rfl | h'
    · have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := a') (a' := i) (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
    · unfold unitSpecs at hs
      rw [hkind] at hs
      rcases List.mem_append.1 hs with hs | hs
      · obtain ⟨t', ht', rfl⟩ := mem_chainSpecs hs
        rw [isep2_chain_box]
        refine isep2_far_box fun x hx => ?_
        have := hS x hx
        omega
      · exact absurd (List.mem_map_of_mem hs) hn
    · have hu := unitSpecs_uv p a' hs
      have := A_add_le p (a := i) (a' := a') (by exact_mod_cast h')
      have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
      rw [PSpec.piece_box]
      refine isep2_far_box fun x hx => ?_
      have := hS x hx
      unfold BoxT.InUV at hu
      omega
  · have hu := (moduleSpecs_uv p r' hs).1
    rw [PSpec.piece_box]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hu
    omega
  · have hv := allCorners_valid hp c hc
    have hcu := corner_uv c
    rw [PSpec.piece_box, hb]
    refine isep2_far_box fun x hx => ?_
    have := hS x hx
    unfold BoxT.InUV at hcu
    obtain ⟨k, u, v, tag⟩ := c
    simp only at hcu
    cases tag with
    | band b n h' => simp only [Valid] at hv; omega
    | halt a'' => simp only [Valid] at hv; omega
    | slab a'' t' =>
      simp only [Valid] at hv
      have hC'' := unitC0_cases p a''.toNat
      rcases lt_trichotomy a'' i with h' | h' | h'
      · have := A_add_le p h'
        omega
      · omega
      · have := A_add_le p h'
        omega
    | left r' idx => simp only [Valid] at hv; omega
    | right r' j' w => simp only [Valid] at hv; omega

end LP

end LeanTheory.Life
