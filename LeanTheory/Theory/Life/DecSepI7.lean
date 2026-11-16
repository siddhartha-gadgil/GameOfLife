/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepI6
public import LeanTheory.Theory.Life.LaneSep3

/-!
# The lanes of the other registers: tools

Research note `N-22`. For the fields `nLane`, `zLane` of `DecSepRest`, the parts of the footprints
of the threads of a `decJz` activation at register `r` are clear of the lanes of every register
`r' ≠ r` (`LaneClear`, `LaneSep`):

* `dsepI_band_lane`: a set in the extended `u`-band of module `r` (`dsepI_zone_lane`: a set of
  the module frame in the zone of the module);
* the regions of the register runs lie in the zone (`dsepI_runNZ_zone`, `dsepI_restNZ_zone`,
  `dsepI_runZ_zone`, `dsepI_restZ_zone`);
* `dsepI_rfoot_lane`: a route clear of the lanes in the sense of `RouteLane` (`LaneSep3`) has a
  clear footprint `routeFootX`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-! ### Sets near module `r` -/

/-- **A set in the extended `u`-band of module `r` is clear of the lanes of every other
register.** -/
theorem dsepI_band_lane {r r' : ℕ} {S : Set Cell}
    (hS : ∀ c ∈ S, U p r - 900 - 248 * D p ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ U p r + 1400 + 144 * D p)
    (hr : r' ≠ r) : LaneClear p r' S := by
  intro c hc
  have := hS c hc
  rcases lt_or_gt_of_ne hr with h | h
  · have := lane_U_gap p h
    omega
  · have := lane_U_gap p h
    omega

/-- **A set of the module frame in the zone of module `r` is clear of the lanes of every other
register.** -/
theorem dsepI_zone_lane {r r' : ℕ} {S : Set Cell} (hS : S ⊆ dsepTZone p) (hr : r' ≠ r) :
    LaneClear p r' (modImg p r S) := by
  refine dsepI_band_lane (fun c hc => ?_) hr
  obtain ⟨d, hd, rfl⟩ := hc
  have h := hS hd
  have hu := modD_uv p r
  have hD := one_le_D p
  simp only [dsepTZone, Set.mem_ofPred_eq] at h
  simp only [Prod.fst_add, Prod.snd_add]
  omega

/-- The NZ run region lies in the zone. -/
theorem dsepI_runNZ_zone : decRunRegNZ ⊆ dsepTZone p := by
  intro x hx
  simp only [decRunRegNZ, unionL, Set.mem_union] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h
  · exact unionL_subset_dec dsepT_dz2dPreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2d1PreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2d2PreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2d3PreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk1PreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk2PreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk3PreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk4PreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk5PreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk6PreRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk7PreRegL_zone h
  · exact h.elim

/-- The NZ rest region lies in the zone. -/
theorem dsepI_restNZ_zone : decRestRegNZ ⊆ dsepTZone p := by
  intro x hx
  simp only [decRestRegNZ, unionL, Set.mem_union] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h
  · exact unionL_subset_dec dsepT_dz2dRestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2d1RestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2d2RestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2d3RestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk1RestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk2RestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk3RestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk4RestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk5RestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk6RestRegL_zone h
  · exact unionL_subset_dec dsepT_dz2mk7RestRegL_zone h
  · exact h.elim

/-- The Z run region lies in the zone. -/
theorem dsepI_runZ_zone : decRunRegZ ⊆ dsepTZone p :=
  unionL_subset_dec dsepT_dz2mk0PreRegL_zone

/-- The Z rest region lies in the zone. -/
theorem dsepI_restZ_zone : dz2mk0RestRegion ⊆ dsepTZone p :=
  unionL_subset_dec dsepT_dz2mk0RestRegL_zone

/-! ### Routes -/

/-- **A route clear of the lanes (`RouteLane`) has a clear footprint** up to its end. -/
theorem dsepI_rfoot_lane {r' : ℕ} : ∀ (cs : List Corner) (c : Corner) (g : WL) (T : ℕ),
    RouteLane p r' g (c :: cs) T → RouteTimedX g (c :: cs) T → ∀ j : ℕ,
      T + j ≤ routeEndX g (c :: cs) T → LaneClear p r' (routeFootX g (c :: cs) T j)
  | cs, c, g, T, ⟨l1, l2, l3⟩, ⟨ht, hts⟩, j, hj => by
    have hm := meetT_cast_X (Int.natCast_nonneg T) ht
    simp only [routeFootX]
    split_ifs with h1 h2
    · exact l1 _ (by omega) h1
    · exact l2
    · cases cs with
      | nil =>
        exfalso
        simp only [routeEndX] at hj
        omega
      | cons c' cs' =>
        refine dsepI_rfoot_lane cs' c' (reflect g c).2 ((meetT g c).toNat + 40)
          (by rw [hm]; exact l3) (by rw [hm]; exact hts) (T + j - ((meetT g c).toNat + 40)) ?_
        have hj' : T + j ≤ routeEndX (reflect g c).2 (c' :: cs') ((meetT g c).toNat + 40) := hj
        omega

end LP

end LeanTheory.Life
