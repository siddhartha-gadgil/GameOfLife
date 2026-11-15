/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncPlan
public import LeanTheory.Theory.Life.RouteSep5

/-!
# The route fields of `IncSep` for the plan of every `inc` instruction

Research note `N-22`. The three route fields `sepC`, `sepR`, `sepM` of `IncSep`
(`ActivationIncStep`) hold for the plan `incPlan p i r` of every `inc` instruction of a
well-formed program:

* `isep_sepC`, `isep_sepR`: the continue and the INC link are the two routes of `incSpecs`
  (`incSpecs_eq`), undelayed, from the end of the body (`2010`): `incLinks_sep` with `d = 0`;
* `isep_sepM`: the merge link is the route of `mergeSpecs` delayed by `T1 + 166 - 1080`
  (`≡ 0 (mod 30)` by the arrival time of the INC link), from `T1`: `mergeLink_sep'`.

These fields were not affected by the former defect of `IncSep` (`ActivationIncSepFalse`: the
former flight fields `flyC`, `flyR`, `flyM`, `fl1`, `fl2` were unsatisfiable) and are unchanged
in the reformulated structure (side windows and the `RF_J` corner window).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r : ℕ}

/-- The routes of an `inc` instruction are those of `incSpecs`. -/
theorem isep_instrSpecs (hins : p[i]? = some (.inc r)) :
    instrSpecs p i = [(unitWL p i incDWL, incMkc p i (incG p i r) (incEc p i r)),
      (unitWL p i incRWL, incMkl p i r (incEl p i r))] := by
  rw [← incSpecs_eq]
  simp [instrSpecs, hins]

/-- **`IncSep.sepC` for the plan of every `inc` instruction** of a well-formed program. -/
theorem isep_sepC (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    RouteSepX (machPieces p) (machRegion p) (unitWL p i incDWL) (incPlan p i r).csC
      ((2010 : ℕ) : ℤ) := by
  have h := incLinks_sep hp hins (d := 0) (by norm_num) (T := 2010) (by norm_num)
    (unitWL p i incDWL, incMkc p i (incG p i r) (incEc p i r))
    (by rw [isep_instrSpecs hins]; exact List.mem_cons_self)
  rw [WL.shift_zero_rs] at h
  exact h

/-- **`IncSep.sepR` for the plan of every `inc` instruction** of a well-formed program. -/
theorem isep_sepR (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    RouteSepX (machPieces p) (machRegion p) (unitWL p i incRWL) (incPlan p i r).csR
      ((2010 : ℕ) : ℤ) := by
  have h := incLinks_sep hp hins (d := 0) (by norm_num) (T := 2010) (by norm_num)
    (unitWL p i incRWL, incMkl p i r (incEl p i r))
    (by rw [isep_instrSpecs hins]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  rw [WL.shift_zero_rs] at h
  exact h

/-- **The delay of the merge link is a multiple of `30`** for a valid plan. -/
theorem isep_T1_mod {P : IncPlan p i r} (hv : P.Valid) : ((P.T1 : ℤ) + 166 - 1080) % 30 = 0 := by
  have h := hv.T0lE
  simp only [IncPlan.T1]
  push_cast
  omega

/-- **`IncSep.sepM` for the plan of every `inc` instruction** of a well-formed program. -/
theorem isep_sepM (hp : p.WellFormed) (hins : p[i]? = some (.inc r)) :
    RouteSepX (machPieces p) (machRegion p) (incPlan p i r).gM (incPlan p i r).csM
      ((incPlan p i r).T1 : ℤ) := by
  have hv := incPlan_valid hp hins
  exact mergeLink_sep' hp (lt_numRegs_of_inc hins) (mergeUsed_of_inc hins) (isep_T1_mod hv)
    (T := ((incPlan p i r).T1 : ℤ)) (by omega)
    (unitWL p (p.length + r) haltDWL, mergeCorners p r (mergeE p r)) (by simp [mergeSpecs])

end LP

end LeanTheory.Life
