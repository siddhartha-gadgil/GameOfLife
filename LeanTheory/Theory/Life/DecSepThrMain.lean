/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepThr5

/-!
# The thread fields of `DecSep` proved so far

Research note `N-22`. Of the `23` thread fields of `DecSepRest`, the eight fields about the
control thread before the run, the run before the cut and the rest of the run after the cut,
against the circuit, the stations and the answer, are proved for every `decJz` instruction of a
well-formed program (`dsepT_fields8`): `nQ1b`, `nQ2`, `nQ3a`, `nQ3b`, `zQ1b`, `zQ2`, `zQ3a`,
`zQ3b`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- **Eight thread fields of `DecSepRest`**, verbatim (`nQ1b`, `nQ2`, `nQ3a`, `nQ3b`, `zQ1b`,
`zQ2`, `zQ3a`, `zQ3b`), for every `decJz` instruction of a well-formed program. -/
theorem dsepT_fields8 (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    (∀ t : ℕ, 4260 ≤ t → t < decTS p i r → ∀ g ∈ modGroup p r ++ decLSN p i r,
      FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r) g.box) ∧
    (∀ g ∈ decLC p i r ++ decLSN p i r, FarApart 2 (modImg p r decRunRegNZ) g.box) ∧
    (∀ t : ℕ, decCutN p i r ≤ t → t < decCapN p i r →
      FarApart 2 (restFootN p i r t) (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t)) ∧
    (∀ t : ℕ, decCutN p i r ≤ t → t < decCapN p i r → ∀ g ∈ decLC p i r,
      FarApart 2 (restFootN p i r t ∪ (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t)) g.box) ∧
    (∀ t : ℕ, 4260 ≤ t → t < decTS p i r → ∀ g ∈ modGroup p r ++ decLSZ p i r,
      FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r) g.box) ∧
    (∀ g ∈ decLC p i r ++ decLSZ p i r, FarApart 2 (modImg p r decRunRegZ) g.box) ∧
    (∀ t : ℕ, decCutZ p i r ≤ t → t < decCapZ p i r →
      FarApart 2 (restFootZ p i r t) (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t)) ∧
    (∀ t : ℕ, decCutZ p i r ≤ t → t < decCapZ p i r → ∀ g ∈ decLC p i r,
      FarApart 2 (restFootZ p i r t ∪ (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t)) g.box) :=
  ⟨dsepT_nQ1b hp hi, dsepT_nQ2 hp hi, dsepT_nQ3a hp hi, dsepT_nQ3b hp hi, dsepT_zQ1b hp hi,
    dsepT_zQ2 hp hi, dsepT_zQ3a hp hi, dsepT_zQ3b hp hi⟩

end LP

end LeanTheory.Life
