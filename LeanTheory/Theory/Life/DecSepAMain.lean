/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepA9

/-!
# Eight thread fields of `DecSepRest`: before the capture and after it

Research note `N-22`. For every `decJz` instruction of a well-formed program, the eight fields
`nQN`, `nQF`, `zQZ`, `zQF`, `nA2a`, `nA2b`, `zA2a`, `zA2b` of `DecSepRest` (`DecSepMain`), verbatim
(`dsepA_fields`): before the capture, the control, the register run and the answer are far from the
token and its pieces, and all of them from the pieces of the answer link (`DecSepA5`, `DecSepA8`);
after the capture, the rest of the register run is far from the end, and the rest and the end are
far from the pieces of the control, of the stations before `j` and of the token (`DecSepA6`,
`DecSepA9`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- **Eight thread fields of `DecSepRest`**, verbatim (`nQN`, `nQF`, `zQZ`, `zQF`, `nA2a`, `nA2b`,
`zA2a`, `zA2b`), for every `decJz` instruction of a well-formed program. -/
theorem dsepA_fields (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    (∀ t : ℕ, 4260 ≤ t → t < decCapN p i r →
      FarApart 2 (qFootN p i r t) (boxesOf (decLNu p i r) ∪ tokFootN p i r t)) ∧
    (∀ t : ℕ, 4260 ≤ t → t < decCapN p i r → ∀ g ∈ decLF0N p i r,
      FarApart 2 (qFootN p i r t ∪ (boxesOf (decLNu p i r) ∪ tokFootN p i r t)) g.box) ∧
    (∀ t : ℕ, 4260 ≤ t → t < decCapZ p i r →
      FarApart 2 (qFootZ p i r t) (boxesOf (decLZu p i r) ∪ tokFootZ p i r t)) ∧
    (∀ t : ℕ, 4260 ≤ t → t < decCapZ p i r → ∀ g ∈ decLF0Z p i r z,
      FarApart 2 (qFootZ p i r t ∪ (boxesOf (decLZu p i r) ∪ tokFootZ p i r t)) g.box) ∧
    (∀ t : ℕ, decCapN p i r ≤ t → t < decEndN p i r →
      FarApart 2 (restFootN p i r t) (boxesOf (decLFN p i r) ∪ finFootN p i r t)) ∧
    (∀ t : ℕ, decCapN p i r ≤ t → t < decEndN p i r →
      ∀ g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r,
      FarApart 2 (restFootN p i r t ∪ (boxesOf (decLFN p i r) ∪ finFootN p i r t)) g.box) ∧
    (∀ t : ℕ, decCapZ p i r ≤ t → t < decEndZ p i r z →
      FarApart 2 (restFootZ p i r t) (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t)) ∧
    (∀ t : ℕ, decCapZ p i r ≤ t → t < decEndZ p i r z →
      ∀ g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r,
      FarApart 2 (restFootZ p i r t ∪ (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t)) g.box) :=
  ⟨dsepA_nQN hi, dsepA_nQF hp hi, dsepA_zQZ hi, dsepA_zQF hp hi, dsepA_nA2a hp hi,
    dsepA_nA2b hp hi, dsepA_zA2a hp hi, dsepA_zA2b hp hi⟩

end LP

end LeanTheory.Life
