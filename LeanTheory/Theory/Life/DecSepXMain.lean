/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepX8

/-!
# The fields `nThr`, `zThr` and `zGate` of `DecSepRest`

Research note `N-22`. The three fields of `DecSepRest` (`DecSepMain`) about the two threads of a
`decJz` activation against each other and against the INC gate, proved for every `decJz`
instruction of a well-formed program (`dsepX_fields`):

* `nThr`: the main thread of an NZ activation against the thread of the unpaired `KZ`
  (`dsepX_nThr`; the one pair that needs timing is the answer link against `KZ`, which meets
  its last band corner before the answer is dispatched);
* `zThr`: the main thread of a Z activation against the thread of the unpaired `KNZ`
  (`dsepX_zThr`);
* `zGate`: both threads of a Z activation against the tight footprint of the INC gate
  (`dsepX_zGate`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- **The fields `nThr`, `zThr`, `zGate` of `DecSepRest`**, verbatim, for every `decJz`
instruction of a well-formed program. -/
theorem dsepX_fields (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    (∀ t : ℕ, 4260 ≤ t → t < decEndN p i r →
      FarApart 2 (footMN p i r t) (boxesOf (decLZu p i r) ∪ unpFootZ p i r t)) ∧
    (∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z →
      FarApart 2 (footMZ p i r z t) (boxesOf (decLNu p i r) ∪ unpFootN p i r t)) ∧
    (∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z →
      FarApart 2 (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪ unpFootN p i r t))
        (gateFoot p r)) :=
  ⟨dsepX_nThr hp hi, dsepX_zThr hp hi, dsepX_zGate hp hi⟩

end LP

end LeanTheory.Life
