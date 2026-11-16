/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepX6

/-!
# The field `nThr` of `DecSep`

Research note `N-22`. The main thread of an NZ activation (footprint `footMN`) against the thread
of the unpaired `KZ` (its reflectors, station `j` of the line Z, and its footprint `unpFootZ`),
for every `decJz` instruction of a well-formed program (`dsepX_nThr`):

* the pieces of the two threads are far apart (`dsepX_LMN_LZu`);
* each moving part of one thread is far from the pieces of the other (the routes by the route
  fields, the rest in coordinates);
* the moving parts are far apart: the loops of `C` and `KNZ` contain the loop of `KZ`
  (`dsepX_C_KZ`, `dsepX_N_KZ`), the module parts are left of the right zone (`dsepX_MR_KZ`), and
  **the answer link after its dispatch** is left of `u = U_r - 300` while `KZ` is then already
  right of `u = U_r + 1150` (`dsepX_finN_late`, `dsepX_unpZ_late`: `KZ` meets its last band corner
  at least `20` generations before the dispatch).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

variable {p : Program} {i r z : ℕ}

/-- A set far from the thread of the unpaired `KZ` at time `t`. -/
def dsepXOkN (p : Program) (i r t : ℕ) (X : Set Cell) : Prop :=
  FarApart 2 X (boxesOf (decLZu p i r) ∪ unpFootZ p i r t)

/-- Unions of sets far from the thread of `KZ`. -/
theorem dsepXOkN.union {t : ℕ} {X Y : Set Cell} (hX : dsepXOkN p i r t X)
    (hY : dsepXOkN p i r t Y) : dsepXOkN p i r t (X ∪ Y) := dsepT_far_union hX hY

/-- Membership in the main thread of an NZ activation. -/
theorem dsepX_mem_LMN {x : Piece} (h : x ∈ decLC p i r ∨ x ∈ modGroup p r ∨ x ∈ decLSN p i r ∨
    x ∈ decLNu p i r ∨ x ∈ decLF0N p i r) : x ∈ decLMN p i r := by
  simp only [decLMN, List.mem_append]
  rcases h with h | h | h | h | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- The pieces of the main thread of an NZ activation are pieces of the machine. -/
theorem dsepX_LMN_mem (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLMN p i r, x ∈ machPieces p := by
  intro x hx
  have hr := lt_numRegs_of_dec hi
  simp only [decLMN, List.mem_append] at hx
  rcases hx with (((h | h) | h) | h) | h
  · exact decLC_mem hi x h
  · exact modGroup_mem hr x h
  · exact decLSN_mem hi x h
  · exact decLNu_mem hi x h
  · refine decLFN_mem hp hi x (mem_dd.2 ?_)
    rcases List.mem_append.1 (mem_dd.1 h) with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h

/-- A piece of the main thread of an NZ activation is not a piece of the thread of `KZ`. -/
theorem dsepX_LMN_not (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {g : Piece}
    (hg : g ∈ decLMN p i r) (hz : g ∈ decLZu p i r) : False :=
  dsepX_ne_of_far (dsepX_LMN_mem hp hi g hg) (dsepX_LMN_LZu hp hi g hg g hz) rfl

/-- **The pieces of the main thread are far from the thread of `KZ`.** -/
theorem dsepX_okN_static (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) {L : List Piece} (hL : ∀ x ∈ L, x ∈ decLMN p i r) :
    dsepXOkN p i r t (boxesOf L) := by
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_
  · exact (farApart_boxesOf fun g hg => (dsepX_LMN_LZu hp hi g (hL g hg) h hh).symm').symm'
  · refine (farApart_boxesOf fun g hg => ?_).symm'
    have hg' := hL g hg
    have hcls := dsepX_LMN_cls hp hi g hg'
    refine dsepX_split_far (fun x hx => dsepX_unpZ_split hi h0 hx) ?_ ?_
    · intro x hx y hy
      exact dsepX_Z_route_far hp hi hx.1 (dsepX_LMN_mem hp hi g hg')
        (fun hz => dsepX_LMN_not hp hi hg' (mem_dd.2 (List.mem_append_left _ hz))) x hx.2 y hy
    · intro x hx y hy
      have := hcls y hy
      omega

/-- A set in the module part of the NZ thread is far from the thread of `KZ`. -/
theorem dsepX_okN_MR (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) {S : Set Cell} (hS : S ⊆ dsepXMR p r) : dsepXOkN p i r t S := by
  have hD := one_le_D p
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_)
    ((dsepX_MR_KZ hi).mono hS (dsepX_unpZ_sub hi h0))
  have hcls := dsepX_LZu_cls hp hi h hh
  refine dsepT_far_cells fun a ha b hb => ?_
  have := hS ha
  have := hcls b hb
  simp only [dsepXMR, Set.mem_ofPred_eq] at *
  omega

/-- **The control `C` is far from the thread of `KZ`.** -/
theorem dsepX_okN_footC (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (ht : t ≤ decTS p i r) : dsepXOkN p i r t (decFootC p i r t) := by
  have hD := one_le_D p
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_)
    ((dsepX_C_KZ hi).mono (dsepX_footC_sub hi h0 ht) (dsepX_unpZ_sub hi h0))
  have hcls := dsepX_LZu_cls hp hi h hh
  have hm : h ∈ machPieces p := decLZu_mem hi h hh
  refine dsepX_split_far (fun x hx => dsepX_footC_split hi h0 ht hx) ?_ ?_
  · intro x hx y hy
    refine dsepX_C_route_far hp hi hx.1 hm (fun hc => ?_) x hx.2 y hy
    exact dsepX_LMN_not hp hi
      (dsepX_mem_LMN (Or.inl (mem_dd.2 (List.mem_append_left _ hc)))) hh
  · intro x hx y hy
    have := hcls y hy
    omega

/-- **The token `KNZ` is far from the thread of `KZ`.** -/
theorem dsepX_okN_tokN (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) (ht : t ≤ decCapN p i r) : dsepXOkN p i r t (tokFootN p i r t) := by
  have hD := one_le_D p
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_)
    ((dsepX_N_KZ hi).mono (dsepX_tokN_sub hi h0 ht) (dsepX_unpZ_sub hi h0))
  have hcls := dsepX_LZu_cls hp hi h hh
  have hm : h ∈ machPieces p := decLZu_mem hi h hh
  obtain ⟨-, -, -, -, l5, -, -⟩ := dsepX_n_layout hi
  refine dsepX_split_far (fun x hx => dsepX_tokN_split hi h0 ht hx) ?_ ?_
  · intro x hx y hy
    refine dsepX_N_route_far hp hi hx.1 hm (fun hc => ?_) x hx.2 y hy
    exact dsepX_LMN_not hp hi
      (dsepX_mem_LMN (Or.inr (Or.inr (Or.inr (Or.inl (mem_dd.2 (List.mem_append_left _ hc))))))) hh
  · intro x hx y hy
    have := hcls y hy
    omega

/-- **The end of the NZ activation is far from the thread of `KZ`**: the capture and the answer
link before the dispatch in the module part; after the dispatch, the answer link left of
`U_r - 300` and `KZ` right of `U_r + 1150`. -/
theorem dsepX_okN_fin (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h1 : decCapN p i r ≤ t) (h2 : t < decEndN p i r) : dsepXOkN p i r t (finFootN p i r t) := by
  have hD := one_le_D p
  have h0 : 4260 ≤ t := by
    have := (decTS_facts p hi).2.2; unfold decCapN decTS at h1; omega
  refine dsepT_far_union_r (farApart_boxesOf fun h hh => ?_) ?_
  · have hcls := dsepX_LZu_cls hp hi h hh
    have hm : h ∈ machPieces p := decLZu_mem hi h hh
    refine dsepX_finN_far hp hi h1 h2 hm (fun hc => ?_) (fun hc => ?_) ?_
    · exact dsepX_LMN_not hp hi (dsepX_mem_LMN (Or.inr (Or.inr (Or.inr (Or.inr
        (mem_dd.2 (List.mem_append_left _ hc))))))) hh
    · exact dsepX_LMN_not hp hi (dsepX_mem_LMN (Or.inr (Or.inr (Or.inr (Or.inr
        (mem_dd.2 (List.mem_append_right _ hc))))))) hh
    · refine dsepT_far_cells fun a ha b hb => ?_
      have := ha.2
      have := hcls b hb
      simp only [Set.mem_ofPred_eq] at *
      omega
  · by_cases hd : t ≤ decDispN p i r
    · have hc : finFootN p i r t ⊆ dsepXMR p r := by
        intro x hx
        unfold finFootN at hx
        simp only [hd, ↓reduceIte] at hx
        have eD : decCapN p i r + 692 = decDispN p i r := by unfold decCapN decDispN; omega
        exact (dsepX_capN_M hi (k := t - decCapN p i r) (by omega) hx).1
      exact (dsepX_MR_KZ hi).mono hc (dsepX_unpZ_sub hi h0)
    · refine dsepT_far_cells fun a ha b hb => ?_
      have := dsepX_finN_late hp hi (by omega) h2 ha
      have := dsepX_unpZ_late hi (t := t) (by omega) hb
      simp only [Set.mem_ofPred_eq] at *
      omega

/-- The rest of the NZ register run is far from the thread of `KZ`. -/
theorem dsepX_okN_rest (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) {t : ℕ}
    (h0 : 4260 ≤ t) : dsepXOkN p i r t (restFootN p i r t) := by
  unfold restFootN
  split_ifs with h
  · exact dsepX_okN_MR hp hi h0 ((dsepX_modImg_H dsepX_restNZ_H).trans
      Set.inter_subset_left)
  · exact (dsepX_okN_static hp hi h0 fun x hx => dsepX_mem_LMN (Or.inr (Or.inl hx))).union
      (dsepX_okN_MR hp hi h0 (dsepX_lanes_M.trans Set.inter_subset_left))

/-- **`DecSep.nThr`**: the main thread of an NZ activation is far from the thread of the unpaired
`KZ` at every generation. -/
theorem dsepX_nThr (hp : p.WellFormed) (hi : p[i]? = some (.decJz r z)) :
    ∀ t : ℕ, 4260 ≤ t → t < decEndN p i r →
      FarApart 2 (footMN p i r t) (boxesOf (decLZu p i r) ∪ unpFootZ p i r t) := by
  intro t h0 h1
  have hLC : ∀ x ∈ decLC p i r, x ∈ decLMN p i r := fun x hx => dsepX_mem_LMN (Or.inl hx)
  have hG : ∀ x ∈ modGroup p r, x ∈ decLMN p i r := fun x hx =>
    dsepX_mem_LMN (Or.inr (Or.inl hx))
  have hSN : ∀ x ∈ decLSN p i r, x ∈ decLMN p i r := fun x hx =>
    dsepX_mem_LMN (Or.inr (Or.inr (Or.inl hx)))
  have hNu : ∀ x ∈ decLNu p i r, x ∈ decLMN p i r := fun x hx =>
    dsepX_mem_LMN (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  have hF0 : ∀ x ∈ decLF0N p i r, x ∈ decLMN p i r := fun x hx =>
    dsepX_mem_LMN (Or.inr (Or.inr (Or.inr (Or.inr hx))))
  have hLN : ∀ x ∈ decLN p i r, x ∈ decLMN p i r := fun x hx =>
    hNu x (mem_dd.2 (List.mem_append_left _ (mem_dd.1 hx)))
  have hFN : ∀ x ∈ decLFN p i r, x ∈ decLMN p i r := by
    intro x hx
    rcases List.mem_append.1 (mem_dd.1 hx) with h | h
    · rcases List.mem_append.1 h with h | h
      · exact hNu x (mem_dd.2 (List.mem_append_right _ h))
      · exact hF0 x (mem_dd.2 (List.mem_append_left _ h))
    · exact hF0 x (mem_dd.2 (List.mem_append_right _ h))
  have happ : ∀ {A B : List Piece}, (∀ x ∈ A, x ∈ decLMN p i r) →
      (∀ x ∈ B, x ∈ decLMN p i r) → ∀ x ∈ A ++ B, x ∈ decLMN p i r := by
    intro A B hA hB x hx
    rcases List.mem_append.1 hx with h | h
    · exact hA x h
    · exact hB x h
  have hst := fun {L : List Piece} (hL : ∀ x ∈ L, x ∈ decLMN p i r) =>
    dsepX_okN_static hp hi h0 hL
  have hMR := fun {S : Set Cell} (hS : S ⊆ dsepXMR p r) => dsepX_okN_MR hp hi h0 hS
  change dsepXOkN p i r t (footMN p i r t)
  unfold footMN
  split_ifs with hc
  · refine (hst hF0).union ((?_ : dsepXOkN p i r t (qFootN p i r t)).union
      ((hst hNu).union (dsepX_okN_tokN hp hi h0 hc)))
    unfold qFootN
    split_ifs with ha hb
    · exact (hst (happ hG hSN)).union (((hst hLC).union (dsepX_okN_footC hp hi h0 ha)).union
        (hMR (dsepX_lanes_M.trans Set.inter_subset_left)))
    · exact (hst (happ hLC hSN)).union
        (hMR ((dsepX_modImg_H dsepX_runNZ_H).trans Set.inter_subset_left))
    · exact (hst hLC).union ((dsepX_okN_rest hp hi h0).union ((hst hSN).union
        (hMR (dsepX_ansN_M hi (by omega)))))
  · exact (hst (happ (happ hLC hSN) hLN)).union ((dsepX_okN_rest hp hi h0).union
      ((hst hFN).union (dsepX_okN_fin hp hi (by omega) h1)))

end LP

end LeanTheory.Life
