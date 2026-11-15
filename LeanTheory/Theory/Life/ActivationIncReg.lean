/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncCompose
public import LeanTheory.Theory.Life.DiagSmall
public import LeanTheory.Theory.Life.RegisterCircuit
public import LeanTheory.Theory.Life.Gen.Dz2eRunG
public import LeanTheory.Theory.Life.Gen.Dz2e1RunG
public import LeanTheory.Theory.Life.Gen.Dz2e2RunG
public import LeanTheory.Theory.Life.Gen.Dz2e3RunG
public import LeanTheory.Theory.Life.Gen.Dz2jAllG

/-!
# The increment at the module, for every register value

The register end of the `inc` activation (research note `N-22`, item (h)): the input glider of
the increment at module `r` (`incInWL` at time `0`, module frame), the register circuit at rest
(`dz2gRest`) and the register diagonal become, `d` generations later (`6990 ≤ d ≤ 7050`), the
circuit in its cycle and the register holding one more.

* **Readiness** (`RegS.Ready`): the invariant, `Vb = 18` and the salvos at least `29` behind
  (`QBeforeL 29`); kept with time (`RegS.Ready.later`).
* **Large values** (`R.Vb + 14 ≤ 2 w`): the pushing salvo of the phase `incPhase R.m` joins the
  queue (`dz2eOp`, `dz2e1Op` … `dz2e3Op` with `RegS.pushAny_join`), `d = 6990`.
* **Small values** (`w ≤ 15`, `RegS.push_dichotomy`): the diagonal is the static block
  `reg1Block w` and the increment is `dz2jAllR w` (`d = 4 w + 6990`), the register afterwards is
  `RegS.block (w + 1)`.
* `regInc_module`: both cases at module `r`, with the **exact** evolution as footprint and its
  inclusion in the (translated) box of the runs and the lanes of the diagonal; separation from
  the other pieces of the module (`RF_J`, the INC gate) is left to refined footprints.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

set_option maxRecDepth 100000 in
/-- The circuit of the increment `dz2e` is `dz2gRest`. -/
theorem dz2eRest_eq_g : dz2eRest = dz2gRest := by
  simp only [dz2eRest, dz2gRest, show dz2eR0 = dz2gR0 from rfl, show dz2eR1 = dz2gR1 from rfl,
    show dz2eR2 = dz2gR2 from rfl, show dz2eR3 = dz2gR3 from rfl, show dz2eR4 = dz2gR4 from rfl,
    show dz2eR5 = dz2gR5 from rfl, show dz2eR6 = dz2gR6 from rfl, show dz2eR7 = dz2gR7 from rfl,
    show dz2eR8 = dz2gR8 from rfl, show dz2eR9 = dz2gR9 from rfl, show dz2eR10 = dz2gR10 from rfl,
    show dz2eR11 = dz2gR11 from rfl, show dz2eR12 = dz2gR12 from rfl,
    show dz2eR13 = dz2gR13 from rfl, show dz2eR14 = dz2gR14 from rfl,
    show dz2eR15 = dz2gR15 from rfl, show dz2eR16 = dz2gR16 from rfl,
    show dz2eR17 = dz2gR17 from rfl, show dz2eR18 = dz2gR18 from rfl,
    show dz2eR19 = dz2gR19 from rfl, show dz2eR20 = dz2gR20 from rfl,
    show dz2eR21 = dz2gR21 from rfl, show dz2eR22 = dz2gR22 from rfl,
    show dz2eR23 = dz2gR23 from rfl, show dz2eR24 = dz2gR24 from rfl,
    show dz2eR25 = dz2gR25 from rfl, show dz2eR26 = dz2gR26 from rfl,
    show dz2eR27 = dz2gR27 from rfl]

namespace LP

/-- **A register ready for an increment**: the invariant, `Vb = 18` and the salvos in flight at
least `29` behind. -/
def RegS.Ready (R : RegS) : Prop := R.Inv ∧ R.Vb = 18 ∧ QBeforeL 29 R.q R.m

/-- Readiness is kept with time. -/
theorem RegS.Ready.later {R : RegS} (h : R.Ready) (n : ℕ) : (R.later n).Ready :=
  ⟨h.1.later n, h.2.1, h.2.2.mono (by simp [RegS.later])⟩

/-- A reaction with the exact evolution as footprint. -/
theorem Reaction.exact {P Q : Finset Cell} {n : ℕ} (h : conway.evolve n P = Q) :
    Reaction P Q n (fun i => (conway.evolve i P : Set Cell)) :=
  ⟨h, fun _ _ => subset_rfl⟩

/-- The region of the increment runs (module frame): the regions of the four phases of `dz2e`
and of `dz2jAll` (unions of components, `RunRegion`). -/
def incRunBox : Set Cell :=
  dz2eRegion ∪ dz2e1Region ∪ dz2e2Region ∪ dz2e3Region ∪ dz2jRegion

/-- **The increment in the module frame, for every register value.** -/
theorem regInc_frame {R : RegS} (hR : R.Ready) :
    ∃ (d : ℕ) (R' : RegS), 6990 ≤ d ∧ d ≤ 7050 ∧ R'.val = R.val + 1 ∧ R'.Ready ∧
      Reaction (dz2gRest ∪ incInWL.cells 0 ∪ conway.evolve R.m (diagW R.q R.K))
        (conway.evolve (d - 6990) dz2gRest ∪ conway.evolve R'.m (diagW R'.q R'.K)) d
        (fun _ => incRunBox) := by
  obtain ⟨hI, hVb, hQ⟩ := hR
  rcases RegS.push_dichotomy hI hVb hQ with hz | ⟨hw, hs⟩
  · obtain ⟨hv', hVs'⟩ := RegS.pushAny_join hI (hQ.toQBefore (by norm_num)) hz
    refine ⟨6990, R.pushAny R.pushVs, le_rfl, by norm_num, RegS.val_pushAny R hI _,
      ⟨RegS.inv_pushAny hI hv' hVs', hVb, QBeforeL.pushAny (by norm_num) hQ⟩, ?_⟩
    rw [incInWL_cells, Nat.sub_self, Rule.evolve_zero, ← dz2eRest_eq_g]
    simp only [RegS.pushAny, pushOf] at hv' hVs' ⊢
    have h4 : (R.m + 6653) % 4 = 0 ∨ (R.m + 6653) % 4 = 3 ∨ (R.m + 6653) % 4 = 2 ∨
        (R.m + 6653) % 4 = 1 := by omega
    rcases h4 with h | h | h | h
    · rw [show incPhase R.m = 0 by simp only [incPhase]; omega] at hv' hVs' ⊢
      simp only [pushSalvo, pushBase, add_zero] at hv' hVs' ⊢
      refine (dz2eOpG R.q R.K R.Vs R.Vb _ R.m hI.1 hv' h hI.2.1 hI.2.2.1
        hVs').mono fun _ _ => ?_
      simp only [incRunBox]
      intro x hx
      simp [hx]
    · rw [show incPhase R.m = 1 by simp only [incPhase]; omega,
        show R.m + 6653 + 1 = R.m + 6654 by omega] at hv' hVs' ⊢
      simp only [pushSalvo, pushBase] at hv' hVs' ⊢
      rw [← dz2e1Rest_eq]
      refine (dz2e1OpG R.q R.K R.Vs R.Vb _ R.m hI.1 hv' (by omega) hI.2.1 hI.2.2.1
        hVs').mono fun _ _ => ?_
      simp only [incRunBox]
      intro x hx
      simp [hx]
    · rw [show incPhase R.m = 2 by simp only [incPhase]; omega,
        show R.m + 6653 + 2 = R.m + 6655 by omega] at hv' hVs' ⊢
      simp only [pushSalvo, pushBase] at hv' hVs' ⊢
      rw [← dz2e2Rest_eq]
      refine (dz2e2OpG R.q R.K R.Vs R.Vb _ R.m hI.1 hv' (by omega) hI.2.1 hI.2.2.1
        hVs').mono fun _ _ => ?_
      simp only [incRunBox]
      intro x hx
      simp [hx]
    · rw [show incPhase R.m = 3 by simp only [incPhase]; omega,
        show R.m + 6653 + 3 = R.m + 6656 by omega] at hv' hVs' ⊢
      simp only [pushSalvo, pushBase] at hv' hVs' ⊢
      rw [← dz2e3Rest_eq]
      refine (dz2e3OpG R.q R.K R.Vs R.Vb _ R.m hI.1 hv' (by omega) hI.2.1 hI.2.2.1
        hVs').mono fun _ _ => ?_
      simp only [incRunBox]
      intro x hx
      simp [hx]
  · have hv0 := hI.2.2.2
    set w := R.K + qMove R.q with hwdef
    refine ⟨4 * w.toNat + 6990, RegS.block (w.toNat + 1) (R.m + 4 * w.toNat + 6990),
      by omega, by omega, ?_, ⟨RegS.inv_block _ _, RegS.Vb_block _ _, RegS.qBeforeL_block _ _ _⟩,
      ?_⟩
    · rw [RegS.val_block]
      simp only [RegS.val]
      omega
    · have h := dz2jAllG w.toNat (Nat.zero_le _)
      rw [dz2jRest_eq, show ((w.toNat : ℕ) : ℤ) = w from Int.toNat_of_nonneg hv0] at h
      rw [incInWL_cells, hs, RegS.diagW_block, show 4 * w.toNat + 6990 - 6990 = 4 * w.toNat by
        omega]
      push_cast
      rw [Int.toNat_of_nonneg hv0]
      refine h.mono fun _ _ x hx => ?_
      simp only [incRunBox]
      simp [hx]

set_option maxRecDepth 100000 in
/-- **The increment at module `r`, for every register value**: the circuit at rest of module
`r` with the input glider, and the register diagonal, become the circuit in its cycle and the
diagonal of the register holding one more; the footprint is the exact evolution, inside the region
of the runs (translated to the module). -/
theorem regInc_module (p : Program) (r : ℕ) {R : RegS} (hR : R.Ready) :
    ∃ (d : ℕ) (R' : RegS), 6990 ≤ d ∧ d ≤ 7050 ∧ R'.val = R.val + 1 ∧ R'.Ready ∧
      conway.evolve d
          (translate (modDX p r, modDY p r) (dz2gRest ∪ incInWL.cells 0) ∪ regAt p r R) =
        translate (modDX p r, modDY p r) (conway.evolve (d - 6990) dz2gRest) ∪ regAt p r R' ∧
      ∀ i ≤ d, (conway.evolve i
          (translate (modDX p r, modDY p r) (dz2gRest ∪ incInWL.cells 0) ∪ regAt p r R) :
            Set Cell) ⊆ (fun c => (modDX p r, modDY p r) + c) '' incRunBox := by
  obtain ⟨d, R', h1, h2, h3, h4, h⟩ := regInc_frame hR
  have ht := h.translate (modDX p r, modDY p r)
  rw [translate_union, translate_union] at ht
  refine ⟨d, R', h1, h2, h3, h4, ?_, fun i hi => ?_⟩
  · simp only [regAt, translate_union]
    rw [ht.evolve_eq, translate_union]
  · simp only [regAt, translate_union]
    exact ht.subset i hi

end LP

end LeanTheory.Life
