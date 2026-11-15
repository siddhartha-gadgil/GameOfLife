/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Salvos
public import LeanTheory.Theory.Life.UVBox

/-!
# The register diagonal as a process in the frame of the register circuit

Research notes `N-20`, `N-22`. The diagonal of the register `REG1` (block and salvos in flight,
`Theory/Life/Diagonal`) placed at the register (`translate (148, 240)`), as a process of the
network method: its footprint at generation `i` is the strip `wStrip Vs Vb i`, the strip of
`diagStrip` moved to the register.

* `diagW q K`: the diagonal at the register;
* `diagW_subset`: every generation lies in the strip;
* `diagW_reaction`: a window of its evolution as a reaction;
* `farApart_box_wStrip`, `farApart_uv_wStrip`: boxes far from the strip, in `v` or in `u`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- The register diagonal (block at `K`, salvos `q`) placed at the register circuit. -/
def diagW (q : List (Salvo × ℤ)) (K : ℤ) : Finset Cell := translate (148, 240) (flights q ∪ counter K)

/-- The strip of the register diagonal at the register, at generation `i`. -/
def wStrip (Vs Vb : ℤ) (i : ℕ) : Set Cell :=
  {c | -113 ≤ c.1 - c.2 ∧ c.1 - c.2 ≤ -70 ∧
    min (Vs + 2 * ((i / 4 : ℕ) : ℤ)) Vb + 388 ≤ c.1 + c.2}

/-- **Every generation of the register diagonal lies in its strip.** -/
theorem diagW_subset {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} (hv : DiagValid regParams Vs Vb K q)
    (i : ℕ) : (conway.evolve i (diagW q K) : Set Cell) ⊆ wStrip Vs Vb i := by
  intro c hc
  rw [diagW, Rule.evolve_translate, mem_coe, mem_translate] at hc
  obtain ⟨h1, h2, h3⟩ := diag_strip regParams regParams_good _ q Vs Vb K rfl hv i (mem_coe.2 hc)
  simp only [regParams, Prod.fst_sub, Prod.snd_sub] at h1 h2 h3
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **A window of the register diagonal**, from generation `m`, for `n` generations. -/
theorem diagW_reaction {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} (hv : DiagValid regParams Vs Vb K q)
    (m n m' : ℕ) (h : n + m = m') :
    Reaction (conway.evolve m (diagW q K)) (conway.evolve m' (diagW q K)) n
      (fun i => wStrip Vs Vb (i + m)) :=
  trajectory_reaction' (diagW_subset hv) m n m' h

/-- A box in `x, y` far below the strip in `v` is far from it. -/
theorem farApart_box_wStrip_v {a b lo hi Vs Vb : ℤ} {i : ℕ}
    (h1 : b + hi + 4 < Vs + 2 * ((i / 4 : ℕ) : ℤ) + 388) (h2 : b + hi + 4 < Vb + 388) :
    FarApart 2 (Box a b lo hi) (wStrip Vs Vb i) := by
  rintro x ⟨-, x2, -, x4⟩ y ⟨-, -, y3⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  rcases min_choice (Vs + 2 * ((i / 4 : ℕ) : ℤ)) Vb with hm | hm <;> rw [hm] at y3 <;> omega

/-- A box in `x, y` outside the lanes of the strip is far from it. -/
theorem farApart_box_wStrip_u {a b lo hi Vs Vb : ℤ} {i : ℕ} (h : b - lo + 4 < -113 ∨ -66 < a - hi) :
    FarApart 2 (Box a b lo hi) (wStrip Vs Vb i) := by
  rintro x ⟨x1, x2, x3, x4⟩ y ⟨y1, y2, -⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  omega

/-- A diagonal box far below the strip in `v` is far from it. -/
theorem farApart_uv_wStrip_v {U₁ U₂ V₁ V₂ Vs Vb : ℤ} {i : ℕ}
    (h1 : V₂ + 4 < Vs + 2 * ((i / 4 : ℕ) : ℤ) + 388) (h2 : V₂ + 4 < Vb + 388) :
    FarApart 2 (UVBox U₁ U₂ V₁ V₂) (wStrip Vs Vb i) := by
  rintro x ⟨-, -, -, x4⟩ y ⟨-, -, y3⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  rcases min_choice (Vs + 2 * ((i / 4 : ℕ) : ℤ)) Vb with hm | hm <;> rw [hm] at y3 <;> omega

/-- A diagonal box outside the lanes of the strip is far from it. -/
theorem farApart_uv_wStrip_u {U₁ U₂ V₁ V₂ Vs Vb : ℤ} {i : ℕ} (h : U₂ + 4 < -113 ∨ -66 < U₁) :
    FarApart 2 (UVBox U₁ U₂ V₁ V₂) (wStrip Vs Vb i) := by
  rintro x ⟨x1, x2, -, -⟩ y ⟨y1, y2, -⟩ ⟨n1, n2, n3, n4⟩
  push_cast at n1 n2 n3 n4
  omega

end LeanTheory.Life
