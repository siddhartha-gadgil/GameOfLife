/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncCompose
public import LeanTheory.Theory.Life.ActivationIncModuleRun
public import LeanTheory.Theory.Life.Decision

/-!
# The halt activation of the simulator

The `halt` field of a `Simulator` (research note `N-22`, report `R-31` §6) for the machine of
`LayoutPieces` / `MachineState`: in a state whose instruction is `halt`, the control glider at the
entrance of the halt unit flies (there is no body: the halt template is the entry chain only, its
output `D` is the line of the control) to the one corner of `haltCorners` on the top track
`v = V_T + 1`, is turned `SW` by the reflector there, and then flies `SW` along `v = V_T + 1` for
ever; the rest of the machine idles and the registers' diagonals evolve on their own.

* **Layout arithmetic, proved**: `ctrlWL_eq`, `haltCorner_uv`, `haltLines`, `haltMeet` (the
  corner is met at time `2857`), `haltOutWL_eq` (the outgoing world line is `SW` with lane
  `x + y = V_T + 1`), `haltRf_eq`, `haltRfP_mem` (the reflector placed by the layout for the halt
  route is a piece of the machine and turns the control: the delays differ by
  `1080 ≡ 0 (mod 30)`).
* **The reflection with its approach and departure** (`rf3_ph10`, `rf3_approach`, `rf3_depart`,
  `rf3_early`, `reflect_early`, `halt_relay`): one generation before `meetT` the incoming glider's
  box touches the reflector's box (`not_far_before_meet`), and one generation after the relay
  the outgoing glider's box does too, so the flight cannot be run beside the idle reflector up to
  `meetT` (the flight clause of `RouteSep` / `RouteSepM` cannot hold). Here the reflector and the
  glider are run jointly from `meetT - 20 = 2837` to `meetT + 40 = 2897`, by new certificates.
* **Correction of the halt cell**: the `SW` glider of lane `V_T + 1` occupies only cells with
  `x + y ∈ [V_T + 2, V_T + 5]`, while `haltCell` has `x + y ∈ {V_T - 1, V_T}`: **`haltCell` is
  never hit**. The corrected cell `haltCellC` has `u = x - y = u_min - 600` (as `haltCell`) and
  `v = x + y = V_T + 4 - (u mod 2)`: it is a cell of phase `0` of the glider at the time
  `haltTime` (`haltCellC_mem`), and it is still outside the region (`haltCellC_notMem`).
* **Separation**, as an explicit hypothesis `HaltSep`: the flights and the relay are far from the
  idle pieces, and the lanes of the registers are far from each other and from the machine and the
  halt glider.
* **The halt lemma** `halt_everAlive`: for a well-formed program and a state with `InvM` whose
  step is `none`, under `HaltSep`, the corrected halt cell is ever alive in the evolution of
  `encM p s`.

**Caveat** (layout): `HaltSep.fly` fails when a halt instruction `a' < a` exists: its halt corner
lies on the same track `v ∈ [V_T, V_T + 1]` at `u = A_{a'} + 14`, on the path of the `SW` glider.
`R-31` assumes the normal form with exactly one `halt` (§2).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The halt route -/

/-- The corner of the halt link of unit `a` (the only corner of `haltCorners p a`). -/
def haltCorner (p : Program) (a : ℕ) : Corner :=
  ⟨3, A p a + haltD, trackOut p 0 0 (A p a + haltD), .halt a⟩

/-- The halt link is the one corner `haltCorner`. -/
theorem haltCorners_eq (p : Program) (a : ℕ) : haltCorners p a = [haltCorner p a] := rfl

/-- The corner point of the halt corner: `(A_a + 14, V_T + 1)`. -/
theorem haltCorner_uv (p : Program) (a : ℕ) :
    (haltCorner p a).u = A p a + 14 ∧ (haltCorner p a).v = VT p + 1 := by
  have := A_even p a
  have := VT_mod p
  refine ⟨rfl, ?_⟩
  simp only [haltCorner, haltD, trackOut, track]
  omega

/-- The control world line of unit `a`: `SE` on lane `A_a + 14`. -/
theorem ctrlWL_eq (p : Program) (a : ℕ) :
    ctrlWL p a = ⟨1, 1, A p a + 14, -451 - 4 * unitDX p a⟩ := by
  have := unitD_uv p a
  simp only [ctrlWL, unitWL, WL.shift, WL.mk.injEq, true_and]
  constructor <;> omega

/-- The control of unit `a` meets the halt corner at time `2857`. -/
theorem haltMeet (p : Program) (a : ℕ) : meetT (ctrlWL p a) (haltCorner p a) = 2857 := by
  have := unitD_uv p a
  have := A_even p a
  have := VT_mod p
  rw [ctrlWL_eq]
  simp only [meetT, delayS, haltCorner, rfIn, rfX, rfCU, rfCV, haltD, trackOut, track, VU] at *
  omega

/-- The glider after the halt corner. -/
def haltOutWL (p : Program) (a : ℕ) : WL := (reflect (ctrlWL p a) (haltCorner p a)).2

/-- **The outgoing world line**: `SW` on the lane `x + y = V_T + 1`. -/
theorem haltOutWL_eq (p : Program) (a : ℕ) :
    haltOutWL p a = ⟨-1, 1, VT p + 1, 2872 + 2 * (A p a + VT p + 10)⟩ := by
  have := unitD_uv p a
  have := A_even p a
  have := VT_mod p
  rw [haltOutWL, ctrlWL_eq]
  simp only [reflect, haltCorner, rfIn, rfOut, rfX, rfY, rfCU, rfCV, haltD, trackOut, track,
    WL.shift, WL.mk.injEq, VU, true_and] at *
  constructor <;> omega

/-- The control of unit `a` follows the halt route: it is on the input line of the corner. -/
theorem haltLines (p : Program) (a : ℕ) : RouteLines (ctrlWL p a) (haltCorners p a) := by
  refine ⟨?_, trivial⟩
  have := A_even p a
  have := VT_mod p
  refine onLine_of_through rfl rfl ?_ ?_
  · simp only [rfCU, rfCV, haltD, trackOut, track]
    omega
  · rw [ctrlWL_eq]
    simp only [WL.Through, haltD]
    ring

/-- The reflector of the halt corner placed by the layout (for the halt route of `instrSpecs`). -/
def haltRfP (p : Program) (a : ℕ) : Piece :=
  (reflect (unitWL p a haltDWL) (haltCorner p a)).1.piece

/-- **The layout's reflector is the one that turns the control**: the control is the layout's
glider `1080 ≡ 0 (mod 30)` generations early. -/
theorem haltRf_eq (p : Program) (a : ℕ) :
    (reflect (ctrlWL p a) (haltCorner p a)).1.piece = haltRfP p a := by
  simp only [haltRfP, reflect, ctrlWL, unitWL, WL.shift, haltDWL]
  congr 2
  omega

/-- **The reflector of the halt corner is a piece of the machine.** -/
theorem haltRfP_mem {p : Program} {a : ℕ} (hins : p[a]? = some .halt) :
    haltRfP p a ∈ machPieces p := by
  have ha : a < p.length := (List.getElem?_eq_some_iff.1 hins).1
  refine List.mem_map_of_mem ?_
  simp only [machSpecs, linksPart, List.mem_append, List.mem_flatMap]
  refine Or.inr (Or.inl ⟨a, List.mem_range.2 ha, ?_⟩)
  simp only [routeSpecs, instrSpecs, hins, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_left, haltCorners_eq, route]

/-! ### The reflection of the halt corner, from `20` generations early

The reflector's box comes within distance `2` of the incoming glider's box during the last
`16` generations before the meeting time `meetT` (for image `3`: the input glider at
`x ∈ [-1, 3]`, the reflector's box at `x ≥ 2`), so the flight cannot be run beside the idle
reflector up to `meetT`. Instead the reflector and the glider are run together from `20`
generations before `meetT` (`rf3_approach`, the reflector at phase `10`), then through the
reflection (`rf0SESW_relay`). -/

/-- **Certificate**: the reflector, image 3, ten generations after phase `0`. -/
theorem rf3_ph10 :
    Reaction (ofRows 2 (-22) [256, 448, 32, 96, 0, 8, 28, 34, 8, 65, 65, 34, 28, 0, 0, 0, 0,
        0, 0, 0, 0, 12, 12])
      (ofRows 2 (-22) [256, 448, 32, 96, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 34, 28, 28, 0, 0, 0, 0,
        12, 12]) 10 (fun _ => Box 2 10 (-22) 0) := by
  life_reaction

set_option maxRecDepth 100000 in
/-- **Certificate**: the approach: the reflector at phase `10` and the input glider `20`
generations before the input of `rf0SESW` become, without touching, the reflector at phase `0`
and that input. -/
theorem rf3_approach :
    Reaction (ofRows 2 (-22) [256, 448, 32, 96, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 34, 28, 28, 0, 0,
        0, 0, 12, 12] ∪ ofRows (-5) (-27) [2, 4, 7])
      (ofRows 2 (-22) [256, 448, 32, 96, 0, 8, 28, 34, 8, 65, 65, 34, 28, 0, 0, 0, 0, 0, 0, 0, 0,
        12, 12] ∪ ofRows 0 (-22) [2, 4, 7]) 20 (fun _ => Box (-5) 10 (-27) 0) := by
  rw [show ofRows 2 (-22) [256, 448, 32, 96, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 34, 28, 28, 0, 0,
        0, 0, 12, 12] ∪ ofRows (-5) (-27) [2, 4, 7] =
      ofRows (-5) (-27) [2, 4, 7, 0, 0, 32768, 57344, 4096, 12288, 0, 0, 0, 0, 0, 0, 0, 0,
        12672, 0, 4352, 3584, 3584, 0, 0, 0, 0, 1536, 1536] by
      rw [ofRows_eq_padRows' (-5) (-27) 2 (-22) 5 7 _ (by norm_num) (by norm_num),
        ofRows_eq_padRows' (-5) (-27) (-5) (-27) 0 0 _ (by norm_num) (by norm_num),
        ← ofRows_orRows]
      rfl,
    show ofRows 2 (-22) [256, 448, 32, 96, 0, 8, 28, 34, 8, 65, 65, 34, 28, 0, 0, 0, 0, 0, 0, 0,
        0, 12, 12] ∪ ofRows 0 (-22) [2, 4, 7] =
      ofRows 0 (-22) [1026, 1796, 135, 384, 0, 32, 112, 136, 32, 260, 260, 136, 112, 0, 0, 0, 0,
        0, 0, 0, 0, 48, 48] by
      rw [ofRows_eq_padRows' 0 (-22) 2 (-22) 0 2 _ (by norm_num) (by norm_num),
        ofRows_eq_padRows' 0 (-22) 0 (-22) 0 0 _ (by norm_num) (by norm_num), ← ofRows_orRows]
      rfl]
  life_reaction

set_option maxRecDepth 100000 in
/-- **Certificate**: the departure: the reflector at phase `0` and the output glider of
`rf0SESW` become, without touching, the reflector at phase `10` and the glider `10` generations
later. -/
theorem rf3_depart :
    Reaction (ofRows 2 (-22) [256, 448, 32, 96, 0, 8, 28, 34, 8, 65, 65, 34, 28, 0, 0, 0, 0, 0, 0,
        0, 0, 12, 12] ∪ ofRows (-4) (-13) [4, 3, 6])
      (ofRows 2 (-22) [256, 448, 32, 96, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 34, 28, 28, 0, 0, 0, 0,
        12, 12] ∪ ofRows (-6) (-10) [5, 3, 2]) 10 (fun _ => Box (-6) 10 (-22) 0) := by
  rw [show ofRows 2 (-22) [256, 448, 32, 96, 0, 8, 28, 34, 8, 65, 65, 34, 28, 0, 0, 0, 0, 0, 0,
        0, 0, 12, 12] ∪ ofRows (-4) (-13) [4, 3, 6] =
      ofRows (-4) (-22) [16384, 28672, 2048, 6144, 0, 512, 1792, 2176, 512, 4164, 4163, 2182,
        1792, 0, 0, 0, 0, 0, 0, 0, 0, 768, 768] by
      rw [ofRows_eq_padRows' (-4) (-22) 2 (-22) 0 6 _ (by norm_num) (by norm_num),
        ofRows_eq_padRows' (-4) (-22) (-4) (-13) 9 0 _ (by norm_num) (by norm_num),
        ← ofRows_orRows]
      rfl,
    show ofRows 2 (-22) [256, 448, 32, 96, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 34, 28, 28, 0, 0, 0, 0,
        12, 12] ∪ ofRows (-6) (-10) [5, 3, 2] =
      ofRows (-6) (-22) [65536, 114688, 8192, 24576, 0, 0, 0, 0, 0, 0, 0, 0, 25349, 3, 8706,
        7168, 7168, 0, 0, 0, 0, 3072, 3072] by
      rw [ofRows_eq_padRows' (-6) (-22) 2 (-22) 0 8 _ (by norm_num) (by norm_num),
        ofRows_eq_padRows' (-6) (-22) (-6) (-10) 12 0 _ (by norm_num) (by norm_num),
        ← ofRows_orRows]
      rfl]
  life_reaction

/-- **The early relay of image 3**: the reflector at phase `10` and the input glider `20`
generations early become the reflector at phase `10` and the output glider `10` generations
after the output of `rf0SESW`, in `60` generations, inside `Box (-6) 10 (-27) 0`. -/
theorem rf3_early :
    Reaction (conway.evolve 10 rf0SESW.G ∪ ofRows (-5) (-27) [2, 4, 7])
      (conway.evolve 10 rf0SESW.G ∪ ofRows (-6) (-10) [5, 3, 2])
      60 (fun _ => Box (-6) 10 (-27) 0) := by
  have h1 := rf3_approach
  rw [← rf3_ph10.evolve_eq] at h1
  have h2 : Reaction (rf0SESW.G ∪ rf0SESW.In) (rf0SESW.G ∪ rf0SESW.Out) 30
      (fun _ => Box (-4) 10 (-22) 0) := by
    have h := rf0SESW.relay
    rw [phase, show rf0SESW.Δ = 30 from rfl, show 30 % 30 = 0 by norm_num, Rule.evolve_zero] at h
    exact h
  have h3 := rf3_depart
  rw [← rf3_ph10.evolve_eq] at h3
  refine ((h1.seq h2).seq h3).mono fun i _ => ?_
  split_ifs
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hx
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hx
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hx
    exact ⟨by omega, by omega, by omega, by omega⟩

/-! ### The corrected halt cell -/

/-- `u = x - y` of the halt cell: `600` left of every piece. -/
def haltU (p : Program) : ℤ := uMin p - 600

/-- `v = x + y` of the corrected halt cell: `V_T + 4` or `V_T + 3`, of the parity of `haltU`. -/
def haltV (p : Program) : ℤ := VT p + 4 - haltU p % 2

/-- **The corrected halt cell**: `u = u_min - 600` (as `haltCell`), `v = V_T + 4 - (u mod 2)`, a
cell of the `SW` halt glider on the lane `V_T + 1`. -/
def haltCellC (p : Program) : Cell := ((haltU p + haltV p) / 2, (haltV p - haltU p) / 2)

/-- The `x` of the reference corner of the halt glider when it covers the halt cell. -/
def haltPx (p : Program) : ℤ := (haltU p + haltV p) / 2 - 1 + haltU p % 2

/-- The time (from the start of the activation) at which the halt glider covers the halt cell. -/
def haltTimeZ (p : Program) (a : ℕ) : ℤ := 2872 + 2 * (A p a + VT p + 10) - 4 * haltPx p

/-- The time of `haltTimeZ`, as a natural number. -/
def haltTime (p : Program) (a : ℕ) : ℕ := (haltTimeZ p a).toNat

/-- The least `u` of the pieces is at most `0`. -/
theorem uMin_nonpos (p : Program) : uMin p ≤ 0 := by
  unfold uMin
  induction machSpecs p with
  | nil => simp
  | cons s l ih =>
    simp only [List.foldr_cons]
    exact (min_le_left _ _).trans ih

/-- The halt glider covers the halt cell after the reflection. -/
theorem haltTimeZ_ge (p : Program) (a : ℕ) : 2897 ≤ haltTimeZ p a := by
  have := uMin_nonpos p
  have := A_nonneg p (a := a) (by omega)
  simp only [haltTimeZ, haltPx, haltV, haltU]
  omega

/-- The time of `haltTime` in `ℤ`. -/
theorem haltTime_cast (p : Program) (a : ℕ) : (haltTime p a : ℤ) = haltTimeZ p a :=
  Int.toNat_of_nonneg (by have := haltTimeZ_ge p a; omega)

/-- `haltTime ≥ 2897`. -/
theorem haltTime_ge (p : Program) (a : ℕ) : 2897 ≤ haltTime p a := by
  have h1 := haltTime_cast p a
  have h2 := haltTimeZ_ge p a
  omega

/-- **The halt glider covers the corrected halt cell** at `haltTime`. -/
theorem haltCellC_mem (p : Program) (a : ℕ) :
    haltCellC p ∈ (haltOutWL p a).cells (haltTime p a) := by
  rw [haltOutWL_eq, haltTime_cast]
  have e1 : (haltTimeZ p a - (2872 + 2 * (A p a + VT p + 10))) / 4 = -haltPx p := by
    unfold haltTimeZ
    omega
  have e2 : ((haltTimeZ p a - (2872 + 2 * (A p a + VT p + 10))) % 4).toNat = 0 := by
    unfold haltTimeZ
    omega
  simp only [WL.cells, WL.px, WL.py, WL.qt, e1, e2]
  have hg : glPh (-1) 1 0 = glSW 0 := by simp [glPh]
  rw [hg, mem_translate]
  have hv := VT_mod p
  rcases Int.emod_two_eq_zero_or_one (haltU p) with h | h
  · have : haltCellC p - (-1 * -haltPx p, -1 * (1 * (-1 * -haltPx p) - (VT p + 1))) =
        ((1 : ℤ), (2 : ℤ)) := by
      simp only [haltCellC, haltPx, haltV, h]
      refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    rw [this, glSW, mem_ofRows]
    rfl
  · have : haltCellC p - (-1 * -haltPx p, -1 * (1 * (-1 * -haltPx p) - (VT p + 1))) =
        ((0 : ℤ), (2 : ℤ)) := by
      simp only [haltCellC, haltPx, haltV, h]
      refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    rw [this, glSW, mem_ofRows]
    rfl

/-- **The corrected halt cell is outside the region of the machine.** -/
theorem haltCellC_notMem (p : Program) : haltCellC p ∉ machRegion p := by
  change ¬ (uMin p - 300 ≤ (haltCellC p).1 - (haltCellC p).2)
  have := VT_mod p
  simp only [haltCellC, haltV, haltU]
  omega

/-- A cell of a `3 × 3` window with rows `< 8` is a set bit of one of the rows. -/
theorem mem_ofRows3 {c : Cell} {x0 y0 : ℤ} {r0 r1 r2 : ℕ} (h0 : r0 < 8) (h1 : r1 < 8)
    (h2 : r2 < 8) (hc : c ∈ ofRows x0 y0 [r0, r1, r2]) : ∃ i < 3, ∃ k < 8,
      ([r0, r1, r2].getD i 0).testBit k = true ∧ c = (x0 + k, y0 + i) := by
  simp only [ofRows, mem_biUnion, mem_range, mem_image, mem_filter] at hc
  obtain ⟨i, hi, k, ⟨hk, hb⟩, rfl⟩ := hc
  simp only [List.length_cons, List.length_nil] at hi
  refine ⟨i, hi, k, ?_, hb, rfl⟩
  interval_cases i <;> simp at hk <;> omega

/-- Every cell of the canonical `SW` glider has `1 ≤ x + y ≤ 4`. -/
theorem glSW_sum (j : ℕ) {c : Cell} (h : c ∈ glSW j) : 1 ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ 4 := by
  rcases j with _ | _ | _ | j <;> simp only [glSW] at h
  · obtain ⟨i, hi, k, hk, hb, rfl⟩ := mem_ofRows3 (by norm_num) (by norm_num) (by norm_num) h
    interval_cases i <;> interval_cases k
    all_goals simp [Nat.testBit] at hb
    all_goals norm_num
  · obtain ⟨i, hi, k, hk, hb, rfl⟩ := mem_ofRows3 (by norm_num) (by norm_num) (by norm_num) h
    interval_cases i <;> interval_cases k
    all_goals simp [Nat.testBit] at hb
    all_goals norm_num
  · obtain ⟨i, hi, k, hk, hb, rfl⟩ := mem_ofRows3 (by norm_num) (by norm_num) (by norm_num) h
    interval_cases i <;> interval_cases k
    all_goals simp [Nat.testBit] at hb
    all_goals norm_num
  · obtain ⟨i, hi, k, hk, hb, rfl⟩ := mem_ofRows3 (by norm_num) (by norm_num) (by norm_num) h
    interval_cases i <;> interval_cases k
    all_goals simp [Nat.testBit] at hb
    all_goals norm_num

/-- **The original `haltCell` is not a cell of the halt glider at any time**: its `x + y` is
`V_T - 1` or `V_T`, the glider's cells have `x + y ∈ [V_T + 2, V_T + 5]`. -/
theorem haltCell_not_hit (p : Program) (a : ℕ) (t : ℤ) :
    haltCell p ∉ (haltOutWL p a).cells t := by
  intro h
  rw [haltOutWL_eq] at h
  simp only [WL.cells, WL.px, WL.py, WL.qt] at h
  rw [mem_translate] at h
  have hg : ∀ k, glPh (-1) 1 k = glSW k := fun k => by simp [glPh]
  rw [hg] at h
  have hs := glSW_sum _ h
  simp only [haltCell, Prod.fst_sub, Prod.snd_sub] at hs
  omega

/-! ### Separation and the halt lemma -/

/-- The relay box of the halt corner, from `20` generations before the meeting. -/
def haltRelayBox (p : Program) (a : ℕ) : Set Cell :=
  (fun x => cornerV (haltCorner p a) + x) '' Box (-6) 10 (-27) 0

/-- The footprint of the halt glider (without the idle pieces), `j` generations after the start
of the activation: the control's box until `20` generations before the corner, the relay box of
the corner during the approach and the reflection, then the box of the outgoing glider. -/
def haltFoot (p : Program) (a : ℕ) (j : ℕ) : Set Cell :=
  if j ≤ 2837 then (ctrlWL p a).box j
  else if j ≤ 2897 then haltRelayBox p a
  else (haltOutWL p a).box j

/-- **The separation facts of the halt activation** of unit `a`. -/
structure HaltSep (p : Program) (a : ℕ) : Prop where
  /-- The control's flight, until `20` generations before the corner, is far from every piece. -/
  pre : ∀ t : ℕ, t < 2837 → ∀ h ∈ machPieces p, FarApart 2 ((ctrlWL p a).box t) h.box
  /-- The relay box of the corner is far from every other piece. -/
  relay : ∀ h ∈ machPieces p, h ≠ haltRfP p a → FarApart 2 (haltRelayBox p a) h.box
  /-- The `SW` flight up to the halt cell is far from every piece. -/
  fly : ∀ t : ℕ, 2897 ≤ t → t < haltTime p a → ∀ h ∈ machPieces p,
    FarApart 2 ((haltOutWL p a).box t) h.box
  /-- The lanes of distinct registers are far apart. -/
  lanes : ∀ r₁ < numRegs p, ∀ r₂ < numRegs p, r₁ ≠ r₂ → FarApart 2 (modLanes p r₁) (modLanes p r₂)
  /-- The pieces and the halt glider are far from the lanes of every register. -/
  laneMach : ∀ j < haltTime p a, ∀ r < numRegs p,
    FarApart 2 (boxesOf (machPieces p) ∪ haltFoot p a j) (modLanes p r)

/-- The placed reflector `10` phases after its meeting phase. -/
theorem reflect_piece_at10 (g : WL) (c : Corner) (T : ℕ)
    (hT : ((T : ℤ) - delayS g c) % 30 = 10) :
    conway.evolve (T % 30) (reflect g c).1.piece.rest =
      translate (cornerV c) (conway.evolve 10 (rfStage c.k).G) := by
  simp only [reflect, PSpec.piece, Base.piece, Piece.place, phase, cornerV]
  rw [Rule.evolve_translate, ← Rule.evolve_add, rfP_rest]
  congr 1
  rw [conway.evolve_mod_of_evolve_eq (rfStage c.k).rest.evolve_eq]
  congr 1
  have h1 := Int.emod_nonneg (-delayS g c) (by norm_num : (30 : ℤ) ≠ 0)
  have h2 := Int.toNat_of_nonneg h1
  unfold delayS at hT h1 h2
  omega

/-- **The early reflection at a corner of image `3`**: from `20` generations before the meeting
time to `10` generations after the end of the reflection, the placed reflector and the glider on
its input line become the reflector and the outgoing glider, inside the translate of
`Box (-6) 10 (-27) 0`. -/
theorem reflect_early {g : WL} {c : Corner} (hk : c.k = 3) (hl : OnLine g c) (T : ℕ)
    (hT : (T : ℤ) = meetT g c - 20) :
    Reaction (conway.evolve (T % 30) (reflect g c).1.piece.rest ∪ g.cells T)
      (conway.evolve ((T + 60) % 30) (reflect g c).1.piece.rest ∪
        (reflect g c).2.cells ((T + 60 : ℕ) : ℤ))
      60 (fun _ => (fun x => cornerV c + x) '' Box (-6) 10 (-27) 0) := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only at hk
  subst hk
  unfold meetT at hT
  rw [reflect_piece_at10 g _ T (by omega), reflect_piece_at10 g _ (T + 60) (by push_cast; omega)]
  have hg : g.cells T = translate (cornerV ⟨3, u, v, tag⟩) (ofRows (-5) (-27) [2, 4, 7]) := by
    rw [hl, WL.shift_cells (rfIn_dir _), show (T : ℤ) - delayS g ⟨3, u, v, tag⟩ = -80 by omega,
      cornerV]
    rfl
  have ho : (reflect g ⟨3, u, v, tag⟩).2.cells ((T + 60 : ℕ) : ℤ) =
      translate (cornerV ⟨3, u, v, tag⟩) (ofRows (-6) (-10) [5, 3, 2]) := by
    simp only [reflect]
    rw [WL.shift_cells (rfOut_dir _), cornerV]
    have e : ((T + 60 : ℕ) : ℤ) - (g.tau - (rfIn 3).tau + 4 * (rfIn 3).dx * rfX 3 u v) = -20 := by
      unfold delayS at hT
      dsimp only at hT
      push_cast
      omega
    rw [e]
    rfl
  rw [hg, ho, ← translate_union, ← translate_union]
  exact rf3_early.translate _

/-- **The reflection of the halt corner** with its reflector alone, from time `2837`. -/
theorem halt_relay (p : Program) (a : ℕ) :
    Reaction (piecesAt [haltRfP p a] 2837 ∪ (ctrlWL p a).cells ((2837 : ℕ) : ℤ))
      (piecesAt [haltRfP p a] (2837 + 60) ∪ (haltOutWL p a).cells ((2837 + 60 : ℕ) : ℤ)) 60
      (fun _ => haltRelayBox p a) := by
  rw [piecesAt_single, piecesAt_single, ← haltRf_eq]
  refine reflect_early rfl (haltLines p a).1 2837 ?_
  change ((2837 : ℕ) : ℤ) = meetT (ctrlWL p a) (haltCorner p a) - 20
  rw [haltMeet]
  norm_num

/-- **The idle pieces of the old route condition cannot be kept far from the control up to the
meeting time**: one generation before the meeting, the control's box touches the box of the
halt reflector. (So the flight condition of `RouteSep` / `RouteSepM`, which quantifies over every
piece of the list including the corner's own reflector until `meetT`, is never satisfied.) -/
theorem not_far_before_meet (p : Program) (a : ℕ) :
    ¬ FarApart 2 ((ctrlWL p a).box ((2856 : ℕ) : ℤ)) (haltRfP p a).box := by
  intro h
  refine h ((haltRfP p a).a, (haltRfP p a).lo + 2) ?_ ((haltRfP p a).a, (haltRfP p a).lo + 2)
    ?_ ⟨by omega, by omega, by omega, by omega⟩
  · have := unitD_uv p a
    have := A_even p a
    have := VT_mod p
    rw [ctrlWL_eq]
    simp only [haltRfP, reflect, PSpec.piece, Base.piece, rfP, Piece.place, haltCorner, rfX,
      rfY, rfCU, rfCV, haltD, trackOut, track, WL.box, WL.px, WL.py, WL.qt, VU] at *
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · simp only [haltRfP, reflect, PSpec.piece, Base.piece, rfP, Piece.place, Piece.box,
      haltCorner]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The instruction of a state with `InvM` and no successor is `halt`. -/
theorem halt_of_step_none {p : Program} {s : MState} (hinv : InvM p s)
    (h : p.step s.cfg = none) : p[s.pc]? = some .halt := by
  have hlt := hinv.1
  rw [Program.step] at h
  change (p[s.pc]?.bind fun i => i.exec s.cfg) = none at h
  rw [List.getElem?_eq_getElem hlt] at h ⊢
  rw [Option.bind_some] at h
  revert h
  cases p[s.pc] with
  | halt => exact fun _ => rfl
  | inc r => simp [Instr.exec]
  | decJz r l =>
    simp only [Instr.exec]
    split_ifs <;> simp

/-- The footprint of the composed halt activation lies in the idle pieces and `haltFoot`. -/
theorem haltFoot_sub (p : Program) (a : ℕ) (L : List Piece) (j : ℕ) :
    (if j ≤ 2837 + 60 then
      (if j ≤ 2837 then boxesOf L ∪ (ctrlWL p a).box (((0 : ℕ) : ℤ) + (j : ℤ))
        else boxesOf L ∪ haltRelayBox p a)
      else boxesOf L ∪ (haltOutWL p a).box (((2897 : ℕ) : ℤ) + ((j - (2837 + 60) : ℕ) : ℤ))) ⊆
      boxesOf L ∪ haltFoot p a j := by
  unfold haltFoot
  by_cases h2 : j ≤ 2837
  · simp only [h2, show j ≤ 2897 by omega, ↓reduceIte, Nat.cast_zero, zero_add]
    exact le_rfl
  · by_cases h3 : j ≤ 2897
    · simp only [h2, h3, ↓reduceIte]
      exact le_rfl
    · simp only [h2, h3, ↓reduceIte]
      rw [show ((2897 : ℕ) : ℤ) + ((j - (2837 + 60) : ℕ) : ℤ) = (j : ℤ) by omega]

/-- The outgoing world line is diagonal. -/
theorem haltOutWL_dir (p : Program) (a : ℕ) : (haltOutWL p a).Dir := reflect_dir _ _

/-- **The halt activation as a reaction**: for a well-formed program and a state with `InvM`
whose instruction is `halt`, under `HaltSep`, the machine idles, the control flies to the halt
corner, is reflected `SW` and flies to the halt cell, and the registers' diagonals evolve on their
own; after `haltTime` the pattern is the idle machine, the halt glider and the registers. -/
theorem halt_reaction {p : Program} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hins : p[s.pc]? = some .halt) (hs : HaltSep p s.pc) :
    Reaction (encM p s)
      (machAt p (s.T + haltTime p s.pc) ∪ (haltOutWL p s.pc).cells (haltTime p s.pc) ∪
        regsAt p (fun r => (s.reg r).later (haltTime p s.pc)) (numRegs p))
      (haltTime p s.pc)
      (fun j => boxesOf (machPieces p) ∪ haltFoot p s.pc j ∪
        stripsOn p s.reg (List.range (numRegs p)) j) := by
  set a := s.pc with ha
  set τ := haltTime p a with hτ
  have hτ2 := haltTime_ge p a
  have hLM := machPieces_sep p hp
  have hinvR : ∀ r' ∈ List.range (numRegs p), (s.reg r').Inv :=
    fun r' h => hinv.2.2.1 r' (List.mem_range.1 h)
  have W1 := window hLM 0 2837 (WL.flight (w := ctrlWL p a) ⟨Or.inl rfl, Or.inl rfl⟩
    ((0 : ℕ) : ℤ) 2837) fun i hi h hh => by
      have := hs.pre i hi h hh
      simpa using this
  have W2 := window_mem hLM (A := [haltRfP p a]) (fun x hx => by
      rw [List.mem_singleton] at hx
      exact hx ▸ haltRfP_mem hins) 2837 60 (halt_relay p a)
    fun i _ h hh hn => hs.relay h hh (by simpa using hn)
  have W3 := window hLM 2897 (τ - 2897) (WL.flight (haltOutWL_dir p a) ((2897 : ℕ) : ℤ) (τ - 2897))
    fun i hi h hh => by
      have := hs.fly (2897 + i) (by omega) (by omega) h hh
      push_cast at this ⊢
      exact this
  have W12 := W1.seq_eq (by simp) W2
  have W123 := (W12.seq_eq (by norm_num) W3).castN (m := τ) (by omega)
  have HR := regsOn_reaction p s.reg τ (List.range (numRegs p)) List.nodup_range hinvR
    fun j _ r₁ h₁ r₂ h₂ hne => (hs.lanes r₁ (List.mem_range.1 h₁) r₂ (List.mem_range.1 h₂)
      hne).mono (regStrip_subset (hinvR r₁ h₁) p r₁ j) (regStrip_subset (hinvR r₂ h₂) p r₂ j)
  have S := W123.par HR fun j hj x hx y hy => by
    obtain ⟨r', hr', hy⟩ := mem_stripsOn.1 hy
    exact hs.laneMach j hj r' (List.mem_range.1 hr') x (haltFoot_sub p a _ j hx) y
      (regStrip_subset (hinvR r' hr') p r' j hy)
  have estart : encM p s = piecesAt (machPieces p) 0 ∪ (ctrlWL p a).cells ((0 : ℕ) : ℤ) ∪
      regsOn p s.reg (List.range (numRegs p)) := by
    rw [encM, machAt, regsAt_eq, ctrlAt_eq, piecesAt_mod _ (show s.T % 30 = 0 % 30 by
      have := hinv.2.1; omega)]
    rfl
  have eend : machAt p (s.T + τ) ∪ (haltOutWL p a).cells τ ∪
      regsAt p (fun r => (s.reg r).later τ) (numRegs p) =
      piecesAt (machPieces p) (2897 + (τ - 2897)) ∪
        (haltOutWL p a).cells (((2897 : ℕ) : ℤ) + ((τ - 2897 : ℕ) : ℤ)) ∪
        regsOn p (fun r => (s.reg r).later τ) (List.range (numRegs p)) := by
    rw [machAt, regsAt_eq, piecesAt_mod _ (show (s.T + τ) % 30 = (2897 + (τ - 2897)) % 30 by
      have := hinv.2.1; omega)]
    rw [show ((2897 : ℕ) : ℤ) + ((τ - 2897 : ℕ) : ℤ) = (τ : ℤ) by omega]
  rw [estart, eend]
  refine S.mono fun j _ => Set.union_subset_union (haltFoot_sub p a _ j) le_rfl

/-- **The halt lemma**: for a well-formed program and a state with `InvM` whose step is `none`
(its instruction is `halt`), under the separation facts `HaltSep`, the corrected halt cell is
alive at the time `haltTime` of the evolution of `encM p s`. -/
theorem halt_everAlive {p : Program} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hstep : p.step s.cfg = none) (hs : HaltSep p s.pc) :
    EverAlive (haltCellC p) (encM p s) := by
  refine ⟨haltTime p s.pc, ?_⟩
  rw [(halt_reaction hp s hinv (halt_of_step_none hinv hstep) hs).evolve_eq]
  exact mem_union_left _ (mem_union_right _ (haltCellC_mem p s.pc))

end LP

end LeanTheory.Life
