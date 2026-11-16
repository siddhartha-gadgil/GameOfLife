/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DecSepAll
public import LeanTheory.Theory.Life.ComputationDecode

/-!
# The Life machine after it halts

Research note `N-23`. The simulator of `MainTheorem.lean` shows that the halt cell is alive iff
the counter machine halts. To read the *output* of the computation, this file follows the Life
machine of a well-formed program `p` along a whole halting run and then for ever after the halt.

* **Along the run** (`exists_evolve_of_reaches`): if the counter machine goes from the
  configuration of a state `s` (with the invariant `MInv`) to a configuration `cf`, then some
  generation of the evolution of `encM p s` is the encoding of a state `s'` with the invariant and
  `s'.cfg = cf`. This is the induction of `Simulator.everAlive_of_halts`, keeping the state.
* **After the halt** (`evolve_late`): from a state whose instruction is `halt`, under `HaltSep`,
  the configuration at every generation `haltTime + n` is `lateConf`: the idle machine, the halt
  glider on its `SW` world line, and the diagonals of the registers evolving on their own. The
  halt activation (`halt_reaction`) gives the generation `haltTime`; from then on the halt glider
  has `u = x - y ≤ u_min - 590` (`haltOut_box_u`: its `u` decreases along the `SW` world line),
  far from the machine and from every register's lanes, which lie in the region
  `u ≥ u_min - 300` (`pieces_region`, `modLanes_region`). The separation of the lanes from each
  other and from the machine is `HaltSep.lanes` and `HaltSep.laneMach`.
* **Register `0` at rest** (`regAt_zero_late`): once every salvo has arrived (`diag_end`, after
  `diagTime`), register `0` is the block `ofRows (blockX p + v) (blockY p + v) [3, 3]` at its
  value `v`.
* **The ray of register `0`** (`late_ray`): from some generation on, the live cells of the ray
  `(blockX p + k, blockY p + k)` are exactly `k = v` and `k = v + 1`: the ray lies in the lanes
  of register `0` (`ray_mem_modLanes`), which nothing else enters. Hence (`readOut_late`) the
  decoding `readOut (blockX p) (blockY p)` of every late generation is the value of register `0`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Along the run -/

/-- **The Life machine follows a run of the counter machine**: if the program goes from `c` to
`cf` and the state `s` (with the invariant) has configuration `c`, then some generation of the
evolution of `encM p s` is the encoding of a state with the invariant and configuration `cf`. -/
theorem exists_evolve_of_reaches {p : Program} (hp : p.WellFormed) (M : MachineSteps p)
    {c cf : Cfg} (h : p.Reaches c cf) :
    ∀ s : MState, s.cfg = c → MInv p s →
      ∃ (t : ℕ) (s' : MState), conway.evolve t (encM p s) = encM p s' ∧ MInv p s' ∧
        s'.cfg = cf := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun s hs hinv => ⟨0, s, rfl, hinv, hs⟩
  | @head a c1 h1 _ ih =>
    intro s hs hinv
    have hstep : p.step s.cfg = some c1 := by rw [hs]; exact h1
    obtain ⟨⟨τ, s1⟩, -, hst, hinv1, hev, -⟩ := exists_goodStep hp M hinv hstep
    have hc1 : s1.cfg = c1 := Option.some.inj (hst.symm.trans hstep)
    obtain ⟨t, s', he, hi, hc⟩ := ih s1 hc1 hinv1
    exact ⟨t + τ, s', by rw [Rule.evolve_add, hev, he], hi, hc⟩

/-! ### After the halt -/

/-- Sets separated in `u = x - y` by more than four are far apart. -/
theorem farApart_of_u {A B : Set Cell} {W : ℤ} (hA : ∀ c ∈ A, c.1 - c.2 ≤ W)
    (hB : ∀ c ∈ B, W + 5 ≤ c.1 - c.2) : FarApart 2 A B := by
  rintro a ha b hb ⟨h1, h2, h3, h4⟩
  have := hA a ha
  have := hB b hb
  push_cast at h1 h2 h3 h4
  omega

/-- **After the halt cell, the halt glider stays far left**: at every time from `haltTime` on,
the box of the halt glider has `u = x - y ≤ u_min - 590`. -/
theorem haltOut_box_u (p : Program) (a : ℕ) {t : ℤ} (ht : haltTimeZ p a ≤ t) {c : Cell}
    (hc : c ∈ (haltOutWL p a).box t) : c.1 - c.2 ≤ uMin p - 590 := by
  rw [haltOutWL_eq] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only [WL.px, WL.py, WL.qt] at h1 h2 h3 h4
  unfold haltTimeZ haltPx haltV haltU at ht
  omega

/-- The machine at any phase lies in the boxes of its pieces. -/
theorem machAt_subset {p : Program} (hp : p.WellFormed) (T : ℕ) :
    (machAt p T : Set Cell) ⊆ boxesOf (machPieces p) := by
  have h := (machAt_reaction hp T 0).subset 0 le_rfl
  rwa [Rule.evolve_zero] at h

/-- The diagonal of a valid register lies in the lanes of its module. -/
theorem regAt_subset_modLanes (p : Program) (r : ℕ) {R : RegS} (hR : R.Inv) :
    (regAt p r R : Set Cell) ⊆ modLanes p r := by
  have h := (regAt_reaction p r hR 0).subset 0 le_rfl
  rw [Rule.evolve_zero] at h
  exact h.trans (regStrip_subset hR p r 0)

/-- The program has at least one register. -/
theorem numRegs_pos (p : Program) : 0 < numRegs p := by
  have := le_max_left 1 ((p.map regBound).foldr max 0)
  unfold numRegs
  omega

/-- **The configuration after the halt**, `t` generations after the start of the halt
activation: the idle machine at phase `T + t`, the halt glider, and the registers' diagonals. -/
def lateConf (p : Program) (s : MState) (t : ℕ) : Finset Cell :=
  machAt p (s.T + t) ∪ (haltOutWL p s.pc).cells t ∪
    regsAt p (fun r => (s.reg r).later t) (numRegs p)

/-- **The evolution after the halt**: for a well-formed program and a state with `InvM` whose
instruction is `halt`, under `HaltSep`, the configuration at every generation `haltTime + n` is
`lateConf`. -/
theorem evolve_late {p : Program} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hins : p[s.pc]? = some .halt) (hs : HaltSep p s.pc) (n : ℕ) :
    conway.evolve (haltTime p s.pc + n) (encM p s) = lateConf p s (haltTime p s.pc + n) := by
  set a := s.pc with ha
  set τ := haltTime p a with hτ
  have hτZ := haltTime_cast p a
  have hτ2 := haltTime_ge p a
  have hLM := machPieces_sep p hp
  have W := window hLM (s.T + τ) n (WL.flight (haltOutWL_dir p a) (τ : ℤ) n)
    fun i _ g hg => farApart_of_u (W := uMin p - 590)
      (fun c hc => haltOut_box_u p a (by omega) hc) fun c hc => by
        have := pieces_region p (mem_boxesOf.2 ⟨g, hg, hc⟩)
        rw [mem_machRegion] at this
        omega
  have hinvR : ∀ r ∈ List.range (numRegs p), ((s.reg r).later τ).Inv :=
    fun r h => (hinv.2.2.1 r (List.mem_range.1 h)).later τ
  have HR := regsOn_reaction p (fun r => (s.reg r).later τ) n (List.range (numRegs p))
    List.nodup_range hinvR fun j _ r₁ h₁ r₂ h₂ hne =>
      (hs.lanes r₁ (List.mem_range.1 h₁) r₂ (List.mem_range.1 h₂) hne).mono
        (regStrip_subset (hinvR r₁ h₁) p r₁ j) (regStrip_subset (hinvR r₂ h₂) p r₂ j)
  have S := W.par HR fun j _ x hx y hy => by
    obtain ⟨r', hr', hy⟩ := mem_stripsOn.1 hy
    have hy' := regStrip_subset (hinvR r' hr') p r' j hy
    rcases hx with hx | hx
    · exact hs.laneMach 0 (by omega) r' (List.mem_range.1 hr') x (Or.inl hx) y hy'
    · have hxu := haltOut_box_u p a (by omega) hx
      have hyu := modLanes_region (uMin_le_mod (List.mem_range.1 hr')) hy'
      rw [mem_machRegion] at hyu
      rintro ⟨h1, h2, h3, h4⟩
      push_cast at h1 h2 h3 h4
      omega
  rw [add_comm, Rule.evolve_add, (halt_reaction hp s hinv hins hs).evolve_eq]
  have e := S.evolve_eq
  have e1 : regsOn p (fun r => ((s.reg r).later τ).later n) (List.range (numRegs p)) =
      regsAt p (fun r => (s.reg r).later (n + τ)) (numRegs p) := by
    rw [regsAt_eq]
    congr 1
    funext r
    rw [RegS.later_later, add_comm]
  rw [e1, show (τ : ℤ) + (n : ℤ) = ((n + τ : ℕ) : ℤ) by push_cast; omega,
    show s.T + τ + n = s.T + (n + τ) by omega] at e
  exact e

/-- **Register `0` at rest**: once every salvo has arrived, register `0` of a state with
`InvM` is the block at its value. -/
theorem regAt_zero_late {p : Program} {s : MState} (hinv : InvM p s) {t : ℕ}
    (ht : diagTime (s.reg 0).K (s.reg 0).q ≤ t) :
    regAt p 0 ((s.reg 0).later t) =
      ofRows (blockX p + (s.reg 0).val) (blockY p + (s.reg 0).val) [3, 3] := by
  set R := s.reg 0 with hRdef
  have hR : R.Inv := hinv.2.2.1 0 (numRegs_pos p)
  have he := diag_end regParams regParams_good _ R.q R.Vs R.Vb R.K rfl hR.1
    (R.m + t - diagTime R.K R.q)
  rw [Nat.sub_add_cancel (by omega)] at he
  have hval : ((R.val : ℕ) : ℤ) = R.K + qMove R.q := Int.toNat_of_nonneg hR.2.2.2
  simp only [regAt, RegS.later]
  rw [diagW, Rule.evolve_translate, he, counter, translate_ofRows, translate_ofRows, blockX,
    blockY, hval]
  congr 1 <;> omega

/-- The ray of register `0` lies in the lanes of register `0`. -/
theorem ray_mem_modLanes (p : Program) (k : ℕ) :
    (blockX p + k, blockY p + k) ∈ modLanes p 0 := by
  refine ⟨((155 : ℤ) + k, (251 : ℤ) + k), ⟨by simp only; omega, by simp only; omega,
    by simp only; omega⟩, ?_⟩
  simp only [blockX, blockY, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> omega

/-- **The ray of register `0` after the halt**: for a well-formed program and a state with
`InvM` whose instruction is `halt`, under `HaltSep`, from some generation on the live cells of
the ray `(blockX p + k, blockY p + k)` are exactly those at the value `v` of register `0` and at
`v + 1`. -/
theorem late_ray {p : Program} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hins : p[s.pc]? = some .halt) (hs : HaltSep p s.pc) :
    ∃ T, ∀ t ≥ T, ∀ k : ℕ, (blockX p + k, blockY p + k) ∈ conway.evolve t (encM p s) ↔
      k = (s.reg 0).val ∨ k = (s.reg 0).val + 1 := by
  set τ := haltTime p s.pc with hτ
  have hτ2 := haltTime_ge p s.pc
  have hτZ := haltTime_cast p s.pc
  have h0 := numRegs_pos p
  refine ⟨τ + diagTime (s.reg 0).K (s.reg 0).q, fun t ht k => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, t = τ + n := ⟨t - τ, by omega⟩
  rw [evolve_late hp s hinv hins hs n, lateConf, mem_union, mem_union, regsAt_eq, mem_regsOn]
  have hray := ray_mem_modLanes p k
  have hrayU := modLanes_region (uMin_le_mod h0) hray
  rw [mem_machRegion] at hrayU
  constructor
  · rintro ((hm | hg) | ⟨r, hr, hreg⟩)
    · exact absurd (Near.refl 2 _) (hs.laneMach 0 (by omega) 0 h0 _
        (Or.inl (machAt_subset hp _ (mem_coe.2 hm))) _ hray)
    · have := haltOut_box_u p s.pc (by push_cast; omega)
        (WL.cells_subset _ _ (mem_coe.2 hg))
      simp only at this
      omega
    · by_cases hr0 : r = 0
      · subst hr0
        rw [regAt_zero_late hinv (by omega)] at hreg
        exact (mem_block_ray _ _ _ _).1 hreg
      · have hR := (hinv.2.2.1 r (List.mem_range.1 hr)).later (τ + n)
        exact absurd (Near.refl 2 _) (hs.lanes r (List.mem_range.1 hr) 0 h0 hr0 _
          (regAt_subset_modLanes p r hR (mem_coe.2 hreg)) _ hray)
  · intro hk
    refine Or.inr ⟨0, List.mem_range.2 h0, ?_⟩
    rw [regAt_zero_late hinv (by omega)]
    exact (mem_block_ray _ _ _ _).2 hk

/-- **The decoding after the halt**: from some generation on, `readOut (blockX p) (blockY p)`
of the configuration is the value of register `0`. -/
theorem readOut_late {p : Program} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hins : p[s.pc]? = some .halt) (hs : HaltSep p s.pc) :
    ∃ T, ∀ t ≥ T, readOut (blockX p) (blockY p) (conway.evolve t (encM p s)) =
      (s.reg 0).val := by
  obtain ⟨T, hT⟩ := late_ray hp s hinv hins hs
  exact ⟨T, fun t ht => readOut_eq_of_block (hT t ht)⟩

end LP

end LeanTheory.Life
