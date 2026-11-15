/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.DiagAppend
public import LeanTheory.Theory.Life.Register1Ops

/-!
# A register of small value is a static block

Research note `N-20`. `DiagValid` asks the reaction of a new salvo with the block to lie above the
strip bound `Vb` (`DiagAppend`), which fails for small values. A register of small value whose
salvos were launched long ago is however a static block: every salvo has arrived.

* `diag_arrived_le`: the generalization of `diag_arrived` to a value `≤ W` (with
  `L ≥ N / 4 + 4 + W`);
* `diagW_static`: then the register diagonal at generation `t` is `reg1Block` of its value;
* `QBeforeL L q m`: every salvo at least `L` cells behind the clock `m / 4`; kept with time, by the
  increment (margin `76`) and by the pull (margin `1217`);
* `RegS.push_dichotomy`, `RegS.pull_dichotomy`: at an operation start, either the hypothesis
  `hz` of `DiagAppend` holds or the register is the static block of its value;
* `RegS.block`: the register after a static-block run, with its invariants.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

/-- **Every salvo has arrived** (value `≤ W`): if at generation `t` every salvo of a valid queue
is at least `L ≥ N / 4 + 4 + W` cells along the diagonal, the gap is at least `2` and the value is
at most `W`, then every salvo has arrived by generation `t`. -/
theorem diag_arrived_le (P : DiagParams) (hP : P.Good) (W L : ℤ)
    (hL : (P.N : ℤ) / 4 + 4 + W ≤ L) (hg2 : 2 ≤ P.g) :
    ∀ (n : ℕ) (q : List (Salvo × ℤ)) (Vs Vb K : ℤ) (t : ℕ), q.length = n →
      DiagValid P Vs Vb K q → (∀ p ∈ q, L ≤ ((t / 4 : ℕ) : ℤ) - p.2) → K + qMove q ≤ W →
      diagTime K q ≤ t
  | _, [], _, _, _, _, _, _, _, _ => by simp [diagTime]
  | n, (σ, e) :: q, Vs, Vb, K, t, hlen, hv, hfar, hval => by
    have hv' := hv
    rw [DiagValid] at hv'
    obtain ⟨hKe, hn4, -, -, -, hN, hd, -, -, -, -, -, -, -, -, hbeh, -, hrest⟩ := hv'
    have he := hfar (σ, e) List.mem_cons_self
    simp only at he
    set Kn := (K + e).toNat with hKn
    have hK : (Kn : ℤ) = K + e := Int.toNat_of_nonneg hKe
    have hNn : (σ.n : ℤ) / 4 ≤ (P.N : ℤ) / 4 :=
      Int.ediv_le_ediv (by norm_num) (by exact_mod_cast hN)
    -- the front salvo has arrived by generation `t`
    have hT : Kn * 4 + σ.n ≤ t := by
      by_contra hT
      have h1 : ((t / 4 : ℕ) : ℤ) ≤ K + e + (σ.n : ℤ) / 4 := by
        have : t / 4 ≤ Kn + σ.n / 4 := by omega
        have h2 : ((Kn + σ.n / 4 : ℕ) : ℤ) = K + e + (σ.n : ℤ) / 4 := by push_cast; rw [hK]
        exact (show ((t / 4 : ℕ) : ℤ) ≤ ((Kn + σ.n / 4 : ℕ) : ℤ) by exact_mod_cast this).trans h2.le
      have hlenq := behind_length (by linarith) q (e + P.g) (((t / 4 : ℕ) : ℤ) - L) hbeh
        (fun p hp => by have := hfar p (List.mem_cons_of_mem _ hp); linarith)
      have hmv := qMove_ge P _ ((σ, e) :: q) Vs Vb K rfl hv
      simp only [qMove, List.length_cons] at hval hmv
      push_cast at hmv
      rcases hlenq with hq | hq
      · subst hq
        simp only [qMove, List.length_nil] at hval hmv
        rcases hd with hd | hd <;> rw [hd] at hval <;> linarith
      · have hq0 : (0 : ℤ) ≤ (q.length : ℤ) := by positivity
        have h2 : 2 * (q.length : ℤ) ≤ (q.length : ℤ) * P.g := by nlinarith
        linarith
    have hdt := diag_arrived_le P hP W L hL hg2 (n - 1) _ _ _ _ (t - (Kn * 4 + σ.n))
      (by simp [shiftQ] at hlen ⊢; omega) hrest (fun p hp => by
        simp only [shiftQ, List.mem_map] at hp
        obtain ⟨p', hp', rfl⟩ := hp
        have := hfar p' (List.mem_cons_of_mem _ hp')
        have h5 : (t - (Kn * 4 + σ.n)) / 4 = t / 4 - (Kn + σ.n / 4) := by omega
        have h6 : Kn + σ.n / 4 ≤ t / 4 := by omega
        rw [h5]
        push_cast [h6]
        omega) (by rw [qMove_shiftQ]; simp only [qMove] at hval; linarith)
    rw [diagTime]
    omega

/-- Every salvo of a queue is at least `L` cells behind the clock `m / 4`. -/
def QBeforeL (L : ℤ) (q : List (Salvo × ℤ)) (m : ℕ) : Prop :=
  ∀ p ∈ q, p.2 + L ≤ ((m / 4 : ℕ) : ℤ)

/-- The empty queue is launched before any time. -/
theorem QBeforeL.nil (L : ℤ) (m : ℕ) : QBeforeL L [] m := fun _ h => (List.not_mem_nil h).elim

/-- `QBeforeL` is kept with time. -/
theorem QBeforeL.mono {L : ℤ} {q : List (Salvo × ℤ)} {m m' : ℕ} (h : QBeforeL L q m)
    (hm : m ≤ m') : QBeforeL L q m' := by
  intro p hp
  have := h p hp
  have : m / 4 ≤ m' / 4 := Nat.div_le_div_right hm
  omega

/-- `QBeforeL` is kept by appending a salvo launched before the new time. -/
theorem QBeforeL.append {L : ℤ} {q : List (Salvo × ℤ)} {m m' : ℕ} (h : QBeforeL L q m)
    (hm : m ≤ m') (σ : Salvo) (e : ℤ) (he : e + L ≤ ((m' / 4 : ℕ) : ℤ)) :
    QBeforeL L (q ++ [(σ, e)]) m' := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h.mono hm p hp
  · rw [List.mem_singleton] at hp
    subst hp
    exact he

/-- `QBeforeL 24` is `QBefore` of `DiagAppend`, so a larger margin gives `QBefore`. -/
theorem QBeforeL.toQBefore {L : ℤ} {q : List (Salvo × ℤ)} {m : ℕ} (h : QBeforeL L q m)
    (hL : 24 ≤ L) : QBefore q m := fun p hp => by have := h p hp; linarith

/-- The margin `L` along the diagonal at generation `m` of salvos with `QBeforeL L q m`. -/
theorem QBeforeL.far {L : ℤ} {q : List (Salvo × ℤ)} {m : ℕ} (h : QBeforeL L q m) :
    ∀ p ∈ q, L ≤ ((m / 4 : ℕ) : ℤ) - p.2 := fun p hp => by have := h p hp; linarith

namespace LP

/-- **The increment keeps `QBeforeL L` for `L ≤ 76`**: the salvo `pushOf m` is at least `76`
cells behind the clock at the end `m + 6990` of the operation. -/
theorem QBeforeL.pushAny {L : ℤ} (hL : L ≤ 76) {R : RegS} (h : QBeforeL L R.q R.m) :
    QBeforeL L (R.q ++ [pushOf R.m]) (R.m + 6990) := by
  refine h.append (by omega) _ _ ?_
  have hj : incPhase R.m < 4 := Nat.mod_lt _ (by norm_num)
  have hb : pushBase (incPhase R.m) ≤ 7 := by
    rcases (incPhase R.m) with _ | _ | _ | j <;> simp [pushBase]
  have : (R.m + 6653 + incPhase R.m) / 4 + 83 ≤ (R.m + 6990) / 4 := by omega
  have : (((R.m + 6653 + incPhase R.m) / 4 : ℕ) : ℤ) + 83 ≤ (((R.m + 6990) / 4 : ℕ) : ℤ) := by
    exact_mod_cast this
  change pushBase (incPhase R.m) + (((R.m + 6653 + incPhase R.m) / 4 : ℕ) : ℤ) + L ≤ _
  linarith

/-- The increment keeps the strip bound `Vb` of the register. -/
theorem RegS.pushAny_Vb (R : RegS) (Vs' : ℤ) : (RegS.pushAny R Vs').Vb = R.Vb := rfl

end LP

/-- **The pull keeps `QBeforeL L` for `L ≤ 1217`**: a pulling salvo of phase `ph ≤ 3` appended
at offset `16 + (m0 + 6555 + ph) / 4` is at least `1217` cells behind the clock at the end
`m0 + 11490` of the operation (`dz2dOp` … `dz2d3Op`). -/
theorem QBeforeL.pull {L : ℤ} (hL : L ≤ 1217) {q : List (Salvo × ℤ)} {m0 : ℕ}
    (h : QBeforeL L q m0) (σ : Salvo) (ph : ℕ) (hph : ph ≤ 3) :
    QBeforeL L (q ++ [(σ, (16 : ℤ) + (((m0 + 6555 + ph) / 4 : ℕ) : ℤ))]) (m0 + 11490) := by
  refine h.append (by omega) _ _ ?_
  have : (m0 + 6555 + ph) / 4 + 1233 ≤ (m0 + 11490) / 4 := by omega
  have : (((m0 + 6555 + ph) / 4 : ℕ) : ℤ) + 1233 ≤ (((m0 + 11490) / 4 : ℕ) : ℤ) := by
    exact_mod_cast this
  linarith

/-- **A register diagonal whose salvos have all arrived is a static block**: a valid queue with
value `≤ 15`, every salvo at least `29` cells behind the clock at `t`, is at generation `t` the
block `reg1Block` of its value. -/
theorem diagW_static {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} {t : ℕ}
    (hv : DiagValid regParams Vs Vb K q) (hQ : QBeforeL 29 q t) (hval : K + qMove q ≤ 15) :
    conway.evolve t (diagW q K) = reg1Block (K + qMove q) := by
  have hN : (regParams.N : ℤ) / 4 + 4 + 15 ≤ 29 := by norm_num [regParams]
  have hg : (2 : ℤ) ≤ regParams.g := by norm_num [regParams]
  have hdt := diag_arrived_le regParams regParams_good 15 29 hN hg _ q Vs Vb K t rfl hv hQ.far hval
  have he := diag_end regParams regParams_good _ q Vs Vb K rfl hv (t - diagTime K q)
  rw [Nat.sub_add_cancel hdt] at he
  rw [diagW, Rule.evolve_translate, he, reg1Block]

namespace LP

/-- **The increment at a register**: with `Vb = 18` and the salvos at least `29` behind, either
the hypothesis of `RegS.pushAny_join` holds, or the value is at most `15` and the register is the
static block of its value. -/
theorem RegS.push_dichotomy {R : RegS} (hR : R.Inv) (hVb : R.Vb = 18)
    (hQ : QBeforeL 29 R.q R.m) :
    R.Vb + 14 ≤ 2 * (R.K + qMove R.q) ∨
      (R.K + qMove R.q ≤ 15 ∧ conway.evolve R.m (diagW R.q R.K) = reg1Block (R.K + qMove R.q)) := by
  by_cases h : R.Vb + 14 ≤ 2 * (R.K + qMove R.q)
  · exact Or.inl h
  · have hw : R.K + qMove R.q ≤ 15 := by omega
    exact Or.inr ⟨hw, diagW_static hR.1 hQ hw⟩

/-- **The pull at a register**: with `Vb = 18` and the salvos at least `29` behind, either the
hypothesis `hz` of `dz2d_join` … `dz2d3_join` holds, or the value is at most `7` and the register
is the static block of its value. -/
theorem RegS.pull_dichotomy {R : RegS} (hR : R.Inv) (hVb : R.Vb = 18)
    (hQ : QBeforeL 29 R.q R.m) :
    R.Vb ≤ 3 + 2 * (R.K + qMove R.q) ∨
      (R.K + qMove R.q ≤ 7 ∧ conway.evolve R.m (diagW R.q R.K) = reg1Block (R.K + qMove R.q)) := by
  by_cases h : R.Vb ≤ 3 + 2 * (R.K + qMove R.q)
  · exact Or.inl h
  · have hw : R.K + qMove R.q ≤ 7 := by omega
    exact Or.inr ⟨hw, diagW_static hR.1 hQ (by omega)⟩

/-- The register holding the block `k` with nothing in flight, at generation `m` of its clock. -/
def RegS.block (k : ℕ) (m : ℕ) : RegS := ⟨[], k, m, 18, 18⟩

/-- The value of the register `RegS.block k m` is `k`. -/
@[simp] theorem RegS.val_block (k m : ℕ) : (RegS.block k m).val = k := by
  simp [RegS.val, RegS.block, qMove]

/-- The register `RegS.block k m` satisfies the invariant. -/
theorem RegS.inv_block (k m : ℕ) : (RegS.block k m).Inv := by
  refine ⟨?_, le_rfl, ?_, by simp [RegS.block, qMove]⟩
  · simp only [RegS.block, DiagValid]
    omega
  · simp only [RegS.block]
    omega

/-- The register `RegS.block k m` has nothing in flight (`QBeforeL` for every margin). -/
theorem RegS.qBeforeL_block (L : ℤ) (k m : ℕ) : QBeforeL L (RegS.block k m).q (RegS.block k m).m :=
  QBeforeL.nil L m

/-- The strip bound `Vb` of `RegS.block k m` is `18`. -/
theorem RegS.Vb_block (k m : ℕ) : (RegS.block k m).Vb = 18 := rfl

/-- The diagonal of `RegS.block k m` at any generation is the static block `reg1Block k`. -/
theorem RegS.diagW_block (k m i : ℕ) :
    conway.evolve i (diagW (RegS.block k m).q (RegS.block k m).K) = reg1Block k := by
  simp only [RegS.block, diagW, flights, empty_union, Rule.evolve_translate,
    (counter_isStillLife _).evolve, reg1Block]

end LP

end LeanTheory.Life
