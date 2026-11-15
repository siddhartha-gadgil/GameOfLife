/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.SalvoPhases
public import LeanTheory.Theory.Life.ActivationIncModule

/-!
# Appending a salvo far behind keeps a register diagonal valid

Research note `N-20`. The register operations (`dz2eOp`, `dz2dOp` and their phase variants) need
the queue of the register diagonal with the new salvo at its back to be valid (`DiagValid`). This
module derives that from the validity of the old queue.

* `SalvoFits P σ`: the conditions of `DiagValid` on a salvo alone (box, reaction, lanes);
* `diagValid_append`: **appending a salvo far behind keeps a valid queue valid**, if the salvo is
  at least `g` behind every salvo of the queue, in front of the block, inside the new strip
  bound `Vs' ≤ Vs`, and if its reaction with the block at its final position
  `K + qMove q` lies above `Vb`;
* `QBefore q m`: every salvo of the queue is at least `24` cells behind the front of the clock
  `m / 4` (true for the queue of a register; kept by the register operations and with time);
* `diagValid_join`: the form used by the operations, with the strip bound `joinVs`;
* `dz2e_join` … `dz2d3_join`: `hv'` and `hVs'` of the eight operation lemmas;
* `RegS.inv_pushAny_join`: the increment of `ActivationIncModule` keeps the invariant and
  `QBefore`.

**Caveat.** `DiagValid` asks the box of the reaction of every salvo with the block to lie above
`Vb` (`Vb ≤ σ.za + σ.zlo + 2 K`). With `18 ≤ Vb` (as in `RegS.Inv` and the operation lemmas)
this forces the value `v = K + qMove q` at which the new salvo arrives to be large: `Vb + 13 ≤ 2 v`
for `regPush` (`v ≥ 16`) and `Vb ≤ 3 + 2 v` for `regPull` (`v ≥ 8`). So the hypotheses `hv'` and
`hVb` of the operation lemmas cannot both hold for small register values (for example an
increment of the empty register `RegS.ofNat 0`); this is a hypothesis of every theorem here.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

/-- The conditions of `DiagValid` on a salvo alone: its period, box, reaction and move fit the
parameters, and its boxes lie in the lanes of the strip. -/
def SalvoFits (P : DiagParams) (σ : Salvo) : Prop :=
  σ.n % 4 = 0 ∧ P.A ≤ σ.a ∧ σ.b ≤ P.B ∧ P.ZA ≤ σ.za ∧ σ.n ≤ P.N ∧ (σ.d = 1 ∨ σ.d = -1) ∧
    P.U₁ ≤ σ.a - σ.hi ∧ σ.b - σ.lo ≤ P.U₂ ∧ P.U₁ ≤ σ.za - σ.zhi ∧ σ.zb - σ.zlo ≤ P.U₂

/-- The pulling salvo fits the register parameters. -/
theorem regPull_fits : SalvoFits regParams regPull := by
  simp only [SalvoFits, regParams, regPull]; norm_num

/-- The pulling salvo at phase 1 fits the register parameters. -/
theorem regPullP1_fits : SalvoFits regParams regPullP1 := by
  simp only [SalvoFits, regParams, regPullP1]; norm_num

/-- The pulling salvo at phase 2 fits the register parameters. -/
theorem regPullP2_fits : SalvoFits regParams regPullP2 := by
  simp only [SalvoFits, regParams, regPullP2]; norm_num

/-- The pulling salvo at phase 3 fits the register parameters. -/
theorem regPullP3_fits : SalvoFits regParams regPullP3 := by
  simp only [SalvoFits, regParams, regPullP3]; norm_num

/-- The pushing salvo fits the register parameters. -/
theorem regPush_fits : SalvoFits regParams regPush := by
  simp only [SalvoFits, regParams, regPush]; norm_num

/-- The pushing salvo at phase 1 fits the register parameters. -/
theorem regPushP1_fits : SalvoFits regParams regPushP1 := by
  simp only [SalvoFits, regParams, regPushP1]; norm_num

/-- The pushing salvo at phase 2 fits the register parameters. -/
theorem regPushP2_fits : SalvoFits regParams regPushP2 := by
  simp only [SalvoFits, regParams, regPushP2]; norm_num

/-- The pushing salvo at phase 3 fits the register parameters. -/
theorem regPushP3_fits : SalvoFits regParams regPushP3 := by
  simp only [SalvoFits, regParams, regPushP3]; norm_num

/-- A salvo at least `g` behind every salvo of a queue (and behind `e₀`) can be put at its back. -/
theorem behind_append {A B g : ℤ} (σ : Salvo) (e : ℤ) (ha : A ≤ σ.a) (hb : σ.b ≤ B) :
    ∀ (q : List (Salvo × ℤ)) (e₀ : ℤ), Behind A B g e₀ q → e₀ ≤ e → (∀ p ∈ q, p.2 + g ≤ e) →
      Behind A B g e₀ (q ++ [(σ, e)])
  | [], _, _, he, _ => ⟨ha, hb, he, trivial⟩
  | (τ, f) :: q, _, ⟨h1, h2, h3, hq⟩, _, hgap =>
    ⟨h1, h2, h3, behind_append σ e ha hb q (f + g) hq (hgap (τ, f) List.mem_cons_self)
      fun p hp => hgap p (List.mem_cons_of_mem _ hp)⟩

/-- Salvos in a strip are in every lower strip. -/
theorem inStrip_mono (P : DiagParams) {Vs Vs' : ℤ} (h : Vs' ≤ Vs) :
    ∀ q : List (Salvo × ℤ), InStrip P Vs q → InStrip P Vs' q
  | [], _ => trivial
  | (_, _) :: q, ⟨h1, h2, h3, hq⟩ => ⟨h1, h2, by linarith, inStrip_mono P h q hq⟩

/-- A salvo in the strip can be put at the back of salvos in the strip. -/
theorem inStrip_append (P : DiagParams) {Vs : ℤ} (σ : Salvo) (e : ℤ) (h1 : P.U₁ ≤ σ.a - σ.hi)
    (h2 : σ.b - σ.lo ≤ P.U₂) (h3 : Vs ≤ σ.a + σ.lo - 2 * e) :
    ∀ q : List (Salvo × ℤ), InStrip P Vs q → InStrip P Vs (q ++ [(σ, e)])
  | [], _ => ⟨h1, h2, h3, trivial⟩
  | (_, _) :: q, ⟨g1, g2, g3, hq⟩ => ⟨g1, g2, g3, inStrip_append P σ e h1 h2 h3 q hq⟩

/-- Shifting a queue with a salvo at its back. -/
theorem shiftQ_append (q : List (Salvo × ℤ)) (σ : Salvo) (e m : ℤ) :
    shiftQ (q ++ [(σ, e)]) m = shiftQ q m ++ [(σ, e - m)] := by
  simp [shiftQ]

/-- In a valid queue the final block lies above `Vb`: `Vb ≤ 18 + 2 (K + qMove q)`. -/
theorem DiagValid.vb_le (P : DiagParams) : ∀ (n : ℕ) (q : List (Salvo × ℤ)) (Vs Vb K : ℤ),
    q.length = n → DiagValid P Vs Vb K q → Vb ≤ 18 + 2 * (K + qMove q)
  | _, [], _, _, _, _, hv => by
    rw [DiagValid] at hv
    simpa [qMove] using hv
  | n, (σ, e) :: q, Vs, Vb, K, hlen, hv => by
    rw [DiagValid] at hv
    have hrest := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have := DiagValid.vb_le P (n - 1) _ _ _ _ (by simp [shiftQ] at hlen ⊢; omega) hrest
    rw [qMove_shiftQ] at this
    simp only [qMove]
    linarith

/-- **Appending a salvo far behind keeps a queue valid.** The salvo fits the parameters, is in
front of the block (`0 ≤ K + e`), at least `g` behind every salvo of the queue, inside the new
strip bound `Vs' ≤ Vs`, and its reaction with the block at the final position `K + qMove q` and
the moved block lie above `Vb`. -/
theorem diagValid_append (P : DiagParams) (hP : P.Good) (σ : Salvo) (hσ : SalvoFits P σ) :
    ∀ (n : ℕ) (q : List (Salvo × ℤ)) (Vs Vb K Vs' e : ℤ), q.length = n →
      DiagValid P Vs Vb K q → Vs' ≤ Vs → Vs' ≤ σ.a + σ.lo - 2 * e → 0 ≤ K + e →
      (∀ p ∈ q, p.2 + P.g ≤ e) → Vb ≤ σ.za + σ.zlo + 2 * (K + qMove q) →
      Vb ≤ 18 + 2 * (K + qMove q + σ.d) → DiagValid P Vs' Vb K (q ++ [(σ, e)])
  | _, [], Vs, Vb, K, Vs', e, _, hv, _, hse, hKe, _, hz, hd => by
    rw [DiagValid] at hv
    obtain ⟨hn4, hA, hB, hZA, hN, hdσ, hu1, hu2, hz1, hz2⟩ := hσ
    simp only [qMove, add_zero] at hz hd
    rw [List.nil_append, DiagValid]
    refine ⟨hKe, hn4, hA, hB, hZA, hN, hdσ, hu1, hu2, hz1, hz2, hse, hz, hv, hd, trivial,
      trivial, ?_⟩
    rw [shiftQ, List.map_nil, DiagValid]
    exact hd
  | n, (τ, f) :: q, Vs, Vb, K, Vs', e, hlen, hv, hVs, hse, _, hgap, hz, hd => by
    rw [DiagValid] at hv
    obtain ⟨hKf, hn4, hA, hB, hZA, hN, hdτ, hu1, hu2, hz1, hz2, hv1, hv2, hv3, hv4, hbeh, hin,
      hrest⟩ := hv
    have hσ' := hσ
    obtain ⟨-, hσA, hσB, -, -, -, hσu1, hσu2, -, -⟩ := hσ'
    have hg4 := hP.2.2.2.1
    have hfe := hgap (τ, f) List.mem_cons_self
    simp only at hfe
    have hNn : (τ.n : ℤ) / 4 ≤ (P.N : ℤ) / 4 :=
      Int.ediv_le_ediv (by norm_num) (by exact_mod_cast hN)
    simp only [qMove] at hz hd
    rw [List.cons_append, DiagValid]
    refine ⟨hKf, hn4, hA, hB, hZA, hN, hdτ, hu1, hu2, hz1, hz2, hVs.trans hv1, hv2, hv3, hv4,
      behind_append σ e hσA hσB q (f + P.g) hbeh hfe
        (fun p hp => hgap p (List.mem_cons_of_mem _ hp)),
      inStrip_append P σ e hσu1 hσu2 hse q (inStrip_mono P hVs q hin), ?_⟩
    rw [shiftQ_append]
    refine diagValid_append P hP σ hσ (n - 1) _ _ _ _ _ _
      (by simp [shiftQ] at hlen ⊢; omega) hrest (by linarith) (by linarith) ?_ ?_ ?_ ?_
    · rcases hdτ with h | h <;> rw [h] <;> linarith
    · intro p hp
      simp only [shiftQ, List.mem_map] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      have := hgap p' (List.mem_cons_of_mem _ hp')
      simp only
      linarith
    · rw [qMove_shiftQ]; linarith
    · rw [qMove_shiftQ]; linarith

/-- Every salvo of a queue is at least `24` cells behind the clock `m / 4`: the salvos were
launched well before generation `m` (an invariant of the register queues). -/
def QBefore (q : List (Salvo × ℤ)) (m : ℕ) : Prop := ∀ p ∈ q, p.2 + 24 ≤ ((m / 4 : ℕ) : ℤ)

/-- The empty queue is launched before any time. -/
theorem QBefore.nil (m : ℕ) : QBefore [] m := fun _ h => (List.not_mem_nil h).elim

/-- `QBefore` is kept with time. -/
theorem QBefore.mono {q : List (Salvo × ℤ)} {m m' : ℕ} (h : QBefore q m) (hm : m ≤ m') :
    QBefore q m' := by
  intro p hp
  have := h p hp
  have : m / 4 ≤ m' / 4 := Nat.div_le_div_right hm
  omega

/-- `QBefore` is kept by appending a salvo launched before the new time. -/
theorem QBefore.append {q : List (Salvo × ℤ)} {m m' : ℕ} (h : QBefore q m) (hm : m ≤ m')
    (σ : Salvo) (e : ℤ) (he : e + 24 ≤ ((m' / 4 : ℕ) : ℤ)) : QBefore (q ++ [(σ, e)]) m' := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h.mono hm p hp
  · rw [List.mem_singleton] at hp
    subst hp
    exact he

/-- The strip bound after a salvo joins at offset `e`: the old one, lowered to the salvo. -/
def joinVs (Vs : ℤ) (σ : Salvo) (e : ℤ) : ℤ := min Vs (σ.a + σ.lo - 2 * e)

/-- **A salvo joining a register diagonal** at time `t ≥ m0`, at offset `base + t / 4`
(`6 ≤ base`), keeps the queue valid with the strip bound `joinVs`, if the queue was launched
before `m0` (`QBefore`), the value is nonnegative, and the reaction of the salvo with the block at
the value lies above `Vb`. -/
theorem diagValid_join {σ : Salvo} (hσ : SalvoFits regParams σ) {q : List (Salvo × ℤ)}
    {Vs Vb K base : ℤ} {m0 t : ℕ} (hv : DiagValid regParams Vs Vb K q)
    (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0) (hmt : m0 ≤ t) (hbase : 6 ≤ base)
    (hz : Vb ≤ σ.za + σ.zlo + 2 * (K + qMove q)) (hd : Vb ≤ 18 + 2 * (K + qMove q + σ.d)) :
    DiagValid regParams (joinVs Vs σ (base + ((t / 4 : ℕ) : ℤ))) Vb K
      (q ++ [(σ, base + ((t / 4 : ℕ) : ℤ))]) := by
  have ht : ((m0 / 4 : ℕ) : ℤ) ≤ ((t / 4 : ℕ) : ℤ) := by
    have : m0 / 4 ≤ t / 4 := Nat.div_le_div_right hmt
    exact_mod_cast this
  have ht0 : (0 : ℤ) ≤ ((t / 4 : ℕ) : ℤ) := by positivity
  refine diagValid_append regParams regParams_good σ hσ _ q Vs Vb K _ _ rfl hv
    (min_le_left _ _) (min_le_right _ _) ?_ ?_ hz hd
  · rcases q with _ | ⟨⟨τ, f⟩, q⟩
    · simp only [qMove] at hval
      linarith
    · have hKf : 0 ≤ K + f := by
        have hv' := hv
        rw [DiagValid] at hv'
        exact hv'.1
      have := hQ (τ, f) List.mem_cons_self
      simp only at this
      linarith
  · intro p hp
    have := hQ p hp
    simp only [regParams]
    linarith

/-- The strip bound `joinVs` at the joining time `t ≥ m0` is at least `-34`, if the old one was at
least `18` at `m0` and the salvo at offset `base` is above `-34`. -/
theorem joinVs_ge {Vs base : ℤ} {σ : Salvo} {m0 t : ℕ} (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ))
    (hmt : m0 ≤ t) (hb : -34 ≤ σ.a + σ.lo - 2 * base) :
    -34 ≤ joinVs Vs σ (base + ((t / 4 : ℕ) : ℤ)) + 2 * ((t / 4 : ℕ) : ℤ) := by
  have ht : ((m0 / 4 : ℕ) : ℤ) ≤ ((t / 4 : ℕ) : ℤ) := by
    have : m0 / 4 ≤ t / 4 := Nat.div_le_div_right hmt
    exact_mod_cast this
  rcases min_choice Vs (σ.a + σ.lo - 2 * (base + ((t / 4 : ℕ) : ℤ))) with h | h <;>
    rw [joinVs, h] <;> linarith

/-- `diagValid_join` and `joinVs_ge` together, for a salvo of the operations. -/
theorem join_both {σ : Salvo} (hσ : SalvoFits regParams σ) {q : List (Salvo × ℤ)}
    {Vs Vb K base : ℤ} {m0 t : ℕ} (hv : DiagValid regParams Vs Vb K q)
    (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0) (hmt : m0 ≤ t) (hbase : 6 ≤ base)
    (hb : -34 ≤ σ.a + σ.lo - 2 * base) (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ))
    (hz : Vb ≤ σ.za + σ.zlo + 2 * (K + qMove q)) (hd : Vb ≤ 18 + 2 * (K + qMove q + σ.d)) :
    DiagValid regParams (joinVs Vs σ (base + ((t / 4 : ℕ) : ℤ))) Vb K
        (q ++ [(σ, base + ((t / 4 : ℕ) : ℤ))]) ∧
      -34 ≤ joinVs Vs σ (base + ((t / 4 : ℕ) : ℤ)) + 2 * ((t / 4 : ℕ) : ℤ) :=
  ⟨diagValid_join hσ hv hval hQ hmt hbase hz hd, joinVs_ge hVs hmt hb⟩

/-- `hv'` and `hVs'` of `dz2eOp` (the pushing salvo, phase `0`). -/
theorem dz2e_join {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} {m0 : ℕ}
    (hv : DiagValid regParams Vs Vb K q) (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0)
    (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) (hz : Vb + 13 ≤ 2 * (K + qMove q)) :
    DiagValid regParams (joinVs Vs regPush ((7 : ℤ) + (((m0 + 6653) / 4 : ℕ) : ℤ))) Vb K
        (q ++ [(regPush, ((7 : ℤ) + (((m0 + 6653) / 4 : ℕ) : ℤ)))]) ∧
      -34 ≤ joinVs Vs regPush ((7 : ℤ) + (((m0 + 6653) / 4 : ℕ) : ℤ)) +
        2 * (((m0 + 6653) / 4 : ℕ) : ℤ) := by
  have := DiagValid.vb_le regParams _ q Vs Vb K rfl hv
  exact join_both regPush_fits hv hval hQ (by omega) (by norm_num)
    (by simp only [regPush]; norm_num) hVs (by simp only [regPush]; linarith)
    (by simp only [regPush]; linarith)

/-- `hv'` and `hVs'` of `dz2e1Op` (the pushing salvo, phase `1`). -/
theorem dz2e1_join {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} {m0 : ℕ}
    (hv : DiagValid regParams Vs Vb K q) (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0)
    (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) (hz : Vb + 13 ≤ 2 * (K + qMove q)) :
    DiagValid regParams (joinVs Vs regPushP1 ((7 : ℤ) + (((m0 + 6654) / 4 : ℕ) : ℤ))) Vb K
        (q ++ [(regPushP1, ((7 : ℤ) + (((m0 + 6654) / 4 : ℕ) : ℤ)))]) ∧
      -34 ≤ joinVs Vs regPushP1 ((7 : ℤ) + (((m0 + 6654) / 4 : ℕ) : ℤ)) +
        2 * (((m0 + 6654) / 4 : ℕ) : ℤ) := by
  have := DiagValid.vb_le regParams _ q Vs Vb K rfl hv
  exact join_both regPushP1_fits hv hval hQ (by omega) (by norm_num)
    (by simp only [regPushP1]; norm_num) hVs (by simp only [regPushP1]; linarith)
    (by simp only [regPushP1]; linarith)

/-- `hv'` and `hVs'` of `dz2e2Op` (the pushing salvo, phase `2`). -/
theorem dz2e2_join {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} {m0 : ℕ}
    (hv : DiagValid regParams Vs Vb K q) (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0)
    (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) (hz : Vb + 14 ≤ 2 * (K + qMove q)) :
    DiagValid regParams (joinVs Vs regPushP2 ((6 : ℤ) + (((m0 + 6655) / 4 : ℕ) : ℤ))) Vb K
        (q ++ [(regPushP2, ((6 : ℤ) + (((m0 + 6655) / 4 : ℕ) : ℤ)))]) ∧
      -34 ≤ joinVs Vs regPushP2 ((6 : ℤ) + (((m0 + 6655) / 4 : ℕ) : ℤ)) +
        2 * (((m0 + 6655) / 4 : ℕ) : ℤ) := by
  have := DiagValid.vb_le regParams _ q Vs Vb K rfl hv
  exact join_both regPushP2_fits hv hval hQ (by omega) (by norm_num)
    (by simp only [regPushP2]; norm_num) hVs (by simp only [regPushP2]; linarith)
    (by simp only [regPushP2]; linarith)

/-- `hv'` and `hVs'` of `dz2e3Op` (the pushing salvo, phase `3`). -/
theorem dz2e3_join {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} {m0 : ℕ}
    (hv : DiagValid regParams Vs Vb K q) (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0)
    (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) (hz : Vb + 14 ≤ 2 * (K + qMove q)) :
    DiagValid regParams (joinVs Vs regPushP3 ((6 : ℤ) + (((m0 + 6656) / 4 : ℕ) : ℤ))) Vb K
        (q ++ [(regPushP3, ((6 : ℤ) + (((m0 + 6656) / 4 : ℕ) : ℤ)))]) ∧
      -34 ≤ joinVs Vs regPushP3 ((6 : ℤ) + (((m0 + 6656) / 4 : ℕ) : ℤ)) +
        2 * (((m0 + 6656) / 4 : ℕ) : ℤ) := by
  have := DiagValid.vb_le regParams _ q Vs Vb K rfl hv
  exact join_both regPushP3_fits hv hval hQ (by omega) (by norm_num)
    (by simp only [regPushP3]; norm_num) hVs (by simp only [regPushP3]; linarith)
    (by simp only [regPushP3]; linarith)

/-- `hv'` and `hVs'` of `dz2dOp` (the pulling salvo, phase `0`). -/
theorem dz2d_join {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} {m0 : ℕ}
    (hv : DiagValid regParams Vs Vb K q) (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0)
    (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) (hz : Vb ≤ 3 + 2 * (K + qMove q)) :
    DiagValid regParams (joinVs Vs regPull ((16 : ℤ) + (((m0 + 6555) / 4 : ℕ) : ℤ))) Vb K
        (q ++ [(regPull, ((16 : ℤ) + (((m0 + 6555) / 4 : ℕ) : ℤ)))]) ∧
      -34 ≤ joinVs Vs regPull ((16 : ℤ) + (((m0 + 6555) / 4 : ℕ) : ℤ)) +
        2 * (((m0 + 6555) / 4 : ℕ) : ℤ) :=
  join_both regPull_fits hv hval hQ (by omega) (by norm_num)
    (by simp only [regPull]; norm_num) hVs (by simp only [regPull]; linarith)
    (by simp only [regPull]; linarith)

/-- `hv'` and `hVs'` of `dz2d1Op` (the pulling salvo, phase `1`). -/
theorem dz2d1_join {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} {m0 : ℕ}
    (hv : DiagValid regParams Vs Vb K q) (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0)
    (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) (hz : Vb ≤ 3 + 2 * (K + qMove q)) :
    DiagValid regParams (joinVs Vs regPullP1 ((16 : ℤ) + (((m0 + 6556) / 4 : ℕ) : ℤ))) Vb K
        (q ++ [(regPullP1, ((16 : ℤ) + (((m0 + 6556) / 4 : ℕ) : ℤ)))]) ∧
      -34 ≤ joinVs Vs regPullP1 ((16 : ℤ) + (((m0 + 6556) / 4 : ℕ) : ℤ)) +
        2 * (((m0 + 6556) / 4 : ℕ) : ℤ) :=
  join_both regPullP1_fits hv hval hQ (by omega) (by norm_num)
    (by simp only [regPullP1]; norm_num) hVs (by simp only [regPullP1]; linarith)
    (by simp only [regPullP1]; linarith)

/-- `hv'` and `hVs'` of `dz2d2Op` (the pulling salvo, phase `2`). -/
theorem dz2d2_join {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} {m0 : ℕ}
    (hv : DiagValid regParams Vs Vb K q) (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0)
    (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) (hz : Vb ≤ 3 + 2 * (K + qMove q)) :
    DiagValid regParams (joinVs Vs regPullP2 ((16 : ℤ) + (((m0 + 6557) / 4 : ℕ) : ℤ))) Vb K
        (q ++ [(regPullP2, ((16 : ℤ) + (((m0 + 6557) / 4 : ℕ) : ℤ)))]) ∧
      -34 ≤ joinVs Vs regPullP2 ((16 : ℤ) + (((m0 + 6557) / 4 : ℕ) : ℤ)) +
        2 * (((m0 + 6557) / 4 : ℕ) : ℤ) :=
  join_both regPullP2_fits hv hval hQ (by omega) (by norm_num)
    (by simp only [regPullP2]; norm_num) hVs (by simp only [regPullP2]; linarith)
    (by simp only [regPullP2]; linarith)

/-- `hv'` and `hVs'` of `dz2d3Op` (the pulling salvo, phase `3`). -/
theorem dz2d3_join {q : List (Salvo × ℤ)} {Vs Vb K : ℤ} {m0 : ℕ}
    (hv : DiagValid regParams Vs Vb K q) (hval : 0 ≤ K + qMove q) (hQ : QBefore q m0)
    (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) (hz : Vb ≤ 3 + 2 * (K + qMove q)) :
    DiagValid regParams (joinVs Vs regPullP3 ((16 : ℤ) + (((m0 + 6558) / 4 : ℕ) : ℤ))) Vb K
        (q ++ [(regPullP3, ((16 : ℤ) + (((m0 + 6558) / 4 : ℕ) : ℤ)))]) ∧
      -34 ≤ joinVs Vs regPullP3 ((16 : ℤ) + (((m0 + 6558) / 4 : ℕ) : ℤ)) +
        2 * (((m0 + 6558) / 4 : ℕ) : ℤ) :=
  join_both regPullP3_fits hv hval hQ (by omega) (by norm_num)
    (by simp only [regPullP3]; norm_num) hVs (by simp only [regPullP3]; linarith)
    (by simp only [regPullP3]; linarith)

namespace LP

/-- Every pushing salvo fits, its reaction reaches down to `-14`, and at its offset base it is
above `-34`. -/
theorem pushSalvo_facts (j : ℕ) : SalvoFits regParams (pushSalvo j) ∧
    -14 ≤ (pushSalvo j).za + (pushSalvo j).zlo ∧ 6 ≤ pushBase j ∧
    -34 ≤ (pushSalvo j).a + (pushSalvo j).lo - 2 * pushBase j := by
  rcases j with _ | _ | _ | j
  · exact ⟨regPush_fits, by simp only [pushSalvo, regPush]; norm_num,
      by simp only [pushBase]; norm_num, by simp only [pushSalvo, regPush, pushBase]; norm_num⟩
  · exact ⟨regPushP1_fits, by simp only [pushSalvo, regPushP1]; norm_num,
      by simp only [pushBase]; norm_num, by simp only [pushSalvo, regPushP1, pushBase]; norm_num⟩
  · exact ⟨regPushP2_fits, by simp only [pushSalvo, regPushP2]; norm_num,
      by simp only [pushBase]; norm_num, by simp only [pushSalvo, regPushP2, pushBase]; norm_num⟩
  · exact ⟨regPushP3_fits, by simp only [pushSalvo, regPushP3]; norm_num,
      by simp only [pushBase]; norm_num, by simp only [pushSalvo, regPushP3, pushBase]; norm_num⟩

/-- The strip bound of a register after the increment `RegS.pushAny`. -/
def RegS.pushVs (R : RegS) : ℤ := joinVs R.Vs (pushOf R.m).1 (pushOf R.m).2

/-- **The increment keeps the register invariant, every phase**: `hv'` and `hVs'` of
`dz2eAny_module` (and `RegS.inv_pushAny`) with the strip bound `RegS.pushVs`, if the queue was
launched before `R.m` and the value is at least `(Vb + 14) / 2`. -/
theorem RegS.pushAny_join {R : RegS} (hR : R.Inv) (hQ : QBefore R.q R.m)
    (hz : R.Vb + 14 ≤ 2 * (R.K + qMove R.q)) :
    DiagValid regParams R.pushVs R.Vb R.K (R.q ++ [pushOf R.m]) ∧
      -34 ≤ R.pushVs + 2 * (((R.m + 6653 + incPhase R.m) / 4 : ℕ) : ℤ) := by
  obtain ⟨hv, -, hVs, hval⟩ := hR
  obtain ⟨hσ, hzl, hb6, hb⟩ := pushSalvo_facts (incPhase R.m)
  have := DiagValid.vb_le regParams _ R.q R.Vs R.Vb R.K rfl hv
  have hd := pushSalvo_d (incPhase R.m)
  exact join_both hσ hv hval hQ (by omega) hb6 hb hVs (by linarith) (by rw [hd]; linarith)

/-- The increment keeps the invariant and `QBefore`. -/
theorem RegS.inv_pushAny_join {R : RegS} (hR : R.Inv) (hQ : QBefore R.q R.m)
    (hz : R.Vb + 14 ≤ 2 * (R.K + qMove R.q)) :
    (R.pushAny R.pushVs).Inv ∧ QBefore (R.pushAny R.pushVs).q (R.pushAny R.pushVs).m := by
  obtain ⟨hv', hVs'⟩ := RegS.pushAny_join hR hQ hz
  refine ⟨RegS.inv_pushAny hR hv' hVs', ?_⟩
  simp only [RegS.pushAny]
  refine hQ.append (by omega) _ _ ?_
  have hj : incPhase R.m < 4 := Nat.mod_lt _ (by norm_num)
  have hb : pushBase (incPhase R.m) ≤ 7 := by
    rcases (incPhase R.m) with _ | _ | _ | j <;> simp [pushBase]
  have : (R.m + 6653 + incPhase R.m) / 4 + 83 ≤ (R.m + 6990) / 4 := by omega
  have : (((R.m + 6653 + incPhase R.m) / 4 : ℕ) : ℤ) + 83 ≤ (((R.m + 6990) / 4 : ℕ) : ℤ) := by
    exact_mod_cast this
  change pushBase (incPhase R.m) + (((R.m + 6653 + incPhase R.m) / 4 : ℕ) : ℤ) + 24 ≤ _
  linarith

end LP

end LeanTheory.Life
