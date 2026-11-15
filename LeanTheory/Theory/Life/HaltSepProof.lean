/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.RouteSep4
public import LeanTheory.Theory.Life.LaneSep2
public import LeanTheory.Theory.Computability.CounterMachineSingleHalt

/-!
# The separation facts of the halt activation

The field `haltSep` of `MachineSteps` (`MainTheorem`): `HaltSep p (p.length - 1)` for every
well-formed program `p` with a single `halt` (`Program.SingleHalt`).

* **`pre` and `relay`**, from the route separation of the halt line (`haltLink_sep`): the
  control world line `ctrlWL p a` is the layout's halt glider `unitWL p a haltDWL` delayed by
  `-1080 ≡ 0 (mod 30)` (`hsep_ctrlWL_eq`), whose route condition `RouteSepX` holds from template
  time `917 - 1080 < 0`, so from the start of the activation (`hsep_route`). The flight clause is
  `pre` (up to `meetT - 20 = 2837`); the relay clause is `relay`, the relay box of `HaltSep` lying
  inside the extended relay box `relayBoxX` (`hsep_relayBox_sub`).
* **`fly`** (`hsep_fly`): after the corner the `SW` glider runs on the top track `v = V_T + 1`,
  left of the column `A_a + 14`. The units end at `v ≤ V_U + 1527 = V_T - 117`, the modules and
  the band, left and right corners start far above, the slab corners lie at `v ≤ V_U + 76`; the
  only other corners on the top track would be halt corners of other units, and with a single
  `halt` there are none (`Desc`: a halt place belongs to a `halt` instruction). Its own reflector
  is behind it (`out_far`).
* **The assembly** `hsep_haltSep`, with the lane fields `haltLanes`, `haltLaneMach`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-- The control of unit `a` is the layout's halt glider of the unit, `1080` generations early. -/
theorem hsep_ctrlWL_eq (p : Program) (a : ℕ) :
    ctrlWL p a = (unitWL p a haltDWL).shift 0 0 (-1080) := by
  simp only [ctrlWL, unitWL, WL.shift, haltDWL, WL.mk.injEq, true_and]
  constructor <;> ring

/-- **The route condition of the control of a `halt` unit**, from the start of the activation. -/
theorem hsep_route {p : Program} (hp : p.WellFormed) {a : ℕ} (hi : p[a]? = some .halt) :
    RouteSepX (machPieces p) (machRegion p) (ctrlWL p a) (haltCorners p a) 0 := by
  rw [hsep_ctrlWL_eq]
  exact haltLink_sep hp hi (by norm_num) (by norm_num)

/-- The relay box of `HaltSep` lies in the extended relay box of the halt corner. -/
theorem hsep_relayBox_sub (p : Program) (a : ℕ) :
    haltRelayBox p a ⊆ relayBoxX (haltCorner p a) := by
  rintro _ ⟨y, ⟨h1, h2, h3, h4⟩, rfl⟩
  simp only [relayBoxX, rxB, rxBox, haltCorner, cornerV, mem_box, Prod.fst_add, Prod.snd_add]
  omega

/-- **The field `pre` of `HaltSep`**: the control's flight up to `20` generations before the
corner is far from every piece. -/
theorem hsep_pre {p : Program} (hp : p.WellFormed) {a : ℕ} (hi : p[a]? = some .halt) :
    ∀ t : ℕ, t < 2837 → ∀ h ∈ machPieces p, FarApart 2 ((ctrlWL p a).box t) h.box := by
  intro t ht h hh
  obtain ⟨-, hfl, -⟩ := hsep_route hp hi
  have hm := haltMeet p a
  exact hfl t (by omega) (by change (t : ℤ) < meetT (ctrlWL p a) (haltCorner p a) - 20; omega)
    h hh

/-- **The field `relay` of `HaltSep`**: the relay box of the halt corner is far from every piece
other than its reflector. -/
theorem hsep_relay {p : Program} (hp : p.WellFormed) {a : ℕ} (hi : p[a]? = some .halt) :
    ∀ h ∈ machPieces p, h ≠ haltRfP p a → FarApart 2 (haltRelayBox p a) h.box := by
  intro h hh hne
  obtain ⟨-, -, -, ⟨L', hperm, hL'⟩, -⟩ := hsep_route hp hi
  have hm := hperm.subset hh
  rcases List.mem_cons.1 hm with he | hm
  · exact absurd (he.trans (haltRf_eq p a)) hne
  · exact (hL' h hm).mono (hsep_relayBox_sub p a) le_rfl

/-- The halt corner has the parity of its image. -/
theorem hsep_cpar (p : Program) (a : ℕ) : CPar (haltCorner p a) := by
  have := trackOut_par p 0 0 (A p a + haltD)
  simp only [CPar, haltCorner, rfCU, rfCV, haltD] at this ⊢
  omega

/-- With a single `halt`, the only halt place of the machine is the one of the last unit. -/
theorem hsep_halt_tag {p : Program} (hs : p.SingleHalt) {c : Corner} (hd : Desc p c) {a' : ℤ}
    (ht : c.tag = .halt a') : a'.toNat = p.length - 1 ∧ 0 ≤ a' := by
  have hv := hd.1
  have hh := hd.2.2.1 a' ht
  have hlt : a'.toNat < p.length := (List.getElem?_eq_some_iff.1 hh).1
  obtain ⟨k, u, v, tag⟩ := c
  simp only at ht
  subst ht
  simp only [Valid] at hv
  refine ⟨?_, hv.1⟩
  by_contra hne
  exact hs a'.toNat (by omega) hh

/-- **The field `fly` of `HaltSep`**: for a well-formed program with a single `halt`, the `SW`
flight of the last unit's halt glider on the top track is far from every piece, from `40`
generations after the corner on. -/
theorem hsep_fly {p : Program} (hp : p.WellFormed) (hs : p.SingleHalt) {a : ℕ}
    (hi : p[a]? = some .halt) (ha : a = p.length - 1) :
    ∀ t : ℕ, 2897 ≤ t → t < haltTime p a → ∀ h ∈ machPieces p,
      FarApart 2 ((haltOutWL p a).box t) h.box := by
  intro t ht _ h hh
  have hlt : a < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have hf := layout_facts p
  have hc : haltCorner p a ∈ allCorners p :=
    instrRoute_corner hlt (x := (unitWL p a haltDWL, haltCorners p a))
      (by simp [instrSpecs, hi]) _ (by simp [haltCorners_eq])
  have hpar := hsep_cpar p a
  have hm := haltMeet p a
  have hw : haltOutWL p a = outWL (haltCorner p a) (delayS (ctrlWL p a) (haltCorner p a)) :=
    reflect_snd _ _
  have hs1 : delayS (ctrlWL p a) (haltCorner p a) = 2917 := by unfold meetT at hm; omega
  rw [hs1] at hw
  obtain ⟨hu, hv⟩ := haltCorner_uv p a
  have hcen : Ray 3 (haltCorner p a).u (haltCorner p a).v ((haltOutWL p a).cu t)
      ((haltOutWL p a).cv t) 13 := by
    rw [hw]
    exact out_center (k := 3) (by norm_num) hpar (s := 2917) (t := t) (by omega)
  have hown : (gbx (haltOutWL p a) t).Far (cornerSpec (haltCorner p a)).bx := by
    rw [hw]
    exact out_far (k := 3) (by norm_num) (.halt a) hpar (s := 2917) (t := t) (by omega)
  simp only [Ray] at hcen
  refine flight_far hp [haltCorner p a] (u1 := (haltOutWL p a).cu t - 4) (u2 := A p a + 5)
    (v1 := VT p - 1) (v2 := VT p + 7) ?_ ?_ ?_ ?_ ?_ ?_ h hh
  · intro c hc'
    rw [List.mem_singleton.1 hc']
    exact hc
  · intro c hc'
    rw [List.mem_singleton.1 hc']
    exact hown
  · refine ⟨le_rfl, ?_, ?_, ?_⟩ <;> omega
  · intro a' s _ hs'
    refine farRect_of_uv (unitSpecs_uv p a' hs') (Or.inr (Or.inr (Or.inl ?_)))
    omega
  · intro r s _ hs'
    refine farRect_of_uv (moduleSpecs_uv p r hs').1 (Or.inr (Or.inr (Or.inr ?_)))
    omega
  · refine allCorners_split hp hlt
      (Q := fun c' => (∀ c ∈ [haltCorner p a], c'.tag ≠ c.tag) →
        FarRect (cornerSpec c').bx ((haltOutWL p a).cu t - 4) (A p a + 5) (VT p - 1) (VT p + 7))
      ?_ ?_
    · intro c' hc' hne
      rw [instrCorners_halt hi, haltCorners_eq, List.mem_singleton] at hc'
      exact absurd hc' (fun e => hne _ List.mem_cons_self (by rw [e]))
    · intro c' _ hd _ hne
      have hv' := hd.1
      refine corner_farRect ?_
      obtain ⟨k', u', v', tag'⟩ := c'
      cases tag' with
      | band b n h => simp only [Valid] at hv' ⊢; omega
      | halt a' =>
        obtain ⟨h1, h2⟩ := hsep_halt_tag hs hd rfl
        exact absurd (by simp only [haltCorner, CTag.halt.injEq]; omega)
          (hne _ List.mem_cons_self)
      | slab a' t' => simp only [Valid] at hv' ⊢; omega
      | left r idx => simp only [Valid] at hv' ⊢; omega
      | right r j w => simp only [Valid] at hv' ⊢; omega

/-- **The separation facts of the halt activation** of the last unit, for every well-formed
program with a single `halt`: the field `haltSep` of `MachineSteps`. -/
theorem hsep_haltSep {p : Program} (hp : p.WellFormed) (hs : p.SingleHalt) :
    HaltSep p (p.length - 1) := by
  have hi : p[p.length - 1]? = some .halt := by
    rw [← List.getLast?_eq_getElem?]
    exact hp.2
  exact ⟨hsep_pre hp hi, hsep_relay hp hi, hsep_fly hp hs hi rfl, haltLanes p,
    haltLaneMach hp _⟩

end LP

end LeanTheory.Life
