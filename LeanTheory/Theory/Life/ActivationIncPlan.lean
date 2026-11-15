/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncStep

/-!
# The activation plan of an `inc` instruction, from the layout

Research note `N-22`, item (h): the layout-arithmetic hypothesis `IncPlan.Valid` of
`inc_step_of_plan` is discharged. For every well-formed program `p` and every instruction
`p[i]? = some (.inc r)`, `incPlan p i r` reads the plan off the layout (`incSpecs`, `mergeSpecs`):

* the corners of the continue and of the INC link are those of `incSpecs p i r`
  (`incSpecs_eq`), the corners of the merge link those of `mergeSpecs p r`;
* the entry copies, window offsets and periods are given by the arrival times (`arrival_eq`);
* the merge link starts at the time the merge unit's chain releases the control; delayed by a
  multiple of `30` it has the reflectors of `mergeSpecs` (`route_delay`).

`incPlan_valid` proves every field of `IncPlan.Valid`: the lines (`unitLink_lines`,
`mergeCorners_lines`), the route law with corner windows (`unitLink_timedX`, `mergeLink_timedX`),
the arrivals (`incLink_offset`, `mergeLink_offset`), the ends of the routes (`upLink_endX`,
`routeEndX_snoc`),
the order `late` (the continue's delay `G` of `incSpecs` against the time `tinc` at which the
increment starts: `Tg = tinc - 1 - δm`, and the continue arrives at least `G`-delayed after the
corner `t0`) and the membership of the active pieces in `machPieces`.

`inc_step` is `inc_step_of_plan` with this plan: only the separation (`IncSep`) and region
(`IncRegion`) facts remain as hypotheses.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The quantities of `incSpecs` -/

/-- The source column of the INC link of instruction `i`. -/
def incCl (p : Program) (i : ℕ) : ℤ := A p i + incR

/-- The entry copy of the INC link at the merge unit of register `r`. -/
def incTl (p : Program) (i r : ℕ) : ℤ :=
  copyIdx C0halt (predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0)) (incCl p i)

/-- The corners of the INC link, with `e` hairpin steps. -/
def incMkl (p : Program) (i r : ℕ) (e : ℤ) : List Corner :=
  upCorners p (instrBand i) 1 (incCl p i) (hairReg p 1 e (incCl p i)) (p.length + r) (incTl p i r)

/-- The hairpin steps of the INC link (window rule). -/
def incEl (p : Program) (i r : ℕ) : ℤ :=
  solveE (unitWL p i incRWL) (incMkl p i r) (destWin p (p.length + r) (incTl p i r))

/-- The arriving world line of the INC link. -/
def incGl (p : Program) (i r : ℕ) : WL := (route (unitWL p i incRWL) (incMkl p i r (incEl p i r))).2

/-- The output world line of the merge unit used by `incSpecs` for the timing. -/
def incGm (p : Program) (i r : ℕ) : WL :=
  (mergeOutWL (incTl p i r)).shift (unitDX p (p.length + r)) (unitDY p (p.length + r))
    (30 * (slot (incGl p i r) (destWin p (p.length + r) (incTl p i r)) - 20))

/-- The time at which the increment starts, as estimated by `incSpecs`. -/
def incTinc (p : Program) (i r : ℕ) : ℤ :=
  timeUV (route (incGm p i r) (mergeCorners p r (mergeE p r))).2 (U p r - 1087 + 1260)
    (U p r - 1087 - 1260)

/-- The source column of the continue of instruction `i`. -/
def incCc (p : Program) (i : ℕ) : ℤ := A p i + incD

/-- The entry copy of the continue at unit `i + 1`. -/
def incTc (p : Program) (i : ℕ) : ℤ :=
  copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (incCc p i)

/-- The corners of the continue, with delay `G` and `e` hairpin steps. -/
def incMkc (p : Program) (i : ℕ) (G e : ℤ) : List Corner :=
  upCorners p (instrBand i) 0 (incCc p i) (hairCont p G e (incCc p i)) (i + 1) (incTc p i)

/-- The hairpin steps of the continue without delay. -/
def incEc0 (p : Program) (i : ℕ) : ℤ :=
  solveE (unitWL p i incDWL) (incMkc p i 0) (destWin p (i + 1) (incTc p i))

/-- The time at which the undelayed continue reaches its fourth corner. -/
def incT0 (p : Program) (i : ℕ) : ℤ :=
  timeUV (route (unitWL p i incDWL) ((incMkc p i 0 (incEc0 p i)).take 3)).2
    (destU p (i + 1) (incTc p i)) (trackBack p (instrBand i) 0 (incCc p i))

/-- The delay of the continue. -/
def incG (p : Program) (i r : ℕ) : ℤ :=
  30 * ceil120 (max 0 (incTinc p i r + 8500 - incT0 p i))

/-- The hairpin steps of the delayed continue. -/
def incEc (p : Program) (i r : ℕ) : ℤ :=
  solveE (unitWL p i incDWL) (incMkc p i (incG p i r)) (destWin p (i + 1) (incTc p i))

/-- **`incSpecs` in terms of the named quantities.** -/
theorem incSpecs_eq (p : Program) (i r : ℕ) :
    incSpecs p i r = [(unitWL p i incDWL, incMkc p i (incG p i r) (incEc p i r)),
      (unitWL p i incRWL, incMkl p i r (incEl p i r))] := rfl

/-! ### Arithmetic of the routes -/

/-- A world line shifted by nothing. -/
theorem WL.shift_zero (w : WL) : w.shift 0 0 0 = w := by
  simp [WL.shift]

/-- **The arrival of an up-going link from its fourth corner**: the reference time of the
arriving world line, in terms of the time `t3` at which the glider reaches the fourth corner
`(destU, BACK)`. -/
theorem upCorners_tau_t3 (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) (g : WL)
    (hH : (H - c) % 2 = 0) (hd : (destU p a t - c) % 2 = 0)
    (hv : (destU p a t + destV p t) % 2 = 1) :
    (route g (upCorners p b s c H a t)).2.tau =
      timeUV (route g ((upCorners p b s c H a t).take 3)).2 (destU p a t) (trackBack p b s c) -
        2 * destU p a t + 2 * trackBack p b s c - 4 * destV p t - 10 := by
  have ho := trackOut_par p b s c
  have hb := trackBack_par p b s c
  simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append, route,
    reflect, WL.shift, rfIn, rfOut, rfX, rfY, rfCU, rfCV, List.take, timeUV]
  omega

/-- A continue hairpin moved by an even delay `G` and `e` steps. -/
theorem hairCont_G (p : Program) (G e c : ℤ) (hG : G % 2 = 0) :
    hairCont p G e c = hairCont p 0 0 c - G - 2 * e := by
  unfold hairCont fixp
  omega

/-- **The route law with corner windows for a link from a unit output to an entry copy**
(`unitLink_timed` with `RouteTimedX`). -/
theorem unitLink_timedX (p : Program) (i a : ℕ) (w τ b s H e' d : ℤ)
    (hw : (w = 68 ∧ τ = 605) ∨ (w = 157 ∧ τ = 1029)) (hb : 0 ≤ b) (hs : 0 ≤ s ∧ s ≤ 4)
    (hH : (H - (A p i + w)) % 2 = 0) (hHI : H ≤ HI p + 90) (he : 0 ≤ e' ∧ e' < P p) :
    RouteTimedX ((unitWL p i ⟨1, 1, w, τ⟩).shift 0 0 d)
      (upCorners p b s (A p i + w) H a (copyIdx (unitC0 p a) e' (A p i + w))) (2010 + d) := by
  have hu := unitD_uv p i
  have ha := A_even p a
  have hai := A_even p i
  have hv := VU_even p
  have hc := copyBeta_spec (unitC0 p a) e' (A p i + w)
  have hr := copyIdx_range p (C0 := unitC0 p a) (c := A p i + w) he
  have hC0 : unitC0 p a % 2 = 1 ∧ -237 ≤ unitC0 p a := by
    obtain h | h | h := unitC0_cases p a <;> rw [h] <;> exact ⟨rfl, by norm_num⟩
  have hA0 := A_nonneg p (a := a) (by omega)
  have hAi := A_nonneg p (a := i) (by omega)
  have hHI' : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hVT := VT_mod p
  refine upCorners_timedX p b s (A p i + w) H a _ (g := (unitWL p i ⟨1, 1, w, τ⟩).shift 0 0 d)
    rfl rfl ?_ hH ?_ ?_ (2010 + d) ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift]; omega
  · simp only [destU, inCol] at hc ⊢; omega
  · simp only [destU, destV, inCol, sideV]; omega
  · simp only [unitWL, WL.shift, trackOut, track, VU] at hu ⊢
    rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · omega
  · simp only [destU, inCol]; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [destV, sideV, trackBack, track, VU]; omega

/-- **The route law with corner windows for the merge link** (`mergeLink_timed` with
`RouteTimedX`), from the time `T` at which the glider leaves the merge unit's chain
(`T ≤ tau + 914`). -/
theorem mergeLink_timedX (p : Program) {r : ℕ} (hr : (r : ℤ) < R p) (e : ℤ) (he : 0 ≤ e)
    (D' T : ℤ) (hT : T ≤ D' + 914) :
    RouteTimedX ((unitWL p (p.length + r) haltDWL).shift 0 0 D') (mergeCorners p r e) T := by
  have hu := unitD_uv p (p.length + r)
  have hA := A_even p (p.length + r)
  have hA0 := A_nonneg p (a := ((p.length + r : ℕ) : ℤ)) (by omega)
  push_cast at hu hA hA0
  have hU := U_even p r
  have hUg := U_ge p (r := r) (by omega)
  have hc := incChan_even p
  have hcb := fixp_bounds (uL - 62 * (2 * D p)) (1 - incPortV % 2)
  have hHI : HI p ≤ -716 - 122 * P p := by unfold HI; omega
  have hP := one_le_P p
  have hD := one_le_D p
  have h3 := (sep03_band_modules p).1
  have hH := hairReg_le p (s := 0) (e := e) (c := A p (p.length + r) + haltD) (by norm_num) he
  have hVT := VT_mod p
  have hmb : 1 ≤ mergeBand p r := by unfold mergeBand N; omega
  simp only [mergeCorners]
  refine downCorners_timedX p _ 0 _ _ _ _ r _
    (g := (unitWL p (p.length + r) haltDWL).shift 0 0 D')
    rfl rfl ?_ (hairReg_par _ _ _ _) ?_ ?_ T ?_ ?_ ?_ ?_ ?_
  · simp only [unitWL, WL.shift, haltDWL, haltD]; omega
  · simp only [haltD]; omega
  · simp only [incPortV]; omega
  · simp only [unitWL, WL.shift, trackOut, track, VU, haltDWL, haltD] at hu ⊢; omega
  · simp only [haltD] at hH ⊢; omega
  · simp only [incChan, leftChan, uL, modLeft, slabR] at hcb hUg ⊢
    have := le_max_left (238 : ℤ) (86 + 58 * P p)
    simp only [haltD] at hH ⊢; omega
  · simp only [trackOut, trackBack, track]; omega
  · simp only [trackBack, track, incPortV, mergeBand, NB, modTop, N, R] at h3 hr ⊢; omega

/-- **The facts of a link from a unit output to an entry copy** (continue or INC link), started
at `2010`: lines, route law, the copy is in range, arrival on the window of the copy (with offset
and periods read off the arrival time), and the arrival time `T0` (`entry_time`) after the end
of the route. -/
theorem upLink_plan (p : Program) (i a : ℕ) (w τ b s H e' : ℤ)
    (hw : (w = 68 ∧ τ = 605) ∨ (w = 157 ∧ τ = 1029)) (hb : 0 ≤ b) (hs : 0 ≤ s ∧ s ≤ 4)
    (hH : (H - (A p i + w)) % 2 = 0) (hHI : H ≤ HI p + 90) (he : 0 ≤ e' ∧ e' < P p)
    {g : WL} {t : ℤ} {cs : List Corner} (hg : g = unitWL p i ⟨1, 1, w, τ⟩)
    (ht : t = copyIdx (unitC0 p a) e' (A p i + w)) (hcs : cs = upCorners p b s (A p i + w) H a t) :
    RouteLines g cs ∧ RouteTimedX g cs ((2010 : ℕ) : ℤ) ∧ 0 ≤ t ∧ t < 2 * P p ∧
      (route g cs).2 = (destWin p a ((t.toNat : ℕ) : ℤ)).shift 0 0
        (((route g cs).2.tau - (destWin p a t).tau) % 30 +
          30 * (((route g cs).2.tau - (destWin p a t).tau) / 30)) ∧
      (routeEndX g cs 2010 : ℤ) + 16 ≤
        180 + 30 * (((route g cs).2.tau - (destWin p a t).tau) / 30) + 16 * t % 30 := by
  subst hg hcs
  obtain ⟨hl, hdx, hdy, hth⟩ := unitLink_lines p i a w τ b s H e' hH
  have htim := unitLink_timedX p i a w τ b s H e' 0 hw hb hs hH hHI he
  rw [WL.shift_zero, add_zero] at htim
  have hr := copyIdx_range p (C0 := unitC0 p a) (c := A p i + w) he
  rw [← ht] at hl hdx hdy hth htim hr
  have hv : (destU p a t + destV p t) % 2 = 1 := by
    have := inCol_side_odd t
    obtain h | h | h := unitC0_cases p a <;>
      simp only [destU, destV, h, C0dec, C0inc, C0halt] at this ⊢ <;> have := VU_even p <;>
      have := A_even p a <;> omega
  have hend := upLink_endX p b s (A p i + w) H a t (unitWL p i ⟨1, 1, w, τ⟩) 2010 htim hv
  have harr := arrival_eq p a t hdx hdy hth
  have htN : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg hr.1
  refine ⟨hl, htim, hr.1, hr.2.1, ?_, ?_⟩
  · rw [htN]
    exact harr
  · have hA := A_even p a
    have hVU := VU_even p
    have hC := unitC0_cases p a
    simp only [destWin, unitWL, sideWL, WL.shift, destU, destV, inCol, sideV, unitDX] at hend ⊢
    omega

/-- **The arrival on the INC window of module `r`** (the analogue of `arrival_eq`): a glider
flying `NE` through the INC port corner, delayed by `d`, is the window delayed by the residue and
the periods of its arrival. -/
theorem incWin_arrival (p : Program) (r : ℕ) {f : WL} (hdx : f.dx = 1) (hdy : f.dy = -1)
    (ht : f.Through (U p r + incChan p) incPortV) (d : ℤ) :
    f.shift 0 0 d = (modWL p r incWin).shift 0 0
      ((f.tau + d - (modWL p r incWin).tau) % 30 +
        30 * ((f.tau + d - (modWL p r incWin).tau) / 30)) := by
  obtain ⟨dx, dy, lane, tau⟩ := f
  simp only at hdx hdy
  subst hdx hdy
  simp only [WL.Through, incPortV] at ht
  simp only [WL.shift, modWL, incWin, modDX, modDY, WL.mk.injEq, true_and]
  constructor <;> omega

/-- The time `tinc` of a glider arriving on the INC window of module `r`. -/
theorem incWin_timeUV (p : Program) (r : ℕ) {f : WL} (hdx : f.dx = 1) (hdy : f.dy = -1)
    (ht : f.Through (U p r + incChan p) incPortV) :
    timeUV f (U p r - 1087 + 1260) (U p r - 1087 - 1260) =
      f.tau - (modWL p r incWin).tau + 195 := by
  have hU := U_even p r
  obtain ⟨dx, dy, lane, tau⟩ := f
  simp only at hdx hdy
  subst hdx hdy
  simp only [WL.Through, incPortV] at ht
  simp only [timeUV, modWL, incWin, WL.shift, modDX]
  omega

/-! ### Membership in the machine -/

/-- A spec of the machine gives a piece of the machine. -/
theorem piece_mem_mach {p : Program} {s : PSpec} (h : s ∈ machSpecs p) :
    s.piece ∈ machPieces p :=
  List.mem_map_of_mem h

/-- The pieces of a used unit are pieces of the machine. -/
theorem unitSpecs_mem {p : Program} {a : ℕ} (ha : a < p.length + numRegs p)
    (hu : unitUsed p a = true) {s : PSpec} (hs : s ∈ unitSpecs p a) : s.piece ∈ machPieces p :=
  piece_mem_mach (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨a, List.mem_filter.2 ⟨List.mem_range.2 ha, hu⟩, hs⟩)))

/-- The pieces of a module are pieces of the machine. -/
theorem moduleSpecs_mem {p : Program} {r : ℕ} (hr : r < numRegs p) {s : PSpec}
    (hs : s ∈ moduleSpecs p r) : s.piece ∈ machPieces p :=
  piece_mem_mach (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, hs⟩)))

/-- The reflectors of the routes of an instruction are pieces of the machine. -/
theorem instrRoutes_mem {p : Program} {i : ℕ} (hi : i < p.length) {s : PSpec}
    (hs : s ∈ routeSpecs (instrSpecs p i)) : s.piece ∈ machPieces p :=
  piece_mem_mach (List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hs⟩)))

/-- The reflectors of a used merge route are pieces of the machine. -/
theorem mergeRoutes_mem {p : Program} {r : ℕ} (hr : r < numRegs p) (hm : mergeUsed p r = true)
    {s : PSpec} (hs : s ∈ routeSpecs (mergeSpecs p r)) : s.piece ∈ machPieces p :=
  piece_mem_mach (List.mem_append_right _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨r, List.mem_filter.2 ⟨List.mem_range.2 hr, hm⟩, hs⟩)))

/-- The first `t + 1` copies of an entry chain are copies of the full chain. -/
theorem chainSpecs_mono {t n : ℕ} (h : t < n) {dx dy : ℤ} {s : PSpec}
    (hs : s ∈ chainSpecs (t + 1) dx dy) : s ∈ chainSpecs n dx dy := by
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hs
  exact List.mem_map.2 ⟨t', List.mem_range.2 (by have := List.mem_range.1 ht'; omega), rfl⟩

/-- The copies `0 … t` of the entry chain of a used unit are pieces of the machine. -/
theorem chainPieces_mem {p : Program} {a t : ℕ} (ha : a < p.length + numRegs p)
    (hu : unitUsed p a = true) (ht : (t : ℤ) < 2 * P p) :
    ∀ x ∈ chainPieces p a t, x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  refine unitSpecs_mem ha hu (List.mem_append_left _ (chainSpecs_mono ?_ hs))
  unfold P at ht
  omega

/-- The register circuit, `RF_J` and the INC gate are pieces of the module. -/
theorem mem_moduleSpecs_head {p : Program} {r : ℕ} {s : PSpec}
    (h : s ∈ groupSpecs ((List.range 28).map Base.dz2g) (modDX p r) (modDY p r) ++
      [⟨.rf 4, modDX p r - 850, modDY p r - 1044, 25⟩,
        ⟨.orGate, modDX p r - 1132, modDY p r - 1291, 16⟩]) : s ∈ moduleSpecs p r := by
  unfold moduleSpecs
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ h)))

/-- A register with an `inc` instruction has its merge unit. -/
theorem mergeUsed_of_inc {p : Program} {i r : ℕ} (hins : p[i]? = some (.inc r)) :
    mergeUsed p r = true :=
  List.any_eq_true.2 ⟨.inc r, List.mem_of_getElem? hins, by simp [isIncOn]⟩

/-! ### The plan -/

/-- The arrival of the continue relative to the window of its entry copy. -/
def incXc (p : Program) (i r : ℕ) : ℤ :=
  (route (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r))).2.tau -
    (destWin p (i + 1) (incTc p i)).tau

/-- The arrival of the INC link relative to the window of its entry copy. -/
def incXl (p : Program) (i r : ℕ) : ℤ :=
  (incGl p i r).tau - (destWin p (p.length + r) (incTl p i r)).tau

/-- The arrival time of the INC link at the side input of the merge unit. -/
def incT0l (p : Program) (i r : ℕ) : ℕ :=
  (180 + 30 * (incXl p i r / 30) + 16 * incTl p i r % 30).toNat

/-- The time at which the merge unit's chain releases the INC control. -/
def incT1 (p : Program) (i r : ℕ) : ℕ := incT0l p i r + (134 + (incTl p i r).toNat * 254)

/-- The arrival of the merge link relative to the INC window of module `r`. -/
def incXm (p : Program) (i r : ℕ) : ℤ :=
  (route (unitWL p (p.length + r) haltDWL) (mergeCorners p r (mergeE p r))).2.tau +
    ((incT1 p i r : ℤ) + 166 - 1080) - (modWL p r incWin).tau

/-- **The activation plan of `inc r` at instruction `i`, read off the layout.** -/
def incPlan (p : Program) (i r : ℕ) : IncPlan p i r where
  csC := incMkc p i (incG p i r) (incEc p i r)
  tc := (incTc p i).toNat
  δc := incXc p i r % 30
  kc := incXc p i r / 30
  T0c := (180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30).toNat
  csR := incMkl p i r (incEl p i r)
  tl := (incTl p i r).toNat
  δl := incXl p i r % 30
  kl := incXl p i r / 30
  T0l := incT0l p i r
  csM := mergeCorners p r (mergeE p r)
  δm := incXm p i r % 30
  km := incXm p i r / 30
  Tg := (194 + 30 * (incXm p i r / 30)).toNat

/-- **The plan of every `inc` instruction of a well-formed program is valid.** -/
theorem incPlan_valid {p : Program} {i r : ℕ} (hp : p.WellFormed)
    (hins : p[i]? = some (.inc r)) : (incPlan p i r).Valid := by
  have hi1 : i + 1 < p.length := succ_lt_of_inc hp hins
  have hr : r < numRegs p := lt_numRegs_of_inc hins
  have hR : (r : ℤ) < R p := by unfold R; exact_mod_cast hr
  have hbi : 0 ≤ instrBand i := by unfold instrBand; omega
  have hec : 0 ≤ predIdx p (i + 1) i 0 ∧ predIdx p (i + 1) i 0 < P p :=
    ⟨predIdx_nonneg _ _ _ _, predIdx_lt_P p hins (by simp [predContrib]) (by omega)⟩
  have hel : 0 ≤ predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0) ∧
      predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0) < P p :=
    ⟨predIdx_nonneg _ _ _ _, predIdx_lt_P p hins (by simp [predContrib]) (by omega)⟩
  -- the continue
  have hGe : 0 ≤ incG p i r := G_nonneg _
  have hecB : 0 ≤ incEc p i r ∧ incEc p i r ≤ 14 := solveE_bounds _ _ _
  have hHc := fixp_bounds (HI p - 62 - incG p i r - 2 * incEc p i r) ((A p i + incD) % 2)
  obtain ⟨lC, tC, tc0, tc1, fC, eC⟩ := upLink_plan p i (i + 1) incD 605 (instrBand i) 0
    (hairCont p (incG p i r) (incEc p i r) (A p i + incD)) (predIdx p (i + 1) i 0)
    (Or.inl ⟨rfl, rfl⟩) hbi (by norm_num) (hairCont_par _ _ _ _)
    (by unfold hairCont; omega) hec (g := unitWL p i incDWL)
    (t := incTc p i) (cs := incMkc p i (incG p i r) (incEc p i r)) rfl rfl rfl
  -- the INC link
  have helB : 0 ≤ incEl p i r ∧ incEl p i r ≤ 14 := solveE_bounds _ _ _
  obtain ⟨lR, tR, tl0, tl1, fR, eR⟩ := upLink_plan p i (p.length + r) incR 1029 (instrBand i) 1
    (hairReg p 1 (incEl p i r) (A p i + incR))
    (predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0))
    (Or.inr ⟨rfl, rfl⟩) hbi (by norm_num) (hairReg_par _ _ _ _)
    (by have := fixp_bounds (HI p + 90 * 1 - 2 * incEl p i r) ((A p i + incR) % 2)
        unfold hairReg; omega) hel (g := unitWL p i incRWL)
    (t := incTl p i r) (cs := incMkl p i r (incEl p i r)) rfl
    (by rw [unitC0_merge]; rfl) rfl
  have hxc : (route (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r))).2.tau -
      (destWin p (i + 1) (incTc p i)).tau = incXc p i r := rfl
  have hxl : (route (unitWL p i incRWL) (incMkl p i r (incEl p i r))).2.tau -
      (destWin p (p.length + r) (incTl p i r)).tau = incXl p i r := rfl
  rw [hxc] at fC eC
  rw [hxl] at fR eR
  have hre := fun g cs T => (Int.natCast_nonneg (routeEndX g cs T))
  have htcN : (((incTc p i).toNat : ℕ) : ℤ) = incTc p i := Int.toNat_of_nonneg tc0
  have htlN : (((incTl p i r).toNat : ℕ) : ℤ) = incTl p i r := Int.toNat_of_nonneg tl0
  have hT0c : (((180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30).toNat : ℕ) : ℤ) =
      180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30 :=
    Int.toNat_of_nonneg (by
      have := hre (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r)) 2010
      omega)
  have hT0l : ((incT0l p i r : ℕ) : ℤ) = 180 + 30 * (incXl p i r / 30) + 16 * incTl p i r % 30 :=
    Int.toNat_of_nonneg (by
      have := hre (unitWL p i incRWL) (incMkl p i r (incEl p i r)) 2010
      omega)
  have oC : incXc p i r % 30 = 4 ∨ incXc p i r % 30 = 5 :=
    incLink_offset p i (i + 1) (instrBand i) (incG p i r) (predIdx p (i + 1) i 0) incD 605 0
      (hairCont p (incG p i r)) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  have oL : incXl p i r % 30 = 4 ∨ incXl p i r % 30 = 5 := by
    have := incLink_offset p i (p.length + r) (instrBand i) 0
      (predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0)) incR 1029 1
      (fun e c => hairReg p 1 e c) (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
    rw [unitC0_merge] at this
    exact this
  -- the merge link
  have hT1 : ((incT1 p i r : ℕ) : ℤ) =
      180 + 30 * (incXl p i r / 30) + 16 * incTl p i r % 30 + 134 + incTl p i r * 254 := by
    unfold incT1
    push_cast
    rw [hT0l, htlN]
    ring
  have hD : ((incT1 p i r : ℤ) + 166 - 1080) % 30 = 0 := by rw [hT1]; omega
  have hrd := route_delay _ hD (unitWL p (p.length + r) haltDWL) (mergeCorners p r (mergeE p r))
  have hA := A_even p ((p.length + r : ℕ) : ℤ)
  have hVU := VU_even p
  have hlane : ((unitWL p (p.length + r) haltDWL).shift 0 0 ((incT1 p i r : ℤ) + 166 - 1080)).lane =
      A p ((p.length + r : ℕ) : ℤ) + haltD := by
    simp only [WL.shift, unitWL, haltDWL, unitDX, unitDY, haltD]
    omega
  have hlane0 : (unitWL p (p.length + r) haltDWL).lane = A p ((p.length + r : ℕ) : ℤ) + haltD := by
    simp only [WL.shift, unitWL, haltDWL, unitDX, unitDY, haltD]
    omega
  obtain ⟨lM, dxM, dyM, thM⟩ := mergeCorners_lines p r (mergeE p r) rfl rfl hlane
  obtain ⟨-, dx0, dy0, th0⟩ := mergeCorners_lines p r (mergeE p r) rfl rfl hlane0
  have heM : 0 ≤ mergeE p r := (solveE_bounds _ _ _).1
  have tM := mergeLink_timedX p hR (mergeE p r) heM ((incT1 p i r : ℤ) + 166 - 1080)
    (incT1 p i r) (by omega)
  have fM := incWin_arrival p r dx0 dy0 th0 ((incT1 p i r : ℤ) + 166 - 1080)
  have hxm : (route (unitWL p (p.length + r) haltDWL) (mergeCorners p r (mergeE p r))).2.tau +
      ((incT1 p i r : ℤ) + 166 - 1080) - (modWL p r incWin).tau = incXm p i r := rfl
  have hrd2 : (route ((unitWL p (p.length + r) haltDWL).shift 0 0
      ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r))).2 =
      (route (unitWL p (p.length + r) haltDWL) (mergeCorners p r (mergeE p r))).2.shift 0 0
        ((incT1 p i r : ℤ) + 166 - 1080) := by rw [hrd]
  rw [hxm, ← hrd2] at fM
  have oM : incXm p i r % 30 = 4 ∨ incXm p i r % 30 = 5 := by
    have := mergeLink_offset p r
    rw [← hxm]
    omega
  have hU := U_even p r
  have hwin : (modWL p r incWin).tau = 4543 - 2 * U p r := by
    simp only [modWL, incWin, WL.shift, modDX]
    omega
  -- the end of the merge route
  have hend : (routeEndX ((unitWL p (p.length + r) haltDWL).shift 0 0
      ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r)) (incT1 p i r) : ℤ) =
      (route ((unitWL p (p.length + r) haltDWL).shift 0 0
        ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r))).2.tau -
        (rfOut 4).tau + 4 * (rfOut 4).dx * rfX 4 (U p r + incChan p) incPortV - 20 :=
    routeEndX_snoc (bandCorners p (mergeBand p r) 0 (A p (p.length + r) + haltD)
      (hairReg p 0 (mergeE p r) (A p (p.length + r) + haltD)) (U p r + incChan p) 3 2)
      ⟨4, U p r + incChan p, incPortV, .left r (2 * D p)⟩ _ _ tM
  have hpar := (incChan_parity p (p.length + r) r).2
  have hch : incChan p ≤ uL := (leftChan_in_extent p (idx := 2 * D p) (v := incPortV)
    ⟨by have := one_le_D p; omega, by have := one_le_D p; omega⟩).2
  have hfin : (route ((unitWL p (p.length + r) haltDWL).shift 0 0
      ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r))).2.tau =
      incXm p i r + (4543 - 2 * U p r) := by
    rw [hrd, ← hxm, hwin]
    simp only [WL.shift]
    ring
  rw [hfin] at hend
  simp only [rfOut, rfX, rfCU, rfCV] at hend
  have hTgN : (((194 + 30 * (incXm p i r / 30)).toNat : ℕ) : ℤ) = 194 + 30 * (incXm p i r / 30) :=
    Int.toNat_of_nonneg (by
      have := Int.natCast_nonneg (routeEndX ((unitWL p (p.length + r) haltDWL).shift 0 0
        ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r)) (incT1 p i r))
      simp only [incPortV, uL] at hend hpar hch
      omega)
  -- the time `tinc` of `incSpecs` is `Tg + 1 + δm`
  have hgm : incGm p i r = (unitWL p (p.length + r) haltDWL).shift 0 0
      ((incT1 p i r : ℤ) + 166 - 1080) := by
    have hs : slot (incGl p i r) (destWin p (p.length + r) (incTl p i r)) = incXl p i r / 30 := rfl
    simp only [incGm, mergeOutWL, WL.shift, unitWL, haltDWL, hs, WL.mk.injEq, true_and]
    constructor <;> omega
  have htinc : incTinc p i r = incXm p i r + 195 := by
    have := incWin_timeUV p r dxM dyM thM
    unfold incTinc
    rw [hgm, this, hfin, hwin]
    ring
  -- the continue arrives after the increment
  have hdC := copyBeta_spec (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (incCc p i)
  have hAi := A_even p i
  have hAi1 := A_even p ((i + 1 : ℕ) : ℤ)
  have hC1 := unitC0_cases p (i + 1)
  have hd : (destU p (i + 1) (incTc p i) - incCc p i) % 2 = 0 := by
    simp only [destU, incTc, incCc, incD] at hdC ⊢
    omega
  have hv : (destU p (i + 1) (incTc p i) + destV p (incTc p i)) % 2 = 1 := by
    have := inCol_side_odd (incTc p i)
    simp only [destU, destV, C0dec, C0inc, C0halt] at this ⊢
    rcases hC1 with h | h | h <;> rw [h] <;> omega
  have hGe2 : incG p i r % 2 = 0 := by unfold incG; omega
  have htau : (route (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r))).2.tau +
      4 * hairCont p (incG p i r) (incEc p i r) (incCc p i) =
      (route (unitWL p i incDWL) (incMkc p i 0 (incEc0 p i))).2.tau +
        4 * hairCont p 0 (incEc0 p i) (incCc p i) := upCorners_tau p (instrBand i) 0 (incCc p i)
    (hairCont p (incG p i r) (incEc p i r) (incCc p i)) (hairCont p 0 (incEc0 p i) (incCc p i))
    (i + 1) (incTc p i) (g := unitWL p i incDWL) rfl rfl (hairCont_par _ _ _ _)
    (hairCont_par _ _ _ _) hd
  have ht3 : (route (unitWL p i incDWL) (incMkc p i 0 (incEc0 p i))).2.tau =
      incT0 p i - 2 * destU p (i + 1) (incTc p i) + 2 * trackBack p (instrBand i) 0 (incCc p i) -
        4 * destV p (incTc p i) - 10 :=
    upCorners_tau_t3 p (instrBand i) 0 (incCc p i) _ (i + 1) (incTc p i) _
      (hairCont_par _ _ _ _) hd hv
  have hH := hairCont_G p (incG p i r) (incEc p i r) (incCc p i) hGe2
  have hH' := hairCont_G p 0 (incEc0 p i) (incCc p i) (by norm_num)
  have hec0 : 0 ≤ incEc0 p i ∧ incEc0 p i ≤ 14 := solveE_bounds _ _ _
  have hG4 : incTinc p i r + 8500 - incT0 p i ≤ 4 * incG p i r := by
    have := le_max_right 0 (incTinc p i r + 8500 - incT0 p i)
    have := le_max_left 0 (incTinc p i r + 8500 - incT0 p i)
    unfold incG ceil120
    omega
  have hxcE : incXc p i r = (route (unitWL p i incDWL) (incMkc p i (incG p i r)
      (incEc p i r))).2.tau -
        (1 + 140 * incTc p i + 16 * incTc p i % 30 - 4 * unitDX p (i + 1)) := by
    simp only [incXc, destWin, unitWL, sideWL, WL.shift]
    ring
  have hlate : 194 + 30 * (incXm p i r / 30) + 946 + 7050 ≤
      180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30 + (134 + incTc p i * 254) + 166 := by
    simp only [destU, destV, inCol, sideV, trackBack, track, unitDX, VU, instrBand] at ht3 hxcE
    omega
  -- membership of the active pieces
  have hinstr : instrSpecs p i = incSpecs p i r := by simp [instrSpecs, hins]
  have hiN : i < p.length := by omega
  have hmU := mergeUsed_of_inc hins
  refine
    { linesC := lC
      timedC := tC
      finC := fC
      δcR := oC
      T0cE := ?_
      endC := ?_
      linesR := lR
      timedR := tR
      finR := fR
      δlR := oL
      T0lE := ?_
      endR := ?_
      linesM := lM
      timedM := tM
      finM := fM
      δmR := oM
      TgE := hTgN
      endM := ?_
      late := ?_
      memC := ?_
      memI := ?_
      memB := ?_ }
  · change _ = _ + _ + 16 * (((incTc p i).toNat : ℕ) : ℤ) % 30
    rw [htcN]
    exact hT0c
  · have h : (routeEndX (unitWL p i incDWL) (incMkc p i (incG p i r) (incEc p i r)) 2010 : ℤ) + 16
        ≤ (((180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30).toNat : ℕ) : ℤ) := by
      rw [hT0c]
      omega
    exact_mod_cast h
  · change _ = _ + _ + 16 * (((incTl p i r).toNat : ℕ) : ℤ) % 30
    rw [htlN]
    exact hT0l
  · have h : (routeEndX (unitWL p i incRWL) (incMkl p i r (incEl p i r)) 2010 : ℤ) + 16 ≤
        ((incT0l p i r : ℕ) : ℤ) := by
      rw [hT0l]
      omega
    exact_mod_cast h
  · have h : ((routeEndX ((unitWL p (p.length + r) haltDWL).shift 0 0
        ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r)) (incT1 p i r) + 16 : ℕ)
          : ℤ) ≤ (((194 + 30 * (incXm p i r / 30)).toNat : ℕ) : ℤ) := by
      rw [hTgN, Nat.cast_add]
      simp only [incPortV, uL] at hend hpar hch
      omega
    exact Int.ofNat_le.mp h
  · have h : (((194 + 30 * (incXm p i r / 30)).toNat : ℕ) : ℤ) + 946 + 7050 ≤
        (((180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30).toNat : ℕ) : ℤ) +
          (134 + (((incTc p i).toNat : ℕ) : ℤ) * 254) + 166 := by
      rw [hTgN, hT0c, htcN]
      exact hlate
    change (194 + 30 * (incXm p i r / 30)).toNat + 946 + 7050 ≤
      (180 + 30 * (incXc p i r / 30) + 16 * incTc p i % 30).toNat +
        (134 + (incTc p i).toNat * 254) + 166
    exact_mod_cast h
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      refine instrRoutes_mem hiN ?_
      rw [hinstr, incSpecs_eq]
      exact List.mem_flatMap.2 ⟨_, List.mem_cons_self, hs⟩
    · refine chainPieces_mem (a := i + 1) (by omega) (by simp [unitUsed, hi1]) ?_ x h
      change (((incTc p i).toNat : ℕ) : ℤ) < _
      rw [htcN]
      exact tc1
  · intro x hx
    simp only [IncPlan.LIraw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (((h | h) | h) | h | h) | h
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      refine instrRoutes_mem hiN ?_
      rw [hinstr, incSpecs_eq]
      exact List.mem_flatMap.2 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hs⟩
    · refine chainPieces_mem (a := p.length + r) (by omega) (by simp [unitUsed, hmU]) ?_ x h
      change (((incTl p i r).toNat : ℕ) : ℤ) < _
      rw [htlN]
      exact tl1
    · change x ∈ List.map PSpec.piece (route ((unitWL p (p.length + r) haltDWL).shift 0 0
        ((incT1 p i r : ℤ) + 166 - 1080)) (mergeCorners p r (mergeE p r))).1 at h
      rw [hrd] at h
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      refine mergeRoutes_mem hr hmU ?_
      simp only [routeSpecs, mergeSpecs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact hs
    · subst h
      exact moduleSpecs_mem hr (s := incGateSpec p r) (mem_moduleSpecs_head
        (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    · subst h
      exact moduleSpecs_mem hr (mem_moduleSpecs_head (List.mem_append_right _ List.mem_cons_self))
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      exact moduleSpecs_mem hr (mem_moduleSpecs_head (List.mem_append_left _ hs))
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    have hk : unitKind p i = .inc := by simp [unitKind, hins]
    refine unitSpecs_mem (a := i) (by omega) (by simp [unitUsed, hiN]) ?_
    simp only [unitSpecs, hk]
    exact List.mem_append_right _ hs

/-! ### The `inc` step -/

/-- **The `inc` step**: for a well-formed program and a state with the instruction `inc r` at the
program counter (register `r` ready), the machine evolves `encM s` into `encM s'` for the next
state `s'` of the counter machine, inside the region of the machine — given the separation and
region facts of the activation plan read off the layout (`incPlan`); it takes `τ > 0`
generations, and every other register is `τ` generations later. -/
theorem inc_step {p : Program} {r : ℕ} (hp : p.WellFormed) (s : MState) (hinv : InvM p s)
    (hins : p[s.pc]? = some (.inc r)) (hready : (s.reg r).Ready)
    (hsep : IncSep (incPlan p s.pc r) ((s.reg r).later 930))
    (hreg : IncRegion (incPlan p s.pc r) ((s.reg r).later 930)) :
    ∃ (τ : ℕ) (s' : MState), 0 < τ ∧ (∀ r', r' ≠ r → s'.reg r' = (s.reg r').later τ) ∧
      p.step s.cfg = some s'.cfg ∧ InvM p s' ∧ (s'.reg r).Ready ∧
      conway.evolve τ (encM p s) = encM p s' ∧
      ∀ j ≤ τ, (conway.evolve j (encM p s) : Set Cell) ⊆ machRegion p :=
  inc_step_of_plan hp s hinv hins hready _ (incPlan_valid hp hins) hsep hreg

end LP

end LeanTheory.Life
