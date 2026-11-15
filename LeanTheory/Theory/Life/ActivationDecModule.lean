/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecAnswers
public import LeanTheory.Theory.Life.ActivationIncEntry
public import LeanTheory.Theory.Life.Gen.ActSideDec

/-!
# The module part of a `decJz` activation: DEC chain, register run input, stations

Research note `N-22`, layer 3. In module `r` the control `C` of `decJz r _` at instruction `i`
(caller `j`, DEC copy `t = 2 j`, `m = 2 D - 1 - t` copies from the downstream end) is relayed by the
DEC chain to the register run; the answer of the run is captured at station `j` by the caller's
token and dispatched. This module proves, for every program:

* **the side input of the DEC chain** (`decWin_eq`, `dec_side_arrival`, `decSideIn`): `C`
  arriving on the window of DEC copy `t` at offset `δ ∈ {4, 8}` is the side input `orSide6`
  (`δ = 4`) or `orSide10` (`δ = 8`, new certificate `Gen/ActSideDec`) of copy `m` at time
  `180 + 30 k + (15 + 16 m) mod 30`, when copy `m` is at phase `0`;
* **the DEC chain** (`decRelay`, `decChainSpecs_piecesAt`, `decChain_reaction`): the copies
  `m, …, 0` of the layout carry it to the output of copy `0` in `134 + 254 m` generations;
* **`C'` to the register run** (`cprime_flight`, `runIn_eq`, `dec_run_time`): the output of copy
  `0` flies in `1771` generations to the input `ofRows (-1186) (-1227) [2, 4, 7]` of the register
  runs placed at module `r`, at the time `sh - 300 ≡ 0 (mod 30)` (`sh = decShift`), so the register
  circuit (at phase `0` at times `≡ 0`) is exactly the circuit at rest of the runs;
* **the module's world lines** (`modShift_cells`, `ansNZWL`, `ansZWL`, `ans_cut_NZ`, `ans_cut_Z`):
  the answer gliders of the split runs (NZ: `ofRows 106 497 [2, 4, 7]` at run time `9503`;
  Z: `ofRows 675 (-139) [6, 5, 4]` at run time `11995`) are the gliders of fixed world lines of the
  module, delayed by `sh`;
* **stations** (`stNZG_eq_capture`, …, `stationNZ_capture`, `stationZ_capture`,
  `stationNZ_unpaired`, `stationZ_unpaired`, `stNZChainY`, `stZChain_answer`): the station
  certificates act on the station pieces `stNZG`, `stZG` of the layout; at station `j` (phase `0`
  at the capture time) the answer and the token of caller `j` (on `tokNZWL j`, `tokZWL j`) become
  the dispatched answer `nzAnsWL j`, `zAnsWL j` of the layout, delayed by `sh`; the answer passes
  the stations `0 … j - 1` before.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### The side input of the DEC chain -/

/-- `σ ∈ {0, 2}`. -/
theorem sigma_cases (q : ℤ) : sigma q = 0 ∨ sigma q = 2 := by
  unfold sigma; omega

/-- The side input of a DEC copy at window offset `δ`: `orSide6` (`δ = 4`) or `orSide10`
(`δ = 8`). -/
def decSideIn (δ : ℤ) : Finset Cell := if δ = 4 then orSide6 else orSide10

/-- The side inputs of the DEC chain are the gliders of the side line at offsets `4` and `8`. -/
theorem decSideIn_cells {δ : ℤ} (hδ : δ = 4 ∨ δ = 8) :
    decSideIn δ = sideBase.cells (180 - δ) := by
  rcases hδ with rfl | rfl <;> rfl

/-- **The window of DEC copy `t` is the side line of the OR gate of copy `m = 2 D - 1 - t`**
(placed at `(-1700 - 35 m, -1727 - 64 m)`, delay `(15 + 16 m) mod 30`). -/
theorem decWin_eq (p : Program) (r : ℕ) (t : ℤ) :
    decWin p r t = (sideBase.shift (-1700 - 35 * (2 * D p - 1 - t)) (-1727 - 64 * (2 * D p - 1 - t))
      ((15 + 16 * (2 * D p - 1 - t)) % 30)).shift (modDX p r) (modDY p r) 0 := by
  simp only [decWin, modWL, sideBase, WL.shift, WL.mk.injEq, true_and]
  constructor <;> ring

/-- **The arriving control is the side input of DEC copy `m`**: on the window of DEC copy `t` at
offset `δ ∈ {4, 8}` (and `k` periods), at time `180 + 30 k + (15 + 16 m) mod 30`. -/
theorem dec_side_arrival (p : Program) (r : ℕ) (t δ k : ℤ) (hδ : δ = 4 ∨ δ = 8) :
    ((decWin p r t).shift 0 0 (δ + 30 * k)).cells
        (180 + 30 * k + (15 + 16 * (2 * D p - 1 - t)) % 30) =
      translate (modDX p r - 1700 - 35 * (2 * D p - 1 - t),
        modDY p r - 1727 - 64 * (2 * D p - 1 - t)) (decSideIn δ) := by
  have hd : sideBase.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  rw [decWin_eq, WL.shift_cells (show WL.Dir ((sideBase.shift (-1700 - 35 * (2 * D p - 1 - t))
      (-1727 - 64 * (2 * D p - 1 - t)) ((15 + 16 * (2 * D p - 1 - t)) % 30)).shift (modDX p r)
      (modDY p r) 0) from hd),
    WL.shift_cells (show WL.Dir (sideBase.shift (-1700 - 35 * (2 * D p - 1 - t))
      (-1727 - 64 * (2 * D p - 1 - t)) ((15 + 16 * (2 * D p - 1 - t)) % 30)) from hd),
    WL.shift_cells hd, decSideIn_cells hδ, translate_translate, translate_translate]
  congr 1
  · ext <;> simp <;> ring
  · congr 1
    ring

/-! ### The DEC chain -/

/-- **The DEC chain from the side input of copy `m` to the output of copy `0`**, in
`134 + 254 m` generations (copy `m` is the first copy of the certificate chain). -/
theorem decRelay (m : ℕ) {S : Finset Cell} (hS : S = orSide6 ∨ S = orSide10) :
    Reaction (relayChain orGate 254 chainV (m + 1) 0 ∪ S)
      (relayChain orGate 254 chainV (m + 1) (134 + m * 254) ∪
        translate (((m + 1 : ℕ) : ℤ) * 35, ((m + 1 : ℕ) : ℤ) * 64) orIn)
      (134 + m * 254) (fun _ => chainFoot (Box 0 90 (-6) 60) chainV (m + 1)) := by
  rcases m with _ | L
  · have h : Reaction (orGate ∪ S) (phase orGate 134 ∪ translate (35, 64) orIn) 134
        (fun _ => Box 0 90 0 60) := by
      rcases hS with rfl | rfl
      · exact orGate_side6
      · exact orGate_side10
    rw [relayChain_one, relayChain_one, phase, Nat.zero_mod, Rule.evolve_zero]
    simp only [zero_mul, add_zero, zero_add, Nat.cast_one, one_mul]
    refine h.mono fun _ _ => (fun c hc => ?_)
    refine box_subset_chainFoot (by omega) ?_
    obtain ⟨h1, h2, h3, h4⟩ := hc
    exact ⟨h1, h2, by omega, h4⟩
  · have h : Reaction (relayChain orGate 254 (35, 64) (L + 2) 0 ∪ S)
        (phase orGate (134 + (L + 1) * 254) ∪ translate (35, 64) (relayChain orGate 254 (35, 64)
          (L + 1) ((L + 1) * 254) ∪ translate (((L + 1 : ℕ) : ℤ) * (35, 64).1,
            ((L + 1 : ℕ) : ℤ) * (35, 64).2) orIn))
        (134 + (L + 1) * 254) (fun _ => chainFoot (Box 0 90 (-6) 60) (35, 64) (L + 2)) := by
      rcases hS with rfl | rfl
      · exact orChainSide6 L
      · exact orChainSide10 L
    rw [show L + 1 + 1 = L + 2 by ring,
      relayChain_succ orGate 254 chainV (L + 1) (134 + (L + 1) * 254),
      show 134 + (L + 1) * 254 + 29 * 254 = (L + 1) * 254 + 30 * 250 by ring,
      relayChain_add_thirty]
    rw [translate_union, translate_translate] at h
    rw [union_assoc, show ((((L + 2 : ℕ) : ℤ) * 35, ((L + 2 : ℕ) : ℤ) * 64) : Cell) =
      (35, 64) + (((L + 1 : ℕ) : ℤ) * (35, 64).1, ((L + 1 : ℕ) : ℤ) * (35, 64).2) by
        ext <;> simp <;> ring]
    exact h

/-- **The copies `0 … m` of a DEC chain at time `T`** are the certificate chain started at copy
`m`, at phase `n`, whenever `T + 15 + 14 m ≡ n (mod 30)`. -/
theorem decChainSpecs_piecesAt (m : ℕ) (dx dy : ℤ) (T n : ℕ)
    (hm : (T + 15 + 14 * m) % 30 = n % 30) :
    piecesAt ((decChainSpecs (m + 1) dx dy).map PSpec.piece) T =
      translate (dx - 1700 - 35 * m, dy - 1727 - 64 * m) (relayChain orGate 254 chainV (m + 1) n)
    := by
  ext c
  rw [mem_piecesAt, mem_translate]
  simp only [decChainSpecs, List.map_map, List.mem_map, List.mem_range, Function.comp,
    relayChain, mem_biUnion, Finset.mem_range, mem_translate]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, hc⟩
    rw [orGate_placed_at, mem_translate] at hc
    refine ⟨m - u, by omega, ?_⟩
    rw [phase_congr orGate (b := (15 + 14 * u) % 30 + T) (by omega)]
    convert hc using 1
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;>
      push_cast [Nat.cast_sub (show u ≤ m by omega)] <;> ring
  · rintro ⟨j, hj, hc⟩
    refine ⟨_, ⟨m - j, by omega, rfl⟩, ?_⟩
    rw [orGate_placed_at, mem_translate]
    rw [phase_congr orGate (b := (15 + 14 * (m - j)) % 30 + T) (by omega)] at hc
    convert hc using 1
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;>
      push_cast [Nat.cast_sub (show j ≤ m by omega)] <;> ring

/-- The first `m + 1` copies of a DEC chain are copies of every longer DEC chain. -/
theorem decChainSpecs_prefix {m n : ℕ} (h : m < n) (dx dy : ℤ) {s : PSpec}
    (hs : s ∈ decChainSpecs (m + 1) dx dy) : s ∈ decChainSpecs n dx dy := by
  simp only [decChainSpecs, List.mem_map, List.mem_range] at hs ⊢
  obtain ⟨u, hu, rfl⟩ := hs
  exact ⟨u, by omega, rfl⟩

/-- **The DEC chain of module `r` relays the control `C`**: the copies `0 … m` of the layout at time
`T0 = 180 + 30 k + (15 + 16 m) mod 30` and the control on the window of DEC copy
`t = 2 D - 1 - m` at offset `δ ∈ {4, 8}` become, `134 + 254 m` generations later, the copies at
their later phases and the output of copy `0`. -/
theorem decChain_reaction (p : Program) (r m : ℕ) (t : ℤ) (hmt : (m : ℤ) = 2 * D p - 1 - t)
    {δ : ℤ} (hδ : δ = 4 ∨ δ = 8) (k : ℤ) (T0 : ℕ)
    (hT0 : (T0 : ℤ) = 180 + 30 * k + (15 + 16 * (m : ℤ)) % 30) :
    Reaction
      (piecesAt ((decChainSpecs (m + 1) (modDX p r) (modDY p r)).map PSpec.piece) T0 ∪
        ((decWin p r t).shift 0 0 (δ + 30 * k)).cells T0)
      (piecesAt ((decChainSpecs (m + 1) (modDX p r) (modDY p r)).map PSpec.piece)
          (T0 + (134 + m * 254)) ∪ translate (modDX p r - 1700 + 35, modDY p r - 1727 + 64) orIn)
      (134 + m * 254)
      (fun _ => (fun c => (modDX p r - 1700 - 35 * m, modDY p r - 1727 - 64 * m) + c) ''
        chainFoot (Box 0 90 (-6) 60) chainV (m + 1)) := by
  rw [decChainSpecs_piecesAt m _ _ T0 0 (by omega),
    decChainSpecs_piecesAt m _ _ (T0 + (134 + m * 254)) (134 + m * 254) (by omega), hT0]
  have hs := dec_side_arrival p r t δ k hδ
  rw [← hmt] at hs
  rw [hs, ← translate_union]
  have hS : decSideIn δ = orSide6 ∨ decSideIn δ = orSide10 := by
    unfold decSideIn; split_ifs <;> simp
  have h := (decRelay m hS).translate (modDX p r - 1700 - 35 * m, modDY p r - 1727 - 64 * m)
  rw [show (modDX p r - 1700 + 35, modDY p r - 1727 + 64) = (modDX p r - 1700 - 35 * (m : ℤ),
      modDY p r - 1727 - 64 * (m : ℤ)) + (((m + 1 : ℕ) : ℤ) * 35, ((m + 1 : ℕ) : ℤ) * 64) by
    ext <;> simp <;> ring, ← translate_translate, ← translate_union]
  exact h

/-! ### `C'` to the register run -/

/-- The input of the register runs (`dz2dOp`, `dz2mk*Run`) is the glider of `cp0WL` at time
`-300`. -/
theorem runIn_eq : ofRows (-1186) (-1227) [2, 4, 7] = cp0WL.cells (-300) := rfl

/-- The output of DEC copy `0` (module frame) is the glider of `cp0WL` at time `-2071`. -/
theorem decOut_eq : translate (-1700 + 35, -1727 + 64) orIn = cp0WL.cells (-2071) := by
  rw [orIn, translate_ofRows]
  rfl

/-- **`C'` flies from the output of DEC copy `0` to the input of the register run**, in `1771`
generations, along `cp0WL` (module `r`). -/
theorem cprime_flight (p : Program) (r : ℕ) :
    Reaction (translate (modDX p r - 1700 + 35, modDY p r - 1727 + 64) orIn)
      (translate (modDX p r, modDY p r) (ofRows (-1186) (-1227) [2, 4, 7])) 1771
      (fun i => (fun c => (modDX p r, modDY p r) + c) '' cp0WL.box (-2071 + i)) := by
  have hd : cp0WL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have h := (WL.flight hd (-2071) 1771).translate (modDX p r, modDY p r)
  rw [show (-2071 : ℤ) + ((1771 : ℕ) : ℤ) = -300 by norm_num, ← runIn_eq, ← decOut_eq,
    translate_translate] at h
  rw [show (modDX p r - 1700 + 35, modDY p r - 1727 + 64) = (modDX p r, modDY p r) +
    (-1700 + 35, -1727 + 64) by ext <;> simp <;> ring]
  exact h

/-- **The register run starts at `sh - 300`**: the control arriving at DEC copy `2 j` in the slot
`k = decSlot` reaches the run input at `T0 + 134 + 254 m + 1771 = decShift - 300`, a multiple of
`30`. -/
theorem dec_run_time (p : Program) (i r : ℕ) :
    180 + 30 * decSlot p i r + (15 + 16 * (2 * D p - 1 - 2 * (callerIdx p r i))) % 30 + 134 +
        254 * (2 * D p - 1 - 2 * (callerIdx p r i)) + 1771 = decShift p i r - 300 ∧
      (decShift p i r - 300) % 30 = 0 := by
  have h := decShift_mod p i r
  rw [decShift_eq] at h ⊢
  constructor <;> omega

/-! ### The module's world lines and the answers of the runs -/

/-- A world line of module `r` delayed by `sh` carries the template's glider translated to the
module, `sh` generations later. -/
theorem modShift_cells (p : Program) (r : ℕ) {w : WL} (hw : w.Dir) (sh t : ℤ) :
    ((modWL p r w).shift 0 0 sh).cells (t + sh) = translate (modDX p r, modDY p r) (w.cells t) := by
  rw [WL.shift_cells (show WL.Dir (modWL p r w) from hw), modWL, WL.shift_cells hw,
    show ((0 : ℤ), (0 : ℤ)) = (0 : Cell) from rfl, translate_zero]
  simp

/-- The NZ answer of the register runs on its world line (module frame, timed for `cp0WL`). -/
def ansNZWL : WL := ⟨1, 1, -391, 8779⟩

/-- The Z answer of the register run `dz2mk0` on its world line (module frame, timed for
`cp0WL`). -/
def ansZWL : WL := ⟨1, -1, -537, 8993⟩

/-- **The NZ answer at the cut** (run time `9503`, i.e. `9203` on the clock of `cp0WL`): the
answer glider `ofRows 106 497 [2, 4, 7]` of `dz2dOpS` … `dz2d3OpS`, `dz2mk1Run_restS` …
`dz2mk7Run_restS`. -/
theorem ans_cut_NZ : ofRows 106 497 [2, 4, 7] = ansNZWL.cells 9203 := rfl

/-- **The Z answer at the cut** (run time `11995`, i.e. `11695` on the clock of `cp0WL`): the
answer glider `dz2mk0A144` of `dz2mk0Run_restS`. -/
theorem ans_cut_Z : ofRows 675 (-139) [6, 5, 4] = ansZWL.cells 11695 := rfl

/-! ### The stations -/

/-- The pieces of the capture certificate NZ are the station NZ of the layout. -/
theorem stCaptureNZG_eq : stCaptureNZG = stNZG := by
  rw [stNZG, stNZP0, stNZP1, stNZP2,
    ofRows_eq_padRows' 380 820 380 829 9 0 _ (by norm_num) (by norm_num),
    ofRows_eq_padRows' 380 820 431 891 71 51 _ (by norm_num) (by norm_num),
    ofRows_eq_padRows' 380 820 464 820 0 84 _ (by norm_num) (by norm_num),
    ← ofRows_orRows, ← ofRows_orRows]
  rfl

/-- The pieces of the unpaired-token certificate NZ are the station NZ of the layout. -/
theorem stUnpairedTokenNZG_eq : stUnpairedTokenNZG = stNZG := by
  rw [stNZG, stNZP0, stNZP1, stNZP2,
    ofRows_eq_padRows' 380 820 380 829 9 0 _ (by norm_num) (by norm_num),
    ofRows_eq_padRows' 380 820 431 891 71 51 _ (by norm_num) (by norm_num),
    ofRows_eq_padRows' 380 820 464 820 0 84 _ (by norm_num) (by norm_num),
    ← ofRows_orRows, ← ofRows_orRows]
  rfl

/-- The pieces of the capture certificate Z are the station Z of the layout. -/
theorem stCaptureZG_eq : stCaptureZG = stZG := by
  rw [stZG, stZP0, stZP1, stZP2,
    ofRows_eq_padRows' 880 (-380) 889 (-323) 57 9 _ (by norm_num) (by norm_num),
    ofRows_eq_padRows' 880 (-380) 951 (-352) 28 71 _ (by norm_num) (by norm_num),
    ofRows_eq_padRows' 880 (-380) 880 (-380) 0 0 _ (by norm_num) (by norm_num),
    ← ofRows_orRows, ← ofRows_orRows]
  rfl

/-- The pieces of the unpaired-token certificate Z are the station Z of the layout. -/
theorem stUnpairedTokenZG_eq : stUnpairedTokenZG = stZG := by
  rw [stZG, stZP0, stZP1, stZP2,
    ofRows_eq_padRows' 880 (-380) 889 (-323) 57 9 _ (by norm_num) (by norm_num),
    ofRows_eq_padRows' 880 (-380) 951 (-352) 28 71 _ (by norm_num) (by norm_num),
    ofRows_eq_padRows' 880 (-380) 880 (-380) 0 0 _ (by norm_num) (by norm_num),
    ← ofRows_orRows, ← ofRows_orRows]
  rfl

end LP

end LeanTheory.Life
