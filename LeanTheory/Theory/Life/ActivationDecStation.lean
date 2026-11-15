/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecModule
public import LeanTheory.Theory.Life.Gen.CapExt

/-!
# The stations of a `decJz` activation: passes, capture, unpaired token

Research note `N-22`, layer 3. On each answer line of module `r` the stations `0 … D - 1` of
`stationSpecs` / `stationZSpecs` repeat every `(72, ±72)`, station `i` at phase `12 i`. For the
activation of `decJz r _` at instruction `i` (caller `j`, shift `sh = decShift`), on the clock of
`cp0WL` delayed by `sh`:

* `PSpec_at`, `phase_stNZG`, `phase_stZG`, `stationSpecs_piecesAt`, `stationZSpecs_piecesAt`:
  the first `n` stations of the layout at time `T` are the certificate chain of stations at phase
  `T mod 30`;
* `stNZY`, `stNZ_relayY`, `stNZChainY`: an NZ answer `30` generations before the position of
  `stNZChain` passes a chain of stations (the position from which the capture certificate starts);
* `stationNZ_capture`, `stationZ_capture`: at `sh + 10350 + 288 j` (NZ) / `sh + 12390 + 288 j`
  (Z) the answer on `ansNZWL` / `ansZWL` and the token of caller `j` on `tokNZWL j` / `tokZWL j`
  (where `decKNZ_target` / `decKZ_target` put the tokens) meet at station `j`, at phase `0`; `492`
  / `472` generations later the dispatched answer is on `nzAnsWL j` / `zAnsWL j`, the first world
  line of the answer route of `decSpecs` (`decGN`, `decGZ`); extended to `692` / `672`
  generations, until the answer is clear of its station (`stationNZ_captureE`,
  `stationZ_captureE`);
* `stationNZ_unpaired`, `stationZ_unpaired`: the token of the other line is absorbed by its station
  (`292` / `272` generations);
* `answerNZ_pass`, `answerZ_pass`: the answer passes the stations `0 … j - 1` before station `j`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Placed pieces and stations -/

/-- A placed piece at time `T` is its base piece at phase `ph + T`, translated. -/
theorem PSpec_at (s : PSpec) (T : ℕ) :
    conway.evolve (T % 30) s.piece.rest =
      translate (s.vx, s.vy) (phase s.base.piece.rest (s.ph + T)) := by
  simp only [PSpec.piece, Piece.place]
  rw [Rule.evolve_translate, evolve_phase s.base.piece.rest_reaction.evolve_eq]
  congr 1
  apply phase_congr
  omega

/-- The three pieces of the station NZ at any phase. -/
theorem phase_stNZG (k : ℕ) :
    phase stNZG k = phase stNZP0 k ∪ phase stNZP1 k ∪ phase stNZP2 k := by
  have h := ((phase_reaction stNZP0_rest 0 (k % 30)).par (phase_reaction stNZP1_rest 0 (k % 30))
    fun _ _ => Box.farApart (by norm_num)).par (phase_reaction stNZP2_rest 0 (k % 30))
    (fun _ _ => FarApart.union_left (Box.farApart (by norm_num)) (Box.farApart (by norm_num)))
  have e : ∀ G : Finset Cell, phase G 0 = G := fun G => by
    rw [phase, Nat.zero_mod, Rule.evolve_zero]
  rw [e, e, e, zero_add] at h
  rw [← stNZG] at h
  change conway.evolve (k % 30) stNZG = _
  rw [h.evolve_eq]
  simp only [phase, Nat.mod_mod]

/-- The three pieces of the station Z at any phase. -/
theorem phase_stZG (k : ℕ) : phase stZG k = phase stZP0 k ∪ phase stZP1 k ∪ phase stZP2 k := by
  have h := ((phase_reaction stZP0_rest 0 (k % 30)).par (phase_reaction stZP1_rest 0 (k % 30))
    fun _ _ => Box.farApart (by norm_num)).par (phase_reaction stZP2_rest 0 (k % 30))
    (fun _ _ => FarApart.union_left (Box.farApart (by norm_num)) (Box.farApart (by norm_num)))
  have e : ∀ G : Finset Cell, phase G 0 = G := fun G => by
    rw [phase, Nat.zero_mod, Rule.evolve_zero]
  rw [e, e, e, zero_add] at h
  rw [← stZG] at h
  change conway.evolve (k % 30) stZG = _
  rw [h.evolve_eq]
  simp only [phase, Nat.mod_mod]

/-- Membership in the pieces of a `flatMap` list. -/
theorem mem_piecesAt_flatMap {f : ℕ → List PSpec} {n T : ℕ} {c : Cell} :
    c ∈ piecesAt (((List.range n).flatMap f).map PSpec.piece) T ↔
      ∃ j < n, c ∈ piecesAt ((f j).map PSpec.piece) T := by
  simp only [mem_piecesAt, List.mem_map, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨_, ⟨s, ⟨j, hj, hs⟩, rfl⟩, hc⟩
    exact ⟨j, hj, _, ⟨s, hs, rfl⟩, hc⟩
  · rintro ⟨j, hj, _, ⟨s, hs, rfl⟩, hc⟩
    exact ⟨_, ⟨s, ⟨j, hj, hs⟩, rfl⟩, hc⟩

/-- Station `j` of the line NZ at time `T`: the station at phase `12 j + T`, translated. -/
theorem stNZ_one_at (dx dy : ℤ) (j T : ℕ) :
    piecesAt ((groupSpecs [.stNZ 0, .stNZ 1, .stNZ 2] (dx + 72 * (j : ℤ)) (dy + 72 * (j : ℤ)) |>.map
      (fun s => { s with ph := 12 * j % 30 })).map PSpec.piece) T =
      translate (dx + 72 * (j : ℤ), dy + 72 * (j : ℤ)) (phase stNZG (12 * j % 30 + T)) := by
  rw [phase_stNZG]
  simp only [groupSpecs, List.map_cons, List.map_nil, piecesAt, List.foldr_cons, List.foldr_nil,
    union_empty, PSpec_at, translate_union, union_assoc]
  rfl

/-- Station `j` of the line Z at time `T`: the station at phase `12 j + T`, translated. -/
theorem stZ_one_at (dx dy : ℤ) (j T : ℕ) :
    piecesAt ((groupSpecs [.stZ 0, .stZ 1, .stZ 2] (dx + 72 * (j : ℤ)) (dy - 72 * (j : ℤ)) |>.map
      (fun s => { s with ph := 12 * j % 30 })).map PSpec.piece) T =
      translate (dx + 72 * (j : ℤ), dy - 72 * (j : ℤ)) (phase stZG (12 * j % 30 + T)) := by
  rw [phase_stZG]
  simp only [groupSpecs, List.map_cons, List.map_nil, piecesAt, List.foldr_cons, List.foldr_nil,
    union_empty, PSpec_at, translate_union, union_assoc]
  rfl

/-- **The first `n` stations NZ of the layout at time `T`** are the certificate chain of stations
at phase `m` whenever `T ≡ m (mod 30)`. -/
theorem stationSpecs_piecesAt (n : ℕ) (dx dy : ℤ) (T m : ℕ) (hm : T % 30 = m % 30) :
    piecesAt ((stationSpecs n dx dy).map PSpec.piece) T =
      translate (dx, dy) (relayChain stNZG 288 (72, 72) n m) := by
  ext c
  rw [stationSpecs, mem_piecesAt_flatMap, mem_translate]
  simp only [relayChain, mem_biUnion, Finset.mem_range, mem_translate]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  rw [stNZ_one_at, mem_translate, phase_congr stNZG (b := 29 * 288 * j + m) (by omega)]
  have key : c - ((dx + 72 * (j : ℤ), dy + 72 * (j : ℤ)) : Cell) =
      c - (dx, dy) - ((j : ℤ) * (72, 72).1, (j : ℤ) * (72, 72).2) := by
    ext <;> simp <;> ring
  rw [key]

/-- **The first `n` stations Z of the layout at time `T`** are the certificate chain of stations at
phase `m` whenever `T ≡ m (mod 30)`. -/
theorem stationZSpecs_piecesAt (n : ℕ) (dx dy : ℤ) (T m : ℕ) (hm : T % 30 = m % 30) :
    piecesAt ((stationZSpecs n dx dy).map PSpec.piece) T =
      translate (dx, dy) (relayChain stZG 288 (72, -72) n m) := by
  ext c
  rw [stationZSpecs, mem_piecesAt_flatMap, mem_translate]
  simp only [relayChain, mem_biUnion, Finset.mem_range, mem_translate]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  rw [stZ_one_at, mem_translate, phase_congr stZG (b := 29 * 288 * j + m) (by omega)]
  have key : c - ((dx + 72 * (j : ℤ), dy - 72 * (j : ℤ)) : Cell) =
      c - (dx, dy) - ((j : ℤ) * (72, -72).1, (j : ℤ) * (72, -72).2) := by
    ext <;> simp <;> ring
  rw [key]

/-! ### The answer passes the stations NZ before station `j` -/

/-- The NZ answer at the position from which the capture certificate starts (`30` generations
before `stNZX`). -/
def stNZY : Finset Cell := ofRows 393 784 [1, 6, 3]

/-- The answer glider moves by `(1, 1)` every four generations. -/
theorem stNZY_four : conway.evolve 4 stNZY = translate (1, 1) stNZY := by
  rw [stNZY, translate_ofRows]
  life_cert

/-- The answer glider during four generations. -/
theorem stNZY_box : ∀ r < 4, (conway.evolve r stNZY : Set Cell) ⊆ Box 393 395 784 787 := by
  intro r hr
  interval_cases r <;> (rw [stNZY]; life_eval; exact coe_ofRows_subset_box rfl)

/-- The region of the station NZ while the answer passes from `stNZY`. -/
def stNZRY : Set Cell := (Box 380 412 829 919 ∪ Box 431 439 891 913 ∪ Box 464 467 820 823) ∪
  {c : Cell | ∃ m : ℤ, 0 ≤ m ∧ m ≤ 72 ∧ c ∈ Box (393 + m * 1) (395 + m * 1) (784 + m * 1)
    (787 + m * 1)}

set_option maxRecDepth 100000 in
/-- **An answer from `stNZY` passes the station NZ** in 288 generations. -/
theorem stNZ_relayY :
    Reaction (stNZG ∪ stNZY) (phase stNZG 288 ∪ translate (72, 72) stNZY) 288
      (fun _ => stNZRY) := by
  have hf := flight_reaction stNZY_four stNZY_box 72 0 (G' := translate (72, 72) stNZY) (by
    rw [Rule.evolve_zero]; norm_num)
  have hg := phase_reaction stNZG_rest 0 288
  rw [phase, Nat.zero_mod, Rule.evolve_zero, zero_add] at hg
  have h := hg.par hf fun i hi => by
    refine FarApart.union_left (FarApart.union_left ?_ ?_) ?_ <;>
      exact Box.farApart (by omega)
  refine h.mono fun i hi c hc => ?_
  rcases hc with hc | hc
  · exact Or.inl hc
  · right
    exact ⟨((i / 4 : ℕ) : ℤ), by positivity, by omega, hc⟩

set_option maxRecDepth 100000 in
/-- **A chain of stations NZ passed from `stNZY`**, any length. -/
theorem stNZChainY (L : ℕ) :
    Reaction (relayChain stNZG 288 (72, 72) (L + 1) 0 ∪ stNZY)
      (relayChain stNZG 288 (72, 72) (L + 1) ((L + 1) * 288) ∪
        translate (((L + 1 : ℕ) : ℤ) * (72, 72).1, ((L + 1 : ℕ) : ℤ) * (72, 72).2) stNZY)
      ((L + 1) * 288) (fun _ => chainFoot stNZRY (72, 72) (L + 1)) := by
  refine chain_reaction_set stNZG_rest stNZ_relayY (fun c hc => Or.inl hc) ?_ ?_ ?_ L
  · intro j hj x hx y hy hn
    simp only [Set.mem_union] at hx hy
    obtain ⟨n1, n2, n3, n4⟩ := hn
    rcases hx with ((⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩) | ⟨a1, a2, a3, a4⟩) <;>
      rcases hy with ((⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩) | ⟨b1, b2, b3, b4⟩) <;>
      (push_cast at *; omega)
  · intro j hj x hx y hy hn
    simp only [stNZRY, Set.mem_union] at hx hy
    obtain ⟨n1, n2, n3, n4⟩ := hn
    rcases hx with (((⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩) | ⟨a1, a2, a3, a4⟩) |
      ⟨m, ml, mu, a1, a2, a3, a4⟩) <;>
      rcases hy with ((⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩) | ⟨b1, b2, b3, b4⟩) <;>
      (push_cast at *; omega)
  · intro j hj x hx y hy hn
    simp only [stNZRY, Set.mem_union] at hx hy
    obtain ⟨n1, n2, n3, n4⟩ := hn
    rcases hx with ((⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩) | ⟨a1, a2, a3, a4⟩) <;>
      rcases hy with (((⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩) | ⟨b1, b2, b3, b4⟩) |
        ⟨m2, m2l, m2u, b1, b2, b3, b4⟩) <;>
      (push_cast at *; omega)

/-! ### World lines at station `j` -/

/-- The answer line NZ is invariant under the station step `(72, 72)`, `288` generations. -/
theorem ansNZWL_step (j : ℤ) : ansNZWL.shift (72 * j) (72 * j) (288 * j) = ansNZWL := by
  simp only [ansNZWL, WL.shift, WL.mk.injEq, true_and]; constructor <;> ring

/-- The answer line Z is invariant under the station step `(72, -72)`, `288` generations. -/
theorem ansZWL_step (j : ℤ) : ansZWL.shift (72 * j) (-72 * j) (288 * j) = ansZWL := by
  simp only [ansZWL, WL.shift, WL.mk.injEq, true_and]; constructor <;> ring

/-- The NZ token line of station `j` is the one of station `0` moved by `j` station steps. -/
theorem tokNZWL_step (j : ℤ) : tokNZWL j = (tokNZWL 0).shift (72 * j) (72 * j) (288 * j) := by
  simp only [tokNZWL, WL.shift, WL.mk.injEq, true_and]; constructor <;> ring

/-- The Z token line of station `j` is the one of station `0` moved by `j` station steps. -/
theorem tokZWL_step (j : ℤ) : tokZWL j = (tokZWL 0).shift (72 * j) (-72 * j) (288 * j) := by
  simp only [tokZWL, WL.shift, WL.mk.injEq, true_and]; constructor <;> ring

/-- The dispatched NZ answer of station `j` is the one of station `0` moved by `j` steps. -/
theorem nzAnsWL_step (j : ℤ) : nzAnsWL j = (nzAnsWL 0).shift (72 * j) (72 * j) (288 * j) := by
  simp only [nzAnsWL, WL.shift, WL.mk.injEq, true_and]; constructor <;> ring

/-- The dispatched Z answer of station `j` is the one of station `0` moved by `j` steps. -/
theorem zAnsWL_step (j : ℤ) : zAnsWL j = (zAnsWL 0).shift (72 * j) (-72 * j) (288 * j) := by
  simp only [zAnsWL, WL.shift, WL.mk.injEq, true_and]; constructor <;> ring

/-- A world line moved by `j` station steps carries the glider moved alike. -/
theorem cells_step {w : WL} (hw : w.Dir) (a b j t : ℤ) :
    (w.shift a b (288 * j)).cells (t + 288 * j) = translate (a, b) (w.cells t) := by
  rw [WL.shift_cells hw]
  congr 2
  ring

/-- The input of the capture certificate NZ: the answer and the token of station `0`. -/
theorem stCaptureNZIn_eq : stCaptureNZIn = ansNZWL.cells 10350 ∪ (tokNZWL 0).cells 10350 := by
  rw [show ansNZWL.cells 10350 = ofRows 393 784 [1, 6, 3] from rfl,
    show (tokNZWL 0).cells 10350 = ofRows 386 870 [7, 4, 2] from rfl, stCaptureNZIn,
    ofRows_eq_padRows' 386 784 393 784 0 7 _ (by norm_num) (by norm_num),
    ofRows_eq_padRows' 386 784 386 870 86 0 _ (by norm_num) (by norm_num), ← ofRows_orRows]
  rfl

/-- The output of the capture certificate NZ is the dispatched answer of station `0`. -/
theorem stCaptureNZOut_eq : stCaptureNZOut = (nzAnsWL 0).cells 10842 := rfl

/-- The input of the capture certificate Z: the answer and the token of station `0`. -/
theorem stCaptureZIn_eq : stCaptureZIn = ansZWL.cells 12390 ∪ (tokZWL 0).cells 12390 := by
  rw [show ansZWL.cells 12390 = ofRows 849 (-313) [2, 6, 5] from rfl,
    show (tokZWL 0).cells 12390 = ofRows 924 (-306) [6, 3, 4] from rfl, stCaptureZIn,
    ofRows_eq_padRows' 849 (-313) 924 (-306) 7 75 _ (by norm_num) (by norm_num),
    ← ofRows_orRows]
  congr 1

/-- The output of the capture certificate Z is the dispatched answer of station `0`. -/
theorem stCaptureZOut_eq : stCaptureZOut = (zAnsWL 0).cells 12862 := rfl

/-- The input of the unpaired-token certificate NZ is the token of station `0`. -/
theorem stUnpairedTokenNZIn_eq : stUnpairedTokenNZIn = (tokNZWL 0).cells 10350 := rfl

/-- The input of the unpaired-token certificate Z is the token of station `0`. -/
theorem stUnpairedTokenZIn_eq : stUnpairedTokenZIn = (tokZWL 0).cells 12390 := rfl

/-- The NZ answer at station `0` (capture position) is `stNZY`. -/
theorem stNZY_eq : stNZY = ansNZWL.cells 10350 := rfl

/-- The Z answer at station `0` is `stZX`. -/
theorem stZX_eq : stZX = ansZWL.cells 12390 := rfl

/-! ### Station `j` of module `r` -/

/-- The pieces of station `j` of the line NZ of module `r`. -/
def stNZOne (p : Program) (r j : ℕ) : List Piece :=
  ((groupSpecs [.stNZ 0, .stNZ 1, .stNZ 2] (modDX p r + 72 * (j : ℤ)) (modDY p r + 72 * (j : ℤ))
    |>.map (fun s => { s with ph := 12 * j % 30 })).map PSpec.piece)

/-- The pieces of station `j` of the line Z of module `r`. -/
def stZOne (p : Program) (r j : ℕ) : List Piece :=
  ((groupSpecs [.stZ 0, .stZ 1, .stZ 2] (modDX p r + 72 * (j : ℤ)) (modDY p r - 72 * (j : ℤ))
    |>.map (fun s => { s with ph := 12 * j % 30 })).map PSpec.piece)

/-- The pieces of station `j < D` are pieces of the module. -/
theorem stNZOne_mem (p : Program) (r : ℕ) {j : ℕ} (hj : j < numCallers p) {g : Piece}
    (hg : g ∈ stNZOne p r j) : g ∈ (moduleSpecs p r).map PSpec.piece := by
  simp only [stNZOne, List.mem_map] at hg ⊢
  obtain ⟨s, hs, rfl⟩ := hg
  refine ⟨s, ?_, rfl⟩
  simp only [moduleSpecs, List.mem_append]
  refine Or.inl (Or.inl (Or.inr ?_))
  simp only [stationSpecs, List.mem_flatMap, List.mem_range]
  exact ⟨j, hj, List.mem_map.2 hs⟩

/-- The pieces of station `j < D` of the line Z are pieces of the module. -/
theorem stZOne_mem (p : Program) (r : ℕ) {j : ℕ} (hj : j < numCallers p) {g : Piece}
    (hg : g ∈ stZOne p r j) : g ∈ (moduleSpecs p r).map PSpec.piece := by
  simp only [stZOne, List.mem_map] at hg ⊢
  obtain ⟨s, hs, rfl⟩ := hg
  refine ⟨s, ?_, rfl⟩
  simp only [moduleSpecs, List.mem_append]
  refine Or.inl (Or.inr ?_)
  simp only [stationZSpecs, List.mem_flatMap, List.mem_range]
  exact ⟨j, hj, List.mem_map.2 hs⟩

/-- **Capture at station `j` of the line NZ**: at `T = sh + 10350 + 288 j` (`sh ≡ 0 mod 30`) the
station `j` (at phase `0`), the NZ answer and the NZ token of caller `j` become, `492` generations
later, the station and the dispatched answer on `nzAnsWL j` delayed by `sh`. -/
theorem stationNZ_capture (p : Program) (r j : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 10350 + 288 * j) :
    Reaction (piecesAt (stNZOne p r j) T ∪ (((modWL p r ansNZWL).shift 0 0 sh).cells T ∪
        ((modWL p r (tokNZWL j)).shift 0 0 sh).cells T))
      (piecesAt (stNZOne p r j) (T + 492) ∪
        ((modWL p r (nzAnsWL j)).shift 0 0 sh).cells (T + 492)) 492
      (fun _ => (fun c => (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ)) + c) ''
        Box 380 467 784 919) := by
  have hA : ansNZWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have hK : (tokNZWL 0).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have hN : (nzAnsWL 0).Dir := ⟨Or.inr rfl, Or.inl rfl⟩
  have e1 : ((T : ℕ) : ℤ) = 10350 + 288 * (j : ℤ) + sh := by omega
  rw [stNZOne, stNZ_one_at, stNZ_one_at, e1,
    show (10350 + 288 * (j : ℤ) + sh + 492) = 10842 + 288 * (j : ℤ) + sh by ring]
  rw [modShift_cells p r ⟨Or.inl rfl, Or.inl rfl⟩, modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩,
    modShift_cells p r ⟨Or.inr rfl, Or.inl rfl⟩, tokNZWL_step, nzAnsWL_step,
    ← ansNZWL_step (j : ℤ), cells_step hA,
    cells_step hK, cells_step hN, translate_translate, translate_translate, translate_translate,
    ← translate_union, ← stCaptureNZIn_eq, ← stCaptureNZOut_eq,
    show ((modDX p r, modDY p r) + (72 * (j : ℤ), 72 * (j : ℤ)) : Cell) =
      (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ)) from rfl,
    ← translate_union, ← translate_union,
    phase_congr stNZG (a := 12 * j % 30 + T) (b := 0) (by omega),
    phase_congr stNZG (a := 12 * j % 30 + (T + 492)) (b := 492) (by omega)]
  have h := stCaptureNZ_relay
  rw [stCaptureNZG_eq] at h
  have h' := h.translate (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ))
  rw [show phase stNZG 0 = stNZG by rw [phase, Nat.zero_mod, Rule.evolve_zero]]
  convert h' using 3

/-- **Capture at station `j` of the line Z**: at `T = sh + 12390 + 288 j` (`sh ≡ 0 mod 30`) the
station `j` (at phase `0`), the Z answer and the Z token of caller `j` become, `472` generations
later, the station and the dispatched answer on `zAnsWL j` delayed by `sh`. -/
theorem stationZ_capture (p : Program) (r j : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 12390 + 288 * j) :
    Reaction (piecesAt (stZOne p r j) T ∪ (((modWL p r ansZWL).shift 0 0 sh).cells T ∪
        ((modWL p r (tokZWL j)).shift 0 0 sh).cells T))
      (piecesAt (stZOne p r j) (T + 472) ∪
        ((modWL p r (zAnsWL j)).shift 0 0 sh).cells (T + 472)) 472
      (fun _ => (fun c => (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ)) + c) ''
        Box 849 979 (-380) (-293)) := by
  have hA : ansZWL.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have hK : (tokZWL 0).Dir := ⟨Or.inr rfl, Or.inr rfl⟩
  have hN : (zAnsWL 0).Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have e1 : ((T : ℕ) : ℤ) = 12390 + 288 * (j : ℤ) + sh := by omega
  rw [stZOne, stZ_one_at, stZ_one_at, e1,
    show (12390 + 288 * (j : ℤ) + sh + 472) = 12862 + 288 * (j : ℤ) + sh by ring]
  rw [modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩, modShift_cells p r ⟨Or.inr rfl, Or.inr rfl⟩,
    modShift_cells p r ⟨Or.inl rfl, Or.inl rfl⟩, tokZWL_step, zAnsWL_step,
    ← ansZWL_step (j : ℤ), cells_step hA, cells_step hK, cells_step hN, translate_translate,
    translate_translate, translate_translate,
    ← translate_union, ← stCaptureZIn_eq, ← stCaptureZOut_eq,
    show ((modDX p r, modDY p r) + (72 * (j : ℤ), -72 * (j : ℤ)) : Cell) =
      (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ)) from Prod.ext rfl (by simp; ring),
    ← translate_union, ← translate_union,
    phase_congr stZG (a := 12 * j % 30 + T) (b := 0) (by omega),
    phase_congr stZG (a := 12 * j % 30 + (T + 472)) (b := 472) (by omega)]
  have h := stCaptureZ_relay
  rw [stCaptureZG_eq] at h
  have h' := h.translate (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ))
  rw [show phase stZG 0 = stZG by rw [phase, Nat.zero_mod, Rule.evolve_zero]]
  convert h' using 3

/-- The extended output of the NZ capture is the dispatched answer `200` generations later. -/
theorem stCaptureNZOutE_eq : stCaptureNZOutE = (nzAnsWL 0).cells 11042 := rfl

/-- The extended output of the Z capture is the dispatched answer `200` generations later. -/
theorem stCaptureZOutE_eq : stCaptureZOutE = (zAnsWL 0).cells 13062 := rfl

set_option maxRecDepth 100000 in
/-- **The NZ capture, extended**: `692` generations, until the dispatched answer is clear of its
station. -/
theorem stCaptureNZ_relayE :
    Reaction (stCaptureNZG ∪ stCaptureNZIn) (phase stCaptureNZG 692 ∪ stCaptureNZOutE) 692
      (fun _ => Box 376 467 784 951) :=
  (stCaptureNZ_relay.seq stCaptureNZ_ext).mono fun i _ => by
    split_ifs
    · exact box_subset_box (by norm_num) le_rfl le_rfl (by norm_num)
    · exact box_subset_box le_rfl le_rfl (by norm_num) le_rfl

set_option maxRecDepth 100000 in
/-- **The Z capture, extended**: `672` generations, until the dispatched answer is clear of its
station. -/
theorem stCaptureZ_relayE :
    Reaction (stCaptureZG ∪ stCaptureZIn) (phase stCaptureZG 672 ∪ stCaptureZOutE) 672
      (fun _ => Box 849 1011 (-380) (-289)) :=
  (stCaptureZ_relay.seq stCaptureZ_ext).mono fun i _ => by
    split_ifs
    · exact box_subset_box le_rfl (by norm_num) le_rfl (by norm_num)
    · exact box_subset_box (by norm_num) le_rfl le_rfl le_rfl

/-- **Capture at station `j` of the line NZ, extended**: as `stationNZ_capture`, run `692`
generations, until the dispatched answer on `nzAnsWL j` is clear of the station. -/
theorem stationNZ_captureE (p : Program) (r j : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 10350 + 288 * j) :
    Reaction (piecesAt (stNZOne p r j) T ∪ (((modWL p r ansNZWL).shift 0 0 sh).cells T ∪
        ((modWL p r (tokNZWL j)).shift 0 0 sh).cells T))
      (piecesAt (stNZOne p r j) (T + 692) ∪
        ((modWL p r (nzAnsWL j)).shift 0 0 sh).cells (T + 692)) 692
      (fun _ => (fun c => (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ)) + c) ''
        Box 376 467 784 951) := by
  have hA : ansNZWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have hK : (tokNZWL 0).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have hN : (nzAnsWL 0).Dir := ⟨Or.inr rfl, Or.inl rfl⟩
  have e1 : ((T : ℕ) : ℤ) = 10350 + 288 * (j : ℤ) + sh := by omega
  rw [stNZOne, stNZ_one_at, stNZ_one_at, e1,
    show (10350 + 288 * (j : ℤ) + sh + 692) = 11042 + 288 * (j : ℤ) + sh by ring]
  rw [modShift_cells p r ⟨Or.inl rfl, Or.inl rfl⟩, modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩,
    modShift_cells p r ⟨Or.inr rfl, Or.inl rfl⟩, tokNZWL_step, nzAnsWL_step,
    ← ansNZWL_step (j : ℤ), cells_step hA,
    cells_step hK, cells_step hN, translate_translate, translate_translate, translate_translate,
    ← translate_union, ← stCaptureNZIn_eq, ← stCaptureNZOutE_eq,
    show ((modDX p r, modDY p r) + (72 * (j : ℤ), 72 * (j : ℤ)) : Cell) =
      (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ)) from rfl,
    ← translate_union, ← translate_union,
    phase_congr stNZG (a := 12 * j % 30 + T) (b := 0) (by omega),
    phase_congr stNZG (a := 12 * j % 30 + (T + 692)) (b := 692) (by omega)]
  have h := stCaptureNZ_relayE
  rw [stCaptureNZG_eq] at h
  have h' := h.translate (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ))
  rw [show phase stNZG 0 = stNZG by rw [phase, Nat.zero_mod, Rule.evolve_zero]]
  convert h' using 3

/-- **Capture at station `j` of the line Z, extended**: as `stationZ_capture`, run `672`
generations, until the dispatched answer on `zAnsWL j` is clear of the station. -/
theorem stationZ_captureE (p : Program) (r j : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 12390 + 288 * j) :
    Reaction (piecesAt (stZOne p r j) T ∪ (((modWL p r ansZWL).shift 0 0 sh).cells T ∪
        ((modWL p r (tokZWL j)).shift 0 0 sh).cells T))
      (piecesAt (stZOne p r j) (T + 672) ∪
        ((modWL p r (zAnsWL j)).shift 0 0 sh).cells (T + 672)) 672
      (fun _ => (fun c => (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ)) + c) ''
        Box 849 1011 (-380) (-289)) := by
  have hA : ansZWL.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have hK : (tokZWL 0).Dir := ⟨Or.inr rfl, Or.inr rfl⟩
  have hN : (zAnsWL 0).Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  have e1 : ((T : ℕ) : ℤ) = 12390 + 288 * (j : ℤ) + sh := by omega
  rw [stZOne, stZ_one_at, stZ_one_at, e1,
    show (12390 + 288 * (j : ℤ) + sh + 672) = 13062 + 288 * (j : ℤ) + sh by ring]
  rw [modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩, modShift_cells p r ⟨Or.inr rfl, Or.inr rfl⟩,
    modShift_cells p r ⟨Or.inl rfl, Or.inl rfl⟩, tokZWL_step, zAnsWL_step,
    ← ansZWL_step (j : ℤ), cells_step hA, cells_step hK, cells_step hN, translate_translate,
    translate_translate, translate_translate,
    ← translate_union, ← stCaptureZIn_eq, ← stCaptureZOutE_eq,
    show ((modDX p r, modDY p r) + (72 * (j : ℤ), -72 * (j : ℤ)) : Cell) =
      (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ)) from Prod.ext rfl (by simp; ring),
    ← translate_union, ← translate_union,
    phase_congr stZG (a := 12 * j % 30 + T) (b := 0) (by omega),
    phase_congr stZG (a := 12 * j % 30 + (T + 672)) (b := 672) (by omega)]
  have h := stCaptureZ_relayE
  rw [stCaptureZG_eq] at h
  have h' := h.translate (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ))
  rw [show phase stZG 0 = stZG by rw [phase, Nat.zero_mod, Rule.evolve_zero]]
  convert h' using 3

/-- **The unpaired NZ token is absorbed by station `j`** (after a Z answer): at
`T = sh + 10350 + 288 j`, `292` generations. -/
theorem stationNZ_unpaired (p : Program) (r j : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 10350 + 288 * j) :
    Reaction (piecesAt (stNZOne p r j) T ∪ ((modWL p r (tokNZWL j)).shift 0 0 sh).cells T)
      (piecesAt (stNZOne p r j) (T + 292)) 292
      (fun _ => (fun c => (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ)) + c) ''
        Box 380 467 820 919) := by
  have hK : (tokNZWL 0).Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  have e1 : ((T : ℕ) : ℤ) = 10350 + 288 * (j : ℤ) + sh := by omega
  rw [stNZOne, stNZ_one_at, stNZ_one_at, e1,
    modShift_cells p r ⟨Or.inl rfl, Or.inr rfl⟩, tokNZWL_step, cells_step hK,
    translate_translate, ← stUnpairedTokenNZIn_eq,
    show ((modDX p r, modDY p r) + (72 * (j : ℤ), 72 * (j : ℤ)) : Cell) =
      (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ)) from rfl,
    ← translate_union,
    phase_congr stNZG (a := 12 * j % 30 + T) (b := 0) (by omega),
    phase_congr stNZG (a := 12 * j % 30 + (T + 292)) (b := 292) (by omega)]
  have h := stUnpairedTokenNZ_relay
  rw [stUnpairedTokenNZG_eq, union_empty] at h
  have h' := h.translate (modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ))
  rw [show phase stNZG 0 = stNZG by rw [phase, Nat.zero_mod, Rule.evolve_zero]]
  exact h'

/-- **The unpaired Z token is absorbed by station `j`** (after an NZ answer): at
`T = sh + 12390 + 288 j`, `272` generations. -/
theorem stationZ_unpaired (p : Program) (r j : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 12390 + 288 * j) :
    Reaction (piecesAt (stZOne p r j) T ∪ ((modWL p r (tokZWL j)).shift 0 0 sh).cells T)
      (piecesAt (stZOne p r j) (T + 272)) 272
      (fun _ => (fun c => (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ)) + c) ''
        Box 880 979 (-380) (-293)) := by
  have hK : (tokZWL 0).Dir := ⟨Or.inr rfl, Or.inr rfl⟩
  have e1 : ((T : ℕ) : ℤ) = 12390 + 288 * (j : ℤ) + sh := by omega
  rw [stZOne, stZ_one_at, stZ_one_at, e1,
    modShift_cells p r ⟨Or.inr rfl, Or.inr rfl⟩, tokZWL_step, cells_step hK,
    translate_translate, ← stUnpairedTokenZIn_eq,
    show ((modDX p r, modDY p r) + (72 * (j : ℤ), -72 * (j : ℤ)) : Cell) =
      (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ)) from Prod.ext rfl (by simp; ring),
    ← translate_union,
    phase_congr stZG (a := 12 * j % 30 + T) (b := 0) (by omega),
    phase_congr stZG (a := 12 * j % 30 + (T + 272)) (b := 272) (by omega)]
  have h := stUnpairedTokenZ_relay
  rw [stUnpairedTokenZG_eq, union_empty] at h
  have h' := h.translate (modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ))
  rw [show phase stZG 0 = stZG by rw [phase, Nat.zero_mod, Rule.evolve_zero]]
  exact h'

/-! ### The answer passes the stations before station `j` -/

/-- **The NZ answer passes the stations `0 … L`** of module `r`: from the capture position of
station `0` at `T = sh + 10350` to the capture position of station `L + 1`, in `288 (L + 1)`
generations, on its world line `ansNZWL` delayed by `sh`. -/
theorem answerNZ_pass (p : Program) (r L : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 10350) :
    Reaction (piecesAt ((stationSpecs (L + 1) (modDX p r) (modDY p r)).map PSpec.piece) T ∪
        ((modWL p r ansNZWL).shift 0 0 sh).cells T)
      (piecesAt ((stationSpecs (L + 1) (modDX p r) (modDY p r)).map PSpec.piece)
          (T + (L + 1) * 288) ∪ ((modWL p r ansNZWL).shift 0 0 sh).cells (T + (L + 1) * 288))
      ((L + 1) * 288)
      (fun _ => (fun c => (modDX p r, modDY p r) + c) '' chainFoot stNZRY (72, 72) (L + 1)) := by
  have hA : ansNZWL.Dir := ⟨Or.inl rfl, Or.inl rfl⟩
  rw [stationSpecs_piecesAt (L + 1) _ _ T 0 (by omega),
    stationSpecs_piecesAt (L + 1) _ _ (T + (L + 1) * 288) ((L + 1) * 288) (by omega)]
  have e1 : ((T : ℕ) : ℤ) = 10350 + sh := by omega
  have e2 : (T : ℤ) + ((L : ℤ) + 1) * 288 = 10350 + 288 * ((L + 1 : ℕ) : ℤ) + sh := by
    push_cast; omega
  rw [e2, e1, modShift_cells p r hA, modShift_cells p r hA,
    ← ansNZWL_step ((L + 1 : ℕ) : ℤ), cells_step hA, ansNZWL_step, ← stNZY_eq,
    ← translate_union, ← translate_union]
  have h := (stNZChainY L).translate (modDX p r, modDY p r)
  convert h using 3
  congr 1
  ext <;> simp <;> ring

/-- **The Z answer passes the stations `0 … L`** of module `r`: from station `0` at
`T = sh + 12390` to the capture position of station `L + 1`, in `288 (L + 1)` generations, on its
world line `ansZWL` delayed by `sh`. -/
theorem answerZ_pass (p : Program) (r L : ℕ) (sh : ℤ) (hsh : sh % 30 = 0) (T : ℕ)
    (hT : (T : ℤ) = sh + 12390) :
    Reaction (piecesAt ((stationZSpecs (L + 1) (modDX p r) (modDY p r)).map PSpec.piece) T ∪
        ((modWL p r ansZWL).shift 0 0 sh).cells T)
      (piecesAt ((stationZSpecs (L + 1) (modDX p r) (modDY p r)).map PSpec.piece)
          (T + (L + 1) * 288) ∪ ((modWL p r ansZWL).shift 0 0 sh).cells (T + (L + 1) * 288))
      ((L + 1) * 288)
      (fun _ => (fun c => (modDX p r, modDY p r) + c) '' chainFoot stZR (72, -72) (L + 1)) := by
  have hA : ansZWL.Dir := ⟨Or.inl rfl, Or.inr rfl⟩
  rw [stationZSpecs_piecesAt (L + 1) _ _ T 0 (by omega),
    stationZSpecs_piecesAt (L + 1) _ _ (T + (L + 1) * 288) ((L + 1) * 288) (by omega)]
  have e1 : ((T : ℕ) : ℤ) = 12390 + sh := by omega
  have e2 : (T : ℤ) + ((L : ℤ) + 1) * 288 = 12390 + 288 * ((L + 1 : ℕ) : ℤ) + sh := by
    push_cast; omega
  rw [e2, e1, modShift_cells p r hA, modShift_cells p r hA,
    ← ansZWL_step ((L + 1 : ℕ) : ℤ), cells_step hA, ansZWL_step, ← stZX_eq,
    ← translate_union, ← translate_union]
  have h := (stZChain L).translate (modDX p r, modDY p r)
  convert h using 3
  congr 1
  ext <;> simp <;> ring

end LP

end LeanTheory.Life
