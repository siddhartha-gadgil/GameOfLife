/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecStepProc
public import LeanTheory.Theory.Life.Gen.BodyDecRunG
public import LeanTheory.Theory.Life.Gen.OrGateTight


/-!
# The threads of a `decJz` activation and its separation facts

Research note `N-22`. For the activation of `decJz r z` at instruction `i`:

* membership of the active pieces in the machine (`decLC_mem`, `decLNu_mem`, `decLFN_mem`, …);
* the body of the `dec` unit with the rest of the machine idle (`decBody_window`);
* composition with footprints at absolute times (`Reaction.seqAbs`, `Reaction.seqAbs_eq`);
* **`DecSep`**: the separation facts of the activation, for both answers, each stopping before the
  interaction it hands over to (corner windows, side windows of `20` generations, station windows
  of `90` generations; the prefix regions of the runs before the cut, the extended captures and the
  INC gate with its tight footprint `gateFoot` in the `Z` thread) — the reformulated form;
* **the main threads** (`decThreadN`, register value `≥ 1`; `decThreadZ`, value `0`): from the end
  of the body to the control at the entrance of the next unit, with the register run, the answer,
  the captured token and the answer link; the unpaired token is the second thread
  (`decUnpZProc`, `decUnpNProc`).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Membership of the active pieces in the machine -/

/-- A placed piece of the machine's specification is a piece of the machine. -/
theorem decPiece_mem {p : Program} {s : PSpec} (h : s ∈ machSpecs p) : s.piece ∈ machPieces p :=
  List.mem_map_of_mem h

/-- The register of a `decJz` instruction is a register of the program. -/
theorem lt_numRegs_of_dec {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    r < numRegs p := by
  have := reg_lt_R p hi
  simp only [regBound] at this
  omega

/-- The pieces of a module are pieces of the machine. -/
theorem decModule_mem {p : Program} {r : ℕ} (hr : r < numRegs p) {s : PSpec}
    (hs : s ∈ moduleSpecs p r) : s.piece ∈ machPieces p :=
  decPiece_mem (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, hs⟩)))

/-- The pieces of a used unit are pieces of the machine. -/
theorem decUnit_mem {p : Program} {a : ℕ} (ha : a < p.length + numRegs p)
    (hu : unitUsed p a = true) {s : PSpec} (hs : s ∈ unitSpecs p a) : s.piece ∈ machPieces p :=
  decPiece_mem (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨a, List.mem_filter.2 ⟨List.mem_range.2 ha, hu⟩, hs⟩)))

/-- The reflectors of the routes of `decJz r z` at instruction `i` are pieces of the machine. -/
theorem decRefl_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) {g : WL}
    {cs : List Corner} (hx : (g, cs) ∈ decSpecs p i r z) : ∀ x ∈ reflP g cs, x ∈ machPieces p := by
  intro x hx'
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx'
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have hI : instrSpecs p i = decSpecs p i r z := by unfold instrSpecs; rw [hi]
  refine decPiece_mem (List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨i, List.mem_range.2 hlt, ?_⟩)))
  rw [hI]
  exact List.mem_flatMap.2 ⟨(g, cs), hx, hs⟩

/-- The copies `0 … t` of the entry chain of an instruction unit are pieces of the machine. -/
theorem decChain_mem {p : Program} {a t : ℕ} (ha : a < p.length) (ht : (t : ℤ) < 2 * P p) :
    ∀ x ∈ chainPieces p a t, x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  refine decUnit_mem (a := a) (by omega) (by simp [unitUsed, ha]) (List.mem_append_left _ ?_)
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hs
  unfold P at ht
  exact List.mem_map.2 ⟨t', List.mem_range.2 (by have := List.mem_range.1 ht'; omega), rfl⟩

/-- The DEC copies of the activation are pieces of the machine. -/
theorem decChainP_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decChainP p i r, x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (decChainP_sub hi hx)
  refine decModule_mem (lt_numRegs_of_dec hi) ?_
  unfold moduleSpecs
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ hs)))

/-- The register circuit of module `r` is part of the machine. -/
theorem modGroup_mem {p : Program} {r : ℕ} (hr : r < numRegs p) :
    ∀ x ∈ modGroup p r, x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  refine decModule_mem hr ?_
  unfold moduleSpecs
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ hs))))

/-- The stations `0 … j - 1` of the line NZ are pieces of the machine. -/
theorem decLSN_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLSN p i r, x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hx)
  have hj := callerIdx_lt_D p hi
  refine decModule_mem (lt_numRegs_of_dec hi) ?_
  unfold moduleSpecs
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  simp only [stationSpecs, List.mem_flatMap, List.mem_range] at hs ⊢
  obtain ⟨k, hk, hs⟩ := hs
  exact ⟨k, by omega, hs⟩

/-- The stations `0 … j - 1` of the line Z are pieces of the machine. -/
theorem decLSZ_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLSZ p i r, x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (mem_dd.1 hx)
  have hj := callerIdx_lt_D p hi
  refine decModule_mem (lt_numRegs_of_dec hi) ?_
  unfold moduleSpecs
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  simp only [stationZSpecs, List.mem_flatMap, List.mem_range] at hs ⊢
  obtain ⟨k, hk, hs⟩ := hs
  exact ⟨k, by omega, hs⟩

/-- Station `j` of the line NZ is part of the machine. -/
theorem stNZOne_mach {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ stNZOne p r (callerIdx p r i), x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (stNZOne_mem p r (callerIdx_lt_D p hi) hx)
  exact decModule_mem (lt_numRegs_of_dec hi) hs

/-- Station `j` of the line Z is part of the machine. -/
theorem stZOne_mach {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ stZOne p r (callerIdx p r i), x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (stZOne_mem p r (callerIdx_lt_D p hi) hx)
  exact decModule_mem (lt_numRegs_of_dec hi) hs

/-- The pieces of the control thread are pieces of the machine. -/
theorem decLC_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLC p i r, x ∈ machPieces p := by
  intro x hx
  rcases List.mem_append.1 (mem_dd.1 hx) with h | h
  · exact decRefl_mem hi (by rw [decSpecs_eq]; simp) x h
  · exact decChainP_mem hi x h

/-- The pieces of the `KNZ` thread are pieces of the machine. -/
theorem decLNu_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLNu p i r, x ∈ machPieces p := by
  intro x hx
  rcases List.mem_append.1 (mem_dd.1 hx) with h | h
  · exact decRefl_mem hi (by rw [decSpecs_eq]; simp) x h
  · exact stNZOne_mach hi x h

/-- The pieces of the `KZ` thread are pieces of the machine. -/
theorem decLZu_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLZu p i r, x ∈ machPieces p := by
  intro x hx
  rcases List.mem_append.1 (mem_dd.1 hx) with h | h
  · exact decRefl_mem hi (by rw [decSpecs_eq]; simp) x h
  · exact stZOne_mach hi x h

/-- The reflectors of `KNZ` are pieces of the machine. -/
theorem decLN_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLN p i r, x ∈ machPieces p :=
  fun x hx => decRefl_mem hi (by rw [decSpecs_eq]; simp) x (mem_dd.1 hx)

/-- The reflectors of `KZ` are pieces of the machine. -/
theorem decLZ_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ decLZ p i r, x ∈ machPieces p :=
  fun x hx => decRefl_mem hi (by rw [decSpecs_eq]; simp) x (mem_dd.1 hx)

/-- The pieces of the end of an NZ activation are pieces of the machine. -/
theorem decLFN_mem {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) : ∀ x ∈ decLFN p i r, x ∈ machPieces p := by
  intro x hx
  have ht := decTN_range hp hi
  rcases List.mem_append.1 (mem_dd.1 hx) with h | h
  · rcases List.mem_append.1 h with h | h
    · exact stNZOne_mach hi x h
    · exact decRefl_mem hi (by rw [decSpecs_eq]; simp [decCsN]) x h
  · exact decChain_mem (succ_lt_of_dec hp hi)
      (by unfold decTNn; rw [Int.toNat_of_nonneg ht.1]; exact ht.2) x h

/-- The pieces of the end of a Z activation are pieces of the machine. -/
theorem decLFZ_mem {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) : ∀ x ∈ decLFZ p i r z, x ∈ machPieces p := by
  intro x hx
  have ht := decTZ_range hp hi
  rcases List.mem_append.1 (mem_dd.1 hx) with h | h
  · rcases List.mem_append.1 h with h | h
    · exact stZOne_mach hi x h
    · exact decRefl_mem hi (by rw [decSpecs_eq]; simp [decCsZ]) x h
  · exact decChain_mem (lt_of_dec hp hi)
      (by unfold decTZn; rw [Int.toNat_of_nonneg ht.1]; exact ht.2) x h

/-! ### The body of the `dec` unit -/

/-- The body of the `dec` unit `a` as pieces. -/
def bodyDecGroup (p : Program) (a : ℕ) : List Piece :=
  (groupSpecs ((List.range 8).map Base.bodyDec) (unitDX p a) (unitDY p a)).map PSpec.piece

/-- The region of the body run of unit `a` (placed). -/
def bodyDecBox (p : Program) (a : ℕ) : Set Cell :=
  (fun c => (unitDX p a, unitDY p a) + c) '' bodyDecRegion

/-- The groups of the `dec` body at time `0` are `bodyDecRest`. -/
theorem piecesAt_bodyDec : piecesAt bodyDecPieces 0 = bodyDecRest := by
  simp only [piecesAt, Nat.zero_mod, Rule.evolve_zero, bodyDecPieces, List.foldr_cons,
    List.foldr_nil, union_empty, bodyDecRest]
  rw [show bodyDecG0.rest = bodyDecR0 from rfl, show bodyDecG1.rest = bodyDecR1 from rfl,
    show bodyDecG2.rest = bodyDecR2 from rfl, show bodyDecG3.rest = bodyDecR3 from rfl,
    show bodyDecG4.rest = bodyDecR4 from rfl, show bodyDecG5.rest = bodyDecR5 from rfl,
    show bodyDecG6.rest = bodyDecR6 from rfl, show bodyDecG7.rest = bodyDecR7 from rfl]
  ac_rfl

/-- **The body of unit `a` at a time `≡ 0 (mod 30)`**: `bodyDecRest`, translated. -/
theorem bodyDecGroup_at (p : Program) (a : ℕ) {T : ℕ} (hT : T % 30 = 0) :
    piecesAt (bodyDecGroup p a) T = translate (unitDX p a, unitDY p a) bodyDecRest := by
  rw [bodyDecGroup, piecesAt_group, List.map_map]
  have e : ((List.range 8).map (Base.piece ∘ Base.bodyDec)) = bodyDecPieces := bodyDec_map
  rw [e, piecesAt_mod bodyDecPieces (show T % 30 = 0 % 30 by omega), piecesAt_bodyDec]

/-- The body of the `dec` unit of instruction `i` is part of the machine. -/
theorem bodyDecGroup_mem {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∀ x ∈ bodyDecGroup p i, x ∈ machPieces p := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have hk : unitKind p i = .dec := by unfold unitKind; rw [hi]
  refine decUnit_mem (a := i) (by omega) (by simp [unitUsed, hlt]) ?_
  unfold unitSpecs
  rw [hk]
  exact List.mem_append_right _ hs

/-- **The body of the `dec` unit `i`** with the rest of the machine idle: the control at the
entrance becomes, `3180` generations later, the gliders `KNZ`, `C` and `KZ`. -/
theorem decBody_window {p : Program} {i : ℕ} (hp : p.WellFormed)
    (hmem : ∀ x ∈ bodyDecGroup p i, x ∈ machPieces p)
    (hfar : ∀ g ∈ machPieces p, g ∉ bodyDecGroup p i → FarApart 2 (bodyDecBox p i) g.box) :
    Reaction (piecesAt (machPieces p) 1080 ∪ ctrlAt p i)
      (piecesAt (machPieces p) (1080 + 3180) ∪ ((unitWL p i decLWL).cells 4260 ∪
        ((unitWL p i decRWL).cells 4260 ∪ (unitWL p i decDWL).cells 4260))) 3180
      (fun _ => boxesOf (machPieces p) ∪ bodyDecBox p i) := by
  have h := bodyDecRun_restG.translate (unitDX p i, unitDY p i)
  have hb : Reaction (piecesAt (bodyDecGroup p i) 1080 ∪ ctrlAt p i)
      (piecesAt (bodyDecGroup p i) (1080 + 3180) ∪ ((unitWL p i decLWL).cells 4260 ∪
        ((unitWL p i decRWL).cells 4260 ∪ (unitWL p i decDWL).cells 4260))) 3180
      (fun _ => bodyDecBox p i) := by
    rw [bodyDecGroup_at p i (by norm_num), bodyDecGroup_at p i (by norm_num), ctrlAt,
      unitWL_cells p i (w := decLWL) ⟨Or.inl rfl, Or.inl rfl⟩,
      unitWL_cells p i (w := decRWL) ⟨Or.inl rfl, Or.inl rfl⟩,
      unitWL_cells p i (w := decDWL) ⟨Or.inl rfl, Or.inl rfl⟩, ← translate_union,
      ← translate_union, ← translate_union, ← translate_union]
    have e1 : decLWL.cells 4260 = ofRows 399 554 [1, 6, 3] := rfl
    have e2 : decRWL.cells 4260 = ofRows 760 633 [1, 6, 3] := rfl
    have e3 : decDWL.cells 4260 = ofRows 868 681 [5, 6, 2] := rfl
    have eQ : bodyDecRest ∪ (ofRows 399 554 [1, 6, 3] ∪ (ofRows 760 633 [1, 6, 3] ∪
        ofRows 868 681 [5, 6, 2])) = bodyDecRest ∪ ofRows 868 681 [5, 6, 2] ∪
        ofRows 760 633 [1, 6, 3] ∪ ofRows 399 554 [1, 6, 3] := by ac_rfl
    rw [e1, e2, e3, bodyIn, eQ]
    exact h
  exact window_mem (machPieces_sep p hp) hmem 1080 3180 hb fun _ _ g hg hn => hfar g hg hn

/-! ### Composition with absolute times -/

/-- **Sequential composition with footprints at absolute times**: a reaction from `a` and one from
`b = a + n`. -/
theorem Reaction.seqAbs {P Q R : Finset Cell} {n m a b : ℕ} {F G : ℕ → Set Cell}
    (h : Reaction P Q n (fun k => F (a + k))) (h' : Reaction Q R m (fun k => G (b + k)))
    (hb : b = a + n) :
    Reaction P R (n + m) (fun k => if a + k ≤ b then F (a + k) else G (a + k)) := by
  refine (h.seq h').mono fun k _ => ?_
  split_ifs with h1 h2 h2
  · exact Set.Subset.rfl
  · omega
  · omega
  · rw [show b + (k - n) = a + k by omega]

/-- The boxes of a concatenation. -/
theorem boxesOf_append (A B : List Piece) : boxesOf (A ++ B) = boxesOf A ∪ boxesOf B := by
  ext c
  simp only [mem_boxesOf, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨g, hg | hg, hc⟩
    · exact Or.inl ⟨g, hg, hc⟩
    · exact Or.inr ⟨g, hg, hc⟩
  · rintro (⟨g, hg, hc⟩ | ⟨g, hg, hc⟩)
    · exact ⟨g, Or.inl hg, hc⟩
    · exact ⟨g, Or.inr hg, hc⟩

/-- A list of pieces of the machine, without repetitions, is separated. -/
theorem ddW {p : Program} (hp : p.WellFormed) {W : List Piece} (h : ∀ x ∈ W, x ∈ machPieces p) :
    (dd W).Pairwise Piece.Sep :=
  dd_pairwise (machPieces_sep p hp) h

/-! ### The lists and footprints of the two branches -/

/-- The reflectors of the NZ answer and the entry copies of unit `i + 1`. -/
noncomputable def decLF0N (p : Program) (i r : ℕ) : List Piece :=
  dd (reflP (decGN p i r) (decCsN p i r) ++ chainPieces p (i + 1) (decTNn p i r))

/-- The reflectors of the Z answer and the entry copies of unit `z`. -/
noncomputable def decLF0Z (p : Program) (i r z : ℕ) : List Piece :=
  dd (reflP (decGZ p i r) (decCsZ p i r z) ++ chainPieces p z (decTZn p i r z))

/-- The active pieces of the main thread of an NZ activation. -/
noncomputable def decLMN (p : Program) (i r : ℕ) : List Piece :=
  decLC p i r ++ modGroup p r ++ decLSN p i r ++ decLNu p i r ++ decLF0N p i r

/-- The active pieces of the main thread of a Z activation. -/
noncomputable def decLMZ (p : Program) (i r z : ℕ) : List Piece :=
  decLC p i r ++ modGroup p r ++ decLSZ p i r ++ decLZu p i r ++ decLF0Z p i r z

/-- The footprint of the control, the register run and the answer (NZ), absolute time `t`. -/
def qFootN (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decTS p i r then
    boxesOf (modGroup p r ++ decLSN p i r) ∪ (boxesOf (decLC p i r) ∪ decFootC p i r t ∪
      modLanes p r)
  else if t ≤ decCutN p i r then
    boxesOf (decLC p i r ++ decLSN p i r) ∪ modImg p r decRunRegNZ
  else boxesOf (decLC p i r) ∪ (restFootN p i r t ∪ (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t))

/-- The footprint of the control, the register run and the answer (Z), absolute time `t`. -/
def qFootZ (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decTS p i r then
    boxesOf (modGroup p r ++ decLSZ p i r) ∪ (boxesOf (decLC p i r) ∪ decFootC p i r t ∪
      modLanes p r)
  else if t ≤ decCutZ p i r then
    boxesOf (decLC p i r ++ decLSZ p i r) ∪ modImg p r decRunRegZ
  else boxesOf (decLC p i r) ∪ (restFootZ p i r t ∪ (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t))

/-- **The footprint of the main thread of an NZ activation**, absolute time `t`. -/
def footMN (p : Program) (i r : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decCapN p i r then
    boxesOf (decLF0N p i r) ∪ (qFootN p i r t ∪ (boxesOf (decLNu p i r) ∪ tokFootN p i r t))
  else boxesOf (decLC p i r ++ decLSN p i r ++ decLN p i r) ∪
    (restFootN p i r t ∪ (boxesOf (decLFN p i r) ∪ finFootN p i r t))

/-- **The footprint of the main thread of a Z activation**, absolute time `t`. -/
def footMZ (p : Program) (i r z : ℕ) (t : ℕ) : Set Cell :=
  if t ≤ decCapZ p i r then
    boxesOf (decLF0Z p i r z) ∪ (qFootZ p i r t ∪ (boxesOf (decLZu p i r) ∪ tokFootZ p i r t))
  else boxesOf (decLC p i r ++ decLSZ p i r ++ decLZ p i r) ∪
    (restFootZ p i r t ∪ (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t))

/-! ### Pieces of the lists -/

/-- The pieces of a list given by membership in two lists. -/
theorem piecesAt_of_mem {L A B : List Piece} (h : ∀ x, x ∈ L ↔ x ∈ A ∨ x ∈ B) (T : ℕ) :
    piecesAt L T = piecesAt A T ∪ piecesAt B T := by
  ext c
  simp only [mem_piecesAt, mem_union]
  constructor
  · rintro ⟨g, hg, hc⟩
    rcases (h g).1 hg with hg | hg
    · exact Or.inl ⟨g, hg, hc⟩
    · exact Or.inr ⟨g, hg, hc⟩
  · rintro (⟨g, hg, hc⟩ | ⟨g, hg, hc⟩)
    · exact ⟨g, (h g).2 (Or.inl hg), hc⟩
    · exact ⟨g, (h g).2 (Or.inr hg), hc⟩

/-- The `KNZ` thread: its reflectors and station `j` of the line NZ. -/
theorem piecesAt_LNu (p : Program) (i r T : ℕ) :
    piecesAt (decLNu p i r) T = piecesAt (decLN p i r) T ∪
      piecesAt (stNZOne p r (callerIdx p r i)) T :=
  piecesAt_of_mem (fun x => by simp only [decLNu, decLN, mem_dd, List.mem_append]) T

/-- The `KZ` thread: its reflectors and station `j` of the line Z. -/
theorem piecesAt_LZu (p : Program) (i r T : ℕ) :
    piecesAt (decLZu p i r) T = piecesAt (decLZ p i r) T ∪
      piecesAt (stZOne p r (callerIdx p r i)) T :=
  piecesAt_of_mem (fun x => by simp only [decLZu, decLZ, mem_dd, List.mem_append]) T

/-- The end of an NZ activation: station `j` and the answer link. -/
theorem piecesAt_LFN (p : Program) (i r T : ℕ) :
    piecesAt (decLFN p i r) T = piecesAt (stNZOne p r (callerIdx p r i)) T ∪
      piecesAt (decLF0N p i r) T :=
  piecesAt_of_mem (fun x => by
    simp only [decLFN, decLF0N, mem_dd, List.mem_append, or_assoc]) T

/-- The end of a Z activation: station `j` and the answer link. -/
theorem piecesAt_LFZ (p : Program) (i r z T : ℕ) :
    piecesAt (decLFZ p i r z) T = piecesAt (stZOne p r (callerIdx p r i)) T ∪
      piecesAt (decLF0Z p i r z) T :=
  piecesAt_of_mem (fun x => by
    simp only [decLFZ, decLF0Z, mem_dd, List.mem_append, or_assoc]) T

/-- Sequential composition at absolute times through a glue equality. -/
theorem Reaction.seqAbs_eq {P Q Q' R : Finset Cell} {n m a b : ℕ} {F G : ℕ → Set Cell}
    (h : Reaction P Q n (fun k => F (a + k))) (e : Q = Q')
    (h' : Reaction Q' R m (fun k => G (b + k))) (hb : b = a + n) :
    Reaction P R (n + m) (fun k => if a + k ≤ b then F (a + k) else G (a + k)) :=
  Reaction.seqAbs (e ▸ h) h' hb

/-! ### The INC gate of the module, with its tight footprint -/

/-- **The tight footprint of the INC OR gate** of module `r`: the cells of its `30` phases lie in
its box without the corner `[60, 90] × [20, 32]` (gate frame, `orGateTight`). -/
def gateFoot (p : Program) (r : ℕ) : Set Cell :=
  (fun c => (modDX p r - 1132, modDY p r - 1291) + c) '' orGateTight

/-- **The INC gate idles inside its tight footprint.** -/
theorem gateIdle (p : Program) (r T n : ℕ) :
    Reaction (piecesAt [gateP p r] T) (piecesAt [gateP p r] (T + n)) n
      (fun _ => gateFoot p r) := by
  refine ⟨(idleR (List.pairwise_singleton _ _) T n).evolve_eq, fun k _ => ?_⟩
  have e : conway.evolve k (piecesAt [gateP p r] T) =
      translate (modDX p r - 1132, modDY p r - 1291)
        (conway.evolve ((k + (T % 30 + 16 % 30)) % 30) orGate) := by
    simp only [piecesAt, List.foldr_cons, List.foldr_nil, union_empty, gateP, incGateSpec,
      PSpec.piece, Piece.place, Base.piece, orGateP, phase]
    rw [Rule.evolve_translate, Rule.evolve_translate, ← Rule.evolve_add, ← Rule.evolve_add,
      ← conway.evolve_mod_of_evolve_eq orGate_rest.evolve_eq, add_assoc]
  rw [e]
  intro c hc
  rw [mem_coe, mem_translate] at hc
  refine ⟨c - (modDX p r - 1132, modDY p r - 1291),
    orGate_phases_tight _ (Nat.mod_lt _ (by norm_num)) (mem_coe.2 hc), ?_⟩
  simp

/-- The tight footprint of the INC gate lies in the box of the gate. -/
theorem gateFoot_subset (p : Program) (r : ℕ) : gateFoot p r ⊆ (gateP p r).box := by
  rintro _ ⟨c, hc, rfl⟩
  simp only [gateP, incGateSpec, PSpec.piece, Piece.place, Piece.box, Box, Base.piece, orGateP,
    Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add]
  rcases hc with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩ <;> omega

/-! ### The separation facts -/

/-- **The separation facts of a `decJz` activation** (instruction `decJz r z` at `i`), for both
answers: the routes (`RouteSepX`, corner windows), the flights (each up to the joint approach of
the piece it enters: `20` generations before a side input, `90` before a capture), the joint
approaches and the reactions (exact evolutions or certified boxes) far from the other pieces, the
concurrent processes far apart, the idle pieces and the lanes of the registers. Before the cut the
register runs use the regions of the runs up to the cut (`decRunRegNZ`, `decRunRegZ`); the captures
run until the dispatched answer is clear of its station (`692` / `672` generations); the INC gate of
the module runs in the `Z` thread with its tight footprint `gateFoot` (`zGate`). -/
structure DecSep (p : Program) (i r z : ℕ) : Prop where
  /-- The route of `C` (corner windows). -/
  sepC : RouteSepX (machPieces p) (machRegion p) (unitWL p i decRWL) (decCornC p i r)
    ((4260 : ℕ) : ℤ)
  /-- The flight of `C` until `20` generations before the side input of DEC copy `m`. -/
  flyC : ∀ t : ℕ, routeEndX (unitWL p i decRWL) (decCornC p i r) 4260 ≤ t →
    t < decTA p i r - 20 → ∀ h ∈ decLC p i r, FarApart 2 ((decGC p i r).box t) h.box
  /-- The joint approach of `C` and DEC copy `m`. -/
  sideC : ∀ h ∈ decLC p i r, h ≠ decCopyM p i r → FarApart 2 (decSideBoxC p i r) h.box
  /-- The DEC chain. -/
  chainC : ∀ h ∈ decLC p i r, h ∉ decChainP p i r → FarApart 2 (decChainFoot p i r) h.box
  /-- The flight of `C'` to the register run. -/
  cpC : ∀ t : ℕ, decTB p i r ≤ t → t < decTS p i r → ∀ h ∈ decLC p i r,
    FarApart 2 (decCpFoot p i r t) h.box
  /-- The route of `KNZ`. -/
  sepN : RouteSepX (machPieces p) (machRegion p) (unitWL p i decLWL) (decCornN p i r)
    ((4260 : ℕ) : ℤ)
  /-- The flight of `KNZ` until `90` generations before the capture position. -/
  flyN : ∀ t : ℕ, routeEndX (unitWL p i decLWL) (decCornN p i r) 4260 ≤ t →
    t < decCapN p i r - 90 → ∀ h ∈ decLNu p i r, FarApart 2 ((decTokN p i r).box t) h.box
  /-- The joint approach of `KNZ` and its station. -/
  winN : ∀ k < 90, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decTokWStartN p i r) : Set Cell) h.box
  /-- The route of `KZ`. -/
  sepZ : RouteSepX (machPieces p) (machRegion p) (unitWL p i decDWL) (decCornZ p i r)
    ((4260 : ℕ) : ℤ)
  /-- The flight of `KZ` until `90` generations before the capture position. -/
  flyZ : ∀ t : ℕ, routeEndX (unitWL p i decDWL) (decCornZ p i r) 4260 ≤ t →
    t < decCapZ p i r - 90 → ∀ h ∈ decLZu p i r, FarApart 2 ((decTokZ p i r).box t) h.box
  /-- The joint approach of `KZ` and its station. -/
  winZ : ∀ k < 90, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decTokWStartZ p i r) : Set Cell) h.box
  /-- The register circuit and the lanes of its register. -/
  grpLane : FarApart 2 (boxesOf (modGroup p r)) (modLanes p r)
  /-- The body. -/
  body : ∀ g ∈ machPieces p, g ∉ bodyDecGroup p i → FarApart 2 (bodyDecBox p i) g.box
  /-- The lanes of distinct registers. -/
  lanes : ∀ r₁ < numRegs p, ∀ r₂ < numRegs p, r₁ ≠ r₂ →
    FarApart 2 (modLanes p r₁) (modLanes p r₂)
  /-- The machine and the body against the lanes of every register. -/
  laneBody : ∀ r' < numRegs p, FarApart 2 (boxesOf (machPieces p) ∪ bodyDecBox p i)
    (modLanes p r')
  /-- (NZ) The absorption of the unpaired `KZ`. -/
  unpZ : ∀ k < 272, ∀ h ∈ decLZu p i r, h ∉ stZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decUnpStartZ p i r) : Set Cell) h.box
  /-- (NZ) The answer's flight from the cut to station `0`. -/
  ansFlyN : ∀ t : ℕ, decCutN p i r ≤ t → t < decSt0N p i r → ∀ h ∈ decLSN p i r,
    FarApart 2 ((decAnsWLN p i r).box t) h.box
  /-- (NZ) The capture at station `j`. -/
  capN : ∀ k < 692, ∀ h ∈ decLFN p i r, h ∉ stNZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decCapStartN p i r) : Set Cell) h.box
  /-- (NZ) The route of the answer. -/
  sepAN : RouteSepX (machPieces p) (machRegion p) (decGN p i r) (decCsN p i r)
    ((decDispN p i r : ℕ) : ℤ)
  /-- (NZ) The answer's flight until `16` generations before the side input. -/
  flyAN : ∀ t : ℕ, routeEndX (decGN p i r) (decCsN p i r) (decDispN p i r) ≤ t →
    t + 16 < decT0N p i r → ∀ h ∈ decLFN p i r, FarApart 2 ((decFinN p i r).box t) h.box
  /-- (NZ) The entry chain of unit `i + 1`. -/
  entAN : ∀ h ∈ decLFN p i r, h ∉ chainPieces p (i + 1) (decTNn p i r) →
    FarApart 2 (entryFoot p (i + 1) (decTNn p i r)) h.box
  /-- (NZ) The flight to the body input of unit `i + 1`. -/
  outAN : ∀ t : ℕ, t < 166 → ∀ h ∈ decLFN p i r, FarApart 2
    ((fun c => (unitDX p (i + 1), unitDY p (i + 1)) + c) '' chainOutWL.box (-166 + (t : ℤ)))
    h.box
  /-- (NZ) The control and the lanes of register `r`. -/
  nQ1a : ∀ t : ℕ, 4260 ≤ t → t < decTS p i r →
    FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t) (modLanes p r)
  /-- (NZ) The control and the lanes against the circuit and the stations. -/
  nQ1b : ∀ t : ℕ, 4260 ≤ t → t < decTS p i r → ∀ g ∈ modGroup p r ++ decLSN p i r,
    FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r) g.box
  /-- (NZ) The run against the control's pieces and the stations. -/
  nQ2 : ∀ g ∈ decLC p i r ++ decLSN p i r, FarApart 2 (modImg p r decRunRegNZ) g.box
  /-- (NZ) The rest of the run against the answer. -/
  nQ3a : ∀ t : ℕ, decCutN p i r ≤ t → t < decCapN p i r →
    FarApart 2 (restFootN p i r t) (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t)
  /-- (NZ) The rest of the run and the answer against the control's pieces. -/
  nQ3b : ∀ t : ℕ, decCutN p i r ≤ t → t < decCapN p i r → ∀ g ∈ decLC p i r,
    FarApart 2 (restFootN p i r t ∪ (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t)) g.box
  /-- (NZ) The control, the run and the answer against `KNZ`. -/
  nQN : ∀ t : ℕ, 4260 ≤ t → t < decCapN p i r →
    FarApart 2 (qFootN p i r t) (boxesOf (decLNu p i r) ∪ tokFootN p i r t)
  /-- (NZ) Before the capture, against the pieces of the answer link. -/
  nQF : ∀ t : ℕ, 4260 ≤ t → t < decCapN p i r → ∀ g ∈ decLF0N p i r,
    FarApart 2 (qFootN p i r t ∪ (boxesOf (decLNu p i r) ∪ tokFootN p i r t)) g.box
  /-- (NZ) The rest of the run against the end. -/
  nA2a : ∀ t : ℕ, decCapN p i r ≤ t → t < decEndN p i r →
    FarApart 2 (restFootN p i r t) (boxesOf (decLFN p i r) ∪ finFootN p i r t)
  /-- (NZ) The end against the pieces of the control, the stations and `KNZ`. -/
  nA2b : ∀ t : ℕ, decCapN p i r ≤ t → t < decEndN p i r →
    ∀ g ∈ decLC p i r ++ decLSN p i r ++ decLN p i r,
    FarApart 2 (restFootN p i r t ∪ (boxesOf (decLFN p i r) ∪ finFootN p i r t)) g.box
  /-- (NZ) The main thread against the unpaired `KZ`. -/
  nThr : ∀ t : ℕ, 4260 ≤ t → t < decEndN p i r →
    FarApart 2 (footMN p i r t) (boxesOf (decLZu p i r) ∪ unpFootZ p i r t)
  /-- (NZ) The threads against every idle piece. -/
  nIdle : ∀ t : ℕ, 4260 ≤ t → t < decEndN p i r → ∀ g ∈ machPieces p,
    g ∉ decLMN p i r ++ decLZu p i r →
    FarApart 2 (footMN p i r t ∪ (boxesOf (decLZu p i r) ∪ unpFootZ p i r t)) g.box
  /-- (NZ) The machine and the threads against the lanes of the other registers. -/
  nLane : ∀ t : ℕ, 4260 ≤ t → t < decEndN p i r → ∀ r' < numRegs p, r' ≠ r →
    FarApart 2 (boxesOf (machPieces p) ∪ (footMN p i r t ∪ (boxesOf (decLZu p i r) ∪
      unpFootZ p i r t))) (modLanes p r')
  /-- (Z) The absorption of the unpaired `KNZ`. -/
  unpN : ∀ k < 292, ∀ h ∈ decLNu p i r, h ∉ stNZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decUnpStartN p i r) : Set Cell) h.box
  /-- (Z) The answer's flight from the cut to station `0`. -/
  ansFlyZ : ∀ t : ℕ, decCutZ p i r ≤ t → t < decSt0Z p i r → ∀ h ∈ decLSZ p i r,
    FarApart 2 ((decAnsWLZ p i r).box t) h.box
  /-- (Z) The capture at station `j`. -/
  capZ : ∀ k < 672, ∀ h ∈ decLFZ p i r z, h ∉ stZOne p r (callerIdx p r i) →
    FarApart 2 (conway.evolve k (decCapStartZ p i r) : Set Cell) h.box
  /-- (Z) The route of the answer. -/
  sepAZ : RouteSepX (machPieces p) (machRegion p) (decGZ p i r) (decCsZ p i r z)
    ((decDispZ p i r : ℕ) : ℤ)
  /-- (Z) The answer's flight until `16` generations before the side input. -/
  flyAZ : ∀ t : ℕ, routeEndX (decGZ p i r) (decCsZ p i r z) (decDispZ p i r) ≤ t →
    t + 16 < decT0Z p i r z → ∀ h ∈ decLFZ p i r z, FarApart 2 ((decFinZ p i r z).box t) h.box
  /-- (Z) The entry chain of unit `z`. -/
  entAZ : ∀ h ∈ decLFZ p i r z, h ∉ chainPieces p z (decTZn p i r z) →
    FarApart 2 (entryFoot p z (decTZn p i r z)) h.box
  /-- (Z) The flight to the body input of unit `z`. -/
  outAZ : ∀ t : ℕ, t < 166 → ∀ h ∈ decLFZ p i r z, FarApart 2
    ((fun c => (unitDX p z, unitDY p z) + c) '' chainOutWL.box (-166 + (t : ℤ)))
    h.box
  /-- (Z) The control and the lanes of register `r`. -/
  zQ1a : ∀ t : ℕ, 4260 ≤ t → t < decTS p i r →
    FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t) (modLanes p r)
  /-- (Z) The control and the lanes against the circuit and the stations. -/
  zQ1b : ∀ t : ℕ, 4260 ≤ t → t < decTS p i r → ∀ g ∈ modGroup p r ++ decLSZ p i r,
    FarApart 2 (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r) g.box
  /-- (Z) The run against the control's pieces and the stations. -/
  zQ2 : ∀ g ∈ decLC p i r ++ decLSZ p i r, FarApart 2 (modImg p r decRunRegZ) g.box
  /-- (Z) The rest of the run against the answer. -/
  zQ3a : ∀ t : ℕ, decCutZ p i r ≤ t → t < decCapZ p i r →
    FarApart 2 (restFootZ p i r t) (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t)
  /-- (Z) The rest of the run and the answer against the control's pieces. -/
  zQ3b : ∀ t : ℕ, decCutZ p i r ≤ t → t < decCapZ p i r → ∀ g ∈ decLC p i r,
    FarApart 2 (restFootZ p i r t ∪ (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t)) g.box
  /-- (Z) The control, the run and the answer against `KZ`. -/
  zQZ : ∀ t : ℕ, 4260 ≤ t → t < decCapZ p i r →
    FarApart 2 (qFootZ p i r t) (boxesOf (decLZu p i r) ∪ tokFootZ p i r t)
  /-- (Z) Before the capture, against the pieces of the answer link. -/
  zQF : ∀ t : ℕ, 4260 ≤ t → t < decCapZ p i r → ∀ g ∈ decLF0Z p i r z,
    FarApart 2 (qFootZ p i r t ∪ (boxesOf (decLZu p i r) ∪ tokFootZ p i r t)) g.box
  /-- (Z) The rest of the run against the end. -/
  zA2a : ∀ t : ℕ, decCapZ p i r ≤ t → t < decEndZ p i r z →
    FarApart 2 (restFootZ p i r t) (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t)
  /-- (Z) The end against the pieces of the control, the stations and `KZ`. -/
  zA2b : ∀ t : ℕ, decCapZ p i r ≤ t → t < decEndZ p i r z →
    ∀ g ∈ decLC p i r ++ decLSZ p i r ++ decLZ p i r,
    FarApart 2 (restFootZ p i r t ∪ (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t)) g.box
  /-- (Z) The main thread against the unpaired `KNZ`. -/
  zThr : ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z →
    FarApart 2 (footMZ p i r z t) (boxesOf (decLNu p i r) ∪ unpFootN p i r t)
  /-- (Z) The threads against the INC gate of the module (with its tight footprint). -/
  zGate : ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z →
    FarApart 2 (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪ unpFootN p i r t)) (gateFoot p r)
  /-- (Z) The threads and the INC gate against every idle piece. -/
  zIdle : ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z → ∀ g ∈ machPieces p,
    g ∉ decLMZ p i r z ++ decLNu p i r ++ [gateP p r] →
    FarApart 2 (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪ unpFootN p i r t) ∪ gateFoot p r)
      g.box
  /-- (Z) The machine and the threads against the lanes of the other registers. -/
  zLane : ∀ t : ℕ, 4260 ≤ t → t < decEndZ p i r z → ∀ r' < numRegs p, r' ≠ r →
    FarApart 2 (boxesOf (machPieces p) ∪ (footMZ p i r z t ∪ (boxesOf (decLNu p i r) ∪
      unpFootN p i r t) ∪ gateFoot p r)) (modLanes p r')

/-! ### The main thread of an NZ activation -/

/-- **The main thread of an NZ activation** (register value `≥ 1`): from the end of the body at
`4260` (the control `C`, the token `KNZ`, the register diagonal) to the control at the entrance of
unit `i + 1` at `decEndN`, the register holding one less. -/
theorem decThreadN {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hs : DecSep p i r z) {R0 : RegS} (hR : R0.Ready)
    (hpos : 1 ≤ R0.val) :
    ∃ R' : RegS, R'.val + 1 = R0.val ∧ R'.Ready ∧
      Reaction (piecesAt (decLMN p i r) 4260 ∪ ((unitWL p i decRWL).cells 4260 ∪
          ((unitWL p i decLWL).cells 4260 ∪ regAt p r R0)))
        (piecesAt (decLMN p i r) (decEndN p i r) ∪ (ctrlAt p (i + 1) ∪ regAt p r R'))
        (decEndN p i r - 4260) (fun k => footMN p i r (4260 + k)) := by
  obtain ⟨hTS, hTS30, hTA⟩ := decTS_facts p hi
  obtain ⟨-, -, -, -, hEnd, -⟩ := decN_times hp hi
  have hr := lt_numRegs_of_dec hi
  have t1 : 4260 ≤ decTS p i r := by unfold decTS; omega
  have hCut : decCutN p i r = decTS p i r + 9503 := rfl
  have hCap : decCapN p i r = decTS p i r + 10650 + 288 * callerIdx p r i := rfl
  have hRE : decRunEndN p i r = decTS p i r + 11490 := rfl
  have t2 : decCutN p i r ≤ decCapN p i r := by omega
  have t3 : decCapN p i r ≤ decEndN p i r := by omega
  have t4 : decRunEndN p i r ≤ decEndN p i r := by omega
  have hn : decCapN p i r - 4260 + (decEndN p i r - decCapN p i r) = decEndN p i r - 4260 := by
    omega
  have hQn : decTS p i r - 4260 + (9503 + (decCapN p i r - decCutN p i r)) =
      decCapN p i r - 4260 := by
    rw [hCap, hCut]
    clear * - t1
    omega
  -- phase 1: the control beside the register, the circuit and the stations idle
  have PC := decCProc hp hi (decLC_mem hi) hs.sepC hs.flyC hs.sideC hs.chainC hs.cpC
  have RG := (regAt_reaction p r hR.1 (decTS p i r - 4260)).mono
    (F' := fun _ => modLanes p r) fun k _ => regStrip_subset hR.1 p r k
  have Q1p := PC.par RG fun k hk => hs.nQ1a (4260 + k) (by omega) (by omega)
  have Q1 := windowW (W := modGroup p r ++ decLSN p i r) (ddW hp fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · exact modGroup_mem hr x h
      · exact decLSN_mem hi x h) 4260 (decTS p i r - 4260) Q1p
    fun k hk g hg => hs.nQ1b (4260 + k) (by omega) (by omega) g hg
  rw [show 4260 + (decTS p i r - 4260) = decTS p i r by omega] at Q1
  -- phase 2: the register run
  obtain ⟨X, R', hval, hrdy, hrun, hrest⟩ := decRunNProc hi (hR.later (decTS p i r - 4260))
    (by rw [RegS.val_later]; exact hpos) hs.grpLane (decEndN p i r) t4
  have Q2 := windowW (W := decLC p i r ++ decLSN p i r) (ddW hp fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · exact decLC_mem hi x h
      · exact decLSN_mem hi x h) (decTS p i r) 9503 hrun
    fun k hk g hg => hs.nQ2 g hg
  -- phase 3: the rest of the run beside the answer
  obtain ⟨Rh, Rt⟩ := Reaction.splitAt hrest (decCapN p i r - decCutN p i r) (by omega)
  have PA := decAnsNProc hp hi (decLSN_mem hi) hs.ansFlyN
  have Q3p := Rh.par PA fun k hk => hs.nQ3a (decCutN p i r + k) (by omega) (by omega)
  have Q3 := windowW (W := decLC p i r) (ddW hp (decLC_mem hi)) (decCutN p i r)
    (decCapN p i r - decCutN p i r) Q3p
    fun k hk g hg => hs.nQ3b (decCutN p i r + k) (by omega) (by omega) g hg
  rw [show decCutN p i r + (decCapN p i r - decCutN p i r) = decCapN p i r by omega] at Q3
  have e2 : piecesAt (decLC p i r ++ decLSN p i r) (decTS p i r + 9503) ∪
      (X ∪ (decAnsWLN p i r).cells (decCutN p i r)) = piecesAt (decLC p i r) (decCutN p i r) ∪
      (X ∪ (piecesAt (decLSN p i r) (decCutN p i r) ∪
        (decAnsWLN p i r).cells (decCutN p i r))) := by
    rw [piecesAt_append, show decTS p i r + 9503 = decCutN p i r from rfl]; ac_rfl
  have Q23 := Reaction.seqAbs_eq (a := decTS p i r) (b := decCutN p i r)
    (F := fun _ => boxesOf (decLC p i r ++ decLSN p i r) ∪ modImg p r decRunRegNZ)
    (G := fun t => boxesOf (decLC p i r) ∪ (restFootN p i r t ∪
      (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t))) Q2 e2 Q3 rfl
  have e1 : piecesAt (modGroup p r ++ decLSN p i r) (decTS p i r) ∪
      (piecesAt (decLC p i r) (decTS p i r) ∪
        translate (modDX p r, modDY p r) (ofRows (-1186) (-1227) [2, 4, 7]) ∪
        regAt p r (R0.later (decTS p i r - 4260))) =
      piecesAt (decLC p i r ++ decLSN p i r) (decTS p i r) ∪
        (piecesAt (modGroup p r) (decTS p i r) ∪
        (translate (modDX p r, modDY p r) (ofRows (-1186) (-1227) [2, 4, 7]) ∪
          regAt p r (R0.later (decTS p i r - 4260)))) := by
    rw [piecesAt_append, piecesAt_append]; ac_rfl
  have Q := Reaction.seqAbs_eq (a := 4260) (b := decTS p i r)
    (F := fun t => boxesOf (modGroup p r ++ decLSN p i r) ∪
      (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r))
    (G := fun t => if t ≤ decCutN p i r then
      boxesOf (decLC p i r ++ decLSN p i r) ∪ modImg p r decRunRegNZ else
      boxesOf (decLC p i r) ∪ (restFootN p i r t ∪
        (boxesOf (decLSN p i r) ∪ decAnsFootN p i r t))) Q1 e1 Q23 (by omega)
  -- `KNZ` beside, the pieces of the answer link idle
  have PN := decTokNProc hi (decLNu_mem hi)
    (dd_pairwise (machPieces_sep p hp) fun x hx => decLNu_mem hi x (mem_dd.2 hx))
    (fun x hx => mem_dd.2 (List.mem_append_left _ hx))
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx)) hs.sepN hs.flyN hs.winN
  have Qq := (Q.castN hQn).mono (F' := fun k => qFootN p i r (4260 + k)) fun k _ => by
    simp only [qFootN]
    split_ifs <;> exact Set.Subset.rfl
  have A1p := Qq.par PN fun k hk => hs.nQN (4260 + k) (by omega) (by omega)
  have A1 := windowW (W := decLF0N p i r) (ddW hp fun x hx => decLFN_mem hp hi x
      (mem_dd.2 (by
        rcases List.mem_append.1 (mem_dd.1 hx) with h | h
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h))) 4260 (decCapN p i r - 4260) A1p
    fun k hk g hg => hs.nQF (4260 + k) (by omega) (by omega) g hg
  rw [show 4260 + (decCapN p i r - 4260) = decCapN p i r by omega] at A1
  -- the end: the rest of the run beside the capture and the answer link
  have PF := decFinNProc hp hi (decLFN_mem hp hi) hs.capN hs.sepAN hs.flyAN hs.entAN hs.outAN
  have Rt' := Rt.castN (m := decEndN p i r - decCapN p i r) (by omega)
  have A2p := (Rt'.mono (F' := fun k => restFootN p i r (decCapN p i r + k)) fun k _ => by
      rw [show decCutN p i r + (k + (decCapN p i r - decCutN p i r)) = decCapN p i r + k by
        omega]).par PF
    fun k hk => hs.nA2a (decCapN p i r + k) (by omega) (by omega)
  have A2 := windowW (W := decLC p i r ++ decLSN p i r ++ decLN p i r) (ddW hp fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · rcases List.mem_append.1 h with h | h
        · exact decLC_mem hi x h
        · exact decLSN_mem hi x h
      · exact decLN_mem hi x h) (decCapN p i r) (decEndN p i r - decCapN p i r) A2p
    fun k hk g hg => hs.nA2b (decCapN p i r + k) (by omega) (by omega) g hg
  rw [show decCapN p i r + (decEndN p i r - decCapN p i r) = decEndN p i r by omega] at A2
  have e3 : piecesAt (decLF0N p i r) (decCapN p i r) ∪
      (piecesAt (decLC p i r) (decCapN p i r) ∪
          (conway.evolve (decCapN p i r - decCutN p i r) X ∪
            (piecesAt (decLSN p i r) (decCapN p i r) ∪ (decAnsWLN p i r).cells (decCapN p i r))) ∪
        (piecesAt (decLNu p i r) (decCapN p i r) ∪ (decTokN p i r).cells (decCapN p i r))) =
      piecesAt (decLC p i r ++ decLSN p i r ++ decLN p i r) (decCapN p i r) ∪
      (conway.evolve (decCapN p i r - decCutN p i r) X ∪
        (piecesAt (decLFN p i r) (decCapN p i r) ∪
          ((decAnsWLN p i r).cells (decCapN p i r) ∪ (decTokN p i r).cells (decCapN p i r)))) := by
    rw [piecesAt_append, piecesAt_append, piecesAt_LNu, piecesAt_LFN]; ac_rfl
  have W := Reaction.seqAbs_eq (a := 4260) (b := decCapN p i r)
    (F := fun t => boxesOf (decLF0N p i r) ∪ (qFootN p i r t ∪
      (boxesOf (decLNu p i r) ∪ tokFootN p i r t)))
    (G := fun t => boxesOf (decLC p i r ++ decLSN p i r ++ decLN p i r) ∪
      (restFootN p i r t ∪ (boxesOf (decLFN p i r) ∪ finFootN p i r t))) A1 e3 A2 (by omega)
  have W' := W.castN hn
  have hv' : (R'.later (decEndN p i r - decRunEndN p i r)).val + 1 = R0.val := by
    rw [RegS.val_later, hval, RegS.val_later]
  refine ⟨R'.later (decEndN p i r - decRunEndN p i r), hv', hrdy.later _, ?_⟩
  refine (W'.congrPQ ?_ ?_).mono fun k _ => ?_
  · simp only [decLMN, piecesAt_append, piecesAt_LNu]
    ac_rfl
  · simp only [decLMN, piecesAt_append, piecesAt_LNu, piecesAt_LFN]
    ac_rfl
  · simp only [footMN]
    split_ifs <;> exact Set.Subset.rfl

/-! ### The main thread of a Z activation -/

/-- **The main thread of a Z activation** (register value `0`): from the end of the body at
`4260` (the control `C`, the token `KZ`, the register diagonal) to the control at the entrance of
unit `z` at `decEndZ`, the register unchanged. -/
theorem decThreadZ {p : Program} {i r z : ℕ} (hp : p.WellFormed)
    (hi : p[i]? = some (.decJz r z)) (hs : DecSep p i r z) {R0 : RegS} (hR : R0.Ready)
    (h0 : R0.val = 0) :
      Reaction (piecesAt (decLMZ p i r z) 4260 ∪ ((unitWL p i decRWL).cells 4260 ∪
          ((unitWL p i decDWL).cells 4260 ∪ regAt p r R0)))
        (piecesAt (decLMZ p i r z) (decEndZ p i r z) ∪
          (ctrlAt p z ∪ regAt p r (R0.later (decEndZ p i r z - 4260))))
        (decEndZ p i r z - 4260) (fun k => footMZ p i r z (4260 + k)) := by
  obtain ⟨hTS, hTS30, hTA⟩ := decTS_facts p hi
  obtain ⟨-, -, -, -, hEnd, hDT⟩ := decZ_times hp hi
  have hEZ : decT0Z p i r z ≤ decEndZ p i r z := by unfold decEndZ; omega
  have hDZ : decDispZ p i r = decTS p i r + 13362 + 288 * callerIdx p r i := rfl
  have hr := lt_numRegs_of_dec hi
  have t1 : 4260 ≤ decTS p i r := by unfold decTS; omega
  have hCut : decCutZ p i r = decTS p i r + 11995 := rfl
  have hCap : decCapZ p i r = decTS p i r + 12690 + 288 * callerIdx p r i := rfl
  have hRE : decRunEndZ p i r = decTS p i r + 27540 := rfl
  have t2 : decCutZ p i r ≤ decCapZ p i r := by omega
  have t3 : decCapZ p i r ≤ decEndZ p i r z := by omega
  have t4 : decRunEndZ p i r ≤ decEndZ p i r z := by omega
  have hn : decCapZ p i r - 4260 + (decEndZ p i r z - decCapZ p i r) = decEndZ p i r z - 4260 := by
    omega
  have hlat : decTS p i r - 4260 + (decEndZ p i r z - decTS p i r) = decEndZ p i r z - 4260 := by
    clear * - t1 t3 hCap
    omega
  have hQn : decTS p i r - 4260 + (11995 + (decCapZ p i r - decCutZ p i r)) =
      decCapZ p i r - 4260 := by
    rw [hCap, hCut]
    clear * - t1
    omega
  -- phase 1: the control beside the register, the circuit and the stations idle
  have PC := decCProc hp hi (decLC_mem hi) hs.sepC hs.flyC hs.sideC hs.chainC hs.cpC
  have RG := (regAt_reaction p r hR.1 (decTS p i r - 4260)).mono
    (F' := fun _ => modLanes p r) fun k _ => regStrip_subset hR.1 p r k
  have Q1p := PC.par RG fun k hk => hs.zQ1a (4260 + k) (by omega) (by omega)
  have Q1 := windowW (W := modGroup p r ++ decLSZ p i r) (ddW hp fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · exact modGroup_mem hr x h
      · exact decLSZ_mem hi x h) 4260 (decTS p i r - 4260) Q1p
    fun k hk g hg => hs.zQ1b (4260 + k) (by omega) (by omega) g hg
  rw [show 4260 + (decTS p i r - 4260) = decTS p i r by omega] at Q1
  -- phase 2: the register run
  obtain ⟨X, hrun, hrest⟩ := decRunZProc hi (hR.later (decTS p i r - 4260))
    (by rw [RegS.val_later]; exact h0) hs.grpLane (decEndZ p i r z) t4
  have Q2 := windowW (W := decLC p i r ++ decLSZ p i r) (ddW hp fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · exact decLC_mem hi x h
      · exact decLSZ_mem hi x h) (decTS p i r) 11995 hrun
    fun k hk g hg => hs.zQ2 g hg
  -- phase 3: the rest of the run beside the answer
  obtain ⟨Rh, Rt⟩ := Reaction.splitAt hrest (decCapZ p i r - decCutZ p i r) (by omega)
  have PA := decAnsZProc hp hi (decLSZ_mem hi) hs.ansFlyZ
  have Q3p := Rh.par PA fun k hk => hs.zQ3a (decCutZ p i r + k) (by omega) (by omega)
  have Q3 := windowW (W := decLC p i r) (ddW hp (decLC_mem hi)) (decCutZ p i r)
    (decCapZ p i r - decCutZ p i r) Q3p
    fun k hk g hg => hs.zQ3b (decCutZ p i r + k) (by omega) (by omega) g hg
  rw [show decCutZ p i r + (decCapZ p i r - decCutZ p i r) = decCapZ p i r by omega] at Q3
  have e2 : piecesAt (decLC p i r ++ decLSZ p i r) (decTS p i r + 11995) ∪
      (X ∪ (decAnsWLZ p i r).cells (decCutZ p i r)) = piecesAt (decLC p i r) (decCutZ p i r) ∪
      (X ∪ (piecesAt (decLSZ p i r) (decCutZ p i r) ∪
        (decAnsWLZ p i r).cells (decCutZ p i r))) := by
    rw [piecesAt_append, show decTS p i r + 11995 = decCutZ p i r from rfl]; ac_rfl
  have Q23 := Reaction.seqAbs_eq (a := decTS p i r) (b := decCutZ p i r)
    (F := fun _ => boxesOf (decLC p i r ++ decLSZ p i r) ∪ modImg p r decRunRegZ)
    (G := fun t => boxesOf (decLC p i r) ∪ (restFootZ p i r t ∪
      (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t))) Q2 e2 Q3 rfl
  have e1 : piecesAt (modGroup p r ++ decLSZ p i r) (decTS p i r) ∪
      (piecesAt (decLC p i r) (decTS p i r) ∪
        translate (modDX p r, modDY p r) (ofRows (-1186) (-1227) [2, 4, 7]) ∪
        regAt p r (R0.later (decTS p i r - 4260))) =
      piecesAt (decLC p i r ++ decLSZ p i r) (decTS p i r) ∪
        (piecesAt (modGroup p r) (decTS p i r) ∪
        (translate (modDX p r, modDY p r) (ofRows (-1186) (-1227) [2, 4, 7]) ∪
          regAt p r (R0.later (decTS p i r - 4260)))) := by
    rw [piecesAt_append, piecesAt_append]; ac_rfl
  have Q := Reaction.seqAbs_eq (a := 4260) (b := decTS p i r)
    (F := fun t => boxesOf (modGroup p r ++ decLSZ p i r) ∪
      (boxesOf (decLC p i r) ∪ decFootC p i r t ∪ modLanes p r))
    (G := fun t => if t ≤ decCutZ p i r then
      boxesOf (decLC p i r ++ decLSZ p i r) ∪ modImg p r decRunRegZ else
      boxesOf (decLC p i r) ∪ (restFootZ p i r t ∪
        (boxesOf (decLSZ p i r) ∪ decAnsFootZ p i r t))) Q1 e1 Q23 (by omega)
  -- `KNZ` beside, the pieces of the answer link idle
  have PN := decTokZProc hi (decLZu_mem hi)
    (dd_pairwise (machPieces_sep p hp) fun x hx => decLZu_mem hi x (mem_dd.2 hx))
    (fun x hx => mem_dd.2 (List.mem_append_left _ hx))
    (fun x hx => mem_dd.2 (List.mem_append_right _ hx)) hs.sepZ hs.flyZ hs.winZ
  have Qq := (Q.castN hQn).mono (F' := fun k => qFootZ p i r (4260 + k)) fun k _ => by
    simp only [qFootZ]
    split_ifs <;> exact Set.Subset.rfl
  have A1p := Qq.par PN fun k hk => hs.zQZ (4260 + k) (by omega) (by omega)
  have A1 := windowW (W := decLF0Z p i r z) (ddW hp fun x hx => decLFZ_mem hp hi x
      (mem_dd.2 (by
        rcases List.mem_append.1 (mem_dd.1 hx) with h | h
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h))) 4260 (decCapZ p i r - 4260) A1p
    fun k hk g hg => hs.zQF (4260 + k) (by omega) (by omega) g hg
  rw [show 4260 + (decCapZ p i r - 4260) = decCapZ p i r by omega] at A1
  -- the end: the rest of the run beside the capture and the answer link
  have PF := decFinZProc hp hi (decLFZ_mem hp hi) hs.capZ hs.sepAZ hs.flyAZ hs.entAZ hs.outAZ
  have Rt' := Rt.castN (m := decEndZ p i r z - decCapZ p i r) (by omega)
  have A2p := (Rt'.mono (F' := fun k => restFootZ p i r (decCapZ p i r + k)) fun k _ => by
      rw [show decCutZ p i r + (k + (decCapZ p i r - decCutZ p i r)) = decCapZ p i r + k by
        omega]).par PF
    fun k hk => hs.zA2a (decCapZ p i r + k) (by omega) (by omega)
  have A2 := windowW (W := decLC p i r ++ decLSZ p i r ++ decLZ p i r) (ddW hp fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · rcases List.mem_append.1 h with h | h
        · exact decLC_mem hi x h
        · exact decLSZ_mem hi x h
      · exact decLZ_mem hi x h) (decCapZ p i r) (decEndZ p i r z - decCapZ p i r) A2p
    fun k hk g hg => hs.zA2b (decCapZ p i r + k) (by omega) (by omega) g hg
  rw [show decCapZ p i r + (decEndZ p i r z - decCapZ p i r) = decEndZ p i r z by omega] at A2
  have e3 : piecesAt (decLF0Z p i r z) (decCapZ p i r) ∪
      (piecesAt (decLC p i r) (decCapZ p i r) ∪
          (conway.evolve (decCapZ p i r - decCutZ p i r) X ∪
            (piecesAt (decLSZ p i r) (decCapZ p i r) ∪ (decAnsWLZ p i r).cells (decCapZ p i r))) ∪
        (piecesAt (decLZu p i r) (decCapZ p i r) ∪ (decTokZ p i r).cells (decCapZ p i r))) =
      piecesAt (decLC p i r ++ decLSZ p i r ++ decLZ p i r) (decCapZ p i r) ∪
      (conway.evolve (decCapZ p i r - decCutZ p i r) X ∪
        (piecesAt (decLFZ p i r z) (decCapZ p i r) ∪
          ((decAnsWLZ p i r).cells (decCapZ p i r) ∪ (decTokZ p i r).cells (decCapZ p i r)))) := by
    rw [piecesAt_append, piecesAt_append, piecesAt_LZu, piecesAt_LFZ]; ac_rfl
  have W := Reaction.seqAbs_eq (a := 4260) (b := decCapZ p i r)
    (F := fun t => boxesOf (decLF0Z p i r z) ∪ (qFootZ p i r t ∪
      (boxesOf (decLZu p i r) ∪ tokFootZ p i r t)))
    (G := fun t => boxesOf (decLC p i r ++ decLSZ p i r ++ decLZ p i r) ∪
      (restFootZ p i r t ∪ (boxesOf (decLFZ p i r z) ∪ finFootZ p i r z t))) A1 e3 A2 (by omega)
  have W' := W.castN hn
  rw [RegS.later_later', hlat] at W'
  refine (W'.congrPQ ?_ ?_).mono fun k _ => ?_
  · simp only [decLMZ, piecesAt_append, piecesAt_LZu]
    ac_rfl
  · simp only [decLMZ, piecesAt_append, piecesAt_LZu, piecesAt_LFZ]
    ac_rfl
  · simp only [footMZ]
    split_ifs <;> exact Set.Subset.rfl

end LP

end LeanTheory.Life
