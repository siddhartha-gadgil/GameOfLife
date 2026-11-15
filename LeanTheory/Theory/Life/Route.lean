/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Chain

/-!
# Routes: lists of relay stages

A *stage* is a periodic piece (period `30`, at rest inside a box `B`) that, at phase `0`, turns an
input `In` into an output `Out` in `Δ` generations inside a box `R ⊇ B`: a reflector turning a
glider, a gate relaying it, a glider flying across empty space. A *route* is a list of stages, the
output of each the input of the next. `route_reaction` proves that a route carries its input to the
output of its last stage, provided the boxes of different stages are far apart (research note
`N-19`). Each piece starts at the phase that makes it ready when the signal arrives:
`routePieces l 0` puts the first piece at phase `0` and every later piece behind by the durations
of the stages before it.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- A relay stage: a periodic piece turning an input into an output. -/
structure Stage where
  /-- The piece at phase `0`. -/
  G : Finset Cell
  /-- The input arriving when the piece is at phase `0`. -/
  In : Finset Cell
  /-- The output, `Δ` generations later. -/
  Out : Finset Cell
  /-- The duration of the stage. -/
  Δ : ℕ
  /-- The box of the piece at rest. -/
  B : Set Cell
  /-- The box of the stage while it relays. -/
  R : Set Cell
  /-- The piece has period `30` and stays in its box. -/
  rest : Reaction G G 30 (fun _ => B)
  /-- The relay. -/
  relay : Reaction (G ∪ In) (phase G Δ ∪ Out) Δ (fun _ => R)
  /-- The rest box lies in the relay box. -/
  hBR : B ⊆ R

namespace Stage

/-- The pieces of a route, the first at phase `n`, each later one behind by the durations of the
stages before it. -/
def pieces : List Stage → ℕ → Finset Cell
  | [], _ => ∅
  | s :: l, n => phase s.G n ∪ pieces l (n + 29 * s.Δ)

/-- The total duration of a route. -/
def dur : List Stage → ℕ
  | [] => 0
  | s :: l => s.Δ + dur l

/-- The rest boxes of a route. -/
def restFoot : List Stage → Set Cell
  | [] => ∅
  | s :: l => s.B ∪ restFoot l

/-- The relay boxes of a route. -/
def relayFoot : List Stage → Set Cell
  | [] => ∅
  | s :: l => s.R ∪ relayFoot l

/-- The stages are linked: the output of each is the input of the next. -/
def Linked : List Stage → Prop
  | [] => True
  | [_] => True
  | s :: t :: l => s.Out = t.In ∧ Linked (t :: l)

/-- The boxes of different stages are far apart (rest and relay boxes, both orders). -/
def Sep : List Stage → Prop
  | [] => True
  | s :: l => (∀ t ∈ l, FarApart 2 s.R t.B ∧ FarApart 2 s.B t.R ∧ FarApart 2 s.B t.B) ∧ Sep l

/-- The output of the last stage. -/
def lastOut : List Stage → Finset Cell
  | [] => ∅
  | [s] => s.Out
  | _ :: t :: l => lastOut (t :: l)

/-- Whole periods do not matter. -/
theorem pieces_add_thirty : ∀ (l : List Stage) (n m : ℕ),
    pieces l (n + 30 * m) = pieces l n
  | [], _, _ => rfl
  | s :: l, n, m => by
    rw [pieces, pieces, show n + 30 * m + 29 * s.Δ = (n + 29 * s.Δ) + 30 * m by ring,
      pieces_add_thirty l, phase, phase, show (n + 30 * m) % 30 = n % 30 by omega]

/-- A set far from every rest box of a route is far from their union. -/
theorem farApart_restFoot {A : Set Cell} : ∀ (l : List Stage), (∀ t ∈ l, FarApart 2 A t.B) →
    FarApart 2 A (restFoot l)
  | [], _ => FarApart.empty_right 2 A
  | t :: l, h => FarApart.union_right (h t List.mem_cons_self)
      (farApart_restFoot l fun u hu => h u (List.mem_cons_of_mem t hu))

/-- A set far from every relay box of a route is far from their union. -/
theorem farApart_relayFoot {A : Set Cell} : ∀ (l : List Stage), (∀ t ∈ l, FarApart 2 A t.R) →
    FarApart 2 A (relayFoot l)
  | [], _ => FarApart.empty_right 2 A
  | t :: l, h => FarApart.union_right (h t List.mem_cons_self)
      (farApart_relayFoot l fun u hu => h u (List.mem_cons_of_mem t hu))

/-- The rest boxes lie in the relay boxes. -/
theorem restFoot_subset : ∀ (l : List Stage), restFoot l ⊆ relayFoot l
  | [] => le_rfl
  | s :: l => Set.union_subset_union s.hBR (restFoot_subset l)

/-- **A route at rest**: its pieces idle side by side for any number of generations. -/
theorem idle : ∀ (l : List Stage), Sep l → ∀ n m : ℕ,
    Reaction (pieces l n) (pieces l (n + m)) m (fun _ => restFoot l)
  | [], _, _, _ => ⟨by simp [pieces], fun _ _ c hc => by simp [pieces] at hc⟩
  | s :: l, ⟨h, hl⟩, n, m => by
    rw [pieces, pieces, show n + m + 29 * s.Δ = (n + 29 * s.Δ) + m by ring]
    exact (phase_reaction s.rest n m).par (idle l hl _ m)
      fun _ _ => farApart_restFoot l fun t ht => (h t ht).2.2

/-- **A route carries its input to the output of its last stage.** -/
theorem route_reaction : ∀ (s : Stage) (l : List Stage), Sep (s :: l) → Linked (s :: l) →
    Reaction (pieces (s :: l) 0 ∪ s.In) (pieces (s :: l) (dur (s :: l)) ∪ lastOut (s :: l))
      (dur (s :: l)) (fun _ => relayFoot (s :: l))
  | s, [], _, _ => by
    simp only [pieces, dur, lastOut, relayFoot, union_empty, Set.union_empty, add_zero]
    rw [phase, Nat.zero_mod, Rule.evolve_zero]
    exact s.relay
  | s, t :: l, ⟨h, hl⟩, ⟨hst, hlink⟩ => by
    -- stage 1: `s` relays, the rest idles
    have h1 := s.relay.par (idle (t :: l) hl (29 * s.Δ) s.Δ)
      fun _ _ => farApart_restFoot (t :: l) fun u hu => (h u hu).1
    -- stage 2: `s` idles, the rest of the route carries the signal
    have h2 := (phase_reaction s.rest s.Δ (dur (t :: l))).par (route_reaction t l hl hlink)
      fun _ _ => farApart_relayFoot (t :: l) fun u hu => (h u hu).2.1
    have e1 : pieces (t :: l) (29 * s.Δ + s.Δ) = pieces (t :: l) 0 := by
      rw [show 29 * s.Δ + s.Δ = 0 + 30 * s.Δ by ring, pieces_add_thirty]
    rw [e1] at h1
    have h := h1.seq_eq (by rw [hst]; ac_rfl) h2
    have e2 : pieces (s :: t :: l) (dur (s :: t :: l)) =
        phase s.G (s.Δ + dur (t :: l)) ∪ pieces (t :: l) (dur (t :: l)) := by
      rw [pieces, dur, show s.Δ + dur (t :: l) + 29 * s.Δ = dur (t :: l) + 30 * s.Δ by ring,
        pieces_add_thirty]
    have e3 : pieces (s :: t :: l) 0 = phase s.G 0 ∪ pieces (t :: l) (29 * s.Δ) := by
      rw [pieces, zero_add]
    rw [e2, e3, phase, Nat.zero_mod, Rule.evolve_zero, show dur (s :: t :: l) = s.Δ + dur (t :: l)
      from rfl, show lastOut (s :: t :: l) = lastOut (t :: l) from rfl,
      show s.G ∪ pieces (t :: l) (29 * s.Δ) ∪ s.In = s.G ∪ s.In ∪ pieces (t :: l) (29 * s.Δ) by
        ac_rfl,
      union_assoc (phase s.G (s.Δ + dur (t :: l)))]
    refine h.mono fun i _ => ?_
    split_ifs
    · exact Set.union_subset_union le_rfl (restFoot_subset _)
    · exact Set.union_subset_union s.hBR le_rfl

end Stage

end LeanTheory.Life
