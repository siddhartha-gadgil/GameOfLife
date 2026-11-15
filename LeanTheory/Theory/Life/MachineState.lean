/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.LayoutPieces
public import LeanTheory.Theory.Life.DiagProc

/-!
# Machine states of the simulator and their encoding

Layer 4 of the assembly plan (research note `N-22`): the state of the Life machine of a counter
program `p` (layout `LP`, `LayoutPieces`) at the start of an activation, and its encoding as a
finite configuration.

* **Gliders on world lines** (`LP.WL.cells`): the glider of the world line `(d, lane, tau)` of
  `scripts/life_gates/life.py` (`glider_at`) at any time; `LP.WL.evolve_cells`: a glider flies along
  its world line; `LP.WL.shift_cells`: the world line moved by `LP.WL.shift` is the glider
  translated and delayed. These connect the world-line arithmetic of `LayoutPieces` (`route`,
  `reflect`) to configurations.
* **States** (`LP.RegS`, `LP.MState`): the program counter, the global time `T` (the machine
  pieces are at phase `T`), and for every register its diagonal (`N-20`): the queue `q` of salvos
  in flight and the block `K` at a reference time, the generations `m` since that reference and the
  strip bounds `Vs`, `Vb`.
* **Encoding** (`LP.encM`): every piece of `LP.machPieces p` at phase `T`, the control glider at
  the entrance of the body of unit `pc` (the output line of the entry chain), and the diagonal of
  every register placed at its module.
* **Invariant** (`LP.InvM`), **projection** (`LP.MState.cfg`), **region** (`LP.machRegion`) and
  **halt cell** (`LP.haltCell`, outside the region).
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Canonical gliders -/

/-- The four phases of the canonical glider flying `SE` (`life.py`, `_PHASES`). -/
def glSE : ℕ → Finset Cell
  | 0 => ofRows 0 0 [2, 4, 7]
  | 1 => ofRows 0 1 [5, 6, 2]
  | 2 => ofRows 0 1 [4, 5, 6]
  | _ => ofRows 1 1 [1, 6, 3]

/-- The four phases of the canonical glider flying `SW`. -/
def glSW : ℕ → Finset Cell
  | 0 => ofRows 0 0 [2, 1, 7]
  | 1 => ofRows 0 1 [5, 3, 2]
  | 2 => ofRows 0 1 [1, 5, 3]
  | _ => ofRows (-1) 1 [4, 3, 6]

/-- The four phases of the canonical glider flying `NW`. -/
def glNW : ℕ → Finset Cell
  | 0 => ofRows 0 0 [7, 1, 2]
  | 1 => ofRows 0 (-1) [2, 3, 5]
  | 2 => ofRows 0 (-1) [3, 5, 1]
  | _ => ofRows (-1) (-1) [6, 3, 4]

/-- The four phases of the canonical glider flying `NE`. -/
def glNE : ℕ → Finset Cell
  | 0 => ofRows 0 0 [7, 4, 2]
  | 1 => ofRows 0 (-1) [2, 6, 5]
  | 2 => ofRows 0 (-1) [6, 5, 4]
  | _ => ofRows 1 (-1) [3, 6, 1]

/-- Phase `j` of the canonical glider of direction `(dx, dy)`. -/
def glPh (dx dy : ℤ) (j : ℕ) : Finset Cell :=
  if dx = 1 then (if dy = 1 then glSE j else glNE j) else (if dy = 1 then glSW j else glNW j)

/-- **Certificate**: the `SE` glider, one generation. -/
theorem glSE_step : ∀ j < 3, conway.evolve 1 (glSE j) = glSE (j + 1)
  | 0, _ => by simp only [glSE]; life_cert
  | 1, _ => by simp only [glSE]; life_cert
  | 2, _ => by simp only [glSE]; life_cert

/-- **Certificate**: the `SW` glider, one generation. -/
theorem glSW_step : ∀ j < 3, conway.evolve 1 (glSW j) = glSW (j + 1)
  | 0, _ => by simp only [glSW]; life_cert
  | 1, _ => by simp only [glSW]; life_cert
  | 2, _ => by simp only [glSW]; life_cert

/-- **Certificate**: the `NW` glider, one generation. -/
theorem glNW_step : ∀ j < 3, conway.evolve 1 (glNW j) = glNW (j + 1)
  | 0, _ => by simp only [glNW]; life_cert
  | 1, _ => by simp only [glNW]; life_cert
  | 2, _ => by simp only [glNW]; life_cert

/-- **Certificate**: the `NE` glider, one generation. -/
theorem glNE_step : ∀ j < 3, conway.evolve 1 (glNE j) = glNE (j + 1)
  | 0, _ => by simp only [glNE]; life_cert
  | 1, _ => by simp only [glNE]; life_cert
  | 2, _ => by simp only [glNE]; life_cert

/-- **Certificate**: the `SE` glider, the fourth generation moves it by `(1, 1)`. -/
theorem glSE_wrap : conway.evolve 1 (glSE 3) = translate (1, 1) (glSE 0) := by
  simp only [glSE, translate_ofRows]; life_cert

/-- **Certificate**: the `SW` glider, the fourth generation moves it by `(-1, 1)`. -/
theorem glSW_wrap : conway.evolve 1 (glSW 3) = translate (-1, 1) (glSW 0) := by
  simp only [glSW, translate_ofRows]; life_cert

/-- **Certificate**: the `NW` glider, the fourth generation moves it by `(-1, -1)`. -/
theorem glNW_wrap : conway.evolve 1 (glNW 3) = translate (-1, -1) (glNW 0) := by
  simp only [glNW, translate_ofRows]; life_cert

/-- **Certificate**: the `NE` glider, the fourth generation moves it by `(1, -1)`. -/
theorem glNE_wrap : conway.evolve 1 (glNE 3) = translate (1, -1) (glNE 0) := by
  simp only [glNE, translate_ofRows]; life_cert

/-- A diagonal direction: both components are `±1`. -/
def IsDir (dx dy : ℤ) : Prop := (dx = 1 ∨ dx = -1) ∧ (dy = 1 ∨ dy = -1)

/-- One generation of a canonical glider, phases `0 … 2`. -/
theorem glPh_step {dx dy : ℤ} (h : IsDir dx dy) {j : ℕ} (hj : j < 3) :
    conway.evolve 1 (glPh dx dy j) = glPh dx dy (j + 1) := by
  obtain ⟨hx | hx, hy | hy⟩ := h <;> subst hx hy <;> simp only [glPh] <;> norm_num
  · exact glSE_step j hj
  · exact glNE_step j hj
  · exact glSW_step j hj
  · exact glNW_step j hj

/-- The fourth generation of a canonical glider moves it by its direction. -/
theorem glPh_wrap {dx dy : ℤ} (h : IsDir dx dy) :
    conway.evolve 1 (glPh dx dy 3) = translate (dx, dy) (glPh dx dy 0) := by
  obtain ⟨hx | hx, hy | hy⟩ := h <;> subst hx hy <;> simp only [glPh] <;> norm_num
  · exact glSE_wrap
  · exact glNE_wrap
  · exact glSW_wrap
  · exact glNW_wrap

/-- Every phase of a canonical glider lies in the box `[-1, 3] × [-1, 3]`. -/
theorem glPh_subset (dx dy : ℤ) (j : ℕ) : (glPh dx dy j : Set Cell) ⊆ Box (-1) 3 (-1) 3 := by
  simp only [glPh]
  split_ifs <;> rcases j with _ | _ | _ | j <;>
    exact coe_ofRows_subset_box rfl

/-! ### Gliders on world lines -/

/-- A world line has a diagonal direction. -/
def WL.Dir (w : WL) : Prop := IsDir w.dx w.dy

/-- The quarter period count of the world line `w` at time `t`. -/
def WL.qt (w : WL) (t : ℤ) : ℤ := (t - w.tau) / 4

/-- The `x` of the reference corner of the glider of `w` at time `t`. -/
def WL.px (w : WL) (t : ℤ) : ℤ := w.dx * w.qt t

/-- The `y` of the reference corner of the glider of `w` at time `t`. -/
def WL.py (w : WL) (t : ℤ) : ℤ := w.dx * (w.dy * w.px t - w.lane)

/-- **The glider of the world line `w` at time `t`** (`life.glider_at`): the canonical glider of
the direction in phase `(t - tau) mod 4`, at `x = dx q`, `y = dx (dy x - lane)`,
`q = ⌊(t - tau) / 4⌋`. -/
def WL.cells (w : WL) (t : ℤ) : Finset Cell :=
  translate (w.px t, w.py t) (glPh w.dx w.dy ((t - w.tau) % 4).toNat)

/-- The box of the glider of `w` at time `t`. -/
def WL.box (w : WL) (t : ℤ) : Set Cell :=
  Box (w.px t - 1) (w.px t + 3) (w.py t - 1) (w.py t + 3)

/-- The glider of a world line lies in its box. -/
theorem WL.cells_subset (w : WL) (t : ℤ) : (w.cells t : Set Cell) ⊆ w.box t := by
  intro c hc
  rw [WL.cells, mem_coe, mem_translate] at hc
  obtain ⟨h1, h2, h3, h4⟩ := glPh_subset _ _ _ (mem_coe.2 hc)
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **One generation of flight** along a world line. -/
theorem WL.evolve_one_cells {w : WL} (h : w.Dir) (t : ℤ) :
    conway.evolve 1 (w.cells t) = w.cells (t + 1) := by
  unfold WL.cells WL.py WL.px WL.qt
  rw [Rule.evolve_translate]
  by_cases hr : (t - w.tau) % 4 < 3
  · have e1 : (t + 1 - w.tau) / 4 = (t - w.tau) / 4 := by omega
    have e2 : ((t + 1 - w.tau) % 4).toNat = ((t - w.tau) % 4).toNat + 1 := by omega
    rw [glPh_step h (by omega), e1, e2]
  · have e1 : (t + 1 - w.tau) / 4 = (t - w.tau) / 4 + 1 := by omega
    have e2 : ((t + 1 - w.tau) % 4).toNat = 0 := by omega
    have e3 : ((t - w.tau) % 4).toNat = 3 := by omega
    rw [e3, glPh_wrap h, translate_translate, e1, e2]
    congr 1
    obtain ⟨hx | hx, hy | hy⟩ := h <;> rw [hx, hy] <;> ext <;> simp <;> ring

/-- **Flight along a world line**: after `n` generations the glider of `w` at time `t` is the glider
of `w` at time `t + n`. -/
theorem WL.evolve_cells {w : WL} (h : w.Dir) (t : ℤ) (n : ℕ) :
    conway.evolve n (w.cells t) = w.cells (t + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 = 1 + n by ring, Rule.evolve_add, ih, WL.evolve_one_cells h]
    push_cast
    ring_nf

/-- **A flight as a reaction**, with the moving box of the glider as footprint. -/
theorem WL.flight {w : WL} (h : w.Dir) (t : ℤ) (n : ℕ) :
    Reaction (w.cells t) (w.cells (t + n)) n (fun i => w.box (t + i)) :=
  ⟨WL.evolve_cells h t n, fun i _ => by rw [WL.evolve_cells h]; exact WL.cells_subset w _⟩

/-- A shifted world line keeps its direction. -/
theorem WL.Dir.shift {w : WL} (h : w.Dir) (p q s : ℤ) : (w.shift p q s).Dir := h

/-- **The world line moved by `(p, q)` and delayed by `s`** carries the glider translated by
`(p, q)`, `s` generations later. -/
theorem WL.shift_cells {w : WL} (h : w.Dir) (p q s t : ℤ) :
    (w.shift p q s).cells t = translate (p, q) (w.cells (t - s)) := by
  obtain ⟨dx, dy, lane, tau⟩ := w
  obtain ⟨hx | hx, hy | hy⟩ := h <;> simp only at hx hy <;> subst hx hy <;>
  · unfold WL.cells WL.py WL.px WL.qt WL.shift
    simp only
    rw [translate_translate]
    congr 1
    · ext <;> simp <;> omega
    · congr 1
      omega

/-! ### Machine states -/

/-- The state of one register: its diagonal (`N-20`) is `evolve m (diagW q K)` (queue `q` and
block `K` at a reference time, `m` generations later), valid with the strip bounds `Vs`, `Vb`. -/
structure RegS where
  /-- The salvos in flight at the reference time. -/
  q : List (Salvo × ℤ)
  /-- The block at the reference time. -/
  K : ℤ
  /-- Generations since the reference time. -/
  m : ℕ
  /-- Strip bound of the salvos. -/
  Vs : ℤ
  /-- Strip bound of the blocks and reactions. -/
  Vb : ℤ

/-- The value of a register: the block once every salvo in flight has arrived. -/
def RegS.val (R : RegS) : ℕ := (R.K + qMove R.q).toNat

/-- A register holding `k`, with nothing in flight. -/
def RegS.ofNat (k : ℕ) : RegS := ⟨[], k, 0, 18, 18⟩

/-- The value of a register holding `k`. -/
@[simp] theorem RegS.val_ofNat (k : ℕ) : (RegS.ofNat k).val = k := by
  simp [RegS.val, RegS.ofNat, qMove]

/-- The register after `n` more generations. -/
def RegS.later (R : RegS) (n : ℕ) : RegS := { R with m := R.m + n }

/-- The value does not change with time. -/
@[simp] theorem RegS.val_later (R : RegS) (n : ℕ) : (R.later n).val = R.val := rfl

/-- The invariant of a register: a valid queue, the bounds used by the register operations
(`dz2eOp`, `dz2dOp`), and a nonnegative value. -/
def RegS.Inv (R : RegS) : Prop :=
  DiagValid regParams R.Vs R.Vb R.K R.q ∧ 18 ≤ R.Vb ∧ 18 ≤ R.Vs + 2 * ((R.m / 4 : ℕ) : ℤ) ∧
    0 ≤ R.K + qMove R.q

/-- A register holding `k` satisfies the invariant. -/
theorem RegS.inv_ofNat (k : ℕ) : (RegS.ofNat k).Inv := by
  refine ⟨?_, le_rfl, by simp [RegS.ofNat], by simp [RegS.ofNat, qMove]⟩
  simp only [RegS.ofNat, DiagValid]
  omega

/-- The invariant is kept with time. -/
theorem RegS.Inv.later {R : RegS} (h : R.Inv) (n : ℕ) : (R.later n).Inv := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, h4⟩
  have : R.m / 4 ≤ (R.m + n) / 4 := Nat.div_le_div_right (by omega)
  simp only [RegS.later]
  omega

/-- The state of the machine at the start of an activation: the program counter, the global time
`T` (every piece of the machine at phase `T`) and the registers. -/
structure MState where
  /-- The program counter. -/
  pc : ℕ
  /-- The global time. -/
  T : ℕ
  /-- The registers. -/
  reg : ℕ → RegS

/-- The configuration of the counter machine of a state. -/
def MState.cfg (s : MState) : Cfg := ⟨s.pc, fun r => (s.reg r).val⟩

/-! ### The encoding -/

/-- The pieces of a list, each at phase `T`. -/
def piecesAt (L : List Piece) (T : ℕ) : Finset Cell :=
  L.foldr (fun g S => conway.evolve (T % 30) g.rest ∪ S) ∅

/-- The boxes of the pieces of a list. -/
def boxesOf (L : List Piece) : Set Cell := L.foldr (fun g S => g.box ∪ S) ∅

/-- The idle bundle of a list of pieces from phase `T`, for `n` generations. -/
def bundleAt (L : List Piece) (hL : L.Pairwise Piece.Sep) (T n : ℕ) : Proc n :=
  Piece.bundle L hL (T % 30) n ((T + n) % 30) (by omega)

/-- The idle bundle starts at the pieces at phase `T`. -/
theorem bundleAt_P (L : List Piece) (hL : L.Pairwise Piece.Sep) (T n : ℕ) :
    (bundleAt L hL T n).P = piecesAt L T := by
  simp only [bundleAt, Piece.bundle]
  clear hL
  induction L with
  | nil => rfl
  | cons g L ih => simp only [List.map_cons, Proc.start_cons, ih, piecesAt, List.foldr_cons]; rfl

/-- The idle bundle ends at the pieces at phase `T + n`. -/
theorem bundleAt_Q (L : List Piece) (hL : L.Pairwise Piece.Sep) (T n : ℕ) :
    (bundleAt L hL T n).Q = piecesAt L (T + n) := by
  simp only [bundleAt, Piece.bundle]
  clear hL
  induction L with
  | nil => rfl
  | cons g L ih => simp only [List.map_cons, Proc.stop_cons, ih, piecesAt, List.foldr_cons]; rfl

/-- The footprint of the idle bundle is the union of the boxes. -/
theorem bundleAt_F (L : List Piece) (hL : L.Pairwise Piece.Sep) (T n i : ℕ) :
    (bundleAt L hL T n).F i = boxesOf L := by
  simp only [bundleAt, Piece.bundle]
  clear hL
  induction L with
  | nil => rfl
  | cons g L ih => simp only [List.map_cons, Proc.foot_cons, ih, boxesOf, List.foldr_cons]; rfl

/-- Every piece of the machine of `p` at phase `T`. -/
def machAt (p : Program) (T : ℕ) : Finset Cell := piecesAt (machPieces p) T

/-- **The machine idles**: for a well-formed program, all pieces at phase `T` become all pieces
at phase `T + n`, inside their boxes. -/
theorem machAt_reaction {p : Program} (hp : p.WellFormed) (T n : ℕ) :
    Reaction (machAt p T) (machAt p (T + n)) n (fun _ => boxesOf (machPieces p)) := by
  have h := (bundleAt (machPieces p) (machPieces_sep p hp) T n).reaction
  rw [bundleAt_P, bundleAt_Q] at h
  exact h.mono fun i _ => (bundleAt_F _ _ T n i).le

/-- The input glider of the body of a unit, in the frame of the unit template (`SE`, on the output
line `u = 14` of the entry chain, at phase `0`): the input of `bodyIncRun_rest` and
`bodyDecRun_rest`. -/
def bodyIn : Finset Cell := ofRows 113 99 [1, 6, 3]

/-- The control glider at the entrance of the body of unit `a`. -/
def ctrlAt (p : Program) (a : ℕ) : Finset Cell := translate (unitDX p a, unitDY p a) bodyIn

/-- The world line of the control glider of unit `a` (reference time `0`). -/
def ctrlWL (p : Program) (a : ℕ) : WL := unitWL p a ⟨1, 1, 14, -451⟩

/-- The control glider is the glider of its world line at time `0`. -/
theorem ctrlAt_eq (p : Program) (a : ℕ) : ctrlAt p a = (ctrlWL p a).cells 0 := by
  rw [ctrlWL, unitWL, WL.shift_cells (by exact ⟨Or.inl rfl, Or.inl rfl⟩), ctrlAt]
  congr 1

/-- The diagonal of a register placed at module `r`. -/
def regAt (p : Program) (r : ℕ) (R : RegS) : Finset Cell :=
  translate (modDX p r, modDY p r) (conway.evolve R.m (diagW R.q R.K))

/-- The strip of the diagonal of module `r` at generation `i` of the register's clock. -/
def regStrip (p : Program) (r : ℕ) (R : RegS) (i : ℕ) : Set Cell :=
  (fun c => (modDX p r, modDY p r) + c) '' wStrip R.Vs R.Vb i

/-- **The diagonal of a register as a process** (`diagW_reaction` placed at module `r`). -/
theorem regAt_reaction (p : Program) (r : ℕ) {R : RegS} (hR : R.Inv) (n : ℕ) :
    Reaction (regAt p r R) (regAt p r (R.later n)) n (fun i => regStrip p r R (i + R.m)) := by
  have h := (diagW_reaction hR.1 R.m n (R.m + n) (by omega)).translate (modDX p r, modDY p r)
  exact h

/-- The diagonals of the registers `0 … n - 1`. -/
def regsAt (p : Program) (reg : ℕ → RegS) (n : ℕ) : Finset Cell :=
  (List.range n).foldr (fun r S => regAt p r (reg r) ∪ S) ∅

/-- **The encoding of a state**: every piece of the machine at phase `T`, the control glider at the
entrance of unit `pc`, the diagonal of every register at its module. -/
def encM (p : Program) (s : MState) : Finset Cell :=
  machAt p s.T ∪ ctrlAt p s.pc ∪ regsAt p s.reg (numRegs p)

/-- **The invariant of the simulation** at the start of an activation: the program counter points
to an instruction, the machine is at phase `0`, every register of the program is valid, and the
registers beyond the program hold `0`. -/
def InvM (p : Program) (s : MState) : Prop :=
  s.pc < p.length ∧ s.T % 30 = 0 ∧ (∀ r < numRegs p, (s.reg r).Inv) ∧
    ∀ r, numRegs p ≤ r → (s.reg r).val = 0

/-- The start state for the input `n`: register `0` holds `n`, the others `0`, at time `0`. -/
def startM (n : ℕ) : MState := ⟨0, 0, fun r => RegS.ofNat (if r = 0 then n else 0)⟩

/-- The start state projects to the initial configuration. -/
theorem startM_cfg (n : ℕ) : (startM n).cfg = Cfg.init n := by
  simp only [MState.cfg, startM, RegS.val_ofNat, Cfg.init]
  congr 1
  funext r
  by_cases hr : r = 0 <;> simp [hr, Function.update]

/-- The start state satisfies the invariant (for a nonempty program). -/
theorem startM_inv {p : Program} (hp : 0 < p.length) (n : ℕ) : InvM p (startM n) := by
  refine ⟨hp, rfl, fun r _ => RegS.inv_ofNat _, fun r hr => ?_⟩
  have : r ≠ 0 := by
    have := le_max_left 1 ((p.map regBound).foldr max 0)
    unfold numRegs at hr
    omega
  simp [startM, this]

/-! ### The region of the machine and the halt cell -/

/-- The least `u = x - y` of the boxes of the pieces of the machine (at most `0`). -/
def uMin (p : Program) : ℤ := (machSpecs p).foldr (fun s m => min m (s.bx.a - s.bx.hi)) 0

/-- **The region of the machine**: every cell at most `300` left (in `u`) of every piece. -/
def machRegion (p : Program) : Set Cell := {c | uMin p - 300 ≤ c.1 - c.2}

/-- The halt cell: `600` left (in `u`) of every piece (`R-31` §6), near the top track. -/
def haltCell (p : Program) : Cell :=
  ((uMin p - 600 + VT p) / 2, (uMin p - 600 + VT p) / 2 - (uMin p - 600))

/-- **The halt cell is outside the region of the machine.** -/
theorem haltCell_notMem (p : Program) : haltCell p ∉ machRegion p := by
  change ¬ (uMin p - 300 ≤ (haltCell p).1 - (haltCell p).2)
  simp only [haltCell]
  omega

end LP

end LeanTheory.Life
