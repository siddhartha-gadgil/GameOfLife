/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.LayoutLP
public import LeanTheory.Theory.Life.Placed
public import LeanTheory.Theory.Life.MergeChain
public import LeanTheory.Theory.Life.Rf0Images
public import LeanTheory.Theory.Life.StationChain
public import LeanTheory.Theory.Life.Gen.BodyIncData
public import LeanTheory.Theory.Life.Gen.BodyDecData
public import LeanTheory.Theory.Life.Gen.Dz2gData

/-!
# The placed pieces of the machine of a counter program (layout `LP`)

Report `R-31` lays out the Life machine of a counter program by closed formulas (`LayoutLP`). This
module lists **every periodic piece of the machine at time `0`**, for every program, each as
`Piece.place base vx vy phase` with one of the certified base pieces:

* the units (`unitSpecs`): the entry chain of `2P` OR gates (`orGateP`, copy `t` at
  `(-35 t, -64 t)`, phase `14 t mod 30`) and the body (`bodyDecPieces`, `bodyIncPieces`), translated
  to `((A_a + V_U) / 2, (V_U - A_a) / 2)`; merge units only for registers with an `inc`;
* the register modules (`moduleSpecs`): the register circuit (`dz2gPieces`), `RF_J`, the OR gate of
  the INC chain, the DEC chain of `2D` OR gates, the `D` dispatch stations on each answer line
  (`stNZ*`, `stZ*`, every `(72, ±72)`, `288` generations later) and the two line-end eaters
  (`eatNZEndP`, `eatZEndP`, certified here), translated to `(U_r / 2, -U_r / 2)`;
* the routes (`instrSpecs`, `mergeSpecs`): one reflector image (`rfP k`) at every corner of every
  link, placed by its corner point (`Corner`, `cornerSpec`) and in phase with its glider (the
  world-line arithmetic of `scripts/life_lp/p1_layout.py`: `WL`, `route`, `solveE`).

The positions are the formulas of `LayoutLP`; the phases follow the glider times exactly as
`p1_layout.py` computes them. `scripts/life_cert/layout_pieces_check.py` re-implements these
definitions and checks them against `p1_layout.layout` on the test programs of `R-31`.

The separation of the pieces (`machSpecs_sep`, `machPieces_sep`) is proved from the inequalities
of `LayoutLP` and the concrete boxes of the base pieces.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset LeanTheory.Computability

namespace LP

/-! ### Base pieces -/

/-- The OR gate (`blockedStream` at the origin, phase `0`) as a piece. -/
def orGateP : Piece := ⟨orGate, 0, 90, 0, 32, orGate_rest⟩

/-- The reflector image `k` (`0 … 7`, numbered as `net.RF_IMG`: `SW→NW`, `NW→NE`, `NE→SE`,
`SE→SW`, `SE→NE`, `NW→SW`, `NE→NW`, `SW→SE`) as a piece. -/
def rfP : ℕ → Piece
  | 0 => ⟨rf0SWNW.G, 0, 22, 2, 10, rf0SWNW_rest⟩
  | 1 => ⟨rf0NWNE.G, -10, -2, 0, 22, rf0NWNE_rest⟩
  | 2 => ⟨rf0NESE.G, -22, 0, -10, -2, rf0NESE_rest⟩
  | 3 => ⟨rf0SESW.G, 2, 10, -22, 0, rf0SESW_rest⟩
  | 4 => ⟨rf0SENE.G, -22, 0, 2, 10, rf0SENE_rest⟩
  | 5 => ⟨rf0NWSW.G, 0, 22, -10, -2, rf0NWSW_rest⟩
  | 6 => ⟨rf0NENW.G, 2, 10, 0, 22, rf0NENW_rest⟩
  | _ => ⟨rf0SWSE.G, -10, -2, -22, 0, rf0SWSE_rest⟩

/-- Piece 0 of the station on the line NZ (the OR gate). -/
def stNZ0P : Piece := ⟨stNZP0, 380, 412, 829, 919, stNZP0_rest⟩

/-- Piece 1 of the station on the line NZ (the reflector). -/
def stNZ1P : Piece := ⟨stNZP1, 431, 439, 891, 913, stNZP1_rest⟩

/-- Piece 2 of the station on the line NZ (the token eater). -/
def stNZ2P : Piece := ⟨stNZP2, 464, 467, 820, 823, stNZP2_rest⟩

/-- Piece 0 of the station on the line Z (the OR gate). -/
def stZ0P : Piece := ⟨stZP0, 889, 979, -325, -293, stZP0_rest⟩

/-- Piece 1 of the station on the line Z (the reflector). -/
def stZ1P : Piece := ⟨stZP1, 951, 973, -352, -344, stZP1_rest⟩

/-- Piece 2 of the station on the line Z (the token eater). -/
def stZ2P : Piece := ⟨stZP2, 880, 883, -380, -377, stZP2_rest⟩

/-- The line-end eater of the line NZ of a module with one caller (module frame). -/
def eatNZEndR : Finset Cell :=
  ofRows 563 954 [3, 5, 4, 12]

/-- **Certificate**: the line-end eater NZ is still (period `30`) in its box. -/
theorem eatNZEndR_rest : Reaction eatNZEndR eatNZEndR 30 (fun _ => Box 563 566 954 957) := by
  rw [eatNZEndR]
  life_reaction

/-- The line-end eater of the line Z of a module with one caller (module frame). -/
def eatZEndR : Finset Cell :=
  ofRows 1013 (-478) [8, 14, 1, 3]

/-- **Certificate**: the line-end eater Z is still (period `30`) in its box. -/
theorem eatZEndR_rest : Reaction eatZEndR eatZEndR 30 (fun _ => Box 1013 1016 (-478) (-475)) := by
  rw [eatZEndR]
  life_reaction

/-- The line-end eater NZ as a piece. -/
def eatNZEndP : Piece := ⟨eatNZEndR, 563, 566, 954, 957, eatNZEndR_rest⟩

/-- The line-end eater Z as a piece. -/
def eatZEndP : Piece := ⟨eatZEndR, 1013, 1016, -478, -475, eatZEndR_rest⟩

/-! ### Placed pieces as data -/

/-- The base pieces of the machine. -/
inductive Base where
  /-- The OR gate. -/
  | orGate
  /-- The reflector image `k`. -/
  | rf (k : ℕ)
  /-- Group `i` of the body of a `dec` unit. -/
  | bodyDec (i : ℕ)
  /-- Group `i` of the body of an `inc` unit. -/
  | bodyInc (i : ℕ)
  /-- Group `i` of the register circuit. -/
  | dz2g (i : ℕ)
  /-- Piece `i` of the station NZ. -/
  | stNZ (i : ℕ)
  /-- Piece `i` of the station Z. -/
  | stZ (i : ℕ)
  /-- The line-end eater NZ. -/
  | eatNZ
  /-- The line-end eater Z. -/
  | eatZ
  deriving Repr, DecidableEq

/-- The base piece. -/
def Base.piece : Base → Piece
  | .orGate => orGateP
  | .rf k => rfP k
  | .bodyDec i => bodyDecPieces.getD i orGateP
  | .bodyInc i => bodyIncPieces.getD i orGateP
  | .dz2g i => dz2gPieces.getD i orGateP
  | .stNZ i => [stNZ0P, stNZ1P, stNZ2P].getD i orGateP
  | .stZ i => [stZ0P, stZ1P, stZ2P].getD i orGateP
  | .eatNZ => eatNZEndP
  | .eatZ => eatZEndP

/-- A placed piece as data: the base piece, the translation and the phase at time `0`. -/
structure PSpec where
  /-- The base piece. -/
  base : Base
  /-- Translation in `x`. -/
  vx : ℤ
  /-- Translation in `y`. -/
  vy : ℤ
  /-- Phase at time `0`. -/
  ph : ℕ
  deriving Repr

/-- The placed piece of a spec. -/
def PSpec.piece (s : PSpec) : Piece := s.base.piece.place s.vx s.vy s.ph

/-! ### World lines and reflectors (`scripts/life_machine/net.py`) -/

/-- A glider world line `(d, lane, tau)`: direction `(dx, dy)`, `lane = dy x - dx y`, the glider is
at `x = dx q` at time `tau + 4 q`. -/
structure WL where
  /-- Direction in `x`. -/
  dx : ℤ
  /-- Direction in `y`. -/
  dy : ℤ
  /-- Lane. -/
  lane : ℤ
  /-- Reference time. -/
  tau : ℤ

/-- The world line after translation by `(p, q)` and delay by `s` (`reactions.shift_wl`). -/
def WL.shift (w : WL) (p q s : ℤ) : WL :=
  ⟨w.dx, w.dy, w.lane + w.dy * p - w.dx * q, w.tau + s - 4 * w.dx * p⟩

/-- The time at which the glider `w` passes the point `(u, v)` of its line (`tuv`). -/
def timeUV (w : WL) (u v : ℤ) : ℤ :=
  w.tau + (w.dx - w.dy) * u + (w.dx + w.dy) * v + 2 * w.dx * w.dy * w.lane

/-- Input world line of the reflector image `k` at the origin. -/
def rfIn : ℕ → WL
  | 0 => ⟨-1, 1, 19, 18⟩
  | 1 => ⟨-1, -1, 22, -68⟩
  | 2 => ⟨1, -1, 23, 26⟩
  | 3 => ⟨1, 1, 22, -60⟩
  | 4 => ⟨1, 1, -21, 26⟩
  | 5 => ⟨-1, -1, -21, 18⟩
  | 6 => ⟨1, -1, -20, -60⟩
  | _ => ⟨-1, 1, -24, -68⟩

/-- Output world line of the reflector image `k` at the origin. -/
def rfOut : ℕ → WL
  | 0 => ⟨-1, -1, -14, 13⟩
  | 1 => ⟨1, -1, -13, -37⟩
  | 2 => ⟨1, 1, -14, 21⟩
  | 3 => ⟨-1, 1, -17, -45⟩
  | 4 => ⟨1, -1, 16, 21⟩
  | 5 => ⟨-1, 1, 12, 13⟩
  | 6 => ⟨-1, -1, 15, -45⟩
  | _ => ⟨1, 1, 15, -37⟩

/-- The `u` of the corner point (meeting point of input and output line) of image `k` at the
origin. -/
def rfCU : ℕ → ℤ
  | 0 => 14 | 1 => -22 | 2 => -14 | 3 => 22 | 4 => -21 | 5 => 21 | 6 => -15 | _ => 15

/-- The `v` of the corner point of image `k` at the origin. -/
def rfCV : ℕ → ℤ
  | 0 => 19 | 1 => 13 | 2 => -23 | 3 => -17 | 4 => -16 | 5 => 12 | 6 => 20 | _ => -24

/-- The place of a route corner in the layout: on track `k` (`0 … 9`) of sub-band `b`, at the
hairpin (`h = true`) or at a column of a unit or a module (`h = false`); on the halt line of unit
`a`; at the input of entry copy `t` of unit `a`; at the port of channel number `idx` of the left
zone of module `r`; at corner `w` (`0 … 3`) of caller `j` in the right zone of module `r`. -/
inductive CTag where
  /-- Track `k` of sub-band `b`; hairpin side or column side. -/
  | band (b k : ℤ) (h : Bool)
  /-- The halt corner of unit `a`. -/
  | halt (a : ℤ)
  /-- The input corner of entry copy `t` of unit `a`. -/
  | slab (a t : ℤ)
  /-- The port corner of left-zone channel `idx` of module `r`. -/
  | left (r idx : ℤ)
  /-- Right-zone corner `w` of caller `j` of module `r`. -/
  | right (r j : ℤ) (w : ℕ)
  deriving DecidableEq

/-- A corner of a route: the reflector image `k` with its corner point at `(u, v)`, and a tag
naming the place of the corner in the layout (used by the separation proof only). -/
structure Corner where
  /-- The reflector image. -/
  k : ℕ
  /-- `u = x - y` of the corner point. -/
  u : ℤ
  /-- `v = x + y` of the corner point. -/
  v : ℤ
  /-- The place of the corner. -/
  tag : CTag

/-- `x`-translation of the reflector image `k` with its corner point at `(u, v)`. -/
def rfX (k : ℕ) (u v : ℤ) : ℤ := (u - rfCU k + v - rfCV k) / 2

/-- `y`-translation of the reflector image `k` with its corner point at `(u, v)`. -/
def rfY (k : ℕ) (u v : ℤ) : ℤ := (v - rfCV k - (u - rfCU k)) / 2

/-- The reflector at the corner `c`, in phase with the glider `g`, and the outgoing glider
(`net.reflect`). -/
def reflect (g : WL) (c : Corner) : PSpec × WL :=
  let p := rfX c.k c.u c.v
  let q := rfY c.k c.u c.v
  let s := g.tau - (rfIn c.k).tau + 4 * (rfIn c.k).dx * p
  (⟨.rf c.k, p, q, ((-s) % 30).toNat⟩, (rfOut c.k).shift p q s)

/-- A route: the reflectors at the corners, and the final glider. -/
def route (g : WL) : List Corner → List PSpec × WL
  | [] => ([], g)
  | c :: cs =>
    let r := reflect g c
    let t := route r.2 cs
    (r.1 :: t.1, t.2)

/-- The window rule applied to a route: route with `e = 0`, residue `r0` of the arrival relative
to the window `win`, then `e = winE r0 (ρ* r0)` (`p1_layout.solve_window`). -/
def solveE (g : WL) (mk : ℤ → List Corner) (win : WL) : ℤ :=
  let r0 := ((route g (mk 0)).2.tau - win.tau) % 30
  winE r0 (rhoStar r0)

/-- The slot of a glider in a window family (`p1_layout.slot`). -/
def slot (g win : WL) : ℤ := (g.tau - win.tau) / 30

/-! ### Units -/

/-- The kind of a unit. -/
inductive UKind where
  /-- A `decJz` instruction. -/
  | dec
  /-- An `inc` instruction. -/
  | inc
  /-- The `halt` instruction. -/
  | halt
  /-- A merge unit (beyond the instructions). -/
  | merge

/-- The kind of unit `a` (units `a ≥ N` are the merge units). -/
def unitKind (p : Program) (a : ℕ) : UKind :=
  match p[a]? with
  | some (.inc _) => .inc
  | some (.decJz _ _) => .dec
  | some .halt => .halt
  | none => .merge

/-- The first input column `C0` of a unit kind. -/
def UKind.C0 : UKind → ℤ
  | .dec => C0dec
  | .inc => C0inc
  | _ => C0halt

/-- `C0` of unit `a`. -/
def unitC0 (p : Program) (a : ℕ) : ℤ := (unitKind p a).C0

/-- Whether an instruction is an `inc` on register `r`. -/
def isIncOn (r : ℕ) : Instr → Bool
  | .inc r' => r' == r
  | _ => false

/-- Whether register `r` has an `inc` caller (only then its merge unit and link exist). -/
def mergeUsed (p : Program) (r : ℕ) : Bool := p.any (isIncOn r)

/-- Whether unit `a` exists: every instruction, and the merge units of registers with `inc`. -/
def unitUsed (p : Program) (a : ℕ) : Bool := a < p.length || mergeUsed p (a - p.length)

/-- `x`-translation of unit `a`: `(A_a + V_U) / 2`. -/
def unitDX (p : Program) (a : ℕ) : ℤ := (A p a + VU p) / 2

/-- `y`-translation of unit `a`: `(V_U - A_a) / 2`. -/
def unitDY (p : Program) (a : ℕ) : ℤ := (VU p - A p a) / 2

/-- The entry chain of `n` OR gates (copy `t` at `(-35 t, -64 t)`, `254 t` generations earlier),
translated by `(dx, dy)`. -/
def chainSpecs (n : ℕ) (dx dy : ℤ) : List PSpec :=
  (List.range n).map fun t : ℕ =>
    ⟨.orGate, dx - 35 * (t : ℤ), dy - 64 * (t : ℤ), 14 * t % 30⟩

/-- A list of base pieces translated by `(dx, dy)` at phase `0`. -/
def groupSpecs (L : List Base) (dx dy : ℤ) : List PSpec :=
  L.map fun g => ⟨g, dx, dy, 0⟩

/-- The pieces of unit `a`: entry chain of `2P` copies and the body of its kind. -/
def unitSpecs (p : Program) (a : ℕ) : List PSpec :=
  chainSpecs (2 * numPreds p) (unitDX p a) (unitDY p a) ++
    match unitKind p a with
    | .dec => groupSpecs ((List.range 8).map Base.bodyDec) (unitDX p a) (unitDY p a)
    | .inc => groupSpecs ((List.range 3).map Base.bodyInc) (unitDX p a) (unitDY p a)
    | _ => []

/-- The world line `w` of a unit template, in unit `a`. -/
def unitWL (p : Program) (a : ℕ) (w : WL) : WL := w.shift (unitDX p a) (unitDY p a) 0

/-- Output `L` of the `dec` template (`SE`, column `-155`). -/
def decLWL : WL := ⟨1, 1, -155, 2665⟩

/-- Output `R` of the `dec` template (`SE`, column `127`). -/
def decRWL : WL := ⟨1, 1, 127, 1221⟩

/-- Output `D'` of the `dec` template (`SE`, column `188`, after the jog). -/
def decDWL : WL := ⟨1, 1, 188, 787⟩

/-- Output `R` of the `inc` template (`SE`, column `157`). -/
def incRWL : WL := ⟨1, 1, 157, 1029⟩

/-- Output `D` of the `inc` template (`SE`, column `68`). -/
def incDWL : WL := ⟨1, 1, 68, 605⟩

/-- Output `D` of the `halt` / `merge` template (`SE`, column `14`), input at copy `0`. -/
def haltDWL : WL := ⟨1, 1, 14, 629⟩

/-- Output `D` of the `merge` template for the input at copy `t` (residue 5, slot 20). -/
def mergeOutWL (t : ℤ) : WL := ⟨1, 1, 14, 629 + 254 * t + 16 * t % 30⟩

/-- The side input line of entry copy `t` (window base). -/
def sideWL (t : ℤ) : WL := ⟨1, -1, -76 + 99 * t, 1 + 140 * t + 16 * t % 30⟩

/-! ### Modules -/

/-- `x`-translation of module `r`: `U_r / 2`. -/
def modDX (p : Program) (r : ℕ) : ℤ := U p r / 2

/-- `y`-translation of module `r`: `-U_r / 2`. -/
def modDY (p : Program) (r : ℕ) : ℤ := -(U p r / 2)

/-- The DEC chain of `n` OR gates (copy number `m` from the downstream end at
`(-1700 - 35 m, -1727 - 64 m)`), translated by `(dx, dy)`. -/
def decChainSpecs (n : ℕ) (dx dy : ℤ) : List PSpec :=
  (List.range n).map fun m : ℕ =>
    ⟨.orGate, dx - 1700 - 35 * (m : ℤ), dy - 1727 - 64 * (m : ℤ), (15 + 14 * m) % 30⟩

/-- The `n` stations on the answer lines (station `j` moved by `(72 j, ±72 j)`, `288 j`
generations later), translated by `(dx, dy)`. -/
def stationSpecs (n : ℕ) (dx dy : ℤ) : List PSpec :=
  (List.range n).flatMap fun j : ℕ =>
    groupSpecs [.stNZ 0, .stNZ 1, .stNZ 2] (dx + 72 * (j : ℤ)) (dy + 72 * (j : ℤ)) |>.map
      (fun s => { s with ph := 12 * j % 30 })

/-- The `n` stations on the line Z, translated by `(dx, dy)`. -/
def stationZSpecs (n : ℕ) (dx dy : ℤ) : List PSpec :=
  (List.range n).flatMap fun j : ℕ =>
    groupSpecs [.stZ 0, .stZ 1, .stZ 2] (dx + 72 * (j : ℤ)) (dy - 72 * (j : ℤ)) |>.map
      (fun s => { s with ph := 12 * j % 30 })

/-- The pieces of module `r`: register circuit, `RF_J`, INC OR gate, DEC chain of `2D` copies,
`D` stations per answer line, two line-end eaters. -/
def moduleSpecs (p : Program) (r : ℕ) : List PSpec :=
  groupSpecs ((List.range 28).map Base.dz2g) (modDX p r) (modDY p r) ++
    [⟨.rf 4, modDX p r - 850, modDY p r - 1044, 25⟩,
      ⟨.orGate, modDX p r - 1132, modDY p r - 1291, 16⟩] ++
    decChainSpecs (2 * numCallers p) (modDX p r) (modDY p r) ++
    stationSpecs (numCallers p) (modDX p r) (modDY p r) ++
    stationZSpecs (numCallers p) (modDX p r) (modDY p r) ++
    [⟨.eatNZ, modDX p r + 72 * (D p - 1), modDY p r + 72 * (D p - 1), 0⟩,
      ⟨.eatZ, modDX p r + 72 * (D p - 1), modDY p r - 72 * (D p - 1), 0⟩]

/-- A world line of the module, in module `r`. -/
def modWL (p : Program) (r : ℕ) (w : WL) : WL := w.shift (modDX p r) (modDY p r) 0

/-- The window of DEC copy `t` of module `r`. -/
def decWin (p : Program) (r : ℕ) (t : ℤ) : WL :=
  let m := 2 * D p - 1 - t
  modWL p r ⟨1, -1, 3351 + 99 * m, 6801 + 140 * m + (15 + 16 * m) % 30⟩

/-- The control `C'` emitted by the DEC chain for the input at copy `t` (window slot 20). -/
def cprimeWL (p : Program) (r : ℕ) (t : ℤ) : WL :=
  let m := 2 * D p - 1 - t
  modWL p r ⟨1, 1, 41, 7429 + 254 * m + (15 + 16 * m) % 30⟩

/-- The window of the INC copy (module frame). -/
def incWin : WL := ⟨1, -1, 2347, 4543⟩

/-- The reference control `C'` of the module's world lines. -/
def cp0WL : WL := ⟨1, 1, 41, 4444⟩

/-- The dispatched NZ answer of caller `j` (module frame, timed for `cp0WL`). -/
def nzAnsWL (j : ℤ) : WL := ⟨-1, 1, 1325 + 144 * j, 12547 + 576 * j⟩

/-- The dispatched Z answer of caller `j` (module frame, timed for `cp0WL`). -/
def zAnsWL (j : ℤ) : WL := ⟨1, 1, 1301 + 144 * j, 9025⟩

/-! ### Links -/

/-- The input column of entry copy `t` of unit `a`. -/
def destU (p : Program) (a : ℕ) (t : ℤ) : ℤ := A p a + inCol (unitC0 p a) t

/-- The side line of entry copy `t` (any unit). -/
def destV (p : Program) (t : ℤ) : ℤ := VU p + sideV t

/-- The window of entry copy `t` of unit `a`. -/
def destWin (p : Program) (a : ℕ) (t : ℤ) : WL := unitWL p a (sideWL t)

/-- The band corners of a link of slot `s` in sub-band `b` from the column `c` (going `SW` on the
`OUT` track from a glider of direction `k0`), with hairpin `H`; then the corner `(cd, BACK)`
turning with image `k4`. -/
def bandCorners (p : Program) (b s c H cd : ℤ) (k0 k4 : ℕ) : List Corner :=
  [⟨k0, c, trackOut p b s c, .band b s false⟩, ⟨7, H, trackOut p b s c, .band b s true⟩,
    ⟨4, H, trackBack p b s c, .band b (9 - s) true⟩,
    ⟨k4, cd, trackBack p b s c, .band b (9 - s) false⟩]

/-- A link from the column `c` (first turn with image `k0`) up to entry copy `t` of unit `a`. -/
def upCornersK (k0 : ℕ) (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) : List Corner :=
  bandCorners p b s c H (destU p a t) k0 6 ++ [⟨1, destU p a t, destV p t, .slab a t⟩]

/-- A link from a unit column `c` up to entry copy `t` of unit `a`. -/
def upCorners (p : Program) (b s c H : ℤ) (a : ℕ) (t : ℤ) : List Corner :=
  upCornersK 3 p b s c H a t

/-- A link from a unit column `c` down to the port line `vp` of left-zone channel `idx` of
module `r` (column `cd`). -/
def downCorners (p : Program) (b s c H cd vp : ℤ) (r : ℕ) (idx : ℤ) : List Corner :=
  bandCorners p b s c H cd 3 2 ++ [⟨4, cd, vp, .left r idx⟩]

/-- The KZ link (slot `2`) from the column `c` down to the Z token of caller `j` of module `r`. -/
def ztokCorners (p : Program) (b c H : ℤ) (r : ℕ) (j : ℤ) : List Corner :=
  bandCorners p b 2 c H (U p r + zTokChan p j) 3 2 ++
    [⟨3, U p r + zTokChan p j, zTokDepth p j, .right r j 2⟩,
      ⟨0, U p r + zTokStation j, zTokDepth p j, .right r j 3⟩]

/-- The NZ answer (slot `3`) of caller `j` of module `r` to entry copy `t` of unit `a`. -/
def nzAnsCorners (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) : List Corner :=
  ⟨0, U p r + nzAnsChan p j, nzAnsPortV j, .left r (2 * D p + 2 + 2 * j)⟩ ::
    upCornersK 5 p b 3 (U p r + nzAnsChan p j) H a t

/-- The Z answer (slot `4`) of caller `j` of module `r` to entry copy `t` of unit `a`. -/
def zAnsCorners (p : Program) (b : ℤ) (r : ℕ) (j H : ℤ) (a : ℕ) (t : ℤ) : List Corner :=
  ⟨4, U p r + zAnsStation j, zAnsDepth p j, .right r j 0⟩ ::
    ⟨6, U p r + zAnsChan p j, zAnsDepth p j, .right r j 1⟩ ::
    upCornersK 5 p b 4 (U p r + zAnsChan p j) H a t

/-- The halt link of unit `a`: one corner, on the top track. -/
def haltCorners (p : Program) (a : ℕ) : List Corner :=
  [⟨3, A p a + haltD, trackOut p 0 0 (A p a + haltD), .halt a⟩]

/-- The merge link of register `r` (merge unit `N + r` to the INC port), residue correction
`e`. -/
def mergeCorners (p : Program) (r : ℕ) (e : ℤ) : List Corner :=
  downCorners p (mergeBand p r) 0 (A p (p.length + r) + haltD)
    (hairReg p 0 e (A p (p.length + r) + haltD)) (U p r + incChan p) incPortV r (2 * D p)

/-- The residue correction of the merge link of register `r`. -/
def mergeE (p : Program) (r : ℕ) : ℤ :=
  solveE (unitWL p (p.length + r) haltDWL) (mergeCorners p r) (modWL p r incWin)

/-- The number of predecessors that instructions `0 … i - 1` give to unit `a`. -/
def predBefore (p : Program) (a i : ℕ) : ℕ :=
  ((List.range i).map fun i' => (p[i']?.map (predContrib p.length a i')).getD 0).sum

/-- The predecessor number of a link into unit `a` from instruction `i`: the start (unit `0`),
the links of the earlier instructions, and `off` (`1` for the second link of `i` into `a`). -/
def predIdx (p : Program) (a i off : ℕ) : ℤ :=
  ((if a = 0 then 1 else 0) + predBefore p a i + off : ℕ)

/-- The caller number of `decJz` instruction `i` on register `r`: the number of earlier `decJz`
on `r`. -/
def callerIdx (p : Program) (r i : ℕ) : ℕ := ((p.take i).filter (isDecOn r)).length

/-- The routes of an `inc r` instruction `i`: the continue (slot `0`, to unit `i + 1`, far hairpin
`G` for the minimum delay after the INC control) and the INC link (slot `1`, to merge unit
`N + r`). -/
def incSpecs (p : Program) (i r : ℕ) : List (WL × List Corner) :=
  let b := instrBand i
  let a := p.length + r
  let cl := A p i + incR
  let tl := copyIdx C0halt (predIdx p a i (if i + 1 = a then 1 else 0)) cl
  let mkl := fun e => upCorners p b 1 cl (hairReg p 1 e cl) a tl
  let gR := unitWL p i incRWL
  let el := solveE gR mkl (destWin p a tl)
  let gl := (route gR (mkl el)).2
  let gm := (mergeOutWL tl).shift (unitDX p a) (unitDY p a) (30 * (slot gl (destWin p a tl) - 20))
  let g2 := (route gm (mergeCorners p r (mergeE p r))).2
  let tinc := timeUV g2 (U p r - 1087 + 1260) (U p r - 1087 - 1260)
  let cc := A p i + incD
  let tc := copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) cc
  let mkc := fun G e => upCorners p b 0 cc (hairCont p G e cc) (i + 1) tc
  let gD := unitWL p i incDWL
  let ec0 := solveE gD (mkc 0) (destWin p (i + 1) tc)
  let t0 := timeUV (route gD ((mkc 0 ec0).take 3)).2 (destU p (i + 1) tc) (trackBack p b 0 cc)
  let G := 30 * ceil120 (max 0 (tinc + 500 - t0))
  let ec := solveE gD (mkc G) (destWin p (i + 1) tc)
  [(gD, mkc G ec), (gR, mkl el)]

/-- The routes of a `decJz r z` instruction `i` (caller `j`, `q = D - 1 - j`): the tokens KNZ
(slot `0`) and KZ (slot `2`) and the control `C` (slot `1`) to module `r`, timed by the closed
formulas of `R-31` §4.2; the NZ answer (slot `3`) to unit `i + 1` and the Z answer (slot `4`) to
unit `z`, timed from the control `C'` of the DEC chain. -/
def decSpecs (p : Program) (i r z : ℕ) : List (WL × List Corner) :=
  let b := instrBand i
  let j : ℤ := callerIdx p r i
  let q := qOf p j
  let cN := A p i + decL
  let cC := A p i + decR
  let cZ := A p i + decD
  let cornN := downCorners p b 0 cN (hairKNZ p q cC cN) (U p r + nzTokChan p j) (nzTokPortV j) r
    (2 * D p + 1 + 2 * j)
  let cornC := downCorners p b 1 cC (hairC p q cC) (U p r + decChan p (2 * j)) (decPortV p (2 * j))
    r (2 * j)
  let cornZ := ztokCorners p b cZ (hairKZ p q cZ) r j
  let gC := (route (unitWL p i decRWL) cornC).2
  let cp := (cprimeWL p r (2 * j)).shift 0 0 (30 * (slot gC (decWin p r (2 * j)) - 20))
  let sh := cp.tau - (modWL p r cp0WL).tau
  let gN := (modWL p r (nzAnsWL j)).shift 0 0 sh
  let cAN := U p r + nzAnsChan p j
  let tN := copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) cAN
  let mkN := fun e => nzAnsCorners p b r j (hairReg p 3 e cAN) (i + 1) tN
  let eA := solveE gN mkN (destWin p (i + 1) tN)
  let gZ := (modWL p r (zAnsWL j)).shift 0 0 sh
  let cAZ := U p r + zAnsChan p j
  let tZ := copyIdx (unitC0 p z) (predIdx p z i (if i + 1 = z then 1 else 0)) cAZ
  let mkZ := fun e => zAnsCorners p b r j (hairReg p 4 e cAZ) z tZ
  let eB := solveE gZ mkZ (destWin p z tZ)
  [(unitWL p i decLWL, cornN), (unitWL p i decRWL, cornC), (unitWL p i decDWL, cornZ),
    (gN, mkN eA), (gZ, mkZ eB)]

/-- The routes of instruction `i`. -/
def instrSpecs (p : Program) (i : ℕ) : List (WL × List Corner) :=
  match p[i]? with
  | some .halt => [(unitWL p i haltDWL, haltCorners p i)]
  | some (.inc r) => incSpecs p i r
  | some (.decJz r z) => decSpecs p i r z
  | none => []

/-- The merge route of register `r`. -/
def mergeSpecs (p : Program) (r : ℕ) : List (WL × List Corner) :=
  [(unitWL p (p.length + r) haltDWL, mergeCorners p r (mergeE p r))]

/-- The reflectors of a list of routes. -/
def routeSpecs (l : List (WL × List Corner)) : List PSpec := l.flatMap fun x => (route x.1 x.2).1

/-! ### The machine -/

/-- The pieces of all units. -/
def unitsPart (p : Program) : List PSpec :=
  ((List.range (p.length + numRegs p)).filter (unitUsed p)).flatMap (unitSpecs p)

/-- The pieces of all modules. -/
def modulesPart (p : Program) : List PSpec := (List.range (numRegs p)).flatMap (moduleSpecs p)

/-- The reflectors of all routes. -/
def linksPart (p : Program) : List PSpec :=
  (List.range p.length).flatMap (fun i => routeSpecs (instrSpecs p i)) ++
    ((List.range (numRegs p)).filter (mergeUsed p)).flatMap fun r => routeSpecs (mergeSpecs p r)

/-- **Every periodic piece of the machine of `p` at time `0`**, as data. -/
def machSpecs (p : Program) : List PSpec := unitsPart p ++ modulesPart p ++ linksPart p

/-- **Every periodic piece of the machine of `p` at time `0`.** -/
def machPieces (p : Program) : List Piece := (machSpecs p).map PSpec.piece

/-! ### Separation: boxes -/

/-- An axis-parallel box `[a, b] × [lo, hi]` as data. -/
structure BoxT where
  /-- Left edge. -/
  a : ℤ
  /-- Right edge. -/
  b : ℤ
  /-- Top edge. -/
  lo : ℤ
  /-- Bottom edge. -/
  hi : ℤ

/-- The box of a placed spec. -/
def PSpec.bx (s : PSpec) : BoxT :=
  ⟨s.base.piece.a + s.vx, s.base.piece.b + s.vx, s.base.piece.lo + s.vy, s.base.piece.hi + s.vy⟩

/-- Two boxes are far apart: more than `2` apart in `x` or in `y`. -/
def BoxT.Far (B C : BoxT) : Prop :=
  B.b + 2 < C.a ∨ C.b + 2 < B.a ∨ B.hi + 2 < C.lo ∨ C.hi + 2 < B.lo

/-- The `uv`-hull of a box (`u = x - y`, `v = x + y`) lies in `[u1, u2] × [v1, v2]`. -/
def BoxT.InUV (B : BoxT) (u1 u2 v1 v2 : ℤ) : Prop :=
  u1 ≤ B.a - B.hi ∧ B.b - B.lo ≤ u2 ∧ v1 ≤ B.a + B.lo ∧ B.b + B.hi ≤ v2

/-- Boxes with `uv`-hulls `6` apart in `u` or in `v` are far apart. -/
theorem BoxT.far_of_uv {B C : BoxT} {u1 u2 v1 v2 u1' u2' v1' v2' : ℤ}
    (hB : B.InUV u1 u2 v1 v2) (hC : C.InUV u1' u2' v1' v2')
    (h : u2 + 6 ≤ u1' ∨ u2' + 6 ≤ u1 ∨ v2 + 6 ≤ v1' ∨ v2' + 6 ≤ v1) : B.Far C := by
  unfold BoxT.InUV at hB hC; unfold BoxT.Far; omega

/-- Far boxes give separated pieces. -/
theorem PSpec.sep_of_far {s t : PSpec} (h : s.bx.Far t.bx) : Piece.Sep s.piece t.piece := by
  refine Box.farApart (r := 2) ?_
  simp only [PSpec.bx, BoxT.Far] at h
  simp only [PSpec.piece, Piece.place]
  push_cast; omega

/-- Translation preserves separation. -/
theorem Piece.sep_place {g h : Piece} (hgh : Piece.Sep g h) (dx dy : ℤ) (p p' : ℕ) :
    Piece.Sep (g.place dx dy p) (h.place dx dy p') := by
  intro x hx y hy hn
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  refine hgh (x.1 - dx, x.2 - dy) ?_ (y.1 - dx, y.2 - dy) ?_ ?_
  · simp only [Piece.place] at x1 x2 x3 x4
    exact ⟨by omega, by omega, by omega, by omega⟩
  · simp only [Piece.place] at y1 y2 y3 y4
    exact ⟨by omega, by omega, by omega, by omega⟩
  · obtain ⟨n1, n2, n3, n4⟩ := hn
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- Pairwise separation of a translated group of base pieces. -/
theorem groupSpecs_sep {L : List Base} (hL : (L.map Base.piece).Pairwise Piece.Sep) (dx dy : ℤ) :
    (groupSpecs L dx dy).Pairwise fun s t => Piece.Sep s.piece t.piece := by
  unfold groupSpecs
  rw [List.pairwise_map]
  rw [List.pairwise_map] at hL
  exact hL.imp fun h => Piece.sep_place h dx dy 0 0

/-- A list ordered by `<` and a family of lists: pairwise relations of the flattened list. -/
theorem pairwise_flatMap_lt {α : Type*} {R : α → α → Prop} {f : ℕ → List α} {l : List ℕ}
    (hl : l.Pairwise (· < ·)) (h1 : ∀ a ∈ l, (f a).Pairwise R)
    (h2 : ∀ a ∈ l, ∀ a' ∈ l, a < a' → ∀ x ∈ f a, ∀ y ∈ f a', R x y) :
    (l.flatMap f).Pairwise R :=
  List.pairwise_flatMap.2 ⟨h1, hl.imp_of_mem fun ha hb hab => h2 _ ha _ hb hab⟩

/-- A filtered range is ordered by `<`. -/
theorem pairwise_lt_range_filter (n : ℕ) (q : ℕ → Bool) :
    ((List.range n).filter q).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter q

/-! ### Separation: units -/

/-- Lower bound of `u` (unit frame) of the pieces of a unit of kind `k`. -/
def UKind.uLo : UKind → ℤ
  | .dec => -180
  | .inc => -36
  | _ => -32

/-- `A_a` is even. -/
theorem A_even (p : Program) (a : ℤ) : A p a % 2 = 0 := by have := A_mod p a; omega

/-- `V_U` is even. -/
theorem VU_even (p : Program) : VU p % 2 = 0 := by have := VT_mod p; unfold VU; omega

/-- `U_r` is even. -/
theorem U_even (p : Program) (r : ℤ) : U p r % 2 = 0 := by have := U_mod p r; omega

/-- The unit translation in `uv`: `dx - dy = A_a`, `dx + dy = V_U`. -/
theorem unitD_uv (p : Program) (a : ℕ) :
    unitDX p a - unitDY p a = A p a ∧ unitDX p a + unitDY p a = VU p := by
  have := A_even p a; have := VU_even p
  unfold unitDX unitDY; omega

/-- The module translation in `uv`: `dx - dy = U_r`, `dx + dy = 0`. -/
theorem modD_uv (p : Program) (r : ℕ) : modDX p r - modDY p r = U p r ∧ modDX p r + modDY p r = 0 := by
  have := U_even p r
  unfold modDX modDY; omega

/-- The groups of the `dec` body, in the unit frame: `u ∈ [-180, 212]`, `v ∈ [213, 1527]`,
`y ≥ 61`. -/
theorem bodyDec_uv (i : ℕ) (hi : i < 8) :
    -180 ≤ (Base.bodyDec i).piece.a - (Base.bodyDec i).piece.hi ∧
      (Base.bodyDec i).piece.b - (Base.bodyDec i).piece.lo ≤ 212 ∧
      213 ≤ (Base.bodyDec i).piece.a + (Base.bodyDec i).piece.lo ∧
      (Base.bodyDec i).piece.b + (Base.bodyDec i).piece.hi ≤ 1527 ∧
      61 ≤ (Base.bodyDec i).piece.lo := by
  interval_cases i <;>
    simp only [Base.piece, bodyDecPieces, bodyDecG0, bodyDecG1, bodyDecG2, bodyDecG3, bodyDecG4,
      bodyDecG5, bodyDecG6, bodyDecG7, List.getD_cons_zero, List.getD_cons_succ] <;> norm_num

/-- The groups of the `inc` body, in the unit frame: `u ∈ [-36, 181]`, `v ∈ [214, 433]`,
`y ≥ 61`. -/
theorem bodyInc_uv (i : ℕ) (hi : i < 3) :
    -36 ≤ (Base.bodyInc i).piece.a - (Base.bodyInc i).piece.hi ∧
      (Base.bodyInc i).piece.b - (Base.bodyInc i).piece.lo ≤ 181 ∧
      214 ≤ (Base.bodyInc i).piece.a + (Base.bodyInc i).piece.lo ∧
      (Base.bodyInc i).piece.b + (Base.bodyInc i).piece.hi ≤ 433 ∧
      61 ≤ (Base.bodyInc i).piece.lo := by
  interval_cases i <;>
    simp only [Base.piece, bodyIncPieces, bodyIncG0, bodyIncG1, bodyIncG2, List.getD_cons_zero,
      List.getD_cons_succ] <;> norm_num

/-- Membership in a translated group. -/
theorem mem_groupSpecs {L : List Base} {dx dy : ℤ} {s : PSpec} (h : s ∈ groupSpecs L dx dy) :
    ∃ g ∈ L, s = ⟨g, dx, dy, 0⟩ := by
  unfold groupSpecs at h
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h
  exact ⟨g, hg, rfl⟩

/-- Membership in a chain. -/
theorem mem_chainSpecs {n : ℕ} {dx dy : ℤ} {s : PSpec} (h : s ∈ chainSpecs n dx dy) :
    ∃ t < n, s = ⟨.orGate, dx - 35 * (t : ℤ), dy - 64 * (t : ℤ), 14 * t % 30⟩ := by
  unfold chainSpecs at h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact ⟨t, List.mem_range.1 ht, rfl⟩

/-- The box of a chain copy. -/
theorem chain_bx (dx dy : ℤ) (t ph : ℕ) :
    (PSpec.mk .orGate (dx - 35 * (t : ℤ)) (dy - 64 * (t : ℤ)) ph).bx =
      ⟨dx - 35 * t, dx - 35 * t + 90, dy - 64 * t, dy - 64 * t + 32⟩ := by
  simp only [PSpec.bx, Base.piece, orGateP]; congr 1 <;> ring

/-- **Region of a unit**: every piece of unit `a` lies in `u ∈ [A_a + uLo, A_a + 58 P + 212]`,
`v ∈ [V_U - 198 P, V_U + 1527]`. -/
theorem unitSpecs_uv (p : Program) (a : ℕ) {s : PSpec} (hs : s ∈ unitSpecs p a) :
    s.bx.InUV (A p a + (unitKind p a).uLo) (A p a + 58 * P p + 212) (VU p - 198 * P p)
      (VU p + 1527) := by
  have hd := unitD_uv p a
  have hP := one_le_P p
  unfold unitSpecs at hs
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨t, ht, rfl⟩ := mem_chainSpecs hs
    rw [chain_bx]
    have ht' : (t : ℤ) < 2 * P p := by unfold P; omega
    have hk : (unitKind p a).uLo ≤ -32 := by cases unitKind p a <;> simp [UKind.uLo]
    unfold BoxT.InUV; simp only; omega
  · cases hk : unitKind p a <;> rw [hk] at hs <;> simp only [List.not_mem_nil] at hs
    · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      have := bodyDec_uv i (List.mem_range.1 hi)
      simp only [BoxT.InUV, PSpec.bx, UKind.uLo]; omega
    · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      have := bodyInc_uv i (List.mem_range.1 hi)
      simp only [BoxT.InUV, PSpec.bx, UKind.uLo]; omega

/-- The copies of a chain are pairwise separated (`64` apart in `y`). -/
theorem chainSpecs_sep (n : ℕ) (dx dy : ℤ) :
    (chainSpecs n dx dy).Pairwise fun s t => Piece.Sep s.piece t.piece := by
  unfold chainSpecs
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {t t'} h => PSpec.sep_of_far ?_
  rw [chain_bx, chain_bx]
  unfold BoxT.Far; simp only; omega

/-- The groups of the `dec` body are the generated `bodyDecPieces`. -/
theorem bodyDec_map : (List.range 8).map (fun i => (Base.bodyDec i).piece) = bodyDecPieces := rfl

/-- The groups of the `inc` body are the generated `bodyIncPieces`. -/
theorem bodyInc_map : (List.range 3).map (fun i => (Base.bodyInc i).piece) = bodyIncPieces := rfl

/-- **The pieces of a unit are pairwise separated.** -/
theorem unitSpecs_sep (p : Program) (a : ℕ) :
    (unitSpecs p a).Pairwise fun s t => Piece.Sep s.piece t.piece := by
  unfold unitSpecs
  refine List.pairwise_append.2 ⟨chainSpecs_sep _ _ _, ?_, ?_⟩
  · cases unitKind p a
    · exact groupSpecs_sep (by rw [List.map_map]; exact bodyDec_map ▸ bodyDecPieces_sep) _ _
    · exact groupSpecs_sep (by rw [List.map_map]; exact bodyInc_map ▸ bodyIncPieces_sep) _ _
    · exact List.Pairwise.nil
    · exact List.Pairwise.nil
  · intro s hs t ht
    obtain ⟨c, hc, rfl⟩ := mem_chainSpecs hs
    refine PSpec.sep_of_far ?_
    rw [chain_bx]
    cases hk : unitKind p a <;> rw [hk] at ht <;> simp only [List.not_mem_nil] at ht
    · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      have := bodyDec_uv i (List.mem_range.1 hi)
      simp only [BoxT.Far, PSpec.bx]; omega
    · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      have := bodyInc_uv i (List.mem_range.1 hi)
      simp only [BoxT.Far, PSpec.bx]; omega

/-- **Units `a < a'` are separated** (their regions are `≥ 6` apart in `u`). -/
theorem unitSpecs_cross (p : Program) {a a' : ℕ} (h : a < a') {s t : PSpec}
    (hs : s ∈ unitSpecs p a) (ht : t ∈ unitSpecs p a') : Piece.Sep s.piece t.piece := by
  have h1 := unitSpecs_uv p a hs
  have h2 := unitSpecs_uv p a' ht
  have hA := A_add_le p (a := a) (a' := a') (by exact_mod_cast h)
  have hk : -180 ≤ (unitKind p a').uLo := by cases unitKind p a' <;> simp [UKind.uLo]
  have hP := one_le_P p
  refine PSpec.sep_of_far (BoxT.far_of_uv h1 h2 (Or.inl ?_))
  unfold PU at hA; omega

/-- **The pieces of all units are pairwise separated.** -/
theorem unitsPart_sep (p : Program) :
    (unitsPart p).Pairwise fun s t => Piece.Sep s.piece t.piece :=
  pairwise_flatMap_lt (pairwise_lt_range_filter _ _) (fun a _ => unitSpecs_sep p a)
    fun _ _ _ _ h _ hs _ ht => unitSpecs_cross p h hs ht

/-! ### Separation: modules -/

/-- The groups of the register circuit (module frame): `u ∈ [-738, 798]`, `v ∈ [-2324, 670]`,
and far from `RF_J` and from the INC OR gate. -/
theorem dz2g_facts (i : ℕ) (hi : i < 28) :
    -738 ≤ (Base.dz2g i).piece.a - (Base.dz2g i).piece.hi ∧
      (Base.dz2g i).piece.b - (Base.dz2g i).piece.lo ≤ 798 ∧
      -2324 ≤ (Base.dz2g i).piece.a + (Base.dz2g i).piece.lo ∧
      (Base.dz2g i).piece.b + (Base.dz2g i).piece.hi ≤ 670 ∧
      BoxT.Far ⟨(Base.dz2g i).piece.a, (Base.dz2g i).piece.b, (Base.dz2g i).piece.lo,
        (Base.dz2g i).piece.hi⟩ ⟨-872, -850, -1042, -1034⟩ ∧
      BoxT.Far ⟨(Base.dz2g i).piece.a, (Base.dz2g i).piece.b, (Base.dz2g i).piece.lo,
        (Base.dz2g i).piece.hi⟩ ⟨-1132, -1042, -1291, -1259⟩ := by
  interval_cases i <;>
    simp only [Base.piece, dz2gPieces, dz2gG0, dz2gG1, dz2gG2, dz2gG3, dz2gG4, dz2gG5, dz2gG6, dz2gG7, dz2gG8, dz2gG9, dz2gG10, dz2gG11, dz2gG12, dz2gG13, dz2gG14, dz2gG15, dz2gG16, dz2gG17, dz2gG18, dz2gG19, dz2gG20, dz2gG21, dz2gG22, dz2gG23, dz2gG24, dz2gG25, dz2gG26, dz2gG27, List.getD_cons_zero, List.getD_cons_succ,
      BoxT.Far] <;> norm_num

/-- The groups of the register circuit are the generated `dz2gPieces`. -/
theorem dz2g_map : (List.range 28).map (fun i => (Base.dz2g i).piece) = dz2gPieces := rfl

/-- The three pieces of the station NZ. -/
theorem stNZ_cases (i : ℕ) (hi : i < 3) :
    ((Base.stNZ i).piece.a = 380 ∧ (Base.stNZ i).piece.b = 412 ∧ (Base.stNZ i).piece.lo = 829 ∧
        (Base.stNZ i).piece.hi = 919) ∨
      ((Base.stNZ i).piece.a = 431 ∧ (Base.stNZ i).piece.b = 439 ∧
        (Base.stNZ i).piece.lo = 891 ∧ (Base.stNZ i).piece.hi = 913) ∨
      ((Base.stNZ i).piece.a = 464 ∧ (Base.stNZ i).piece.b = 467 ∧
        (Base.stNZ i).piece.lo = 820 ∧ (Base.stNZ i).piece.hi = 823) := by
  interval_cases i <;> simp [Base.piece, stNZ0P, stNZ1P, stNZ2P]

/-- The three pieces of the station Z. -/
theorem stZ_cases (i : ℕ) (hi : i < 3) :
    ((Base.stZ i).piece.a = 889 ∧ (Base.stZ i).piece.b = 979 ∧ (Base.stZ i).piece.lo = -325 ∧
        (Base.stZ i).piece.hi = -293) ∨
      ((Base.stZ i).piece.a = 951 ∧ (Base.stZ i).piece.b = 973 ∧
        (Base.stZ i).piece.lo = -352 ∧ (Base.stZ i).piece.hi = -344) ∨
      ((Base.stZ i).piece.a = 880 ∧ (Base.stZ i).piece.b = 883 ∧
        (Base.stZ i).piece.lo = -380 ∧ (Base.stZ i).piece.hi = -377) := by
  interval_cases i <;> simp [Base.piece, stZ0P, stZ1P, stZ2P]

/-- The classes of pieces of a module. -/
inductive ModCls (p : Program) (r : ℕ) : PSpec → Prop where
  /-- A group of the register circuit. -/
  | dz2g (i : ℕ) (ph : ℕ) : i < 28 → ModCls p r ⟨.dz2g i, modDX p r, modDY p r, ph⟩
  /-- `RF_J`. -/
  | rfj (ph : ℕ) : ModCls p r ⟨.rf 4, modDX p r - 850, modDY p r - 1044, ph⟩
  /-- The INC OR gate. -/
  | inc (ph : ℕ) : ModCls p r ⟨.orGate, modDX p r - 1132, modDY p r - 1291, ph⟩
  /-- Copy `m` of the DEC chain. -/
  | dec (m ph : ℕ) : m < 2 * numCallers p →
      ModCls p r ⟨.orGate, modDX p r - 1700 - 35 * (m : ℤ), modDY p r - 1727 - 64 * (m : ℤ), ph⟩
  /-- Piece `i` of station `j` on the line NZ. -/
  | stNZ (i j ph : ℕ) : i < 3 → j < numCallers p →
      ModCls p r ⟨.stNZ i, modDX p r + 72 * (j : ℤ), modDY p r + 72 * (j : ℤ), ph⟩
  /-- Piece `i` of station `j` on the line Z. -/
  | stZ (i j ph : ℕ) : i < 3 → j < numCallers p →
      ModCls p r ⟨.stZ i, modDX p r + 72 * (j : ℤ), modDY p r - 72 * (j : ℤ), ph⟩
  /-- The line-end eater NZ. -/
  | eatNZ (ph : ℕ) : ModCls p r ⟨.eatNZ, modDX p r + 72 * (D p - 1), modDY p r + 72 * (D p - 1), ph⟩
  /-- The line-end eater Z. -/
  | eatZ (ph : ℕ) : ModCls p r ⟨.eatZ, modDX p r + 72 * (D p - 1), modDY p r - 72 * (D p - 1), ph⟩

/-- Every piece of a module is in one of the classes. -/
theorem moduleSpecs_cls (p : Program) (r : ℕ) {s : PSpec} (hs : s ∈ moduleSpecs p r) :
    ModCls p r s := by
  unfold moduleSpecs at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ((((hs | hs | hs) | hs) | hs) | hs) | hs | hs
  · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    exact .dz2g i 0 (List.mem_range.1 hi)
  · subst hs; exact .rfj _
  · subst hs; exact .inc _
  · unfold decChainSpecs at hs
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hs
    exact .dec m _ (List.mem_range.1 hm)
  · unfold stationSpecs at hs
    obtain ⟨j, hj, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
    obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact .stNZ 0 j _ (by norm_num) (List.mem_range.1 hj)
    · exact .stNZ 1 j _ (by norm_num) (List.mem_range.1 hj)
    · exact .stNZ 2 j _ (by norm_num) (List.mem_range.1 hj)
  · unfold stationZSpecs at hs
    obtain ⟨j, hj, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
    obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact .stZ 0 j _ (by norm_num) (List.mem_range.1 hj)
    · exact .stZ 1 j _ (by norm_num) (List.mem_range.1 hj)
    · exact .stZ 2 j _ (by norm_num) (List.mem_range.1 hj)
  · subst hs; exact .eatNZ _
  · subst hs; exact .eatZ _

/-- Membership in the DEC chain. -/
theorem mem_decChainSpecs {n : ℕ} {dx dy : ℤ} {s : PSpec} (h : s ∈ decChainSpecs n dx dy) :
    ∃ m < n, s = ⟨.orGate, dx - 1700 - 35 * (m : ℤ), dy - 1727 - 64 * (m : ℤ), (15 + 14 * m) % 30⟩ := by
  unfold decChainSpecs at h
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
  exact ⟨m, List.mem_range.1 hm, rfl⟩

/-- Membership in the stations NZ. -/
theorem mem_stationSpecs {n : ℕ} {dx dy : ℤ} {s : PSpec} (h : s ∈ stationSpecs n dx dy) :
    ∃ j < n, ∃ i < 3, s = ⟨.stNZ i, dx + 72 * (j : ℤ), dy + 72 * (j : ℤ), 12 * j % 30⟩ := by
  unfold stationSpecs at h
  obtain ⟨j, hj, h⟩ := List.mem_flatMap.1 h
  obtain ⟨s', hs', rfl⟩ := List.mem_map.1 h
  obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  refine ⟨j, List.mem_range.1 hj, ?_⟩
  rcases hg with rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩

/-- Membership in the stations Z. -/
theorem mem_stationZSpecs {n : ℕ} {dx dy : ℤ} {s : PSpec} (h : s ∈ stationZSpecs n dx dy) :
    ∃ j < n, ∃ i < 3, s = ⟨.stZ i, dx + 72 * (j : ℤ), dy - 72 * (j : ℤ), 12 * j % 30⟩ := by
  unfold stationZSpecs at h
  obtain ⟨j, hj, h⟩ := List.mem_flatMap.1 h
  obtain ⟨s', hs', rfl⟩ := List.mem_map.1 h
  obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  refine ⟨j, List.mem_range.1 hj, ?_⟩
  rcases hg with rfl | rfl | rfl
  · exact ⟨0, by norm_num, rfl⟩
  · exact ⟨1, by norm_num, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩

/-- The box of a spec, unfolded. -/
theorem PSpec.bx_mk (g : Base) (vx vy : ℤ) (ph : ℕ) :
    (PSpec.mk g vx vy ph).bx = ⟨g.piece.a + vx, g.piece.b + vx, g.piece.lo + vy, g.piece.hi + vy⟩ :=
  rfl

/-- The boxes of the OR gate and of the reflector image `4`. -/
theorem base_boxes :
    Base.orGate.piece.a = 0 ∧ Base.orGate.piece.b = 90 ∧ Base.orGate.piece.lo = 0 ∧
      Base.orGate.piece.hi = 32 ∧ (Base.rf 4).piece.a = -22 ∧ (Base.rf 4).piece.b = 0 ∧
      (Base.rf 4).piece.lo = 2 ∧ (Base.rf 4).piece.hi = 10 ∧ Base.eatNZ.piece.a = 563 ∧
      Base.eatNZ.piece.b = 566 ∧ Base.eatNZ.piece.lo = 954 ∧ Base.eatNZ.piece.hi = 957 ∧
      Base.eatZ.piece.a = 1013 ∧ Base.eatZ.piece.b = 1016 ∧ Base.eatZ.piece.lo = -478 ∧
      Base.eatZ.piece.hi = -475 := by
  simp [Base.piece, orGateP, rfP, eatNZEndP, eatZEndP]

/-- **The pieces of a module are pairwise separated.** -/
theorem moduleSpecs_sep (p : Program) (r : ℕ) :
    (moduleSpecs p r).Pairwise fun s t => Piece.Sep s.piece t.piece := by
  have hb := base_boxes
  have hD : (D p) = (numCallers p : ℤ) := rfl
  have hD1 := one_le_D p
  unfold moduleSpecs
  simp only [List.pairwise_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  next => exact groupSpecs_sep (by rw [List.map_map]; exact dz2g_map ▸ dz2gPieces_sep) _ _
  next =>
    refine List.pairwise_pair.2 (PSpec.sep_of_far ?_)
    simp only [PSpec.bx_mk, BoxT.Far]; omega
  next =>
    intro x hx y hy
    obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have := dz2g_facts i (List.mem_range.1 hi)
    simp only [BoxT.Far] at this
    rcases hy with rfl | rfl <;> refine PSpec.sep_of_far ?_ <;>
      simp only [PSpec.bx_mk, BoxT.Far] <;> omega
  next =>
    unfold decChainSpecs
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp fun {m m'} h => PSpec.sep_of_far ?_
    simp only [PSpec.bx_mk, BoxT.Far]; omega
  next =>
    intro x hx y hy
    obtain ⟨m, hm, rfl⟩ := mem_decChainSpecs hy
    refine PSpec.sep_of_far ?_
    rcases hx with hx | rfl | rfl
    · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      have := dz2g_facts i (List.mem_range.1 hi)
      simp only [PSpec.bx_mk, BoxT.Far]; omega
    all_goals simp only [PSpec.bx_mk, BoxT.Far]; omega
  next =>
    refine pairwise_flatMap_lt List.pairwise_lt_range (fun j _ => ?_) ?_
    · unfold groupSpecs
      simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> refine PSpec.sep_of_far ?_ <;>
        simp only [PSpec.bx_mk, BoxT.Far, Base.piece, stNZ0P, stNZ1P, stNZ2P,
          List.getD_cons_zero, List.getD_cons_succ] <;> omega
    · intro j _ j' _ hjj x hx y hy
      obtain ⟨s1, hs1, rfl⟩ := List.mem_map.1 hx
      obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs1
      obtain ⟨s2, hs2, rfl⟩ := List.mem_map.1 hy
      obtain ⟨g', hg', rfl⟩ := mem_groupSpecs hs2
      refine PSpec.sep_of_far ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg hg'
      rcases hg with rfl | rfl | rfl <;> rcases hg' with rfl | rfl | rfl <;>
        simp only [PSpec.bx_mk, BoxT.Far, Base.piece, stNZ0P, stNZ1P, stNZ2P,
          List.getD_cons_zero, List.getD_cons_succ] <;> omega
  next =>
    intro x hx y hy
    obtain ⟨j, hj, i, hi, rfl⟩ := mem_stationSpecs hy
    have hc := stNZ_cases i hi
    refine PSpec.sep_of_far ?_
    rcases hx with (hx | rfl | rfl) | hx
    · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hx
      obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hg
      have := dz2g_facts i' (List.mem_range.1 hi')
      have := modD_uv p r
      simp only [PSpec.bx_mk, BoxT.Far]; omega
    · simp only [PSpec.bx_mk, BoxT.Far]; omega
    · simp only [PSpec.bx_mk, BoxT.Far]; omega
    · obtain ⟨m, hm, rfl⟩ := mem_decChainSpecs hx
      have := modD_uv p r
      simp only [PSpec.bx_mk, BoxT.Far]; omega
  next =>
    refine pairwise_flatMap_lt List.pairwise_lt_range (fun j _ => ?_) ?_
    · unfold groupSpecs
      simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> refine PSpec.sep_of_far ?_ <;>
        simp only [PSpec.bx_mk, BoxT.Far, Base.piece, stZ0P, stZ1P, stZ2P,
          List.getD_cons_zero, List.getD_cons_succ] <;> omega
    · intro j _ j' _ hjj x hx y hy
      obtain ⟨s1, hs1, rfl⟩ := List.mem_map.1 hx
      obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hs1
      obtain ⟨s2, hs2, rfl⟩ := List.mem_map.1 hy
      obtain ⟨g', hg', rfl⟩ := mem_groupSpecs hs2
      refine PSpec.sep_of_far ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg hg'
      rcases hg with rfl | rfl | rfl <;> rcases hg' with rfl | rfl | rfl <;>
        simp only [PSpec.bx_mk, BoxT.Far, Base.piece, stZ0P, stZ1P, stZ2P,
          List.getD_cons_zero, List.getD_cons_succ] <;> omega
  next =>
    intro x hx y hy
    obtain ⟨j, hj, i, hi, rfl⟩ := mem_stationZSpecs hy
    have hc := stZ_cases i hi
    have := modD_uv p r
    refine PSpec.sep_of_far ?_
    rcases hx with ((hx | rfl | rfl) | hx) | hx
    · obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hx
      obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hg
      have := dz2g_facts i' (List.mem_range.1 hi')
      simp only [PSpec.bx_mk, BoxT.Far]; omega
    · simp only [PSpec.bx_mk, BoxT.Far]; omega
    · simp only [PSpec.bx_mk, BoxT.Far]; omega
    · obtain ⟨m, hm, rfl⟩ := mem_decChainSpecs hx
      simp only [PSpec.bx_mk, BoxT.Far]; omega
    · obtain ⟨j', hj', i', hi', rfl⟩ := mem_stationSpecs hx
      have := stNZ_cases i' hi'
      simp only [PSpec.bx_mk, BoxT.Far]; omega
  next =>
    refine List.pairwise_pair.2 (PSpec.sep_of_far ?_)
    simp only [PSpec.bx_mk, BoxT.Far]; omega
  next =>
    intro x hx y hy
    have := modD_uv p r
    refine PSpec.sep_of_far ?_
    rcases hx with (((hx | rfl | rfl) | hx) | hx) | hx <;> rcases hy with rfl | rfl
    all_goals first
      | (simp only [PSpec.bx_mk, BoxT.Far]; omega)
      | (obtain ⟨g, hg, rfl⟩ := mem_groupSpecs hx
         obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hg
         have := dz2g_facts i' (List.mem_range.1 hi')
         simp only [PSpec.bx_mk, BoxT.Far]; omega)
      | (obtain ⟨m, hm, rfl⟩ := mem_decChainSpecs hx
         simp only [PSpec.bx_mk, BoxT.Far]; omega)
      | (obtain ⟨j', hj', i', hi', rfl⟩ := mem_stationSpecs hx
         have := stNZ_cases i' hi'
         simp only [PSpec.bx_mk, BoxT.Far]; omega)
      | (obtain ⟨j', hj', i', hi', rfl⟩ := mem_stationZSpecs hx
         have := stZ_cases i' hi'
         simp only [PSpec.bx_mk, BoxT.Far]; omega)

end LP

end LeanTheory.Life
