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

end LP

end LeanTheory.Life
