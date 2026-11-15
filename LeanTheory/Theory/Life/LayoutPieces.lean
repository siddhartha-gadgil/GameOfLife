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
  deriving Repr

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
theorem modD_uv (p : Program) (r : ℕ) :
    modDX p r - modDY p r = U p r ∧ modDX p r + modDY p r = 0 := by
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
    simp only [Base.piece, dz2gPieces, dz2gG0, dz2gG1, dz2gG2, dz2gG3, dz2gG4, dz2gG5, dz2gG6,
      dz2gG7, dz2gG8, dz2gG9, dz2gG10, dz2gG11, dz2gG12, dz2gG13, dz2gG14, dz2gG15, dz2gG16,
      dz2gG17, dz2gG18, dz2gG19, dz2gG20, dz2gG21, dz2gG22, dz2gG23, dz2gG24, dz2gG25, dz2gG26,
      dz2gG27, List.getD_cons_zero, List.getD_cons_succ,
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
    ∃ m < n,
      s = ⟨.orGate, dx - 1700 - 35 * (m : ℤ), dy - 1727 - 64 * (m : ℤ), (15 + 14 * m) % 30⟩ := by
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

/-- A list of three elements is pairwise related iff its three pairs are. -/
theorem pairwise_three {α : Type*} {R : α → α → Prop} {a b c : α} :
    [a, b, c].Pairwise R ↔ R a b ∧ R a c ∧ R b c := by
  simp [List.pairwise_cons, and_assoc]

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
      simp only [List.map_cons, List.map_nil]
      rw [pairwise_three]
      refine ⟨?_, ?_, ?_⟩ <;> refine PSpec.sep_of_far ?_ <;>
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
      simp only [List.map_cons, List.map_nil]
      rw [pairwise_three]
      refine ⟨?_, ?_, ?_⟩ <;> refine PSpec.sep_of_far ?_ <;>
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

/-- **Region of a module**: every piece of module `r` lies in `u ∈ [U_r - 738, U_r + 1350 + 144 D]`,
`v ∈ [-3328 - 198 D, 1379 + 144 D]`, and left of `u = U_r + 800` or above `v = 700`. -/
theorem moduleSpecs_uv (p : Program) (r : ℕ) {s : PSpec} (hs : s ∈ moduleSpecs p r) :
    s.bx.InUV (U p r - 738) (U p r + 1350 + 144 * D p) (-3328 - 198 * D p) (1379 + 144 * D p) ∧
      (s.bx.b - s.bx.lo ≤ U p r + 800 ∨ s.bx.b + s.bx.hi ≤ 700) := by
  have hb := base_boxes
  have hD : (D p) = (numCallers p : ℤ) := rfl
  have hD1 := one_le_D p
  have hm := modD_uv p r
  rcases moduleSpecs_cls p r hs with ⟨i, ph, hi⟩ | ph | ph | ⟨m, ph, hm'⟩ | ⟨i, j, ph, hi, hj⟩ |
    ⟨i, j, ph, hi, hj⟩ | ph | ph
  · have := dz2g_facts i hi
    simp only [PSpec.bx_mk, BoxT.InUV]; omega
  · simp only [PSpec.bx_mk, BoxT.InUV]; omega
  · simp only [PSpec.bx_mk, BoxT.InUV]; omega
  · simp only [PSpec.bx_mk, BoxT.InUV]; omega
  · have := stNZ_cases i hi
    simp only [PSpec.bx_mk, BoxT.InUV]; omega
  · have := stZ_cases i hi
    simp only [PSpec.bx_mk, BoxT.InUV]; omega
  · simp only [PSpec.bx_mk, BoxT.InUV]; omega
  · simp only [PSpec.bx_mk, BoxT.InUV]; omega

/-- `U` is increasing: `r < r' → U_r + P_M ≤ U_{r'}`. -/
theorem U_add_le (p : Program) {r r' : ℤ} (h : r < r') : U p r + PM p ≤ U p r' := by
  have hD := one_le_D p
  have : U p r' - U p r = PM p * (r' - r) := by unfold U; ring
  have h1 : (0 : ℤ) ≤ PM p := by unfold PM; omega
  nlinarith

/-- **Modules `r < r'` are separated.** -/
theorem moduleSpecs_cross (p : Program) {r r' : ℕ} (h : r < r') {s t : PSpec}
    (hs : s ∈ moduleSpecs p r) (ht : t ∈ moduleSpecs p r') : Piece.Sep s.piece t.piece := by
  have h1 := (moduleSpecs_uv p r hs).1
  have h2 := (moduleSpecs_uv p r' ht).1
  have hU := U_add_le p (r := r) (r' := r') (by exact_mod_cast h)
  have hD := one_le_D p
  refine PSpec.sep_of_far (BoxT.far_of_uv h1 h2 (Or.inl ?_))
  unfold PM at hU; omega

/-- **The pieces of all modules are pairwise separated.** -/
theorem modulesPart_sep (p : Program) :
    (modulesPart p).Pairwise fun s t => Piece.Sep s.piece t.piece :=
  pairwise_flatMap_lt List.pairwise_lt_range (fun r _ => moduleSpecs_sep p r)
    fun _ _ _ _ h _ hs _ ht => moduleSpecs_cross p h hs ht

/-- Units are numbered below `N + R`. -/
theorem mem_unitsPart {p : Program} {s : PSpec} (hs : s ∈ unitsPart p) :
    ∃ a < p.length + numRegs p, s ∈ unitSpecs p a := by
  obtain ⟨a, ha, hs⟩ := List.mem_flatMap.1 hs
  exact ⟨a, List.mem_range.1 (List.mem_filter.1 ha).1, hs⟩

/-- Modules are numbered below `R`. -/
theorem mem_modulesPart {p : Program} {s : PSpec} (hs : s ∈ modulesPart p) :
    ∃ r < numRegs p, s ∈ moduleSpecs p r := by
  obtain ⟨r, hr, hs⟩ := List.mem_flatMap.1 hs
  exact ⟨r, List.mem_range.1 hr, hs⟩

/-- **Units and modules are separated** (`R-31` #6). -/
theorem units_modules_sep (p : Program) {s t : PSpec} (hs : s ∈ unitsPart p)
    (ht : t ∈ modulesPart p) : Piece.Sep s.piece t.piece := by
  obtain ⟨a, ha, hs⟩ := mem_unitsPart hs
  obtain ⟨r, hr, ht⟩ := mem_modulesPart ht
  have h1 := unitSpecs_uv p a hs
  have h2 := (moduleSpecs_uv p r ht).1
  have h6 := (sep06_units_module0 p (a := a) (by unfold N R; omega)).1
  have hU : U0 p ≤ U p r := by
    have := one_le_D p
    unfold U PM; nlinarith
  have hD := one_le_D p
  refine PSpec.sep_of_far (BoxT.far_of_uv h1 h2 (Or.inl ?_))
  unfold U slabR modLeft at *; omega

/-! ### Combinatorics of the links: predecessor and caller numbers -/

/-- Every element of a list is at most its `foldr max 0`. -/
theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- One more instruction adds its contribution to the predecessor count. -/
theorem predBefore_succ (p : Program) (a i : ℕ) :
    predBefore p a (i + 1) = predBefore p a i + (p[i]?.map (predContrib p.length a i)).getD 0 := by
  unfold predBefore
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- The predecessor count before `i` is monotone in `i`. -/
theorem predBefore_mono (p : Program) (a : ℕ) {i i' : ℕ} (h : i ≤ i') :
    predBefore p a i ≤ predBefore p a i' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [predBefore_succ]; omega

/-- **Predecessor numbers increase with the instruction** (`C1`): a link of instruction `i` into
`a` (its number `off` below the contribution of `i` to `a`) comes before every link of a later
instruction. -/
theorem predIdx_lt (p : Program) {a i i' off off' : ℕ} {ins : Instr} (hi : p[i]? = some ins)
    (hoff : off < predContrib p.length a i ins) (hii : i < i') :
    predIdx p a i off < predIdx p a i' off' := by
  have h1 := predBefore_succ p a i
  have h2 := predBefore_mono p a (show i + 1 ≤ i' by omega)
  rw [hi] at h1
  simp only [Option.map_some, Option.getD_some] at h1
  unfold predIdx; push_cast; omega

/-- `predCount` is the start plus the contributions of all instructions. -/
theorem predCount_eq (p : Program) (a : ℕ) :
    predCount p a = (if a = 0 then 1 else 0) + predBefore p a p.length := rfl

/-- **Predecessor numbers are below `P`** (`C2`). -/
theorem predIdx_lt_P (p : Program) {a i off : ℕ} {ins : Instr} (hi : p[i]? = some ins)
    (hoff : off < predContrib p.length a i ins) (ha : a < p.length + numRegs p) :
    predIdx p a i off < P p := by
  have h1 := predBefore_succ p a i
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have h2 := predBefore_mono p a (show i + 1 ≤ p.length by omega)
  rw [hi] at h1
  simp only [Option.map_some, Option.getD_some] at h1
  have h3 : predCount p a ≤ numPreds p := by
    unfold numPreds
    exact le_trans (le_foldr_max (List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩))
      (le_max_right _ _)
  rw [predCount_eq] at h3
  unfold predIdx P; push_cast; split_ifs at * <;> omega

/-- The caller count before `i + 1`. -/
theorem callerIdx_succ (p : Program) (r i : ℕ) :
    callerIdx p r (i + 1) = callerIdx p r i + ((p[i]?.toList).filter (isDecOn r)).length := by
  unfold callerIdx
  rw [List.take_add_one, List.filter_append, List.length_append]

/-- The caller count is monotone. -/
theorem callerIdx_mono (p : Program) (r : ℕ) {i i' : ℕ} (h : i ≤ i') :
    callerIdx p r i ≤ callerIdx p r i' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [callerIdx_succ]; omega

/-- A `decJz` on `r` counts as a caller. -/
theorem callerIdx_succ_dec (p : Program) {r i z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    callerIdx p r (i + 1) = callerIdx p r i + 1 := by
  rw [callerIdx_succ, hi]
  simp [isDecOn]

/-- **Caller numbers increase** (`C3`). -/
theorem callerIdx_lt (p : Program) {r i i' z : ℕ} (hi : p[i]? = some (.decJz r z)) (h : i < i') :
    callerIdx p r i < callerIdx p r i' := by
  have := callerIdx_succ_dec p hi
  have := callerIdx_mono p r (show i + 1 ≤ i' by omega)
  omega

/-- The register of an instruction is below `R` (`C5`). -/
theorem reg_lt_R (p : Program) {i : ℕ} {ins : Instr} (hi : p[i]? = some ins) :
    regBound ins ≤ numRegs p := by
  unfold numRegs
  refine le_trans (le_foldr_max (List.mem_map.2 ⟨ins, ?_, rfl⟩)) (le_max_right _ _)
  exact List.mem_of_getElem? hi

/-- **Caller numbers are below `D`** (`C4`). -/
theorem callerIdx_lt_D (p : Program) {r i z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    callerIdx p r i < numCallers p := by
  have hR := reg_lt_R p hi
  simp only [regBound] at hR
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  have h1 := callerIdx_succ_dec p hi
  have h2 := callerIdx_mono p r (show i + 1 ≤ p.length by omega)
  have h3 : callerIdx p r p.length = decCount p r := by
    unfold callerIdx decCount; rw [List.take_length]
  have h4 : decCount p r ≤ numCallers p := by
    unfold numCallers
    exact le_trans (le_foldr_max (List.mem_map.2 ⟨r, List.mem_range.2 (by omega), rfl⟩))
      (le_max_right _ _)
  omega

/-- In a well-formed program an instruction other than `halt` is not the last (`C6`). -/
theorem succ_lt_of_wf {p : Program} (hp : p.WellFormed) {i : ℕ} {ins : Instr}
    (hi : p[i]? = some ins) (hne : ins ≠ .halt) : i + 1 < p.length := by
  have hlast : p[p.length - 1]? = some .halt := by
    rw [← List.getLast?_eq_getElem?]; exact hp.2
  have hlt : i < p.length := (List.getElem?_eq_some_iff.1 hi).1
  by_contra hcon
  have : i = p.length - 1 := by omega
  rw [this, hlast] at hi
  exact hne (Option.some.inj hi).symm

/-- In a well-formed program every jump target is an instruction (`C6`). -/
theorem jump_lt_of_wf {p : Program} (hp : p.WellFormed) {i r z : ℕ}
    (hi : p[i]? = some (.decJz r z)) : z < p.length :=
  hp.1 r z (List.mem_of_getElem? hi)

/-! ### Route corners: boxes, places, separation -/

/-- The reflector of a corner as a spec (phase `0`; the box does not depend on the phase). -/
def cornerSpec (c : Corner) : PSpec := ⟨.rf c.k, rfX c.k c.u c.v, rfY c.k c.u c.v, 0⟩

/-- The reflectors of a route have the boxes of its corners. -/
theorem route_bx (g : WL) (cs : List Corner) :
    (route g cs).1.map PSpec.bx = cs.map fun c => (cornerSpec c).bx := by
  induction cs generalizing g with
  | nil => rfl
  | cons c cs ih =>
    simp only [route, List.map_cons, ih]
    rfl

/-- **The box of a corner**: within `25` of the corner point in `u`, within `[-24, 27]` in `v`. -/
theorem corner_uv (c : Corner) :
    (cornerSpec c).bx.InUV (c.u - 25) (c.u + 25) (c.v - 24) (c.v + 27) := by
  obtain ⟨k, u, v, tag⟩ := c
  simp only [cornerSpec, PSpec.bx_mk, BoxT.InUV, rfX, rfY]
  match k with
  | 0 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 1 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 2 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 3 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 4 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 5 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | 6 => simp only [Base.piece, rfP, rfCU, rfCV]; omega
  | n + 7 =>
    have h2 : rfCU (n + 7) = 15 := by cases n <;> rfl
    have h3 : rfCV (n + 7) = -24 := by cases n <;> rfl
    simp only [Base.piece, h2, h3, rfP]; omega

/-- Corners `56` apart in `u` or `57` apart in `v` have far reflectors. -/
theorem corner_far {c c' : Corner}
    (h : c.u + 56 ≤ c'.u ∨ c'.u + 56 ≤ c.u ∨ c.v + 57 ≤ c'.v ∨ c'.v + 57 ≤ c.v) :
    (cornerSpec c).bx.Far (cornerSpec c').bx :=
  BoxT.far_of_uv (corner_uv c) (corner_uv c') (by omega)

/-- `C0` of a unit is one of `-237`, `-91`, `-67`. -/
theorem unitC0_cases (p : Program) (a : ℕ) :
    unitC0 p a = -237 ∨ unitC0 p a = -91 ∨ unitC0 p a = -67 := by
  unfold unitC0; cases unitKind p a <;> simp [UKind.C0, C0dec, C0inc, C0halt]

/-- The input columns of a unit are `≥ 31` left of its pieces. -/
theorem unitC0_uLo (p : Program) (a : ℕ) : unitC0 p a + 31 ≤ (unitKind p a).uLo := by
  unfold unitC0; cases unitKind p a <;> simp [UKind.C0, C0dec, C0inc, C0halt, UKind.uLo]

/-- **The place of a corner is valid**: its point lies where its tag says (linear constraints in
the parameters of `LP`). -/
def Valid (p : Program) (c : Corner) : Prop :=
  match c.tag with
  | .band b k h => 1 ≤ b ∧ b ≤ N p + R p ∧ 0 ≤ k ∧ k ≤ 9 ∧ VT p + 660 * b + 62 * k ≤ c.v ∧
      c.v ≤ VT p + 660 * b + 62 * k + 1 ∧ (h = true → c.u ≤ HI p + 360) ∧
      (h = false → slabL p + 30 ≤ c.u)
  | .halt a => 0 ≤ a ∧ a < N p ∧ c.u = A p a + 14 ∧ VT p ≤ c.v ∧ c.v ≤ VT p + 1
  | .slab a t => 0 ≤ a ∧ a < N p + R p ∧ 0 ≤ t ∧ t < 2 * P p ∧
      c.u = A p a + unitC0 p a.toNat - 61 * t ∧ c.v = VU p + 76 - 99 * t
  | .left r idx => 0 ≤ r ∧ r < R p ∧ 0 ≤ idx ∧ idx ≤ 4 * D p ∧ U p r - 794 - 62 * idx ≤ c.u ∧
      c.u ≤ U p r - 793 - 62 * idx ∧ modTop p + 72 ≤ c.v ∧ c.v ≤ 1181 + 144 * D p
  | .right r j w => 0 ≤ r ∧ r < R p ∧ 0 ≤ j ∧ j < D p ∧
      (w = 0 ∧ c.u = U p r + 1301 + 144 * j ∧ c.v = 1500 + 180 * (D p - 1 - j) ∨
        w = 1 ∧ U p r + 1409 + 144 * D p + 124 * (D p - 1 - j) ≤ c.u ∧
          c.u ≤ U p r + 1410 + 144 * D p + 124 * (D p - 1 - j) ∧ c.v = 1500 + 180 * (D p - 1 - j) ∨
        w = 2 ∧ U p r + 1471 + 144 * D p + 124 * (D p - 1 - j) ≤ c.u ∧
          c.u ≤ U p r + 1472 + 144 * D p + 124 * (D p - 1 - j) ∧ c.v = 1561 + 180 * (D p - 1 - j) ∨
        w = 3 ∧ c.u = U p r + 1230 + 144 * j ∧ c.v = 1561 + 180 * (D p - 1 - j))

/-- The global linear facts of the layout used by the separation of corners. -/
theorem layout_facts (p : Program) :
    1 ≤ P p ∧ 1 ≤ D p ∧ 1 ≤ R p ∧ 0 ≤ N p ∧ VU p = VT p - 1644 ∧ slabL p = -206 - 122 * P p ∧
      HI p + 390 ≤ slabL p - 120 ∧ VT p + 660 * (2 + N p + R p) ≤ -3324 - 198 * D p - 120 ∧
      modTop p = -3324 - 198 * D p ∧ PU p = 540 + 180 * P p ∧ PM p = 2400 + 540 * D p := by
  have h8 := sep08_hairpins_unit0 p
  have h3 := sep03_band_modules p
  have hA : A p 0 = 0 := by unfold A; ring
  refine ⟨one_le_P p, one_le_D p, one_le_R p, zero_le_N p, rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩
  · omega
  · unfold NB modTop at h3; omega

/-- **Two corners with valid, distinct places are `≥ 56` apart in `u` or `≥ 57` in `v`.** -/
theorem corner_gap (p : Program) {c c' : Corner} (hc : Valid p c) (hc' : Valid p c')
    (hne : c.tag ≠ c'.tag) :
    c.u + 56 ≤ c'.u ∨ c'.u + 56 ≤ c.u ∨ c.v + 57 ≤ c'.v ∨ c'.v + 57 ≤ c.v := by
  obtain ⟨k, u, v, tag⟩ := c
  obtain ⟨k', u', v', tag'⟩ := c'
  have hf := layout_facts p
  simp only at hne ⊢
  cases tag with
  | band b n h =>
    cases tag' with
    | band b' n' h' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.band.injEq, not_and] at hne
      cases h <;> cases h' <;> simp at hne hc hc' <;>
        rcases lt_trichotomy b b' with hb | rfl | hb <;> omega
    | halt a' => simp only [Valid] at hc hc'; omega
    | slab a' t' => simp only [Valid] at hc hc'; omega
    | left r' i' => simp only [Valid] at hc hc'; omega
    | right r' j' w' => simp only [Valid] at hc hc'; omega
  | halt a =>
    cases tag' with
    | band b' n' h' => simp only [Valid] at hc hc'; omega
    | halt a' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.halt.injEq] at hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := A_add_le p h; omega
      · have := A_add_le p h; omega
    | slab a' t' => simp only [Valid] at hc hc'; omega
    | left r' i' => simp only [Valid] at hc hc'; omega
    | right r' j' w' => simp only [Valid] at hc hc'; omega
  | slab a t =>
    cases tag' with
    | band b' n' h' => simp only [Valid] at hc hc'; omega
    | halt a' => simp only [Valid] at hc hc'; omega
    | slab a' t' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.slab.injEq, not_and] at hne
      have h1 := unitC0_cases p a.toNat
      have h2 := unitC0_cases p a'.toNat
      rcases lt_trichotomy a a' with h | rfl | h
      · have := A_add_le p h; omega
      · omega
      · have := A_add_le p h; omega
    | left r' i' => simp only [Valid] at hc hc'; omega
    | right r' j' w' => simp only [Valid] at hc hc'; omega
  | left r i =>
    cases tag' with
    | band b' n' h' => simp only [Valid] at hc hc'; omega
    | halt a' => simp only [Valid] at hc hc'; omega
    | slab a' t' => simp only [Valid] at hc hc'; omega
    | left r' i' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.left.injEq, not_and] at hne
      rcases lt_trichotomy r r' with h | rfl | h
      · have := U_add_le p h; omega
      · omega
      · have := U_add_le p h; omega
    | right r' j' w' =>
      simp only [Valid] at hc hc'
      rcases lt_trichotomy r r' with h | rfl | h
      · have := U_add_le p h; omega
      · omega
      · have := U_add_le p h; omega
  | right r j w =>
    cases tag' with
    | band b' n' h' => simp only [Valid] at hc hc'; omega
    | halt a' => simp only [Valid] at hc hc'; omega
    | slab a' t' => simp only [Valid] at hc hc'; omega
    | left r' i' =>
      simp only [Valid] at hc hc'
      rcases lt_trichotomy r r' with h | rfl | h
      · have := U_add_le p h; omega
      · omega
      · have := U_add_le p h; omega
    | right r' j' w' =>
      simp only [Valid] at hc hc'
      simp only [ne_eq, CTag.right.injEq, not_and] at hne
      rcases lt_trichotomy r r' with h | rfl | h
      · have := U_add_le p h; omega
      · omega
      · have := U_add_le p h; omega

/-- **A corner with a valid place is separated from every piece of every unit.** -/
theorem corner_unit_sep (p : Program) {c : Corner} (hc : Valid p c) {a : ℕ}
    {s : PSpec} (hs : s ∈ unitSpecs p a) :
    Piece.Sep (cornerSpec c).piece s.piece := by
  have h1 := corner_uv c
  have h2 := unitSpecs_uv p a hs
  have hf := layout_facts p
  have hk : -180 ≤ (unitKind p a).uLo := by cases unitKind p a <;> simp [UKind.uLo]
  refine PSpec.sep_of_far (BoxT.far_of_uv h1 h2 ?_)
  obtain ⟨k, u, v, tag⟩ := c
  simp only at h1 ⊢
  cases tag with
  | band b n h => simp only [Valid] at hc; omega
  | halt a' => simp only [Valid] at hc; omega
  | slab a' t =>
    simp only [Valid] at hc
    have hc0 := unitC0_cases p a'.toNat
    rcases lt_trichotomy a' a with h | h | h
    · have := A_add_le p h; omega
    · have h' : a'.toNat = a := by omega
      have := unitC0_uLo p a
      rw [h'] at hc; subst h; omega
    · have := A_add_le p h; omega
  | left r idx => simp only [Valid] at hc; omega
  | right r j w => simp only [Valid] at hc; omega

/-- **A corner with a valid place is separated from every piece of every module.** -/
theorem corner_module_sep (p : Program) {c : Corner} (hc : Valid p c) {r : ℕ}
    {s : PSpec} (hs : s ∈ moduleSpecs p r) : Piece.Sep (cornerSpec c).piece s.piece := by
  have h1 := corner_uv c
  obtain ⟨h2, h2'⟩ := moduleSpecs_uv p r hs
  have hf := layout_facts p
  refine PSpec.sep_of_far ?_
  obtain ⟨k, u, v, tag⟩ := c
  unfold BoxT.InUV at h1 h2
  unfold BoxT.Far
  simp only at h1 ⊢
  cases tag with
  | band b n h => simp only [Valid] at hc; omega
  | halt a' => simp only [Valid] at hc; omega
  | slab a' t => simp only [Valid] at hc; omega
  | left r' idx =>
    simp only [Valid] at hc
    rcases lt_trichotomy r' r with h | rfl | h
    · have := U_add_le p h; omega
    · omega
    · have := U_add_le p h; omega
  | right r' j w =>
    simp only [Valid] at hc
    rcases lt_trichotomy r' r with h | rfl | h
    · have := U_add_le p h; omega
    · obtain ⟨_, _, _, _, hw⟩ := hc
      rcases hw with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;>
        rcases h2' with h2' | h2' <;> omega
    · have := U_add_le p h; omega

/-! ### The corners of the machine -/

/-- The corners of a list of routes. -/
def specCorners (l : List (WL × List Corner)) : List Corner := l.flatMap (·.2)

/-- The corners of the routes of instruction `i`. -/
def instrCorners (p : Program) (i : ℕ) : List Corner := specCorners (instrSpecs p i)

/-- All route corners of the machine. -/
def allCorners (p : Program) : List Corner :=
  (List.range p.length).flatMap (instrCorners p) ++
    ((List.range (numRegs p)).filter (mergeUsed p)).flatMap fun r => specCorners (mergeSpecs p r)

/-- The reflectors of routes have the boxes of their corners. -/
theorem routeSpecs_bx (l : List (WL × List Corner)) :
    (routeSpecs l).map PSpec.bx = (specCorners l).map fun c => (cornerSpec c).bx := by
  unfold routeSpecs specCorners
  rw [List.map_flatMap, List.map_flatMap]
  simp only [route_bx]

/-- **The route reflectors of the machine have the boxes of its corners.** -/
theorem linksPart_bx (p : Program) :
    (linksPart p).map PSpec.bx = (allCorners p).map fun c => (cornerSpec c).bx := by
  unfold linksPart allCorners instrCorners
  rw [List.map_append, List.map_append, List.map_flatMap, List.map_flatMap, List.map_flatMap,
    List.map_flatMap]
  simp only [routeSpecs_bx]

/-- Separation of boxes. -/
def BoxT.Sep (B C : BoxT) : Prop := FarApart 2 (Box B.a B.b B.lo B.hi) (Box C.a C.b C.lo C.hi)

/-- Separation of placed pieces depends only on their boxes. -/
theorem PSpec.sep_iff (s t : PSpec) : Piece.Sep s.piece t.piece ↔ s.bx.Sep t.bx := Iff.rfl

/-- Separation of boxes is symmetric. -/
theorem BoxT.Sep.symm {B C : BoxT} (h : B.Sep C) : C.Sep B := by
  intro x hx y hy hn
  refine h y hy x hx ?_
  obtain ⟨n1, n2, n3, n4⟩ := hn
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- A piece of the routes has the box of a corner of the machine. -/
theorem mem_linksPart {p : Program} {t : PSpec} (ht : t ∈ linksPart p) :
    ∃ c ∈ allCorners p, t.bx = (cornerSpec c).bx := by
  have : t.bx ∈ (linksPart p).map PSpec.bx := List.mem_map.2 ⟨t, ht, rfl⟩
  rw [linksPart_bx] at this
  obtain ⟨c, hc, h⟩ := List.mem_map.1 this
  exact ⟨c, hc, h.symm⟩

/-- The window rule gives `e ∈ [0, 14]`. -/
theorem solveE_bounds (g : WL) (mk : ℤ → List Corner) (win : WL) :
    0 ≤ solveE g mk win ∧ solveE g mk win ≤ 14 := by
  change 0 ≤ winE _ _ ∧ winE _ _ ≤ 14
  unfold winE; omega

/-- The extra delay of an INC continue is `≥ 0`. -/
theorem G_nonneg (x : ℤ) : 0 ≤ 30 * ceil120 (max 0 x) := by
  unfold ceil120; omega

/-- The corners of a `halt` instruction. -/
theorem instrCorners_halt {p : Program} {i : ℕ} (hi : p[i]? = some .halt) :
    instrCorners p i = haltCorners p i := by
  simp [instrCorners, specCorners, instrSpecs, hi]

/-- The corners of an `inc r` instruction: the continue and the INC link, with some `G ≥ 0` and
`e`'s in `[0, 14]`. -/
theorem instrCorners_inc {p : Program} {i r : ℕ} (hi : p[i]? = some (.inc r)) :
    ∃ G ec el : ℤ, 0 ≤ G ∧ 0 ≤ ec ∧ ec ≤ 14 ∧ 0 ≤ el ∧ el ≤ 14 ∧
      instrCorners p i = upCorners p (instrBand i) 0 (A p i + incD)
          (hairCont p G ec (A p i + incD)) (i + 1)
          (copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0) (A p i + incD)) ++
        upCorners p (instrBand i) 1 (A p i + incR) (hairReg p 1 el (A p i + incR))
          (p.length + r)
          (copyIdx C0halt (predIdx p (p.length + r) i (if i + 1 = p.length + r then 1 else 0))
            (A p i + incR)) := by
  simp only [instrCorners, specCorners, instrSpecs, hi, incSpecs, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  exact ⟨_, _, _, G_nonneg _, (solveE_bounds _ _ _).1, (solveE_bounds _ _ _).2,
    (solveE_bounds _ _ _).1, (solveE_bounds _ _ _).2, rfl⟩

/-- The corners of a `decJz r z` instruction (caller `j`): the tokens and `C`, then the answers,
with `e`'s in `[0, 14]`. -/
theorem instrCorners_dec {p : Program} {i r z : ℕ} (hi : p[i]? = some (.decJz r z)) :
    ∃ eA eB : ℤ, 0 ≤ eA ∧ eA ≤ 14 ∧ 0 ≤ eB ∧ eB ≤ 14 ∧
      instrCorners p i =
        downCorners p (instrBand i) 0 (A p i + decL)
            (hairKNZ p (qOf p (callerIdx p r i)) (A p i + decR) (A p i + decL))
            (U p r + nzTokChan p (callerIdx p r i)) (nzTokPortV (callerIdx p r i)) r
            (2 * D p + 1 + 2 * (callerIdx p r i)) ++
          downCorners p (instrBand i) 1 (A p i + decR)
            (hairC p (qOf p (callerIdx p r i)) (A p i + decR))
            (U p r + decChan p (2 * (callerIdx p r i))) (decPortV p (2 * (callerIdx p r i))) r
            (2 * (callerIdx p r i)) ++
          ztokCorners p (instrBand i) (A p i + decD)
            (hairKZ p (qOf p (callerIdx p r i)) (A p i + decD)) r (callerIdx p r i) ++
          nzAnsCorners p (instrBand i) r (callerIdx p r i)
            (hairReg p 3 eA (U p r + nzAnsChan p (callerIdx p r i))) (i + 1)
            (copyIdx (unitC0 p (i + 1)) (predIdx p (i + 1) i 0)
              (U p r + nzAnsChan p (callerIdx p r i))) ++
          zAnsCorners p (instrBand i) r (callerIdx p r i)
            (hairReg p 4 eB (U p r + zAnsChan p (callerIdx p r i))) z
            (copyIdx (unitC0 p z) (predIdx p z i (if i + 1 = z then 1 else 0))
              (U p r + zAnsChan p (callerIdx p r i))) := by
  simp only [instrCorners, specCorners, instrSpecs, hi, decSpecs, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]
  exact ⟨_, _, (solveE_bounds _ _ _).1, (solveE_bounds _ _ _).2,
    (solveE_bounds _ _ _).1, (solveE_bounds _ _ _).2, rfl⟩

/-! ### Owners of the places -/

/-- The places owned by instruction `i`: its sub-band, its halt corner, the entry copies of its
links (predecessor number `predIdx`), the ports of its caller number on its register. -/
def TagOf (p : Program) (i : ℕ) : CTag → Prop
  | .band b _ _ => b = 1 + i
  | .halt a => a = i
  | .slab a t => ∃ (ins : Instr) (off a' : ℕ), a = a' ∧ p[i]? = some ins ∧
      off < predContrib p.length a' i ins ∧
      2 * predIdx p a' i off ≤ t ∧ t ≤ 2 * predIdx p a' i off + 1
  | .left r idx => ∃ (z r' : ℕ), r = r' ∧ p[i]? = some (.decJz r' z) ∧
      (idx = 2 * (callerIdx p r' i : ℤ) ∨ idx = 2 * D p + 1 + 2 * (callerIdx p r' i : ℤ) ∨
        idx = 2 * D p + 2 + 2 * (callerIdx p r' i : ℤ))
  | .right r j _ => ∃ (z r' : ℕ), r = r' ∧ p[i]? = some (.decJz r' z) ∧ j = callerIdx p r' i

/-- **A place has at most one owner.** -/
theorem TagOf_unique (p : Program) {i i' : ℕ} {τ : CTag} (h : TagOf p i τ) (h' : TagOf p i' τ) :
    i = i' := by
  cases τ with
  | band b k hb => simp only [TagOf] at h h'; omega
  | halt a => simp only [TagOf] at h h'; omega
  | slab a t =>
    simp only [TagOf] at h h'
    obtain ⟨ins, off, a1, rfl, hi, ho, h1, h2⟩ := h
    obtain ⟨ins', off', a2, ha2, hi', ho', h1', h2'⟩ := h'
    have : a2 = a1 := by omega
    subst this
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := predIdx_lt p (off' := off') hi ho hlt; omega
    · have := predIdx_lt p (off' := off) hi' ho' hlt; omega
  | left r idx =>
    simp only [TagOf] at h h'
    obtain ⟨z, r1, rfl, hi, h1⟩ := h
    obtain ⟨z', r2, hr2, hi', h1'⟩ := h'
    have : r2 = r1 := by omega
    subst this
    have hD := callerIdx_lt_D p hi
    have hD' := callerIdx_lt_D p hi'
    have hDe : D p = (numCallers p : ℤ) := rfl
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := callerIdx_lt p hi hlt; omega
    · have := callerIdx_lt p hi' hlt; omega
  | right r j w =>
    simp only [TagOf] at h h'
    obtain ⟨z, r1, rfl, hi, h1⟩ := h
    obtain ⟨z', r2, hr2, hi', h1'⟩ := h'
    have : r2 = r1 := by omega
    subst this
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := callerIdx_lt p hi hlt; omega
    · have := callerIdx_lt p hi' hlt; omega

/-- The places owned by the merge link of register `r`: its sub-band and the INC port. -/
def TagOfM (p : Program) (r : ℕ) : CTag → Prop
  | .band b _ _ => b = 1 + N p + r
  | .left r' idx => r' = r ∧ idx = 2 * D p
  | _ => False

/-- A place of an instruction is not a place of a merge link. -/
theorem TagOf_not_M (p : Program) {i r : ℕ} (hi : i < p.length) {τ : CTag} (h : TagOf p i τ)
    (h' : TagOfM p r τ) : False := by
  cases τ with
  | band b k hb => simp only [TagOf, TagOfM, N] at h h'; omega
  | halt a => simp only [TagOfM] at h'
  | slab a t => simp only [TagOfM] at h'
  | left r' idx =>
    simp only [TagOf, TagOfM] at h h'
    obtain ⟨z, r1, rfl, hi, h1⟩ := h
    have hD := callerIdx_lt_D p hi
    have hDe : D p = (numCallers p : ℤ) := rfl
    omega
  | right r' j w => simp only [TagOfM] at h'

/-- A place has at most one merge owner. -/
theorem TagOfM_unique (p : Program) {r r' : ℕ} {τ : CTag} (h : TagOfM p r τ)
    (h' : TagOfM p r' τ) : r = r' := by
  cases τ with
  | band b k hb => simp only [TagOfM] at h h'; omega
  | halt a => simp only [TagOfM] at h
  | slab a t => simp only [TagOfM] at h
  | left r'' idx => simp only [TagOfM] at h h'; omega
  | right r'' j w => simp only [TagOfM] at h

/-! ### Valid places of the corners of the links -/

/-- `A_a ≥ 0` for `a ≥ 0`. -/
theorem A_nonneg (p : Program) {a : ℤ} (h : 0 ≤ a) : 0 ≤ A p a := by
  have := one_le_P p
  unfold A PU; positivity

/-- `U_r ≥ U_0` for `r ≥ 0`, and the left end of every module is right of every unit column. -/
theorem U_ge (p : Program) {r : ℤ} (h : 0 ≤ r) :
    U0 p ≤ U p r ∧ slabR p + 120 ≤ U0 p + modLeft p := by
  have hD := one_le_D p
  have h6 := (sep06_units_module0 p (a := 0) (by have := zero_le_N p; have := one_le_R p; omega)).1
  have hA : A p 0 = 0 := by unfold A; ring
  refine ⟨by unfold U PM; nlinarith, by omega⟩

/-- The band corners of a link: valid, on sub-band `b`. -/
theorem bandCorners_valid (p : Program) {b s c H cd : ℤ} {k0 k4 : ℕ}
    (hb : 1 ≤ b ∧ b ≤ N p + R p) (hs : 0 ≤ s ∧ s ≤ 4) (hc : slabL p + 30 ≤ c)
    (hH : H ≤ HI p + 360) (hcd : slabL p + 30 ≤ cd) :
    ∀ x ∈ bandCorners p b s c H cd k0 k4, Valid p x ∧ ∃ k h, x.tag = .band b k h := by
  intro x hx
  simp only [bandCorners, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, _, _, rfl⟩ <;> simp only [Valid, trackOut, trackBack, track] <;>
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, fun h => ?_,
      fun h => ?_⟩ <;>
    first | omega | simp at h

/-- The corners of a link up to entry copy `t` of unit `a`. -/
theorem upCornersK_valid (p : Program) {k0 : ℕ} {b s c H t : ℤ} {a : ℕ}
    (hb : 1 ≤ b ∧ b ≤ N p + R p) (hs : 0 ≤ s ∧ s ≤ 4) (hc : slabL p + 30 ≤ c)
    (hH : H ≤ HI p + 360) (ha : (a : ℤ) < N p + R p) (ht : 0 ≤ t ∧ t < 2 * P p) :
    ∀ x ∈ upCornersK k0 p b s c H a t, Valid p x ∧
      ((∃ k h, x.tag = .band b k h) ∨ x.tag = .slab a t) := by
  have hA := A_nonneg p (a := a) (by omega)
  have h0 := unitC0_cases p a
  have hP := one_le_P p
  intro x hx
  simp only [upCornersK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | rfl
  · obtain ⟨h1, h2⟩ := bandCorners_valid p hb hs hc hH
      (by unfold destU inCol slabL; omega) x hx
    exact ⟨h1, Or.inl h2⟩
  · refine ⟨?_, Or.inr rfl⟩
    simp only [Valid, destU, destV, inCol, sideV, Int.toNat_natCast]
    omega

/-- The corners of a link down to left-zone port `idx` of module `r`. -/
theorem downCorners_valid (p : Program) {b s c H idx vp : ℤ} {r : ℕ}
    (hb : 1 ≤ b ∧ b ≤ N p + R p) (hs : 0 ≤ s ∧ s ≤ 4) (hc : slabL p + 30 ≤ c)
    (hH : H ≤ HI p + 360) (hr : (r : ℤ) < R p) (hidx : 0 ≤ idx ∧ idx ≤ 4 * D p)
    (hvp : modTop p + 72 ≤ vp ∧ vp ≤ 1181 + 144 * D p) :
    ∀ x ∈ downCorners p b s c H (U p r + leftChan idx vp) vp r idx, Valid p x ∧
      ((∃ k h, x.tag = .band b k h) ∨ x.tag = .left r idx) := by
  have hU := U_ge p (r := r) (by omega)
  have hl := fixp_bounds (uL - 62 * idx) (1 - vp % 2)
  have hP := one_le_P p
  have hD := one_le_D p
  intro x hx
  simp only [downCorners, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | rfl
  · obtain ⟨h1, h2⟩ := bandCorners_valid p hb hs hc hH
      (by unfold leftChan uL slabL slabR modLeft at *; omega) x hx
    exact ⟨h1, Or.inl h2⟩
  · refine ⟨?_, Or.inr rfl⟩
    simp only [Valid]
    unfold leftChan uL at *
    omega

/-- The corners of the KZ link (slot `2`) down to the Z token of caller `j` of module `r`. -/
theorem ztokCorners_valid (p : Program) {b c H j : ℤ} {r : ℕ}
    (hb : 1 ≤ b ∧ b ≤ N p + R p) (hc : slabL p + 30 ≤ c) (hH : H ≤ HI p + 360)
    (hr : (r : ℤ) < R p) (hj : 0 ≤ j ∧ j < D p) :
    ∀ x ∈ ztokCorners p b c H r j, Valid p x ∧
      ((∃ k h, x.tag = .band b k h) ∨ x.tag = .right r j 2 ∨ x.tag = .right r j 3) := by
  have hU := U_ge p (r := r) (by omega)
  have hd := zAnsDepth_eq p j
  have h1 := fixp_bounds (uR p + 124 * qOf p j + 62) (1 - zTokDepth p j % 2)
  have hP := one_le_P p
  intro x hx
  simp only [ztokCorners, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | rfl | rfl
  · obtain ⟨h1, h2⟩ := bandCorners_valid p hb (by omega) hc hH
      (by unfold zTokChan uR qOf slabL slabR modLeft at *; omega) x hx
    exact ⟨h1, Or.inl h2⟩
  · refine ⟨?_, Or.inr (Or.inl rfl)⟩
    simp only [Valid]
    refine ⟨by omega, hr, hj.1, hj.2, Or.inr (Or.inr (Or.inl ⟨trivial, ?_, ?_, ?_⟩))⟩ <;>
      unfold zTokChan zTokDepth uR qOf at * <;> omega
  · refine ⟨?_, Or.inr (Or.inr rfl)⟩
    simp only [Valid]
    refine ⟨by omega, hr, hj.1, hj.2, Or.inr (Or.inr (Or.inr ⟨trivial, ?_, ?_⟩))⟩ <;>
      unfold zTokStation zTokDepth qOf at * <;> omega

/-- The corners of the NZ answer of caller `j` of module `r` to entry copy `t` of unit `a`. -/
theorem nzAnsCorners_valid (p : Program) {b j H t : ℤ} {r a : ℕ}
    (hb : 1 ≤ b ∧ b ≤ N p + R p) (hH : H ≤ HI p + 360) (hr : (r : ℤ) < R p)
    (hj : 0 ≤ j ∧ j < D p) (ha : (a : ℤ) < N p + R p) (ht : 0 ≤ t ∧ t < 2 * P p) :
    ∀ x ∈ nzAnsCorners p b r j H a t, Valid p x ∧
      ((∃ k h, x.tag = .band b k h) ∨ x.tag = .slab a t ∨
        x.tag = .left r (2 * D p + 2 + 2 * j)) := by
  have hU := U_ge p (r := r) (by omega)
  have hl := fixp_bounds (uL - 62 * (2 * D p + 2 + 2 * j)) (1 - nzAnsPortV j % 2)
  have hP := one_le_P p
  intro x hx
  simp only [nzAnsCorners, List.mem_cons] at hx
  rcases hx with rfl | hx
  · refine ⟨?_, Or.inr (Or.inr rfl)⟩
    simp only [Valid]
    unfold nzAnsChan leftChan nzAnsPortV uL modTop at *
    omega
  · obtain ⟨h1, h2⟩ := upCornersK_valid p hb (by omega) (by
      unfold nzAnsChan leftChan uL nzAnsPortV slabL slabR modLeft at *; omega) hH ha ht x hx
    rcases h2 with h2 | h2
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr (Or.inl h2)⟩

/-- The corners of the Z answer of caller `j` of module `r` to entry copy `t` of unit `a`. -/
theorem zAnsCorners_valid (p : Program) {b j H t : ℤ} {r a : ℕ}
    (hb : 1 ≤ b ∧ b ≤ N p + R p) (hH : H ≤ HI p + 360) (hr : (r : ℤ) < R p)
    (hj : 0 ≤ j ∧ j < D p) (ha : (a : ℤ) < N p + R p) (ht : 0 ≤ t ∧ t < 2 * P p) :
    ∀ x ∈ zAnsCorners p b r j H a t, Valid p x ∧
      ((∃ k h, x.tag = .band b k h) ∨ x.tag = .slab a t ∨ x.tag = .right r j 0 ∨
        x.tag = .right r j 1) := by
  have hU := U_ge p (r := r) (by omega)
  have hd := zAnsDepth_eq p j
  have h1 := fixp_bounds (uR p + 124 * qOf p j) (1 - zAnsDepth p j % 2)
  have hP := one_le_P p
  intro x hx
  simp only [zAnsCorners, List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · refine ⟨?_, Or.inr (Or.inr (Or.inl rfl))⟩
    simp only [Valid]
    refine ⟨by omega, hr, hj.1, hj.2, Or.inl ⟨trivial, ?_, ?_⟩⟩ <;>
      unfold zAnsStation qOf at * <;> omega
  · refine ⟨?_, Or.inr (Or.inr (Or.inr rfl))⟩
    simp only [Valid]
    refine ⟨by omega, hr, hj.1, hj.2, Or.inr (Or.inl ⟨trivial, ?_, ?_, ?_⟩)⟩ <;>
      unfold zAnsChan uR qOf at * <;> omega
  · obtain ⟨h1, h2⟩ := upCornersK_valid p hb (by omega) (by
      unfold zAnsChan uR qOf slabL slabR modLeft at *; omega) hH ha ht x hx
    rcases h2 with h2 | h2
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr (Or.inl h2)⟩

/-- The entry copy of a link is in `[0, 2P)` when its predecessor number is below `P`. -/
theorem copyIdx_range (p : Program) {C0 e c : ℤ} (he : 0 ≤ e ∧ e < P p) :
    0 ≤ copyIdx C0 e c ∧ copyIdx C0 e c < 2 * P p ∧ 2 * e ≤ copyIdx C0 e c ∧
      copyIdx C0 e c ≤ 2 * e + 1 := by
  have := copyBeta_spec C0 e c
  omega

/-- Predecessor numbers are `≥ 0`. -/
theorem predIdx_nonneg (p : Program) (a i off : ℕ) : 0 ≤ predIdx p a i off := by
  unfold predIdx; omega

/-- **The corners of every instruction are at valid places owned by the instruction.** -/
theorem instrCorners_valid {p : Program} (hp : p.WellFormed) {i : ℕ} (hi : i < p.length) :
    ∀ c ∈ instrCorners p i, Valid p c ∧ TagOf p i c.tag := by
  have hf := layout_facts p
  have hA := A_nonneg p (a := i) (by omega)
  have hN : (i : ℤ) < N p := by unfold N; exact_mod_cast hi
  obtain ⟨ins, hins⟩ : ∃ ins, p[i]? = some ins := ⟨_, List.getElem?_eq_getElem hi⟩
  have hb : 1 ≤ instrBand i ∧ instrBand i ≤ N p + R p := by unfold instrBand; omega
  cases ins with
  | halt =>
    rw [instrCorners_halt hins]
    intro c hc
    simp only [haltCorners, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    refine ⟨?_, by simp [TagOf]⟩
    simp only [Valid, haltD, trackOut, track, true_and]
    omega
  | inc r =>
    obtain ⟨G, ec, el, hG, he1, he2, hl1, hl2, heq⟩ := instrCorners_inc hins
    rw [heq]
    have hi1 := succ_lt_of_wf hp hins (by simp)
    have hr := reg_lt_R p hins
    simp only [regBound] at hr
    have hR : (r : ℤ) < R p := by unfold R; omega
    have hc1 := fixp_bounds (HI p - 62 - G - 2 * ec) ((A p i + incD) % 2)
    have hc2 := hairReg_le p (s := 1) (e := el) (c := A p i + incR) (by norm_num) hl1
    have hoff1 : 0 < predContrib p.length (i + 1) i (.inc r) := by simp [predContrib]
    have hoff2 : (if i + 1 = p.length + r then 1 else 0) <
        predContrib p.length (p.length + r) i (.inc r) := by simp [predContrib]
    have hp1 := predIdx_lt_P p hins hoff1 (by omega)
    have hp2 := predIdx_lt_P p hins hoff2 (by omega)
    have ht1 := copyIdx_range p (C0 := unitC0 p (i + 1)) (c := A p i + incD)
      ⟨predIdx_nonneg p _ _ _, hp1⟩
    have ht2 := copyIdx_range p (C0 := C0halt) (c := A p i + incR) ⟨predIdx_nonneg p _ _ _, hp2⟩
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨h1, h2⟩ := upCornersK_valid p hb (by norm_num)
        (by unfold incD slabL at *; omega) (by unfold hairCont at *; omega)
        (by unfold N at *; omega) ⟨ht1.1, ht1.2.1⟩ c hc
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨k, h, h2⟩ | h2 <;> rw [h2]
      · simp [TagOf, instrBand]
      · exact ⟨_, 0, _, rfl, hins, hoff1, ht1.2.2.1, ht1.2.2.2⟩
    · obtain ⟨h1, h2⟩ := upCornersK_valid p hb (by norm_num)
        (by unfold incR slabL at *; omega) hc2 (by unfold N R at *; omega)
        ⟨ht2.1, ht2.2.1⟩ c hc
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨k, h, h2⟩ | h2 <;> rw [h2]
      · simp [TagOf, instrBand]
      · exact ⟨_, _, _, rfl, hins, hoff2, ht2.2.2.1, ht2.2.2.2⟩
  | decJz r z =>
    obtain ⟨eA, eB, hA1, hA2, hB1, hB2, heq⟩ := instrCorners_dec hins
    rw [heq]
    have hi1 := succ_lt_of_wf hp hins (by simp)
    have hz := jump_lt_of_wf hp hins
    have hr := reg_lt_R p hins
    simp only [regBound] at hr
    have hR : (r : ℤ) < R p := by unfold R; omega
    have hj := callerIdx_lt_D p hins
    have hDe : D p = (numCallers p : ℤ) := rfl
    have hq : 0 ≤ qOf p (callerIdx p r i) := by unfold qOf; omega
    have hEC : 0 ≤ eCtot (qOf p (callerIdx p r i)) := by
      have := xC_spec hq; have := eC_bounds (qOf p (callerIdx p r i))
      have := sigma_bounds (qOf p (callerIdx p r i)); unfold eCtot; omega
    have hN8 := eN_spec hq
    have hx := xC_spec hq
    have hK := eKZ_spec hq
    have hec := eC_bounds (qOf p (callerIdx p r i))
    have hsg := sigma_bounds (qOf p (callerIdx p r i))
    have hHC := fixp_bounds (HI p + 90 - 2 * eCtot (qOf p (callerIdx p r i))) ((A p i + decR) % 2)
    have hHN := fixp_bounds (hairC p (qOf p (callerIdx p r i)) (A p i + decR) - 62 -
      2 * eN (qOf p (callerIdx p r i))) ((A p i + decL) % 2)
    have hHZ := hairReg_le p (s := 2) (e := eKZ (qOf p (callerIdx p r i))) (c := A p i + decD)
      (by norm_num) hK.2.1
    have hH3 := hairReg_le p (s := 3) (e := eA) (c := U p r + nzAnsChan p (callerIdx p r i))
      (by norm_num) hA1
    have hH4 := hairReg_le p (s := 4) (e := eB) (c := U p r + zAnsChan p (callerIdx p r i))
      (by norm_num) hB1
    have hoff1 : 0 < predContrib p.length (i + 1) i (.decJz r z) := by simp [predContrib]
    have hoff2 : (if i + 1 = z then 1 else 0) < predContrib p.length z i (.decJz r z) := by
      simp [predContrib]
    have hp1 := predIdx_lt_P p hins hoff1 (by omega)
    have hp2 := predIdx_lt_P p hins hoff2 (by omega)
    have ht1 := copyIdx_range p (C0 := unitC0 p (i + 1))
      (c := U p r + nzAnsChan p (callerIdx p r i)) ⟨predIdx_nonneg p _ _ _, hp1⟩
    have ht2 := copyIdx_range p (C0 := unitC0 p z) (c := U p r + zAnsChan p (callerIdx p r i))
      ⟨predIdx_nonneg p _ _ _, hp2⟩
    have hleft : ∀ idx : ℤ, (idx = 2 * (callerIdx p r i : ℤ) ∨
        idx = 2 * D p + 1 + 2 * (callerIdx p r i : ℤ) ∨
        idx = 2 * D p + 2 + 2 * (callerIdx p r i : ℤ)) → TagOf p i (.left r idx) := by
      intro idx h
      exact ⟨z, r, rfl, hins, h⟩
    have hright : ∀ w : ℕ, TagOf p i (.right r (callerIdx p r i) w) := by
      intro w
      exact ⟨z, r, rfl, hins, rfl⟩
    have hband : ∀ k h, TagOf p i (.band (instrBand i) k h) := by
      intro k h; simp [TagOf, instrBand]
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (((hc | hc) | hc) | hc) | hc
    · obtain ⟨h1, h2⟩ := downCorners_valid p hb (s := 0) (by norm_num)
        (by unfold decL slabL at *; omega) (by unfold hairKNZ hairC at *; omega) hR
        (idx := 2 * D p + 1 + 2 * (callerIdx p r i)) (by omega)
        (vp := nzTokPortV (callerIdx p r i)) (by unfold nzTokPortV modTop; omega) c hc
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨k, h, h2⟩ | h2 <;> rw [h2]
      · exact hband k h
      · exact hleft _ (by omega)
    · obtain ⟨h1, h2⟩ := downCorners_valid p hb (s := 1) (by norm_num)
        (by unfold decR slabL at *; omega) (by unfold hairC at *; omega) hR
        (idx := 2 * (callerIdx p r i)) (by omega)
        (vp := decPortV p (2 * (callerIdx p r i))) (by unfold decPortV modTop; omega) c hc
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨k, h, h2⟩ | h2 <;> rw [h2]
      · exact hband k h
      · exact hleft _ (by omega)
    · obtain ⟨h1, h2⟩ := ztokCorners_valid p hb (by unfold decD slabL at *; omega)
        (by unfold hairKZ; exact hHZ) hR (j := callerIdx p r i) (by omega) c hc
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨k, h, h2⟩ | h2 | h2 <;> rw [h2]
      · exact hband k h
      · exact hright 2
      · exact hright 3
    · obtain ⟨h1, h2⟩ := nzAnsCorners_valid p hb hH3 hR (j := callerIdx p r i) (by omega)
        (a := i + 1) (by unfold N at *; omega) ⟨ht1.1, ht1.2.1⟩ c hc
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨k, h, h2⟩ | h2 | h2 <;> rw [h2]
      · exact hband k h
      · exact ⟨_, 0, _, rfl, hins, hoff1, ht1.2.2.1, ht1.2.2.2⟩
      · exact hleft _ (by omega)
    · obtain ⟨h1, h2⟩ := zAnsCorners_valid p hb hH4 hR (j := callerIdx p r i) (by omega)
        (a := z) (by unfold N at *; omega) ⟨ht2.1, ht2.2.1⟩ c hc
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨k, h, h2⟩ | h2 | h2 | h2 <;> rw [h2]
      · exact hband k h
      · exact ⟨_, _, _, rfl, hins, hoff2, ht2.2.2.1, ht2.2.2.2⟩
      · exact hright 0
      · exact hright 1

/-- Pairwise distinct tags, through the list of tags. -/
theorem pairwise_tag_iff (L : List Corner) :
    L.Pairwise (fun c c' => c.tag ≠ c'.tag) ↔ (L.map Corner.tag).Pairwise (· ≠ ·) :=
  List.pairwise_map.symm

/-- **The corners of one instruction have pairwise distinct places.** -/
theorem instrCorners_tags {p : Program} (hp : p.WellFormed) {i : ℕ} (hi : i < p.length) :
    (instrCorners p i).Pairwise fun c c' => c.tag ≠ c'.tag := by
  obtain ⟨ins, hins⟩ : ∃ ins, p[i]? = some ins := ⟨_, List.getElem?_eq_getElem hi⟩
  cases ins with
  | halt =>
    rw [instrCorners_halt hins]
    simp [haltCorners]
  | inc r =>
    obtain ⟨G, ec, el, -, -, -, -, -, heq⟩ := instrCorners_inc hins
    have hi1 := succ_lt_of_wf hp hins (by simp)
    rw [heq, pairwise_tag_iff]
    simp only [upCorners, upCornersK, bandCorners, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil]
    simp [List.pairwise_cons]
    omega
  | decJz r z =>
    obtain ⟨eA, eB, -, -, -, -, heq⟩ := instrCorners_dec hins
    have hz : i + 1 = z → predIdx p z i (if i + 1 = z then 1 else 0) =
        predIdx p (i + 1) i 0 + 1 := by
      intro h; subst h; simp [predIdx]
    have h1 := copyBeta_spec (unitC0 p (i + 1)) (predIdx p (i + 1) i 0)
      (U p r + nzAnsChan p (callerIdx p r i))
    have h2 := copyBeta_spec (unitC0 p z) (predIdx p z i (if i + 1 = z then 1 else 0))
      (U p r + zAnsChan p (callerIdx p r i))
    rw [heq, pairwise_tag_iff]
    simp only [upCornersK, bandCorners, downCorners, ztokCorners, nzAnsCorners,
      zAnsCorners, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
    simp only [ne_eq, sub_zero, Int.reduceSub, Nat.cast_add, Nat.cast_one, List.pairwise_cons,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, CTag.band.injEq,
      Bool.false_eq_true, and_false, not_false_eq_true, OfNat.zero_ne_ofNat, and_self, and_true,
      reduceCtorEq, zero_ne_one, forall_eq, Bool.true_eq_false, OfNat.ofNat_ne_one,
      OfNat.ofNat_eq_ofNat, Nat.succ_ne_self, Nat.reduceEqDiff, CTag.left.injEq, add_eq_right,
      true_and, add_left_inj, add_right_inj, OfNat.one_ne_ofNat, right_eq_add, CTag.right.injEq,
      OfNat.ofNat_ne_zero, CTag.slab.injEq, not_and, IsEmpty.forall_iff, implies_true,
      List.Pairwise.nil]
    have hD := one_le_D p
    refine ⟨by omega, by omega, fun h => ?_⟩
    have := hz (by exact_mod_cast h)
    omega

/-- **The corners of the merge link of register `r` are at valid places owned by it.** -/
theorem mergeCorners_valid (p : Program) {r : ℕ} (hr : r < numRegs p) :
    ∀ c ∈ specCorners (mergeSpecs p r), Valid p c ∧ TagOfM p r c.tag := by
  have hf := layout_facts p
  have hR : (r : ℤ) < R p := by unfold R; exact_mod_cast hr
  have hA := A_nonneg p (a := p.length + r) (by omega)
  have he := solveE_bounds (unitWL p (p.length + r) haltDWL) (mergeCorners p r)
    (modWL p r incWin)
  have hH := hairReg_le p (s := 0) (e := mergeE p r) (c := A p (p.length + r) + haltD)
    (by norm_num) he.1
  intro c hc
  simp only [specCorners, mergeSpecs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    mergeCorners] at hc
  obtain ⟨h1, h2⟩ := downCorners_valid p (b := mergeBand p r) (s := 0)
    (by unfold mergeBand N at *; omega) (by norm_num) (by unfold haltD at *; omega) hH hR
    (idx := 2 * D p) (by omega) (vp := incPortV) (by unfold incPortV; omega) c hc
  refine ⟨h1, ?_⟩
  rcases h2 with ⟨k, h, h2⟩ | h2 <;> rw [h2]
  · simp [TagOfM, mergeBand]
  · simp [TagOfM]

/-- The corners of a merge link have pairwise distinct places. -/
theorem mergeCorners_tags (p : Program) (r : ℕ) :
    (specCorners (mergeSpecs p r)).Pairwise fun c c' => c.tag ≠ c'.tag := by
  have hD := one_le_D p
  rw [pairwise_tag_iff]
  simp only [specCorners, mergeSpecs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    mergeCorners, downCorners, bandCorners, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil]
  simp [List.pairwise_cons]

/-- **Every corner of the machine is at a valid place.** -/
theorem allCorners_valid {p : Program} (hp : p.WellFormed) : ∀ c ∈ allCorners p, Valid p c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨i, hi, hc⟩ := List.mem_flatMap.1 hc
    exact (instrCorners_valid hp (List.mem_range.1 hi) c hc).1
  · obtain ⟨r, hr, hc⟩ := List.mem_flatMap.1 hc
    exact (mergeCorners_valid p (List.mem_range.1 (List.mem_filter.1 hr).1) c hc).1

/-- **The corners of the machine have pairwise distinct places.** -/
theorem allCorners_tags {p : Program} (hp : p.WellFormed) :
    (allCorners p).Pairwise fun c c' => c.tag ≠ c'.tag := by
  unfold allCorners
  refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
  · refine pairwise_flatMap_lt List.pairwise_lt_range
      (fun i hi => instrCorners_tags hp (List.mem_range.1 hi)) ?_
    intro i hi i' hi' hii c hc c' hc' heq
    have h1 := (instrCorners_valid hp (List.mem_range.1 hi) c hc).2
    have h2 := (instrCorners_valid hp (List.mem_range.1 hi') c' hc').2
    rw [heq] at h1
    have := TagOf_unique p h1 h2
    omega
  · refine pairwise_flatMap_lt (pairwise_lt_range_filter _ _) (fun r _ => mergeCorners_tags p r) ?_
    intro r hr r' hr' hrr c hc c' hc' heq
    have h1 := (mergeCorners_valid p (List.mem_range.1 (List.mem_filter.1 hr).1) c hc).2
    have h2 := (mergeCorners_valid p (List.mem_range.1 (List.mem_filter.1 hr').1) c' hc').2
    rw [heq] at h1
    have := TagOfM_unique p h1 h2
    omega
  · intro c hc c' hc' heq
    obtain ⟨i, hi, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨r, hr, hc'⟩ := List.mem_flatMap.1 hc'
    have h1 := (instrCorners_valid hp (List.mem_range.1 hi) c hc).2
    have h2 := (mergeCorners_valid p (List.mem_range.1 (List.mem_filter.1 hr).1) c' hc').2
    rw [heq] at h1
    exact TagOf_not_M p (List.mem_range.1 hi) h1 h2

/-- **The route reflectors of the machine are pairwise separated.** -/
theorem linksPart_sep {p : Program} (hp : p.WellFormed) :
    (linksPart p).Pairwise fun s t => Piece.Sep s.piece t.piece := by
  have hv := allCorners_valid hp
  have h : ((allCorners p).map fun c => (cornerSpec c).bx).Pairwise BoxT.Sep := by
    refine List.pairwise_map.2 ((allCorners_tags hp).imp_of_mem fun hc hc' hne => ?_)
    exact (PSpec.sep_iff _ _).1 (PSpec.sep_of_far (corner_far (corner_gap p (hv _ hc)
      (hv _ hc') hne)))
  rw [← linksPart_bx] at h
  have h2 : (linksPart p).Pairwise fun s t => BoxT.Sep s.bx t.bx := List.pairwise_map.1 h
  exact h2

/-- **Units and routes are separated.** -/
theorem units_links_sep {p : Program} (hp : p.WellFormed) {s t : PSpec} (hs : s ∈ unitsPart p)
    (ht : t ∈ linksPart p) : Piece.Sep s.piece t.piece := by
  obtain ⟨a, -, hs⟩ := mem_unitsPart hs
  obtain ⟨c, hc, hbx⟩ := mem_linksPart ht
  have := corner_unit_sep p (allCorners_valid hp c hc) hs
  rw [PSpec.sep_iff] at this ⊢
  rw [hbx]
  exact this.symm

/-- **Modules and routes are separated.** -/
theorem modules_links_sep {p : Program} (hp : p.WellFormed) {s t : PSpec}
    (hs : s ∈ modulesPart p) (ht : t ∈ linksPart p) : Piece.Sep s.piece t.piece := by
  obtain ⟨r, -, hs⟩ := mem_modulesPart hs
  obtain ⟨c, hc, hbx⟩ := mem_linksPart ht
  have := corner_module_sep p (allCorners_valid hp c hc) hs
  rw [PSpec.sep_iff] at this ⊢
  rw [hbx]
  exact this.symm

/-- **Separation of the machine (as data)**: for every well-formed program, the placed pieces of
its machine are pairwise separated. -/
theorem machSpecs_sep {p : Program} (hp : p.WellFormed) :
    (machSpecs p).Pairwise fun s t => Piece.Sep s.piece t.piece := by
  unfold machSpecs
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨unitsPart_sep p, modulesPart_sep p,
    fun s hs t ht => units_modules_sep p hs ht⟩, linksPart_sep hp, ?_⟩
  intro s hs t ht
  rcases List.mem_append.1 hs with hs | hs
  · exact units_links_sep hp hs ht
  · exact modules_links_sep hp hs ht

/-- **Separation of the machine**: for every well-formed program, the periodic pieces of its Life
machine (layout `LP` of `R-31`) are pairwise separated: their boxes are far apart. -/
theorem machPieces_sep (p : Program) (hp : p.WellFormed) : (machPieces p).Pairwise Piece.Sep :=
  List.pairwise_map.2 (machSpecs_sep hp)

end LP

end LeanTheory.Life
