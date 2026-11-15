#!/usr/bin/env python3
"""Joint approach certificates for the `decJz` step (untrusted generator; Lean checks everything).

A glider approaching an OR gate (side input) or a station (token) comes within distance 2 of the
piece's box before the certificate of the reaction starts, so the flight cannot be separated from
the piece up to that time.  These certificates run the piece and the glider together over the
approach:

* `decSideW6`, `decSideW7`, `decSideW10`: the OR gate at phase `10` and the side glider `20`
  generations before the side input (`orSide6`, `orSide7`, `orSide10`), inside `Box 0 90 0 40`;
* `stTokWNZ`, `stTokWZ`: a station (phase `0`) and the token `90` generations before the capture
  position (`stUnpairedTokenNZIn`, `stUnpairedTokenZIn`), the token flying through the station's
  bounding box without touching it.

Usage: dec_window.py OUT.lean"""
import os
import re
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_gates'))
from life import step_cells, window_of_cells, cells_of_window, bbox  # noqa: E402

LT = os.path.join(HERE, '..', '..', 'LeanTheory', 'Theory', 'Life')
GL = {(1, 1): [(0, 0, [2, 4, 7]), (0, 1, [5, 6, 2]), (0, 1, [4, 5, 6]), (1, 1, [1, 6, 3])],
      (-1, 1): [(0, 0, [2, 1, 7]), (0, 1, [5, 3, 2]), (0, 1, [1, 5, 3]), (-1, 1, [4, 3, 6])],
      (-1, -1): [(0, 0, [7, 1, 2]), (0, -1, [2, 3, 5]), (0, -1, [3, 5, 1]), (-1, -1, [6, 3, 4])],
      (1, -1): [(0, 0, [7, 4, 2]), (0, -1, [2, 6, 5]), (0, -1, [6, 5, 4]), (1, -1, [3, 6, 1])]}


def glider(w, t):
    dx, dy, lane, tau = w
    q, j = (t - tau) // 4, (t - tau) % 4
    px = dx * q
    py = dx * (dy * px - lane)
    x0, y0, r = GL[(dx, dy)][j]
    return cells_of_window(x0 + px, y0 + py, r)


def ev(c, n):
    for _ in range(n):
        c = step_cells(c)
    return c


def run_hull(c, n):
    h = bbox(c)
    for _ in range(n):
        c = step_cells(c)
        b = bbox(c)
        h = (min(h[0], b[0]), min(h[1], b[1]), max(h[2], b[2]), max(h[3], b[3]))
    return c, h


def lean_rows(src, name):
    m = re.search(r"def " + name + r" : Finset Cell :=\s*ofRows \(?(-?\d+)\)? \(?(-?\d+)\)?\s*\[([\d,\s]*)\]",
                  src)
    return cells_of_window(int(m.group(1)), int(m.group(2)),
                           [int(x) for x in m.group(3).split(',') if x.strip()])


def z(v):
    return '(%d)' % v if v < 0 else str(v)


def ofr(c):
    x, y, rows = window_of_cells(c)
    return 'ofRows %s %s [%s]' % (z(x), z(y), ', '.join(map(str, rows)))


def pad(A, U):
    x, y, _ = window_of_cells(A)
    X, Y, _ = window_of_cells(U)
    return "ofRows_eq_padRows' %s %s %s %s %d %d _ (by norm_num) (by norm_num)" % (
        z(X), z(Y), z(x), z(y), y - Y, x - X)


def boxs(b):
    return 'Box %s %s %s %s' % (z(b[0]), z(b[1]), z(b[2]), z(b[3]))


ORG = [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
       644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920,
       1227889072522402593802240, 642241841670271749074944, 453347182355485948903424,
       147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0,
       5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0,
       274877906944, 4505248894812160, 3378524354248704, 6755399441055744]
orGate = cells_of_window(0, 0, ORG)
G10 = ev(orGate, 10)
SIDE = (1, -1, -76, 1)
SB = (0, 90, 0, 40)
parts = ['''/-- The OR gate at phase `10`. -/
theorem orGate_phase10' : phase orGate 10 = %s := by
  rw [phase, show 10 %% 30 = 10 by norm_num, orGate]
  life_cert
''' % ofr(G10)]
for nm, d in (('6', 4), ('7', 5), ('10', 8)):
    E = glider(SIDE, 160 - d)
    S = glider(SIDE, 180 - d)
    end, h = run_hull(G10 | E, 20)
    assert end == orGate | S
    assert SB[0] <= h[0] and h[2] <= SB[1] and SB[2] <= h[1] and h[3] <= SB[3], h
    U0 = G10 | E
    U1 = orGate | S
    parts.append('''/-- The side glider `20` generations before `orSide%s` (on `sideBase` at `%d`). -/
def decSideE%s : Finset Cell := %s

/-- `decSideE%s` is the glider of the side line. -/
theorem decSideE%s_eq : decSideE%s = LP.sideBase.cells %d := rfl

set_option maxRecDepth 100000 in
/-- **Certificate**: the OR gate at phase `10` and the side glider `20` generations before the side
input `orSide%s` become the gate at phase `0` and `orSide%s`, inside `%s`. -/
theorem decSideW%s :
    Reaction (phase orGate 10 ∪ decSideE%s) (orGate ∪ orSide%s) 20 (fun _ => %s) := by
  rw [show phase orGate 10 ∪ decSideE%s = %s by
      rw [orGate_phase10', decSideE%s, %s, %s, ← ofRows_orRows]; rfl,
    show orGate ∪ orSide%s = %s by
      rw [orGate, orSide%s, %s, %s, ← ofRows_orRows]; rfl]
  life_reaction
''' % (nm, 160 - d, nm, ofr(E), nm, nm, nm, 160 - d, nm, nm, boxs(SB), nm, nm, nm, boxs(SB),
       nm, ofr(U0), nm, pad(G10, U0), pad(E, U0), nm, ofr(U1), nm, pad(orGate, U1), pad(S, U1)))

src = open(os.path.join(LT, 'StationFacts.lean')).read()
for nm, gname, inname, tok, T in (('NZ', 'stCaptureNZG', 'stUnpairedTokenNZIn', (1, -1, -1256, 8806), 10350),
                                  ('Z', 'stCaptureZG', 'stUnpairedTokenZIn', (-1, -1, -1230, 16087), 12390)):
    G = lean_rows(src, gname)
    In = lean_rows(src, inname)
    assert In == glider(tok, T)
    E = glider(tok, T - 90)
    end, h = run_hull(G | E, 90)
    h = (h[0], h[2], h[1], h[3])
    assert end == G | In
    U0 = G | E
    U1 = G | In
    parts.append('''/-- The token of station `0` of the line %s, `90` generations before the capture position. -/
def stTokE%s : Finset Cell := %s

set_option maxRecDepth 100000 in
/-- **Certificate**: the station of the line %s (phase `0`) and the token `90` generations before
the capture position: the token flies through the station's box, untouched, inside `%s`. -/
theorem stTokW%s : Reaction (%s ∪ stTokE%s) (%s ∪ %s) 90 (fun _ => %s) := by
  rw [show %s ∪ stTokE%s = %s by
      rw [%s, stTokE%s, %s, %s, ← ofRows_orRows]; rfl,
    show %s ∪ %s = %s by
      rw [%s, %s, %s, %s, ← ofRows_orRows]; rfl]
  life_reaction
''' % (nm, nm, ofr(E), nm, boxs(h), nm, gname, nm, gname, inname, boxs(h),
       gname, nm, ofr(U0), gname, nm, pad(G, U0), pad(E, U0),
       gname, inname, ofr(U1), gname, inname, pad(G, U1), pad(In, U1)))

HDR = '''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationDecStation
public import LeanTheory.Theory.Life.Gen.ActSide
public import LeanTheory.Theory.Life.Gen.ActSideDec

/-!
# Joint approach certificates of the `decJz` step

A glider approaching an OR gate from the side, or a token approaching its station, comes within
distance `2` of the piece's box before the certificate of the reaction starts. These certificates
run the piece and the glider together over the approach (generated by
`scripts/life_cert/dec_window.py`, untrusted; every certificate is checked here):

* `decSideW6`, `decSideW7`, `decSideW10`: the OR gate at phase `10` and the side glider `20`
  generations before the side inputs `orSide6`, `orSide7`, `orSide10`, inside `Box 0 90 0 40`;
* `stTokWNZ`, `stTokWZ`: a station at phase `0` and the token `90` generations before its capture
  position, which flies through the station's box untouched.
-/

set_option linter.style.longLine false

@[expose] public section

namespace LeanTheory.Life

open Finset

'''
open(sys.argv[1], 'w').write(HDR + '\n'.join(parts) + '\nend LeanTheory.Life\n')
print('ok')
