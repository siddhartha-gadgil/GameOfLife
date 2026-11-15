#!/usr/bin/env python3
"""Early side inputs of the OR gate (untrusted generator; Lean checks everything).

The glider arriving on the side line of an OR gate (`orSide6`, window offset 4, or `orSide7`,
offset 5; `ActivationIncEntry.sideIn`) comes within distance 2 of the gate's box `Box 0 90 0 32`
in the last 10-11 generations before the side-input time `T0`, so its flight cannot be run beside
the idle gate up to `T0`.  Instead the gate and the glider are run **together** from `16`
generations before `T0`: the gate at phase `14` (it is at phase `0` at `T0`) and the glider of the
side line `16` generations early (`sideBase` at time `160` resp. `159`) become, in `16`
generations, exactly `orGate ∪ orSide6` resp. `orGate ∪ orSide7`, inside `Box 0 90 0 38`
(which lies in the tight relay footprint `orFoot` and in the gate box `Box 0 90 0 60`).
Before `T0 - 16` the glider box (`WL.box`) stays at rows `>= 36`, i.e. `>= 4` rows above the box
of the gate.

Usage: side_early.py OUT.lean"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_gates'))
from life import step_cells, window_of_cells, cells_of_window  # noqa: E402

ORG = [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
       644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920,
       1227889072522402593802240, 642241841670271749074944, 453347182355485948903424,
       147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0,
       5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0,
       274877906944, 4505248894812160, 3378524354248704, 6755399441055744]
orGate = cells_of_window(0, 0, ORG)
SIDE = {6: (44, 32, [3, 6, 1]), 7: (43, 32, [6, 5, 4])}
LEAD = 16
BOX = (0, 90, 0, 38)
GL = {(1, -1): [(0, 0, [7, 4, 2]), (0, -1, [2, 6, 5]), (0, -1, [6, 5, 4]), (1, -1, [3, 6, 1])]}
SIDEBASE = (1, -1, -76, 1)


def glider(w, t):
    """The window of `WL.cells w t` and the box `WL.box w t` (Lean's definitions)."""
    dx, dy, lane, tau = w
    q, j = (t - tau) // 4, (t - tau) % 4
    px = dx * q
    py = dx * (dy * px - lane)
    x0, y0, rows = GL[(dx, dy)][j]
    return (x0 + px, y0 + py, rows), (px - 1, px + 3, py - 1, py + 3)


def inbox(c, b):
    return all(b[0] <= x <= b[1] and b[2] <= y <= b[3] for x, y in c)


G = [orGate]
for _ in range(30):
    G.append(step_cells(G[-1]))
assert G[30] == orGate
assert inbox(orGate, (0, 90, 0, 32)) and all(inbox(g, (0, 90, 0, 32)) for g in G)
assert BOX[3] <= 38 and BOX[2] >= -6       # inside orFoot's early box and Box 0 90 0 60

res = {}
for r, d in ((6, 4), (7, 5)):
    w0, _ = glider(SIDEBASE, 180 - d)
    assert w0 == SIDE[r], (w0, SIDE[r])
    wa, _ = glider(SIDEBASE, 180 - d - LEAD)
    # before the window the glider box is far (FarApart 2) from the gate box: rows >= 32 + 3
    for s in range(LEAD + 1, LEAD + 200):
        _, b = glider(SIDEBASE, 180 - d - s)
        assert b[2] >= 35, (r, s, b)
    c = G[(30 - LEAD) % 30] | cells_of_window(*wa)
    for i in range(LEAD + 1):
        assert inbox(c, BOX), (r, i)
        if i < LEAD:
            c = step_cells(c)
    assert c == orGate | cells_of_window(*SIDE[r])
    res[r] = wa


def z(v):
    return '(%d)' % v if v < 0 else str(v)


def ofr(w):
    return 'ofRows %s %s [%s]' % (z(w[0]), z(w[1]), ', '.join(map(str, w[2])))


def pad(a, u):
    return "ofRows_eq_padRows' %s %s %s %s %d %d _ (by norm_num) (by norm_num)" % (
        z(u[0]), z(u[1]), z(a[0]), z(a[1]), a[1] - u[1], a[0] - u[0])


def box(b):
    return 'Box %s %s %s %s' % (z(b[0]), z(b[1]), z(b[2]), z(b[3]))


PH = (30 - LEAD) % 30
G14 = window_of_cells(G[PH])
parts = ['''/-- The OR gate at phase `%d`. -/
theorem orGate_phase%d : phase orGate %d = %s := by
  rw [phase, show %d %% 30 = %d by norm_num, orGate]
  life_cert
''' % (PH, PH, PH, ofr(G14), PH, PH)]
for r, d in ((6, 4), (7, 5)):
    wa = res[r]
    U0 = window_of_cells(G[PH] | cells_of_window(*wa))
    U1 = window_of_cells(orGate | cells_of_window(*SIDE[r]))
    T = 180 - d - LEAD
    parts.append(f"""/-- The side input `orSide{r}`, `{LEAD}` generations early. -/
def orSide{r}E : Finset Cell := {ofr(wa)}

/-- The early side input `orSide{r}E` is the glider of the side line at time `{T}`. -/
theorem orSide{r}E_eq : orSide{r}E = sideBase.cells {T} := rfl

set_option maxRecDepth 100000 in
/-- **Certificate**: the OR gate at phase `{PH}` and the side input `orSide{r}`, `{LEAD}`
generations early, become the gate at phase `0` and `orSide{r}`, inside `{box(BOX)}`. -/
theorem orGate_side{r}E :
    Reaction (phase orGate {PH} ∪ orSide{r}E) (orGate ∪ orSide{r}) {LEAD} (fun _ => {box(BOX)}) := by
  rw [show phase orGate {PH} ∪ orSide{r}E = {ofr(U0)} by
      rw [orGate_phase{PH}, orSide{r}E, {pad(G14, U0)}, {pad(wa, U0)}, ← ofRows_orRows]; rfl,
    show orGate ∪ orSide{r} = {ofr(U1)} by
      rw [orGate, orSide{r}, {pad((0, 0, ORG), U1)}, {pad(SIDE[r], U1)}, ← ofRows_orRows]; rfl]
  life_reaction
""")

HDR = '''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationIncEntry

/-!
# Early side inputs of the OR gate: certificates

The glider arriving on the side line of an OR gate (`orSide6`, offset `4`; `orSide7`, offset `5`)
comes within distance `2` of the gate's box in the last `10`-`11` generations before the side-input
time, so its flight cannot be run beside the idle gate up to that time. Instead the gate and the
glider are run **together** from `%d` generations before: the gate at phase `%d` and the glider of
the side line `%d` generations early (`orSide6E = sideBase.cells %d`, `orSide7E = sideBase.cells
%d`) become exactly `orGate ∪ orSide6` resp. `orGate ∪ orSide7`, inside `%s`
(`orGate_side6E`, `orGate_side7E`). Before that window the glider box is `>= 4` rows above the box
of the gate. Generated by `scripts/life_cert/side_early.py` (untrusted); the certificates are
checked here.
-/

set_option linter.style.longLine false

@[expose] public section

namespace LeanTheory.Life

open Finset

namespace LP

''' % (LEAD, PH, LEAD, 176 - LEAD, 175 - LEAD, box(BOX))
open(sys.argv[1], 'w').write(HDR + '\n'.join(parts) + '\nend LP\n\nend LeanTheory.Life\n')
print('ok')
