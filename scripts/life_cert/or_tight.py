#!/usr/bin/env python3
"""Tight footprints of the OR gate relays (through input, side inputs orSide6 / orSide7).

The crude footprint `Box 0 90 (-6) 60` of `orGate_relay` / `orGate_side6/7` contains the upper
left corner of the gate's frame, where the slab reflector of entry copy 0 of a merge / halt unit
sits.  The reaction never goes there: until generation `s` (166 for the through input, 46 for the
side inputs; both phase 16) the pattern stays in `Box 0 90 (-6) 38`; from then on it is the gate at
rest (`Box 0 90 0 32`) and the output glider, alone, in `Box 49 73 36 60`.  The glider at `s` is
the same in the three cases (`orOutMid`, 88 generations before the output place).

Usage: or_tight.py OUT.lean   (untrusted generator; Lean checks everything)."""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_gates'))
from life import step_cells, window_of_cells  # noqa: E402


def ofrows_set(x0, y0, rows):
    s = set()
    for j, r in enumerate(rows):
        i = 0
        while r:
            if r & 1:
                s.add((x0 + i, y0 + j))
            r >>= 1
            i += 1
    return s


ORG = [16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
       644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920,
       1227889072522402593802240, 642241841670271749074944, 453347182355485948903424,
       147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0,
       5368709120, 1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0,
       274877906944, 4505248894812160, 3378524354248704, 6755399441055744]
orGate = ofrows_set(0, 0, ORG)
orIn = ofrows_set(36, -6, [5, 6, 2])
side = {6: ofrows_set(44, 32, [3, 6, 1]), 7: ofrows_set(43, 32, [6, 5, 4])}
out = {(x + 35, y + 64) for x, y in orIn}
EARLY = (0, 90, -6, 38)     # a b lo hi
LATE = (49, 73, 36, 60)
REST = (0, 90, 0, 32)


def ev(c, n):
    for _ in range(n):
        c = step_cells(c)
    return c


def inbox(c, b):
    return all(b[0] <= x <= b[1] and b[2] <= y <= b[3] for x, y in c)


G = [orGate]
for _ in range(30):
    G.append(step_cells(G[-1]))
assert G[30] == orGate
assert all(inbox(g, REST) for g in G)


def check(start, n, s):
    c = start
    for i in range(s + 1):
        assert inbox(c, EARLY), i
        if i < s:
            c = step_cells(c)
    mid = c - G[s % 30]
    assert G[s % 30] <= c and len(mid) == 5
    m = mid
    for i in range(n - s + 1):
        assert inbox(m, LATE)
        if i < n - s:
            m = step_cells(m)
    assert m == out
    assert ev(start, n) == G[n % 30] | out
    return mid


mid = check(orGate | orIn, 254, 166)
assert check(orGate | side[6], 134, 46) == mid
assert check(orGate | side[7], 134, 46) == mid
assert REST[3] + 2 < LATE[2]


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


def box(b):
    return 'Box %s %s %s %s' % (z(b[0]), z(b[1]), z(b[2]), z(b[3]))


G16 = G[16]
U = G16 | mid
parts = []
parts.append('''/-- The OR gate at phase `16`. -/
theorem orGate_phase16 : phase orGate 16 = %s := by
  rw [phase, show 16 %% 30 = 16 by norm_num, orGate]
  life_cert

/-- The output glider of an OR gate relay, `88` generations before it reaches the input place of
the next copy. -/
def orOutMid : Finset Cell := %s

/-- **Certificate**: the output glider flies from `orOutMid` to the input place of the next copy
in `88` generations, inside `%s`. -/
theorem orOutMid_flight :
    Reaction orOutMid (translate (35, 64) orIn) 88 (fun _ => %s) := by
  rw [orOutMid, orIn, translate_ofRows, show (36 : ℤ) + 35 = 71 by norm_num,
    show (-6 : ℤ) + 64 = 58 by norm_num]
  life_reaction

/-- The OR gate at phase `16` with the output glider `orOutMid`, as one window. -/
theorem orGate_phase16_mid : phase orGate 16 ∪ orOutMid = %s := by
  rw [orGate_phase16, orOutMid, %s, %s, ← ofRows_orRows]
  rfl
''' % (ofr(G16), ofr(mid), box(LATE), box(LATE), ofr(U), pad(G16, U), pad(mid, U)))

U0 = orGate | orIn
parts.append('''set_option maxRecDepth 100000 in
/-- **Certificate**: the first `166` generations of the through relay, inside `%s`. -/
theorem orGate_relay_early :
    Reaction (orGate ∪ orIn) (phase orGate 166 ∪ orOutMid) 166 (fun _ => %s) := by
  rw [show phase orGate 166 = phase orGate 16 by
    rw [phase, phase, show 166 %% 30 = 16 %% 30 by norm_num],
    orGate_phase16_mid, show orGate ∪ orIn = %s by
      rw [orGate, orIn, %s, %s, ← ofRows_orRows]; rfl]
  life_reaction
''' % (box(EARLY), box(EARLY), ofr(U0), pad(orGate, U0), pad(orIn, U0)))
for r in (6, 7):
    S = side[r]
    U0 = orGate | S
    parts.append('''set_option maxRecDepth 100000 in
/-- **Certificate**: the first `46` generations of the side relay `orSide%d`, inside `%s`. -/
theorem orGate_side%d_early :
    Reaction (orGate ∪ orSide%d) (phase orGate 46 ∪ orOutMid) 46 (fun _ => %s) := by
  rw [show phase orGate 46 = phase orGate 16 by
    rw [phase, phase, show 46 %% 30 = 16 %% 30 by norm_num],
    orGate_phase16_mid, show orGate ∪ orSide%d = %s by
      rw [orGate, orSide%d, %s, %s, ← ofRows_orRows]; rfl]
  life_reaction
''' % (r, box(EARLY), r, r, box(EARLY), r, ofr(U0), r, pad(orGate, U0), pad(S, U0)))

HDR = '''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.MergeSide
public import LeanTheory.Theory.Life.Gen.ActSide

/-!
# Tight footprints of the OR gate relays: certificates

The crude footprint `Box 0 90 (-6) 60` of `orGate_relay`, `orGate_side6`, `orGate_side7` contains
the upper left corner of the gate's frame (`x ≤ 35`, `y ≥ 33`), where the reflector of the input
corner of entry copy `0` of a merge or halt unit sits. The reactions never go there: until
generation `166` (through input) or `46` (side inputs), both at phase `16`, the pattern stays in
`%s` (`orGate_relay_early`, `orGate_side6_early`, `orGate_side7_early`);
from then on it is the gate at rest and the output glider `orOutMid` (the same in the three
cases), which flies alone inside `%s` (`orOutMid_flight`).
Generated by `scripts/life_cert/or_tight.py` (untrusted); the certificates are checked here.
-/

set_option linter.style.longLine false

@[expose] public section

namespace LeanTheory.Life

open Finset

''' % (box(EARLY), box(LATE))
open(sys.argv[1], 'w').write(HDR + '\n'.join(parts) + '\nend LeanTheory.Life\n')
print('ok')
