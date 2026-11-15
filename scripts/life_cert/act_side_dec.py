#!/usr/bin/env python3
"""Side input of the OR gate at the R-29 residue 10 (window offset 8 of LP: the control C of a decJz
instruction with odd q arrives at the DEC chain at offset 4 + 2 sigma = 8): it releases the through
relay's output (variant of act_side.py)."""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ('life_route', 'life_zero', 'life_machine', 'life_gates'):
    sys.path.insert(0, os.path.join(HERE, '..', d))
from gcommon import *                      # noqa
from net import wl_out, piece_cells, env_box  # noqa
from life import step_cells, bbox, window_of_cells, chebyshev_dist, cells_of_window  # noqa

V = (35, 64)
g = ('asm', 0, 0, 0, 0)
eb = env_box(g)
In = glider_at(*wl_out((SE, 43, 5), g), 150)
Out = {(x + V[0], y + V[1]) for x, y in In}
res = {}
for r in (10,):
    w = wl_out((NE, -76, r - 1), g)
    found = None
    for t1 in range(-3000, 3000, 30):
        S = glider_at(*w, t1)
        G = piece_cells(g, t1)
        if 3 <= chebyshev_dist(S, G) and chebyshev_dist(S, G) <= 8:
            found = t1
            break
    S = glider_at(*w, found)
    G = piece_cells(g, found)
    c = G | S
    R = bbox(c)
    for D in range(1, 1500):
        c = step_cells(c)
        b = bbox(c)
        R = (min(R[0], b[0]), min(R[1], b[1]), max(R[2], b[2]), max(R[3], b[3]))
        if c == piece_cells(g, found + D) | Out:
            break
    else:
        D = None
    res[r] = (found, window_of_cells(S), D, R)
    print('residue', r, 't1', found, 'S', window_of_cells(S), 'Delta', D, 'mod30', D % 30 if D else None, 'R', R, 'G phase', found % 30)


def z(v):
    return '(%d)' % v if v < 0 else str(v)


def ofr(c):
    x, y, rows = window_of_cells(c)
    return 'ofRows %s %s [%s]' % (z(x), z(y), ', '.join(map(str, rows)))


def pad(A, U):
    x, y, _ = window_of_cells(A)
    X, Y, _ = window_of_cells(U)
    return "ofRows_eq_padRows' %s %s %s %s %d %d _ (by norm_num) (by norm_num)" % (z(X), z(Y), z(x), z(y), y - Y, x - X)


if len(sys.argv) > 1:
    G0 = piece_cells(g, 150)
    parts = []
    for r, (t1, Sw, D, R) in res.items():
        assert t1 % 30 == 150 % 30
        S = set(cells_of_window(*Sw)) if False else glider_at(*wl_out((NE, -76, r - 1), g), t1)
        GD = piece_cells(g, t1 + D)
        U1, U2 = G0 | S, GD | Out
        parts.append('''/-- The side input of the OR gate at residue %d (R-29 numbering). -/
def orSide%d : Finset Cell := %s

/-- The OR gate after %d generations. -/
theorem orGate_phase%d : phase orGate %d = %s := by
  rw [phase, show %d %% 30 = %d by norm_num, orGate]
  life_cert

set_option maxRecDepth 100000 in
/-- **Certificate**: the side input at residue %d releases the input of the next copy, in %d
generations. -/
theorem orGate_side%d :
    Reaction (orGate ∪ orSide%d) (phase orGate %d ∪ translate (35, 64) orIn) %d
      (fun _ => Box %s %s %s %s) := by
  rw [orGate_phase%d, show orGate ∪ orSide%d = %s by
      rw [orGate, orSide%d, %s, %s, ← ofRows_orRows]; rfl,
    show %s ∪ translate (35, 64) orIn = %s by
      rw [orIn, translate_ofRows, show (%d : ℤ) + 35 = %d by norm_num, show (%d : ℤ) + 64 = %d by norm_num,
        %s, %s, ← ofRows_orRows]; rfl]
  life_reaction

/-- **The merge chain entered from the side** (residue %d): the side input of the first of
`L + 2` OR gates is carried to the place of the input of a copy number `L + 2`. -/
theorem orChainSide%d (L : ℕ) :
    Reaction (relayChain orGate 254 (35, 64) (L + 2) 0 ∪ orSide%d)
      (phase orGate (%d + (L + 1) * 254) ∪ translate (35, 64) (relayChain orGate 254 (35, 64) (L + 1)
        ((L + 1) * 254) ∪ translate (((L + 1 : ℕ) : ℤ) * (35, 64).1, ((L + 1 : ℕ) : ℤ) * (35, 64).2) orIn))
      (%d + (L + 1) * 254) (fun _ => chainFoot (Box 0 90 (-6) 60) (35, 64) (L + 2)) :=
  chain_side_reaction orGate_rest orGate_relay orGate_side%d (by norm_num)
    (fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, by omega, by omega⟩)
    (fun _ ⟨h1, h2, h3, h4⟩ => ⟨by omega, by omega, by omega, by omega⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) L
''' % (r, r, ofr(S), D, r, D, ofr(GD), D, D % 30, r, D, r, r, D, D, z(R[0]), z(R[2]), z(R[1]), z(R[3]),
       r, r, ofr(U1), r, pad(G0, U1), pad(S, U1), ofr(GD), ofr(U2),
       window_of_cells(In)[0], window_of_cells(In)[0] + 35, window_of_cells(In)[1], window_of_cells(In)[1] + 64,
       pad(GD, U2), pad(Out, U2), r, r, r, D, D, r))
    open(sys.argv[1], 'w').write('''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.MergeChain

/-!
# The merge chain entered from the side at the residue 10

The side input of the OR gate at the R-29 residue 10 (window offset `8` of the side world line
`sideWL`; the control `C` of a `decJz` instruction with odd `q = D - 1 - j` arrives at its DEC copy
at offset `4 + 2 σ = 8`) releases the same glider as the through input, `134` generations later, so
a chain of OR gates carries it like a through input (`chain_side_reaction`).
Generated by `scripts/life_cert/act_side_dec.py` (untrusted); the certificates are checked here.
-/

set_option linter.style.longLine false

@[expose] public section

namespace LeanTheory.Life

open Finset

''' + '\n'.join(parts) + '\nend LeanTheory.Life\n')
