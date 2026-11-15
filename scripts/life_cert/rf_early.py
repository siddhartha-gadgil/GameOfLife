#!/usr/bin/env python3
"""Early reflections of the 8 reflector images (untrusted generator; Lean checks).

For every image `k` of the reflector (`rf_images.py`), the reflector `10` generations after phase
`0` and the input glider `20` generations before the input of the stage (`rfIn k` at time `-80`)
become, in `60` generations, the reflector at phase `10` again and the output glider `10`
generations after the output (`rfOut k` at time `-20`).  The footprint is the tight hull of the
run; it is checked to lie in the extended relay box `rxBox k` of `RouteSep.lean`.
Usage: rf_early.py OUT.lean"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_gates'))
from life import cells_of_window, step_cells, bbox, window_of_cells, transform  # noqa

RF0 = cells_of_window(0, 2, [12288, 34816, 66563, 214019, 66560, 1607680, 2633728, 2097152, 6291456])
IN = cells_of_window(20, 0, [1, 5, 3])
OUT = cells_of_window(11, -4, [2, 3, 5])
RFIN = {0: (-1, 1, 19, 18), 1: (-1, -1, 22, -68), 2: (1, -1, 23, 26), 3: (1, 1, 22, -60),
        4: (1, 1, -21, 26), 5: (-1, -1, -21, 18), 6: (1, -1, -20, -60), 7: (-1, 1, -24, -68)}
RFOUT = {0: (-1, -1, -14, 13), 1: (1, -1, -13, -37), 2: (1, 1, -14, 21), 3: (-1, 1, -17, -45),
         4: (1, -1, 16, 21), 5: (-1, 1, 12, 13), 6: (-1, -1, 15, -45), 7: (1, 1, 15, -37)}
# rxBox of RouteSep.lean: (a, b, lo, hi)
RX = {0: (0, 28, -7, 10), 1: (-10, 7, 0, 28), 2: (-28, 0, -10, 7), 3: (-7, 10, -28, 0),
      4: (-28, 0, -7, 10), 5: (0, 28, -10, 7), 6: (-7, 10, 0, 28), 7: (-10, 7, -28, 0)}
GL = {(1, 1): [(0, 0, [2, 4, 7]), (0, 1, [5, 6, 2]), (0, 1, [4, 5, 6]), (1, 1, [1, 6, 3])],
      (-1, 1): [(0, 0, [2, 1, 7]), (0, 1, [5, 3, 2]), (0, 1, [1, 5, 3]), (-1, 1, [4, 3, 6])],
      (-1, -1): [(0, 0, [7, 1, 2]), (0, -1, [2, 3, 5]), (0, -1, [3, 5, 1]), (-1, -1, [6, 3, 4])],
      (1, -1): [(0, 0, [7, 4, 2]), (0, -1, [2, 6, 5]), (0, -1, [6, 5, 4]), (1, -1, [3, 6, 1])]}
NAMES = ['rf0SWNW', 'rf0NWNE', 'rf0NESE', 'rf0SESW', 'rf0SENE', 'rf0NWSW', 'rf0NENW', 'rf0SWSE']


def glider(w, t):
    """The window of `WL.cells w t` (Lean's definition)."""
    dx, dy, lane, tau = w
    q, j = (t - tau) // 4, (t - tau) % 4
    px = dx * q
    py = dx * (dy * px - lane)
    x0, y0, rows = GL[(dx, dy)][j]
    return (x0 + px, y0 + py, rows)


def z(v):
    return '(%d)' % v if v < 0 else str(v)


def wrap(head, items, ind):
    """`head [i1, i2, ...]` broken into lines of at most 100 characters."""
    lines, cur = [], head + '['
    for n, it in enumerate(items):
        s = str(it) + (', ' if n + 1 < len(items) else ']')
        if len(cur) + len(s.rstrip()) > 88:
            lines.append(cur.rstrip())
            cur = ' ' * ind + s
        else:
            cur += s
    lines.append(cur)
    return '\n'.join(lines)


def ofr(w):
    return 'ofRows %s %s [%s]' % (z(w[0]), z(w[1]), ', '.join(map(str, w[2])))


def box(b):
    return 'Box %s %s %s %s' % (z(b[0]), z(b[1]), z(b[2]), z(b[3]))


def pad(a, u):
    return "ofRows_eq_padRows' %s %s %s %s %d %d _ (by norm_num) (by norm_num)" % (
        z(u[0]), z(u[1]), z(a[0]), z(a[1]), a[1] - u[1], a[0] - u[0])


def hull(b, c):
    d = bbox(c)
    return d if b is None else (min(b[0], d[0]), min(b[1], d[1]), max(b[2], d[2]), max(b[3], d[3]))


def stmt(name, ws, ind):
    """Lean text of `ofRows .. ∪ ofRows ..` broken into lines."""
    return (' ∪\n' + ' ' * ind).join(wrap('ofRows %s %s ' % (z(w[0]), z(w[1])), w[2], ind + 4)
                                      for w in ws)


out = []
boxes = []
for k in range(8):
    G = set(transform(RF0, k))
    I = set(transform(IN, k))
    O = set(transform(OUT, k))
    # rest box
    c, B = set(G), None
    for _ in range(30):
        B = hull(B, c)
        c = step_cells(c)
    G10 = G
    for _ in range(10):
        G10 = step_cells(G10)
    wI = glider(RFIN[k], -80)
    wO = glider(RFOUT[k], -20)
    I80 = cells_of_window(*wI)
    O20 = cells_of_window(*wO)
    # sanity: the Lean gliders at -60 / -30 are the stage input / output
    assert cells_of_window(*glider(RFIN[k], -60)) == I
    assert cells_of_window(*glider(RFOUT[k], -30)) == O
    c, E = G10 | I80, None
    for n in range(61):
        E = hull(E, c)
        if n < 60:
            c = step_cells(c)
    assert c == G10 | O20, k
    o10 = set(O)
    for _ in range(10):
        o10 = step_cells(o10)
    assert o10 == O20
    Ebox = (E[0], E[2], E[1], E[3])  # a b lo hi
    r = RX[k]
    assert r[0] <= Ebox[0] and Ebox[1] <= r[1] and r[2] <= Ebox[2] and Ebox[3] <= r[3], (k, Ebox)
    boxes.append(Ebox)
    Bb = (B[0], B[2], B[1], B[3])
    wG = window_of_cells(G)
    wG10 = window_of_cells(G10)
    U1 = window_of_cells(G10 | I80)
    U2 = window_of_cells(G10 | O20)
    out.append('''/-- **Certificate**: the reflector, image %d, ten generations after phase `0`. -/
theorem rfE%d_ph10 :
    Reaction
      (%s)
      (%s)
      10 (fun _ => %s) := by
  life_reaction

set_option maxRecDepth 100000 in
/-- **Certificate**: the early reflection of image %d: the reflector at phase `10` and the input
glider `20` generations early become the reflector at phase `10` and the output glider `10`
generations late. -/
theorem rfE%d_run :
    Reaction
      (%s)
      (%s)
      60 (fun _ => %s) := by
  rw [show
      %s =
      %s by
      rw [%s,
        %s,
        ← ofRows_orRows]
      rfl,
    show
      %s =
      %s by
      rw [%s,
        %s,
        ← ofRows_orRows]
      rfl]
  life_reaction
''' % (k, k, wrap('ofRows %s %s ' % (z(wG[0]), z(wG[1])), wG[2], 8),
       wrap('ofRows %s %s ' % (z(wG10[0]), z(wG10[1])), wG10[2], 8), box(Bb),
       k, k, stmt('', [wG10, wI], 6), stmt('', [wG10, wO], 6), box(Ebox),
       stmt('', [wG10, wI], 6), wrap('ofRows %s %s ' % (z(U1[0]), z(U1[1])), U1[2], 8),
       pad(wG10, U1), pad(wI, U1),
       stmt('', [wG10, wO], 6), wrap('ofRows %s %s ' % (z(U2[0]), z(U2[1])), U2[2], 8),
       pad(wG10, U2), pad(wO, U2)))

cases = '\n'.join('  | %d => %s' % (k, box(boxes[k])) if k < 7 else '  | _ => %s' % box(boxes[k])
                  for k in range(8))
proofs = '\n'.join('''  · have h := rfE%d_run
    rw [← rfE%d_ph10.evolve_eq] at h
    exact h''' % (k, k) for k in range(8))
sub = '\n'.join('  · exact ⟨by omega, by omega, by omega, by omega⟩' for k in range(8))

open(sys.argv[1], 'w').write('''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.ActivationInc

/-!
# Early reflections of the eight reflector images

The incoming glider comes within distance `2` of the box of its reflector about `12` generations
before it is met, and the outgoing glider is near the reflector until about `2` generations after
the reflection, so a route cannot run its glider beside the idle reflector up to the meeting time.
Instead, the reflector and the glider are run **together** from `20` generations before the
meeting time to `40` after (`60` generations): for every image `k`, the reflector `10`
generations after phase `0` (`rfE*_ph10`) and the glider of `rfIn k` at time `-80` become the
reflector at phase `10` and the glider of `rfOut k` at time `-20`, inside the box `rfBoxE k`
(`rfE_early`). Outside this window the glider box is far from the reflector box for every image.
Generated by `scripts/life_cert/rf_early.py` (untrusted); every certificate is checked here.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

namespace LP

%s
/-- The footprint of the early reflection of image `k` (corner frame), the tight hull of the run
(for image `3` the box of `rf3_early`). -/
def rfBoxE : ℕ → Set Cell
%s

/-- **The early reflection of every image**: the reflector `10` generations after phase `0` and
the glider of the input line at time `-80` (`20` generations before the input of the stage)
become, in `60` generations, the reflector at phase `10` and the glider of the output line at time
`-20` (`10` generations after the output of the stage), inside `rfBoxE k`. -/
theorem rfE_early (k : ℕ) :
    Reaction (conway.evolve 10 (rfStage k).G ∪ (rfIn k).cells (-80))
      (conway.evolve 10 (rfStage k).G ∪ (rfOut k).cells (-20)) 60 (fun _ => rfBoxE k) := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k
%s

end LP

end LeanTheory.Life
''' % ('\n'.join(out), cases, proofs))
print(boxes)
