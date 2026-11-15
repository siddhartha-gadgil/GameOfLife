#!/usr/bin/env python3
"""Lean certificates for the station facts of cat_specs.json (untrusted generator; Lean checks).
Usage: cat_emit.py OUT.lean"""
import json
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_gates'))
from life import cells_of_window, step_cells, window_of_cells  # noqa

spec = json.load(open(os.path.join(HERE, 'results', 'cat_specs.json')))


def z(v):
    return '(%d)' % v if v < 0 else str(v)


def cells(w):
    return set(cells_of_window(w['x0'], w['y0'], [int(r) for r in w['rows']]))


def ofr(c, ind='  '):
    x, y, rows = window_of_cells(c)
    s = 'ofRows %s %s [%s]' % (z(x), z(y), ', '.join(map(str, rows)))
    if len(s) + len(ind) < 98:
        return s
    return 'ofRows %s %s\n%s  [%s]' % (z(x), z(y), ind, (',\n%s   ' % ind).join(map(str, rows)))


def box(b):
    return 'Box %s %s %s %s' % (z(b['xmin']), z(b['xmax']), z(b['ymin']), z(b['ymax']))


def pad(A, U):
    x, y, _ = window_of_cells(A)
    X, Y, _ = window_of_cells(U)
    return "ofRows_eq_padRows' %s %s %s %s %d %d _ (by norm_num) (by norm_num)" % (z(X), z(Y), z(x), z(y), y - Y, x - X)


def camel(n):
    p = n.split('_')
    return 'st' + ''.join(q[:1].upper() + q[1:] for q in p)


def union_eq(atoms_defs, U):
    """`rw [defs..., pads..., ← ofRows_orRows...]; rfl` proving a1 ∪ a2 = ofRows U."""
    names = [n for n, _ in atoms_defs]
    pads = [pad(c, U) for _, c in atoms_defs]
    return 'rw [%s, %s, %s]; rfl' % (', '.join(names), ', '.join(pads),
                                     ', '.join(['← ofRows_orRows'] * (len(atoms_defs) - 1)))


out = []
for e in spec['catalogue']:
    if e['kind'] not in ('reaction', 'stage'):
        continue
    N = camel(e['name'])
    G = cells(e['G'])
    In = set().union(*[cells(g['cells']) for g in e['In']])
    Out = set().union(*[cells(g['cells']) for g in e['Out']]) if e['Out'] else set()
    D = int(e['Delta'])
    c = set(G)
    for _ in range(D % 30):
        c = step_cells(c)
    GD = c
    doc = e['name'].replace('_', ' ')
    out.append('/-- The pieces of the station fact `%s` at phase `0` (generated). -/\ndef %sG : Finset Cell :=\n  %s\n'
               % (e['name'], N, ofr(G)))
    out.append('/-- **Certificate**: the pieces of `%s` have period `30` and stay in their box. -/\n'
               'theorem %sG_rest : Reaction %sG %sG 30 (fun _ => %s) := by\n  rw [%sG]\n  life_reaction\n'
               % (e['name'], N, N, N, box(e['B']), N))
    out.append('/-- The input of `%s`. -/\ndef %sIn : Finset Cell :=\n  %s\n' % (e['name'], N, ofr(In)))
    out.append('/-- The pieces of `%s` after %d generations. -/\ntheorem %sG_phase : phase %sG %d =\n    %s := by\n'
               '  rw [phase, show %d %% 30 = %d by norm_num, %sG]\n  life_cert\n'
               % (e['name'], D, N, N, D, ofr(GD, '    '), D, D % 30, N))
    U1 = G | In
    if Out:
        out.append('/-- The output of `%s`. -/\ndef %sOut : Finset Cell :=\n  %s\n' % (e['name'], N, ofr(Out)))
        U2 = GD | Out
        qrw = ('    show %s ∪ %sOut = %s by\n      rw [%sOut, %s, %s, ← ofRows_orRows]; rfl]'
               % (ofr(GD, '      '), N, ofr(U2, '      '), N, pad(GD, U2), pad(Out, U2)))
        Q = 'phase %sG %d ∪ %sOut' % (N, D, N)
    else:
        qrw = '    union_empty]'
        Q = 'phase %sG %d ∪ ∅' % (N, D)
    out.append('set_option maxRecDepth 100000 in\n/-- **Certificate**: %s, %d generations. -/\n'
               'theorem %s_relay :\n    Reaction (%sG ∪ %sIn) (%s) %d (fun _ => %s) := by\n'
               '  rw [%sG_phase, show %sG ∪ %sIn = %s by\n      %s,\n%s\n  life_reaction\n'
               % (doc, D, N, N, N, Q, D, box(e['R']), N, N, N, ofr(U1, '      '),
                  union_eq([('%sG' % N, G), ('%sIn' % N, In)], U1), qrw))
    if e['kind'] == 'stage':
        out.append('/-- `%s` as a stage of a route. -/\ndef %sStage : Stage where\n  G := %sG\n  In := %sIn\n'
                   '  Out := %sOut\n  Δ := %d\n  B := %s\n  R := %s\n  rest := %sG_rest\n  relay := %s_relay\n'
                   '  hBR := fun _ ⟨h1, h2, h3, h4⟩ => ⟨by omega, by omega, by omega, by omega⟩\n'
                   % (e['name'], N, N, N, N, D, box(e['B']), box(e['R']), N, N))

open(sys.argv[1], 'w').write('''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Route

/-!
# The dispatch station: its eight local facts

The dispatch station of the register machine (reports `R-29`, `R-31`): a gate, a reflector and an
eater on an answer line. Its facts, each a certificate at phase `0` of the common clock: capture of
the answer by the caller's token (lines NZ and Z), passage of an answer at a station not armed by a
token, absorption of an unpaired token, and absorption at the end of the line. Stations repeat by
translation (`R-31`). Data from `scripts/life_cert/results/cat_specs.json` (untrusted search),
generated by `scripts/life_cert/cat_emit.py`; every certificate is checked here.
-/

set_option linter.style.longLine false

@[expose] public section

namespace LeanTheory.Life

open Finset

''' + '\n'.join(out) + '\nend LeanTheory.Life\n')
