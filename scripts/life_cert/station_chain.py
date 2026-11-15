#!/usr/bin/env python3
"""Lean for the chains of dispatch stations (answer passing stations), lines NZ and Z (untrusted
generator; Lean checks).  Usage: station_chain.py OUT.lean"""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ('life_machine', 'life_gates'):
    sys.path.insert(0, os.path.join(HERE, '..', d))
from net import piece_cells, env_box  # noqa
from life import cells_of_window, bbox, glider_at, window_of_cells, step_cells  # noqa

spec = json.load(open(os.path.join(HERE, 'results', 'cat_specs.json')))


def z(v):
    return '(%d)' % v if v < 0 else str(v)


def ofr(c):
    x, y, rows = window_of_cells(c)
    return 'ofRows %s %s [%s]' % (z(x), z(y), ', '.join(map(str, rows)))


def box(b):
    return 'Box %s %s %s %s' % (z(b[0]), z(b[2]), z(b[1]), z(b[3]))


out = []
for name, L, v, d in (('pass_NZ', 'NZ', (72, 72), (1, 1)), ('pass_Z', 'Z', (72, -72), (1, -1))):
    e = [x for x in spec['catalogue'] if x['name'] == name][0]
    t0 = int(e['t0'])
    assert t0 % 30 == 0
    parts = [(piece_cells(tuple(p), t0), env_box(tuple(p))) for p in e['pieces']]
    ec = cells_of_window(e['eater_cells']['x0'], e['eater_cells']['y0'], e['eater_cells']['rows'])
    parts.append((set(ec), bbox(ec)))
    wl = e['In'][0]['wl']
    X = glider_at(d, wl[1], wl[2], t0)
    pb = None
    c = set(X)
    for _ in range(4):
        b = bbox(c)
        pb = b if pb is None else (min(pb[0], b[0]), min(pb[1], b[1]), max(pb[2], b[2]), max(pb[3], b[3]))
        c = step_cells(c)
    P = 'st' + L
    names = []
    for k, (cells, b) in enumerate(parts):
        nm = '%sP%d' % (P, k)
        names.append((nm, b))
        out.append('/-- Piece %d of the station on the line %s, at phase `0`. -/\ndef %s : Finset Cell :=\n  %s\n'
                   % (k, L, nm, ofr(cells)))
        out.append('/-- **Certificate**: piece %d of the station %s has period `30` in its box. -/\n'
                   'theorem %s_rest : Reaction %s %s 30 (fun _ => %s) := by\n  rw [%s]\n  life_reaction\n'
                   % (k, L, nm, nm, nm, box(b), nm))
    G = ' ∪ '.join(n for n, _ in names)
    B = ' ∪ '.join(box(b) for _, b in names)
    out.append('/-- The station on the line %s at phase `0`. -/\ndef %sG : Finset Cell := %s\n' % (L, P, G))
    out.append('/-- The answer glider at the station %s. -/\ndef %sX : Finset Cell := %s\n' % (L, P, ofr(X)))
    out.append('/-- The answer glider moves by `(%d, %d)` every four generations. -/\n'
               'theorem %sX_four : conway.evolve 4 %sX = translate (%d, %d) %sX := by\n'
               '  rw [%sX, translate_ofRows]\n  life_cert\n' % (d[0], d[1], P, P, d[0], d[1], P, P))
    out.append('/-- The answer glider during four generations. -/\n'
               'theorem %sX_box : ∀ r < 4, (conway.evolve r %sX : Set Cell) ⊆ %s := by\n'
               '  intro r hr\n  interval_cases r <;> (rw [%sX]; life_eval; exact coe_ofRows_subset_box rfl)\n'
               % (P, P, box(pb), P))
    # rest of G with the union of boxes
    seps = []
    out.append('/-- The station %s at rest, inside its three boxes. -/\n'
               'theorem %sG_rest : Reaction %sG %sG 30 (fun _ => %s) := by\n'
               '  have h := (%s_rest.par %s_rest fun _ _ => Box.farApart (by norm_num)).par %s_rest\n'
               '    (fun _ _ => FarApart.union_left (Box.farApart (by norm_num)) (Box.farApart (by norm_num)))\n'
               '  exact h\n' % (L, P, P, P, B, names[0][0], names[1][0], names[2][0]))
    # moving box of the glider and path set
    q = '((i / 4 : ℕ) : ℤ)'
    mov = 'Box (%s + %s * %s) (%s + %s * %s) (%s + %s * %s) (%s + %s * %s)' % (
        z(pb[0]), q, z(d[0]), z(pb[2]), q, z(d[0]), z(pb[1]), q, z(d[1]), z(pb[3]), q, z(d[1]))
    path = ('{c : Cell | ∃ m : ℤ, 0 ≤ m ∧ m ≤ 72 ∧ c ∈ Box (%s + m * %s) (%s + m * %s) (%s + m * %s) (%s + m * %s)}'
            % (z(pb[0]), z(d[0]), z(pb[2]), z(d[0]), z(pb[1]), z(d[1]), z(pb[3]), z(d[1])))
    R = '(%s) ∪ %s' % (B, path)
    out.append('/-- The region of the station %s while an answer passes. -/\ndef %sR : Set Cell := %s\n' % (L, P, R))
    out.append('''set_option maxRecDepth 100000 in
/-- **An answer passes the station %s** in 288 generations, to the place of the next station's. -/
theorem %s_relay :
    Reaction (%sG ∪ %sX) (phase %sG 288 ∪ translate (%d, %d) %sX) 288 (fun _ => %sR) := by
  have hf := flight_reaction %sX_four %sX_box 72 0 (G' := translate (%d, %d) %sX) (by
    rw [Rule.evolve_zero]; norm_num)
  have hg := phase_reaction %sG_rest 0 288
  rw [phase, Nat.zero_mod, Rule.evolve_zero, zero_add] at hg
  have h := hg.par hf fun i hi => by
    refine FarApart.union_left (FarApart.union_left ?_ ?_) ?_ <;>
      exact Box.farApart (by omega)
  refine h.mono fun i hi c hc => ?_
  rcases hc with hc | hc
  · exact Or.inl hc
  · right
    exact ⟨((i / 4 : ℕ) : ℤ), by positivity, by omega, hc⟩
''' % (L, P, P, P, P, v[0], v[1], P, P, P, P, v[0], v[1], P, P))
    shiftB = lambda bx, j: 'Box (%s + %s * %s) (%s + %s * %s) (%s + %s * %s) (%s + %s * %s)' % (
        z(bx[0]), j, z(v[0]), z(bx[2]), j, z(v[0]), z(bx[1]), j, z(v[1]), z(bx[3]), j, z(v[1]))
    def pat(v, withR):
        q = '(⟨{0}1, {0}2, {0}3, {0}4⟩ | ⟨{0}1, {0}2, {0}3, {0}4⟩) | ⟨{0}1, {0}2, {0}3, {0}4⟩'.format(v)
        if withR:
            m = 'm' if v == 'a' else 'm2'
            return '((' + q + ') | ⟨' + m + ', ' + m + 'l, ' + m + 'u, {0}1, {0}2, {0}3, {0}4⟩)'.format(v)
        return '(' + q + ')'

    def mk(rx, ry):
        sl = (P + 'R, ') if (rx or ry) else ''
        return ('intro j hj x hx y hy hn\n    simp only [' + sl + 'Set.mem_union] at hx hy\n'
                '    obtain ⟨n1, n2, n3, n4⟩ := hn\n    rcases hx with ' + pat('a', rx) + ' <;>\n'
                '      rcases hy with ' + pat('b', ry) + ' <;>\n      (push_cast at *; omega)')
    tac0, tac1, tac2 = mk(False, False), mk(True, False), mk(False, True)
    out.append('''set_option maxRecDepth 100000 in
/-- **A chain of stations on the line %s**, any length: an answer passes `L + 1` stations placed
every `(%d, %d)` in `(L + 1) 288` generations. -/
theorem %sChain (L : ℕ) :
    Reaction (relayChain %sG 288 (%d, %d) (L + 1) 0 ∪ %sX)
      (relayChain %sG 288 (%d, %d) (L + 1) ((L + 1) * 288) ∪
        translate (((L + 1 : ℕ) : ℤ) * (%d, %d).1, ((L + 1 : ℕ) : ℤ) * (%d, %d).2) %sX)
      ((L + 1) * 288) (fun _ => chainFoot %sR (%d, %d) (L + 1)) := by
  refine chain_reaction_set %sG_rest %s_relay (fun c hc => Or.inl hc) ?_ ?_ ?_ L
  · %s
  · %s
  · %s
''' % (L, v[0], v[1], P, P, v[0], v[1], P, P, v[0], v[1], v[0], v[1], v[0], v[1], P, P, v[0], v[1], P, P,
       tac0, tac1, tac2))

open(sys.argv[1], 'w').write('''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.StationFacts

/-!
# Chains of dispatch stations

The stations on an answer line of a register (reports `R-29`, `R-31`) repeat every `(72, 72)`
(line NZ) or `(72, -72)` (line Z), started `288` generations later. An answer passing a station is
a free flight next to the idle station, so a chain of stations relays the answer
(`chain_reaction_set`): `stNZChain`, `stZChain`. Data from
`scripts/life_cert/results/cat_specs.json`, generated by `scripts/life_cert/station_chain.py`
(untrusted); everything is checked here.
-/

set_option linter.style.longLine false

@[expose] public section

namespace LeanTheory.Life

open Finset

''' + '\n'.join(out) + '\nend LeanTheory.Life\n')
